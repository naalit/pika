# The Pika compiler's backend
This document describes the architecture of the Pika compiler's backend,
some of which has been implemented and some of which hasn't yet.

### CPS transform and Low IR
Pika's Low IR lives in `backend/low.rs`, and it describes code in Continuation-Passing Style.
That means that instead of returning a value, every function takes an extra argument which is a closure to pass their return value to, called a *continuation*.
Essentially, the code is always moving forward, and all calls are tail calls, so we don't need to use the LLVM stack for return addresses, etc.
We use our own custom stack for that, described in the next section.

Low IR is also in A-Normal Form (or maybe it's not if that precludes CPS?), so every argument to a call, operator, etc. must be a variable.
So, every intermediate value is bound with a `let .. in` expression.

For example, this Pika code:
```cr
f := fun x y z: Int => (x + y) * (z + x)
a := f 8 6 3
```
Turns into something like this in Low IR:
```ml
let f = fun (x y z: Int), (k: fun Int => ()) =>
  let _0 = x + y (* arguments to calls and operators must be simple variables, so we use `let` for intermediates *)
  let _1 = z + x
  let _2 = _0 * _1
  in k _2 (* instead of returning, we call the continuation with the return value *)
let a = fun (k: fun Int => ()) => f 8 6 3, k (* this is essentially tail recursion: we're passing the continuation unchanged *)
```
Of course, in actual Low IR currying is explicit, and it's in general much longer (operators are curried and take continuations too, etc.), but that's the idea.

### The Pika stack
We do use the LLVM stack *within* a Pika function, essentially for register spilling, and also for FFI calls.
But between Pika functions, we use our own stack, implemented as a segmented stack, possibly with an overlap between segments like GHC has to avoid the "hot split" problem, the reason Go abandoned segmented stacks.
We store return addresses implicitly, as part of the environment of continuations.
Continuation environments are just a spot on the stack, since they have stack semantics except for effects.
When a continuation is called, it's responsible for freeing its environment, just by shifting the stack pointer.

A custom stack lets us do a few things:
- We can store things on the stack with a size not known at compile time, as long as we store a size somewhere too.
- We can have a segmented stack, so recursion won't overflow even when stack allocating large objects.
- We can implement effects as stackful coroutines efficiently.

Since we pass things on the Pika stack, we don't want monomorphization everywhere, and these two functions:
```cr
f := (fun (t:Type) (x:t) => x) Int
g := fun i:Int => i + 2
```
must be ABI-compatible, all function parameters are passed as `i8*`s, then, if the size of the type is small enough, casted from the i8*, otherwise loaded.
It's pretty similar to what OCaml does, and it means that things less than a word can still be passed in registers, which is good.

### Effects
Speaking of effects, here's how they're implemented. Effects have three parts: the `catch`, the `perform`, and the `continue`
(the actual syntax for these isn't decided yet).
When we reach a `catch`, we allocate a new stack segment, copy anything the code inside the `catch` needs to it, and switch to that stack while we execute the `catch` code.
At the start of that stack segment we put the continuation of the `catch`, which expects an `Eff R E`, a sum type of `Return R` and `Effect (E a) (fun a => Eff R E)`.
The continuation we pass to the code inside the `catch` wraps the return value in a `Return` variant, and passes it to the `catch`'s continuation at the start of the new stack, switching back the stack and releasing the new segment as it does so.

If we hit a `perform` inside the `catch`, though, we:
- Capture the continuation of the `perform`, we'll call it `kp`.
- Wrap it in an function that sets the continuation at the start of the new stack to *its* continuation, then calls `kp`, but that way `kp` returns to the new continuation instead of the old one (i.e. the `continue`'s continuation, not the `catch`'s).
- Wrap that with the `perform`'s value in an `Effect` variant.
- Switch back to the old stack and call the continuation of the `catch`, passing it that `Effect` variant. The new stack is saved in case the function part of the `Effect` is called, and if it's dropped the new stack is released.

At least eventually, we'll optimize unresumable effects, ones with continuations `! -> ...`, to not allocate a new stack segment and just set the stack pointer back when they're `perform`ed.
That should give them the performance of a simple call, no overhead at all.
