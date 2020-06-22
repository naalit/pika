# Pika
Pika is a little dependently typed systems language that's currently a work in progress.
It's a toy language right now, but we'll see where it goes.

### Goals
Pika should:
- Prevent bugs and encourage good program organization
- Have predictable and fast performance and memory usage
- Eventually, work well on GPUs and embedded systems

To that end, some things Pika has/will have:
- Dependent types
- Staging
  - This is how GPU support will work, and replaces macros
- Algebraic effects
  - The type system specifies which functions are pure, which is important for GPUs again where no IO exists,
      and for preventing bugs
- No implicit heap allocation
  - On GPUs, for example, there is no heap
- Ownership
  - Quantitative Type Theory, so values can be erased (e.g. types, multiplicity 0), move-only (multiplicity 1), or copiable (Rust `Copy`, multiplicity ω)
  - We'll also have borrows and mutability more or less like Rust, but hopefully we can avoid any lifetime annotations, those are annoying and confusing
  - The compiler decides to pass by reference or by value based on size, regardless of borrowing
- No runtime

### Status
Currently, Pika supports typechecking, compiling to LLVM, and running simple expressions with functions and ints.
It has some support for pairs and records, but don't expect that to work very well yet.

It does type erasure via monomorphization, so no types are passed around at runtime (but monomorphized functions are currently 100% inlined, so try to avoid large ones for now) and has full support for closures.
It uses bidirectional type checking via something adjacent to Normalization-By-Evaluation.

### Example
This runs with the current compiler:
```crystal
# Polymorphic Church natural numbers
Nat := fun (t:Type) (fun t => t) t => t

# Zero returns `x` unchanged
zero : Nat = fun t f x: => x

# The successor function returns another number that applies `f` to the first one's output
suc : (fun Nat => Nat) = fun n t f x: => f (n t f x)

# We don't need type annotations if the compiler can figure it out
one := suc zero
two := suc one

# Functions are curried, so `const T a` returns a function that ignores its argument and returns `a`
const : fun (t:Type) t t => t = fun _ a b: => a
a := one Int (const Int 12) 2 # returns 12

# Functions can pattern-match and recurse (no mutual recursion yet, though)
fib := fun
  0 => 1
  1 => 1
  i:Int => (fib (i - 1)) + (fib (i - 2))

# `pika run path-to-this-file.pk` will compile it with LLVM and print out the value of `main`
# It should be 610
main := fib 14
```

#### Why "Pika"?
Pikas are little mammals that live on mountains, close relatives of rabbits. Pika the language is also small, but it isn't a close relative of any rabbits. Since it has dependent types, it has pi types, and "Pika" has "Pi" in it, so that's something else.

I think all programming languages should be named after animals. Lots of them already have animal mascots anyway - so Go should be called Gopher, and Rust should be Crab (..or just Ferris? I think Gopher works better than Crab). Originally I was going to pick an insectivore so that I could say the language eats bugs, but I like "Pika" even though pikas are herbivores.
