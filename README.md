# Pika
Pika is a small, dependently typed ML with algebraic effects and unboxed types.
This is the rewritten version of the compiler, and the new typechecker is heavily inspired by [smalltt](https://github.com/AndrasKovacs/smalltt).

Pika compiles to native code with LLVM (through [Durin](https://github.com/tolziplohu/durin), a dependently typed optimizing intermediate language).
It doesn't have all its planned features implemented yet, but the core is there: dependent types, algebraic effects, and unboxed types all work.

### Example
Pika doesn't have all its planned features implemented yet, but here are some that currently work.
Look in the `tests` folder for more examples of Pika code that works today.
For a demonstration of planned features, see `demo.pk`.
```cr
# Syntax is similar to Standard ML, but comments use #
# Pika doesn't have universes, so Type has type Type
val U : Type = Type

# Functions can have implicit parameters with []
fun id [T] (x : T) : T = x

# And types can be inferred
fun one (x : Type) = x
fun two y = one y

# You can pass implicit parameters implicitly or explicitly
val test = id Type
val test2 = id [Type] Type

# And you can use explicit lambdas instead of `fun`
# Also, `_` introduces a hole filled by unification
val id2 : [T] T -> _ = x => x

# Pika has datatypes and pattern matching as well
# With explicit boxing and unboxing (but things are unboxed by default)
type List T of
  Nil
  Cons T (box List T)
where
  # This is in List's "associated namespace", as are the constructors, like `impl` in Rust.
  # Code outside of the associated namespace needs to qualify the constructors when matching, like `List.Nil`
  fun len [T] (self : List T) : I32 = case self of
    Nil => 0
    Cons x rest => 1 + len rest
  # Pika uses significant indentation for blocks

val _ = List.len (List.Cons Type (List.Nil))

# And algebraic effects
eff Console of
  Print String : ()
  Read () : String

fun greet () : () with Console = do
  Console.Print "Hello, "
  val name : String = Console.Read ()
  Console.Print name

# Now we handle the effects
# Print out what `greet` tells us to, but make `Read` always return "Pika"
fun main () with IO = catch greet () of
  () => ()
  eff (Console.Print s) k => do
    puts s
    k ()
  eff (Console.Read ()) k => k "Pika"
```

#### Why "Pika"?
Lots of languages have animal mascots, so Pika's is the pika.
Pikas are little mammals that live on mountains, close relatives of rabbits.
Pika the language is also small, but it isn't a close relative of any rabbits.
Since it has dependent types, it has pi types, and "Pika" has "Pi" in it, so that's something else.
