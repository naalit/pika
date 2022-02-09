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
# Syntax is similar to Standard ML or OCaml, but comments use #
# Pika doesn't have universes, so Type has type Type
let U : Type = Type

# Functions can have implicit parameters with []
fun id [T] (x : T) : T = x

# And types can be inferred
fun one (x : Type) = x
fun two y = one y

# You can pass implicit parameters implicitly or explicitly
let test = id Type
let test2 = id [Type] Type

# And you can use explicit lambdas instead of `fun`
# Also, `_` introduces a hole filled by unification
let id2 : [T] T -> _ = x => x

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

let _ = List.len (List.Cons Type (List.Nil))

# And algebraic effects
eff Console of
  Print String : ()
  Read () : String

fun greet () : () with Console = do
  Console.Print "Hello, "
  let name : String = Console.Read ()
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

### Significant indentation

#### Why does Pika have significant indentation?

Part of it is because I don't want semicolons, I want newlines to delimit statements, but I also want it to be easy to continue a statement on the next line.
This is why Python has `\`, but that's not a good solution; and some languages use properties of the syntax so it's (somewhat) unambiguous, like Lua or JavaScript, but that's doesn't work for ML-like languages with juxtaposition as function application.

Also, using `end` like Pika used to do often looks weird when indentation for things other than blocks is used, for example here where there are three dedents but only one has an `end`:
```cr
fun do_something x y z =
  case find_the_thing x y z of
    Some a => a
    None =>
      x + y * 2 + z * 3
  end
```

It's also a lot nicer when passing lambdas as arguments. Compare:
```cr
list
  .iter
  .filter
    x => x % 2 == 0 and x % 5 == 0
  .map
    x => x * 2 + 3
```
to either of the lambdas here:
```cr
list
  .iter
  # Remember, the lambda can't be on another line without a backslash!
  .filter (x => x % 2 == 0 and x % 5 == 0)
  # This is the special multiline lambda syntax, which mostly exists for
  # this sort of thing, but it's still not great for this short lambda.
  .map do x =>
    x * 2 + 3
  end
```

#### How does Pika's significant indentation work?

Pika's significant indentation isn't quite like other languages with significant indentation.
It's more like some of the proposals for significant indentation in Scheme, like [wisp](https://srfi.schemers.org/srfi-119/); and unlike Haskell, there aren't complex layout rules using column numbers, it's just INDENT and DEDENT tokens when the indentation goes up and down.
It's designed so that code usually does what it looks like - indentation should never be misleading.

There are generally three cases for what indentation means in Pika:

1. Blocks, like `do`, `where`, `case-of`, etc., are delimited by indentation. This is simple, and works like Python:
    ```ml
    fun unwrap_and_print_or self default = case self of
      Some x => do
        print x
        x
      None => default
    ```

2. In expressions, indentation can be used for grouping: more-indented lines are essentially wrapped in parentheses. This is especially useful for function calls with many or very long arguments. For example:
    ```cr
    Map.from
      List.zip
        context.keys
        List.Cons 1
          get_list_one ()
    # -->
    Map.from (List.zip context.keys (List.Cons 1 (get_list_one ()))

    3 + 4 *
      5 + 6
    # -->
    3 + 4 * (5 + 6)
    ```

3. If the more-indented line begins with a binary operator like `+` or `.`, the previous lines are grouped. This is handy for operator chaining, especially with `.` method syntax.
    ```cr
    range 0 100
      .reverse
      .filter is_even
      .map
        x => x * 3
      .collect

    term_one * 0.5 + term_two * 0.3 + term_three * 0.2
      + adj
      * scale
    # -->
    ((term_one * 0.5 + term_two * 0.3 + term_three * 0.2) + adj) * scale
    ```


### Why "Pika"?
Lots of languages have animal mascots, so Pika's is the pika.
Pikas are little mammals that live on mountains, close relatives of rabbits.
Pika the language is also small, but it isn't a close relative of any rabbits.
Since it has dependent types, it has pi types, and "Pika" has "Pi" in it, so that's something else.
