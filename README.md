# Pika
This is a rewrite of the Pika compiler.
Currently it doesn't really work, but it should be significantly faster and more robust than the old version eventually.
The new typechecker is heavily inspired by [smalltt](https://github.com/AndrasKovacs/smalltt).

Pika is a small, dependently typed ML with algebraic effects and unboxed types.
The language has also been redesigned since the last compiler, so for details see `demo.pk`.

### Why rewrite the compiler?
Well, parts of the old one were annoying, and it wasn't very fast.
The language was due for a redesign anyway.

Plus, it seems that's [what everybody](https://github.com/brendanzab/rust-nbe-for-mltt) is [doing nowadays](https://github.com/ollef/sixty).
