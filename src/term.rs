use crate::common::*;
use crate::error::Spanned;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Builtin {
    Int,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Def(pub Spanned<Sym>, pub STerm);

/// A spanned term. Most terms will have this type
pub type STerm = Spanned<Term>;

/// A `Term` represents a type or term `before` reduction.
/// We do type checking on `Term`s, and when we want to use it as a type we `reduce()` it to a `Value`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Unit,                       // ()
    The(STerm, STerm),          // the T x
    Binder(Sym, Option<STerm>), // x: T
    Var(Sym),                   // a
    I32(i32),                   // 3
    Type,                       // Type
    Builtin(Builtin),           // Int
    Fun(STerm, STerm),          // fn a => x
    App(STerm, STerm),          // f x
    Pair(STerm, STerm),         // x, y
}
impl CDisplay for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter, b: &Bindings) -> std::fmt::Result {
        match self {
            Term::Unit => write!(f, "()"),
            Term::The(t, u) => write!(f, "the {} {}", WithContext(b, &**t), WithContext(b, &**u)),
            Term::Binder(x, None) => write!(f, "({}{}:)", b.resolve(*x), x.num()),
            Term::Binder(x, Some(t)) => write!(f, "{}{}: {}", b.resolve(*x), x.num(), WithContext(b, &**t)),
            Term::Var(s) => write!(f, "{}{}", b.resolve(*s), s.num()),
            Term::I32(i) => write!(f, "{}", i),
            Term::Type => write!(f, "Type"),
            Term::Builtin(b) => write!(f, "{:?}", b),
            Term::Fun(x, y) => write!(f, "fun {} => {}", WithContext(b, &**x), WithContext(b, &**y)),
            Term::App(x, y) => write!(f, "{}({})", WithContext(b, &**x), WithContext(b, &**y)),
            Term::Pair(x, y) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
        }
    }
}
