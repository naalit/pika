use crate::common::*;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Builtin {
    Int,
}

/// A spanned term. Most terms will have this type
pub type STerm = crate::error::Spanned<Term>;

/// A `Term` represents a type or term `before` reduction.
/// We do type checking on `Term`s, and when we want to use it as a type we `reduce()` it to a `Value`
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Unit,                       // ()
    The(STerm, STerm),          // the T x
    Let(Sym, STerm, STerm),     // let x = y in z
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
            Term::Let(s, x, y) => write!(
                f,
                "let {} = {} in {}",
                b.resolve(*s),
                WithContext(b, &**x),
                WithContext(b, &**y)
            ),
            Term::The(t, u) => write!(f, "the {} {}", WithContext(b, &**t), WithContext(b, &**u)),
            Term::Binder(x, None) => write!(f, "({}{}:)", b.resolve(*x), x.num()),
            Term::Binder(x, Some(t)) => write!(f, "{}{}: {}", b.resolve(*x), x.num(), WithContext(b, &**t)),
            Term::Var(s) => write!(f, "{}{}", b.resolve(*s), s.num()),
            Term::I32(i) => write!(f, "{}", i),
            Term::Type => write!(f, "Type"),
            Term::Builtin(b) => write!(f, "{:?}", b),
            Term::Fun(x, y) => write!(f, "fn {} => {}", WithContext(b, &**x), WithContext(b, &**y)),
            Term::App(x, y) => write!(f, "{}({})", WithContext(b, &**x), WithContext(b, &**y)),
            Term::Pair(x, y) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
        }
    }
}
