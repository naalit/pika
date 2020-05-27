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
    Unit,                               // ()
    The(STerm, STerm),                  // the T x
    Binder(Sym, Option<STerm>),         // x: T
    Var(Sym),                           // a
    I32(i32),                           // 3
    Type,                               // Type
    Builtin(Builtin),                   // Int
    Fun(STerm, STerm),                  // fn a => x
    App(STerm, STerm),                  // f x
    Pair(STerm, STerm),                 // x, y
    Struct(StructId, Vec<(Spanned<Sym>, STerm)>), // struct { x := 3 }
    /// We use RawSym's here because it should work on any record with a field named this
    Project(STerm, Spanned<RawSym>), // r.m
}
impl Term {
    pub fn traverse(&self, f: impl Fn(&Term) + Copy) {
        f(self);
        match self {
            Term::The(t, u) | Term::Fun(t, u) | Term::App(t, u) | Term::Pair(t, u) => {
                t.traverse(f);
                u.traverse(f);
            },
            Term::Binder(_, Some(t)) | Term::Project(t, _) => {
                t.traverse(f);
            }
            Term::Struct(_, v) => for (_, t) in v.iter() {
                t.traverse(f);
            }
            _ => (),
        }
    }
}
impl CDisplay for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter, b: &Bindings) -> std::fmt::Result {
        match self {
            Term::Unit => write!(f, "()"),
            Term::The(t, u) => write!(f, "the {} {}", WithContext(b, &**t), WithContext(b, &**u)),
            Term::Binder(x, None) => write!(f, "({}{}:)", b.resolve(*x), x.num()),
            Term::Binder(x, Some(t)) => {
                write!(f, "{}{}: {}", b.resolve(*x), x.num(), WithContext(b, &**t))
            }
            Term::Var(s) => write!(f, "{}{}", b.resolve(*s), s.num()),
            Term::I32(i) => write!(f, "{}", i),
            Term::Type => write!(f, "Type"),
            Term::Builtin(b) => write!(f, "{:?}", b),
            Term::Fun(x, y) => write!(
                f,
                "fun {} => {}",
                WithContext(b, &**x),
                WithContext(b, &**y)
            ),
            Term::App(x, y) => write!(f, "{}({})", WithContext(b, &**x), WithContext(b, &**y)),
            Term::Pair(x, y) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
            Term::Struct(id, v) => {
                write!(f, "struct({}) {{ ", id.num())?;
                for (name, val) in v.iter() {
                    write!(
                        f,
                        "{}{} := {}, ",
                        b.resolve(**name),
                        name.num(),
                        WithContext(b, &**val)
                    )?;
                }
                write!(f, "}}")
            }
            Term::Project(r, m) => write!(f, "({}).{}", WithContext(b, &**r), b.resolve_raw(**m),),
        }
    }
}
