use string_interner::{StringInterner, DefaultStringInterner, Sym};
use std::sync::RwLock;

lazy_static::lazy_static! {
    pub static ref INTERN: RwLock<DefaultStringInterner> = RwLock::new(StringInterner::default());
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Builtin {
    Int,
}

#[derive(Debug, Clone)]
pub enum Term {
    Var(Sym),                   // a
    I32(i32),                   // 3
    Type,                       // Type
    Builtin(Builtin),           // Int
    Fun(Sym, Box<Term>),        // fn a => x
    Arrow(Box<Term>, Box<Term>),// fn x -> y (function type)
    App(Box<Term>, Box<Term>),  // f x
}
impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Term::Var(s) => write!(f, "{}", INTERN.read().unwrap().resolve(*s).unwrap()),
            Term::I32(i) => write!(f, "{}", i),
            Term::Type => write!(f, "Type"),
            Term::Builtin(b) => write!(f, "{:?}", b),
            Term::Fun(x, b) => write!(f, "fn {} => {}", INTERN.read().unwrap().resolve(*x).unwrap(), b),
            Term::Arrow(x, y) => write!(f, "fn {} -> {}", x, y),
            Term::App(x, y) => write!(f, "{}({})", x, y),
        }
    }
}
impl Term {
    pub fn occurs(&self, v: Sym) -> bool {
        match self {
            Term::Var(x) => *x == v,
            Term::Fun(x, t) => *x != v && t.occurs(v),
            Term::Arrow(x, y) => x.occurs(v) || y.occurs(v),
            Term::App(x, y) => x.occurs(v) || y.occurs(v),
            _ => false,
        }
    }

    pub fn sub(&mut self, from: Sym, to: &Term) {
        match self {
            Term::Var(x) if *x == from => *self = to.clone(),
            Term::Fun(x, t) if *x != from => t.sub(from, to),
            Term::Arrow(x, y) | Term::App(x, y) => {
                x.sub(from, to);
                y.sub(from, to);
            }
            _ => (),
        }
    }
}
