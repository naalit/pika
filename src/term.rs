use string_interner::{StringInterner, DefaultStringInterner, Sym};
use std::sync::RwLock;

lazy_static::lazy_static! {
    pub static ref INTERN: RwLock<DefaultStringInterner> = RwLock::new(StringInterner::default());
}

use std::ops::{Deref, DerefMut};
use std::collections::HashMap;

pub struct Env(HashMap<Sym, STerm>, usize);
impl std::fmt::Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for (k, v) in self.0.iter() {
            writeln!(f, "\t{} = {}", INTERN.read().unwrap().resolve(*k).unwrap(), **v)?;
        }
        write!(f, "  }}")
    }
}
impl Env {
    /// Temporarily sets k = v and runs f; essentially scoping helper
    pub fn with<T>(&mut self, k: Sym, v: STerm, f: impl FnOnce(&mut Env) -> T) -> T {
        let old = self.remove(&k);
        self.insert(k, v);
        let ret = f(self);
        self.remove(&k);
        if let Some(v) = old {
            self.insert(k, v);
        }
        ret
    }
    pub fn new() -> Self {
        Env(HashMap::new(), 0)
    }
    pub fn next_tv(&mut self) -> Sym {
        let mut intern = INTERN.write().unwrap();
        let mut s = intern.get_or_intern(format!("t{}", self.1));
        while self.0.contains_key(&s) {
            self.1 += 1;
            s = intern.get_or_intern(format!("t{}", self.1));
        }
        self.1 += 1;
        s
    }
}
impl Deref for Env {
    type Target = HashMap<Sym, STerm>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for Env {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Builtin {
    Int,
}

pub type STerm = crate::error::Spanned<Term>;

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Unit,                       // ()
    Let(Sym, STerm, STerm),// let x = y in z
    Ann(STerm, STerm),  // x: T
    Var(Sym),                   // a
    I32(i32),                   // 3
    Type,                       // Type
    Builtin(Builtin),           // Int
    Fun(Sym, STerm),        // fn a => x
    Arrow(STerm, STerm),// fn x -> y (function type)
    App(STerm, STerm),  // f x
    Pair(STerm, STerm), // x, y
}
impl Term {
    /// Is `x : self` valid?
    fn is_type(&self, env: &Env) -> bool {
        match self {
            Term::Unit => true,
            Term::Type => true,
            Term::Builtin(Builtin::Int) => true,
            Term::Arrow(_, _) => true,
            Term::Pair(x, y) => x.is_type(env) && y.is_type(env),
            Term::Ann(_, t) if **t == Term::Type => true,
            // e.g. (Int, Int) : (Type, Type) should still be a type
            Term::Ann(x, _) => x.is_type(env),
            Term::Var(x) => env.get(x).unwrap().is_type(env),
            _ => false,
        }
    }

    /// Is `x : T : self` valid?
    fn is_type_type(&self, env: &Env) -> bool {
        match self {
            // () : () : ()
            Term::Unit => true,
            Term::Type => true,
            // (Type, Type)
            Term::Pair(x, y) => x.is_type_type(env) && y.is_type_type(env),
            // the annotation should always be Type here
            Term::Ann(x, _) => x.is_type_type(env),
            Term::Var(x) => env.get(x).unwrap().is_type_type(env),
            _ => false,
        }
    }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality - yes, Term implements PartialEq, but *please do not* use that
    pub fn subtype_of(&self, sup: &Term, env: &Env) -> bool {
        match (self, sup) {
            (x, y) if x == y && x.is_type(env) => true,
            // (Type, Type) <= Type
            (_, Term::Type) if self.is_type_type(env) => true,
            (Term::Pair(ax, ay), Term::Pair(bx, by)) => ax.subtype_of(bx, env) && ay.subtype_of(by, env),
            // (Type -> (Type, Type)) <= ((Type, Type) -> Type)
            (Term::Arrow(ax, ay), Term::Arrow(bx, by)) => bx.subtype_of(ax, env) && ay.subtype_of(by, env),
            (Term::Var(x), _) => env.get(x).unwrap().subtype_of(sup, env),
            (_, Term::Var(x)) => self.subtype_of(env.get(x).unwrap(), env),
            // the annotation should always be Type here
            (Term::Ann(x, _), _) => x.subtype_of(sup, env),
            _ => false,
        }
    }
}
impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Term::Unit => write!(f, "()"),
            Term::Let(s, x, y) => write!(f, "let {} = {} in {}", INTERN.read().unwrap().resolve(*s).unwrap(), **x, **y),
            Term::Ann(x, t) => write!(f, "{} : {}", **x, **t),
            Term::Var(s) => write!(f, "{}", INTERN.read().unwrap().resolve(*s).unwrap()),
            Term::I32(i) => write!(f, "{}", i),
            Term::Type => write!(f, "Type"),
            Term::Builtin(b) => write!(f, "{:?}", b),
            Term::Fun(x, b) => write!(f, "fn {} => {}", INTERN.read().unwrap().resolve(*x).unwrap(), **b),
            Term::Arrow(x, y) => write!(f, "fn {} -> {}", **x, **y),
            Term::App(x, y) => write!(f, "{}({})", **x, **y),
            Term::Pair(x, y) => write!(f, "({}, {})", **x, **y),
        }
    }
}
impl Term {
    pub fn occurs(&self, v: Sym) -> bool {
        match self {
            Term::Var(x) => *x == v,
            // non-recursive, for now at least
            Term::Let(x, t, u) => t.occurs(v) || (*x != v && u.occurs(v)),
            Term::Fun(x, t) => *x != v && t.occurs(v),
            Term::Arrow(x, y) => x.occurs(v) || y.occurs(v),
            Term::App(x, y) | Term::Pair(x, y) | Term::Ann(x, y) => x.occurs(v) || y.occurs(v),
            _ => false,
        }
    }

    pub fn sub(&mut self, from: Sym, to: &Term) {
        match self {
            Term::Var(x) if *x == from => *self = to.clone(),
            Term::Fun(x, t) if *x != from => t.sub(from, to),
            Term::Let(x, t, u) => {
                t.sub(from, to);
                if *x != from {
                    u.sub(from, to);
                }
            }
            Term::Arrow(x, y) | Term::App(x, y) | Term::Pair(x, y) | Term::Ann(x, y) => {
                x.sub(from, to);
                y.sub(from, to);
            }
            _ => (),
        }
    }
}
