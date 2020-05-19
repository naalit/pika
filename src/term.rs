use crate::bicheck::TypeError;
use crate::common::*;

use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Env {
    types: HashMap<Sym, STerm>,
    vals: HashMap<Sym, STerm>,
    count: usize,
}
// impl std::fmt::Display for Env {
//     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//         writeln!(f, "{{")?;
//         for (k, v) in self.types.iter() {
//             writeln!(f, "\t{} : {}", INTERN.read().unwrap().resolve(*k).unwrap(), **v)?;
//         }
//         for (k, v) in self.vals.iter() {
//             writeln!(f, "\t{} = {}", INTERN.read().unwrap().resolve(*k).unwrap(), **v)?;
//         }
//         write!(f, "  }}")
//     }
// }
impl Env {
    pub fn remove_ty(&mut self, k: Sym) -> Option<STerm> {
        self.types.remove(&k)
    }
    pub fn insert_ty(&mut self, k: Sym, v: STerm) -> Option<STerm> {
        self.types.insert(k, v)
    }
    pub fn ty(&self, k: Sym) -> Option<&STerm> {
        self.types.get(&k)
    }
    pub fn remove_val(&mut self, k: Sym) -> Option<STerm> {
        self.vals.remove(&k)
    }
    pub fn insert_val(&mut self, k: Sym, v: STerm) -> Option<STerm> {
        self.vals.insert(k, v)
    }
    pub fn val(&self, k: Sym) -> Option<&STerm> {
        self.vals.get(&k)
    }

    /// Temporarily sets k : v and runs f; essentially scoping helper
    pub fn with_ty<T>(&mut self, k: Sym, v: STerm, f: impl FnOnce(&mut Env) -> T) -> T {
        let old = self.remove_ty(k);
        self.insert_ty(k, v);
        let ret = f(self);
        self.remove_ty(k);
        if let Some(v) = old {
            self.insert_ty(k, v);
        }
        ret
    }
    /// Temporarily sets k = v and runs f; essentially scoping helper
    pub fn with_val<T>(&mut self, k: Sym, v: STerm, f: impl FnOnce(&mut Env) -> T) -> T {
        let old = self.remove_val(k);
        self.insert_val(k, v);
        let ret = f(self);
        self.remove_val(k);
        if let Some(v) = old {
            self.insert_val(k, v);
        }
        ret
    }
    pub fn new() -> Self {
        Env {
            types: HashMap::new(),
            vals: HashMap::new(),
            count: 0,
        }
    }
    // pub fn next_tv(&mut self) -> Sym {
    //     let mut intern = INTERN.write().unwrap();
    //     let mut s = intern.get_or_intern(format!("t{}", self.1));
    //     while self.types.contains_key(&s) {
    //         self.1 += 1;
    //         s = intern.get_or_intern(format!("t{}", self.1));
    //     }
    //     self.1 += 1;
    //     s
    // }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Builtin {
    Int,
}

pub type STerm = crate::error::Spanned<Term>;

impl STerm {
    /// *DOES NOT* currently do beta-reduction or anything, just reduces variables in `env`
    // pub fn reduce(&self, env: &mut Env) -> Self {
    //     let mut x = self.copy_span((**self).clone());
    //     match &mut *x {
    //         Term::Var(v) => if let Some(v) = env.val(*v) {
    //             x = v.clone();
    //         }
    //         Term::App(f, x) => {
    //             *f = f.reduce(env);
    //             *x = x.reduce(env);
    //         }
    //         Term::Fun(args, body) => {
    //             *args = args.reduce(env);
    //             let mut menv = env.clone();
    //             for i in env.vals.keys() {
    //                 if args.defines(*i) {
    //                     menv.remove_val(*i);
    //                 }
    //             }
    //             *body = body.reduce(&mut menv);
    //         }
    //         Term::Binder(_, t) => *t = t.reduce(env),
    //         Term::Pair(x, y) => {
    //             *x = x.reduce(env);
    //             let mut menv = env.clone();
    //             for i in env.vals.keys() {
    //                 if x.defines(*i) {
    //                     menv.remove_val(*i);
    //                 }
    //             }
    //             *y = y.reduce(&mut menv);
    //         }
    //         _ => (),
    //     }
    //     x
    // }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality - yes, Term implements PartialEq, but *please do not* use that
    pub fn subtype_of(&self, sup: &STerm, env: &Env) -> Result<bool, TypeError> {
        Ok(match (&**self, &**sup) {
            (x, y) if x == y && x.is_type(env) => true,
            // (Type, Type) <= Type
            (_, Term::Type) if self.is_type_type(env) => true,
            (Term::Pair(ax, ay), Term::Pair(bx, by)) => {
                ax.subtype_of(bx, env)? && ay.subtype_of(by, env)?
            }
            // (Type -> (Type, Type)) <= ((Type, Type) -> Type)
            (Term::Fun(ax, ay), Term::Fun(bx, by)) => {
                bx.subtype_of(ax, env)? && ay.subtype_of(by, env)?
            }
            (Term::Var(x), _) => {
                if let Some(x) = env.val(*x) {
                    x.subtype_of(sup, env)?
                } else {
                    return Err(TypeError::NotFound(self.copy_span(*x)));
                }
            }
            (_, Term::Var(x)) => {
                if let Some(x) = env.val(*x) {
                    self.subtype_of(x, env)?
                } else {
                    return Err(TypeError::NotFound(self.copy_span(*x)));
                }
            }
            // the annotation should always be Type here
            (Term::Binder(_, t), _) => t.subtype_of(sup, env)?,
            _ => false,
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Unit,                   // ()
    Let(Sym, STerm, STerm), // let x = y in z
    Binder(Sym, STerm),     // x: T
    Var(Sym),               // a
    I32(i32),               // 3
    Type,                   // Type
    Builtin(Builtin),       // Int
    Fun(STerm, STerm),      // fn a => x
    App(STerm, STerm),      // f x
    Pair(STerm, STerm),     // x, y
}
impl Term {
    /// Is `x : self` valid?
    fn is_type(&self, env: &Env) -> bool {
        match self {
            Term::Unit => true,
            Term::Type => true,
            Term::Builtin(Builtin::Int) => true,
            Term::Pair(x, y) => x.is_type(env) && y.is_type(env),
            // The binder really evaluates to the type
            Term::Binder(_, _) => true,
            Term::Var(x) => {
                env.val(*x).map_or(false, |x| x.is_type(env))
                    || env.ty(*x).map_or(false, |x| x.is_type_type(env))
            }
            // uh... maybe? TODO figure out
            Term::Fun(x, t) => true,
            _ => false,
        }
    }

    /// Is `x : T : self` valid? This should mean it's a type all the way down, i.e. `x : T1 : T2 ... TN : self` for all N
    fn is_type_type(&self, env: &Env) -> bool {
        match self {
            // () : () : ()
            Term::Unit => true,
            Term::Type => true,
            // (Type, Type)
            Term::Pair(x, y) => x.is_type_type(env) && y.is_type_type(env),
            Term::Binder(_, t) => t.is_type_type(env),
            Term::Var(x) => env.val(*x).map_or(false, |x| x.is_type_type(env)),
            _ => false,
        }
    }
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
            Term::Binder(x, t) => write!(f, "{}: {}", b.resolve(*x), WithContext(b, &**t)),
            Term::Var(s) => write!(f, "{}", b.resolve(*s)),
            Term::I32(i) => write!(f, "{}", i),
            Term::Type => write!(f, "Type"),
            Term::Builtin(b) => write!(f, "{:?}", b),
            Term::Fun(x, y) => write!(f, "fn {} => {}", WithContext(b, &**x), WithContext(b, &**y)),
            Term::App(x, y) => write!(f, "{}({})", WithContext(b, &**x), WithContext(b, &**y)),
            Term::Pair(x, y) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
        }
    }
}
impl Term {
    /// *Type* the definitions in `self`
    pub fn apply_defs(&self, env: &mut Env) {
        match self {
            Term::Binder(x, t) => {
                env.insert_ty(*x, t.clone());
            }
            Term::Let(_, t, u) | Term::App(t, u) | Term::Pair(t, u) => {
                t.apply_defs(env);
                u.apply_defs(env);
            }
            _ => (),
        }
    }

    pub fn occurs(&self, v: Sym) -> bool {
        match self {
            Term::Var(x) => *x == v,
            // non-recursive, for now at least
            Term::Let(x, t, u) => t.occurs(v) || u.occurs(v),
            Term::Binder(_, t) => t.occurs(v),
            Term::Fun(u, t) | Term::Pair(u, t) => (u.occurs(v) || t.occurs(v)),
            Term::App(x, y) => x.occurs(v) || y.occurs(v),
            _ => false,
        }
    }

    pub fn sub(&mut self, from: Sym, to: &Term) {
        match self {
            Term::Var(x) if *x == from => *self = to.clone(),
            Term::Fun(u, t) | Term::Pair(u, t) => {
                u.sub(from, to);
                t.sub(from, to);
            }
            Term::Let(x, t, u) => {
                t.sub(from, to);
                if *x != from {
                    u.sub(from, to);
                }
            }
            Term::Binder(_, t) => t.sub(from, to),
            Term::App(x, y) => {
                x.sub(from, to);
                y.sub(from, to);
            }
            _ => (),
        }
    }
}
