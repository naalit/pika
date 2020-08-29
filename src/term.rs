//! We have three IRs in the frontend:
//! - `Pre` or presyntax is what we get from the parser.
//! - `Term` or core syntax is what we get after elaborating (name resolution, type checking, etc.).
//! - `Val` is a value, where local variables are inlined and beta reduction is performed.
//!   - If we inline all variables, it's a `IVal` (for "inlined"), otherwise it's a `UVal` (for "un-inlined").
//!   - We try unification first on `UVal`s, and if that fails we try it on `IVal`s.
//!   - We can get an `IVal` from a `UVal`, but not vice versa.
use crate::error::*;
use crate::query::*;

pub use std::collections::VecDeque;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Icit {
    Impl,
    Expl,
}

/// Presyntax should always come with a span, for error reporting.
pub type Pre = Spanned<Pre_>;
/// This makes what fields are for clearer.
///
/// Note that in a lot of places where types are optional in the grammar, they're required in the presyntax.
/// This is intentional: when the type is left out, it gets replaced with `Hole`, which is then solved with unification.
pub type PreTy = Pre;
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pre_ {
    Type,
    Var(Name),
    Lam(Name, Icit, PreTy, Pre),
    Pi(Name, Icit, PreTy, PreTy),
    /// A `Fun` is a special case of `Pi` where there's no name (or `"_"`) and it's explicit.
    /// It could be represented as `Pi`, but it's so common that this is worth it, for better performance and errors.
    Fun(PreTy, PreTy),
    App(Icit, Pre, Pre),
    Do(Vec<PreDef>),
    Struct(Vec<PreDef>),
    Hole,
}

/// The return type of a constructor is optional even here, since the behaviour is different.
/// When a constructor return type is missing, we don't unify it, we use the type declaration,
/// and add the type parameters declared there as implicit parameters to the constructor.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PreCons(pub Name, pub Vec<(Name, Icit, PreTy)>, pub Option<PreTy>);
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PreDef {
    Fun(Name, Vec<(Name, Icit, PreTy)>, PreTy, Pre),
    Val(Name, PreTy, Pre),
    Type(Name, Vec<(Name, Icit, PreTy)>, Vec<PreCons>),
    Impl(Option<Name>, PreTy, Pre),
    Expr(Pre),

    // Declarations
    FunDec(Name, Vec<(Name, Icit, PreTy)>, PreTy),
    ValDec(Name, PreTy),
}
impl PreDef {
    pub fn name(&self) -> Option<Name> {
        match self {
            PreDef::Fun(n, _, _, _)
            | PreDef::Val(n, _, _)
            | PreDef::Type(n, _, _)
            | PreDef::FunDec(n, _, _)
            | PreDef::ValDec(n, _) => Some(*n),
            PreDef::Impl(n, _, _) => *n,
            PreDef::Expr(_) => None,
        }
    }
    /// This picks the best span for refering to the definition
    pub fn span(&self) -> Span {
        match self {
            // TODO spanned names
            PreDef::Fun(_, _, _, t) => t.span(),
            PreDef::Val(_, _, t) => t.span(),
            PreDef::Type(_, _, _) => todo!("spanned names"),
            PreDef::Impl(_, _, t) => t.span(),
            PreDef::Expr(t) => t.span(),
            PreDef::FunDec(_, _, t) => t.span(),
            PreDef::ValDec(_, t) => t.span(),
        }
    }
}

// TODO NonZeroU32's
/// A De Bruijn index, representing the number of enclosing lambda abstractions before we get to the one that binds the variable.
///
/// `\x.(\y.yx)x` is `\.(\.01)0`
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Ix(u32);
/// A De Bruijn level, the opposite of an index.
/// It represents the number of lambda abstractions we have to descend into from the root to get to the one that binds the variable.
///
/// `\x.(\y.yx)x` is `\.(\.10)0`
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Lvl(u32);
impl Ix {
    pub fn zero() -> Self {
        Self(0)
    }

    pub fn inc(self) -> Self {
        Self(self.0 + 1)
    }

    pub fn dec(self) -> Self {
        Self(self.0 - 1)
    }

    /// Converts an index to a level, given the number of enclosing abstractions.
    pub fn to_lvl(self, enclosing: Lvl) -> Lvl {
        assert!(
            self.0 <= enclosing.0,
            "Can't access a variable that hasn't been bound yet!"
        );
        // If we go up `self` levels, we'll still be this many away from the root.
        Lvl(enclosing.0 - self.0)
    }
}
impl Lvl {
    pub fn zero() -> Self {
        Self(0)
    }

    pub fn inc(self) -> Self {
        Self(self.0 + 1)
    }

    pub fn dec(self) -> Self {
        Self(self.0 - 1)
    }

    /// Converts a level to an index, given the number of enclosing abstractions.
    pub fn to_ix(self, enclosing: Lvl) -> Ix {
        assert!(
            self.0 <= enclosing.0,
            "Can't access a variable that hasn't been bound yet!"
        );
        // If we go down `self` levels from the root, there are still this many levels between us and the binding.
        Ix(enclosing.0 - self.0)
    }

    pub fn apply_meta(self, t: Term) -> Term {
        (0..self.0)
            .map(|i| Term::Var(Var::Local(Ix(i))))
            .fold(t, |f, x| Term::App(Icit::Expl, Box::new(f), Box::new(x)))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Meta {
    Type(PreDefId),
    /// The local meta index is a u16 so that this type fits in a word.
    /// So no more than 65535 metas are allowed per definition, which is probably fine.
    Local(DefId, u16),
}

pub type Ty = Term;
/// The core syntax. This uses `Ix`, De Bruijn indices.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Type,
    Var(Var<Ix>),
    Lam(Icit, Box<Term>),
    Pi(Icit, Box<Ty>, Box<Ty>),
    Fun(Box<Ty>, Box<Ty>),
    App(Icit, Box<Term>, Box<Term>),
    /// There was a type error somewhere, and we already reported it, so we want to continue as much as we can.
    Error,
}

// -- values --

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Env {
    /// Since locals are De Bruijn indices, we store a `VecDeque`, push to the front and index normally.
    /// TODO try (A)Rc<Val> here, because closures?
    /// Or `im::Vector`?
    /// When elaborating, we often want to evaluate something without any locals, or just add one or two at the front.
    /// To make that efficient, we leave off the tail of `None`s, and if an index goes past the length, it's `None`.
    vals: VecDeque<Option<Val>>,
    size: Lvl,
}
impl Env {
    pub fn new(size: Lvl) -> Self {
        Env {
            vals: VecDeque::new(),
            size,
        }
    }

    pub fn get(&self, i: Ix) -> Option<&Val> {
        // Option<&Option<Val>>
        self.vals
            .get(i.0 as usize)
            // Option<Option<&Val>>
            .map(Option::as_ref)
            .flatten()
    }

    /// If it's not present, returns a local variable value
    pub fn val(&self, i: Ix) -> Val {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .unwrap_or(Val::local(i.to_lvl(self.size)))
    }

    pub fn push(&mut self, v: Option<Val>) {
        self.size = self.size.inc();
        if v.is_some() || !self.vals.is_empty() {
            self.vals.push_front(v);
        }
    }
}

use crate::elaborate::MCxt;

/// A closure, representing a term that's waiting for an argument to be evaluated.
/// It's used in both lambdas and pi types.
///
/// Note that it stores a `Box<Env>`, because we store it inline in `Val` and the `VecDeque` that `Env` uses is actually very big.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Clos(pub Box<Env>, pub Box<Term>);
impl Clos {
    pub fn env_size(&self) -> Lvl {
        self.0.size
    }

    /// Quotes the closure back into a `Term`, but leaves it behind the lambda, so don't extract it.
    pub fn quote(self, mcxt: &MCxt) -> Term {
        // We only need to do eval-quote if we've captured variables, which isn't that often
        // Otherwise, we just need to inline meta solutions
        if self.0.vals.is_empty() {
            // TODO should this return a box and reuse it?
            self.1.inline_metas(mcxt, self.0.size)
        } else {
            use crate::evaluate::{evaluate, quote};
            let Clos(mut env, t) = self;
            env.push(None);
            // `inc()` since it's wrapped in a lambda
            quote(evaluate(*t, &env, mcxt), env.size.inc(), mcxt)
        }
    }

    /// Equivalent to `self.apply(Val::local(self.env_size()), mcxt)`
    pub fn vquote(self, mcxt: &MCxt) -> Val {
        use crate::evaluate::evaluate;
        let Clos(mut env, t) = self;
        env.push(None);
        evaluate(*t, &env, mcxt)
    }

    pub fn apply(self, arg: Val, mcxt: &MCxt) -> Val {
        use crate::evaluate::evaluate;
        let Clos(mut env, t) = self;
        env.push(Some(arg));
        evaluate(*t, &env, mcxt)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Var<Local> {
    Local(Local),
    Top(DefId),
    Rec(PreDefId),
    Meta(Meta),
}

pub type Spine = Vec<(Icit, Val)>;

pub type VTy = Val;
/// A value in normal(-ish) form.
/// Values are never behind any abstractions, since those use `Clos` to store a `Term`.
/// So, values use `Lvl`, De Bruijn levels, which make things like unification easier.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Val {
    Type,
    /// The spine are arguments applied in order. It can be empty.
    App(Var<Lvl>, Spine),
    Lam(Icit, Clos),
    Pi(Icit, Box<VTy>, Clos),
    Fun(Box<VTy>, Box<VTy>),
    Error,
}
impl Val {
    pub fn local(lvl: Lvl) -> Val {
        Val::App(Var::Local(lvl), Vec::new())
    }

    pub fn top(def: DefId) -> Val {
        Val::App(Var::Top(def), Vec::new())
    }

    pub fn rec(id: PreDefId) -> Val {
        Val::App(Var::Rec(id), Vec::new())
    }

    pub fn meta(meta: Meta) -> Val {
        Val::App(Var::Meta(meta), Vec::new())
    }
}
