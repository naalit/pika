//! We have three IRs in the frontend:
//! - `Pre` or presyntax is what we get from the parser.
//! - `Term` or core syntax is what we get after elaborating (name resolution, type checking, etc.).
//! - `Val` is a value, where beta reduction and associated substitution has been performed.
use crate::common::*;
use crate::elaborate::MCxt;

/// Records the reason we introduced a meta, used when reporting an unsolved meta to the user.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum MetaSource {
    ImplicitParam(Name),
    LocalType(Name),
    Hole,
    HoleType,
}

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
    Do(Vec<PreDefAn>),
    Struct(Vec<PreDefAn>),
    Hole(MetaSource),
}

/// What can go inside of `@[whatever]`; currently, attributes are only used for benchmarking and user-defined attributes don't exist.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Attribute {
    Normalize,
    Elaborate,
}
impl Attribute {
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "normalize" => Ok(Attribute::Normalize),
            "elaborate" => Ok(Attribute::Elaborate),
            _ => Err(format!("unknown attribute: @[{}]", s)),
        }
    }
}

/// A `PreDef`, plus any attributes that were applied to that definition.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PreDefAn {
    pub attributes: Vec<Attribute>,
    pub inner: PreDef,
}
impl std::ops::Deref for PreDefAn {
    type Target = PreDef;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// The return type of a constructor is optional even here, since the behaviour is different.
/// When a constructor return type is missing, we don't unify it, we use the type declaration,
/// and add the type parameters declared there as implicit parameters to the constructor.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PreCons(pub Name, pub Vec<(Name, Icit, PreTy)>, pub Option<PreTy>);
/// A definition, declaration, or statement - anything that can appear in a `do`, `struct`, or `sig` block.
///
/// `PreDef` doesn't keep track of attributes; see `PreDefAn` for that.
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
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
pub struct Ix(u32);
/// A De Bruijn level, the opposite of an index.
/// It represents the number of lambda abstractions we have to descend into from the root to get to the one that binds the variable.
///
/// `\x.(\y.yx)x` is `\.(\.10)0`
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
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
            "Can't access a variable (index {}) that hasn't been bound yet (enclosing = {})!",
            self.0,
            enclosing.0,
        );
        // If we go up `self` levels, we'll still be this many away from the root.
        Lvl(enclosing.0 - self.0)
    }
}
impl Lvl {
    pub fn max(self, o: Lvl) -> Lvl {
        Lvl(self.0.max(o.0))
    }

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
            "Can't access a variable (level {}) that hasn't been bound yet (enclosing = {})!",
            self.0,
            enclosing.0,
        );
        // If we go down `self` levels from the root, there are still this many levels between us and the binding.
        Ix(enclosing.0 - self.0)
    }

    pub fn apply_meta(self, t: Term) -> Term {
        (0..self.0)
            .rev()
            .map(|i| Term::Var(Var::Local(Ix(i))))
            .fold(t, |f, x| Term::App(Icit::Expl, Box::new(f), Box::new(x)))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
pub enum Meta {
    /// A meta representing the type of a definition that doesn't have one yet, used for (mutual) recursion.
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
    Lam(Name, Icit, Box<Ty>, Box<Term>),
    Pi(Name, Icit, Box<Ty>, Box<Ty>),
    Fun(Box<Ty>, Box<Ty>),
    App(Icit, Box<Term>, Box<Term>),
    /// There was a type error somewhere, and we already reported it, so we want to continue as much as we can.
    Error,
}

impl Term {
    pub fn ty(&self, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Term::Type | Term::Pi(_, _, _, _) | Term::Fun(_, _) => Val::Type,
            Term::Var(v) => match *v {
                Var::Local(i) => mcxt.local_ty(i, db).clone(),
                Var::Top(i) => (*db.elaborate_def(i).unwrap().typ).clone(),
                Var::Rec(_) => todo!("find meta solution"),
                Var::Meta(_) => todo!("find meta solution"),
            },
            Term::Lam(n, i, ty, body) => {
                let ty = (**ty).clone().evaluate(&mcxt.env(), mcxt);
                Val::Pi(
                    *i,
                    Box::new(ty.clone()),
                    Box::new(Clos(
                        mcxt.env(),
                        {
                            let mut mcxt = mcxt.clone();
                            mcxt.define(*n, NameInfo::Local(ty), db);
                            body.ty(&mcxt, db).quote(mcxt.size, &mcxt)
                        },
                        *n,
                    )),
                )
            }
            Term::App(_, f, x) => match f.ty(mcxt, db) {
                Val::Fun(_, to) => *to,
                Val::Pi(_, _, cl) => cl.apply((**x).clone().evaluate(&mcxt.env(), mcxt), mcxt),
                // It might be a name that refers to a function type, so we need to inline it
                Val::App(h, sp, g) => match g.resolve(h, sp, mcxt.size, db, mcxt) {
                    Some(Val::Fun(_, to)) => *to,
                    Some(Val::Pi(_, _, cl)) => {
                        cl.apply((**x).clone().evaluate(&mcxt.env(), mcxt), mcxt)
                    }
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            Term::Error => Val::Error,
        }
    }
}

/// Like `Names`, but generalized to arbitrary types.
#[derive(Clone, Default, Debug)]
pub struct IVec<T>(VecDeque<T>);
impl<T> IVec<T> {
    pub fn new() -> Self {
        IVec(VecDeque::new())
    }

    pub fn get(&self, ix: Ix) -> &T {
        self.0.get(ix.0 as usize).unwrap_or_else(|| {
            panic!(
                "Tried to access ix {} of IVec but size is {}",
                ix.0,
                self.0.len()
            )
        })
    }

    pub fn add(&mut self, n: T) {
        self.0.push_front(n);
    }

    pub fn remove(&mut self) -> Option<T> {
        self.0.pop_front()
    }

    pub fn size(&self) -> Lvl {
        Lvl(self.0.len() as u32)
    }
}

// -- pretty printing --

pub struct Names(VecDeque<Name>);
impl Names {
    pub fn new(mut cxt: Cxt, db: &dyn Compiler) -> Names {
        let mut v = VecDeque::new();
        while let MaybeEntry::Yes(CxtEntry {
            name, info, rest, ..
        }) = db.lookup_cxt_entry(cxt)
        {
            cxt = rest;
            match info {
                NameInfo::Local(_) => v.push_back(name),
                _ => (),
            }
        }
        Names(v)
    }
    pub fn get(&self, ix: Ix) -> Name {
        self.0[ix.0 as usize]
    }
    pub fn disamb(&self, n: Name, db: &dyn Compiler) -> Name {
        // Disambiguate names by adding ' at the end
        let mut n = n;
        while self.0.iter().any(|x| *x == n) {
            let mut s = n.get(db);
            s.push('\'');
            n = db.intern_name(s);
        }
        n
    }
    pub fn add(&mut self, n: Name) {
        self.0.push_front(n);
    }
    pub fn remove(&mut self) {
        self.0.pop_front();
    }
}

impl Term {
    pub fn pretty(&self, db: &dyn Compiler, names: &mut Names) -> Doc {
        match self {
            Term::Type => Doc::start("Type"),
            Term::Var(v) => match v {
                Var::Local(ix) => Doc::start(names.get(*ix).get(db)),
                Var::Top(id) => Doc::start(
                    db.lookup_intern_predef(db.lookup_intern_def(*id).0)
                        .name()
                        .unwrap()
                        .get(db),
                ),
                Var::Rec(id) => Doc::start(db.lookup_intern_predef(*id).name().unwrap().get(db)),
                Var::Meta(m) => match m {
                    Meta::Type(id) => Doc::start("<type of ")
                        .add(db.lookup_intern_predef(*id).name().unwrap().get(db))
                        .add(">"),
                    Meta::Local(def, id) => Doc::none().debug(def).add("?").add(id),
                },
            },
            Term::Lam(n, i, _ty, t) => {
                let n = names.disamb(*n, db);
                {
                    names.add(n);
                    let r = match i {
                        Icit::Impl => Doc::start("\\[").add(n.get(db)).add("]"),
                        Icit::Expl => Doc::start("\\").add(n.get(db)),
                    }
                    .add(". ")
                    .chain(t.pretty(db, names))
                    .prec(Prec::Term);
                    names.remove();
                    r
                }
            }
            Term::Pi(n, i, from, to) => {
                let n = names.disamb(*n, db);
                {
                    let r = match i {
                        Icit::Impl => Doc::start("[")
                            .add(n.get(db))
                            .add(" : ")
                            .chain(from.pretty(db, names))
                            .add("]"),
                        Icit::Expl => Doc::start("(")
                            .add(n.get(db))
                            .add(" : ")
                            .chain(from.pretty(db, names))
                            .add(")"),
                    };
                    names.add(n);
                    let r = r
                        .space()
                        .add("->")
                        .space()
                        .chain(to.pretty(db, names))
                        .prec(Prec::Term);
                    names.remove();
                    r
                }
            }
            Term::Fun(from, to) => from
                .pretty(db, names)
                .nest(Prec::App)
                .space()
                .add("->")
                .space()
                .chain(to.pretty(db, names))
                .prec(Prec::Term),
            Term::App(i, f, x) => f
                .pretty(db, names)
                .nest(Prec::App)
                .space()
                .chain(match i {
                    Icit::Impl => Doc::start("[").chain(x.pretty(db, names)).add("]"),
                    Icit::Expl => x.pretty(db, names).nest(Prec::Atom),
                })
                .prec(Prec::App),
            Term::Error => Doc::start("<error>"),
        }
    }
}

// -- values --

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Env {
    /// Since locals are De Bruijn indices, we store a `VecDeque`, push to the front and index normally.
    /// When elaborating, we often want to evaluate something without any locals, or just add one or two at the front.
    /// To make that efficient, we leave off the tail of `None`s, and if an index goes past the length, it's `None`.
    vals: VecDeque<Option<Arc<Val>>>,
    pub size: Lvl,
}
impl Env {
    pub fn inline_metas(&mut self, mcxt: &MCxt) {
        for i in &mut self.vals {
            if let Some(x) = i {
                *x = Arc::new((**x).clone().inline_metas(mcxt));
            }
        }
    }

    pub fn new(size: Lvl) -> Self {
        Env {
            vals: VecDeque::new(),
            size,
        }
    }

    pub fn get(&self, i: Ix) -> Option<&Val> {
        // Option<&Option<Arc<Val>>>
        self.vals
            .get(i.0 as usize)
            // Option<Option<&Arc<Val>>>
            .map(Option::as_ref)
            .flatten()
            .map(Arc::as_ref)
    }

    /// If it's not present, returns a local variable value
    pub fn val(&self, i: Ix) -> Val {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .map(Val::Arc)
            .unwrap_or(Val::local(i.to_lvl(self.size)))
    }

    pub fn push(&mut self, v: Option<Val>) {
        self.size = self.size.inc();
        if v.is_some() || !self.vals.is_empty() {
            self.vals.push_front(v.map(Arc::new));
        }
    }
}

/// A closure, representing a term that's waiting for an argument to be evaluated.
/// It's used in both lambdas and pi types.
///
/// Note that a `Clos` is very big (contains an inline `Env` and `Term`), so storing it behind a Box is advised.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Clos(pub Env, pub Term, pub Name);
impl Clos {
    pub fn env_size(&self) -> Lvl {
        self.0.size
    }

    /// Quotes the closure back into a `Term`, but leaves it behind the lambda.
    /// So `enclosing` is the number of abstractions enclosing the *lambda*, it doesn't include the lambda.
    pub fn quote(self, enclosing: Lvl, mcxt: &MCxt) -> Term {
        // We only need to do eval-quote if we've captured variables, which isn't that often
        // Otherwise, we just need to inline meta solutions
        // TODO is this still true?
        if self.0.vals.is_empty() {
            // TODO should this return a box and reuse it?
            self.1.inline_metas(mcxt, self.0.size)
        } else {
            let Clos(mut env, t, _) = self;
            env.push(Some(Val::local(enclosing.inc())));
            t.evaluate(&env, mcxt).quote(enclosing.inc(), mcxt)
        }
    }

    /// Equivalent to `self.apply(Val::local(l), mcxt)`
    pub fn vquote(self, l: Lvl, mcxt: &MCxt) -> Val {
        let Clos(mut env, t, _) = self;
        env.push(Some(Val::local(l)));
        t.evaluate(&env, mcxt)
    }

    pub fn apply(self, arg: Val, mcxt: &MCxt) -> Val {
        let Clos(mut env, t, _) = self;
        env.push(Some(arg));
        t.evaluate(&env, mcxt)
    }
}

/// The head of an application in a `Val`, which is some sort of variable which may or may not have a value yet.
///
/// The `Local` type parameter should be the type of a local variable, either `Lvl` or `Ix`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Var<Local> {
    Local(Local),
    Top(DefId),
    Rec(PreDefId),
    Meta(Meta),
}

pub type Spine = Vec<(Icit, Val)>;

/// A `Glued` represents what a `Val::App` evaluates to.
/// Each `Val::App` has a `Glued` associated with it, which lazily inlines and beta-reduces the value.
/// It caches the value for future uses.
///
/// The most common place where a `Glued` is resolved in during unification:
/// we try to unify without resolving `Glued`s, but if that fails, we try again with resolving them.
#[derive(Clone, Debug)]
pub struct Glued(Arc<RwLock<Option<Val>>>);

/// Always returns true, should only be used as part of <Val as PartialEq>
impl PartialEq for Glued {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for Glued {}
/// Does nothing, should only be used as part of <Val as Hash>
impl std::hash::Hash for Glued {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Glued {
    pub fn new() -> Self {
        Glued(Arc::new(RwLock::new(None)))
    }

    /// Like `resolve()`, but only inlines metas, not definitions. So, it doesn't need a database or quote level.
    pub fn resolve_meta(&self, h: Var<Lvl>, sp: impl IntoOwned<Spine>, mcxt: &MCxt) -> Option<Val> {
        let guard = self.0.read().unwrap();
        if let Some(v) = &*guard {
            Some(v.clone())
        } else {
            drop(guard);
            match h {
                // We won't inline the local
                Var::Local(_) => None,
                // If we inlined the Rec, it would probably lead to infinite recursion
                Var::Rec(_) => None,
                Var::Top(_) => None,
                Var::Meta(m) => {
                    if let Some(val) = mcxt.get_meta(m) {
                        let val = sp
                            .into_owned()
                            .into_iter()
                            .fold(val, |f, (i, x)| f.app(i, x, mcxt));
                        let val = Val::Arc(Arc::new(val));
                        *self.0.write().unwrap() = Some(val.clone());
                        Some(val)
                    } else {
                        None
                    }
                }
            }
        }
    }

    /// Resolves the `Glued`: returns a `Val::Arc` to the cached value if available, otherwise inlines the head and beta-reduces, returning the result.
    /// If the head can't be inlined, e.g. because it's a parameter, returns None.
    pub fn resolve(
        &self,
        h: Var<Lvl>,
        sp: impl IntoOwned<Spine>,
        l: Lvl,
        db: &dyn Compiler,
        mcxt: &MCxt,
    ) -> Option<Val> {
        let guard = self.0.read().unwrap();
        if let Some(v) = &*guard {
            Some(v.clone())
        } else {
            drop(guard);
            match h {
                // We won't inline the local
                Var::Local(_) => None,
                // If we inlined the Rec, it would probably lead to infinite recursion
                Var::Rec(_) => None,
                Var::Top(def) => {
                    let val = db.elaborate_def(def).ok()?.term;
                    let val = (*val).clone();
                    let val = val.evaluate(&Env::new(l), mcxt);
                    let val = sp
                        .into_owned()
                        .into_iter()
                        .fold(val, |f, (i, x)| f.app(i, x, mcxt));
                    let val = Val::Arc(Arc::new(val));
                    *self.0.write().unwrap() = Some(val.clone());
                    Some(val)
                }
                Var::Meta(m) => {
                    if let Some(val) = mcxt.get_meta(m) {
                        let val = sp
                            .into_owned()
                            .into_iter()
                            .fold(val, |f, (i, x)| f.app(i, x, mcxt));
                        let val = Val::Arc(Arc::new(val));
                        *self.0.write().unwrap() = Some(val.clone());
                        Some(val)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

pub type VTy = Val;
/// A value in normal(-ish) form.
/// Values are never behind any abstractions, since those use `Clos` to store a `Term`.
/// So, values use `Lvl`, De Bruijn levels, which make things like unification easier.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Val {
    Type,
    Arc(Arc<Val>),
    /// The spine are arguments applied in order. It can be empty.
    App(Var<Lvl>, Spine, Glued),
    Lam(Icit, Box<VTy>, Box<Clos>),
    Pi(Icit, Box<VTy>, Box<Clos>),
    Fun(Box<VTy>, Box<VTy>),
    Error,
}
impl Val {
    pub fn pretty(&self, db: &dyn Compiler, mcxt: &MCxt) -> Doc {
        self.clone()
            .inline_metas(mcxt)
            .quote(mcxt.size, mcxt)
            .pretty(db, &mut Names::new(mcxt.cxt, db))
    }

    /// Unwraps any top-level `Val::Arc`s, so you don't have to recurse to deal with that case when matching on a reference.
    pub fn unarc(&self) -> &Val {
        match self {
            Val::Arc(x) => x.unarc(),
            x => x,
        }
    }

    pub fn local(lvl: Lvl) -> Val {
        Val::App(Var::Local(lvl), Vec::new(), Glued::new())
    }

    pub fn top(def: DefId) -> Val {
        Val::App(Var::Top(def), Vec::new(), Glued::new())
    }

    pub fn rec(id: PreDefId) -> Val {
        Val::App(Var::Rec(id), Vec::new(), Glued::new())
    }

    pub fn meta(meta: Meta) -> Val {
        Val::App(Var::Meta(meta), Vec::new(), Glued::new())
    }
}
