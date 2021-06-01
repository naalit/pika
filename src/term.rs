//! We have three IRs in the frontend:
//! - `Pre` or presyntax is what we get from the parser.
//! - `Term` or core syntax is what we get after elaborating (name resolution, type checking, etc.).
//! - `Val` is a value, where beta reduction and associated substitution has been performed.
use crate::elaborate::{MCxt, MCxtType};
use crate::pattern::Pat;
use crate::{common::*, elaborate::ReasonExpected};

impl Literal {
    pub fn pretty(self, db: &dyn Compiler) -> Doc {
        match self {
            Literal::Positive(i) => Doc::start(i).style(Style::Literal),
            Literal::Negative(i) => Doc::start(i).style(Style::Literal),
            Literal::Float(i) => Doc::start(f64::from_bits(i)).style(Style::Literal),
            Literal::String(n) => Doc::start('"').add(n.get(db).escape_debug()).add('"'),
        }
    }
}

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

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum BinOp {
    Add,    // +
    Sub,    // -
    Mul,    // *
    Div,    // /
    Exp,    // **
    Mod,    // %
    BitAnd, // &
    BitOr,  // |
    BitXor, // ^^
    BitShl, // <<
    BitShr, // >>
    Eq,     // ==
    NEq,    // !=
    Lt,     // <
    Gt,     // >
    Leq,    // <=
    Geq,    // >=
    PipeL,  // <|
    PipeR,  // |>
}
impl BinOp {
    pub fn returns_arg_ty(self) -> bool {
        matches!(
            self,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::Exp
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::BitShl
                | BinOp::BitShr
        )
    }

    pub fn name(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Exp => "**",
            BinOp::Mod => "%",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^^",
            BinOp::BitShl => "<<",
            BinOp::BitShr => ">>",
            BinOp::Eq => "==",
            BinOp::NEq => "!=",
            BinOp::Lt => "<",
            BinOp::Gt => ">",
            BinOp::Leq => "<=",
            BinOp::Geq => ">=",
            BinOp::PipeL => "<|",
            BinOp::PipeR => "|>",
        }
    }

    pub fn ty(self) -> Val {
        use BinOp::*;
        match self {
            // Right now they only work on I32's, not I64's.
            // TODO add traits and make these work on all numbers
            Add | Sub | Mul | Div | Exp | Mod | BitAnd | BitOr | BitXor | BitShl | BitShr => {
                Val::Fun(
                    Box::new(Val::builtin(Builtin::I32, Val::Type)),
                    Box::new(Val::Fun(
                        Box::new(Val::builtin(Builtin::I32, Val::Type)),
                        Box::new(Val::builtin(Builtin::I32, Val::Type)),
                        Vec::new(),
                    )),
                    Vec::new(),
                )
            }
            Eq | NEq | Lt | Gt | Leq | Geq => Val::Fun(
                Box::new(Val::builtin(Builtin::I32, Val::Type)),
                Box::new(Val::Fun(
                    Box::new(Val::builtin(Builtin::I32, Val::Type)),
                    Box::new(Val::builtin(Builtin::Bool, Val::Type)),
                    Vec::new(),
                )),
                Vec::new(),
            ),
            // TODO: `(<<): [t] [P: t -> Type] (f : (x : t) -> P x) (x : t) -> P x`
            PipeL | PipeR => todo!("pipes"),
        }
    }

    pub fn ret_ty(self) -> Option<Val> {
        match self {
            BinOp::Eq | BinOp::NEq | BinOp::Lt | BinOp::Gt | BinOp::Leq | BinOp::Geq => {
                Some(Val::builtin(Builtin::Bool, Val::Type))
            }
            _ => None,
        }
    }
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
    Pi(Name, Icit, PreTy, PreTy, Vec<Pre>),
    /// A `Fun` is a special case of `Pi` where there's no name (or `"_"`) and it's explicit.
    /// It could be represented as `Pi`, but it's so common that this is worth it, for better performance and errors.
    Fun(PreTy, PreTy, Vec<Pre>),
    App(Icit, Pre, Pre),
    Do(Vec<PreDefAn>),
    Hole(MetaSource),
    /// Dot(a, b, [c, d]) = a.b c d
    Dot(Pre, SName, Vec<(Icit, Pre)>),
    OrPat(Pre, Pre),
    EffPat(Pre, Pre),
    /// The bool is `true` if this is actually a `catch`
    Case(bool, Pre, Vec<(Pre, Pre)>),
    Lit(Literal),
    Unit,
    And(Pre, Pre),
    Or(Pre, Pre),
    BinOp(Spanned<BinOp>, Pre, Pre),
    /// If(cond, then, else)
    If(Pre, Pre, Pre),
    Sig(Vec<PreDefAn>),
    Struct(Vec<PreDefAn>),
    StructShort(Vec<(Name, Option<Pre>)>),
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
impl From<PreDef> for PreDefAn {
    fn from(inner: PreDef) -> PreDefAn {
        PreDefAn {
            inner,
            attributes: Vec::new(),
        }
    }
}
impl std::ops::Deref for PreDefAn {
    type Target = PreDef;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// PreDefs all have spans, usually the span of the name
pub type SName = Spanned<Name>;
/// The return type of a constructor is optional even here, since the behaviour is different.
/// When a constructor return type is missing, we don't unify it, we use the type declaration,
/// and add the type parameters declared there as implicit parameters to the constructor.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PreCons(pub SName, pub Vec<(Name, Icit, PreTy)>, pub Option<PreTy>);
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PreDataType {
    Standard(Vec<PreCons>),
    ShortForm(PreTy),
}
impl PreDataType {
    pub fn is_short_form(&self) -> bool {
        matches!(self, PreDataType::ShortForm(_))
    }

    pub fn iter<'a>(&'a self, db: &'a dyn Compiler) -> ConsIterator<'a> {
        match self {
            PreDataType::Standard(v) => ConsIterator::Standard(v.iter()),
            PreDataType::ShortForm(t) => ConsIterator::ShortForm(db, Some(t)),
        }
    }
}
pub enum ConsIterator<'a> {
    Standard(std::slice::Iter<'a, PreCons>),
    ShortForm(&'a dyn Compiler, Option<&'a PreTy>),
}
impl<'a> Iterator for ConsIterator<'a> {
    type Item = (SName, Vec<(Name, Icit, &'a PreTy)>, Option<&'a PreTy>);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ConsIterator::Standard(i) => i.next().map(|PreCons(name, args, ty)| {
                (
                    name.clone(),
                    args.iter().map(|(n, i, t)| (*n, *i, t)).collect(),
                    ty.as_ref(),
                )
            }),
            ConsIterator::ShortForm(db, t) => t.take().map(|t| {
                let name = t.copy_span(db.intern_name(String::new()));
                let arg_name = db.intern_name("_".to_string());
                (name, vec![(arg_name, Icit::Expl, t)], None)
            }),
        }
    }
}

/// A definition, declaration, or statement - anything that can appear in a `do`, `struct`, or `sig` block.
///
/// `PreDef` doesn't keep track of attributes; see `PreDefAn` for that.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PreDef {
    Fun(
        SName,
        Vec<(Name, Icit, PreTy)>,
        PreTy,
        Pre,
        Option<Vec<Pre>>,
    ),
    Val(SName, PreTy, Pre),
    Type {
        name: SName,
        is_eff: bool,
        ty_args: Vec<(Name, Icit, PreTy)>,
        ctors: PreDataType,
        namespace: Vec<PreDefAn>,
    },
    Impl(Option<SName>, PreTy, Pre),
    Expr(Pre),

    // Declarations
    FunDec(SName, Vec<(Name, Icit, PreTy)>, PreTy, Option<Vec<Pre>>),
    ValDec(SName, PreTy),

    /// Pre-typed term, used for data constructors.
    Cons(SName, VTy),

    /// PreDefAn with added type, used when type-checking structs
    Typed(Box<PreDefAn>, VTy, ReasonExpected),
}
impl PreDef {
    pub fn ordered(&self) -> bool {
        match self {
            PreDef::Fun(_, _, _, _, _)
            | PreDef::Type { .. }
            | PreDef::FunDec(_, _, _, _)
            | PreDef::ValDec(_, _) => false,
            PreDef::Val(_, _, _) | PreDef::Impl(_, _, _) | PreDef::Expr(_) | PreDef::Cons(_, _) => {
                true
            }
            PreDef::Typed(x, _, _) => x.ordered(),
        }
    }

    pub fn name(&self) -> Option<Name> {
        match self {
            PreDef::Fun(n, _, _, _, _)
            | PreDef::Val(n, _, _)
            | PreDef::Type { name: n, .. }
            | PreDef::FunDec(n, _, _, _)
            | PreDef::Cons(n, _)
            | PreDef::ValDec(n, _) => Some(**n),
            PreDef::Impl(n, _, _) => n.as_ref().map(|x| **x),
            PreDef::Expr(_) => None,
            PreDef::Typed(d, _, _) => d.name(),
        }
    }

    /// This picks the best span for refering to the definition
    pub fn span(&self) -> Span {
        match self {
            PreDef::Fun(n, _, _, _, _)
            | PreDef::Val(n, _, _)
            | PreDef::Type { name: n, .. }
            | PreDef::FunDec(n, _, _, _)
            | PreDef::Cons(n, _)
            | PreDef::ValDec(n, _) => n.span(),
            PreDef::Impl(Some(n), _, _) => n.span(),
            PreDef::Impl(None, _, t) => t.span(),
            PreDef::Expr(t) => t.span(),
            PreDef::Typed(d, _, _) => d.span(),
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
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
pub struct Size(u32);
impl Size {
    pub fn next_lvl(self) -> Lvl {
        Lvl(self.0)
    }

    pub fn to_ix(self, l: Lvl) -> Ix {
        assert!(
            l.0 + 1 <= self.0,
            "Can't access a variable (level {}) that hasn't been bound yet (enclosing = {})!",
            l.0,
            self.0,
        );
        // If we go down `self` levels from the root, there are still this many levels between us and the binding.
        Ix(self.0 - l.0 - 1)
    }

    pub fn to_lvl_(self, l: Ix) -> Lvl {
        assert!(
            l.0 + 1 <= self.0,
            "Can't access a variable (ix {}) that hasn't been bound yet (enclosing = {})!",
            l.0,
            self.0,
        );
        // If we go down `self` levels from the root, there are still this many levels between us and the binding.
        Lvl(self.0 - l.0 - 1)
    }

    pub fn inc(self) -> Size {
        Size(self.0 + 1)
    }

    pub fn dec(self) -> Size {
        Size(self.0 - 1)
    }

    pub fn zero() -> Size {
        Size(0)
    }

    pub fn apply_meta(self, v: Var<Ix>, ret_ty: Ty, mcxt: &MCxt) -> Term {
        let ty = (0..self.0)
            .map(|i| (mcxt.local_ty(Ix(i)), mcxt.local_name(Ix(i))))
            .fold((ret_ty, self), |(to, l), (from, name)| {
                (
                    // `ret_ty` is at level `self`, so the innermost local type is one less than that
                    Term::Clos(
                        Pi,
                        name,
                        Icit::Expl,
                        Box::new(from.quote(l.dec(), mcxt)),
                        Box::new(to),
                        Vec::new(),
                    ),
                    // and then each one outwards is one less
                    // The last one is at Lvl(0)
                    l.dec(),
                )
            })
            .0;
        // Because Terms use indices, the type here refers to its own parameters instead of locals in the outer context
        let t = Term::Var(v, Box::new(ty));
        // Now visit them from outermost to innermost
        (0..self.0)
            .rev()
            .map(|i| {
                Term::Var(
                    Var::Local(Ix(i)),
                    Box::new(mcxt.local_ty(Ix(i)).quote(self, mcxt)),
                )
            })
            .fold(t, |f, x| Term::App(Icit::Expl, Box::new(f), Box::new(x)))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Meta {
    /// A meta representing part of the type of a definition that doesn't have one yet, used for (mutual) recursion.
    /// It can be solved and used by any definition.
    Global(PreDefId, u16, MetaSource),
    /// The local meta index is a u16 so that this type fits in a word.
    /// So no more than 65535 metas are allowed per definition, which is probably fine.
    Local(DefId, u16, MetaSource),
}
impl Meta {
    /// If we're unifying `self` and `b`, and this returns true, `self` should be solved to `b`.
    /// If it returns false, `b` should be solved to `self`.
    pub fn higher_priority(self, b: Meta, mcxt: &MCxt) -> bool {
        let (local_def, local_pre) = match mcxt.ty {
            MCxtType::Local(i) => (Some(i), Some(mcxt.db.lookup_intern_def(i).0)),
            MCxtType::Global(i) => (None, Some(i)),
            MCxtType::Universal => (None, None),
        };
        match (self, b) {
            // In general, solve later metas first if they're from the same definition
            (Meta::Local(i, n, _), Meta::Local(i2, n2, _)) if i == i2 => n > n2,
            (Meta::Global(i, n, _), Meta::Global(i2, n2, _)) if i == i2 => n > n2,

            // If one is from the definition we're currently in, solve that one first
            // We don't want it leaking
            (Meta::Local(i, _, _), _) if local_def == Some(i) => true,
            (_, Meta::Local(i, _, _)) if local_def == Some(i) => false,
            (Meta::Global(i, _, _), _) if local_pre == Some(i) => true,
            (_, Meta::Global(i, _, _)) if local_pre == Some(i) => false,

            // Otherwise, solve locals before globals, and later definitions before earlier ones
            (Meta::Local(i, _, _), Meta::Local(i2, _, _)) => i2 > i,
            (Meta::Global(i, _, _), Meta::Global(i2, _, _)) => i2 > i,
            (Meta::Local(_, _, _), Meta::Global(_, _, _)) => true,
            (Meta::Global(_, _, _), Meta::Local(_, _, _)) => false,
        }
    }

    pub fn source(self) -> MetaSource {
        match self {
            Meta::Global(_, _, source) | Meta::Local(_, _, source) => source,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum StructKind<Ty> {
    Struct(Box<Ty>),
    Sig,
}

pub type Ty = Term;
/// The core syntax. This uses `Ix`, De Bruijn indices.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Type,
    Var(Var<Ix>, Box<Ty>),
    Clos(ClosTy, Name, Icit, Box<Ty>, Box<Term>, Vec<Term>),
    Fun(Box<Ty>, Box<Ty>, Vec<Term>),
    App(Icit, Box<Term>, Box<Term>),
    /// Stores the type of the scrutinee as the second argument
    /// The last argument is the effects caught
    Case(Box<Term>, Box<Ty>, Vec<(Pat, Term)>, Vec<Term>, Box<Ty>),
    /// The Builtin is the type - it can only be a builtin integer type
    Lit(Literal, Builtin),
    /// do A; B; () end
    Do(Vec<(DefId, Term)>),
    Struct(StructKind<Term>, Vec<(DefId, Name, Term)>),
    Dot(Box<Term>, Name),
}

impl Term {
    pub fn make_if(self, yes: Term, no: Term, rty: Term) -> Term {
        Term::Case(
            Box::new(self),
            Box::new(Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type))),
            vec![(Pat::Bool(true), yes), (Pat::Bool(false), no)],
            Vec::new(),
            Box::new(rty),
        )
    }

    pub fn ty(&self, at: Size, mcxt: &MCxt) -> Term {
        match self {
            Term::Type => Term::Type,
            Term::Var(_, t) => (**t).clone(),
            Term::Clos(Lam, n, i, aty, body, effs) => Term::Clos(
                Pi,
                *n,
                *i,
                aty.clone(),
                Box::new(body.ty(at.inc(), mcxt)),
                effs.clone(),
            ),
            Term::Clos(Pi, _, _, _, _, _) => Term::Type,
            Term::Fun(_, _, _) => Term::Type,
            Term::App(_, f, x) => match f.ty(at, mcxt).inline_top(mcxt) {
                Term::Fun(_, to, _) => *to,
                Term::Clos(Pi, _, _, _, to, _) => {
                    // Peel off one Pi to get the type of the next `f`.
                    // It's dependent, so we need to add `x` to the environment.
                    let mut env = Env::new(at);
                    let x = (**x).clone().evaluate(&env, mcxt);
                    env.push(Some(x));
                    // Then we evaluate-quote to so `rty` is in the context `at`.
                    to.eval_quote(&mut env, at, mcxt)
                }
                fty => unreachable!("{:?}", fty),
            },
            Term::Case(_, _, _, _, ty) => (**ty).clone(),
            Term::Lit(_, b) => Term::Var(Var::Builtin(*b), Box::new(Term::Type)),
            Term::Do(v) => match v.last() {
                Some((_, x)) => x.ty(at, mcxt),
                None => Term::Var(Var::Builtin(Builtin::UnitType), Box::new(Term::Type)),
            },
            Term::Struct(StructKind::Sig, _) => Term::Type,
            Term::Struct(StructKind::Struct(t), _) => (**t).clone(),
            Term::Dot(x, m) => match x.ty(at, mcxt).inline_top(mcxt) {
                Term::Struct(StructKind::Sig, v) => v
                    .into_iter()
                    .find(|(_, n, _)| n == m)
                    .map(|(_, _, x)| x)
                    .unwrap(),
                _ => unreachable!(),
            },
        }
    }

    /// If this is an application, return its head. Otherwise, return itself unchanged.
    pub fn head(&self) -> &Term {
        match self {
            Term::App(_, f, _) => f.head(),
            x => x,
        }
    }

    /// If this is a function type, give the return type. It *might not be valid at the original level* since this could be a Pi.
    /// Returns itself unchanged if it isn't a function type.
    pub fn ret(&self) -> &Term {
        match self {
            Term::Fun(_, to, _) => to.ret(),
            Term::Clos(Pi, _, _, _, to, _) => to.ret(),
            x => x,
        }
    }

    pub fn spine_len(&self) -> usize {
        match self {
            Term::App(_, f, _) => f.spine_len() + 1,
            _ => 0,
        }
    }

    pub fn arity(&self, only_expl: bool) -> usize {
        match self {
            Term::Fun(_, to, _) => 1 + to.arity(only_expl),
            Term::Clos(Pi, _, Icit::Impl, _, to, _) if only_expl => to.arity(only_expl),
            Term::Clos(Pi, _, Icit::Impl, _, to, _) => 1 + to.arity(only_expl),
            Term::Clos(Pi, _, Icit::Expl, _, to, _) => 1 + to.arity(only_expl),
            _ => 0,
        }
    }

    pub fn is_cons(&self) -> bool {
        matches!(self, Term::Var(Var::Cons(_), _))
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

    pub fn size(&self) -> Size {
        Size(self.0.len() as u32)
    }
}

// -- pretty printing --

#[derive(Clone, Debug)]
pub struct Names(VecDeque<Name>, Name);
impl Names {
    /// Returns the name representing "_"
    pub fn hole_name(&self) -> Name {
        self.1
    }
    pub fn new(mut cxt: Cxt, db: &dyn Compiler) -> Names {
        let mut v = VecDeque::new();
        while let MaybeEntry::Yes(CxtEntry {
            name, info, rest, ..
        }) = db.lookup_cxt_entry(cxt)
        {
            cxt = rest;
            if let NameInfo::Local(_) = info {
                v.push_back(name)
            }
        }
        Names(v, db.intern_name("_".into()))
    }
    pub fn size(&self) -> Size {
        Size(self.0.len() as u32)
    }
    pub fn get(&self, ix: Ix) -> Name {
        *self.0.get(ix.0 as usize).unwrap_or_else(|| {
            panic!(
                "Name index out of bounds: ix={} but len={}",
                ix.0,
                self.0.len()
            )
        })
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
            Term::Var(v, _) => match v {
                Var::Local(ix) => Doc::start(names.get(*ix).get(db)),
                Var::Top(id) | Var::Type(id, _) | Var::Cons(id) => Doc::start(
                    db.lookup_intern_predef(db.lookup_intern_def(*id).0)
                        .name()
                        .unwrap()
                        .get(db),
                ),
                Var::Rec(id) => Doc::start(db.lookup_intern_predef(*id).name().unwrap().get(db)),
                Var::Meta(m) => match m {
                    Meta::Global(id, i, _) => Doc::start("?:")
                        .add(db.lookup_intern_predef(*id).name().unwrap().get(db))
                        .add(":")
                        .add(i)
                        .add(""),
                    Meta::Local(def, id, _) => Doc::start("?").add(def.num()).add(".").add(id),
                },
                Var::File(f) => Doc::start({
                    use std::path::Path;
                    let files = crate::error::FILES.read().unwrap();
                    let path: &Path = files.get(*f).unwrap().name().as_ref();
                    path.file_stem().unwrap().to_str().unwrap().to_owned()
                }),
                Var::Builtin(b) => b.pretty(),
            },
            Term::Lit(l, _) => l.pretty(db),
            Term::Clos(Lam, n, i, _ty, t, _effs) => {
                let n = names.disamb(*n, db);
                {
                    names.add(n);
                    let r = match i {
                        Icit::Impl => Doc::start("[").add(n.get(db)).add("]"),
                        Icit::Expl => Doc::start(n.get(db)),
                    }
                    .space()
                    .add("=>")
                    .space()
                    .chain(t.pretty(db, names))
                    .prec(Prec::Term);
                    names.remove();
                    r
                }
            }
            Term::Clos(Pi, n, i, from, to, effs) => {
                let n = names.disamb(*n, db);
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
                    .group()
                    .line()
                    .add("->")
                    .space()
                    .chain(to.pretty(db, names));
                names.remove();
                let r = if effs.is_empty() {
                    r
                } else {
                    r.chain(
                        Doc::none()
                            .line()
                            .chain(Doc::keyword("with"))
                            .space()
                            .chain(Doc::intersperse(
                                effs.iter().map(|e| e.pretty(db, names)),
                                Doc::start(",").space(),
                            ))
                            .indent(),
                    )
                };
                r.prec(Prec::Term)
            }
            Term::Fun(from, to, effs) => from
                .pretty(db, names)
                .nest(Prec::App)
                .line()
                .add("->")
                .space()
                .chain(to.pretty(db, names))
                .chain(if effs.is_empty() {
                    Doc::none()
                } else {
                    Doc::none()
                        .space()
                        .chain(Doc::keyword("with"))
                        .space()
                        .chain(Doc::intersperse(
                            effs.iter().map(|e| e.pretty(db, names)),
                            Doc::start(",").space(),
                        ))
                })
                .prec(Prec::Term),
            // Show binops nicely
            Term::App(i, f, x)
                if *i == Icit::Expl
                    && matches!(&**f, Term::Var(Var::Builtin(Builtin::BinOp(_)), _)) =>
            {
                x.pretty(db, names)
                    .nest(Prec::App)
                    .line()
                    .chain(f.pretty(db, names))
                    .prec(Prec::App)
            }
            Term::App(i, f, x) => f
                .pretty(db, names)
                .nest(Prec::App)
                .space()
                .chain(match i {
                    Icit::Impl => Doc::start("[").chain(x.pretty(db, names)).add("]"),
                    Icit::Expl => x.pretty(db, names).nest(Prec::Atom),
                })
                .prec(Prec::App),
            Term::Case(x, _, cases, effs, _) => {
                Doc::keyword(if effs.is_empty() { "case" } else { "catch" })
                    .space()
                    .chain(x.pretty(db, names))
                    .space()
                    .chain(Doc::keyword("of"))
                    .line()
                    .chain(Doc::intersperse(
                        cases.iter().map(|(pat, body)| {
                            let mut names = names.clone();
                            pat.pretty(db, &mut names)
                                .space()
                                .add("=>")
                                .space()
                                .chain(body.pretty(db, &mut names))
                        }),
                        Doc::none().hardline(),
                    ))
                    .indent()
                    .line()
                    .chain(Doc::keyword("end"))
                    .prec(Prec::Term)
            }
            Term::Do(sc) => {
                let mut doc = Doc::keyword("do");
                let mut i = 0;
                for (id, term) in sc {
                    let (pre_id, _state) = db.lookup_intern_def(*id);
                    let predef = db.lookup_intern_predef(pre_id);
                    match predef.name() {
                        Some(n) => {
                            let n = names.disamb(n, db);
                            doc = doc.hardline().chain(
                                Doc::keyword("val")
                                    .space()
                                    .add(n.get(db))
                                    .space()
                                    .add("=")
                                    .space()
                                    .chain(term.pretty(db, names)),
                            );
                            names.add(n);
                            i += 1;
                        }
                        None => {
                            doc = doc.hardline().chain(term.pretty(db, names));
                        }
                    };
                }
                for _ in 0..i {
                    names.remove();
                }
                doc.indent()
                    .line()
                    .chain(Doc::keyword("end"))
                    .prec(Prec::Atom)
            }
            Term::Struct(kind, v) => {
                let mut doc = match kind {
                    StructKind::Struct(_) => Doc::keyword("struct"),
                    StructKind::Sig => Doc::keyword("sig"),
                };
                let mut i = 0;
                for (_, name, term) in v {
                    let name = names.disamb(*name, db);
                    doc = doc.hardline().chain(
                        Doc::keyword("val")
                            .space()
                            .add(name.get(db))
                            .space()
                            .add("=")
                            .space()
                            .chain(term.pretty(db, names)),
                    );
                    names.add(name);
                    i += 1;
                }
                for _ in 0..i {
                    names.remove();
                }
                doc.indent()
                    .line()
                    .chain(Doc::keyword("end"))
                    .prec(Prec::Atom)
            }
            Term::Dot(x, m) => x.pretty(db, names).nest(Prec::Atom).add('.').add(m.get(db)),
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
    pub size: Size,
}
impl Env {
    pub fn inline_metas(&mut self, mcxt: &MCxt) {
        for x in self.vals.iter_mut().flatten() {
            *x = Arc::new((**x).clone().inline_metas(self.size, mcxt));
        }
    }

    pub fn new(size: Size) -> Self {
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
    pub fn val(&self, i: Ix, ty: Ty, mcxt: &MCxt) -> Val {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .map(Val::Arc)
            .unwrap_or_else(|| Val::local(self.size.to_lvl_(i), ty.evaluate(self, mcxt)))
    }

    pub fn push(&mut self, v: Option<Val>) {
        self.size = self.size.inc();
        if v.is_some() || !self.vals.is_empty() {
            self.vals.push_front(v.map(Arc::new));
        }
    }

    pub fn pop(&mut self) {
        self.size = self.size.dec();
        self.vals.pop_front();
    }
}

/// A closure, representing a term that's waiting for an argument to be evaluated.
/// It's used in both lambdas and pi types.
///
/// Note that a `Clos` is very big (contains an inline `Env` and `Term`), so storing it behind a Box is advised.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Clos {
    pub env: Env,
    pub ty: VTy,
    pub term: Term,
    pub name: Name,
}
impl Clos {
    pub fn env_size(&self) -> Size {
        self.env.size
    }

    /// Quotes the closure back into a `Term`, but leaves it behind the lambda.
    /// So `at` is the number of abstractions enclosing the *lambda*, it doesn't include the lambda.
    pub fn quote(self, at: Size, mcxt: &MCxt) -> Term {
        let Clos {
            mut env, term, ty, ..
        } = self;
        env.push(Some(Val::local(at.next_lvl(), ty)));
        term.eval_quote(&mut env, at.inc(), mcxt)
    }

    /// Equivalent to `self.apply(Val::local(at.next_lvl(), cl.ty), mcxt)`.
    /// Like `quote`, `at` should not be incremented for the closure.
    pub fn vquote(self, at: Size, mcxt: &MCxt) -> Val {
        let Clos {
            mut env, term, ty, ..
        } = self;
        env.push(Some(Val::local(at.next_lvl(), ty)));
        term.evaluate(&env, mcxt)
    }

    pub fn apply(self, arg: Val, mcxt: &MCxt) -> Val {
        let Clos { mut env, term, .. } = self;
        env.push(Some(arg));
        term.evaluate(&env, mcxt)
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
    File(FileId),
    Meta(Meta),
    /// Datatypes are identified by their DefId as well, since they all have one and they're distinct.
    /// A `Type(id)` is the same as a `Top(id)`, except that it can't be inlined.
    /// You can still call `elaborate_def()` on it to get its type.
    Type(DefId, ScopeId),
    Cons(DefId),
    Builtin(Builtin),
}
impl Var<Ix> {
    pub fn cvt(self, l: Size) -> Var<Lvl> {
        match self {
            Var::Local(i) => Var::Local(l.to_lvl_(i)),
            Var::Top(i) => Var::Top(i),
            Var::Rec(i) => Var::Rec(i),
            Var::Meta(m) => Var::Meta(m),
            Var::Type(i, s) => Var::Type(i, s),
            Var::Cons(i) => Var::Cons(i),
            Var::File(f) => Var::File(f),
            Var::Builtin(b) => Var::Builtin(b),
        }
    }
}
impl Var<Lvl> {
    pub fn cvt(self, l: Size) -> Var<Ix> {
        match self {
            Var::Local(i) => Var::Local(l.to_ix(i)),
            Var::Top(i) => Var::Top(i),
            Var::Rec(i) => Var::Rec(i),
            Var::Meta(m) => Var::Meta(m),
            Var::Type(i, s) => Var::Type(i, s),
            Var::Cons(i) => Var::Cons(i),
            Var::File(f) => Var::File(f),
            Var::Builtin(b) => Var::Builtin(b),
        }
    }
}
impl<T: PartialEq> Var<T> {
    /// Checks whether two heads can be considered equivalent.
    /// Either they're actually equal, or one is Rec and one is Top, etc.
    pub fn unify(self, other: Var<T>, db: &dyn Compiler) -> bool {
        match (self, other) {
            (x, y) if x == y => true,

            // Ignore the scope id's, just make sure they're the same datatype
            (Var::Type(a, _), Var::Type(b, _)) => a == b,

            (Var::Rec(a), Var::Type(b, _))
            | (Var::Type(b, _), Var::Rec(a))
            | (Var::Rec(a), Var::Top(b))
            | (Var::Top(b), Var::Rec(a))
            | (Var::Cons(b), Var::Rec(a))
            | (Var::Rec(a), Var::Cons(b)) => {
                let (b, _) = db.lookup_intern_def(b);
                a == b
            }

            (Var::Top(a), Var::Type(b, _))
            | (Var::Type(b, _), Var::Top(a))
            | (Var::Top(a), Var::Cons(b))
            | (Var::Cons(b), Var::Top(a)) => a == b,

            _ => false,
        }
    }
}

/// An eliminator is something that can be waiting on a neutral value: either an application to an argument, or a case-of.
/// A neutral value has a chain of eliminators which are applied one by one when it's resolved.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Elim {
    App(Icit, Val),
    /// Case(env, scrutinee_ty, branches, effects, ret_ty)
    Case(Env, Box<Term>, Vec<(Pat, Term)>, Vec<Term>, Box<Term>),
    Dot(Name),
}
impl Elim {
    pub fn into_app(self) -> Option<(Icit, Val)> {
        match self {
            Elim::App(i, v) => Some((i, v)),
            _ => None,
        }
    }

    pub fn assert_app(&self) -> (Icit, &Val) {
        match self {
            Elim::App(i, v) => (*i, v),
            _ => panic!("Called assert_app() on {:?}", self),
        }
    }
}

pub type Spine = Vec<Elim>;

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

impl Default for Glued {
    fn default() -> Self {
        Self::new()
    }
}

impl Glued {
    pub fn new() -> Self {
        Glued(Arc::new(RwLock::new(None)))
    }

    /// Resolves the `Glued`: returns a `Val::Arc` to the cached value if available, otherwise inlines the head and beta-reduces, returning the result.
    /// If the head can't be inlined, e.g. because it's a parameter, returns None.
    pub fn resolve(
        &self,
        h: Var<Lvl>,
        sp: impl IntoOwned<Spine>,
        at: Size,
        mcxt: &MCxt,
    ) -> Option<Val> {
        // TODO make this work
        // let guard = self.0.read().unwrap();
        // if let Some(v) = &*guard {
        //     Some(v.clone())
        // } else
        {
            // drop(guard);
            let h = match h {
                // Check the mcxt's local constraints
                Var::Local(lvl) => {
                    let val = mcxt.local_val(lvl)?.clone();
                    // We don't cache this, because we might use this value outside of the local scope
                    Some(val)
                }
                // A datatype is already fully evaluated
                Var::Type(_, _) => None,
                Var::Cons(_) => None,
                Var::File(_) => None,
                Var::Builtin(Builtin::BinOp(op)) => {
                    let mut sp = sp.into_owned();
                    if sp.len() == 2 {
                        if let Elim::App(Icit::Expl, b) = sp.pop().unwrap() {
                            if let Elim::App(Icit::Expl, a) = sp.pop().unwrap() {
                                let a = a.inline(at, mcxt);
                                let b = b.inline(at, mcxt);
                                if let Some(v) = op.eval(&a, &b) {
                                    return Some(v);
                                }
                            }
                        }
                    }
                    return None;
                }
                Var::Builtin(_) => None,
                Var::Rec(rec) => {
                    let def = mcxt.cxt.lookup_rec(rec, mcxt.db)?;
                    let val = mcxt.def_term(def)?;
                    let val = val.evaluate(&Env::new(at), mcxt);
                    // let val = Val::Arc(Arc::new(val));
                    // *self.0.write().unwrap() = Some(val.clone());
                    Some(val)
                }
                Var::Top(def) => {
                    let val = mcxt.def_term(def)?;
                    let val = val.evaluate(&Env::new(at), mcxt);
                    // let val = Val::Arc(Arc::new(val));
                    // *self.0.write().unwrap() = Some(val.clone());
                    Some(val)
                }
                Var::Meta(m) => mcxt
                    .get_meta(m)
                    .map(|term| term.evaluate(&Env::new(at), mcxt)),
            }?;
            Some(sp.into_owned().into_iter().fold(h, |h, e| h.app(e, mcxt)))
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClosTy {
    Lam,
    Pi,
}
pub use ClosTy::*;

pub type VTy = Val;
/// A value in normal(-ish) form.
/// Values are never behind any abstractions, since those use `Clos` to store a `Term`.
/// So, values use `Lvl`, De Bruijn levels, which make things like unification easier.
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Val {
    Type,
    Arc(Arc<Val>),
    /// The spine are arguments applied in order. It can be empty.
    /// Stores the type of the head.
    App(Var<Lvl>, Box<VTy>, Spine, Glued),
    /// The effects are in the outer scope, so that they can be stored as `Val`s.
    /// So they can't depend on the immediate argument.
    Clos(ClosTy, Icit, Box<Clos>, Vec<Val>),
    Fun(Box<VTy>, Box<VTy>, Vec<Val>),
    /// The Builtin is the type - it can only be a builtin integer type
    Lit(Literal, Builtin),
    /// do A; B; () end
    Do(Env, Vec<(DefId, Term)>),
    Struct(StructKind<Val>, Vec<(DefId, Name, Val)>),
}
impl Val {
    pub fn pretty(&self, mcxt: &MCxt) -> Doc {
        self.clone()
            .quote(mcxt.size, mcxt)
            .pretty(mcxt.db, &mut Names::new(mcxt.cxt, mcxt.db))
    }

    /// Unwraps any top-level `Val::Arc`s, so you don't have to recurse to deal with that case when matching on a reference.
    pub fn unarc(&self) -> &Val {
        match self {
            Val::Arc(x) => x.unarc(),
            x => x,
        }
    }

    /// Assuming this is the type of a constructor, returns either the return type or the effect type.
    /// Increments `at` as needed.
    pub fn cons_ret_type(self, at: &mut Size, mcxt: &MCxt) -> Val {
        match self {
            // The return type is
            Val::Fun(_, to, effs) if effs.is_empty() => to.cons_ret_type(at, mcxt),
            Val::Fun(_, _, mut effs) => {
                assert_eq!(effs.len(), 1);
                effs.pop().unwrap()
            }
            Val::Clos(Pi, _, cl, effs) if effs.is_empty() => cl.vquote(*at, mcxt).cons_ret_type(
                {
                    *at = at.inc();
                    at
                },
                mcxt,
            ),
            Val::Clos(Pi, _, _, mut effs) => {
                assert_eq!(effs.len(), 1);
                effs.pop().unwrap()
            }
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).cons_ret_type(at, mcxt),
            x => x,
        }
    }

    pub fn arity(&self, only_expl: bool) -> usize {
        match self {
            Val::Fun(_, to, _) => 1 + to.arity(only_expl),
            Val::Clos(Pi, Icit::Impl, cl, _) if only_expl => cl.term.arity(only_expl),
            Val::Clos(Pi, Icit::Impl, cl, _) => 1 + cl.term.arity(only_expl),
            Val::Clos(Pi, Icit::Expl, cl, _) => 1 + cl.term.arity(only_expl),
            _ => 0,
        }
    }

    pub fn local(lvl: Lvl, ty: VTy) -> Val {
        Val::App(Var::Local(lvl), Box::new(ty), Vec::new(), Glued::new())
    }

    pub fn datatype(def: DefId, scope: ScopeId, ty: VTy) -> Val {
        Val::App(
            Var::Type(def, scope),
            Box::new(ty),
            Vec::new(),
            Glued::new(),
        )
    }

    pub fn boolean(b: bool) -> Val {
        match b {
            true => Val::builtin(Builtin::True, Val::builtin(Builtin::Bool, Val::Type)),
            false => Val::builtin(Builtin::False, Val::builtin(Builtin::Bool, Val::Type)),
        }
    }

    pub fn top(def: DefId, ty: VTy) -> Val {
        Val::App(Var::Top(def), Box::new(ty), Vec::new(), Glued::new())
    }

    pub fn rec(id: PreDefId, ty: VTy) -> Val {
        Val::App(Var::Rec(id), Box::new(ty), Vec::new(), Glued::new())
    }

    pub fn builtin(b: Builtin, ty: VTy) -> Val {
        Val::App(Var::Builtin(b), Box::new(ty), Vec::new(), Glued::new())
    }

    pub fn cons(id: DefId, ty: VTy) -> Val {
        Val::App(Var::Cons(id), Box::new(ty), Vec::new(), Glued::new())
    }

    pub fn file(id: FileId, ty: VTy) -> Val {
        Val::App(Var::File(id), Box::new(ty), Vec::new(), Glued::new())
    }

    pub fn meta(meta: Meta, ty: VTy) -> Val {
        Val::App(Var::Meta(meta), Box::new(ty), Vec::new(), Glued::new())
    }
}
