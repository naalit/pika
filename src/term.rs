//! We have three IRs in the frontend:
//! - `Pre` or presyntax is what we get from the parser.
//! - `Term` or core syntax is what we get after elaborating (name resolution, type checking, etc.).
//! - `Val` is a value, where beta reduction and associated substitution has been performed.
use crate::common::*;
use crate::elaborate::MCxt;
use crate::pattern::Pat;

impl Literal {
    pub fn pretty(self) -> Doc {
        match self {
            Literal::Positive(i) => Doc::start(i).style(Style::Literal),
            Literal::Negative(i) => Doc::start(i).style(Style::Literal),
        }
    }

    pub fn to_usize(self) -> usize {
        // TODO: BitSet stores literals as usize, so this only works on 64-bit, TODO 32-bit support
        match self {
            Literal::Positive(i) => i as usize,
            Literal::Negative(i) => i as usize,
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
    Struct(Vec<PreDefAn>),
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
}
impl PreDef {
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

    pub fn apply_meta(self, v: Var<Ix>, ret_ty: Ty, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        let ty = (0..self.0)
            .map(|i| (mcxt.local_ty(Ix(i), db), mcxt.local_name(Ix(i), db)))
            .fold((ret_ty, self), |(to, l), (from, name)| {
                (
                    // `ret_ty` is at level `self`, so the innermost local type is one less than that
                    Term::Pi(
                        name,
                        Icit::Expl,
                        Box::new(from.quote(l.dec(), mcxt, db)),
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
        let t = Term::Var(v, Box::new(ty.clone()));
        // Now visit them from outermost to innermost
        (0..self.0)
            .rev()
            .map(|i| {
                Term::Var(
                    Var::Local(Ix(i)),
                    Box::new(mcxt.local_ty(Ix(i), db).quote(self, mcxt, db)),
                )
            })
            .fold((t, ty), |(f, fty), x| {
                // Peel off one Pi to get the type of the next `f`.
                // It's dependent, so we need to add `x` to the environment.
                // Then we evaluate-quote to so `rty` is in the context `self`.
                let mut env = Env::new(self);
                env.push(Some(x.clone().evaluate(&env, mcxt, db)));
                let rty = match &fty {
                    Term::Pi(_, _, _, x, _) => (**x).clone().eval_quote(&mut env, self, mcxt, db),
                    _ => unreachable!(),
                };
                (
                    Term::App(Icit::Expl, Box::new(f), Box::new(x)),
                    rty,
                )
            })
            .0
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
pub enum Meta {
    /// A meta representing part of the type of a definition that doesn't have one yet, used for (mutual) recursion.
    /// It can be solved and used by any definition.
    Global(PreDefId, u16),
    /// The local meta index is a u16 so that this type fits in a word.
    /// So no more than 65535 metas are allowed per definition, which is probably fine.
    Local(DefId, u16),
}

/*
Problem: `(if a then b else c) d`
We can turn that into `Lazy(App(If(...), d))`, but then we need the head type.
We need the head type for all applications, to see what effects to pass.

*/

pub type Ty = Term;
/// The core syntax. This uses `Ix`, De Bruijn indices.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Type,
    Var(Var<Ix>, Box<Ty>),
    Lam(Name, Icit, Box<Ty>, Box<Term>, Vec<Term>),
    Pi(Name, Icit, Box<Ty>, Box<Ty>, Vec<Term>),
    Fun(Box<Ty>, Box<Ty>, Vec<Term>),
    App(Icit, Box<Term>, Box<Term>),
    /// Stores the type of the scrutinee as the second argument
    /// The last argument is the effects caught
    Case(Box<Term>, Box<Ty>, Vec<(Pat, Term)>, Vec<Term>),
    /// The Builtin is the type - it can only be a builtin integer type
    Lit(Literal, Builtin),
    /// If(cond, then, else)
    If(Box<Term>, Box<Term>, Box<Term>),
    /// do A; B; () end
    Do(Vec<(DefId, Term)>),
    /// There was a type error somewhere, and we already reported it, so we want to continue as much as we can.
    Error,
}

impl Term {
    pub fn ty(&self, l: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Term::Type => Term::Type,
            Term::Var(_, t) => (**t).clone(),
            Term::Lam(n, i, aty, body, effs) => Term::Pi(*n, *i, aty.clone(), Box::new(body.ty(l.inc(), mcxt, db)), effs.clone()),
            Term::Pi(_, _, _, _, _) => Term::Type,
            Term::Fun(_, _, _) => Term::Type,
            Term::App(_, f, x) => match f.ty(l, mcxt, db) {
                Term::Fun(_, to, _) => *to,
                Term::Pi(_, _, _, to, _) => {
                    // Peel off one Pi to get the type of the next `f`.
                    // It's dependent, so we need to add `x` to the environment.
                    let mut env = Env::new(l);
                    let x = (**x).clone().evaluate(&env, mcxt, db);
                    env.push(Some(x));
                    // Then we evaluate-quote to so `rty` is in the context `enclosing`.
                    to.eval_quote(&mut env, l, mcxt, db)
                }
                fty => unreachable!("{:?}", fty),
            },
            Term::Case(_, _, v, _) => match v.first() {
                Some((pat, body)) => {
                    let l = pat.add_names(l, &mut Names::new(mcxt.cxt, db));
                    body.ty(l, mcxt, db)
                }
                // If it's an empty case, return error, which is mostly ignored as a type
                // I don't *think* this causes any problems
                _ => Term::Error,
            }
            Term::Lit(_, b) => Term::Var(Var::Builtin(*b), Box::new(Term::Type)),
            Term::If(_, a, _) => a.ty(l, mcxt, db),
            Term::Do(v) => match v.last() {
                Some((_, x)) => x.ty(l, mcxt, db),
                None => Term::Var(Var::Builtin(Builtin::UnitType), Box::new(Term::Type)),
            }
            Term::Error => Term::Error,
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
            Term::Pi(_, _, _, to, _) => to.ret(),
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
            Term::Pi(_, Icit::Impl, _, to, _) if only_expl => to.arity(only_expl),
            Term::Pi(_, Icit::Impl, _, to, _) => 1 + to.arity(only_expl),
            Term::Pi(_, Icit::Expl, _, to, _) => 1 + to.arity(only_expl),
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

    pub fn size(&self) -> Lvl {
        Lvl(self.0.len() as u32)
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
                    Meta::Global(id, i) => Doc::start("?:")
                        .add(db.lookup_intern_predef(*id).name().unwrap().get(db))
                        .add(":")
                        .add(i)
                        .add(""),
                    Meta::Local(def, id) => Doc::start("?").add(def.num()).add(".").add(id),
                },
                Var::Builtin(b) => b.pretty(),
            },
            Term::Lit(l, _) => l.pretty(),
            Term::Lam(n, i, _ty, t, _effs) => {
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
            Term::Pi(n, i, from, to, effs) => {
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
            Term::Error => Doc::start("<error>"),
            Term::Case(x, _, cases, effs) => {
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
            Term::If(cond, yes, no) => Doc::keyword("if")
                .space()
                .chain(cond.pretty(db, names))
                .line()
                .chain(Doc::keyword("then"))
                .space()
                .chain(yes.pretty(db, names))
                .line()
                .chain(Doc::keyword("else"))
                .space()
                .chain(no.pretty(db, names))
                .prec(Prec::Term),
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
    pub fn inline_metas(&mut self, mcxt: &MCxt, db: &dyn Compiler) {
        for i in &mut self.vals {
            if let Some(x) = i {
                *x = Arc::new((**x).clone().inline_metas(mcxt, db));
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
    pub fn val(&self, i: Ix, ty: Ty, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .map(Val::Arc)
            .unwrap_or_else(|| Val::local(i.to_lvl(self.size), ty.evaluate(self, mcxt, db)))
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
    pub fn env_size(&self) -> Lvl {
        self.env.size
    }

    /// Quotes the closure back into a `Term`, but leaves it behind the lambda.
    /// So `enclosing` is the number of abstractions enclosing the *lambda*, it doesn't include the lambda.
    pub fn quote(self, enclosing: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        let Clos {
            mut env, term, ty, ..
        } = self;
        env.push(Some(Val::local(enclosing.inc(), ty)));
        term.eval_quote(&mut env, enclosing.inc(), mcxt, db)
    }

    /// Equivalent to `self.apply(Val::local(l, cl.ty), mcxt)`
    pub fn vquote(self, l: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        let Clos {
            mut env, term, ty, ..
        } = self;
        env.push(Some(Val::local(l, ty)));
        term.evaluate(&env, mcxt, db)
    }

    pub fn apply(self, arg: Val, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        let Clos { mut env, term, .. } = self;
        env.push(Some(arg));
        term.evaluate(&env, mcxt, db)
    }
}

/// A term that hasn't been evaluated yet, because it's either an `if` or `case` and the scrutinee is a neutral term.
/// It's similar to a closure, but isn't waiting on an argument, but rather variables in the environment.
///
/// Note that a `Lazy` is very big (contains an inline `Env` and `Term`), so storing it behind a Box is advised.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lazy {
    pub env: Env,
    pub term: Term,
}
impl Lazy {
    pub fn env_size(&self) -> Lvl {
        self.env.size
    }

    /// Quotes the closure back into a `Term`.
    pub fn quote(self, enclosing: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        let Lazy { mut env, term } = self;
        term.eval_quote(&mut env, enclosing, mcxt, db)
    }

    /// Tries to evaluate the `Lazy` again; if it can't be evaluated, this will just return another `Lazy`.
    pub fn evaluate(self, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        let Lazy { env, term } = self;
        term.evaluate(&env, mcxt, db)
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
    /// Datatypes are identified by their DefId as well, since they all have one and they're distinct.
    /// A `Type(id)` is the same as a `Top(id)`, except that it can't be inlined.
    /// You can still call `elaborate_def()` on it to get its type.
    Type(DefId, ScopeId),
    Cons(DefId),
    Builtin(Builtin),
}
impl Var<Ix> {
    pub fn cvt(self, l: Lvl) -> Var<Lvl> {
        match self {
            Var::Local(i) => Var::Local(i.to_lvl(l)),
            Var::Top(i) => Var::Top(i),
            Var::Rec(i) => Var::Rec(i),
            Var::Meta(m) => Var::Meta(m),
            Var::Type(i, s) => Var::Type(i, s),
            Var::Cons(i) => Var::Cons(i),
            Var::Builtin(b) => Var::Builtin(b),
        }
    }
}
impl Var<Lvl> {
    pub fn cvt(self, l: Lvl) -> Var<Ix> {
        match self {
            Var::Local(i) => Var::Local(i.to_ix(l)),
            Var::Top(i) => Var::Top(i),
            Var::Rec(i) => Var::Rec(i),
            Var::Meta(m) => Var::Meta(m),
            Var::Type(i, s) => Var::Type(i, s),
            Var::Cons(i) => Var::Cons(i),
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

impl Default for Glued {
    fn default() -> Self {
        Self::new()
    }
}

impl Glued {
    pub fn new() -> Self {
        Glued(Arc::new(RwLock::new(None)))
    }

    /// Like `resolve()`, but only inlines metas and local constraints, not definitions or local constraints. So, it doesn't need a quote level.
    pub fn resolve_meta(
        &self,
        h: Var<Lvl>,
        sp: impl IntoOwned<Spine>,
        mcxt: &MCxt,
        db: &dyn Compiler,
    ) -> Option<Val> {
        let guard = self.0.read().unwrap();
        if let Some(v) = &*guard {
            Some(v.clone())
        } else {
            drop(guard);
            match h {
                // Check the mcxt's local constraints
                Var::Local(lvl) => {
                    let val = mcxt.local_val(lvl)?.clone();
                    let val = sp
                        .into_owned()
                        .into_iter()
                        .fold(val, |f, (i, x)| f.app(i, x, mcxt, db));
                    // We don't cache this, because we might use this value outside of the local scope
                    Some(val)
                }
                // If we inlined the Rec, it would probably lead to infinite recursion
                Var::Rec(_) => None,
                Var::Type(_, _) => None,
                Var::Cons(_) => None,
                Var::Top(_) => None,
                Var::Builtin(_) => None,
                Var::Meta(m) => {
                    if let Some(val) = mcxt.get_meta(m) {
                        let val = sp
                            .into_owned()
                            .into_iter()
                            .fold(val, |f, (i, x)| f.app(i, x, mcxt, db));
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
                // Check the mcxt's local constraints
                Var::Local(lvl) => {
                    let val = mcxt.local_val(lvl)?.clone();
                    let val = sp
                        .into_owned()
                        .into_iter()
                        .fold(val, |f, (i, x)| f.app(i, x, mcxt, db));
                    // We don't cache this, because we might use this value outside of the local scope
                    Some(val)
                }
                // A datatype is already fully evaluated
                Var::Type(_, _) => None,
                Var::Cons(_) => None,
                Var::Builtin(Builtin::BinOp(op)) => {
                    let sp = sp.into_owned();
                    if sp.len() != 2 {
                        None
                    } else {
                        let a = sp[0].1.clone().inline(l, db, mcxt);
                        let b = sp[1].1.clone().inline(l, db, mcxt);
                        if let Some(v) = op.eval(&a, &b) {
                            Some(v)
                        } else {
                            None
                        }
                    }
                }
                Var::Builtin(_) => None,
                Var::Rec(rec) => {
                    let def = mcxt.cxt.lookup_rec(rec, db)?;
                    let val = db.elaborate_def(def).ok()?.term;
                    let val = (*val).clone();
                    let val = val.evaluate(&Env::new(l), mcxt, db);
                    let val = sp
                        .into_owned()
                        .into_iter()
                        .fold(val, |f, (i, x)| f.app(i, x, mcxt, db));
                    let val = Val::Arc(Arc::new(val));
                    *self.0.write().unwrap() = Some(val.clone());
                    Some(val)
                }
                Var::Top(def) => {
                    let val = db.elaborate_def(def).ok()?.term;
                    let val = (*val).clone();
                    let val = val.evaluate(&Env::new(l), mcxt, db);
                    let val = sp
                        .into_owned()
                        .into_iter()
                        .fold(val, |f, (i, x)| f.app(i, x, mcxt, db));
                    let val = Val::Arc(Arc::new(val));
                    *self.0.write().unwrap() = Some(val.clone());
                    Some(val)
                }
                Var::Meta(m) => {
                    if let Some(val) = mcxt.get_meta(m) {
                        let val = sp
                            .into_owned()
                            .into_iter()
                            .fold(val, |f, (i, x)| f.app(i, x, mcxt, db));
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
    Lazy(Box<Lazy>),
    Error,
}
impl Val {
    pub fn pretty(&self, db: &dyn Compiler, mcxt: &MCxt) -> Doc {
        self.clone()
            .quote(mcxt.size, mcxt, db)
            .pretty(db, &mut Names::new(mcxt.cxt, db))
    }

    /// Unwraps any top-level `Val::Arc`s, so you don't have to recurse to deal with that case when matching on a reference.
    pub fn unarc(&self) -> &Val {
        match self {
            Val::Arc(x) => x.unarc(),
            x => x,
        }
    }

    /// Assuming this is the type of a constructor, returns either the return type or the effect type
    pub fn cons_ret_type(self, l: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Val::Fun(_, to, effs) if effs.is_empty() => to.cons_ret_type(l.inc(), mcxt, db),
            Val::Fun(_, _, mut effs) => {
                assert_eq!(effs.len(), 1);
                effs.pop().unwrap()
            }
            Val::Clos(Pi, _, cl, effs) if effs.is_empty() => {
                cl.vquote(l.inc(), mcxt, db)
                    .cons_ret_type(l.inc(), mcxt, db)
            }
            Val::Clos(Pi, _, _, mut effs) => {
                assert_eq!(effs.len(), 1);
                effs.pop().unwrap()
            }
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).cons_ret_type(l.inc(), mcxt, db),
            x => x,
        }
    }

    pub fn ret_type(self, l: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Val::Fun(_, to, _) => to.ret_type(l.inc(), mcxt, db),
            Val::Clos(Pi,  _, cl, _) => cl.vquote(l.inc(), mcxt, db).ret_type(l.inc(), mcxt, db),
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).ret_type(l.inc(), mcxt, db),
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

    pub fn meta(meta: Meta, ty: VTy) -> Val {
        Val::App(Var::Meta(meta), Box::new(ty), Vec::new(), Glued::new())
    }
}
