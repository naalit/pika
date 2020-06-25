use crate::bicheck::TCtx;
use crate::common::*;
use crate::{
    affine::Mult,
    term::{Builtin, STerm},
};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

/// The evaluation context
pub struct ECtx<'a> {
    database: &'a dyn MainGroupP,
    scope: ScopeId,
    pub vals: HashMap<Sym, Arc<Elab>>,
}
impl<'a> Clone for ECtx<'a> {
    fn clone(&self) -> Self {
        ECtx {
            database: self.database,
            scope: self.scope(),
            vals: self.vals.clone(),
        }
    }
}
impl<'a> ECtx<'a> {
    pub fn new(db: &'a (impl Scoped + HasDatabase)) -> Self {
        ECtx {
            scope: db.scope(),
            database: db.database(),
            vals: HashMap::new(),
        }
    }

    pub fn val(&self, k: Sym) -> Option<Arc<Elab>> {
        self.vals
            .get(&k)
            .cloned()
            .or_else(|| self.database.elab(self.scope.clone(), k))
    }
    pub fn set_val(&mut self, k: Sym, v: Elab) {
        self.vals.insert(k, Arc::new(v));
    }
}
impl<'a> HasBindings for ECtx<'a> {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.database.bindings_ref()
    }
}
impl<'a> HasDatabase for ECtx<'a> {
    fn database(&self) -> &dyn MainGroupP {
        self.database
    }
}
impl<'a> Scoped for ECtx<'a> {
    fn scope(&self) -> ScopeId {
        self.scope.clone()
    }
}

pub struct Cloner {
    bindings: Arc<RwLock<Bindings>>,
    map: HashMap<Sym, Sym>,
}
impl Cloner {
    pub fn new(bindings: &impl HasBindings) -> Self {
        Cloner {
            bindings: bindings.bindings_ref().clone(),
            map: HashMap::new(),
        }
    }

    pub fn set(&mut self, from: Sym, to: Sym) {
        self.map.insert(from, to);
    }

    pub fn get(&self, s: Sym) -> Option<Sym> {
        self.map.get(&s).copied()
    }
}
impl HasBindings for Cloner {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        &self.bindings
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub enum ElabStmt {
    Def(Sym, Elab),
    Expr(Elab),
}
impl ElabStmt {
    pub fn cloned(&self, cln: &mut Cloner) -> Self {
        match self {
            ElabStmt::Def(s, x) => {
                let fresh = cln.bindings_mut().fresh(*s);
                #[cfg(feature = "logging")]
                {
                    let b = &cln.bindings();
                    println!(
                        "Renaming {}{} to {}{}",
                        b.resolve(*s),
                        s.num(),
                        b.resolve(fresh),
                        fresh.num()
                    );
                }
                cln.set(*s, fresh);
                ElabStmt::Def(fresh, x.cloned(cln))
            }
            ElabStmt::Expr(x) => ElabStmt::Expr(x.cloned(cln)),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Default)]
pub struct Clos {
    pub tys: Vec<(Sym, Arc<Elab>)>,
    pub vals: Vec<(Sym, Arc<Elab>)>,
    pub is_move: bool,
    pub span: Span,
}
impl Clos {
    /// We need to rename anything stored in the closure, too, since it can use local variables
    pub fn cloned(&self, cln: &mut Cloner) -> Self {
        Clos {
            tys: self
                .tys
                .iter()
                .map(|(k, v)| (cln.get(*k).unwrap_or(*k), Arc::new(v.cloned(cln))))
                .collect(),
            vals: self
                .vals
                .iter()
                .map(|(k, v)| (cln.get(*k).unwrap_or(*k), Arc::new(v.cloned(cln))))
                .collect(),
            is_move: self.is_move,
            span: self.span,
        }
    }
}
impl<'a> TCtx<'a> {
    pub fn clos(&self, t: &STerm, is_move: bool) -> Clos {
        let tys: Vec<_> = self
            .tys
            .iter()
            .filter(|(k, _)| t.uses(**k))
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        let vals = tys
            .iter()
            .filter_map(|(k, _)| Some((*k, self.ectx.vals.get(k)?.clone())))
            .collect();
        Clos {
            tys,
            vals,
            is_move,
            span: t.span(),
        }
    }

    pub fn add_clos(&mut self, clos: &Clos) {
        self.tys.extend(clos.tys.iter().cloned());
        self.ectx.vals.extend(clos.vals.iter().cloned());
    }
}
impl<'a> ECtx<'a> {
    pub fn add_clos(&mut self, clos: &Clos) {
        self.vals.extend(clos.vals.iter().cloned());
    }
}

/// The language of elaborated terms, which have enough type information to reconstruct types pretty easily
///
/// For a term to get to here, it must be well typed
#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub enum Elab {
    Unit,                                    // ()
    Binder(Sym, BElab),                      // x: T
    Var(Span, Sym, BElab), // (a, T) --> the T a; we need the span for "moved variable" errors
    I32(i32),              // 3
    Type(u32),             // Type0
    Builtin(Builtin),      // Int
    Fun(Clos, Vec<(Vec<Elab>, Elab, Elab)>), // fun { a b => the T x; c d => the U y }
    App(BElab, BElab),     // f x
    Pair(BElab, BElab),    // x, y
    Tag(TagId),            // tag X
    StructIntern(StructId), // struct { x := 3 }
    StructInline(Vec<(Sym, Elab)>), // struct { x := 3 }
    Project(BElab, RawSym), // r.m
    Block(Vec<ElabStmt>),  // do { x; y }
    Union(Vec<Elab>),      // x | y
    Bottom,
    Top,
}
type BElab = Box<Elab>;

pub fn unionize_ty(v: Vec<(Vec<Elab>, Elab, Elab)>, ectx: &ECtx) -> (Vec<Elab>, Elab) {
    let len = v.first().unwrap().0.len();
    let (args, ret) = v.into_iter().fold(
        ((0..len).map(|_| Vec::new()).collect::<Vec<_>>(), Vec::new()),
        |(mut accf, mut acct), (from, to, _)| {
            for (accf, from) in accf.iter_mut().zip(from) {
                accf.push(from);
            }
            acct.push(to);
            (accf, acct)
        },
    );
    let args = args
        .into_iter()
        .map(|v| Elab::Union(v).simplify_unions(ectx))
        .collect();
    let ret = Elab::Union(ret).simplify_unions(ectx);
    (args, ret)
}

impl Elab {
    /// Binders are usually confusing in type errors, so you can get rid of them
    pub fn unbind(&self) -> &Self {
        match self {
            Elab::Binder(_, x) => x,
            x => x,
        }
    }

    /// Are there any values that occupy both types `self` and `other`?
    /// Bottom doesn't count, of course, since it's not a value
    /// The same as "could a value of type `other` match `self`?" or vice versa
    pub fn overlap(&self, other: &Elab, ectx: &ECtx) -> bool {
        match (self, other) {
            (Elab::Union(v), Elab::Union(v2)) => {
                v.iter().any(|x| v2.iter().any(|y| x.overlap(y, ectx)))
            }
            (Elab::Union(v), _) => v.iter().any(|x| x.overlap(other, ectx)),
            (_, Elab::Union(v)) => v.iter().any(|x| self.overlap(x, ectx)),
            _ => {
                self.subtype_of(other, &mut ectx.clone())
                    || other.subtype_of(self, &mut ectx.clone())
            }
        }
    }

    /// Instead of calling `Elab::union()` and over again, if you construct a union with several parts,
    /// call this after to simplify it in one pass
    pub fn simplify_unions(mut self, ectx: &ECtx) -> Self {
        match &mut self {
            Elab::Union(v) => match v.len() {
                0 => self,
                1 => v.pop().unwrap(),
                _ => {
                    let mut ectx = ectx.clone();
                    let mut rv: Vec<Elab> = Vec::new();
                    for val in v.split_off(0) {
                        let mut i = 0;
                        let mut should_add = true;
                        while i < rv.len() {
                            let x = &rv[i];

                            // If `val` covers `x`'s case, we don't need `x`
                            if x.subtype_of(&val, &mut ectx) {
                                rv.remove(i);
                            } else {
                                i += 1;
                                // but if `x` covers `val`'s case, we don't need `val`
                                if val.subtype_of(x, &mut ectx) {
                                    should_add = false;
                                    break;
                                }
                            }
                        }
                        if should_add {
                            rv.push(val);
                        }
                    }

                    rv.sort_by(|x, y| x.partial_cmp(y).unwrap());

                    if rv.len() == 1 {
                        rv.pop().unwrap()
                    } else {
                        Elab::Union(rv)
                    }
                }
            },
            _ => self,
        }
    }

    /// Does this term reference this symbol at all?
    /// Only works for local variables, not ones you'd find in `db.elab()`
    pub fn uses(&self, s: Sym) -> bool {
        use Elab::*;
        match self {
            Type(_) | Unit | I32(_) | Builtin(_) | Tag(_) | Top | Bottom => false,
            Var(_, x, ty) => *x == s || ty.uses(s),
            Fun(_, v) => v.iter().any(|(a, b, c)| {
                !a.iter().any(|x| x.binds(s))
                    && !b.binds(s)
                    && !c.binds(s)
                    && (b.uses(s) || c.uses(s) || a.iter().any(|x| x.uses(s)))
            }),
            App(x, y) | Pair(x, y) => x.uses(s) || y.uses(s),
            Binder(_, x) => x.uses(s),
            // Can't use local variables
            StructIntern(_) => false,
            StructInline(v) => v.iter().any(|(_, x)| x.uses(s)),
            Project(r, _) => r.uses(s),
            Block(v) => v.iter().any(|x| match x {
                ElabStmt::Def(_, e) => e.uses(s),
                ElabStmt::Expr(e) => e.uses(s),
            }),
            Union(v) => v.iter().any(|x| x.uses(s)),
        }
    }

    /// Does this term bind this symbol somewhere?
    /// Only works for local variables, not ones you'd find in `db.elab()`
    pub fn binds(&self, s: Sym) -> bool {
        use Elab::*;
        match self {
            Type(_) | Unit | I32(_) | Builtin(_) | Tag(_) | Top | Bottom => false,
            Binder(x, ty) => *x == s || ty.binds(s),
            Fun(_, v) => v
                .iter()
                .any(|(a, b, c)| b.binds(s) || c.binds(s) || a.iter().any(|x| x.binds(s))),
            App(x, y) | Pair(x, y) => x.binds(s) || y.binds(s),
            Var(_, _, ty) => ty.binds(s),
            StructIntern(_) => false,
            StructInline(v) => v.iter().any(|(x, e)| *x == s || e.binds(s)),
            Project(r, _) => r.binds(s),
            Block(v) => v.iter().any(|x| match x {
                ElabStmt::Def(x, e) => *x == s || e.binds(s),
                ElabStmt::Expr(e) => e.binds(s),
            }),
            Union(v) => v.iter().any(|x| x.binds(s)),
        }
    }

    /// Reduce to full normal form, essentially recursively calling whnf()
    pub fn normal(self, ectx: &mut ECtx) -> Self {
        // Call whnf()
        let s = self.whnf(ectx);
        // And recurse
        use Elab::*;
        match s {
            Var(sp, s, mut ty) => {
                // Reuse the Box
                *ty = ty.normal(ectx);
                Var(sp, s, ty)
            }
            Fun(c, v) => Fun(
                c,
                v.into_iter()
                    .map(|(a, b, t)| {
                        (
                            a.into_iter().map(|a| a.normal(ectx)).collect(),
                            b.normal(ectx),
                            t.normal(ectx),
                        )
                    })
                    .collect(),
            ),
            App(mut x, mut y) => {
                // Reuse Boxes
                *x = x.normal(ectx);
                *y = y.normal(ectx);
                App(x, y)
            }
            Pair(mut x, mut y) => {
                // Reuse Boxes
                *x = x.normal(ectx);
                *y = y.normal(ectx);
                Pair(x, y)
            }
            Binder(s, mut x) => {
                *x = x.normal(ectx);
                Binder(s, x)
            }
            StructInline(v) => {
                StructInline(v.into_iter().map(|(s, x)| (s, x.normal(ectx))).collect())
            }
            Project(mut r, m) => {
                *r = r.normal(ectx);
                Project(r, m)
            }
            Block(v) => Block(
                v.into_iter()
                    .map(|x| match x {
                        ElabStmt::Def(s, e) => ElabStmt::Def(s, e.normal(ectx)),
                        ElabStmt::Expr(e) => ElabStmt::Expr(e.normal(ectx)),
                    })
                    .collect(),
            ),
            Union(v) => {
                Union(v.into_iter().map(|x| x.normal(ectx)).collect()).simplify_unions(ectx)
            }
            x => x,
        }
    }

    /// Reduce to Weak-Head Normal Form
    ///
    /// This is like actual normal form, but we only perform one level of beta- or projection-reduction
    /// So we're guaranteed not to have `(\x.t)u` at the top level, but we could have e.g. `(\x.(\y.t)u)`
    /// This is the form we store types in, so if you need to compare types you'll need to call `whnf` recursively
    pub fn whnf(self, ectx: &mut ECtx) -> Self {
        match self {
            // Binders don't count as forms
            Elab::Binder(s, mut t) => {
                // Reuse the Box
                *t = t.whnf(ectx);
                Elab::Binder(s, t)
            }
            // Unions don't either (no head)
            // (TODO somehow reuse the Vec)
            Elab::Union(v) => Elab::Union(v.into_iter().map(|x| x.whnf(ectx)).collect()),
            Elab::Var(sp, x, mut ty) => {
                if let Some(t) = ectx.val(x) {
                    match &*t {
                        // Update to the new type, but don't re-look-up the var
                        Elab::Var(sp, y, new_ty) if x == *y => Elab::Var(
                            *sp,
                            x,
                            Box::new(new_ty.cloned(&mut Cloner::new(&ectx)).whnf(ectx)),
                        ),
                        _ => t.cloned(&mut Cloner::new(&ectx)).whnf(ectx),
                    }
                } else {
                    *ty = ty.whnf(ectx);
                    Elab::Var(sp, x, ty)
                }
            }
            Elab::App(mut f, mut x) => {
                // We recursively WHNF the head
                *f = f.whnf(ectx);
                // We actually reduce the argument too, just not the body of functions etc.
                // We need to make sure to apply all substitutions that aren't behind a closure
                *x = x.whnf(ectx);
                match *f {
                    Elab::Fun(cl, v) => {
                        ectx.add_clos(&cl);
                        let tx = x.get_type(ectx);
                        let mut rf = Vec::new();
                        // If we find a branch that *might* match before one that *does*, we set this
                        let mut fuzzy = false;
                        for (mut args, body, to) in v {
                            // Guaranteed to match
                            if tx.subtype_of(args.first().unwrap(), ectx) {
                                args.first().unwrap().do_match(&x, ectx);
                                if !fuzzy && args.len() == 1 {
                                    return body.whnf(ectx);
                                } else {
                                    rf.push((args, body, to));
                                }
                            } else if tx.overlap(args.first().unwrap(), ectx) {
                                // Might match
                                fuzzy = true;
                                rf.push((args, body, to));
                            }
                        }
                        assert_ne!(rf.len(), 0, "none matched");
                        if fuzzy {
                            Elab::App(Box::new(Elab::Fun(cl, rf)), x)
                        } else {
                            let rf = rf
                                .into_iter()
                                .map(|(mut a, b, c)| {
                                    a.remove(0);
                                    (a, b, c)
                                })
                                .collect();
                            // If we passed in a move-only argument, it now captures it, so it's move-only
                            Elab::Fun(
                                Clos {
                                    is_move: cl.is_move || tx.multiplicity(ectx) == Mult::One,
                                    ..cl
                                },
                                rf,
                            )
                            .whnf(ectx)
                        }
                    }
                    Elab::App(f2, x2) => match &*f2 {
                        // This needs to be a binary operator, since that's the only builtin that takes two arguments
                        Elab::Builtin(b) => {
                            // Since we need them as i32s, we need to WHNF the arguments as well
                            // And we'd like to reuse these Boxes as well
                            match (b, &*x2, &*x) {
                                (Builtin::Add, Elab::I32(n), Elab::I32(m)) => Elab::I32(n + m),
                                (Builtin::Sub, Elab::I32(n), Elab::I32(m)) => Elab::I32(n - m),
                                (Builtin::Mul, Elab::I32(n), Elab::I32(m)) => Elab::I32(n * m),
                                (Builtin::Div, Elab::I32(n), Elab::I32(m)) => Elab::I32(n / m),
                                _ => Elab::App(Box::new(Elab::App(f2, x2)), x),
                            }
                        }
                        _ => Elab::App(Box::new(Elab::App(f2, x2)), x),
                    },
                    // Still not a function
                    _ => Elab::App(f, x),
                }
            }
            Elab::Project(r, m) => {
                // We recursively WHNF the head
                let r = r.whnf(ectx);
                match r {
                    Elab::StructIntern(i) => {
                        let scope = ScopeId::Struct(i, Box::new(ectx.scope()));
                        for i in ectx.database.symbols(scope.clone()).iter() {
                            if i.raw() == m {
                                let val = ectx.database.elab(scope.clone(), **i).unwrap();
                                return val.cloned(&mut Cloner::new(&ectx));
                            }
                        }
                        panic!("not found")
                    }
                    Elab::StructInline(v) => {
                        let (_, val) = v.into_iter().find(|(name, _)| name.raw() == m).unwrap();
                        return val;
                    }
                    // Still not a record
                    _ => Elab::Project(Box::new(r), m),
                }
            }
            Elab::Fun(mut cl, v) => {
                // Update the closure
                for (k, val) in ectx.vals.iter() {
                    if !cl.vals.iter().any(|(s, _)| s == k)
                        && !v.iter().any(|(a, b, c)| {
                            b.binds(*k) || c.binds(*k) || a.iter().any(|x| x.binds(*k))
                        })
                        && v.iter().any(|(a, b, c)| {
                            b.uses(*k) || c.uses(*k) || a.iter().any(|x| x.uses(*k))
                        })
                    {
                        cl.vals.push((*k, val.clone()));
                    }
                }
                Elab::Fun(cl, v)
            }
            x => x,
        }
    }

    /// Like `get_type()`, but looks up actual types for recursive calls. Should only be used after type checking.
    pub fn get_type_rec(&self, env: &(impl Scoped + HasDatabase)) -> Elab {
        match (self.get_type(env), self) {
            (Elab::Bottom, Elab::Var(_, s, _)) => {
                env.database().elab(env.scope(), *s).unwrap().get_type(env)
            }
            (x, _) => x,
        }
    }

    /// Gets the "best" type of `self`.
    pub fn get_type(&self, env: &(impl Scoped + HasDatabase)) -> Elab {
        use Elab::*;
        match self {
            Top => Top,
            Bottom => Type(0),
            Type(i) => Type(i + 1),
            Unit => Unit,
            I32(i) => I32(*i),
            Builtin(b) => b.get_type(),
            Tag(t) => Tag(*t),
            Var(_, _, t) => t.cloned(&mut Cloner::new(&env)),
            Fun(cl, v) => {
                let mut cln = Cloner::new(&env);
                Fun(
                    cl.cloned(&mut cln),
                    v.iter()
                        .map(|(from, _, to)| {
                            (
                                from.iter().map(|x| x.cloned(&mut cln)).collect(),
                                to.cloned(&mut cln),
                                to.get_type(env),
                            )
                        })
                        .collect(),
                )
            }
            App(f, x) => match f.get_type(env) {
                Fun(cl, v) => {
                    let mut rf = Vec::new();
                    let tx = x.get_type(env);
                    let mut ectx = ECtx::new(env);
                    ectx.add_clos(&cl);
                    let mut cln = Cloner::new(&env);
                    let mut fuzzy = false;

                    for (args, to, _) in v {
                        if tx.overlap(args.first().unwrap(), &ectx) {
                            let mut args: Vec<_> =
                                args.iter().map(|x| x.cloned(&mut cln)).collect();
                            let arg = args.remove(0);
                            arg.do_match(&x, &mut ectx);

                            // Only commit to this branch if it's guaranteed to match first
                            if !fuzzy && args.is_empty() && tx.subtype_of(&arg, &mut ectx) {
                                let to = to.cloned(&mut cln).whnf(&mut ectx);
                                return to;
                            } else {
                                // It could potentially match, but we're not sure
                                fuzzy = true;
                                let t = to.get_type(env);
                                let to = to.cloned(&mut cln);
                                rf.push((args, to, t));
                            }
                        }
                    }
                    debug_assert_ne!(
                        rf.len(),
                        0,
                        "None of {} matched {}",
                        f.get_type(env).pretty(env).ansi_string(),
                        tx.pretty(env).ansi_string()
                    );
                    if rf[0].0.is_empty() {
                        return Elab::Union(
                            rf.into_iter().map(|(a, b, c)| b.whnf(&mut ectx)).collect(),
                        )
                        .simplify_unions(&ectx);
                    }
                    // If we passed in a move-only argument, it now captures it, so it's move-only
                    Fun(
                        Clos {
                            is_move: cl.is_move || tx.multiplicity(env) == Mult::One,
                            ..cl
                        },
                        rf,
                    )
                    .whnf(&mut ectx)
                }
                f @ Tag(_) | f @ App(_, _) => App(Box::new(f), Box::new(x.get_type(env))),
                // This triggers with recursive functions
                Bottom => Bottom,
                _ => panic!("not a function type"),
            },
            Pair(x, y) => Pair(Box::new(x.get_type(env)), Box::new(y.get_type(env))),
            Binder(_, x) => x.get_type(env),
            StructIntern(id) => {
                let scope = ScopeId::Struct(*id, Box::new(env.scope()));
                // TODO rename
                StructInline(
                    env.database()
                        .symbols(scope.clone())
                        .iter()
                        .filter_map(|x| {
                            Some((**x, env.database().elab(scope.clone(), **x)?.get_type(env)))
                        })
                        .collect(),
                )
            }
            StructInline(v) => StructInline(v.iter().map(|(n, x)| (*n, x.get_type(env))).collect()),
            Project(r, m) => {
                if let StructInline(t) = r.get_type(env) {
                    t.iter()
                        .find(|(n, _)| n.raw() == *m)
                        .unwrap()
                        .1
                        .cloned(&mut Cloner::new(env))
                } else {
                    panic!("not a struct type")
                }
            }
            Block(v) => match v.last().unwrap() {
                ElabStmt::Def(_, _) => Unit,
                ElabStmt::Expr(e) => e.get_type(env),
            },
            // Unions can only be types, and the type of a union doesn't mean that much
            Union(_) => Type(self.universe(env)),
        }
    }

    /// What's the lowest universe this is definitely in - `self : TypeN`?
    pub fn universe(&self, env: &(impl Scoped + HasDatabase)) -> u32 {
        match self {
            Elab::Unit | Elab::I32(_) | Elab::Builtin(_) => 0,
            Elab::Tag(_) => 0,
            Elab::Bottom => 0,
            // TODO get rid of top
            Elab::Top => u32::MAX,
            Elab::Type(i) => i + 1,
            Elab::Binder(_, t) => t.universe(env),
            Elab::Var(_, _, t) => t.universe(env).saturating_sub(1),
            Elab::Pair(x, y) => x.universe(env).max(y.universe(env)),
            Elab::App(_, _) => match self.get_type(env) {
                Elab::App(f, x) => f.universe(env).max(x.universe(env)).saturating_sub(1),
                x => x.universe(env).saturating_sub(1),
            },
            Elab::Union(v) => v.iter().map(|x| x.universe(env)).max().unwrap_or(0),
            Elab::StructInline(v) => v.iter().map(|(_, x)| x.universe(env)).max().unwrap_or(0),
            Elab::StructIntern(id) => env
                .database()
                .symbols(ScopeId::Struct(*id, Box::new(env.scope())))
                .iter()
                .map(|x| {
                    env.database()
                        .elab(ScopeId::Struct(*id, Box::new(env.scope())), **x)
                        .map_or(0, |x| x.universe(env))
                })
                .max()
                .unwrap_or(0),
            Elab::Fun(_, v) => v
                .iter()
                .map(|(_, _, t)| t.universe(env).saturating_sub(1))
                .max()
                .unwrap_or(0),
            Elab::Project(r, m) => {
                if let Elab::StructInline(v) = r.get_type(env) {
                    v.iter()
                        .find(|(s, _)| s.raw() == *m)
                        .unwrap()
                        .1
                        .universe(env)
                        .saturating_sub(1)
                } else {
                    unreachable!()
                }
            }
            Elab::Block(_) => self.get_type(env).universe(env).saturating_sub(1),
        }
    }

    /// Adds substitutions created by matching `other` with `self` (`self` is the pattern) to `ctx`
    /// Does not check if it's a valid match, that's the typechecker's job
    pub fn do_match(&self, other: &Elab, ectx: &mut ECtx) {
        use Elab::*;
        match (self, other) {
            (Binder(s, _), _) => {
                let other = other.cloned(&mut Cloner::new(ectx)).whnf(ectx);
                #[cfg(feature = "logging")]
                {
                    println!(
                        "Setting {} := {}",
                        s.pretty(&ectx.bindings()).ansi_string(),
                        other.pretty(&ectx.bindings()).ansi_string()
                    );
                }
                ectx.set_val(*s, other);
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.do_match(bx, ectx);
                ay.do_match(by, ectx);
            }
            (App(af, ax), App(bf, bx)) => {
                af.do_match(bf, ectx);
                ax.do_match(bx, ectx);
            }
            _ => (),
        }
    }

    /// Clones `self`. Unlike a normal clone, we freshen any bound variables (but not free variables)
    /// This means that other code doesn't have to worry about capture-avoidance, we do it here for free
    pub fn cloned(&self, cln: &mut Cloner) -> Self {
        use Elab::*;
        match self {
            Var(sp, s, t) => {
                if let Some(x) = cln.get(*s) {
                    // Here's how this (`x == self`) happens:
                    // 1. We come up with a Elab using, say, x3. That Elab gets stored in Salsa's database.
                    // 2. We reset the Bindings, define x0, x1, and x2, and ask for the Elab again.
                    // 3. Salsa gives us the Elab from the database, which references x3. We call cloned() on it.
                    // 4. We see a bound variable, x3, and define a fresh variable to replace it with. The fresh variable is now also x3.
                    // 5. Now we want to replace x3 with x3, so we better not call cloned() recursively or we'll get stuck in a loop.
                    // Note, though, that this is expected behaviour and doesn't need fixing.
                    if x == *s {
                        Var(*sp, x, Box::new(t.cloned(cln)))
                    } else {
                        Var(*sp, x, Box::new(t.cloned(cln))).cloned(cln)
                    }
                } else {
                    // Free variable
                    Var(*sp, *s, Box::new(t.cloned(cln)))
                }
            }
            Top => Top,
            Bottom => Bottom,
            Unit => Unit,
            Type(i) => Type(*i),
            I32(i) => I32(*i),
            Builtin(b) => Builtin(*b),
            Tag(t) => Tag(*t),
            App(f, x) => App(Box::new(f.cloned(cln)), Box::new(x.cloned(cln))),
            // Rename bound variables
            // This case runs before any that depend on it, and the Elab has unique names
            Binder(s, t) => {
                let fresh = cln.bindings_mut().fresh(*s);
                #[cfg(feature = "logging")]
                {
                    let b = &cln.bindings();
                    println!(
                        "Renaming {}{} to {}{}",
                        b.resolve(*s),
                        s.num(),
                        b.resolve(fresh),
                        fresh.num()
                    );
                }
                cln.set(*s, fresh);
                Binder(fresh, Box::new(t.cloned(cln)))
            }
            // All these allow bound variables, so we have to make sure they're done in order
            Fun(cl, v) => Fun(
                cl.cloned(cln),
                v.iter()
                    .map(|(a, b, c)| {
                        (
                            a.iter().map(|x| x.cloned(cln)).collect(),
                            b.cloned(cln),
                            c.cloned(cln),
                        )
                    })
                    .collect(),
            ),
            Pair(x, y) => {
                let x = Box::new(x.cloned(cln));
                let y = Box::new(y.cloned(cln));
                Pair(x, y)
            }
            StructIntern(i) => {
                // The typechecker only creates a StructIntern if it doesn't capture any local variables, so we don't need to propagate renames into it
                // And we don't need to rename things inside it, because we'll do that when we access them
                // So we don't need to do anything here
                StructIntern(*i)
            }
            StructInline(v) => StructInline(
                v.into_iter()
                    .map(|(name, val)| {
                        let val = val.cloned(cln);
                        let fresh = cln.bindings_mut().fresh(*name);
                        #[cfg(feature = "logging")]
                        {
                            let b = &cln.bindings();
                            println!(
                                "Renaming {}{} to {}{}",
                                b.resolve(*name),
                                name.num(),
                                b.resolve(fresh),
                                fresh.num()
                            );
                        }
                        cln.set(*name, fresh);
                        (fresh, val)
                    })
                    .collect(),
            ),
            Project(r, m) => Project(Box::new(r.cloned(cln)), *m),
            Block(v) => Block(v.iter().map(|x| x.cloned(cln)).collect()),
            Union(v) => Union(v.iter().map(|x| x.cloned(cln)).collect()),
        }
    }
}

impl Pretty for Elab {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        match self {
            Elab::Unit => Doc::start("()").style(Style::Literal),
            Elab::Binder(x, t) => x
                .pretty(ctx)
                .add(":")
                .style(Style::Binder)
                .space()
                .chain(t.pretty(ctx))
                .prec(Prec::Term),
            Elab::Bottom => Doc::start("Empty"),
            Elab::Top => Doc::start("Any"),
            Elab::Var(_, s, _) => s.pretty(ctx),
            Elab::I32(i) => Doc::start(i).style(Style::Literal),
            Elab::Type(0) => Doc::start("Type"),
            Elab::Type(i) => Doc::start("Type").add(i),
            Elab::Builtin(b) => Doc::start(b),
            Elab::Fun(cl, v) if v.len() == 1 => {
                let (args, body, _) = v.first().unwrap();
                let until_body = if cl.is_move {
                    Doc::start("move").space().add("fun")
                } else {
                    Doc::start("fun")
                }
                .style(Style::Keyword)
                .line()
                .chain(Doc::intersperse(
                    args.iter().map(|x| x.pretty(ctx).nest(Prec::Atom)),
                    Doc::none().line(),
                ))
                .indent()
                .line()
                .add("=>");
                Doc::either(
                    until_body
                        .clone()
                        .line()
                        .add("  ")
                        .chain(body.pretty(ctx).indent())
                        .group(),
                    until_body.space().chain(body.pretty(ctx).indent()).group(),
                )
                .prec(Prec::Term)
            }
            Elab::Fun(cl, v) => pretty_block(
                "fun",
                v.iter().map(|(args, body, _)| {
                    let until_body = if cl.is_move {
                        Doc::start("move").space().add("fun")
                    } else {
                        Doc::start("fun")
                    }
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
                        args.iter().map(|x| x.pretty(ctx).nest(Prec::Atom)),
                        Doc::none().line(),
                    ))
                    .indent()
                    .line()
                    .add("=>");
                    Doc::either(
                        until_body
                            .clone()
                            .line()
                            .add("  ")
                            .chain(body.pretty(ctx).indent())
                            .group(),
                        until_body.space().chain(body.pretty(ctx).indent()).group(),
                    )
                }),
            ),
            Elab::App(x, y) => x
                .pretty(ctx)
                .nest(Prec::App)
                .space()
                .chain(y.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            Elab::Pair(x, y) => Doc::start("(")
                .chain(x.pretty(ctx))
                .add(",")
                .space()
                .chain(y.pretty(ctx))
                .add(")")
                .prec(Prec::Atom),
            Elab::Tag(id) => id.pretty(ctx),
            Elab::StructIntern(i) => Doc::start("struct#").style(Style::Keyword).add(i.num()),
            Elab::StructInline(v) => pretty_block(
                "struct",
                v.iter().map(|(name, val)| {
                    name.pretty(ctx)
                        .style(Style::Binder)
                        .space()
                        .add(":=")
                        .line()
                        .chain(val.pretty(ctx))
                        .group()
                }),
            ),
            Elab::Block(v) => pretty_block(
                "do",
                v.iter().map(|s| match s {
                    ElabStmt::Expr(e) => e.pretty(ctx),
                    ElabStmt::Def(name, val) => name
                        .pretty(ctx)
                        .style(Style::Binder)
                        .space()
                        .add(":=")
                        .line()
                        .chain(val.pretty(ctx))
                        .group(),
                }),
            ),
            Elab::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).chain(m.pretty(ctx)),
            Elab::Union(v) => Doc::intersperse(
                v.iter().map(|x| x.pretty(ctx)),
                Doc::none().space().add("|").space(),
            ),
        }
    }
}
