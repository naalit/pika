use crate::bicheck::TCtx;
use crate::common::*;
use crate::{
    pattern::Pat,
    term::{Builtin, STerm},
};
use std::collections::{HashMap, HashSet};
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

#[derive(Clone)]
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

    /// Gets it from the rename map, or returns it as-is if there's no rename set for it.
    /// This takes care of recursive renaming (x -> y -> z)
    pub fn get(&self, s: Sym) -> Sym {
        if let Some(k) = self.map.get(&s).copied() {
            // Here's how this (`k == s`) happens:
            // 1. We come up with a Elab using, say, x3. That Elab gets stored in Salsa's database.
            // 2. We reset the Bindings, define x0, x1, and x2, and ask for the Elab again.
            // 3. Salsa gives us the Elab from the database, which references x3. We call cloned() on it.
            // 4. We see a bound variable, x3, and define a fresh variable to replace it with. The fresh variable is now also x3.
            // 5. Now we want to replace x3 with x3, so we better not call get() recursively or we'll get stuck in a loop.
            // Note, though, that this is expected behaviour and doesn't need fixing.
            if k == s {
                k
            } else {
                self.get(k)
            }
        } else {
            s
        }
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

/// The closure object stores not just captured function environments, but also header-like information for functions.
#[derive(Debug, PartialEq, Eq, PartialOrd, Default)]
pub struct Clos {
    pub tys: Vec<(Sym, Arc<Elab>)>,
    pub vals: Vec<(Sym, Arc<Elab>)>,
    pub is_move: bool,
    pub implicit: bool,
    pub span: Span,
}
impl Clos {
    pub fn empty(is_move: bool) -> Self {
        Clos {
            is_move,
            implicit: false,
            tys: Vec::new(),
            vals: Vec::new(),
            span: Span::empty(),
        }
    }

    /// We need to rename anything stored in the closure, too, since it can use local variables
    pub fn cloned(&self, cln: &mut Cloner) -> Self {
        Clos {
            tys: self
                .tys
                .iter()
                .map(|(k, v)| (cln.get(*k), Arc::new(v.cloned(cln))))
                .collect(),
            vals: self
                .vals
                .iter()
                .map(|(k, v)| (cln.get(*k), Arc::new(v.cloned(cln))))
                .collect(),
            is_move: self.is_move,
            implicit: self.implicit,
            span: self.span,
        }
    }
}
impl<'a> TCtx<'a> {
    pub fn clos(&self, t: &STerm, is_move: bool, implicit: bool) -> Clos {
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
            implicit,
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
    Unit,                                           // ()
    Binder(Sym, BElab),                             // x: T
    Var(Span, Sym, BElab), // (a, T) --> the T a; we need the span for "moved variable" errors
    I32(i32),              // 3
    Type(u32),             // Type0
    Builtin(Builtin),      // Int
    CaseOf(Box<Elab>, Vec<(Pat, Elab)>, Box<Elab>), // case x of { a => the T b }
    Fun(Clos, Box<Elab>, Box<Elab>), // fun x => y
    App(BElab, BElab),     // f x
    Pair(BElab, BElab),    // x, y
    Data(TypeId, StructId, BElab), // type D: T of ...
    Cons(TagId, BElab),    // C : D
    StructIntern(StructId), // struct { x := 3 }
    StructInline(Vec<(Sym, Elab)>), // struct { x := 3 }
    Project(BElab, RawSym), // r.m
    Block(Vec<ElabStmt>),  // do { x; y }
    Union(Vec<Elab>),      // x | y
    Bottom,                // empty
    Top,                   // any
}
type BElab = Box<Elab>;

impl Elab {
    /// Returns a list of all free variables in this term
    pub fn fvs(&self, ectx: &ECtx) -> Vec<Sym> {
        // Add the symbols currently bound in the environment to the bound list
        let mut bound = ectx.vals.keys().copied().collect();
        let mut free = Vec::new();
        self.fvs_(&mut bound, &mut free);
        // Instead of adding the symbols in the database to the bound list, just check afterwards
        free.retain(|s| ectx.database().term(ectx.scope(), *s).is_none());
        free
    }

    /// Helper for `fvs`
    pub fn fvs_(&self, bound: &mut HashSet<Sym>, free: &mut Vec<Sym>) {
        use Elab::*;
        match self {
            Type(_) | Unit | I32(_) | Builtin(_) | Top | Bottom => (),
            Var(_, x, ty) => {
                if !bound.contains(x) {
                    free.push(*x);
                }
                ty.fvs_(bound, free);
            }
            CaseOf(val, cases, _) => {
                val.fvs_(bound, free);
                for (pat, body) in cases {
                    pat.fvs_(bound, free);
                    body.fvs_(bound, free);
                }
            }
            Fun(cl, x, y) => {
                for (k, _) in &cl.vals {
                    bound.insert(*k);
                }
                x.fvs_(bound, free);
                y.fvs_(bound, free);
            }
            App(x, y) | Pair(x, y) => {
                x.fvs_(bound, free);
                y.fvs_(bound, free);
            }
            Binder(s, t) => {
                t.fvs_(bound, free);
                bound.insert(*s);
            }
            // TODO outlaw locals in data types
            Data(_, _, _) | Cons(_, _) => (),
            // Can't use local variables
            StructIntern(_) => (),
            StructInline(v) => {
                for (k, v) in v {
                    bound.insert(*k);
                    v.fvs_(bound, free);
                }
            }
            Project(r, _) => r.fvs_(bound, free),
            Block(v) => v.iter().for_each(|x| match x {
                ElabStmt::Def(x, e) => {
                    bound.insert(*x);
                    e.fvs_(bound, free);
                }
                ElabStmt::Expr(e) => e.fvs_(bound, free),
            }),
            Union(v) => v.iter().for_each(|x| x.fvs_(bound, free)),
        }
    }

    /// Binders are usually confusing in type errors, so you can get rid of them
    pub fn unbind(&self) -> &Self {
        match self {
            Elab::Binder(_, x) => x,
            x => x,
        }
    }

    /// The analog of `head()` for function return values.
    /// `result(fun x => fun y => z) = z`
    pub fn result(&self) -> &Elab {
        match self {
            Elab::Fun(_, _, x) => x.result(),
            _ => self,
        }
    }

    /// If this term is an application, what's the function that's being applied? If not, returns itself.
    /// `head((f x y) z) = f`
    pub fn head(&self) -> &Elab {
        match self {
            Elab::App(f, _) => f.head(),
            _ => self,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Elab::Fun(_, _, to) => to.arity() + 1,
            _ => 0,
        }
    }

    /// How many `App` nodes are there chained together left-associatively?
    pub fn spine_len(&self) -> usize {
        match self {
            Elab::App(f, _) => f.spine_len() + 1,
            _ => 0,
        }
    }

    pub fn cons(&self) -> Option<TagId> {
        match self {
            Elab::Cons(id, _) => Some(*id),
            Elab::App(f, _) => f.cons(),
            _ => None,
        }
    }

    pub fn simplify_unions(mut self, ectx: &ECtx) -> Self {
        match &mut self {
            Elab::Union(v) => {
                match v.len() {
                    0 => self,
                    1 => v.pop().unwrap(),
                    _ => {
                        let mut tctx = TCtx::from(ectx.clone());
                        let mut rv: Vec<Elab> = Vec::new();
                        for val in v.split_off(0) {
                            let mut i = 0;
                            let mut should_add = true;
                            while i < rv.len() {
                                let x = &rv[i];

                                // If `val` covers `x`'s case, we don't need `x`
                                if x.unify(&val, &mut tctx, &mut Vec::new()) {
                                    rv.remove(i);
                                } else {
                                    i += 1;
                                    // but if `x` covers `val`'s case, we don't need `val`
                                    if val.unify(x, &mut tctx, &mut Vec::new()) {
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
                }
            }
            _ => self,
        }
    }

    /// Does this term reference this symbol at all?
    /// Only works for local variables, not ones you'd find in `db.elab()`
    pub fn uses(&self, s: Sym) -> bool {
        use Elab::*;
        match self {
            Type(_) | Unit | I32(_) | Builtin(_) | Top | Bottom => false,
            Var(_, x, ty) => *x == s || ty.uses(s),
            // TODO Pat::uses()
            CaseOf(val, cases, ty) => {
                val.uses(s) || ty.uses(s) || cases.iter().any(|(pat, body)| body.uses(s))
            }
            App(x, y) | Pair(x, y) | Fun(_, x, y) => x.uses(s) || y.uses(s),
            Binder(_, x) => x.uses(s),
            // TODO outlaw locals in data types
            Data(_, _, _) | Cons(_, _) => false,
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
            Type(_) | Unit | I32(_) | Builtin(_) | Top | Bottom => false,
            Binder(x, ty) => *x == s || ty.binds(s),
            // TODO Pat::binds()
            CaseOf(val, cases, ty) => {
                val.binds(s) || ty.binds(s) || cases.iter().any(|(pat, body)| body.binds(s))
            }
            App(x, y) | Pair(x, y) | Fun(_, x, y) => x.binds(s) || y.binds(s),
            Var(_, _, ty) => ty.binds(s),
            // TODO outlaw locals in data types
            Data(_, _, _) | Cons(_, _) => false,
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
            Fun(cl, mut from, mut to) => {
                ectx.add_clos(&cl);
                Fun(
                    cl,
                    {
                        *from = from.normal(ectx);
                        from
                    },
                    {
                        *to = to.normal(ectx);
                        to
                    },
                )
            }
            CaseOf(mut val, cases, mut ty) => CaseOf(
                {
                    *val = val.normal(ectx);
                    val
                },
                cases
                    .into_iter()
                    .map(|(pat, body)| (pat, body.normal(ectx)))
                    .collect(),
                {
                    *ty = ty.normal(ectx);
                    ty
                },
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
            Data(a, b, mut t) => {
                *t = t.normal(ectx);
                Data(a, b, t)
            }
            Cons(id, mut t) => {
                *t = t.normal(ectx);
                Cons(id, t)
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
    /// This is the form we store types in, so if you need to compare types you'll need to call `whnf` recursively.
    /// `whnf()` implies `save_ctx()`
    pub fn whnf(self, ectx: &mut ECtx) -> Self {
        match self {
            // Binders don't count as forms
            Elab::Binder(s, mut t) => {
                // Reuse the Box
                *t = t.whnf(ectx);
                Elab::Binder(s, t)
            }
            Elab::Cons(id, mut t) => {
                *t = t.whnf(ectx);
                Elab::Cons(id, t)
            }
            Elab::Pair(mut x, mut y) => {
                *x = x.whnf(ectx);
                *y = y.whnf(ectx);
                Elab::Pair(x, y)
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
                    Elab::Fun(cl, from, to) => {
                        ectx.add_clos(&cl);
                        from.do_match(&x, ectx);
                        to.whnf(ectx)
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
            Elab::Fun(mut cl, from, to) => {
                // Update the closure
                for (k, val) in ectx.vals.iter() {
                    if !cl.vals.iter().any(|(s, _)| s == k)
                        && !from.binds(*k)
                        && !to.binds(*k)
                        && (from.uses(*k) || to.uses(*k))
                    {
                        cl.vals.push((*k, val.clone()));
                    }
                }
                Elab::Fun(cl, from, to)
            }
            Elab::CaseOf(mut val, mut cases, mut ty) => {
                *val = val.whnf(ectx);
                *ty = ty.whnf(ectx);
                for i in 0..cases.len() {
                    match cases[i].0.matches(&val, ectx) {
                        Yes => return cases.swap_remove(i).1.whnf(ectx),
                        No => (),
                        // If it might match, we don't want another case to return Yes
                        Maybe => break,
                    }
                }
                // None of them is guaranteed to match, so don't reduce it yet
                Elab::CaseOf(val, cases, ty)
            }
            Elab::StructInline(v) => {
                Elab::StructInline(v.into_iter().map(|(k, v)| (k, v.whnf(ectx))).collect())
            }
            x => x,
        }
    }

    /// Inlines any *local* variables, but not global ones, and doesn't reduce applications, case-of, or projections.
    pub fn save_ctx(self, ectx: &ECtx) -> Self {
        match self {
            // Binders don't count as forms
            Elab::Binder(s, mut t) => {
                // Reuse the Box
                *t = t.save_ctx(ectx);
                Elab::Binder(s, t)
            }
            Elab::Cons(id, mut t) => {
                *t = t.save_ctx(ectx);
                Elab::Cons(id, t)
            }
            // Unions don't either (no head)
            // (TODO somehow reuse the Vec)
            Elab::Union(v) => Elab::Union(v.into_iter().map(|x| x.save_ctx(ectx)).collect()),
            Elab::Var(sp, x, mut ty) => {
                if let Some(t) = ectx.vals.get(&x) {
                    match &**t {
                        // Update to the new type, but don't re-look-up the var
                        Elab::Var(sp, y, new_ty) if x == *y => Elab::Var(
                            *sp,
                            x,
                            Box::new(new_ty.cloned(&mut Cloner::new(&ectx)).save_ctx(ectx)),
                        ),
                        _ => t.cloned(&mut Cloner::new(&ectx)).save_ctx(ectx),
                    }
                } else {
                    *ty = ty.save_ctx(ectx);
                    Elab::Var(sp, x, ty)
                }
            }
            Elab::App(mut f, mut x) => {
                // We recursively WHNF the head
                *f = f.save_ctx(ectx);
                // We actually reduce the argument too, just not the body of functions etc.
                // We need to make sure to apply all substitutions that aren't behind a closure
                *x = x.save_ctx(ectx);
                Elab::App(f, x)
            }
            Elab::Project(mut r, m) => {
                *r = r.save_ctx(ectx);
                Elab::Project(r, m)
            }
            Elab::Fun(mut cl, from, to) => {
                // Update the closure
                for (k, val) in ectx.vals.iter() {
                    if !cl.vals.iter().any(|(s, _)| s == k)
                        && !from.binds(*k)
                        && !to.binds(*k)
                        && (from.uses(*k) || to.uses(*k))
                    {
                        cl.vals.push((*k, val.clone()));
                    }
                }
                Elab::Fun(cl, from, to)
            }
            Elab::CaseOf(mut val, cases, mut ty) => {
                *val = val.save_ctx(ectx);
                *ty = ty.save_ctx(ectx);
                // TODO Pat::save_ctx()
                let cases = cases
                    .into_iter()
                    .map(|(p, x)| (p, x.save_ctx(ectx)))
                    .collect();
                Elab::CaseOf(val, cases, ty)
            }
            Elab::Pair(mut x, mut y) => {
                *x = x.save_ctx(ectx);
                *y = y.save_ctx(ectx);
                Elab::Pair(x, y)
            }
            Elab::StructInline(v) => {
                Elab::StructInline(v.into_iter().map(|(k, v)| (k, v.save_ctx(ectx))).collect())
            }
            // Elab::Block(_) => {}
            // Elab::Data(_, _, _) => {}
            // Elab::Builtin(_) => {}
            // Elab::Type(_) => {}
            // Elab::StructIntern(_) => {}
            // Elab::Bottom => {}
            // Elab::Top => {}
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
            I32(_) => Builtin(crate::term::Builtin::Int),
            Builtin(b) => b.get_type(),
            Var(_, _, t) => t.cloned(&mut Cloner::new(&env)),
            Data(_, _, t) | Cons(_, t) => t.cloned(&mut Cloner::new(&env)),
            Fun(cl, from, to) => {
                let mut cln = Cloner::new(&env);
                // We can determine types from Elabs without context, so no need to match types or apply the closure
                // However, if we have e.g. `fun (a0:) (x:a0) => x`, we type it as `fun (a1:) a1 => a1`, so we need to clone the body before or after typing it, and after is usually less work
                let from = from.cloned(&mut cln);
                let to = to.get_type(env).cloned(&mut cln);
                Fun(cl.cloned(&mut cln), Box::new(from), Box::new(to))
            }
            CaseOf(_, _, t) => t.cloned(&mut Cloner::new(&env)),
            App(f, x) => match f.get_type(env) {
                Fun(cl, from, to) => {
                    // We need to WHNF the body, with the appropriate definitions in scope
                    let mut ectx = ECtx::new(env);
                    ectx.add_clos(&cl);
                    // And of course, the return type can depend on the argument value, so pass it that
                    from.do_match(&x, &mut ectx);
                    to.whnf(&mut ectx)
                }
                // This triggers with recursive functions
                Bottom => Bottom,
                Top => Top,
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
            Elab::Bottom => 0,
            // TODO get rid of top
            Elab::Top => u32::MAX,
            Elab::Type(i) => i + 1,
            Elab::Binder(_, t) => t.universe(env),
            Elab::Var(_, _, t) | Elab::CaseOf(_, _, t) => t.universe(env).saturating_sub(1),
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
            Elab::Fun(_, _, to) => to.universe(env),
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
            Elab::Data(_, _, t) | Elab::Cons(_, t) => t.universe(env).saturating_sub(1),
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
                        s.pretty(&ectx).ansi_string(),
                        other.pretty(&ectx).ansi_string()
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
            Var(sp, s, t) => Var(*sp, cln.get(*s), Box::new(t.cloned(cln))),
            Top => Top,
            Bottom => Bottom,
            Unit => Unit,
            Type(i) => Type(*i),
            I32(i) => I32(*i),
            Builtin(b) => Builtin(*b),
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
            Fun(cl, from, to) => {
                let from = from.cloned(cln);
                let to = to.cloned(cln);
                Fun(cl.cloned(cln), Box::new(from), Box::new(to))
            }
            CaseOf(val, cases, ty) => CaseOf(
                Box::new(val.cloned(cln)),
                cases
                    .iter()
                    .map(|(pat, body)| (pat.cloned(cln), body.cloned(cln)))
                    .collect(),
                Box::new(ty.cloned(cln)),
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
            Data(a, b, t) => Data(*a, *b, Box::new(t.cloned(cln))),
            Cons(id, t) => Cons(*id, Box::new(t.cloned(cln))),
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
            // TODO pretty currying
            Elab::Fun(cl, from, to) => {
                let until_body = if cl.is_move {
                    Doc::start("move").space().add("fun")
                } else {
                    Doc::start("fun")
                }
                .style(Style::Keyword)
                // .line()
                // .add("{")
                // .line()
                // .chain(Doc::intersperse(
                //     cl.vals
                //         .iter()
                //         .map(|(k, v)| k.pretty(ctx).space().add(":=").space().chain(v.pretty(ctx))),
                //     Doc::start(",").space(),
                // ))
                // .line()
                // .add("}")
                .line()
                .chain(if cl.implicit {
                    Doc::start("[").chain(from.pretty(ctx)).add("]")
                } else {
                    from.pretty(ctx).nest(Prec::Atom)
                })
                .line()
                .add("=>");
                Doc::either(
                    until_body
                        .clone()
                        .line()
                        .add("  ")
                        .chain(to.pretty(ctx).indent())
                        .group(),
                    until_body.space().chain(to.pretty(ctx).indent()).group(),
                )
                .prec(Prec::Term)
            }
            Elab::CaseOf(val, cases, _) => Doc::start("case")
                .style(Style::Keyword)
                .space()
                .chain(val.pretty(ctx))
                .space()
                .chain(pretty_block(
                    "of",
                    cases.iter().map(|(pat, body)| {
                        pat.pretty(ctx)
                            .line()
                            .add("=>")
                            .line()
                            .chain(body.pretty(ctx))
                            .indent()
                            .group()
                    }),
                )),
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
            Elab::Data(id, _, _) => Doc::start("type")
                .style(Style::Keyword)
                .space()
                .chain(id.pretty(ctx).style(Style::Binder))
                .group(),
            Elab::Cons(id, _) => id.pretty(ctx),
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
            Elab::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).add(".").chain(m.pretty(ctx)),
            Elab::Union(v) => Doc::intersperse(
                v.iter().map(|x| x.pretty(ctx)),
                Doc::none().space().add("|").space(),
            ),
        }
    }
}
