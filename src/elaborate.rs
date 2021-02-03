use crate::common::*;
use crate::term::*;
use std::sync::Arc;
use std::time::Instant;

#[derive(Debug, Clone, PartialEq)]
pub enum MetaEntry {
    Solved(Arc<Val>, Span),
    Unsolved(Option<Name>, Span, MetaSource),
}

use std::collections::HashMap;
type Rename = HashMap<Lvl, Lvl>;

impl Term {
    /// Applies `ren`, and makes sure `self` is a valid solution to `meta` in this scope.
    /// Checks to make sure any locals it uses are in `ren` ("scope check"), and that it doesn't contain `meta` ("occurs check").
    fn check_solution(
        self,
        meta: Spanned<Var<Lvl>>,
        ren: &mut Rename,
        // The level this term was previously enclosed in
        lfrom: Lvl,
        // The level this term will be enclosed in after check_solution()
        lto: Lvl,
        names: &mut Names,
    ) -> Result<Term, TypeError> {
        match self {
            Term::Var(v, _) if v.cvt(lfrom) == *meta => {
                Err(TypeError::MetaOccurs(meta.span(), *meta))
            }
            Term::Var(v, mut ty) => {
                *ty = ty.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                match v {
                    // We store the renamings as levels and go between here, since indices change inside lambdas but levels don't.
                    Var::Local(ix) => match ren.get(&ix.to_lvl(lfrom)) {
                        Some(lvl) => Ok(Term::Var(Var::Local(lvl.to_ix(lto)), ty)),
                        None => {
                            println!("wrong {:?} = {:?}", ix, ix.to_lvl(lfrom));
                            Err(TypeError::MetaScope(meta.span(), *meta, names.get(ix)))
                        }
                    },
                    // The type of something can't depend on its own value
                    // TODO a different error for this case? Is this even possible?
                    Var::Rec(id) if matches!(*meta, Var::Meta(Meta::Global(id2, _)) if id2 == id) =>
                    {
                        println!("type depends on value: {:?}", meta);
                        Err(TypeError::MetaOccurs(meta.span(), *meta))
                    }
                    v => Ok(Term::Var(v, ty)),
                }
            }
            Term::Lam(n, i, mut ty, mut t) => {
                *ty = ty.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                // Allow the body to use the bound variable
                ren.insert(lfrom.inc(), lto.inc());
                names.add(n);
                *t = t.check_solution(meta, ren, lfrom.inc(), lto.inc(), names)?;
                names.remove();
                Ok(Term::Lam(n, i, ty, t))
            }
            Term::Pi(n, i, mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                // Allow the body to use the bound variable
                ren.insert(lfrom.inc(), lto.inc());
                names.add(n);
                *b = b.check_solution(meta, ren, lfrom.inc(), lto.inc(), names)?;
                names.remove();
                Ok(Term::Pi(n, i, a, b))
            }
            Term::Fun(mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *b = b.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::Fun(a, b))
            }
            Term::App(i, mut a, mut fty, mut b) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *fty = fty.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *b = b.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::App(i, a, fty, b))
            }
            Term::Error => Ok(Term::Error),
            Term::Type => Ok(Term::Type),
            Term::Lit(x, t) => Ok(Term::Lit(x, t)),
            Term::Case(mut x, mut ty, cases) => {
                let cases = cases
                    .into_iter()
                    .map(|(pat, body)| {
                        let mut names = names.clone();
                        let mut lfold = lfrom;
                        let lfrom = pat.add_names(lfrom, &mut names);
                        let mut lto = lto;
                        // Adjust lfrom and lto by the same amount
                        while lfold != lfrom {
                            lfold = lfold.inc();
                            lto = lto.inc();
                        }
                        Ok((
                            pat,
                            body.check_solution(meta.clone(), ren, lfrom, lto, &mut names)?,
                        ))
                    })
                    .collect::<Result<_, _>>()?;
                *x = x.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *ty = ty.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::Case(x, ty, cases))
            }
            Term::If(mut cond, mut yes, mut no) => {
                *cond = cond.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *yes = yes.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *no = no.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::If(cond, yes, no))
            }
        }
    }
}

/// A snapshot of the state of a `MCxt`, so you can clone and restore states for scoping without affecting meta solutions.
///
/// We'll probably eventually switch to storing meta solutions as an `Rc<RefCell<>>` or similar, and get rid of this type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CxtState {
    pub cxt: Cxt,
    pub size: Lvl,
    pub local_constraints: HashMap<Lvl, Val>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MCxtType {
    Local(DefId),
    Global(PreDefId),
}

/// The context used for typechecking a term.
/// Besides storing a `Cxt` for name resolution, stores meta solutions and local constraints.
/// Most operations also require a database to interact with the `Cxt`.
#[derive(Debug, Clone, PartialEq)]
pub struct MCxt {
    pub cxt: Cxt,
    pub size: Lvl,
    ty: MCxtType,
    local_metas: Vec<MetaEntry>,
    local_constraints: HashMap<Lvl, Val>,
    solved_globals: Vec<RecSolution>,
    children: Vec<DefId>,
}
impl MCxt {
    pub fn state(&self) -> CxtState {
        CxtState {
            cxt: self.cxt,
            size: self.size,
            local_constraints: self.local_constraints.clone(),
        }
    }
    pub fn set_state(&mut self, state: CxtState) {
        let CxtState {
            cxt,
            size,
            local_constraints,
        } = state;
        self.cxt = cxt;
        self.size = size;
        self.local_constraints = local_constraints;
    }

    pub fn new(cxt: Cxt, ty: MCxtType, db: &dyn Compiler) -> Self {
        MCxt {
            cxt,
            size: cxt.size(db),
            ty,
            local_metas: Vec::new(),
            local_constraints: HashMap::new(),
            solved_globals: Vec::new(),
            children: Vec::new(),
        }
    }

    /// Checks if a local has a constraint on its value, and if so returns it.
    pub fn local_val(&self, lvl: Lvl) -> Option<&Val> {
        self.local_constraints.get(&lvl)
    }

    /// Looks up the name of a local in the context.
    ///
    /// Panics if the given index is larger than the size of the context.
    pub fn local_name(&self, mut ix: Ix, db: &dyn Compiler) -> Name {
        let mut cxt = self.cxt;
        loop {
            match db.lookup_cxt_entry(cxt) {
                MaybeEntry::Yes(CxtEntry {
                    rest, info, name, ..
                }) => {
                    cxt = rest;
                    match info {
                        NameInfo::Local(_) => {
                            if ix == Ix::zero() {
                                break name;
                            } else {
                                ix = ix.dec();
                            }
                        }
                        _ => continue,
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    /// Looks up the type of a local in the context.
    ///
    /// Panics if the given index is larger than the size of the context.
    pub fn local_ty(&self, mut ix: Ix, db: &dyn Compiler) -> VTy {
        let mut cxt = self.cxt;
        loop {
            match db.lookup_cxt_entry(cxt) {
                MaybeEntry::Yes(CxtEntry { rest, info, .. }) => {
                    cxt = rest;
                    match info {
                        NameInfo::Local(ty) => {
                            if ix == Ix::zero() {
                                break ty;
                            } else {
                                ix = ix.dec();
                            }
                        }
                        _ => continue,
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    /// Looks up a name in the context.
    pub fn lookup(&self, name: Name, db: &dyn Compiler) -> Result<(Var<Ix>, VTy), DefError> {
        self.cxt.lookup(name, db)
    }

    /// Adds a definition to the context, and handles increasing the cached size.
    pub fn define(&mut self, name: Name, info: NameInfo, db: &dyn Compiler) {
        if let NameInfo::Local(_) = &info {
            self.size = self.size.inc();
        }
        self.cxt = self.cxt.define(name, info, db);
        debug_assert_eq!(self.size, self.cxt.size(db));
    }

    /// Looks up the solution to the given meta, if one exists.
    pub fn get_meta(&self, meta: Meta) -> Option<Val> {
        match meta {
            Meta::Global(id, n) => self
                .solved_globals
                .iter()
                .find(|s| s.id() == id && s.num() == n)
                .map(|s| s.val().clone()),
            Meta::Local(def, num) => {
                if let MCxtType::Local(d) = self.ty {
                    assert_eq!(def, d, "local meta escaped its definition!");
                }
                match &self.local_metas[num as usize] {
                    MetaEntry::Solved(v, _) => Some(Val::Arc(v.clone())), //.map(|x| x.inline_metas(self)),
                    MetaEntry::Unsolved(_, _, _) => None,
                }
            }
        }
    }

    /// Undoes the last call to `define()`.
    pub fn undef(&mut self, db: &dyn Compiler) {
        self.cxt = match db.lookup_cxt_entry(self.cxt) {
            MaybeEntry::Yes(CxtEntry { rest, info, .. }) => {
                if let NameInfo::Local(_) = &info {
                    self.size = self.size.dec();
                }
                rest
            }
            _ => panic!("Called undef() without define()!"),
        };
        debug_assert_eq!(self.size, self.cxt.size(db));
    }

    /// Creates an empty environment at the level this context is at.
    pub fn env(&self) -> Env {
        Env::new(self.size)
    }

    /// Registers a new local constraint generated by unification.
    pub fn solve_local(&mut self, local: Lvl, spine: &Spine, val: Val) -> Result<(), TypeError> {
        assert!(
            spine.is_empty(),
            "We don't support solving locals to lambdas yet"
        );

        // Just add it to the local constraints as is, it doesn't need lambdas or anything like a meta
        self.local_constraints.insert(local, val);

        Ok(())
    }

    /// Registers a meta solution found by unification.
    pub fn solve(
        &mut self,
        span: Span,
        meta: Meta,
        spine: &Spine,
        val: Val,
        db: &dyn Compiler,
    ) -> Result<(), TypeError> {
        // The value can only use variables that we're passing to the meta
        let mut meta_scope: Rename = spine
            .iter()
            // Each argument is another lambda we're going to wrap it in
            .zip(std::iter::successors(Some(self.size.inc()), |lvl| {
                Some(lvl.inc())
            }))
            .map(|((_, x), to_lvl)| match x.unarc() {
                Val::App(Var::Local(from_lvl), _, sp, _) if sp.is_empty() => (*from_lvl, to_lvl),
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect();
        let term = val.quote(self.size, &self, db);
        // The level it will be at after we wrap it in lambdas
        let to_lvl = (0..spine.len()).fold(self.size, |x, _| x.inc());

        // Get the type of each argument
        let tys: Vec<Ty> = spine
            .iter()
            .zip(std::iter::successors(Some(self.size), |lvl| {
                Some(lvl.inc())
            }))
            .map(|((_, v), l)| match v.unarc() {
                Val::App(Var::Local(_), ty, sp, _) if sp.is_empty() => {
                    (**ty).clone().quote(l, self, db)
                }
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect();

        let term = term.check_solution(
            Spanned::new(Var::Meta(meta), span),
            &mut meta_scope,
            self.size,
            to_lvl,
            &mut Names::new(self.cxt, db),
        )?;
        // Actually wrap it in lambdas
        // We could look up the local variables' names in the cxt, but it's probably not worth it
        let empty_name = db.intern_name("_".to_string());
        let term = tys.into_iter().rev().fold(term, |term, ty| {
            Term::Lam(empty_name, Icit::Expl, Box::new(ty), Box::new(term))
        });

        // Reevaluating the term so we don't have to clone it to quote it, and it should inline solved metas as well
        let val = term.evaluate(&Env::new(self.size), &self, db);
        // Now add it to the solved metas
        match meta {
            Meta::Global(id, n) => {
                self.solved_globals
                    .push(RecSolution::Inferred(id, n, span, val));
            }
            Meta::Local(def, idx) => {
                if let MCxtType::Local(d) = self.ty {
                    assert_eq!(def, d, "local meta escaped its definition!");
                }
                // TODO should we do anything with the span we already have in `local_metas`, where it was introduced?
                self.local_metas[idx as usize] = MetaEntry::Solved(Arc::new(val), span);
            }
        }
        Ok(())
    }

    /// Creates a new meta with no solution.
    pub fn new_meta(
        &mut self,
        name: Option<Name>,
        span: Span,
        source: MetaSource,
        ty: Ty,
        db: &dyn Compiler,
    ) -> Term {
        use std::convert::TryInto;

        let meta = match self.ty {
            MCxtType::Local(def) => Meta::Local(
                def,
                self.local_metas
                    .len()
                    .try_into()
                    .expect("Only 65535 metas allowed per definition"),
            ),
            MCxtType::Global(def) => Meta::Global(
                def,
                self.local_metas
                    .len()
                    .try_into()
                    .expect("Only 65535 metas allowed per definition"),
            ),
        };
        self.local_metas
            .push(MetaEntry::Unsolved(name, span, source));

        // Apply it to all the bound variables in scope
        self.size.apply_meta(Var::Meta(meta), ty, self, db)
    }

    /// Makes sure all local metas are solved.
    /// If some aren't, it reports errors to `db` and returns Err(()).
    pub fn check_locals(&mut self, db: &dyn Compiler) -> Result<(), ()> {
        if let MCxtType::Local(def) = self.ty {
            let mut ret = Ok(());
            for (i, entry) in self.local_metas.iter().enumerate() {
                match entry {
                    MetaEntry::Solved(_, _) => (),
                    MetaEntry::Unsolved(_, span, _) => {
                        db.report_error(Error::new(
                            self.cxt.file(db),
                            Doc::start("Could not find solution for ")
                                .chain(Meta::Local(def, i as u16).pretty(self, db))
                                .style(Style::Bold),
                            *span,
                            "search started here",
                        ));
                        ret = Err(());
                    }
                }
            }
            ret
        } else {
            panic!("Don't call check_locals() on a global MCxt!")
        }
    }
}
impl Var<Lvl> {
    fn pretty_meta(self, mcxt: &MCxt, db: &dyn Compiler) -> Doc {
        match self {
            Var::Meta(m) => m.pretty(mcxt, db),

            Var::Local(l) => Doc::start("constrained value of local ")
                .chain(Val::local(l, Val::Error).pretty(db, mcxt)),

            _ => unreachable!(),
        }
    }
}
impl Meta {
    fn pretty(self, mcxt: &MCxt, db: &dyn Compiler) -> Doc {
        match self {
            Meta::Global(id, _) => match &**db.lookup_intern_predef(id) {
                PreDef::Fun(n, _, _, _) => Doc::start("type of function '").add(n.get(db)).add("'"),
                PreDef::Val(n, _, _) => Doc::start("type of definition '").add(n.get(db)).add("'"),
                PreDef::Type(n, _, _, _) => {
                    Doc::start("type of data type '").add(n.get(db)).add("'")
                }
                PreDef::Impl(Some(n), _, _) => {
                    Doc::start("type of implicit '").add(n.get(db)).add("'")
                }
                PreDef::Impl(None, _, _) => Doc::start("type of implicit"),
                PreDef::Expr(_) => Doc::start("type of expression"),
                PreDef::FunDec(n, _, _) => Doc::start("type of function declaration '")
                    .add(n.get(db))
                    .add("'"),
                PreDef::ValDec(n, _) => Doc::start("type of declaration '").add(n.get(db)).add("'"),
                PreDef::Cons(_, _) => unreachable!("Constructor types should already be solved!"),
            },
            Meta::Local(_, n) => match &mcxt.local_metas[n as usize] {
                MetaEntry::Solved(_, _) => panic!("meta already solved"),
                MetaEntry::Unsolved(_, _, source) => match source {
                    MetaSource::ImplicitParam(n) => {
                        Doc::start("implicit parameter '").add(n.get(db)).add("'")
                    }
                    MetaSource::LocalType(n) => Doc::start("type of '").add(n.get(db)).add("'"),
                    MetaSource::Hole => Doc::start("hole"),
                    MetaSource::HoleType => Doc::start("type of hole"),
                },
            },
        }
    }
}

impl PreDef {
    /// Extracts the type given. If no type is given, returns a meta; if it doesn't typecheck, reports errors to the database and returns None.
    pub fn given_type(&self, id: PreDefId, cxt: Cxt, db: &dyn Compiler) -> Option<VTy> {
        let mut mcxt = MCxt::new(cxt, MCxtType::Global(id), db);
        match self {
            PreDef::Fun(_, args, rty, _) | PreDef::FunDec(_, args, rty) => {
                let mut rargs = Vec::new();
                elab_args(args, &mut rargs, cxt.file(db), &mut mcxt, db);
                match check(rty, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                    Ok(rty) => {
                        let rty = rty.evaluate(&mcxt.env(), &mcxt, db);
                        let mut l = mcxt.size;
                        Some(rargs.into_iter().rfold(rty, |rty, (name, i, xty)| {
                            let rty = rty.quote(l, &mcxt, db);
                            l = l.dec();
                            Val::Pi(
                                i,
                                Box::new(Clos {
                                    name,
                                    ty: xty,
                                    env: Env::new(l),
                                    term: rty,
                                }),
                            )
                        }))
                    }
                    Err(e) => {
                        db.report_error(e.to_error(cxt.file(db), db, &mcxt));
                        None
                    }
                }
            }
            PreDef::Type(_, args, _, _) => {
                let mut rargs = Vec::new();
                elab_args(args, &mut rargs, cxt.file(db), &mut mcxt, db);
                let mut l = mcxt.size;
                Some(rargs.into_iter().rfold(Val::Type, |rty, (name, i, xty)| {
                    let rty = rty.quote(l, &mcxt, db);
                    l = l.dec();
                    Val::Pi(
                        i,
                        Box::new(Clos {
                            name,
                            ty: xty,
                            env: Env::new(l),
                            term: rty,
                        }),
                    )
                }))
            }
            PreDef::Expr(x) => Some(
                mcxt.new_meta(
                    None,
                    x.span(),
                    MetaSource::LocalType(db.intern_name("_".to_string())),
                    Term::Type,
                    db,
                )
                .evaluate(&mcxt.env(), &mcxt, db),
            ),
            PreDef::ValDec(_, ty) | PreDef::Val(_, ty, _) | PreDef::Impl(_, ty, _) => {
                match check(ty, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                    Ok(ty) => Some(ty.evaluate(&mcxt.env(), &mcxt, db)),
                    Err(e) => {
                        db.report_error(e.to_error(cxt.file(db), db, &mcxt));
                        None
                    }
                }
            }
            PreDef::Cons(_, ty) => Some(ty.clone()),
        }
    }
}

pub fn elaborate_def(db: &dyn Compiler, def: DefId) -> Result<ElabInfo, DefError> {
    let start_time = Instant::now();

    let (predef_id, cxt) = db.lookup_intern_def(def);
    let predef = db.lookup_intern_predef(predef_id);
    let file = cxt.file(db);
    let mut mcxt = MCxt::new(cxt, MCxtType::Local(def), db);
    let (term, ty): (Term, VTy) = match &**predef {
        PreDef::Val(_, ty, val) | PreDef::Impl(_, ty, val) => {
            let tyspan = ty.span();
            match check(ty, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                Ok(ty) => {
                    let ty = ty.evaluate(&mcxt.env(), &mcxt, db);
                    match check(val, &ty, ReasonExpected::Given(tyspan), db, &mut mcxt) {
                        Ok(val) => Ok((val, ty)),
                        Err(e) => {
                            db.report_error(e.to_error(file, db, &mcxt));
                            Err(DefError::ElabError(def))
                        }
                    }
                }
                Err(e) => {
                    db.report_error(e.to_error(file, db, &mcxt));
                    // The given type is invalid, but we can still try to infer the type
                    match infer(true, val, db, &mut mcxt) {
                        Ok(x) => Ok(x),
                        Err(e) => {
                            db.report_error(e.to_error(file, db, &mcxt));
                            Err(DefError::ElabError(def))
                        }
                    }
                }
            }
        }
        PreDef::Fun(_, args, body_ty, body) => {
            // First, add the arguments to the environment
            let mut targs = Vec::new();
            elab_args(args, &mut targs, file, &mut mcxt, db);

            // Then elaborate and evaluate the given return type
            let tyspan = body_ty.span();
            let body_ty = match check(
                body_ty,
                &Val::Type,
                ReasonExpected::UsedAsType,
                db,
                &mut mcxt,
            ) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db, &mcxt));
                    // TODO make a meta? or just call `infer()`?
                    Term::Error
                }
            };
            let vty = body_ty.evaluate(&mcxt.env(), &mcxt, db);

            // And last, check the function body against the return type
            let body = match check(body, &vty, ReasonExpected::Given(tyspan), db, &mut mcxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db, &mcxt));
                    return Err(DefError::ElabError(def));
                }
            };

            // Then construct the function term and type
            Ok((
                targs
                    .iter()
                    .rfold((body, mcxt.size), |(body, mut size), (name, icit, ty)| {
                        // We need to quote the type of this argument, so decrease the size to
                        // remove this argument from the context, since its own type can't use it
                        size = size.dec();
                        (
                            Term::Lam(
                                *name,
                                *icit,
                                Box::new(ty.clone().quote(size, &mcxt, db)),
                                Box::new(body),
                            ),
                            size,
                        )
                    })
                    .0,
                targs
                    .into_iter()
                    .rfold((vty, mcxt.size), |(to, size), (name, icit, from)| {
                        (
                            Val::Pi(
                                icit,
                                Box::new(Clos {
                                    // Don't include the closure's argument in its environment
                                    env: Env::new(size.dec()),
                                    ty: from,
                                    term: to.quote(size, &mcxt, db),
                                    name,
                                }),
                            ),
                            size.dec(),
                        )
                    })
                    .0,
            ))
        }
        PreDef::Cons(_name, ty) => {
            // We don't have to do anything since the type was already determined when elaborating the type definition
            Ok((
                Term::Var(
                    Var::Cons(def),
                    Box::new(ty.clone().quote(mcxt.size, &mcxt, db)),
                ),
                ty.clone(),
            ))
        }
        PreDef::Type(name, args, cons, assoc) => {
            // A copy of the context before we added the type arguments
            let cxt_before = mcxt.state();

            // Evaluate the argument types and collect them up
            let mut targs = Vec::new();
            elab_args(args, &mut targs, file, &mut mcxt, db);

            // Create the type of the datatype we're defining (e.g. `Option : Type -> Type`)
            // We have to do this now, so that the constructors can use the type
            let (ty_ty, _) = targs
                .iter()
                .rfold((Val::Type, mcxt.size), |(to, l), (n, i, from)| {
                    (
                        Val::Pi(
                            *i,
                            Box::new(Clos {
                                env: Env::new(l.dec()),
                                ty: from.clone(),
                                term: to.clone().quote(l, &mcxt, db),
                                name: *n,
                            }),
                        ),
                        l.dec(),
                    )
                });
            mcxt.define(
                **name,
                NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()),
                db,
            );

            // The context after adding the type arguments, used when evaluating constructors without
            // explicit return types, where all type arguments are implicitly in scope
            let cxt_after = mcxt.state();

            // Add the datatype's type to the context before adding the type arguments for use by cons types
            mcxt.set_state(cxt_before);
            mcxt.define(
                **name,
                NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()),
                db,
            );
            let cxt_before = mcxt.state();

            let mut scope = Vec::new();

            // Go through the constructors and elaborate them
            let mut seen: HashMap<Name, Span> = HashMap::new();
            for PreCons(cname, args, cty) in cons {
                if let Some(&span) = seen.get(cname) {
                    let e = Error::new(
                        file,
                        format!(
                            "Duplicate constructor name '{}' in type definition",
                            db.lookup_intern_name(**cname)
                        ),
                        cname.span(),
                        "declared again here",
                    )
                    .with_label(file, span, "previously declared here");
                    db.report_error(e);
                    continue;
                } else {
                    seen.insert(**cname, cname.span());
                }

                let mut cargs = Vec::new();

                // If the user provided a type for the constructor, they can't use the type arguments
                // Either way, we need to reset it somewhat so we can't use arguments from other constructors
                // But we use the same mcxt, so meta solutions get saved, we just reset the `CxtState`
                if cty.is_some() {
                    mcxt.set_state(cxt_before.clone());
                } else {
                    mcxt.set_state(cxt_after.clone());
                    // If they can use the type parameters, add them all as implicit arguments
                    // They go in the same order as the type parameters, so we don't need to change the mcxt
                    for (n, _i, t) in &targs {
                        cargs.push((*n, Icit::Impl, t.clone()));
                    }
                }
                let start_size = mcxt.size;

                // Elaborate the constructor argument types
                elab_args(args, &mut cargs, file, &mut mcxt, db);

                // If the user provided a return type for the constructor, typecheck it
                let cty = if let Some(cty) = cty {
                    match check(cty, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                        Ok(x) => match x.ret().head() {
                            Term::Var(Var::Rec(id), _) if *id == predef_id => x,
                            _ => {
                                // We want the type to appear in the error message as it was written - e.g. `Result T E`
                                let mut type_string = db.lookup_intern_name(**name);
                                for (n, _, _) in &targs {
                                    type_string.push(' ');
                                    type_string.push_str(&db.lookup_intern_name(*n));
                                }
                                let e = Error::new(
                                    file,
                                    "Constructor return type must be the type it's a part of",
                                    cty.span(),
                                    Doc::start("expected return type ")
                                        .chain(Doc::start(type_string).style(Style::None))
                                        .style(Style::Error),
                                );
                                db.report_error(e);
                                Term::Error
                            }
                        },
                        Err(e) => {
                            db.report_error(e.to_error(file, db, &mcxt));
                            // TODO make a meta? or just call `infer()`?
                            Term::Error
                        }
                    }
                // If they didn't provide a return type, use the type constructor applied to all args
                } else {
                    // predef_id is for the type being declared
                    // Ty a b of C [a] [b] ... : Ty a b
                    // so Ix's decrease from left to right, and start at the first implicit argument
                    // which is right after the state cxt_before stores
                    let ty_ty = ty_ty.clone().quote(mcxt.size, &mcxt, db);
                    targs
                        .iter()
                        .fold(
                            (
                                Term::Var(Var::Rec(predef_id), Box::new(ty_ty.clone())),
                                cxt_before.size.to_ix(mcxt.size),
                                ty_ty.clone(),
                                mcxt.size,
                            ),
                            |(f, ix, ty, l), (_n, i, t)| {
                                let (rty, xty, l) = match &ty {
                                    Term::Pi(_, _, xty, x) => {
                                        // It might use the value, so give it that
                                        let mut env = Env::new(l);
                                        env.push(Some(Val::local(ix.to_lvl(l), t.clone())));
                                        (
                                            (**x)
                                                .clone()
                                                .evaluate(&env, &mcxt, db)
                                                .quote(mcxt.size, &mcxt, db),
                                            xty.clone(),
                                            l.inc(),
                                        )
                                    }
                                    Term::Fun(xty, x) => ((**x).clone(), xty.clone(), l),
                                    _ => unreachable!(),
                                };
                                let ix = ix.dec();
                                (
                                    Term::App(
                                        *i,
                                        Box::new(f),
                                        Box::new(ty),
                                        Box::new(Term::Var(Var::Local(ix), xty)),
                                    ),
                                    ix,
                                    rty,
                                    l,
                                )
                            },
                        )
                        .0
                };

                let (full_ty, _) =
                    cargs
                        .into_iter()
                        .rfold((cty, mcxt.size), |(to, l), (n, i, from)| {
                            (
                                Term::Pi(
                                    n,
                                    i,
                                    Box::new(from.quote(l.dec(), &mcxt, db)),
                                    Box::new(to),
                                ),
                                l.dec(),
                            )
                        });

                let full_ty = full_ty.evaluate(&Env::new(start_size), &mcxt, db);
                // .inline_metas(&mcxt, db);

                scope.push((cname.clone(), full_ty));
            }

            mcxt.set_state(cxt_before.clone());

            // Make sure to inline metas solved in constructor types
            let ty_ty = ty_ty.inline_metas(&mcxt, db);
            mcxt.undef(db);
            mcxt.define(
                **name,
                NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()),
                db,
            );
            let mut scope: Vec<_> = scope
                .into_iter()
                .map(|(cname, ty)| {
                    let ty = ty.inline_metas(&mcxt, db);
                    let def_id = db.intern_def(
                        db.intern_predef(Arc::new(PreDef::Cons(cname.clone(), ty).into())),
                        cxt_before.cxt,
                    );
                    (*cname, def_id)
                })
                .collect();

            // Add definitions from the associated namespace
            // They need the type of the datatype we're defining
            // They also need the constructors, so we create a temporary scope.
            // Since Var::unify doesn't compare the scope ids, it works.
            let tscope = db.intern_scope(Arc::new(scope.clone()));
            let assoc_cxt = cxt.define(
                **name,
                NameInfo::Other(Var::Type(def, tscope), ty_ty.clone()),
                db,
            );
            // And they have access to all the constructors in `scope` at the top level
            let assoc_cxt = scope.iter().fold(assoc_cxt, |cxt, &(n, v)| {
                cxt.define(n, NameInfo::Def(v), db)
            });
            scope.extend(
                intern_block(assoc.clone(), db, assoc_cxt)
                    .into_iter()
                    .filter_map(|id| {
                        let (pre, _) = db.lookup_intern_def(id);
                        let pre = db.lookup_intern_predef(pre);
                        // If it doesn't have a name, we don't include it in the Vec
                        // TODO: but then we don't elaborate it and check for errors. Does this ever happen?
                        pre.name().map(|n| (n, id))
                    })
                    .inspect(|(_, id)| {
                        // Report any errors
                        let _ = db.elaborate_def(*id);
                    }),
            );

            // Add the associated namespace, including constructors, to this term's children so they'll get lowered
            mcxt.children.extend(scope.iter().map(|&(_, id)| id));

            let scope = db.intern_scope(Arc::new(scope));

            Ok((
                Term::Var(
                    Var::Type(def, scope),
                    Box::new(ty_ty.clone().quote(mcxt.size, &mcxt, db)),
                ),
                ty_ty,
            ))
        }
        PreDef::Expr(e) => match infer(true, e, db, &mut mcxt) {
            Err(e) => {
                db.report_error(e.to_error(file, db, &mcxt));
                Err(DefError::ElabError(def))
            }
            Ok(stuff) => Ok(stuff),
        },
        PreDef::FunDec(_, from, to) => {
            // TODO: When function declarations are actually used, change this so they're dependent.
            for (_, _, from) in from {
                if let Err(e) = check(from, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                    db.report_error(e.to_error(file, db, &mcxt));
                }
            }
            if let Err(e) = check(to, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                db.report_error(e.to_error(file, db, &mcxt));
            }
            Err(DefError::NoValue)
        }
        PreDef::ValDec(_, ty) => {
            if let Err(e) = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
                db.report_error(e.to_error(file, db, &mcxt));
            }
            Err(DefError::NoValue)
        }
    }?;
    // mcxt.solved_globals
    //     .push(RecSolution::Defined(predef_id, 0, predef.span(), ty.clone()));
    let ret = match mcxt.check_locals(db) {
        Ok(()) => {
            let term = term.inline_metas(&mcxt, mcxt.size, db);
            let ty = ty.inline_metas(&mcxt, db);

            // Print out the type and value of each definition
            // let d = Doc::keyword("val")
            //     .space()
            //     .add(predef.name().map_or("_".to_string(), |x| x.get(db)))
            //     .space()
            //     .add(":")
            //     .space()
            //     .chain(ty.pretty(db, &mcxt))
            //     .space()
            //     .add("=")
            //     .space()
            //     .chain(term.pretty(db, &mut Names::new(mcxt.cxt, db)));
            // println!("{}\n", d.ansi_string());

            Ok(ElabInfo {
                term: Arc::new(term),
                typ: Arc::new(ty),
                solved_globals: Arc::new(mcxt.solved_globals),
                children: Arc::new(mcxt.children),
            })
        }
        Err(()) => {
            // We don't want the term with local metas in it getting out
            Err(DefError::ElabError(def))
        }
    };

    if let Ok(ret) = &ret {
        if predef.attributes.contains(&Attribute::Elaborate) {
            let end_time = Instant::now();
            let name = predef
                .name()
                .map(|x| db.lookup_intern_name(x))
                .unwrap_or("<unnamed>".into());
            println!("Elaborate time for {}: {:?}", name, end_time - start_time);
        }
        if predef.attributes.contains(&Attribute::Normalize) {
            let mcxt = MCxt::new(cxt, MCxtType::Local(def), db);
            let term = (*ret.term).clone();

            let n_start = Instant::now();
            let _ = term
                .evaluate(&mcxt.env(), &mcxt, db)
                .force(mcxt.size, db, &mcxt);
            let n_end = Instant::now();
            let name = predef
                .name()
                .map(|x| db.lookup_intern_name(x))
                .unwrap_or("<unnamed>".into());
            println!("Normalize time for {}: {:?}", name, n_end - n_start);
        }
    }

    ret
}

/// Elaborates and evaluates the argument types, adding the arguments to the context and storing them in `rargs`.
/// Any type errors will be reported to the database.
fn elab_args(
    args: &[(Name, Icit, Pre)],
    rargs: &mut Vec<(Name, Icit, VTy)>,
    file: FileId,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) {
    for (name, icit, ty) in args {
        let ty = match check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt) {
            Ok(x) => x,
            Err(e) => {
                db.report_error(e.to_error(file, db, mcxt));
                Term::Error
            }
        };
        let vty = ty.evaluate(&mcxt.env(), mcxt, db);
        rargs.push((*name, *icit, vty.clone()));
        mcxt.define(*name, NameInfo::Local(vty), db);
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ScopeType {
    Type(Name),
    Struct,
}

/// The reason we expected a value to have a given type, used in "could not match types" errors
#[derive(Clone, PartialEq, Debug)]
pub enum ReasonExpected {
    UsedAsType,
    IfCond,
    MustMatch(Span),
    Given(Span),
    ArgOf(Span, VTy),
}
impl ReasonExpected {
    /// Adds a description of the reason to the `err`.
    /// This function adds it to an existing error instead of returning a Doc because some reasons have spans attached, and some don't.
    fn add(self, err: Error, file: FileId, db: &dyn Compiler, mcxt: &MCxt) -> Error {
        match self {
            ReasonExpected::UsedAsType => err
                .with_note(Doc::start("expected because it was used as a type").style(Style::Note)),
            ReasonExpected::IfCond => err.with_note(
                Doc::start("expected because if conditions must have type Bool").style(Style::Note),
            ),
            ReasonExpected::MustMatch(span) => err.with_label(
                file,
                span,
                "expected because it must match the type of this",
            ),
            ReasonExpected::Given(span) => {
                err.with_label(file, span, "expected because it was given here")
            }
            ReasonExpected::ArgOf(span, ty) => err.with_label(
                file,
                span,
                Doc::start("expected because it was passed to this, of type ")
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .style(Style::Note),
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    NotFound(Spanned<Name>),
    NotFunction(MCxt, Spanned<VTy>),
    Unify(MCxt, Spanned<VTy>, VTy, ReasonExpected),
    NotIntType(Span, VTy, ReasonExpected),
    UntypedLiteral(Span),
    MetaScope(Span, Var<Lvl>, Name),
    MetaOccurs(Span, Var<Lvl>),
    NotStruct(Spanned<VTy>),
    MemberNotFound(Span, ScopeType, Name),
    InvalidPattern(Span),
    WrongNumConsArgs(Span, usize, usize),
    Inexhaustive(Span, crate::pattern::Cov, VTy),
    InvalidPatternBecause(Box<TypeError>),
    WrongArity(Spanned<VTy>, usize, usize),
}
impl TypeError {
    fn to_error(self, file: FileId, db: &dyn Compiler, mcxt: &MCxt) -> Error {
        match self {
            TypeError::NotFound(n) => Error::new(
                file,
                format!("Name not found in scope: '{}'", n.get(db)),
                n.span(),
                "not found",
            ),
            TypeError::NotFunction(mcxt, t) => Error::new(
                file,
                Doc::start("Expected function type in application, but got: ")
                    .chain(t.pretty(db, &mcxt).style(Style::None))
                    .style(Style::Bold),
                t.span(),
                "not a function",
            ),
            TypeError::Unify(mcxt, a, b, r) => r.add(
                Error::new(
                    file,
                    Doc::start("Could not match types, expected ")
                        .chain(b.pretty(db, &mcxt).style(Style::None))
                        .add(", got ")
                        .chain(a.pretty(db, &mcxt).style(Style::None))
                        .style(Style::Bold),
                    a.span(),
                    Doc::start("expected ")
                        .chain(b.pretty(db, &mcxt).style(Style::None))
                        .add(" here")
                        .style(Style::Error),
                ),
                file,
                db,
                &mcxt,
            ),
            // TODO do these two ever occur?
            TypeError::MetaScope(s, m, n) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt, db))
                    .add(" requires variable ")
                    .add(n.get(db))
                    .add(", which is not in its scope")
                    .style(Style::Bold),
                s,
                format!("solution found here"),
            ),
            TypeError::MetaOccurs(s, m) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt, db))
                    .add(" would be recursive")
                    .style(Style::Bold),
                s,
                format!("solution found here"),
            ),
            TypeError::NotStruct(ty) => Error::new(
                file,
                Doc::start("Value of type ")
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .add(" does not have members")
                    .style(Style::Bold),
                ty.span(),
                format!("tried to access member here"),
            ),
            TypeError::MemberNotFound(span, sctype, m) => Error::new(
                file,
                Doc::start("Could not find member ")
                    .add(db.lookup_intern_name(m))
                    .add(" in ")
                    .add(match sctype {
                        ScopeType::Type(name) => {
                            format!("namespace of type {}", db.lookup_intern_name(name))
                        }
                        ScopeType::Struct => format!("struct"),
                    })
                    .style(Style::Bold),
                span,
                format!("not found: {}", db.lookup_intern_name(m)),
            ),
            TypeError::InvalidPattern(span) => Error::new(
                file,
                Doc::start("Invalid pattern: expected '_', variable, literal, or constructor")
                    .style(Style::Bold),
                span,
                format!("invalid pattern"),
            ),
            TypeError::WrongNumConsArgs(span, expected, got) => Error::new(
                file,
                Doc::start("Expected ")
                    .add(expected)
                    .add(" arguments to constructor in pattern, got ")
                    .add(got)
                    .style(Style::Bold),
                span,
                format!("expected {} arguments", expected),
            ),
            TypeError::Inexhaustive(span, cov, ty) => Error::new(
                file,
                Doc::start("Inexhaustive match: patterns ")
                    .chain(cov.pretty_rest(&ty, db, mcxt).style(Style::None))
                    .add(" not covered")
                    .style(Style::Bold),
                span,
                Doc::start("this has type ")
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .style(Style::Error),
            ),
            TypeError::InvalidPatternBecause(e) => {
                let mut e = e.to_error(file, db, mcxt);
                let message = format!("Invalid pattern: {}", e.message());
                *e.message() = message;
                e
            }
            TypeError::NotIntType(span, ty, r) => r.add(
                Error::new(
                    file,
                    Doc::start("Expected value of type ")
                        .chain(ty.pretty(db, mcxt).style(Style::None))
                        .add(", got integer")
                        .style(Style::Bold),
                    span,
                    format!("this is an integer"),
                ),
                file,
                db,
                mcxt,
            ),
            TypeError::UntypedLiteral(span) => Error::new(
                file,
                Doc::start("Could not infer type of ambiguous literal").style(Style::Bold),
                span,
                Doc::start("try adding a type, like ")
                    .chain(Doc::start("I32").style(Style::None))
                    .add(" or ")
                    .chain(Doc::start("I64").style(Style::None))
                    .style(Style::Error),
            ),
            TypeError::WrongArity(ty, expected, got) => Error::new(
                file,
                Doc::start(if got > expected {
                    "Too many arguments "
                } else {
                    "Too few arguments "
                })
                .add(got)
                .add(" to value of type ")
                .chain(ty.pretty(db, mcxt).style(Style::None))
                .add(" which expects ")
                .add(expected)
                .add(if expected == 1 {
                    " argument"
                } else {
                    " arguments"
                })
                .style(Style::Bold),
                ty.span(),
                format!(
                    "expected {} {} here, got {}",
                    expected,
                    if expected == 1 {
                        "argument"
                    } else {
                        "arguments"
                    },
                    got
                ),
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct UnifyMode {
    inline: bool,
    local: bool,
}
impl UnifyMode {
    fn new(local: bool, inline: bool) -> UnifyMode {
        UnifyMode { inline, local }
    }
}

fn p_unify(
    mode: UnifyMode,
    a: Val,
    b: Val,
    l: Lvl,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<TBool, TypeError> {
    match (a, b) {
        (Val::Arc(a), b) | (b, Val::Arc(a)) => {
            let a = a.into_owned();
            p_unify(mode, a, b, l, span, db, mcxt)
        }

        (Val::Error, _) | (_, Val::Error) => Ok(Yes),
        (Val::Type, Val::Type) => Ok(Yes),

        (Val::App(h, _, v, _), Val::App(h2, _, v2, _)) if h.unify(h2, db) => {
            let mut r = Yes;
            for ((i, a), (i2, b)) in v.into_iter().zip(v2.into_iter()) {
                assert_eq!(i, i2);
                r = r & p_unify(mode, a, b, l, span, db, mcxt)?;
            }
            Ok(r)
        }

        // Since our terms are locally nameless (we're using De Bruijn levels), we automatically get alpha equivalence.
        (Val::Lam(_, cl), Val::Lam(_, cl2)) => p_unify(
            mode,
            cl.vquote(l, mcxt, db),
            cl2.vquote(l, mcxt, db),
            l.inc(),
            span,
            db,
            mcxt,
        ),

        // If one side is a lambda, the other side just needs to unify to the same thing when we apply it to the same thing
        (Val::Lam(icit, cl), t) | (t, Val::Lam(icit, cl)) => {
            let ty = cl.ty.clone();
            p_unify(
                mode,
                cl.vquote(l, mcxt, db),
                t.app(icit, Val::local(l, ty), mcxt, db),
                l.inc(),
                span,
                db,
                mcxt,
            )
        }

        (Val::Pi(i, cl), Val::Pi(i2, cl2)) if i == i2 => {
            Ok(
                p_unify(mode, cl.ty.clone(), cl2.ty.clone(), l, span, db, mcxt)?
                // Applying both to the same thing (Local(l))
                & p_unify(
                    mode,
                    cl.vquote(l, mcxt, db),
                    cl2.vquote(l, mcxt, db),
                    l.inc(),
                    span,
                    db,
                    mcxt,
                )?,
            )
        }
        (Val::Pi(Icit::Expl, cl), Val::Fun(from, to))
        | (Val::Fun(from, to), Val::Pi(Icit::Expl, cl)) => {
            Ok(p_unify(mode, cl.ty.clone(), *from, l, span, db, mcxt)?
                & p_unify(mode, cl.vquote(l, mcxt, db), *to, l.inc(), span, db, mcxt)?)
        }
        (Val::Fun(a, b), Val::Fun(a2, b2)) => {
            Ok(p_unify(mode, *a, *a2, l, span, db, mcxt)?
                & p_unify(mode, *b, *b2, l, span, db, mcxt)?)
        }

        // Solve metas

        // Make sure order doesn't matter - switch sides if the second one is higher
        (Val::App(Var::Meta(m), mty, s, g), Val::App(Var::Meta(m2), mty2, s2, g2)) if m2 > m => {
            p_unify(
                mode,
                Val::App(Var::Meta(m2), mty2, s2, g2),
                Val::App(Var::Meta(m), mty, s, g),
                l,
                span,
                db,
                mcxt,
            )
        }

        (Val::App(Var::Meta(m), _, sp, _), t) | (t, Val::App(Var::Meta(m), _, sp, _)) => {
            match mcxt.get_meta(m) {
                Some(v) => {
                    let v = sp.into_iter().fold(v, |f, (i, x)| f.app(i, x, mcxt, db));
                    p_unify(mode, v, t, l, span, db, mcxt)
                }
                None => {
                    mcxt.solve(span, m, &sp, t, db)?;
                    Ok(Yes)
                }
            }
        }

        // Solve local constraints
        // We prioritize solving the innermost local - so the one with the highest level
        (Val::App(Var::Local(m), mty, s, g), Val::App(Var::Local(m2), mty2, s2, g2))
            if mode.local && m2 > m =>
        {
            p_unify(
                mode,
                Val::App(Var::Local(m2), mty2, s2, g2),
                Val::App(Var::Local(m), mty, s, g),
                l,
                span,
                db,
                mcxt,
            )
        }
        // is_none() because if it's already solved, we'll do that with the normal inlining logic down below
        (Val::App(Var::Local(l), _, sp, _), t) | (t, Val::App(Var::Local(l), _, sp, _))
            if mode.local && mcxt.local_val(l).is_none() =>
        {
            mcxt.solve_local(l, &sp, t)?;
            Ok(Yes)
        }

        // If the reason we can't unify is that one side is a top variable, then we can try again after inlining.
        (Val::App(Var::Top(_), _, _, _), _) | (_, Val::App(Var::Top(_), _, _, _))
            if !mode.inline =>
        {
            Ok(Maybe)
        }

        (Val::App(h, hty, sp, g), Val::App(h2, hty2, sp2, g2)) if mode.inline => {
            if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                p_unify(mode, Val::App(h2, hty2, sp2, g2), v, l, span, db, mcxt)
            } else if let Some(v) = g2.resolve(h2, sp2, l, db, mcxt) {
                p_unify(mode, Val::App(h, hty, sp, g), v, l, span, db, mcxt)
            } else {
                Ok(No)
            }
        }

        (Val::App(h, _, sp, g), x) | (x, Val::App(h, _, sp, g)) if mode.inline => {
            if let Some(v) = g.resolve(h, sp, l, db, mcxt) {
                p_unify(mode, x, v, l, span, db, mcxt)
            } else {
                Ok(No)
            }
        }

        // If that's not the reason, then we know inlining won't help.
        _ => Ok(No),
    }
}

/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn unify(
    a: Val,
    b: Val,
    l: Lvl,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<bool, TypeError> {
    match p_unify(
        UnifyMode::new(false, false),
        a.clone(),
        b.clone(),
        l,
        span,
        db,
        mcxt,
    )? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(UnifyMode::new(false, true), a, b, l, span, db, mcxt)?.not_maybe()),
    }
}

/// Like `unify()`, but finds local constraints and adds them to the context.
///
/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn local_unify(
    a: Val,
    b: Val,
    l: Lvl,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<bool, TypeError> {
    match p_unify(
        UnifyMode::new(true, false),
        a.clone(),
        b.clone(),
        l,
        span,
        db,
        mcxt,
    )? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(UnifyMode::new(true, true), a, b, l, span, db, mcxt)?.not_maybe()),
    }
}

/// If `term` of type `ty` takes implicit parameters, insert metas to apply them.
fn insert_metas(
    insert: bool,
    term: Term,
    ty: VTy,
    span: Span,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> (Term, VTy) {
    match ty {
        Val::Pi(Icit::Impl, cl) if insert => {
            let meta = mcxt.new_meta(
                None,
                span,
                MetaSource::ImplicitParam(cl.name),
                cl.ty.clone().quote(mcxt.size, mcxt, db),
                db,
            );
            let vmeta = meta.clone().evaluate(&mcxt.env(), mcxt, db);
            let ret = (*cl).clone().apply(vmeta, mcxt, db);
            insert_metas(
                insert,
                Term::App(
                    Icit::Impl,
                    Box::new(term),
                    Box::new(Val::Pi(Icit::Impl, cl).quote(mcxt.size, mcxt, db)),
                    Box::new(meta),
                ),
                ret,
                span,
                mcxt,
                db,
            )
        }
        Val::App(h, hty, sp, g) if insert => match g.resolve(h, &sp, mcxt.size, db, mcxt) {
            Some(ty) => insert_metas(insert, term, ty, span, mcxt, db),
            None => (term, Val::App(h, hty, sp, g)),
        },
        Val::Arc(x) if insert => {
            let x = x.into_owned();
            insert_metas(insert, term, x, span, mcxt, db)
        }
        ty => (term, ty),
    }
}

pub fn infer(
    insert: bool,
    pre: &Pre,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<(Term, VTy), TypeError> {
    match &**pre {
        Pre_::Type => Ok((Term::Type, Val::Type)),

        Pre_::Lit(_) => Err(TypeError::UntypedLiteral(pre.span())),

        Pre_::BinOp(op, a, b) => {
            let f = Term::Var(
                Var::Builtin(Builtin::BinOp(**op)),
                Box::new(op.ty().quote(mcxt.size, mcxt, db)),
            );
            let (f, fty) = infer_app(f, op.ty(), op.span(), Icit::Expl, a, db, mcxt)?;
            let fspan = Span(a.span().0, op.span().1);
            infer_app(f, fty, fspan, Icit::Expl, b, db, mcxt)
        }

        Pre_::If(cond, yes, no) => {
            let cond = check(
                cond,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::IfCond,
                db,
                mcxt,
            )?;
            let yspan = yes.span();
            let (yes, ty) = infer(insert, yes, db, mcxt)?;
            let no = check(no, &ty, ReasonExpected::MustMatch(yspan), db, mcxt)?;
            Ok((Term::If(Box::new(cond), Box::new(yes), Box::new(no)), ty))
        }

        Pre_::Var(name) => {
            let (term, ty) = match mcxt.lookup(*name, db) {
                Ok((v, ty)) => Ok((
                    Term::Var(v, Box::new(ty.clone().quote(mcxt.size, mcxt, db))),
                    ty,
                )),
                // If something else had a type error, try to keep going anyway and maybe catch more
                Err(DefError::ElabError(def)) => Ok((
                    Term::Error,
                    // TODO pros/cons of using a meta here?
                    Val::Error, //Val::meta(Meta::Type(db.lookup_intern_def(def).0), Val::Type),
                )),
                Err(DefError::NoValue) => Err(TypeError::NotFound(pre.copy_span(*name))),
            }?;
            Ok(insert_metas(insert, term, ty, pre.span(), mcxt, db))
        }

        Pre_::Lam(name, icit, ty, body) => {
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt, db);
            // TODO Rc to get rid of the clone()?
            mcxt.define(*name, NameInfo::Local(vty.clone()), db);
            let (body, bty) = infer(true, body, db, mcxt)?;
            mcxt.undef(db);
            // TODO do we insert metas here?
            Ok((
                Term::Lam(*name, *icit, Box::new(ty), Box::new(body)),
                Val::Pi(
                    *icit,
                    // `inc()` since we're wrapping it in a lambda
                    Box::new(Clos {
                        env: mcxt.env(),
                        ty: vty,
                        term: bty.quote(mcxt.size.inc(), mcxt, db),
                        name: *name,
                    }),
                ),
            ))
        }

        Pre_::Pi(name, icit, ty, ret) => {
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            // TODO Rc to get rid of the clone()?
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt, db);
            mcxt.define(*name, NameInfo::Local(vty), db);
            let ret = check(ret, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            mcxt.undef(db);
            Ok((
                Term::Pi(*name, *icit, Box::new(ty), Box::new(ret)),
                Val::Type,
            ))
        }

        Pre_::Fun(from, to) => {
            let from = check(from, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let to = check(to, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            Ok((Term::Fun(Box::new(from), Box::new(to)), Val::Type))
        }

        Pre_::App(icit, f, x) => {
            let fspan = f.span();
            // Don't insert metas in `f` if we're passing an implicit argument
            let (f, fty) = infer(*icit == Icit::Expl, f, db, mcxt)?;

            infer_app(f, fty, fspan, *icit, x, db, mcxt)
                .map(|(term, ty)| insert_metas(insert, term, ty, pre.span(), mcxt, db))
        }

        Pre_::Do(v) => {
            // We store the whole block in Salsa, then query the last expression
            let mut block = crate::query::intern_block(v.clone(), db, mcxt.cxt);
            // Make sure any type errors get reported
            for &i in &block {
                let _ = db.elaborate_def(i);
            }
            // Now query the last expression again
            if let Some(&last) = block.last() {
                let (pre, _) = db.lookup_intern_def(last);
                // If it's not an expression, don't return anything
                if let PreDef::Expr(_) = &**db.lookup_intern_predef(pre) {
                    if let Ok(info) = db.elaborate_def(last) {
                        block.pop();
                        mcxt.children.append(&mut block);
                        return Ok(((*info.term).clone(), Val::Arc(info.typ)));
                    } else {
                        // If there was a type error inside the block, we'll leave it, we don't want a cascade of errors
                        return Ok((Term::Error, Val::Error));
                    }
                }
            }
            mcxt.children.append(&mut block);
            todo!("return ()")
        }

        Pre_::Struct(_) => todo!("elaborate struct"),

        Pre_::Hole(source) => {
            let ty = mcxt.new_meta(None, pre.span(), MetaSource::HoleType, Term::Type, db);
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt, db);
            Ok((mcxt.new_meta(None, pre.span(), *source, ty, db), vty))
        }

        Pre_::Dot(head, m, args) => {
            match infer(true, head, db, mcxt).map(|(x, ty)| {
                (
                    x.evaluate(&mcxt.env(), mcxt, db)
                        .inline(mcxt.size, db, mcxt),
                    ty,
                )
            })? {
                (_, Val::Error) => return Ok((Term::Error, Val::Error)),
                (Val::App(Var::Builtin(Builtin::Bool), _, _, _), _) => {
                    let tbool = Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type));
                    let vbool = Val::builtin(Builtin::Bool, Val::Type);
                    match &*db.lookup_intern_name(**m) {
                        "True" => Ok((
                            Term::Var(Var::Builtin(Builtin::True), Box::new(tbool)),
                            vbool,
                        )),
                        "False" => Ok((
                            Term::Var(Var::Builtin(Builtin::False), Box::new(tbool)),
                            vbool,
                        )),
                        _ => Err(TypeError::MemberNotFound(
                            Span(head.span().0, m.span().1),
                            ScopeType::Type(db.intern_name("Bool".into())),
                            **m,
                        )),
                    }
                }
                (Val::App(Var::Type(id, scope), _, sp, _), _) if sp.is_empty() => {
                    let scope = db.lookup_intern_scope(scope);
                    for &(n, v) in scope.iter().rev() {
                        if n == **m {
                            match db.elaborate_def(v) {
                                Ok(info) => {
                                    let fty: Val = info.typ.into_owned();
                                    let f = Term::Var(
                                        Var::Top(v),
                                        Box::new(fty.clone().quote(mcxt.size, mcxt, db)),
                                    );
                                    return args
                                        .iter()
                                        .try_fold(
                                            (f, fty, Span(head.span().0, m.span().1)),
                                            |(f, fty, fspan), (i, x)| {
                                                let (f, fty) = insert_metas(
                                                    *i == Icit::Expl,
                                                    f,
                                                    fty,
                                                    fspan,
                                                    mcxt,
                                                    db,
                                                );
                                                let (f, fty) =
                                                    infer_app(f, fty, fspan, *i, x, db, mcxt)?;
                                                Ok((f, fty, Span(fspan.0, x.span().1)))
                                            },
                                        )
                                        .map(|(f, fty, fspan)| {
                                            insert_metas(insert, f, fty, fspan, mcxt, db)
                                        });
                                }
                                Err(_) => return Ok((Term::Error, Val::Error)),
                            }
                        }
                    }
                    Err(TypeError::MemberNotFound(
                        Span(head.span().0, m.span().1),
                        ScopeType::Type(
                            db.lookup_intern_predef(db.lookup_intern_def(id).0)
                                .name()
                                .unwrap(),
                        ),
                        **m,
                    ))
                }
                (_, ty) => Err(TypeError::NotStruct(Spanned::new(
                    ty,
                    Span(head.span().0, m.span().1),
                ))),
            }
        }

        Pre_::Case(x, cases) => {
            let xspan = x.span();
            let (x, x_ty) = infer(true, x, db, mcxt)?;
            crate::pattern::elab_case(
                x,
                xspan,
                x_ty,
                ReasonExpected::MustMatch(xspan),
                cases,
                None,
                mcxt,
                db,
            )
        }

        Pre_::OrPat(_, _) => unreachable!("| is only allowed in patterns"),
    }
}

/// Handles common logic of checking an argument to an application.
/// Doesn't insert metas, so do that after if applicable.
fn infer_app(
    f: Term,
    fty: VTy,
    fspan: Span,
    icit: Icit,
    x: &Pre,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<(Term, VTy), TypeError> {
    let (term, ty) = match &fty {
        Val::Pi(icit2, cl) => {
            assert_eq!(icit, *icit2);

            let x = check(
                x,
                &cl.ty,
                ReasonExpected::ArgOf(fspan, fty.clone()),
                db,
                mcxt,
            )?;
            // TODO Rc to get rid of the clone()?
            let to = (**cl)
                .clone()
                .apply(x.clone().evaluate(&mcxt.env(), mcxt, db), mcxt, db);
            Ok((
                Term::App(
                    icit,
                    Box::new(f),
                    Box::new(fty.quote(mcxt.size, mcxt, db)),
                    Box::new(x),
                ),
                to,
            ))
        }
        Val::Fun(from, to) => {
            let x = check(
                x,
                &from,
                ReasonExpected::ArgOf(fspan, fty.clone()),
                db,
                mcxt,
            )?;
            let to = (**to).clone();
            Ok((
                Term::App(
                    icit,
                    Box::new(f),
                    Box::new(fty.quote(mcxt.size, mcxt, db)),
                    Box::new(x),
                ),
                to,
            ))
        }
        // The type was already Error, so we'll leave it there, not introduce a meta
        Val::Error => Ok((Term::Error, Val::Error)),
        _ => {
            if let Term::App(_, _, hty, _) = &f {
                let hty = f.head_ty(hty).clone().evaluate(&mcxt.env(), mcxt, db);
                let exp = hty.arity(false);
                return Err(TypeError::WrongArity(
                    Spanned::new(hty, Span(fspan.0, x.span().1)),
                    exp,
                    f.spine_len() + 1,
                ));
            }
            return Err(TypeError::NotFunction(
                mcxt.clone(),
                Spanned::new(fty, fspan),
            ));
        }
    }?;
    Ok((term, ty))
}

pub fn check(
    pre: &Pre,
    ty: &VTy,
    reason: ReasonExpected,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<Term, TypeError> {
    match (&**pre, ty) {
        (_, Val::Arc(x)) => check(pre, x, reason, db, mcxt),

        (Pre_::Lam(n, i, ty, body), Val::Pi(i2, cl)) if i == i2 => {
            let ty2 = &cl.ty;
            let ety = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let vty = ety.clone().evaluate(&mcxt.env(), mcxt, db);
            if !unify(vty.clone(), ty2.clone(), mcxt.size, pre.span(), db, mcxt)? {
                return Err(TypeError::Unify(
                    mcxt.clone(),
                    ty.copy_span(vty),
                    ty2.clone(),
                    reason,
                ));
            }
            mcxt.define(*n, NameInfo::Local(vty.clone()), db);
            let body = check(
                body,
                // TODO not clone ??
                &(**cl).clone().apply(Val::local(mcxt.size, vty), mcxt, db),
                reason,
                db,
                mcxt,
            )?;
            mcxt.undef(db);
            Ok(Term::Lam(*n, *i, Box::new(ety), Box::new(body)))
        }

        (Pre_::Lam(n, Icit::Expl, ty, body), Val::Fun(ty2, body_ty)) => {
            let ety = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let vty = ety.clone().evaluate(&mcxt.env(), mcxt, db);
            if !unify(
                vty.clone(),
                (**ty2).clone(),
                mcxt.size,
                pre.span(),
                db,
                mcxt,
            )? {
                return Err(TypeError::Unify(
                    mcxt.clone(),
                    ty.copy_span(vty),
                    (**ty2).clone(),
                    reason,
                ));
            }
            mcxt.define(*n, NameInfo::Local(vty), db);
            let body = check(body, &*body_ty, reason, db, mcxt)?;
            mcxt.undef(db);
            Ok(Term::Lam(*n, Icit::Expl, Box::new(ety), Box::new(body)))
        }

        // We implicitly insert lambdas so `\x.x : [a] -> a -> a` typechecks
        (_, Val::Pi(Icit::Impl, cl)) => {
            // Add a ' after the name so it doesn't shadow names the term defined (' isn't valid in Pika identifiers)
            let name = {
                let mut s = cl.name.get(db);
                s.push('\'');
                db.intern_name(s)
            };
            mcxt.define(name, NameInfo::Local(cl.ty.clone()), db);
            let body = check(
                pre,
                &(**cl).clone().vquote(mcxt.size, mcxt, db),
                reason,
                db,
                mcxt,
            )?;
            mcxt.undef(db);
            let ty = cl.ty.clone().quote(mcxt.size, mcxt, db);
            Ok(Term::Lam(cl.name, Icit::Impl, Box::new(ty), Box::new(body)))
        }

        (Pre_::Lit(l), _) => match ty.unarc() {
            Val::App(Var::Builtin(b), _, _, _) if matches!(b, Builtin::I32 | Builtin::I64) => {
                Ok(Term::Lit(*l, *b))
            }
            Val::App(Var::Meta(_), _, _, _) => Err(TypeError::UntypedLiteral(pre.span())),
            _ => Err(TypeError::NotIntType(
                pre.span(),
                ty.clone().inline_metas(mcxt, db),
                reason,
            )),
        },

        (Pre_::Case(value, cases), _) => {
            let vspan = value.span();
            let (value, val_ty) = infer(true, value, db, mcxt)?;
            crate::pattern::elab_case(
                value,
                vspan,
                val_ty,
                ReasonExpected::MustMatch(vspan),
                cases,
                Some((ty.clone(), reason.clone())),
                mcxt,
                db,
            )
            .map(|(x, _)| x)
        }

        (Pre_::If(cond, yes, no), _) => {
            let cond = check(
                cond,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::IfCond,
                db,
                mcxt,
            )?;
            let yes = check(yes, &ty, reason.clone(), db, mcxt)?;
            let no = check(no, &ty, reason, db, mcxt)?;
            Ok(Term::If(Box::new(cond), Box::new(yes), Box::new(no)))
        }

        _ => {
            if let Val::App(h, _, sp, g) = ty {
                if let Some(v) = g.resolve(*h, sp, mcxt.size, db, mcxt) {
                    return check(pre, &v, reason, db, mcxt);
                }
            }

            let (term, i_ty) = infer(true, pre, db, mcxt)?;
            // TODO should we take `ty` by value?
            if !unify(ty.clone(), i_ty.clone(), mcxt.size, pre.span(), db, mcxt)? {
                // Use an arity error if we got a function type but don't expect one
                match (&ty, &i_ty) {
                    (Val::Pi(_, _), _) | (Val::Fun(_, _), _) => (),
                    (_, Val::Fun(_, _)) | (_, Val::Pi(_, _))
                        if matches!(term, Term::App(_, _, _, _)) =>
                    {
                        let got = term.spine_len();
                        let hty = match term.evaluate(&mcxt.env(), mcxt, db) {
                            Val::App(_, hty, _, _) => *hty,
                            _ => i_ty,
                        };
                        let exp = hty.arity(false);
                        return Err(TypeError::WrongArity(pre.copy_span(hty), exp, got));
                    }
                    _ => (),
                }
                return Err(TypeError::Unify(
                    mcxt.clone(),
                    pre.copy_span(i_ty.inline_metas(mcxt, db)),
                    ty.clone().inline_metas(mcxt, db),
                    reason,
                ));
            }
            Ok(term)
        }
    }
}
