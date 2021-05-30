use crate::common::*;
use crate::term::*;
use std::sync::Arc;
use std::time::Instant;

#[derive(Debug, Clone, PartialEq)]
pub enum MetaEntry {
    Solved(Arc<Term>, Span),
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
        lfrom: Size,
        // The level this term will be enclosed in after check_solution()
        lto: Size,
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
                    Var::Local(ix) => match ren.get(&lfrom.to_lvl_(ix)) {
                        Some(lvl) => Ok(Term::Var(Var::Local(lto.to_ix(*lvl)), ty)),
                        None => {
                            eprintln!("wrong {:?} = {:?}", ix, lfrom.to_lvl_(ix));
                            Err(TypeError::MetaScope(meta.span(), *meta, names.get(ix)))
                        }
                    },
                    // The type of something can't depend on its own value
                    // TODO a different error for this case? Is this even possible?
                    Var::Rec(id) if matches!(*meta, Var::Meta(Meta::Global(id2, _)) if id2 == id) =>
                    {
                        eprintln!("type depends on value: {:?}", meta);
                        Err(TypeError::MetaOccurs(meta.span(), *meta))
                    }
                    v => Ok(Term::Var(v, ty)),
                }
            }
            Term::Clos(t, n, i, mut a, mut b, effs) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                // Allow the body to use the bound variable
                ren.insert(lfrom.next_lvl(), lto.next_lvl());
                names.add(n);
                *b = b.check_solution(meta.clone(), ren, lfrom.inc(), lto.inc(), names)?;
                names.remove();
                ren.remove(&lfrom.next_lvl());
                effs.into_iter()
                    .map(|x| x.check_solution(meta.clone(), ren, lfrom, lto, names))
                    .collect::<Result<_, _>>()
                    .map(|v| Term::Clos(t, n, i, a, b, v))
            }
            Term::Fun(mut a, mut b, effs) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *b = b.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                effs.into_iter()
                    .map(|x| x.check_solution(meta.clone(), ren, lfrom, lto, names))
                    .collect::<Result<_, _>>()
                    .map(|v| Term::Fun(a, b, v))
            }
            Term::App(i, mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *b = b.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::App(i, a, b))
            }
            Term::Type => Ok(Term::Type),
            Term::Lit(x, t) => Ok(Term::Lit(x, t)),
            Term::Case(mut x, mut ty, cases, effs, mut rty) => {
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
                *ty = ty.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *rty = rty.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                effs.into_iter()
                    .map(|x| x.check_solution(meta.clone(), ren, lfrom, lto, names))
                    .collect::<Result<_, _>>()
                    .map(|v| Term::Case(x, ty, cases, v, rty))
            }
            Term::Do(v) => v
                .into_iter()
                .map(|(id, term)| {
                    term.check_solution(meta.clone(), ren, lfrom, lto, names)
                        .map(|term| (id, term))
                })
                .collect::<Result<_, _>>()
                .map(Term::Do),
            Term::Struct(k, v) => Ok(Term::Struct(
                match k {
                    StructKind::Struct(t) => StructKind::Struct(Box::new(t.check_solution(
                        meta.clone(),
                        ren,
                        lfrom,
                        lto,
                        names,
                    )?)),
                    StructKind::Sig => StructKind::Sig,
                },
                v.into_iter()
                    .map(|(n, t)| {
                        t.check_solution(meta.clone(), ren, lfrom, lto, names)
                            .map(|t| (n, t))
                    })
                    .collect::<Result<_, _>>()?,
            )),
            Term::Dot(mut x, m) => {
                *x = x.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::Dot(x, m))
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
    pub size: Size,
    pub local_constraints: HashMap<Lvl, Val>,
    pub eff_stack: EffStack,
    pub is_sig: bool,
}
/// Implemented manually only because HashMap doesn't implement Hash.
/// It should be the same as a hypothetical derived implementation.
#[allow(clippy::derive_hash_xor_eq)]
impl std::hash::Hash for CxtState {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.cxt.hash(state);
        self.size.hash(state);
        for (k, v) in &self.local_constraints {
            k.hash(state);
            v.hash(state);
        }
        self.eff_stack.hash(state);
    }
}
impl CxtState {
    pub fn new(cxt: Cxt, db: &dyn Compiler) -> Self {
        CxtState {
            cxt,
            size: cxt.size(db),
            local_constraints: Default::default(),
            eff_stack: Default::default(),
            is_sig: false,
        }
    }

    /// Adds a definition to the context, and handles increasing the cached size.
    pub fn define(&mut self, name: Name, info: NameInfo, db: &dyn Compiler) {
        if let NameInfo::Local(_) = &info {
            self.size = self.size.inc();
        }
        self.cxt = self.cxt.define(name, info, db);
        debug_assert_eq!(self.size, self.cxt.size(db));
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MCxtType {
    Local(DefId),
    Global(PreDefId),
}

#[derive(Debug, Clone, PartialEq, Default, Eq, Hash)]
pub struct EffStack {
    effs: Vec<Val>,
    scopes: Vec<(bool, usize, Span)>,
}
impl EffStack {
    pub fn is_empty(&self) -> bool {
        self.effs.is_empty()
    }
    pub fn len(&self) -> usize {
        self.effs.len()
    }
    pub fn push_eff(&mut self, eff: Val) {
        self.effs.push(eff);
    }
    pub fn pop_eff(&mut self) -> Option<Val> {
        self.effs.pop()
    }
    /// `open` is whether this scope is open to new effects - i.e., we're inferring the type instead of checking it
    pub fn push_scope(&mut self, open: bool, span: Span) {
        self.scopes.push((open, self.effs.len(), span))
    }
    pub fn pop_scope(&mut self) -> Vec<Val> {
        if let Some((_, len, _)) = self.scopes.pop() {
            self.effs.split_off(len)
        } else {
            panic!("pop_scope() without push_scope()")
        }
    }
    pub fn find_eff(&self, eff: &Val, db: &dyn Compiler, mcxt: &mut MCxt) -> Option<usize> {
        let mut mcxt = mcxt.clone();
        let start = self.scopes.last().map_or(0, |(_, l, _)| *l);
        for (i, e) in self.effs[start..].iter().enumerate() {
            if unify(
                eff.clone(),
                e.clone(),
                mcxt.size,
                Span::empty(),
                db,
                &mut mcxt,
            )
            .unwrap_or(false)
            {
                return Some(i);
            }
        }
        None
    }

    pub fn scope_start(&self) -> Option<usize> {
        self.scopes.last().map(|(_, len, _)| *len)
    }

    fn try_eff(&mut self, eff: Val, db: &dyn Compiler, mcxt: &mut MCxt) -> bool {
        if self.find_eff(&eff, db, mcxt).is_some() {
            return true;
        }
        if self.scopes.last().map_or(false, |(open, _, _)| *open) {
            self.push_eff(eff);
            return true;
        }
        false
    }
}

/// The context used for typechecking a term.
/// Besides storing a `Cxt` for name resolution, stores meta solutions and local constraints.
/// Most operations also require a database to interact with the `Cxt`.
#[derive(Debug, Clone, PartialEq)]
pub struct MCxt {
    pub cxt: Cxt,
    pub size: Size,
    pub eff_stack: EffStack,
    is_sig: bool,
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
            eff_stack: self.eff_stack.clone(),
            is_sig: false,
        }
    }
    pub fn set_state(&mut self, state: CxtState) {
        let CxtState {
            cxt,
            size,
            local_constraints,
            eff_stack,
            is_sig,
        } = state;
        self.cxt = cxt;
        self.size = size;
        self.local_constraints = local_constraints;
        self.eff_stack = eff_stack;
        self.is_sig = is_sig;
    }

    pub fn new(cxt: Cxt, ty: MCxtType, db: &dyn Compiler) -> Self {
        MCxt {
            cxt,
            size: cxt.size(db),
            eff_stack: Default::default(),
            ty,
            local_metas: Vec::new(),
            local_constraints: HashMap::new(),
            solved_globals: Vec::new(),
            children: Vec::new(),
            is_sig: false,
        }
    }

    pub fn from_state(state: CxtState, ty: MCxtType) -> Self {
        let CxtState {
            cxt,
            size,
            local_constraints,
            eff_stack,
            is_sig,
        } = state;
        MCxt {
            cxt,
            size,
            eff_stack,
            ty,
            local_metas: Vec::new(),
            local_constraints,
            solved_globals: Vec::new(),
            children: Vec::new(),
            is_sig,
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

    pub fn last_local(&self, db: &dyn Compiler) -> Option<(Var<Lvl>, VTy)> {
        let mut cxt = self.cxt;
        loop {
            match db.lookup_cxt_entry(cxt) {
                MaybeEntry::Yes(CxtEntry { rest, info, .. }) => {
                    cxt = rest;
                    match info {
                        NameInfo::Local(ty) => {
                            break Some((Var::Local(self.size.dec().next_lvl()), ty));
                        }
                        _ => continue,
                    }
                }
                _ => unreachable!(),
            }
        }
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
    pub fn get_meta(&self, meta: Meta) -> Option<Term> {
        match meta {
            Meta::Global(id, n) => self
                .solved_globals
                .iter()
                .find(|s| s.id() == Some(id) && s.num() == n)
                .map(|s| s.term().clone()),
            Meta::Local(def, num) => {
                if let MCxtType::Local(d) = self.ty {
                    if def == d {
                        return match &self.local_metas[num as usize] {
                            MetaEntry::Solved(v, _) => Some((**v).clone()), //.map(|x| x.inline_metas(self)),
                            MetaEntry::Unsolved(_, _, _) => None,
                        };
                    }
                }
                self.solved_globals.iter().find_map(|s| match s {
                    RecSolution::ParentLocal(d, n, _, t) if *d == def && *n == num => {
                        Some(t.clone())
                    }
                    _ => None,
                })
            }
        }
    }

    /// Undoes the last call to `define()`.
    pub fn undef(&mut self, db: &dyn Compiler) {
        self.cxt = match db.lookup_cxt_entry(self.cxt) {
            MaybeEntry::Yes(CxtEntry { rest, info, .. }) => {
                if let NameInfo::Local(_) = &info {
                    self.size = self.size.dec();
                    // Remove local constraints that no longer apply
                    let next_lvl = self.size.next_lvl();
                    self.local_constraints.retain(|&k, _| k < next_lvl);
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
        let mut meta_scope = spine
            .iter()
            // Each argument is another lambda we're going to wrap it in
            .zip(std::iter::successors(Some(self.size.next_lvl()), |lvl| {
                Some(lvl.inc())
            }))
            .map(|(e, to_lvl)| match e.assert_app().1.unarc() {
                Val::App(Var::Local(from_lvl), _, sp, _) if sp.is_empty() => {
                    Ok((*from_lvl, to_lvl))
                }
                x => Err(TypeError::MetaSpine(span, Var::Meta(meta), x.clone())),
            })
            .collect::<Result<Rename, _>>()?;
        let term = val.quote(self.size, &self, db);
        // The level it will be at after we wrap it in lambdas
        let to_lvl = (0..spine.len()).fold(self.size, |x, _| x.inc());

        // Get the type of each argument
        let tys: Vec<Ty> = spine
            .iter()
            .zip(std::iter::successors(Some(self.size), |size| {
                Some(size.inc())
            }))
            .map(|(e, l)| match e.assert_app().1.unarc() {
                Val::App(Var::Local(_), ty, sp, _) if sp.is_empty() => {
                    let mut names = Names::new(self.cxt, db);
                    while names.size() != l {
                        // TODO actual names?
                        names.add(names.hole_name());
                    }
                    (**ty).clone().quote(l, self, db).check_solution(
                        Spanned::new(Var::Meta(meta), span),
                        &mut meta_scope,
                        l,
                        l,
                        &mut Names::new(self.cxt, db),
                    )
                }
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect::<Result<_, _>>()?;

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
        let term = tys.into_iter().rfold(term, |term, ty| {
            Term::Clos(
                Lam,
                empty_name,
                Icit::Expl,
                Box::new(ty),
                Box::new(term),
                Vec::new(),
            )
        });

        // Now add it to the solved metas
        match meta {
            Meta::Global(id, n) => {
                self.solved_globals
                    .push(RecSolution::Inferred(id, n, span, term));
            }
            Meta::Local(def, idx) => {
                if let MCxtType::Local(d) = self.ty {
                    if def == d {
                        // TODO should we do anything with the span we already have in `local_metas`, where it was introduced?
                        self.local_metas[idx as usize] = MetaEntry::Solved(Arc::new(term), span);
                        return Ok(());
                    }
                }
                self.solved_globals
                    .push(RecSolution::ParentLocal(def, idx, span, term));
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

    pub fn elab_block(
        &mut self,
        v: Vec<PreDefAn>,
        is_sig: bool,
        db: &dyn Compiler,
    ) -> Result<Vec<DefId>, TypeError> {
        let mut state = self.state();
        state.is_sig = is_sig;
        let block = crate::query::intern_block(v, db, state);
        // Make sure any type errors get reported
        {
            let mut mcxt2 = self.clone();
            for &i in &block {
                if let Ok(info) = db.elaborate_def(i) {
                    for e in &*info.effects {
                        assert!(self.eff_stack.try_eff(e.clone(), db, &mut mcxt2));
                    }
                    for i in &*info.solved_globals {
                        match i {
                            RecSolution::ParentLocal(d, n, span, term)
                                if self.ty == MCxtType::Local(*d) =>
                            {
                                match &self.local_metas[*n as usize] {
                                    MetaEntry::Solved(t2, s2) => {
                                        let t2 = (**t2).clone().evaluate(&self.env(), self, db);
                                        let term = term.clone().evaluate(&self.env(), self, db);
                                        if !unify(
                                            t2.clone(),
                                            term.clone(),
                                            self.size,
                                            *span,
                                            db,
                                            &mut mcxt2,
                                        )? {
                                            db.maybe_report_error(
                                                TypeError::Unify(
                                                    self.clone(),
                                                    Spanned::new(term, *span),
                                                    t2,
                                                    ReasonExpected::MustMatch(*s2),
                                                )
                                                .into_error(self.cxt.file(db), db, self),
                                            );
                                        }
                                    }
                                    MetaEntry::Unsolved(_, _, _) => {
                                        self.local_metas[*n as usize] =
                                            MetaEntry::Solved(Arc::new(term.clone()), *span);
                                    }
                                }
                            }
                            _ => self.solved_globals.push(i.clone()),
                        }
                    }
                }
            }
        }
        Ok(block)
    }
}
impl Var<Lvl> {
    fn pretty_meta(self, mcxt: &MCxt, db: &dyn Compiler) -> Doc {
        match self {
            Var::Meta(m) => m.pretty(mcxt, db),

            Var::Local(l) => Doc::start("constrained value of local ")
                .chain(Val::local(l, Val::Type).pretty(db, mcxt)),

            _ => unreachable!(),
        }
    }
}
impl PreDef {
    fn describe(&self, db: &dyn Compiler) -> Doc {
        match self {
            PreDef::Fun(n, _, _, _, _) => Doc::start("type of function '").add(n.get(db)).add("'"),
            PreDef::Val(n, _, _) => Doc::start("type of definition '").add(n.get(db)).add("'"),
            PreDef::Type {
                name,
                is_eff: false,
                ..
            } => Doc::start("type of data type '").add(name.get(db)).add("'"),
            PreDef::Type {
                name, is_eff: true, ..
            } => Doc::start("type of effect type '")
                .add(name.get(db))
                .add("'"),
            PreDef::Impl(Some(n), _, _) => Doc::start("type of implicit '").add(n.get(db)).add("'"),
            PreDef::Impl(None, _, _) => Doc::start("type of implicit"),
            PreDef::Expr(_) => Doc::start("type of expression"),
            PreDef::FunDec(n, _, _, _) => Doc::start("type of function declaration '")
                .add(n.get(db))
                .add("'"),
            PreDef::ValDec(n, _) => Doc::start("type of declaration '").add(n.get(db)).add("'"),
            PreDef::Cons(_, _) => unreachable!("Constructor types should already be solved!"),
            PreDef::Typed(d, _, _) => d.describe(db),
        }
    }
}
impl Meta {
    fn pretty(self, mcxt: &MCxt, db: &dyn Compiler) -> Doc {
        match self {
            Meta::Global(id, _) => db.lookup_intern_predef(id).describe(db),
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
    /// Extracts the type given. If no type is given, returns a meta; if it doesn't typecheck, returns None and doesn't report the errors as they'll be caught in elaborate_def().
    pub fn given_type(&self, id: PreDefId, cxt: Cxt, db: &dyn Compiler) -> Option<VTy> {
        let mut mcxt = MCxt::new(cxt, MCxtType::Global(id), db);
        match self {
            PreDef::Typed(_, ty, _) => Some(ty.clone()),
            PreDef::Fun(_, args, rty, _, effs) | PreDef::FunDec(_, args, rty, effs) => {
                let mut rargs = Vec::new();
                elab_args(args, &mut rargs, &mut mcxt, db).ok()?;

                // TODO what to do with inferred effects?
                let effs: Result<_, _> = effs
                    .iter()
                    .flatten()
                    .map(|x| {
                        check(
                            x,
                            &Val::builtin(Builtin::Eff, Val::Type),
                            ReasonExpected::UsedInWith,
                            db,
                            &mut mcxt,
                        )
                        .map(|x| x.evaluate(&mcxt.env(), &mcxt, db))
                    })
                    .collect();

                match check(rty, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt)
                    .and_then(|a| effs.map(|b| (a, b)))
                {
                    Ok((rty, effs)) => {
                        let rty = rty.evaluate(&mcxt.env(), &mcxt, db);
                        let mut l = mcxt.size;
                        Some(
                            rargs
                                .into_iter()
                                .rfold((rty, effs), |(rty, effs), (name, i, xty)| {
                                    let rty = rty.quote(l, &mcxt, db);
                                    l = l.dec();
                                    (
                                        Val::Clos(
                                            Pi,
                                            i,
                                            Box::new(Clos {
                                                name,
                                                ty: xty,
                                                env: Env::new(l),
                                                term: rty,
                                            }),
                                            effs,
                                        ),
                                        Vec::new(),
                                    )
                                })
                                .0,
                        )
                    }
                    Err(_) => None,
                }
            }
            PreDef::Type {
                is_eff, ty_args, ..
            } => {
                let mut rargs = Vec::new();
                elab_args(ty_args, &mut rargs, &mut mcxt, db).ok()?;
                let mut l = mcxt.size;
                let ty_rty = if *is_eff {
                    Val::builtin(Builtin::Eff, Val::Type)
                } else {
                    Val::Type
                };
                Some(rargs.into_iter().rfold(ty_rty, |rty, (name, i, xty)| {
                    let rty = rty.quote(l, &mcxt, db);
                    l = l.dec();
                    Val::Clos(
                        Pi,
                        i,
                        Box::new(Clos {
                            name,
                            ty: xty,
                            env: Env::new(l),
                            term: rty,
                        }),
                        Vec::new(),
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
                    Err(_) => None,
                }
            }
            PreDef::Cons(_, ty) => Some(ty.clone()),
        }
    }
}

// TODO infer-check split for definitions
pub fn elaborate_def(db: &dyn Compiler, def: DefId) -> Result<ElabInfo, DefError> {
    let start_time = Instant::now();

    let (predef_id, state) = db.lookup_intern_def(def);
    let predef = db.lookup_intern_predef(predef_id);
    let cxt = state.cxt;
    let file = cxt.file(db);
    let mut mcxt = MCxt::from_state(state, MCxtType::Local(def));

    let (term, ty) = match infer_def(&predef, def, &mut mcxt, db) {
        Ok(x) => x,
        Err(e) => {
            db.maybe_report_error(e.into_error(file, db, &mcxt));
            return Err(DefError::ElabError);
        }
    };

    // mcxt.solved_globals
    //     .push(RecSolution::Defined(predef_id, 0, predef.span(), ty.clone()));
    let ret = match mcxt.check_locals(db) {
        Ok(()) => {
            let term = term.inline_metas(&mcxt, cxt.size(db), db);
            let ty = ty.inline_metas(cxt.size(db), &mcxt, db);

            // Print out the type and value of each definition
            // let d = Doc::keyword("val")
            //     .space()
            //     .add(predef.name().map_or("_".to_string(), |x| x.get(db)))
            //     .line()
            //     .add(":")
            //     .space()
            //     .chain(ty.pretty(db, &mcxt))
            //     .group()
            //     .line()
            //     .add("=")
            //     .space()
            //     .chain(term.pretty(db, &mut Names::new(cxt, db)))
            //     .indent()
            //     .group();
            // println!("{}\n", d.ansi_string());

            let effects = if mcxt.eff_stack.scopes.last().map_or(false, |x| x.0) {
                mcxt.eff_stack.pop_scope()
            } else {
                Vec::new()
            };

            Ok(ElabInfo {
                term: Arc::new(term),
                typ: Arc::new(ty),
                solved_globals: Arc::new(mcxt.solved_globals),
                children: Arc::new(mcxt.children),
                effects: Arc::new(effects),
            })
        }
        Err(()) => {
            // We don't want the term with local metas in it getting out
            Err(DefError::ElabError)
        }
    };

    if let Ok(ret) = &ret {
        if predef.attributes.contains(&Attribute::Elaborate) {
            let end_time = Instant::now();
            let name = predef
                .name()
                .map(|x| db.lookup_intern_name(x))
                .unwrap_or_else(|| "<unnamed>".to_string());
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
                .unwrap_or_else(|| "<unnamed>".to_string());
            println!("Normalize time for {}: {:?}", name, n_end - n_start);
        }
    }

    ret
}

fn infer_def(
    def: &PreDef,
    id: DefId,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<(Term, VTy), TypeError> {
    match def {
        PreDef::Typed(def, ty, reason) => {
            let term = check_def(def, id, ty, reason.clone(), mcxt, db)?;
            Ok((term, ty.clone()))
        }
        PreDef::FunDec(_, _from, _to, _effs) => {
            // TODO: When function declarations are actually used, change this so they're dependent.
            todo!("function declarations")
            // for (_, _, from) in from {
            //     if let Err(e) = check(from, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
            //         db.report_error(e.into_error(file, db, &mcxt));
            //     }
            // }
            // if let Err(e) = check(to, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
            //     db.report_error(e.into_error(file, db, &mcxt));
            // }
            // Err(DefError::NoValue)
        }
        PreDef::ValDec(name, ty) => {
            if !mcxt.is_sig {
                return Err(TypeError::IllegalDec(name.span(), true));
            }
            let t = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            Ok((t, Val::Type))
        }
        _ if mcxt.is_sig => {
            return Err(TypeError::IllegalDec(def.span(), false));
        }

        PreDef::Val(_, ty, val) | PreDef::Impl(_, ty, val) => {
            let tyspan = ty.span();
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let ty = ty.evaluate(&mcxt.env(), &mcxt, db);
            let val = check(val, &ty, ReasonExpected::Given(tyspan), db, mcxt)?;
            Ok((val, ty))
            // TODO multiple TypeErrors?
            // Err(e) => {
            //     db.maybe_report_error(e.into_error(file, db, &mcxt));
            //     // The given type is invalid, but we can still try to infer the type
            //     match infer(true, val, db, &mut mcxt) {
            //         Ok(x) => Ok(x),
            //         Err(e) => {
            //             db.maybe_report_error(e.into_error(file, db, &mcxt));
            //             Err(DefError::ElabError)
            //         }
            //     }
            // }
        }
        PreDef::Fun(_, args, body_ty, body, effs) => {
            // First, add the arguments to the environment
            let mut targs = Vec::new();
            elab_args(args, &mut targs, mcxt, db)?;

            // Then elaborate and evaluate the given return type
            let tyspan = body_ty.span();
            let body_ty = check(body_ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let vty = body_ty.evaluate(&mcxt.env(), &mcxt, db);

            let (effs, open) = match effs {
                Some(effs) => (effs.clone(), false),
                None => (Vec::new(), true),
            };
            let effs = effs
                .iter()
                .map(|x| {
                    check(
                        x,
                        &Val::builtin(Builtin::Eff, Val::Type),
                        ReasonExpected::UsedInWith,
                        db,
                        mcxt,
                    )
                    .map(|x| x.evaluate(&mcxt.env(), &mcxt, db))
                })
                .collect::<Result<_, _>>()?;
            // And last, check the function body against the return type
            let (body, vty, effs) = check_fun(
                body,
                vty,
                ReasonExpected::Given(tyspan),
                effs,
                open,
                db,
                mcxt,
            )?;

            // Then construct the function term and type
            let effs_t: Vec<_> = effs
                .iter()
                // Decrease the size because the effects are outside the last pi type
                .map(|x| x.clone().quote(mcxt.size.dec(), &mcxt, db))
                .collect();
            Ok((
                targs
                    .iter()
                    .rfold(
                        (body, mcxt.size, effs_t),
                        |(body, mut size, effs), (name, icit, ty)| {
                            // We need to quote the type of this argument, so decrease the size to
                            // remove this argument from the context, since its own type can't use it
                            size = size.dec();
                            (
                                Term::Clos(
                                    Lam,
                                    *name,
                                    *icit,
                                    Box::new(ty.clone().quote(size, &mcxt, db)),
                                    Box::new(body),
                                    effs,
                                ),
                                size,
                                Vec::new(),
                            )
                        },
                    )
                    .0,
                targs
                    .into_iter()
                    .rfold(
                        (vty, mcxt.size, effs),
                        |(to, size, effs), (name, icit, from)| {
                            (
                                Val::Clos(
                                    Pi,
                                    icit,
                                    Box::new(Clos {
                                        // Don't include the closure's argument in its environment
                                        env: Env::new(size.dec()),
                                        ty: from,
                                        term: to.quote(size, &mcxt, db),
                                        name,
                                    }),
                                    effs,
                                ),
                                size.dec(),
                                Vec::new(),
                            )
                        },
                    )
                    .0,
            ))
        }
        PreDef::Cons(_name, ty) => {
            // We don't have to do anything since the type was already determined when elaborating the type definition
            Ok((
                Term::Var(
                    Var::Cons(id),
                    Box::new(ty.clone().quote(mcxt.size, &mcxt, db)),
                ),
                ty.clone(),
            ))
        }
        PreDef::Type {
            name,
            is_eff,
            ty_args,
            ctors,
            namespace,
        } => {
            // A copy of the context before we added the type arguments
            let cxt_before = mcxt.state();

            // Evaluate the argument types and collect them up
            let mut targs = Vec::new();
            elab_args(ty_args, &mut targs, mcxt, db)?;

            // Create the type of the datatype we're defining (e.g. `Option : Type -> Type`)
            // We have to do this now, so that the constructors can use the type
            let ty_rty = if *is_eff {
                Val::builtin(Builtin::Eff, Val::Type)
            } else {
                Val::Type
            };
            let (ty_ty, _) = targs
                .iter()
                .rfold((ty_rty, mcxt.size), |(to, l), (n, i, from)| {
                    (
                        Val::Clos(
                            Pi,
                            *i,
                            Box::new(Clos {
                                env: Env::new(l.dec()),
                                ty: from.clone(),
                                term: to.quote(l, &mcxt, db),
                                name: *n,
                            }),
                            Vec::new(),
                        ),
                        l.dec(),
                    )
                });
            let (predef_id, _) = db.lookup_intern_def(id);
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
            for (cname, args, cty) in ctors.iter(db) {
                if let Some(&span) = seen.get(&cname) {
                    let file = mcxt.cxt.file(db);
                    let e = Error::new(
                        file,
                        format!(
                            "Duplicate constructor name '{}' in type definition",
                            db.lookup_intern_name(*cname)
                        ),
                        cname.span(),
                        "declared again here",
                    )
                    .with_label(file, span, "previously declared here");
                    db.report_error(e);
                    continue;
                } else {
                    seen.insert(*cname, cname.span());
                }

                let mut cargs = Vec::new();

                // If the user provided a type for the constructor, they can't use the type arguments
                // Either way, we need to reset it somewhat so we can't use arguments from other constructors
                // But we use the same mcxt, so meta solutions get saved, we just reset the `CxtState`
                // Also, effect constructors can always use the type arguments
                if cty.is_some() && !is_eff {
                    mcxt.set_state(cxt_before.clone());
                } else {
                    mcxt.set_state(cxt_after.clone());
                    // If they can use the type parameters, add them all as implicit arguments
                    // They go in the same order as the type parameters, so we don't need to change the mcxt
                    for (n, i, t) in &targs {
                        cargs.push((
                            *n,
                            if ctors.is_short_form() {
                                *i
                            } else {
                                Icit::Impl
                            },
                            t.clone(),
                        ));
                    }
                }
                let start_size = mcxt.size;

                // Elaborate the constructor argument types
                for (name, icit, ty) in args {
                    let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
                    let vty = ty.evaluate(&mcxt.env(), &mcxt, db);
                    cargs.push((name, icit, vty.clone()));
                    mcxt.define(name, NameInfo::Local(vty), db);
                }

                // If the user provided a return type for the constructor, typecheck it
                let (cty, eff_ty) = if let Some(cty) = cty {
                    let x = check(cty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
                    if *is_eff {
                        // TODO make this a function or something

                        // predef_id is for the type being declared
                        // Ty a b of C [a] [b] ... : Ty a b
                        // so Ix's decrease from left to right, and start at the first implicit argument
                        // which is right after the state cxt_before stores
                        // But, this is an effect, so the parent data type isn't inside the innermost pi
                        // So if there are any pis, decrease the level by one
                        // TODO what if the last argument is a fun but there was a pi before that?
                        let size = if start_size != mcxt.size {
                            mcxt.size.dec()
                        } else {
                            mcxt.size
                        };
                        let ty_ty = ty_ty.clone().quote(size, &mcxt, db);
                        let (f, _, _) = targs.iter().fold(
                            (
                                Term::Var(Var::Rec(predef_id), Box::new(ty_ty.clone())),
                                cxt_before.size.next_lvl(),
                                ty_ty.clone(),
                            ),
                            |(f, lvl, ty), (_n, i, t)| {
                                let ix = size.to_ix(lvl);
                                let (xty, rty) = match ty {
                                    Term::Clos(Pi, _, _, xty, rty, _) => {
                                        // It might use the value, so give it that
                                        let mut env = Env::new(size);
                                        env.push(Some(Val::local(size.to_lvl_(ix), t.clone())));
                                        (*xty, rty.eval_quote(&mut env, size, &mcxt, db))
                                    }
                                    Term::Fun(xty, rty, _) => (*xty, *rty),
                                    _ => unreachable!(),
                                };
                                (
                                    Term::App(
                                        *i,
                                        Box::new(f),
                                        Box::new(Term::Var(Var::Local(ix), Box::new(xty))),
                                    ),
                                    lvl.inc(),
                                    rty,
                                )
                            },
                        );
                        (x, Some(f))
                    } else {
                        match x.ret().head() {
                            Term::Var(Var::Rec(id), _) if *id == predef_id => (x, None),
                            _ => {
                                // We want the type to appear in the error message as it was written - e.g. `Result T E`
                                let mut type_string = db.lookup_intern_name(**name);
                                for (n, _, _) in &targs {
                                    type_string.push(' ');
                                    type_string.push_str(&db.lookup_intern_name(*n));
                                }
                                let e = Error::new(
                                    mcxt.cxt.file(db),
                                    "Constructor return type must be the type it's a part of",
                                    cty.span(),
                                    Doc::start("expected return type ")
                                        .chain(Doc::start(type_string).style(Style::None))
                                        .style(Style::Error),
                                );
                                db.report_error(e);
                                return Err(TypeError::Sentinel);
                            }
                        }
                    }
                // If they didn't provide a return type, use the type constructor applied to all args
                } else {
                    if *is_eff {
                        let e = Error::new(
                            mcxt.cxt.file(db),
                            format!(
                                "Effect constructor '{}' must declare return type",
                                db.lookup_intern_name(*cname)
                            ),
                            cname.span(),
                            "this requires a return type",
                        )
                        .with_note("use the unit type `()` if it returns nothing");
                        db.report_error(e);
                        continue;
                    }

                    // predef_id is for the type being declared
                    // Ty a b of C [a] [b] ... : Ty a b
                    // so Ix's decrease from left to right, and start at the first implicit argument
                    // which is right after the state cxt_before stores
                    let ty_ty = ty_ty.clone().quote(mcxt.size, &mcxt, db);
                    (
                        targs
                            .iter()
                            .fold(
                                (
                                    Term::Var(Var::Rec(predef_id), Box::new(ty_ty.clone())),
                                    cxt_before.size.next_lvl(),
                                    ty_ty.clone(),
                                ),
                                |(f, lvl, ty), (_n, i, t)| {
                                    let ix = mcxt.size.to_ix(lvl);
                                    let (xty, rty) = match ty {
                                        Term::Clos(Pi, _, _, xty, rty, _) => {
                                            // It might use the value, so give it that
                                            let mut env = Env::new(mcxt.size);
                                            env.push(Some(Val::local(
                                                mcxt.size.to_lvl_(ix),
                                                t.clone(),
                                            )));
                                            (*xty, rty.eval_quote(&mut env, mcxt.size, &mcxt, db))
                                        }
                                        Term::Fun(xty, rty, _) => (*xty, *rty),
                                        _ => unreachable!(),
                                    };
                                    (
                                        Term::App(
                                            *i,
                                            Box::new(f),
                                            Box::new(Term::Var(Var::Local(ix), Box::new(xty))),
                                        ),
                                        lvl.inc(),
                                        rty,
                                    )
                                },
                            )
                            .0,
                        None,
                    )
                };

                let (full_ty, _, _) = cargs.into_iter().rfold(
                    (cty, eff_ty, mcxt.size),
                    |(to, eff, l), (n, i, from)| {
                        (
                            Term::Clos(
                                Pi,
                                n,
                                i,
                                Box::new(from.quote(l.dec(), &mcxt, db)),
                                Box::new(to),
                                eff.into_iter().collect(),
                            ),
                            None,
                            l.dec(),
                        )
                    },
                );

                let full_ty = full_ty.evaluate(&Env::new(cxt_before.size), &mcxt, db);
                // .inline_metas(&mcxt, db);

                scope.push((cname.clone(), full_ty));
            }

            mcxt.set_state(cxt_before.clone());

            // Make sure to inline metas solved in constructor types
            let ty_ty = ty_ty.inline_metas(mcxt.size, &mcxt, db);
            mcxt.undef(db);
            mcxt.define(
                **name,
                NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()),
                db,
            );
            let mut scope: Vec<_> = scope
                .into_iter()
                .map(|(cname, ty)| {
                    let ty = ty.inline_metas(mcxt.size, &mcxt, db);
                    let def_id = db.intern_def(
                        db.intern_predef(Arc::new(PreDef::Cons(cname.clone(), ty).into())),
                        cxt_before.clone(),
                    );
                    (*cname, def_id)
                })
                .collect();

            // Add definitions from the associated namespace
            // They need the type of the datatype we're defining
            // They also need the constructors, so we create a temporary scope.
            // Since Var::unify doesn't compare the scope ids, it works.
            let tscope = db.intern_scope(Arc::new(scope.clone()));
            let assoc_cxt = mcxt.cxt.define(
                **name,
                NameInfo::Other(Var::Type(id, tscope), ty_ty.clone()),
                db,
            );
            // And they have access to all the constructors in `scope` at the top level
            let assoc_cxt = scope.iter().fold(assoc_cxt, |cxt, &(n, v)| {
                cxt.define(n, NameInfo::Def(v), db)
            });
            scope.extend(
                // The associated namespace can't directly use effects
                intern_block(namespace.clone(), db, CxtState::new(assoc_cxt, db))
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
                    Var::Type(id, scope),
                    Box::new(ty_ty.clone().quote(mcxt.size, &mcxt, db)),
                ),
                ty_ty,
            ))
        }
        PreDef::Expr(e) => infer(true, e, db, mcxt),
    }
}

fn check_def(
    def: &PreDef,
    id: DefId,
    ty: &VTy,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<Term, TypeError> {
    match def {
        PreDef::Val(_, ty2, val) | PreDef::Impl(_, ty2, val) => {
            let ty2 = check(ty2, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let ty2 = ty2.evaluate(&mcxt.env(), &mcxt, db);
            try_unify(ty, &ty2, None, def.span(), reason.clone(), mcxt, db)?;
            let val = check(val, ty, reason, db, mcxt)?;
            Ok(val)
        }
        // TODO functions
        _ => {
            let (term, i_ty) = infer_def(def, id, mcxt, db)?;
            try_unify(ty, &i_ty, Some(&term), def.span(), reason, mcxt, db)?;
            Ok(term)
        }
    }
}

fn try_unify(
    ty: &VTy,
    i_ty: &VTy,
    term: Option<&Term>,
    span: Span,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<(), TypeError> {
    if !unify(ty.clone(), i_ty.clone(), mcxt.size, span, db, mcxt)? {
        // Use an arity error if we got a function type but don't expect one
        match (&ty, &i_ty) {
            (Val::Clos(Pi, _, _, _), _) | (Val::Fun(_, _, _), _) => (),
            (_, Val::Fun(_, _, _)) | (_, Val::Clos(Pi, _, _, _))
                if matches!(term, Some(Term::App(_, _, _))) =>
            {
                let got = term.unwrap().spine_len();
                let hty = match term.cloned().unwrap().evaluate(&mcxt.env(), mcxt, db) {
                    Val::App(_, hty, _, _) => *hty,
                    _ => i_ty.clone(),
                };
                let exp = hty.arity(false);
                return Err(TypeError::WrongArity(Spanned::new(hty, span), exp, got));
            }
            _ => (),
        }
        Err(TypeError::Unify(
            mcxt.clone(),
            Spanned::new(i_ty.clone().inline_metas(mcxt.size, mcxt, db), span),
            ty.clone().inline_metas(mcxt.size, mcxt, db),
            reason,
        ))
    } else {
        Ok(())
    }
}

/// Elaborates and evaluates the argument types, adding the arguments to the context and storing them in `rargs`.
/// Stops at the first type error.
fn elab_args(
    args: &[(Name, Icit, Pre)],
    rargs: &mut Vec<(Name, Icit, VTy)>,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<(), TypeError> {
    for (name, icit, ty) in args {
        let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
        let vty = ty.evaluate(&mcxt.env(), mcxt, db);
        rargs.push((*name, *icit, vty.clone()));
        mcxt.define(*name, NameInfo::Local(vty), db);
    }
    Ok(())
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ScopeType {
    Type(Name),
    Struct,
}

/// The reason we expected a value to have a given type, used in "could not match types" errors
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ReasonExpected {
    UsedAsType,
    UsedInWith,
    IfCond,
    LogicOp,
    MustMatch(Span),
    Given(Span),
    ArgOf(Span, VTy),
}
impl ReasonExpected {
    pub fn span_or(&self, or: Span) -> Span {
        match self {
            ReasonExpected::MustMatch(s)
            | ReasonExpected::Given(s)
            | ReasonExpected::ArgOf(s, _) => *s,
            _ => or,
        }
    }

    /// Adds a description of the reason to the `err`.
    /// This function adds it to an existing error instead of returning a Doc because some reasons have spans attached, and some don't.
    fn add(self, err: Error, file: FileId, db: &dyn Compiler, mcxt: &MCxt) -> Error {
        match self {
            ReasonExpected::UsedAsType => err
                .with_note(Doc::start("expected because it was used as a type").style(Style::Note)),
            ReasonExpected::UsedInWith => err.with_note(
                Doc::start("expected because it was used as an effect in a `with` type")
                    .style(Style::Note),
            ),
            ReasonExpected::IfCond => err.with_note(
                Doc::start("expected because if conditions must have type Bool").style(Style::Note),
            ),
            ReasonExpected::LogicOp => err.with_note(
                Doc::start("expected because operands of `and` and `or` must have type Bool")
                    .style(Style::Note),
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
                Doc::start("expected because it was passed to this, of type")
                    .line()
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
    InvalidLiteral(Span, Literal, Builtin),
    MetaScope(Span, Var<Lvl>, Name),
    MetaOccurs(Span, Var<Lvl>),
    MetaSpine(Span, Var<Lvl>, Val),
    NotStruct(Spanned<VTy>),
    MemberNotFound(Span, ScopeType, Name),
    InvalidPattern(Span),
    WrongNumConsArgs(Span, usize, usize),
    Inexhaustive(Span, crate::pattern::Cov, VTy),
    InvalidPatternBecause(Box<TypeError>),
    WrongArity(Spanned<VTy>, usize, usize),
    EffNotAllowed(Span, Val, EffStack),
    /// No catchable effects for `catch` expression. If the `bool` is true, then IO was included.
    WrongCatchType(Span, bool),
    EffPatternType(Span, Span, Val, Vec<Val>),
    BinOpType(Span, VTy, Span),
    /// If the `bool` is true, this is a declaration outside a `sig`; otherwise, vice-versa.
    IllegalDec(Span, bool),
    /// An error has already been reported to the database, so this should be ignored.
    Sentinel,
}
impl TypeError {
    fn into_error(self, file: FileId, db: &dyn Compiler, mcxt: &MCxt) -> Option<Error> {
        Some(match self {
            TypeError::Sentinel => return None,
            TypeError::IllegalDec(span, true) => Error::new(
                file,
                "Illegal declaration outside record signature",
                span,
                "declarations aren't allowed here; try adding a body with =",
            ),
            TypeError::IllegalDec(span, false) => Error::new(
                file,
                "Illegal non-declaration in record signature",
                span,
                "definitions aren't allowed here; try removing the body",
            ),
            TypeError::BinOpType(vspan, vty, opspan) => Error::new(
                file,
                Doc::start("Expected number in operand to binary operator, but got type ")
                    .chain(vty.pretty(db, mcxt).style(Style::None))
                    .style(Style::Bold),
                vspan,
                "expected number here"
            )
            .with_label(file, opspan, "in operand of this operator"),
            TypeError::NotFound(n) => Error::new(
                file,
                format!("Name not found in scope: '{}'", n.get(db)),
                n.span(),
                "not found",
            ),
            TypeError::NotFunction(mcxt, t) => Error::new(
                file,
                Doc::start("Expected function type in application, but got")
                    .line()
                    .chain(t.pretty(db, &mcxt).style(Style::None))
                    .style(Style::Bold),
                t.span(),
                "not a function",
            ),
            TypeError::Unify(mcxt, a, b, r) => r.add(
                Error::new(
                    file,
                    Doc::start("Could not match types, expected")
                        .line()
                        .chain(b.pretty(db, &mcxt).style(Style::None))
                        .line()
                        .add("but got")
                        .line()
                        .chain(a.pretty(db, &mcxt).style(Style::None))
                        .style(Style::Bold),
                    a.span(),
                    Doc::start("expected")
                        .line()
                        .chain(b.pretty(db, &mcxt).style(Style::None))
                        .line()
                        .add("here")
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
                "solution found here",
            ),
            TypeError::MetaOccurs(s, m) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt, db))
                    .add(" would be recursive")
                    .style(Style::Bold),
                s,
                "solution found here",
            ),
            // TODO: this is complicated to explain, so make and link to a wiki page in the error message
            TypeError::MetaSpine(s, m, v) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt, db))
                    .add(" is ambiguous: cannot depend on value")
                    .line()
                    .chain(v.pretty(db, mcxt).style(Style::None))
                    .style(Style::Bold),
                s,
                "solution depends on a non-variable",
            )
            .with_note(Doc::start("because here it depends on a specific value, the compiler doesn't know what the solution should be for other values").style(Style::Note)),
            TypeError::NotStruct(ty) => Error::new(
                file,
                Doc::start("Value of type")
                    .line()
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .line()
                    .add("does not have members")
                    .style(Style::Bold),
                ty.span(),
                "tried to access member here",
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
                        ScopeType::Struct => "struct".to_string(),
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
                "invalid pattern",
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
                Doc::start("Inexhaustive match: patterns")
                    .line()
                    .chain(cov.pretty_rest(&ty, db, mcxt).style(Style::None))
                    .line()
                    .add("not covered")
                    .style(Style::Bold),
                span,
                Doc::start("this has type ")
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .style(Style::Error),
            ),
            TypeError::InvalidPatternBecause(e) => {
                let mut e = e.into_error(file, db, mcxt)?;
                let message = format!("Invalid pattern: {}", e.message());
                *e.message() = message;
                e
            }
            TypeError::NotIntType(span, ty, r) => r.add(
                Error::new(
                    file,
                    Doc::start("Expected value of type")
                        .line()
                        .chain(ty.pretty(db, mcxt).style(Style::None))
                        .line()
                        .add("but got integer")
                        .style(Style::Bold),
                    span,
                    "this is an integer",
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
            TypeError::InvalidLiteral(span, l, t) => Error::new(
                file,
                Doc::start("Invalid literal for type ")
                    .add(t.name())
                    .add(": value ")
                    .chain(l.pretty(db)),
                span,
                Doc::start("Does not fit in type ")
                    .add(t.name()),
            ),
            TypeError::EffNotAllowed(span, eff, mut stack) => {
                let base = Error::new(
                    file,
                    Doc::start("Effect")
                        .line()
                        .chain(eff.pretty(db, mcxt).style(Style::None))
                        .line()
                        .add("not allowed in this context")
                        .style(Style::Bold),
                    span,
                    Doc::start("this performs effect")
                        .line()
                        .chain(eff.pretty(db, mcxt).style(Style::None))
                        .style(Style::Error)
                );
                if stack.scopes.is_empty() {
                    base.with_note("effects are not allowed in the top level context")
                } else if stack.scope_start().unwrap() == stack.effs.len() {
                    base.with_label(file, stack.scopes.last().unwrap().2, "this context does not allow effects")
                } else {
                    base.with_label(file, stack.scopes.last().unwrap().2,
                        Doc::start("this context allows effects ")
                            .chain(Doc::intersperse(stack.pop_scope().into_iter().map(|eff| eff.pretty(db, mcxt).style(Style::None)), Doc::start(",").space()))
                            .style(Style::Error)
                    )
                }
            }
            TypeError::WrongArity(ty, expected, got) => Error::new(
                file,
                Doc::start(if got > expected {
                    "Too many arguments "
                } else {
                    "Too few arguments "
                })
                .add(got)
                .add(" to value of type")
                .line()
                .chain(ty.pretty(db, mcxt).style(Style::None))
                .line()
                .add("which expects ")
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
            TypeError::WrongCatchType(span, has_io) => Error::new(
                file,
                Doc::start("`catch` expression requires effect to catch, but expression performs no catchable effects")
                    .style(Style::Bold),
                span,
                if has_io {
                    "this expression only performs the IO effect, which can't be caught"
                } else {
                    "this expression performs no effects"
                },
            )
            .with_note(
                Doc::start("to pattern-match on a value without effects, use ")
                    .chain(Doc::keyword("case"))
                    .add(" instead of ")
                    .chain(Doc::keyword("catch"))
                    .style(Style::Note)
            ),
            TypeError::EffPatternType(vspan, pspan, _ty, effs) if effs.is_empty() => Error::new(
                file,
                Doc::start("`eff` pattern requires caught effects to match against, but `case` doesn't catch effects")
                    .style(Style::Bold),
                pspan,
                "`eff` pattern requires effects",
            )
            .with_label(
                file,
                vspan,
                Doc::start("if this expression performs effects, try using ")
                    .chain(Doc::keyword("catch"))
                    .add(" instead of ")
                    .chain(Doc::keyword("case"))
                    .add(" here")
                    .style(Style::Note),
            ),
            TypeError::EffPatternType(vspan, pspan, ty, effs) => Error::new(
                file,
                Doc::start("got effect type")
                    .line()
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .line()
                    .add("but expected one of")
                    .line()
                    .chain(Doc::intersperse(effs.iter().map(|e| e.pretty(db, mcxt).style(Style::None)), Doc::start(',').space()))
                    .style(Style::Bold),
                pspan,
                "wrong effect type for `eff` pattern",
            )
            .with_label(
                file,
                vspan,
                Doc::start("this expression performs effects")
                    .line()
                    .chain(Doc::intersperse(effs.iter().map(|e| e.pretty(db, mcxt).style(Style::None)), Doc::start(',').line()).group())
                    .style(Style::Note),
            ),
        })
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

fn p_unify_elim(
    mode: UnifyMode,
    a: Elim,
    b: Elim,
    size: Size,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<TBool, TypeError> {
    match (a, b) {
        (Elim::App(i, a), Elim::App(j, b)) if i == j => p_unify(mode, a, b, size, span, db, mcxt),

        _ => Ok(No),
    }
}

fn p_unify(
    mode: UnifyMode,
    a: Val,
    b: Val,
    size: Size,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<TBool, TypeError> {
    match (a, b) {
        (Val::Arc(a), b) | (b, Val::Arc(a)) => {
            let a = a.into_owned();
            p_unify(mode, a, b, size, span, db, mcxt)
        }

        (Val::Type, Val::Type) => Ok(Yes),

        (Val::Lit(a, _), Val::Lit(b, _)) => Ok((a == b).into()),

        (Val::App(h, _, v, _), Val::App(h2, _, v2, _)) if h.unify(h2, db) => {
            let mut r = Yes;
            for (a, b) in v.into_iter().zip(v2.into_iter()) {
                r = r & p_unify_elim(mode, a, b, size, span, db, mcxt)?;
            }
            Ok(r)
        }

        (Val::Struct(k, v), Val::Struct(k2, v2)) => {
            match (k, k2) {
                (StructKind::Struct(_), StructKind::Struct(_)) => (),
                (StructKind::Sig, StructKind::Sig) => (),
                _ => return Ok(No),
            }
            let mut r = Yes;
            for ((n, a), (n2, b)) in v.into_iter().zip(v2.into_iter()) {
                if n != n2 {
                    return Ok(No);
                }
                r = r & p_unify(mode, a, b, size, span, db, mcxt)?;
            }
            Ok(r)
        }

        // Since our terms are locally nameless (we're using De Bruijn levels), we automatically get alpha equivalence.
        (Val::Clos(Lam, _, cl, _), Val::Clos(Lam, _, cl2, _)) => p_unify(
            mode,
            cl.vquote(size, mcxt, db),
            cl2.vquote(size, mcxt, db),
            size.inc(),
            span,
            db,
            mcxt,
        ),

        // If one side is a lambda, the other side just needs to unify to the same thing when we apply it to the same thing
        (Val::Clos(Lam, icit, cl, _), t) | (t, Val::Clos(Lam, icit, cl, _)) => {
            let ty = cl.ty.clone();
            p_unify(
                mode,
                cl.vquote(size, mcxt, db),
                t.app(Elim::App(icit, Val::local(size.next_lvl(), ty)), mcxt, db),
                size.inc(),
                span,
                db,
                mcxt,
            )
        }

        (Val::Clos(Pi, i, cl, effs), Val::Clos(Pi, i2, cl2, effs2)) if i == i2 => {
            Ok(
                p_unify(mode, cl.ty.clone(), cl2.ty.clone(), size, span, db, mcxt)?
                // Applying both to the same thing (Local(l))
                & p_unify(
                    mode,
                    cl.vquote(size, mcxt, db),
                    cl2.vquote(size, mcxt, db),
                    size.inc(),
                    span,
                    db,
                    mcxt,
                )?
                & TBool::from(effs.len() == effs2.len())
                & effs
                    .into_iter()
                    .zip(effs2)
                    .map(|(a, b)| p_unify(mode, a, b, size, span, db, mcxt))
                    .fold(Ok(Yes), |acc, r| acc.and_then(|acc| r.map(|r| acc & r)))?,
            )
        }
        (Val::Clos(Pi, Icit::Expl, cl, effs), Val::Fun(from, to, effs2))
        | (Val::Fun(from, to, effs), Val::Clos(Pi, Icit::Expl, cl, effs2)) => {
            Ok(p_unify(mode, cl.ty.clone(), *from, size, span, db, mcxt)?
                & p_unify(
                    mode,
                    cl.vquote(size, mcxt, db),
                    *to,
                    size.inc(),
                    span,
                    db,
                    mcxt,
                )?
                & TBool::from(effs.len() == effs2.len())
                & effs
                    .into_iter()
                    .zip(effs2)
                    .map(|(a, b)| p_unify(mode, a, b, size, span, db, mcxt))
                    .fold(Ok(Yes), |acc, r| acc.and_then(|acc| r.map(|r| acc & r)))?)
        }
        (Val::Fun(a, b, effs), Val::Fun(a2, b2, effs2)) => {
            Ok(p_unify(mode, *a, *a2, size, span, db, mcxt)?
                & p_unify(mode, *b, *b2, size, span, db, mcxt)?
                & TBool::from(effs.len() == effs2.len())
                & effs
                    .into_iter()
                    .zip(effs2)
                    .map(|(a, b)| p_unify(mode, a, b, size, span, db, mcxt))
                    .fold(Ok(Yes), |acc, r| acc.and_then(|acc| r.map(|r| acc & r)))?)
        }

        // Solve metas

        // Make sure order doesn't matter - switch sides if the second one is higher
        (Val::App(Var::Meta(m), mty, s, g), Val::App(Var::Meta(m2), mty2, s2, g2)) if m2 > m => {
            p_unify(
                mode,
                Val::App(Var::Meta(m2), mty2, s2, g2),
                Val::App(Var::Meta(m), mty, s, g),
                size,
                span,
                db,
                mcxt,
            )
        }

        (Val::App(Var::Meta(m), _, sp, _), t) | (t, Val::App(Var::Meta(m), _, sp, _)) => {
            match mcxt.get_meta(m) {
                Some(v) => {
                    let v = sp
                        .into_iter()
                        .fold(v.evaluate(&mcxt.env(), mcxt, db), |f, e| f.app(e, mcxt, db));
                    p_unify(mode, v, t, size, span, db, mcxt)
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
            if mode.local
                && m2 > m
                && mcxt.local_val(m).is_none()
                && mcxt.local_val(m2).is_none() =>
        {
            p_unify(
                mode,
                Val::App(Var::Local(m2), mty2, s2, g2),
                Val::App(Var::Local(m), mty, s, g),
                size,
                span,
                db,
                mcxt,
            )
        }
        (Val::App(Var::Local(l), _, sp, _), t) | (t, Val::App(Var::Local(l), _, sp, _))
            if mode.local
                // because if it's already solved, or if the other one is a solved local, we'll handle that with the normal inlining logic down below
                && mcxt.local_val(l).is_none()
                && !matches!(t, Val::App(Var::Local(l2), _, _, _) if mcxt.local_val(l2).is_some()) =>
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
        // Same with local variables with constraints
        (Val::App(Var::Local(l), _, _, _), _) | (_, Val::App(Var::Local(l), _, _, _))
            if !mode.inline && mcxt.local_val(l).is_some() =>
        {
            Ok(Maybe)
        }

        (Val::App(h, hty, sp, g), Val::App(h2, hty2, sp2, g2)) if mode.inline => {
            if let Some(v) = g.resolve(h, &sp, size, db, mcxt) {
                p_unify(mode, Val::App(h2, hty2, sp2, g2), v, size, span, db, mcxt)
            } else if let Some(v) = g2.resolve(h2, sp2, size, db, mcxt) {
                p_unify(mode, Val::App(h, hty, sp, g), v, size, span, db, mcxt)
            } else {
                Ok(No)
            }
        }

        (Val::App(h, _, sp, g), x) | (x, Val::App(h, _, sp, g)) if mode.inline => {
            if let Some(v) = g.resolve(h, sp, size, db, mcxt) {
                p_unify(mode, x, v, size, span, db, mcxt)
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
    size: Size,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<bool, TypeError> {
    match p_unify(
        UnifyMode::new(false, false),
        a.clone(),
        b.clone(),
        size,
        span,
        db,
        mcxt,
    )? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(UnifyMode::new(false, true), a, b, size, span, db, mcxt)?.not_maybe()),
    }
}

/// Like `unify()`, but finds local constraints and adds them to the context.
///
/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn local_unify(
    a: Val,
    b: Val,
    size: Size,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<bool, TypeError> {
    match p_unify(
        UnifyMode::new(true, false),
        a.clone(),
        b.clone(),
        size,
        span,
        db,
        mcxt,
    )? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(UnifyMode::new(true, true), a, b, size, span, db, mcxt)?.not_maybe()),
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
        Val::Clos(Pi, Icit::Impl, cl, effs) if insert => {
            let meta = mcxt.new_meta(
                None,
                span,
                MetaSource::ImplicitParam(cl.name),
                cl.ty.clone().quote(mcxt.size, mcxt, db),
                db,
            );
            // TODO effects when applying implicits
            assert!(
                effs.is_empty(),
                "effects when applying implicits not supported yet"
            );
            let vmeta = meta.clone().evaluate(&mcxt.env(), mcxt, db);
            let ret = (*cl).clone().apply(vmeta, mcxt, db);
            insert_metas(
                insert,
                Term::App(Icit::Impl, Box::new(term), Box::new(meta)),
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

        // By default, () refers to the unit *value*
        Pre_::Unit => Ok((
            Term::Var(
                Var::Builtin(Builtin::Unit),
                Box::new(Term::Var(
                    Var::Builtin(Builtin::UnitType),
                    Box::new(Term::Type),
                )),
            ),
            Val::builtin(Builtin::UnitType, Val::Type),
        )),

        Pre_::Lit(Literal::String(n)) => Ok((
            Term::Lit(Literal::String(*n), Builtin::String),
            Val::builtin(Builtin::String, Val::Type),
        )),
        Pre_::Lit(_) => Err(TypeError::UntypedLiteral(pre.span())),

        Pre_::BinOp(op, a, b) => {
            let (va, aty) = infer(true, a, db, mcxt)?;
            // Check b against the type and inline metas first, to allow:
            // a : ?0, b : I32 --> `a + b` which solves ?0 to I32
            let b = check(b, &aty, ReasonExpected::MustMatch(a.span()), db, mcxt)?;
            let aty = aty.inline_metas(mcxt.size, mcxt, db);
            let ity = match &aty {
                Val::App(Var::Builtin(b), _, _, _) => match *b {
                    Builtin::I32 => Term::Var(Var::Builtin(Builtin::I32), Box::new(Term::Type)),
                    Builtin::I64 => Term::Var(Var::Builtin(Builtin::I64), Box::new(Term::Type)),
                    Builtin::F32 => Term::Var(Var::Builtin(Builtin::F32), Box::new(Term::Type)),
                    Builtin::F64 => Term::Var(Var::Builtin(Builtin::F64), Box::new(Term::Type)),
                    _ => return Err(TypeError::BinOpType(a.span(), aty, op.span())),
                },
                _ => return Err(TypeError::BinOpType(a.span(), aty, op.span())),
            };
            // The return type could be different from `ity`, e.g. `==`
            let vrty = op.ret_ty();
            let rty = vrty
                .clone()
                .map(|x| x.quote(mcxt.size, mcxt, db))
                .unwrap_or_else(|| ity.clone());
            let vrty = vrty.unwrap_or_else(|| ity.clone().evaluate(&mcxt.env(), mcxt, db));
            let fty = Term::Fun(
                Box::new(ity.clone()),
                Box::new(Term::Fun(Box::new(ity.clone()), Box::new(rty), Vec::new())),
                Vec::new(),
            );
            let f = Term::Var(Var::Builtin(Builtin::BinOp(**op)), Box::new(fty));
            Ok((
                Term::App(
                    Icit::Expl,
                    Box::new(Term::App(Icit::Expl, Box::new(f), Box::new(va))),
                    Box::new(b),
                ),
                vrty,
            ))
        }

        // a and b ==> if a then b else False
        Pre_::And(a, b) => {
            let a = check(
                a,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::LogicOp,
                db,
                mcxt,
            )?;
            let b = check(
                b,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::LogicOp,
                db,
                mcxt,
            )?;
            let false_t = Term::Var(
                Var::Builtin(Builtin::False),
                Box::new(Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type))),
            );
            Ok((
                a.make_if(
                    b,
                    false_t,
                    Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type)),
                ),
                Val::builtin(Builtin::Bool, Val::Type),
            ))
        }

        // a or b ==> if a then True else b
        Pre_::Or(a, b) => {
            let a = check(
                a,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::LogicOp,
                db,
                mcxt,
            )?;
            let b = check(
                b,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::LogicOp,
                db,
                mcxt,
            )?;
            let true_t = Term::Var(
                Var::Builtin(Builtin::True),
                Box::new(Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type))),
            );
            Ok((
                a.make_if(
                    true_t,
                    b,
                    Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type)),
                ),
                Val::builtin(Builtin::Bool, Val::Type),
            ))
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
            let tty = ty.clone().quote(mcxt.size, mcxt, db);
            Ok((cond.make_if(yes, no, tty), ty))
        }

        Pre_::Var(name) => {
            // If its name is `_`, it's a hole
            if &db.lookup_intern_name(*name) == "_" {
                return infer(
                    insert,
                    &pre.copy_span(Pre_::Hole(MetaSource::Hole)),
                    db,
                    mcxt,
                );
            }

            let (term, ty) = match mcxt.lookup(*name, db) {
                Ok((v, ty)) => Ok((
                    Term::Var(v, Box::new(ty.clone().quote(mcxt.size, mcxt, db))),
                    ty,
                )),
                // If something else had a type error, try to keep going anyway and maybe catch more
                Err(DefError::ElabError) => Err(TypeError::Sentinel),
                Err(DefError::NoValue) => Err(TypeError::NotFound(pre.copy_span(*name))),
            }?;
            Ok(insert_metas(insert, term, ty, pre.span(), mcxt, db))
        }

        Pre_::Lam(name, icit, ty, body) => {
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt, db);
            // TODO Rc to get rid of the clone()?
            mcxt.define(*name, NameInfo::Local(vty.clone()), db);
            mcxt.eff_stack.push_scope(true, pre.span());

            let (body, bty) = infer(true, body, db, mcxt)?;
            let effs = mcxt.eff_stack.pop_scope();

            mcxt.undef(db);

            let effs_t = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt, db))
                .collect();
            Ok((
                Term::Clos(Lam, *name, *icit, Box::new(ty), Box::new(body), effs_t),
                Val::Clos(
                    Pi,
                    *icit,
                    // `inc()` since we're wrapping it in a lambda
                    Box::new(Clos {
                        env: mcxt.env(),
                        ty: vty,
                        term: bty.quote(mcxt.size.inc(), mcxt, db),
                        name: *name,
                    }),
                    effs,
                ),
            ))
        }

        Pre_::Pi(name, icit, ty, ret, effs) => {
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            // TODO Rc to get rid of the clone()?
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt, db);
            mcxt.define(*name, NameInfo::Local(vty), db);
            let ret = check(ret, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            mcxt.undef(db);

            let effs = effs
                .iter()
                .map(|x| {
                    check(
                        x,
                        &Val::builtin(Builtin::Eff, Val::Type),
                        ReasonExpected::UsedInWith,
                        db,
                        mcxt,
                    )
                })
                .collect::<Result<_, _>>()?;

            Ok((
                Term::Clos(Pi, *name, *icit, Box::new(ty), Box::new(ret), effs),
                Val::Type,
            ))
        }

        Pre_::Fun(from, to, effs) => {
            let from = check(from, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;
            let to = check(to, &Val::Type, ReasonExpected::UsedAsType, db, mcxt)?;

            let effs = effs
                .iter()
                .map(|x| {
                    check(
                        x,
                        &Val::builtin(Builtin::Eff, Val::Type),
                        ReasonExpected::UsedInWith,
                        db,
                        mcxt,
                    )
                })
                .collect::<Result<_, _>>()?;

            Ok((Term::Fun(Box::new(from), Box::new(to), effs), Val::Type))
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
            let mut block = mcxt.elab_block(v.clone(), false, db)?;

            // Now query the last expression
            let mut ret_ty = None;
            let mut state = mcxt.state();
            if let Some(&last) = block.last() {
                let (pre_id, state2) = db.lookup_intern_def(last);
                state = state2;
                // If it's not an expression, don't return anything
                if let PreDef::Expr(_) = &**db.lookup_intern_predef(pre_id) {
                    if let Ok(info) = db.elaborate_def(last) {
                        ret_ty = Some((*info.typ).clone());
                    } else {
                        // If there was a type error inside the block, we'll leave it, we don't want a cascade of errors
                        return Err(TypeError::Sentinel);
                    }
                }
            }
            let ret_ty = match ret_ty {
                Some(ty) => ty,
                None => {
                    let predef = db.intern_predef(Arc::new(PreDefAn::from(PreDef::Expr(
                        pre.copy_span(Pre_::Unit),
                    ))));
                    let unit_def = db.intern_def(predef, state);
                    block.push(unit_def);
                    Val::builtin(Builtin::UnitType, Val::Type)
                }
            };
            let block = block
                .into_iter()
                .filter_map(|id| Some((id, (*db.elaborate_def(id).ok()?.term).clone())))
                .collect();
            Ok((Term::Do(block), ret_ty))
        }

        Pre_::Sig(v) => {
            let block = mcxt.elab_block(v.clone(), true, db)?;
            let struct_block: Vec<_> = block
                .into_iter()
                .filter_map(|id| {
                    let info = db.elaborate_def(id).ok()?;
                    let (pre, _) = db.lookup_intern_def(id);
                    let name = db.lookup_intern_predef(pre).name().unwrap();
                    Some((name, (*info.term).clone()))
                })
                .collect();
            Ok((Term::Struct(StructKind::Sig, struct_block), Val::Type))
        }
        Pre_::Struct(v) => {
            let block = mcxt.elab_block(v.clone(), false, db)?;
            let (struct_block, sig_block) = block
                .into_iter()
                .filter_map(|id| {
                    let info = db.elaborate_def(id).ok()?;
                    let (pre, _) = db.lookup_intern_def(id);
                    let name = db.lookup_intern_predef(pre).name().unwrap();
                    let ty = (*info.typ).clone().quote(mcxt.size, mcxt, db);
                    Some(((name, (*info.term).clone()), (name, ty)))
                })
                .unzip();
            let ty = Term::Struct(StructKind::Sig, sig_block);
            let term = Term::Struct(StructKind::Struct(Box::new(ty.clone())), struct_block);
            let vty = ty.evaluate(&mcxt.env(), mcxt, db);
            Ok((term, vty))
        }
        Pre_::StructShort(_) => todo!("elaborate short-form struct"),

        Pre_::Hole(source) => {
            let ty = mcxt.new_meta(None, pre.span(), MetaSource::HoleType, Term::Type, db);
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt, db);
            Ok((mcxt.new_meta(None, pre.span(), *source, ty, db), vty))
        }

        Pre_::Dot(head, m, args) => {
            match infer(false, head, db, mcxt)
                .map(|(x, ty)| (x.inline_top(db), ty.inline(mcxt.size, db, mcxt)))?
            {
                (s, Val::Struct(StructKind::Sig, v)) => match v.iter().find(|&&(n, _)| n == **m) {
                    Some((_, ty)) => Ok((Term::Dot(Box::new(s), **m), ty.clone())),
                    None => Err(TypeError::MemberNotFound(
                        Span(head.span().0, m.span().1),
                        ScopeType::Struct,
                        **m,
                    )),
                },
                (Term::Var(Var::Builtin(Builtin::Bool), _), _) => {
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
                (Term::Var(Var::Type(id, scope), _), _) => {
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
                                Err(_) => return Err(TypeError::Sentinel),
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

        Pre_::Case(is_catch, x, cases) => {
            let xspan = x.span();
            let (x, x_ty, x_effs) = if *is_catch {
                mcxt.eff_stack.push_scope(true, xspan);
                let (x, x_ty) = infer(true, x, db, mcxt)?;
                let mut x_effs = mcxt.eff_stack.pop_scope();
                let before_len = x_effs.len();
                x_effs.retain(|x| !matches!(x, Val::App(Var::Builtin(Builtin::IO), _, _, _)));
                if x_effs.len() != before_len {
                    // It had IO
                    if !mcxt.eff_stack.clone().try_eff(
                        Val::builtin(Builtin::IO, Val::builtin(Builtin::Eff, Val::Type)),
                        db,
                        mcxt,
                    ) {
                        return Err(TypeError::EffNotAllowed(
                            pre.span(),
                            Val::builtin(Builtin::IO, Val::builtin(Builtin::Eff, Val::Type)),
                            mcxt.eff_stack.clone(),
                        ));
                    }
                }
                (x, x_ty, x_effs)
            } else {
                let (x, x_ty) = infer(true, x, db, mcxt)?;
                (x, x_ty, Vec::new())
            };
            if *is_catch && x_effs.is_empty() {
                return Err(TypeError::WrongCatchType(xspan, false));
            }
            crate::pattern::elab_case(
                x,
                xspan,
                x_ty,
                x_effs,
                ReasonExpected::MustMatch(xspan),
                cases,
                None,
                mcxt,
                db,
            )
        }

        Pre_::OrPat(_, _) => unreachable!("| is only allowed in patterns"),
        Pre_::EffPat(_, _) => unreachable!("eff _ _ is only allowed in patterns"),
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
    let fty = fty.inline(mcxt.size, db, mcxt);
    let (term, ty) = match &fty {
        Val::Clos(Pi, icit2, cl, effs) => {
            assert_eq!(icit, *icit2);

            let span = Span(fspan.0, x.span().1);
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
            for eff in effs {
                if !mcxt.eff_stack.try_eff(eff.clone(), db, &mut mcxt.clone()) {
                    return Err(TypeError::EffNotAllowed(
                        span,
                        eff.clone(),
                        mcxt.eff_stack.clone(),
                    ));
                }
            }
            Ok((Term::App(icit, Box::new(f), Box::new(x)), to))
        }
        Val::Fun(from, to, effs) => {
            let span = Span(fspan.0, x.span().1);
            let x = check(
                x,
                &from,
                ReasonExpected::ArgOf(fspan, fty.clone()),
                db,
                mcxt,
            )?;
            let to = (**to).clone();
            for eff in effs {
                if !mcxt.eff_stack.try_eff(eff.clone(), db, &mut mcxt.clone()) {
                    return Err(TypeError::EffNotAllowed(
                        span,
                        eff.clone(),
                        mcxt.eff_stack.clone(),
                    ));
                }
            }
            Ok((Term::App(icit, Box::new(f), Box::new(x)), to))
        }
        _ => {
            if let (Icit::Expl, Term::Var(Var::Type(_, sid), _)) =
                (icit, f.head().clone().inline_top(db))
            {
                let scope = db.lookup_intern_scope(sid);
                let m = db.intern_name(String::new());
                for &(n, v) in scope.iter() {
                    if n == m {
                        match db.elaborate_def(v) {
                            Ok(info) => {
                                let mut fty = IntoOwned::<Val>::into_owned(info.typ)
                                    .quote(mcxt.size, mcxt, db);
                                let mut f2 = Term::Var(Var::Top(v), Box::new(fty.clone()));
                                let mut f = f;
                                // Apply the constructor to all the type arguments
                                loop {
                                    match f {
                                        Term::App(i, f3, x) => {
                                            f2 = Term::App(i, Box::new(f2), x.clone());
                                            match fty {
                                                Term::Clos(Pi, _, _, _, to, _) => {
                                                    // Peel off one Pi to get the type of the next `f`.
                                                    // It's dependent, so we need to add `x` to the environment.
                                                    let mut env = mcxt.env();
                                                    let x = x.evaluate(&env, mcxt, db);
                                                    env.push(Some(x));
                                                    // Then we evaluate-quote to so `fty` is in the context `enclosing`.
                                                    fty = (*to)
                                                        .clone()
                                                        .eval_quote(&mut env, mcxt.size, mcxt, db)
                                                }
                                                _ => unreachable!(),
                                            };
                                            f = *f3;
                                        }
                                        _ => break,
                                    }
                                }
                                let fty = fty.evaluate(&mcxt.env(), mcxt, db);

                                return infer_app(f2, fty, fspan, icit, x, db, mcxt);
                            }
                            Err(_) => return Err(TypeError::Sentinel),
                        }
                    }
                }
            }

            if let Term::App(_, _, _) = &f {
                let hty = f
                    .head()
                    .ty(mcxt.size, mcxt, db)
                    .evaluate(&mcxt.env(), mcxt, db);
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

        // When checking () against Type, we know it's refering to the unit type
        (Pre_::Unit, Val::Type) => Ok(Term::Var(
            Var::Builtin(Builtin::UnitType),
            Box::new(Term::Type),
        )),

        (Pre_::Lam(n, i, ty, body), Val::Clos(Pi, i2, cl, effs)) if i == i2 => {
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
            let bty = (**cl)
                .clone()
                .apply(Val::local(mcxt.size.next_lvl(), vty.clone()), mcxt, db);

            mcxt.define(*n, NameInfo::Local(vty), db);

            // TODO not clone ??
            let (body, _bty, effs) = check_fun(body, bty, reason, effs.clone(), false, db, mcxt)?;

            mcxt.undef(db);
            let effs = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt, db))
                .collect();
            Ok(Term::Clos(Lam, *n, *i, Box::new(ety), Box::new(body), effs))
        }

        (Pre_::Lam(n, Icit::Expl, ty, body), Val::Fun(ty2, body_ty, effs)) => {
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
            let (body, _bty, effs) = check_fun(
                body,
                (**body_ty).clone(),
                reason,
                effs.clone(),
                false,
                db,
                mcxt,
            )?;
            mcxt.undef(db);

            let effs = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt, db))
                .collect();
            Ok(Term::Clos(
                Lam,
                *n,
                Icit::Expl,
                Box::new(ety),
                Box::new(body),
                effs,
            ))
        }

        // We implicitly insert lambdas so `\x.x : [a] -> a -> a` typechecks
        // // If we didn't have the restriction that the term must be a lambda, then it would allow something like Swift's `autoclosure`
        // // So if we want that in the future, it would be very easy to implement
        // // (Pre_::Lam(_, Icit::Expl, _, _), Val::Pi(Icit::Impl, cl, effs)) => {
        // For now, we have that restriction turned off so that `val _ : [a] a -> a = id id` typechecks.
        // TODO figure out how to make that typecheck without allowing unrestricted autoclosures.
        (_, Val::Clos(Pi, Icit::Impl, cl, effs)) => {
            // Add a ' after the name so it doesn't shadow names the term defined (' isn't valid in Pika identifiers)
            let name = {
                let mut s = cl.name.get(db);
                s.push('\'');
                db.intern_name(s)
            };
            let bty = (**cl).clone().vquote(mcxt.size, mcxt, db);
            mcxt.define(name, NameInfo::Local(cl.ty.clone()), db);
            let (body, _bty, effs) = check_fun(pre, bty, reason, effs.clone(), false, db, mcxt)?;
            mcxt.undef(db);

            let ty = cl.ty.clone().quote(mcxt.size, mcxt, db);
            let effs = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt, db))
                .collect();
            Ok(Term::Clos(
                Lam,
                cl.name,
                Icit::Impl,
                Box::new(ty),
                Box::new(body),
                effs,
            ))
        }

        // If it's an op like `+` or `*`, the arguments will have the same type as the return type
        // But make sure to fall through to `infer` if it's something like `!=`
        (Pre_::BinOp(op, a, b), _) if op.returns_arg_ty() => {
            let ity = match ty {
                Val::App(Var::Builtin(b), _, _, _) => match *b {
                    Builtin::I32 => Term::Var(Var::Builtin(Builtin::I32), Box::new(Term::Type)),
                    Builtin::I64 => Term::Var(Var::Builtin(Builtin::I64), Box::new(Term::Type)),
                    Builtin::F32 => Term::Var(Var::Builtin(Builtin::F32), Box::new(Term::Type)),
                    Builtin::F64 => Term::Var(Var::Builtin(Builtin::F64), Box::new(Term::Type)),
                    _ => return Err(TypeError::BinOpType(a.span(), ty.clone(), op.span())),
                },
                _ => return Err(TypeError::BinOpType(a.span(), ty.clone(), op.span())),
            };
            let a = check(a, ty, reason.clone(), db, mcxt)?;
            let b = check(b, ty, reason, db, mcxt)?;
            let fty = Term::Fun(
                Box::new(ity.clone()),
                Box::new(Term::Fun(
                    Box::new(ity.clone()),
                    Box::new(ity.clone()),
                    Vec::new(),
                )),
                Vec::new(),
            );
            let f = Term::Var(Var::Builtin(Builtin::BinOp(**op)), Box::new(fty));
            Ok(Term::App(
                Icit::Expl,
                Box::new(Term::App(Icit::Expl, Box::new(f), Box::new(a))),
                Box::new(b),
            ))
        }

        (Pre_::Lit(l), _)
            if matches!(
                l,
                Literal::Positive(_) | Literal::Negative(_) | Literal::Float(_)
            ) =>
        {
            match ty.clone().inline(mcxt.size, db, mcxt) {
                Val::App(Var::Builtin(b @ Builtin::I32), _, _, _) => {
                    match l {
                        Literal::Positive(i) => {
                            if *i > i32::MAX as u64 {
                                return Err(TypeError::InvalidLiteral(pre.span(), *l, b));
                            }
                        }
                        Literal::Negative(i) => {
                            if *i < i32::MIN as i64 {
                                return Err(TypeError::InvalidLiteral(pre.span(), *l, b));
                            }
                        }
                        _ => return Err(TypeError::InvalidLiteral(pre.span(), *l, b)),
                    }
                    Ok(Term::Lit(*l, b))
                }
                Val::App(Var::Builtin(b @ Builtin::I64), _, _, _) => {
                    match l {
                        Literal::Positive(i) => {
                            if *i > i64::MAX as u64 {
                                return Err(TypeError::InvalidLiteral(pre.span(), *l, b));
                            }
                        }
                        Literal::Negative(_) => (),
                        _ => return Err(TypeError::InvalidLiteral(pre.span(), *l, b)),
                    }
                    Ok(Term::Lit(*l, b))
                }
                Val::App(Var::Builtin(b @ Builtin::F32), _, _, _)
                | Val::App(Var::Builtin(b @ Builtin::F64), _, _, _) => {
                    let l = match l {
                        Literal::Float(_) => *l,
                        Literal::Positive(i) => Literal::Float((*i as f64).to_bits()),
                        Literal::Negative(i) => Literal::Float((*i as f64).to_bits()),
                        _ => return Err(TypeError::InvalidLiteral(pre.span(), *l, b)),
                    };
                    Ok(Term::Lit(l, b))
                }
                Val::App(Var::Meta(_), _, _, _) => Err(TypeError::UntypedLiteral(pre.span())),
                ty => Err(TypeError::NotIntType(
                    pre.span(),
                    ty.inline_metas(mcxt.size, mcxt, db),
                    reason,
                )),
            }
        }

        (Pre_::Case(is_catch, x, cases), _) => {
            let xspan = x.span();
            let (x, x_ty, x_effs) = if *is_catch {
                mcxt.eff_stack.push_scope(true, xspan);
                let (x, x_ty) = infer(true, x, db, mcxt)?;
                let mut x_effs = mcxt.eff_stack.pop_scope();
                let before_len = x_effs.len();
                x_effs.retain(|x| !matches!(x, Val::App(Var::Builtin(Builtin::IO), _, _, _)));
                if x_effs.len() != before_len {
                    // It had IO
                    if !mcxt.eff_stack.clone().try_eff(
                        Val::builtin(Builtin::IO, Val::builtin(Builtin::Eff, Val::Type)),
                        db,
                        mcxt,
                    ) {
                        return Err(TypeError::EffNotAllowed(
                            pre.span(),
                            Val::builtin(Builtin::IO, Val::builtin(Builtin::Eff, Val::Type)),
                            mcxt.eff_stack.clone(),
                        ));
                    }
                }
                (x, x_ty, x_effs)
            } else {
                let (x, x_ty) = infer(true, x, db, mcxt)?;
                (x, x_ty, Vec::new())
            };
            if *is_catch && x_effs.is_empty() {
                return Err(TypeError::WrongCatchType(xspan, false));
            }
            crate::pattern::elab_case(
                x,
                xspan,
                x_ty,
                x_effs,
                ReasonExpected::MustMatch(xspan),
                cases,
                Some((ty.clone(), reason)),
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
            let tty = ty.clone().quote(mcxt.size, mcxt, db);
            Ok(cond.make_if(yes, no, tty))
        }

        (Pre_::Struct(v), Val::Struct(StructKind::Sig, v2)) => {
            if v.len() != v2.len() {
                let err = Error::new(
                    mcxt.cxt.file(db),
                    format!(
                        "Wrong number of record members, got {}, expected {} because of type",
                        v.len(),
                        v2.len(),
                    ),
                    pre.span(),
                    format!("expected {} record members here", v2.len()),
                );
                let err = reason.add(err, mcxt.cxt.file(db), db, mcxt);
                db.report_error(err);
                return Err(TypeError::Sentinel);
            }
            let block = mcxt.elab_block(
                v.iter()
                    .zip(v2)
                    .map(|(d, (n, ty))| {
                        if d.name() != Some(*n) {
                            db.report_error(
                                Error::new(
                                    mcxt.cxt.file(db),
                                    format!(
                                        "Wrong name of record member, got {}, expected {} because of type",
                                        d.name().unwrap().get(db),
                                        n.get(db),
                                    ),
                                    pre.span(),
                                    "wrong name",
                                )
                                .with_note(
                                    "currently out-of-order record definitions aren't allowed",
                                ),
                            );
                            return Err(TypeError::Sentinel);
                        }
                        Ok(PreDef::Typed(Box::new(d.clone()), ty.clone(), reason.clone()).into())
                    })
                    .collect::<Result<_, _>>()?,
                false,
                db,
            )?;
            let (struct_block, sig_block) = block
                .into_iter()
                .filter_map(|id| {
                    let info = db.elaborate_def(id).ok()?;
                    let (pre, _) = db.lookup_intern_def(id);
                    let name = db.lookup_intern_predef(pre).name().unwrap();
                    let ty = (*info.typ).clone().quote(mcxt.size, mcxt, db);
                    Some(((name, (*info.term).clone()), (name, ty)))
                })
                .unzip();
            let ty = Term::Struct(StructKind::Sig, sig_block);
            let term = Term::Struct(StructKind::Struct(Box::new(ty.clone())), struct_block);
            Ok(term)
        }
        _ => {
            if let Val::App(h, _, sp, g) = ty {
                if let Some(v) = g.resolve(*h, sp, mcxt.size, db, mcxt) {
                    return check(pre, &v, reason, db, mcxt);
                }
            }

            let (term, mut i_ty) = infer(true, pre, db, mcxt)?;

            match (ty, &mut i_ty) {
                (Val::Fun(_, _, effs), Val::Fun(_, _, effs2))
                | (Val::Clos(Pi, _, _, effs), Val::Fun(_, _, effs2))
                | (Val::Fun(_, _, effs), Val::Clos(Pi, _, _, effs2))
                | (Val::Clos(Pi, _, _, effs), Val::Clos(Pi, _, _, effs2))
                    if effs.len() < effs2.len() =>
                {
                    // Capture ambient effects - implicit effect polymorphism
                    let mut effs3 = Vec::new();
                    let mut tcxt = mcxt.clone();
                    for e in effs2.take() {
                        let mut found = false;
                        for i in effs {
                            if unify(
                                e.clone(),
                                i.clone(),
                                tcxt.size,
                                Span::empty(),
                                db,
                                &mut tcxt,
                            )
                            .unwrap_or(false)
                            {
                                found = true;
                                break;
                            }
                        }
                        if found {
                            effs3.push(e);
                        } else {
                            if !mcxt.eff_stack.clone().try_eff(e.clone(), db, mcxt) {
                                return Err(TypeError::EffNotAllowed(
                                    pre.span(),
                                    e,
                                    mcxt.eff_stack.clone(),
                                ));
                            }
                        }
                    }
                    *effs2 = effs3;
                }
                (_, _) => (),
            };

            try_unify(ty, &i_ty, Some(&term), pre.span(), reason, mcxt, db)?;
            Ok(term)
        }
    }
}

fn check_fun(
    body: &Pre,
    rty: VTy,
    reason: ReasonExpected,
    effs: Vec<Val>,
    open: bool,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<(Term, VTy, Vec<Val>), TypeError> {
    let span = reason.span_or(body.span());
    mcxt.eff_stack.push_scope(open, span);
    for e in effs {
        mcxt.eff_stack.push_eff(e.clone());
    }
    let term = check(body, &rty, reason, db, mcxt)?;
    let effs = mcxt.eff_stack.pop_scope();
    Ok((term, rty, effs))
}
