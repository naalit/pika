use super::{unify, ReasonExpected, TypeError};
use crate::common::*;
use crate::term::{ClosTy::*, Env, Ix, Lvl, Meta, MetaSource, Names, PreDefAn, Spine, StructKind};

#[derive(Debug, Clone, PartialEq)]
pub enum MetaEntry {
    Solved(Arc<Term>, FileSpan),
    Unsolved(Option<Name>, VTy, Span, MetaSource, Spine),
}

#[derive(Debug, Clone, PartialEq, Default, Eq, Hash)]
pub struct ImplStack(Vec<Vec<(Option<Name>, VTy, Val, Span)>>);
impl ImplStack {
    pub fn scope(&mut self) {
        self.0.push(Vec::new());
    }

    pub fn add(&mut self, name: Option<Name>, ty: VTy, val: Val, span: Span) {
        if self.0.is_empty() {
            self.scope();
        }
        self.0.last_mut().unwrap().push((name, ty, val, span));
    }
}
impl<'db> MCxt<'db> {
    pub fn find_impl(&mut self, ty: &VTy, span: Span) -> Option<Val> {
        for scope in self.impls.0.iter().rev() {
            let mut found = Vec::new();
            let mut metas = None;
            for (iname, ity, ival, ispan) in scope {
                let mut mcxt2 = self.clone();
                if unify(
                    ty.clone(),
                    ity.clone(),
                    self.size,
                    Span::empty(),
                    &mut mcxt2,
                )
                .unwrap_or(false)
                {
                    found.push((ival.clone(), iname.clone(), *ispan));
                    // If unifying the types solved any metas, make sure to save the solutions
                    metas = Some((mcxt2.local_metas, mcxt2.solved_globals));
                }
            }
            match found.len() {
                0 => continue,
                1 => {
                    let (local, global) = metas.unwrap();
                    self.local_metas = local;
                    self.solved_globals = global;
                    return Some(found.pop().unwrap().0);
                }
                _ => {
                    let file = self.cxt.file(self.db);
                    let mut err = Error::new(
                        file,
                        "Multiple solutions found for implicit in the same scope",
                        span,
                        "search started here",
                    );
                    for (_, n, s) in found {
                        err = err.with_label(
                            file,
                            s,
                            if let Some(n) = n {
                                format!("candidate '{}' found here", n.get(self.db))
                            } else {
                                "candidate found here".to_string()
                            },
                        );
                    }
                    self.db.report_error(err);
                    return None;
                }
            }
        }
        None
    }
}
/// The context used for typechecking a term.
/// Besides storing a `Cxt` for name resolution, stores meta solutions and local constraints, and a handle to the database.
#[derive(Clone)]
pub struct MCxt<'db> {
    pub db: &'db dyn Compiler,
    pub cxt: Cxt,
    pub size: Size,
    pub eff_stack: EffStack,
    pub is_sig: bool,
    pub ty: MCxtType,
    pub impls: ImplStack,
    pub local_metas: Vec<MetaEntry>,
    pub local_defs: Vec<(DefId, Term)>,
    pub local_constraints: HashMap<Lvl, Val>,
    pub solved_globals: Vec<RecSolution>,
    pub children: Vec<DefId>,
}
impl<'db> MCxt<'db> {
    pub fn state(&self) -> CxtState {
        CxtState {
            cxt: self.cxt,
            size: self.size,
            impls: self.impls.clone(),
            local_constraints: self.local_constraints.clone(),
            local_defs: self.local_defs.clone(),
            eff_stack: self.eff_stack.clone(),
            is_sig: false,
        }
    }
    pub fn set_state(&mut self, state: CxtState) {
        let CxtState {
            cxt,
            size,
            local_constraints,
            local_defs,
            impls,
            eff_stack,
            is_sig,
        } = state;
        self.cxt = cxt;
        self.size = size;
        self.local_constraints = local_constraints;
        self.local_defs = local_defs;
        self.eff_stack = eff_stack;
        self.is_sig = is_sig;
        self.impls = impls;
    }

    pub fn new(cxt: Cxt, ty: MCxtType, db: &'db dyn Compiler) -> Self {
        MCxt {
            db,
            cxt,
            size: cxt.size(db),
            eff_stack: Default::default(),
            impls: Default::default(),
            ty,
            local_metas: Vec::new(),
            local_defs: Vec::new(),
            local_constraints: HashMap::new(),
            solved_globals: Vec::new(),
            children: Vec::new(),
            is_sig: false,
        }
    }

    pub fn empty_universal(db: &'db dyn Compiler) -> Self {
        MCxt {
            db,
            cxt: Cxt::new(0, db),
            size: Size::zero(),
            eff_stack: Default::default(),
            ty: MCxtType::Universal,
            impls: Default::default(),
            local_metas: Vec::new(),
            local_defs: Vec::new(),
            local_constraints: HashMap::new(),
            solved_globals: Vec::new(),
            children: Vec::new(),
            is_sig: false,
        }
    }

    pub fn from_state(state: CxtState, ty: MCxtType, db: &'db dyn Compiler) -> Self {
        let CxtState {
            cxt,
            size,
            local_constraints,
            local_defs,
            eff_stack,
            impls,
            is_sig,
        } = state;
        MCxt {
            db,
            cxt,
            size,
            eff_stack,
            ty,
            impls,
            local_metas: Vec::new(),
            local_constraints,
            local_defs,
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
    pub fn local_name(&self, mut ix: Ix) -> Name {
        let mut cxt = self.cxt;
        loop {
            match self.db.lookup_cxt_entry(cxt) {
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
    pub fn local_ty(&self, mut ix: Ix) -> VTy {
        let mut cxt = self.cxt;
        loop {
            match self.db.lookup_cxt_entry(cxt) {
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
    pub fn lookup(&self, name: Name) -> Result<(Var<Ix>, VTy), DefError> {
        self.cxt.lookup(name, self.db)
    }

    pub fn last_local(&self) -> Option<(Var<Lvl>, VTy)> {
        let mut cxt = self.cxt;
        loop {
            match self.db.lookup_cxt_entry(cxt) {
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
    pub fn define(&mut self, name: Name, info: NameInfo) {
        if let NameInfo::Local(_) = &info {
            self.size = self.size.inc();
        }
        self.cxt = self.cxt.define(name, info, self.db);
        debug_assert_eq!(self.size, self.cxt.size(self.db));
    }

    /// Looks up the solution to the given meta, if one exists.
    pub fn get_meta(&self, meta: Meta) -> Option<Term> {
        match meta {
            Meta::Global(id, n, _) => self
                .solved_globals
                .iter()
                .find(|s| s.id() == Some(id) && s.num() == n)
                .map(|s| s.term().clone()),
            Meta::Local(def, num, _) => {
                if let MCxtType::Local(d) = self.ty {
                    if def == d {
                        return match &self.local_metas[num as usize] {
                            MetaEntry::Solved(v, _) => Some((**v).clone()), //.map(|x| x.inline_metas(self)),
                            MetaEntry::Unsolved(_, _, _, _, _) => None,
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

    pub fn meta_span(&self, meta: Meta) -> Option<FileSpan> {
        match meta {
            Meta::Global(id, n, _) => self
                .solved_globals
                .iter()
                .find(|s| s.id() == Some(id) && s.num() == n)
                .map(|s| s.span()),
            Meta::Local(def, num, _) => {
                if let MCxtType::Local(d) = self.ty {
                    if def == d {
                        return match &self.local_metas[num as usize] {
                            MetaEntry::Solved(_, s) => Some(*s),
                            MetaEntry::Unsolved(_, _, _, _, _) => None,
                        };
                    }
                }
                self.solved_globals.iter().find_map(|s| match s {
                    RecSolution::ParentLocal(d, n, s, _) if *d == def && *n == num => Some(*s),
                    _ => None,
                })
            }
        }
    }

    /// Undoes the last call to `define()`.
    pub fn undef(&mut self) {
        self.cxt = match self.db.lookup_cxt_entry(self.cxt) {
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
        debug_assert_eq!(self.size, self.cxt.size(self.db));
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
        size: Size,
    ) -> Result<(), TypeError> {
        // The value can only use variables that we're passing to the meta
        let mut meta_scope = spine
            .iter()
            // Each argument is another lambda we're going to wrap it in
            .zip(std::iter::successors(Some(size.next_lvl()), |lvl| {
                Some(lvl.inc())
            }))
            .map(|(e, to_lvl)| match e.assert_app().1.unarc() {
                Val::App(Var::Local(from_lvl), _, sp, _) if sp.is_empty() => {
                    Ok((*from_lvl, to_lvl))
                }
                x => Err(TypeError::MetaSpine(span, Var::Meta(meta), x.clone())),
            })
            .collect::<Result<Rename, _>>()?;
        let term = val.quote(size, self);
        // The level it will be at after we wrap it in lambdas
        let to_lvl = (0..spine.len()).fold(size, |x, _| x.inc());

        // Get the type of each argument
        let tys: Vec<Ty> = spine
            .iter()
            .zip(std::iter::successors(Some(size), |size| Some(size.inc())))
            .map(|(e, l)| match e.assert_app().1.unarc() {
                Val::App(Var::Local(_), ty, sp, _) if sp.is_empty() => {
                    let mut names = Names::new(self.cxt, self.db);
                    while names.size() != l {
                        // TODO actual names?
                        names.add(names.hole_name());
                    }
                    (**ty).clone().quote(l, self).check_solution(
                        Spanned::new(Var::Meta(meta), span),
                        &mut meta_scope,
                        l,
                        l,
                        &mut Names::new(self.cxt, self.db),
                    )
                }
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect::<Result<_, _>>()?;

        let term = term.check_solution(
            Spanned::new(Var::Meta(meta), span),
            &mut meta_scope,
            size,
            to_lvl,
            &mut Names::new(self.cxt, self.db),
        )?;
        // Actually wrap it in lambdas
        // We could look up the local variables' names in the cxt, but it's probably not worth it
        let empty_name = self.db.intern_name("_".to_string());
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
        let span = FileSpan::new(self.cxt.file(self.db), span);
        match meta {
            Meta::Global(id, n, source) => {
                self.solved_globals
                    .push(RecSolution::Global(id, n, span, term, source));
            }
            Meta::Local(def, idx, _) => {
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
    pub fn new_meta(&mut self, name: Option<Name>, span: Span, source: MetaSource, ty: Ty) -> Term {
        use std::convert::TryInto;

        let meta = match self.ty {
            MCxtType::Local(def) => Meta::Local(
                def,
                self.local_metas
                    .len()
                    .try_into()
                    .expect("Only 65535 metas allowed per definition"),
                source,
            ),
            MCxtType::Global(def) => Meta::Global(
                def,
                self.local_metas
                    .len()
                    .try_into()
                    .expect("Only 65535 metas allowed per definition"),
                source,
            ),
            MCxtType::Universal => panic!("a Universal MCxt can't create a meta!"),
        };
        self.local_metas.push(MetaEntry::Unsolved(
            name,
            ty.clone().evaluate(&self.env(), self),
            span,
            source,
            self.size.meta_spine(self),
        ));

        // Apply it to all the bound variables in scope
        self.size.apply_meta(Var::Meta(meta), ty, self)
    }

    /// Makes sure all local metas are solved.
    /// If some aren't, it reports errors to `db` and returns Err(()).
    pub fn check_locals(&mut self) -> Result<(), ()> {
        if let MCxtType::Local(id) = self.ty {
            let mut ret = Ok(());
            for i in 0..self.local_metas.len() {
                match &self.local_metas[i] {
                    MetaEntry::Solved(_, _) => (),
                    MetaEntry::Unsolved(_, ty, span, source, spine) => {
                        // Copy everything so we can modify `self` in `find_impl()`
                        let (&span, &source) = (span, source);
                        let ty = ty.clone();
                        let spine = spine.clone();

                        if matches!(source, MetaSource::ImplicitParam(_) | MetaSource::Hole) {
                            if let Some(val) = self.find_impl(&ty, span) {
                                self.solve(
                                    span,
                                    Meta::Local(id, i as u16, source),
                                    &spine,
                                    val,
                                    self.size,
                                )
                                .map_err(|x| self.db.maybe_report_error(x.into_error(0, self)))?;
                                continue;
                            }
                        }

                        self.db.report_error(Error::new(
                            self.cxt.file(self.db),
                            Doc::start("Could not find solution for ")
                                .chain(source.pretty(self.db))
                                .add(" of type ")
                                .chain(ty.pretty(self).style(Style::None))
                                .style(Style::Bold),
                            span,
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

    pub fn def_term(&self, def: DefId) -> Option<Term> {
        if let Some(t) = self
            .local_defs
            .iter()
            .rev()
            .find(|(d, _)| *d == def)
            .map(|(_, t)| t)
        {
            return Some(t.clone());
        }
        match self.db.elaborate_def(def) {
            Ok(info) => info.term.map(|x| (*x).clone()),
            Err(_) => None,
        }
    }

    pub fn elab_block(&mut self, v: Vec<PreDefAn>, is_sig: bool) -> Result<Vec<DefId>, TypeError> {
        self.elab_block_with(v.into_iter().map(|x| (x, None)), is_sig)
    }

    pub fn elab_block_with(
        &mut self,
        v: impl IntoIterator<Item = (PreDefAn, Option<(DefId, Term)>)>,
        is_sig: bool,
    ) -> Result<Vec<DefId>, TypeError> {
        let mut state = self.state();
        state.is_sig = is_sig;
        let block = InternBlock::new(v.into_iter().collect(), state).intern(self.db);
        // Make sure any type errors get reported
        {
            let mut mcxt2 = self.clone();
            for &i in &block {
                if let Ok(info) = self.db.elaborate_def(i) {
                    for e in &*info.effects {
                        assert!(self.eff_stack.try_eff(e.clone(), &mut mcxt2));
                    }
                    for i in &*info.solved_globals {
                        match i {
                            RecSolution::ParentLocal(d, n, span, term)
                                if self.ty == MCxtType::Local(*d) =>
                            {
                                match &self.local_metas[*n as usize] {
                                    MetaEntry::Solved(t2, s2) => {
                                        let t2 = (**t2).clone().evaluate(&self.env(), self);
                                        let term = term.clone().evaluate(&self.env(), self);
                                        if !unify(
                                            t2.clone(),
                                            term.clone(),
                                            self.size,
                                            span.span,
                                            &mut mcxt2,
                                        )? {
                                            self.db.maybe_report_error(
                                                TypeError::Unify(
                                                    Spanned::new(term, span.span),
                                                    t2,
                                                    ReasonExpected::MustMatch(s2.span),
                                                )
                                                .into_error(self.cxt.file(self.db), self),
                                            );
                                        }
                                    }
                                    MetaEntry::Unsolved(_, _, _, _, _) => {
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
                    Var::Rec(id) if matches!(*meta, Var::Meta(Meta::Global(id2, _, _)) if id2 == id) =>
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
            Term::Box(b, mut x) => {
                *x = x.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::Box(b, x))
            }
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
                    .map(|(d, n, t)| {
                        t.check_solution(meta.clone(), ren, lfrom, lto, names)
                            .map(|t| (d, n, t))
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
    pub local_defs: Vec<(DefId, Term)>,
    pub impls: ImplStack,
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
            local_defs: Default::default(),
            eff_stack: Default::default(),
            impls: Default::default(),
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
    Universal,
}

#[derive(Debug, Clone, PartialEq, Default, Eq, Hash)]
pub struct EffStack {
    pub effs: Vec<Val>,
    pub scopes: Vec<(bool, usize, Span)>,
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
    pub fn find_eff(&self, eff: &Val, mcxt: &mut MCxt) -> Option<usize> {
        let mut mcxt = mcxt.clone();
        let start = self.scopes.last().map_or(0, |(_, l, _)| *l);
        for (i, e) in self.effs[start..].iter().enumerate() {
            if unify(eff.clone(), e.clone(), mcxt.size, Span::empty(), &mut mcxt).unwrap_or(false) {
                return Some(i);
            }
        }
        None
    }

    pub fn scope_start(&self) -> Option<usize> {
        self.scopes.last().map(|(_, len, _)| *len)
    }

    pub fn try_eff(&mut self, eff: Val, mcxt: &mut MCxt) -> bool {
        if self.find_eff(&eff, mcxt).is_some() {
            return true;
        }
        if self.scopes.last().map_or(false, |(open, _, _)| *open) {
            self.push_eff(eff);
            return true;
        }
        false
    }
}

impl Var<Lvl> {
    pub fn pretty_meta(self, mcxt: &MCxt) -> Doc {
        match self {
            Var::Meta(m) => m.source().pretty(mcxt.db),

            Var::Local(l) => Doc::start("constrained value of local ")
                .chain(Val::local(l, Val::Type).pretty(mcxt)),

            _ => unreachable!(),
        }
    }
}
impl MetaSource {
    pub fn pretty(self, db: &dyn Compiler) -> Doc {
        match self {
            MetaSource::ImplicitParam(n) => {
                Doc::start("implicit parameter '").add(n.get(db)).add("'")
            }
            MetaSource::LocalType(n) => Doc::start("type of '").add(n.get(db)).add("'"),
            MetaSource::Hole => Doc::start("hole"),
            MetaSource::HoleType => Doc::start("type of hole"),
        }
    }
}
