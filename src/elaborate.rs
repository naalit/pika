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
        meta: Spanned<Meta>,
        ren: &mut Rename,
        lfrom: Lvl,
        lto: Lvl,
        names: &mut Names,
    ) -> Result<Term, TypeError> {
        match self {
            Term::Var(v) => match v {
                Var::Meta(m) if m == *meta => Err(TypeError::MetaOccurs(meta.span(), *meta)),
                // We store the renamings as levels and go between here, since indices change inside lambdas but levels don't.
                Var::Local(ix) => match ren.get(&ix.to_lvl(lfrom)) {
                    Some(lvl) => Ok(Term::Var(Var::Local(lvl.to_ix(lto)))),
                    None => {
                        println!("wrong {:?} = {:?}", ix, ix.to_lvl(lfrom));
                        Err(TypeError::MetaScope(meta.span(), *meta, names.get(ix)))
                    }
                },
                // The type of something can't depend on its own value
                // TODO a different error for this case? Is this even possible?
                Var::Rec(id)
                    if (if let Meta::Type(id2) = *meta {
                        id2 == id
                    } else {
                        false
                    }) =>
                {
                    Err(TypeError::MetaOccurs(meta.span(), *meta))
                }
                v => Ok(Term::Var(v)),
            },
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
            Term::App(i, mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, lfrom, lto, names)?;
                *b = b.check_solution(meta, ren, lfrom, lto, names)?;
                Ok(Term::App(i, a, b))
            }
            Term::Error => Ok(Term::Error),
            Term::Type => Ok(Term::Type),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct CxtState {
    pub cxt: Cxt,
    pub size: Lvl,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MCxt {
    pub cxt: Cxt,
    pub size: Lvl,
    def: DefId,
    local_metas: Vec<MetaEntry>,
    solved_globals: Vec<RecSolution>,
}
impl MCxt {
    pub fn state(&self) -> CxtState {
        CxtState {
            cxt: self.cxt,
            size: self.size,
        }
    }
    pub fn set_state(&mut self, state: CxtState) {
        let CxtState { cxt, size } = state;
        self.cxt = cxt;
        self.size = size;
    }

    pub fn new(cxt: Cxt, def: DefId, db: &dyn Compiler) -> Self {
        MCxt {
            cxt,
            size: cxt.size(db),
            def,
            local_metas: Vec::new(),
            solved_globals: Vec::new(),
        }
    }

    pub fn local_ty(&self, mut ix: Ix, db: &dyn Compiler) -> VTy {
        let mut cxt = self.cxt;
        loop {
            match db.lookup_cxt_entry(cxt) {
                MaybeEntry::Yes(CxtEntry { rest, info, .. }) => {
                    cxt = rest;
                    match info {
                        NameInfo::Def(_) => continue,
                        NameInfo::Rec(_) => continue,
                        NameInfo::Local(ty) => {
                            if ix == Ix::zero() {
                                break ty;
                            } else {
                                ix = ix.dec();
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    pub fn lookup(&self, name: Name, db: &dyn Compiler) -> Option<NameResult> {
        self.cxt.lookup(name, db)
    }

    pub fn define(&mut self, name: Name, info: NameInfo, db: &dyn Compiler) {
        if let NameInfo::Local(_) = &info {
            self.size = self.size.inc();
        }
        self.cxt = self.cxt.define(name, info, db);
        debug_assert_eq!(self.size, self.cxt.size(db));
    }

    pub fn get_meta(&self, meta: Meta) -> Option<Val> {
        match meta {
            Meta::Type(id) => self
                .solved_globals
                .iter()
                .find(|s| s.id() == id)
                .map(|s| s.val().clone()),
            Meta::Local(def, num) => {
                assert_eq!(def, self.def, "local meta escaped its definition!");
                match &self.local_metas[num as usize] {
                    MetaEntry::Solved(v, _) => Some(Val::Arc(v.clone())), //.map(|x| x.inline_metas(self)),
                    MetaEntry::Unsolved(_, _, _) => None,
                }
            }
        }
    }

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

    pub fn env(&self) -> Env {
        Env::new(self.size)
    }

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
                Val::App(Var::Local(from_lvl), sp, _) if sp.is_empty() => (*from_lvl, to_lvl),
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect();
        let term = val.quote(self.size, &self);
        // The level it will be at after we wrap it in lambdas
        let to_lvl = (0..spine.len()).fold(self.size, |x, _| x.inc());

        // Get the type of each argument
        let tys: Vec<Ty> = spine
            .iter()
            .zip(std::iter::successors(Some(self.size), |lvl| {
                Some(lvl.inc())
            }))
            .map(|((_, v), l)| match v.unarc() {
                Val::App(Var::Local(from_lvl), sp, _) if sp.is_empty() => {
                    let ty = self.local_ty(from_lvl.to_ix(self.size), db);
                    ty.quote(l, self)
                }
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect();

        let term = term.check_solution(
            Spanned::new(meta, span),
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
        let val = term.evaluate(&Env::new(self.size), &self);
        // Now add it to the solved metas
        match meta {
            Meta::Type(id) => {
                self.solved_globals
                    .push(RecSolution::Infered(id, span, val));
            }
            Meta::Local(def, idx) => {
                assert_eq!(def, self.def, "local meta escaped its definition!");
                // TODO should we do anything with the span we already have in `local_metas`, where it was introduced?
                self.local_metas[idx as usize] = MetaEntry::Solved(Arc::new(val), span);
            }
        }
        Ok(())
    }

    pub fn new_meta(&mut self, name: Option<Name>, span: Span, source: MetaSource) -> Term {
        use std::convert::TryInto;

        let meta = Meta::Local(
            self.def,
            self.local_metas
                .len()
                .try_into()
                .expect("Only 65535 metas allowed per definition"),
        );
        self.local_metas
            .push(MetaEntry::Unsolved(name, span, source));

        // Apply it to all the bound variables in scope
        self.size.apply_meta(Term::Var(Var::Meta(meta)))
    }

    /// Makes sure all local metas are solved.
    /// If some aren't, it reports errors to `db` and returns Err(()).
    pub fn check_locals(&mut self, db: &dyn Compiler) -> Result<(), ()> {
        let mut ret = Ok(());
        for (i, entry) in self.local_metas.iter().enumerate() {
            match entry {
                MetaEntry::Solved(_, _) => (),
                MetaEntry::Unsolved(_, span, _) => {
                    db.report_error(Error::new(
                        self.cxt.file(db),
                        Doc::start("Could not find solution for ")
                            .chain(Meta::Local(self.def, i as u16).pretty(self, db)),
                        *span,
                        "introduced here",
                    ));
                    ret = Err(());
                }
            }
        }
        ret
    }
}
impl Meta {
    fn pretty(self, mcxt: &MCxt, db: &dyn Compiler) -> Doc {
        match self {
            Meta::Type(id) => match &**db.lookup_intern_predef(id) {
                PreDef::Fun(n, _, _, _) => Doc::start("type of function ").add(n.get(db)),
                PreDef::Val(n, _, _) => Doc::start("type of definition ").add(n.get(db)),
                PreDef::Type(n, _, _) => Doc::start("type of data type ").add(n.get(db)),
                PreDef::Impl(Some(n), _, _) => Doc::start("type of implicit ").add(n.get(db)),
                PreDef::Impl(None, _, _) => Doc::start("type of implicit"),
                PreDef::Expr(_) => Doc::start("type of expression"),
                PreDef::FunDec(n, _, _) => {
                    Doc::start("type of function declaration ").add(n.get(db))
                }
                PreDef::ValDec(n, _) => Doc::start("type of declaration ").add(n.get(db)),
                PreDef::Cons(_, _) => unreachable!("Constructor types should already be solved!"),
            },
            Meta::Local(_, n) => match &mcxt.local_metas[n as usize] {
                MetaEntry::Solved(_, _) => panic!("meta already solved"),
                MetaEntry::Unsolved(_, _, source) => match source {
                    MetaSource::ImplicitParam(n) => {
                        Doc::start("implicit parameter ").add(n.get(db))
                    }
                    MetaSource::LocalType(n) => Doc::start("type of ").add(n.get(db)),
                    MetaSource::Hole => Doc::start("hole"),
                    MetaSource::HoleType => Doc::start("type of hole"),
                },
            },
        }
    }
}

pub fn elaborate_def(db: &dyn Compiler, def: DefId) -> Result<ElabInfo, DefError> {
    let start_time = Instant::now();

    let (predef_id, cxt) = db.lookup_intern_def(def);
    let predef = db.lookup_intern_predef(predef_id);
    let file = cxt.file(db);
    let mut mcxt = MCxt::new(cxt, def, db);
    let (term, ty): (Term, VTy) = match &**predef {
        PreDef::Val(_, ty, val) | PreDef::Impl(_, ty, val) => {
            match check(ty, &Val::Type, db, &mut mcxt) {
                Ok(ty) => {
                    let ty = ty.evaluate(&mcxt.env(), &mcxt);
                    match check(val, &ty, db, &mut mcxt) {
                        Ok(val) => Ok((val, ty)),
                        Err(e) => {
                            db.report_error(e.to_error(file, db, &mcxt));
                            Err(DefError::ElabError)
                        }
                    }
                }
                Err(e) => {
                    db.report_error(e.to_error(file, db, &mcxt));
                    // We can still try to infer the type
                    match infer(true, val, db, &mut mcxt) {
                        Ok(x) => Ok(x),
                        Err(e) => {
                            db.report_error(e.to_error(file, db, &mcxt));
                            Err(DefError::ElabError)
                        }
                    }
                }
            }
        }
        PreDef::Fun(_, args, body_ty, body) => {
            let mut targs = Vec::new();
            for (name, icit, ty) in args {
                let ty = match check(ty, &Val::Type, db, &mut mcxt) {
                    Ok(x) => x,
                    Err(e) => {
                        db.report_error(e.to_error(file, db, &mcxt));
                        // TODO make a meta? or just call `infer()`?
                        Term::Error
                    }
                };
                let vty = ty.evaluate(&mcxt.env(), &mcxt);
                targs.push((*name, *icit, vty.clone()));
                mcxt.define(*name, NameInfo::Local(vty), db);
            }
            let body_ty = match check(body_ty, &Val::Type, db, &mut mcxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db, &mcxt));
                    // TODO make a meta? or just call `infer()`?
                    Term::Error
                }
            };
            let vty = body_ty.evaluate(&mcxt.env(), &mcxt);
            let body = match check(body, &vty, db, &mut mcxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db, &mcxt));
                    return Err(DefError::ElabError);
                }
            };
            Ok((
                targs
                    .iter()
                    .rfold((body, mcxt.size), |(body, mut size), (name, icit, ty)| {
                        // We're going to need to quote the types, so undefine the most recent arg
                        size = size.dec();
                        (
                            Term::Lam(
                                *name,
                                *icit,
                                Box::new(ty.clone().quote(size, &mcxt)),
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
                                Box::new(from),
                                Box::new(Clos(Env::new(size), to.quote(size, &mcxt), name)),
                            ),
                            size.dec(),
                        )
                    })
                    .0,
            ))
        }
        PreDef::Cons(_name, ty) => {
            // We don't have to do anything since the type was already determined
            Ok((Term::Var(Var::Cons(def)), ty.clone()))
        }
        PreDef::Type(name, args, cons) => {
            // A copy of the context before we added the type arguments
            let cxt_before = mcxt.state();

            // Evaluate the argument types and collect them up
            let mut targs = Vec::new();
            for (name, icit, ty) in args {
                let ty = match check(ty, &Val::Type, db, &mut mcxt) {
                    Ok(x) => x,
                    Err(e) => {
                        db.report_error(e.to_error(file, db, &mcxt));
                        // TODO make a meta? or just call `infer()`?
                        Term::Error
                    }
                };
                let vty = ty.evaluate(&mcxt.env(), &mcxt);
                targs.push((*name, *icit, vty.clone()));
                mcxt.define(*name, NameInfo::Local(vty), db);
            }

            // We have to do this now, so that the constructors can use the type
            let (ty_ty, _) = targs
                .iter()
                .rfold((Val::Type, mcxt.size), |(to, l), (n, i, from)| {
                    (
                        Val::Pi(
                            *i,
                            Box::new(from.clone()),
                            Box::new(Clos(Env::new(l.dec()), to.clone().quote(l, &mcxt), *n)),
                        ),
                        l.dec(),
                    )
                });
            mcxt.solved_globals.push(RecSolution::Defined(
                predef_id,
                predef.span(),
                ty_ty.clone(),
            ));

            let cxt_after = mcxt.state();

            let mut scope = Vec::new();

            // Go through the constructors
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
                // But we want to use the same mcxt, so meta solutions get saved
                if cty.is_some() {
                    mcxt.set_state(cxt_before);
                } else {
                    mcxt.set_state(cxt_after);
                    // If they can use the type parameters, add them all as implicit arguments
                    // They go in the same order as the type parameters, so we don't need to change the mcxt
                    for (n, _i, t) in &targs {
                        cargs.push((*n, Icit::Impl, t.clone()));
                    }
                }

                // TODO this should be a function
                for (name, icit, ty) in args {
                    let ty = match check(ty, &Val::Type, db, &mut mcxt) {
                        Ok(x) => x,
                        Err(e) => {
                            db.report_error(e.to_error(file, db, &mcxt));
                            // TODO make a meta? or just call `infer()`?
                            Term::Error
                        }
                    };
                    let vty = ty.evaluate(&mcxt.env(), &mcxt);
                    cargs.push((*name, *icit, vty.clone()));
                    mcxt.define(*name, NameInfo::Local(vty), db);
                }

                // If the user provided a type for the constructor, typecheck it
                let cty = if let Some(cty) = cty {
                    match check(cty, &Val::Type, db, &mut mcxt) {
                        Ok(x) => match x.ret().head() {
                            Term::Var(Var::Rec(id)) if *id == predef_id => x,
                            _ => {
                                // We want the type to appear in the error message as it was written
                                let mut type_string = db.lookup_intern_name(**name);
                                for (n, _, _) in &targs {
                                    type_string.push(' ');
                                    type_string.push_str(&db.lookup_intern_name(*n));
                                }
                                let e = Error::new(
                                    file,
                                    "Constructor return type must be the type it's a part of",
                                    cty.span(),
                                    format!("expected return type '{}'", type_string),
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
                    targs
                        .iter()
                        .fold(
                            (
                                Term::Var(Var::Rec(predef_id)),
                                cxt_before.size.to_ix(mcxt.size),
                            ),
                            |(f, ix), (_n, i, _t)| {
                                let ix = ix.dec();
                                (
                                    Term::App(*i, Box::new(f), Box::new(Term::Var(Var::Local(ix)))),
                                    ix,
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
                                Term::Pi(n, i, Box::new(from.quote(l.dec(), &mcxt)), Box::new(to)),
                                l.dec(),
                            )
                        });

                let full_ty = full_ty.evaluate(&mcxt.env(), &mcxt).inline_metas(&mcxt);

                let def_id = db.intern_def(
                    db.intern_predef(Arc::new(PreDef::Cons(cname.clone(), full_ty).into())),
                    cxt_before.cxt,
                );
                scope.push((**cname, def_id));
            }

            let scope = db.intern_scope(Arc::new(scope));

            Ok((Term::Var(Var::Type(def, scope)), ty_ty))
        }
        PreDef::Expr(e) => match infer(true, e, db, &mut mcxt) {
            Err(e) => {
                db.report_error(e.to_error(file, db, &mcxt));
                Err(DefError::ElabError)
            }
            Ok(stuff) => Ok(stuff),
        },
        PreDef::FunDec(_, from, to) => {
            for (_, _, from) in from {
                if let Err(e) = check(from, &Val::Type, db, &mut mcxt) {
                    db.report_error(e.to_error(file, db, &mcxt));
                }
            }
            if let Err(e) = check(to, &Val::Type, db, &mut mcxt) {
                db.report_error(e.to_error(file, db, &mcxt));
            }
            Err(DefError::NoValue)
        }
        PreDef::ValDec(_, ty) => {
            if let Err(e) = check(ty, &Val::Type, db, &mut mcxt) {
                db.report_error(e.to_error(file, db, &mcxt));
            }
            Err(DefError::NoValue)
        }
    }?;
    mcxt.solved_globals
        .push(RecSolution::Defined(predef_id, predef.span(), ty.clone()));
    let ret = match mcxt.check_locals(db) {
        Ok(()) => {
            let term = term.inline_metas(&mcxt, mcxt.size);
            let ty = ty.inline_metas(&mcxt);

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
                .unwrap_or("<unnamed>".into());
            println!("Elaborate time for {}: {:?}", name, end_time - start_time);
        }
        if predef.attributes.contains(&Attribute::Normalize) {
            let mcxt = MCxt::new(cxt, def, db);
            let term = (*ret.term).clone();

            let n_start = Instant::now();
            let _ = term
                .evaluate(&mcxt.env(), &mcxt)
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

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ScopeType {
    Type,
    Struct,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    NotFound(Spanned<Name>),
    NotFunction(MCxt, Spanned<VTy>),
    Unify(MCxt, Spanned<VTy>, VTy),
    MetaScope(Span, Meta, Name),
    MetaOccurs(Span, Meta),
    NotStruct(Spanned<VTy>),
    MemberNotFound(Span, ScopeType, Name),
}
impl TypeError {
    fn to_error(self, file: FileId, db: &dyn Compiler, mcxt: &MCxt) -> Error {
        match self {
            TypeError::NotFound(n) => Error::new(
                file,
                format!("Name not found in scope: {}", n.get(db)),
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
            TypeError::Unify(mcxt, a, b) => Error::new(
                file,
                Doc::start("Could not match types, expected ")
                    .chain(b.pretty(db, &mcxt).style(Style::None))
                    .add(", got ")
                    .chain(a.pretty(db, &mcxt).style(Style::None))
                    .style(Style::Bold),
                a.span(),
                Doc::start("expected ")
                    .chain(b.pretty(db, &mcxt))
                    .add(" here"),
            ),
            // TODO show metas nicer
            TypeError::MetaScope(s, m, n) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty(mcxt, db))
                    .add(" requires variable ")
                    .add(n.get(db))
                    .add(", which is not in its scope"),
                s,
                format!("solution found here"),
            ),
            TypeError::MetaOccurs(s, m) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty(mcxt, db))
                    .add(" would be recursive"),
                s,
                format!("solution found here"),
            ),
            TypeError::NotStruct(ty) => Error::new(
                file,
                Doc::start("Value of type ")
                    .chain(ty.pretty(db, mcxt).style(Style::None))
                    .add(" does not have members"),
                ty.span(),
                format!("tried to access member here"),
            ),
            TypeError::MemberNotFound(span, sctype, m) => Error::new(
                file,
                Doc::start("Could not find member ")
                    .add(db.lookup_intern_name(m))
                    .add(" in ")
                    .add(match sctype {
                        ScopeType::Type => "type namespace",
                        ScopeType::Struct => "struct",
                    }),
                span,
                format!("not found: {}", db.lookup_intern_name(m)),
            ),
        }
    }
}

fn p_unify(
    inline: bool,
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
            p_unify(inline, a, b, l, span, db, mcxt)
        }

        (Val::Error, _) | (_, Val::Error) => Ok(Yes),
        (Val::Type, Val::Type) => Ok(Yes),

        (Val::App(h, v, _), Val::App(h2, v2, _)) if h.unify(h2, db) => {
            let mut r = Yes;
            for ((i, a), (i2, b)) in v.into_iter().zip(v2.into_iter()) {
                assert_eq!(i, i2);
                r = r & p_unify(inline, a, b, l, span, db, mcxt)?;
            }
            Ok(r)
        }

        // Since our terms are locally nameless (we're using De Bruijn levels), we automatically get alpha equivalence.
        (Val::Lam(_, _, cl), Val::Lam(_, _, cl2)) => p_unify(
            inline,
            cl.vquote(l, mcxt),
            cl2.vquote(l, mcxt),
            l.inc(),
            span,
            db,
            mcxt,
        ),

        // If one side is a lambda, the other side just needs to unify to the same thing when we apply it to the same thing
        (Val::Lam(icit, _, cl), t) | (t, Val::Lam(icit, _, cl)) => p_unify(
            inline,
            cl.vquote(l, mcxt),
            t.app(icit, Val::local(l), mcxt),
            l.inc(),
            span,
            db,
            mcxt,
        ),

        (Val::Pi(i, ty, cl), Val::Pi(i2, ty2, cl2)) if i == i2 => {
            Ok(p_unify(inline, *ty, *ty2, l, span, db, mcxt)?
                // Applying both to the same thing (Local(l))
                & p_unify(
                    inline,
                    cl.vquote(l, mcxt),
                    cl2.vquote(l, mcxt),
                    l.inc(),
                    span,
                    db,
                    mcxt,
                )?)
        }
        (Val::Pi(Icit::Expl, ty, cl), Val::Fun(from, to))
        | (Val::Fun(from, to), Val::Pi(Icit::Expl, ty, cl)) => {
            // TODO: I'm not 100% this is right
            Ok(p_unify(inline, *ty, *from, l, span, db, mcxt)?
                & p_unify(inline, cl.vquote(l, mcxt), *to, l.inc(), span, db, mcxt)?)
        }
        (Val::Fun(a, b), Val::Fun(a2, b2)) => Ok(p_unify(inline, *a, *a2, l, span, db, mcxt)?
            & p_unify(inline, *b, *b2, l, span, db, mcxt)?),

        // Solve metas

        // Make sure order doesn't matter - switch sides if the second one is higher
        (Val::App(Var::Meta(m), s, g), Val::App(Var::Meta(m2), s2, g2)) if m2 > m => p_unify(
            inline,
            Val::App(Var::Meta(m2), s2, g2),
            Val::App(Var::Meta(m), s, g),
            l,
            span,
            db,
            mcxt,
        ),

        (Val::App(Var::Meta(m), sp, _), t) | (t, Val::App(Var::Meta(m), sp, _)) => {
            match mcxt.get_meta(m) {
                Some(v) => {
                    let v = sp.into_iter().fold(v, |f, (i, x)| f.app(i, x, mcxt));
                    p_unify(inline, v, t, l, span, db, mcxt)
                }
                None => {
                    mcxt.solve(span, m, &sp, t, db)?;
                    Ok(Yes)
                }
            }
        }

        // If the reason we can't unify is that one side is a top variable, then we can try again after inlining.
        (Val::App(Var::Top(_), _, _), _) | (_, Val::App(Var::Top(_), _, _)) if !inline => Ok(Maybe),

        (Val::App(h, sp, g), Val::App(h2, sp2, g2)) if inline => {
            if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                p_unify(inline, Val::App(h2, sp2, g2), v, l, span, db, mcxt)
            } else if let Some(v) = g2.resolve(h2, sp2, l, db, mcxt) {
                p_unify(inline, Val::App(h, sp, g), v, l, span, db, mcxt)
            } else {
                Ok(No)
            }
        }

        (Val::App(h, sp, g), x) | (x, Val::App(h, sp, g)) if inline => {
            if let Some(v) = g.resolve(h, sp, l, db, mcxt) {
                p_unify(inline, x, v, l, span, db, mcxt)
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
    match p_unify(false, a.clone(), b.clone(), l, span, db, mcxt)? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(true, a, b, l, span, db, mcxt)?.not_maybe()),
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
        Val::Pi(Icit::Impl, _pty, cl) if insert => {
            let meta = mcxt.new_meta(None, span, MetaSource::ImplicitParam(cl.2));
            let vmeta = meta.clone().evaluate(&mcxt.env(), mcxt);
            let ret = cl.apply(vmeta, mcxt);
            insert_metas(
                insert,
                Term::App(Icit::Impl, Box::new(term), Box::new(meta)),
                ret,
                span,
                mcxt,
                db,
            )
        }
        Val::App(h, sp, g) if insert => match g.resolve(h, &sp, mcxt.size, db, mcxt) {
            Some(ty) => insert_metas(insert, term, ty, span, mcxt, db),
            None => (term, Val::App(h, sp, g)),
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

        Pre_::Var(name) => {
            let (term, ty) = match mcxt.lookup(*name, db) {
                Some(NameResult::Def(def)) => {
                    match db.def_type(def) {
                        Ok(ty) => Ok((Term::Var(Var::Top(def)), (*ty).clone())),
                        // If something else had a type error, try to keep going anyway and maybe catch more
                        Err(DefError::ElabError) => Ok((
                            Term::Error,
                            Val::meta(Meta::Type(db.lookup_intern_def(def).0)),
                        )),
                        Err(DefError::NoValue) => Err(TypeError::NotFound(pre.copy_span(*name))),
                    }
                }
                Some(NameResult::Rec(id)) => {
                    Ok((Term::Var(Var::Rec(id)), Val::meta(Meta::Type(id))))
                }
                Some(NameResult::Local(ix, ty)) => Ok((Term::Var(Var::Local(ix)), ty)),
                None => Err(TypeError::NotFound(pre.copy_span(*name))),
            }?;
            Ok(insert_metas(insert, term, ty, pre.span(), mcxt, db))
        }

        Pre_::Lam(name, icit, ty, body) => {
            let ty = check(ty, &Val::Type, db, mcxt)?;
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt);
            // TODO Rc to get rid of the clone()?
            mcxt.define(*name, NameInfo::Local(vty.clone()), db);
            let (body, bty) = infer(true, body, db, mcxt)?;
            mcxt.undef(db);
            // TODO do we insert metas here?
            Ok((
                Term::Lam(*name, *icit, Box::new(ty), Box::new(body)),
                Val::Pi(
                    *icit,
                    Box::new(vty),
                    // `inc()` since we're wrapping it in a lambda
                    Box::new(Clos(mcxt.env(), bty.quote(mcxt.size.inc(), mcxt), *name)),
                ),
            ))
        }

        Pre_::Pi(name, icit, ty, ret) => {
            let ty = check(ty, &Val::Type, db, mcxt)?;
            // TODO Rc to get rid of the clone()?
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt);
            mcxt.define(*name, NameInfo::Local(vty), db);
            let ret = check(ret, &Val::Type, db, mcxt)?;
            mcxt.undef(db);
            Ok((
                Term::Pi(*name, *icit, Box::new(ty), Box::new(ret)),
                Val::Type,
            ))
        }

        Pre_::Fun(from, to) => {
            let from = check(from, &Val::Type, db, mcxt)?;
            let to = check(to, &Val::Type, db, mcxt)?;
            Ok((Term::Fun(Box::new(from), Box::new(to)), Val::Type))
        }

        Pre_::App(icit, f, x) => {
            let fspan = f.span();
            // Don't insert metas in `f` if we're passing an implicit argument
            let (f, fty) = infer(*icit == Icit::Expl, f, db, mcxt)?;

            infer_app(insert, pre.span(), f, fty, fspan, *icit, x, db, mcxt)
        }

        Pre_::Do(v) => {
            // We store the whole block in Salsa, then query the last expression
            let block = crate::query::intern_block(v.clone(), db, mcxt.cxt);
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
                        return Ok(((*info.term).clone(), Val::Arc(info.typ)));
                    } else {
                        // If there was a type error inside the block, we'll leave it, we don't want a cascade of errors
                        return Ok((Term::Error, Val::Error));
                    }
                }
            }
            todo!("return ()")
        }

        Pre_::Struct(_) => todo!("elaborate struct"),

        Pre_::Hole(source) => Ok((
            mcxt.new_meta(None, pre.span(), *source),
            mcxt.new_meta(None, pre.span(), MetaSource::HoleType)
                .evaluate(&mcxt.env(), mcxt),
        )),

        Pre_::Dot(head, m, args) => {
            match infer(true, head, db, mcxt).map(|(x, ty)| {
                (
                    x.evaluate(&mcxt.env(), mcxt).inline(mcxt.size, db, mcxt),
                    ty,
                )
            })? {
                (_, Val::Error) => return Ok((Term::Error, Val::Error)),
                (Val::App(Var::Type(_id, scope), sp, _), _) if sp.is_empty() => {
                    let scope = db.lookup_intern_scope(scope);
                    for &(n, v) in scope.iter().rev() {
                        if n == **m {
                            match db.elaborate_def(v) {
                                Ok(info) => {
                                    let f = Term::Var(Var::Top(v));
                                    let fty = info.typ.into_owned();
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
                                                let (f, fty) = infer_app(
                                                    false,
                                                    pre.span(),
                                                    f,
                                                    fty,
                                                    fspan,
                                                    *i,
                                                    x,
                                                    db,
                                                    mcxt,
                                                )?;
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
                        ScopeType::Type,
                        **m,
                    ))
                }
                (_, ty) => Err(TypeError::NotStruct(Spanned::new(
                    ty,
                    Span(head.span().0, m.span().1),
                ))),
            }
        }
    }
}

fn infer_app(
    insert: bool,
    pre_span: Span,
    f: Term,
    fty: VTy,
    fspan: Span,
    icit: Icit,
    x: &Pre,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<(Term, VTy), TypeError> {
    let (term, ty) = match fty {
        Val::Pi(icit2, from, cl) => {
            assert_eq!(icit, icit2);

            let x = check(x, &*from, db, mcxt)?;
            // TODO Rc to get rid of the clone()?
            let to = cl.apply(x.clone().evaluate(&mcxt.env(), mcxt), mcxt);
            Ok((Term::App(icit, Box::new(f), Box::new(x)), to))
        }
        Val::Fun(from, to) => {
            let x = check(x, &*from, db, mcxt)?;
            Ok((Term::App(icit, Box::new(f), Box::new(x)), *to))
        }
        // The type was already Error, so we'll leave it there, not introduce a meta
        Val::Error => Ok((Term::Error, Val::Error)),
        fty => {
            return Err(TypeError::NotFunction(
                mcxt.clone(),
                Spanned::new(fty, fspan),
            ))
        }
    }?;
    Ok(insert_metas(insert, term, ty, pre_span, mcxt, db))
}

pub fn check(pre: &Pre, ty: &VTy, db: &dyn Compiler, mcxt: &mut MCxt) -> Result<Term, TypeError> {
    match (&**pre, ty) {
        (_, Val::Arc(x)) => check(pre, x, db, mcxt),

        (Pre_::Lam(n, i, ty, body), Val::Pi(i2, ty2, cl)) if i == i2 => {
            let ety = check(ty, &Val::Type, db, mcxt)?;
            let vty = ety.clone().evaluate(&mcxt.env(), mcxt);
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
                ));
            }
            mcxt.define(*n, NameInfo::Local(vty), db);
            let body = check(
                body,
                // TODO not clone ??
                &cl.clone().apply(Val::local(mcxt.size), mcxt),
                db,
                mcxt,
            )?;
            mcxt.undef(db);
            Ok(Term::Lam(*n, *i, Box::new(ety), Box::new(body)))
        }

        (Pre_::Lam(n, Icit::Expl, ty, body), Val::Fun(ty2, body_ty)) => {
            let ety = check(ty, &Val::Type, db, mcxt)?;
            let vty = ety.clone().evaluate(&mcxt.env(), mcxt);
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
                ));
            }
            mcxt.define(*n, NameInfo::Local(vty), db);
            let body = check(body, &*body_ty, db, mcxt)?;
            mcxt.undef(db);
            Ok(Term::Lam(*n, Icit::Expl, Box::new(ety), Box::new(body)))
        }

        // We implicitly insert lambdas so `\x.x : [a] -> a -> a` typechecks
        (_, Val::Pi(Icit::Impl, ty, cl)) => {
            // Add a ' after the name so it doesn't shadow names the term defined (' isn't valid in Pika identifiers)
            let name = {
                let mut s = cl.2.get(db);
                s.push('\'');
                db.intern_name(s)
            };
            mcxt.define(name, NameInfo::Local((**ty).clone()), db);
            let body = check(pre, &cl.clone().vquote(mcxt.size, mcxt), db, mcxt)?;
            mcxt.undef(db);
            let ty = (**ty).clone().quote(mcxt.size, mcxt);
            Ok(Term::Lam(cl.2, Icit::Impl, Box::new(ty), Box::new(body)))
        }

        _ => {
            if let Val::App(h, sp, g) = ty {
                if let Some(v) = g.resolve(*h, sp, mcxt.size, db, mcxt) {
                    return check(pre, &v, db, mcxt);
                }
            }

            let (term, i_ty) = infer(true, pre, db, mcxt)?;
            // TODO should we take `ty` by value?
            if !unify(ty.clone(), i_ty.clone(), mcxt.size, pre.span(), db, mcxt)? {
                eprintln!("{:?} vs {:?}", i_ty, ty);
                return Err(TypeError::Unify(
                    mcxt.clone(),
                    pre.copy_span(i_ty.inline_metas(mcxt)),
                    ty.clone().inline_metas(mcxt),
                ));
            }
            Ok(term)
        }
    }
}
