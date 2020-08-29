use crate::error::*;
use crate::evaluate::*;
use crate::query::*;
use crate::term::*;
use std::sync::Arc;

pub enum MetaEntry {
    Solved(Val, Span),
    Unsolved(Option<Name>, Span),
}

use std::collections::HashMap;
type Rename = HashMap<Lvl, Lvl>;

impl Term {
    /// Applies `ren`, and makes sure `self` is a valid solution to `meta` in this scope.
    /// Checks to make sure any locals it uses are in `ren` ("scope check"), and that it doesn't contain `meta` ("occurs check").
    fn check_solution(
        self,
        meta: Spanned<Meta>,
        ren: &Rename,
        enclosing: Lvl,
    ) -> Result<Term, TypeError> {
        match self {
            Term::Var(v) => match v {
                Var::Meta(m) if m == *meta => Err(TypeError::MetaOccurs(meta.span(), *meta)),
                // We store the renamings as levels and go between here, since indices change inside lambdas but levels don't.
                Var::Local(ix) => match ren.get(&ix.to_lvl(enclosing)) {
                    Some(lvl) => Ok(Term::Var(Var::Local(lvl.to_ix(enclosing)))),
                    None => Err(TypeError::MetaScope(meta.span(), *meta, todo!("names"))),
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
            Term::Lam(i, mut t) => {
                *t = t.check_solution(meta, ren, enclosing.inc())?;
                Ok(Term::Lam(i, t))
            }
            Term::Pi(i, mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, enclosing)?;
                *b = b.check_solution(meta, ren, enclosing.inc())?;
                Ok(Term::Pi(i, a, b))
            }
            Term::Fun(mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, enclosing)?;
                *b = b.check_solution(meta, ren, enclosing)?;
                Ok(Term::Fun(a, b))
            }
            Term::App(i, mut a, mut b) => {
                *a = a.check_solution(meta.clone(), ren, enclosing)?;
                *b = b.check_solution(meta, ren, enclosing)?;
                Ok(Term::App(i, a, b))
            }
            Term::Error => Ok(Term::Error),
            Term::Type => Ok(Term::Type),
        }
    }
}

pub struct MCxt {
    cxt: Cxt,
    size: Lvl,
    def: DefId,
    local_metas: Vec<MetaEntry>,
    solved_globals: Vec<RecSolution>,
}
impl MCxt {
    pub fn new(cxt: Cxt, def: DefId, db: &dyn Compiler) -> Self {
        MCxt {
            cxt,
            size: cxt.size(db),
            def,
            local_metas: Vec::new(),
            solved_globals: Vec::new(),
        }
    }

    pub fn lookup(&self, name: Name, db: &dyn Compiler) -> Option<NameResult> {
        self.cxt.lookup(name, db)
    }

    pub fn define(&mut self, name: Name, info: NameInfo, db: &dyn Compiler) {
        self.cxt = self.cxt.define(name, info, db);
        self.size = self.size.inc();
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
                    MetaEntry::Solved(v, _) => Some(v.clone()),
                    MetaEntry::Unsolved(_, _) => None,
                }
            }
        }
    }

    pub fn undef(&mut self, db: &dyn Compiler) {
        self.cxt = match db.lookup_cxt_entry(self.cxt) {
            MaybeEntry::Yes(CxtEntry { rest, .. }) => rest,
            _ => panic!("Called undef() without define()!"),
        };
        self.size = self.size.dec();
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
        let meta_scope: Rename = spine
            .iter()
            // Each argument is another lambda we're going to wrap it in
            .zip(std::iter::successors(Some(self.size), |lvl| {
                Some(lvl.inc())
            }))
            .map(|((_, x), to_lvl)| match x {
                Val::App(Var::Local(from_lvl), sp) if sp.is_empty() => (*from_lvl, to_lvl),
                _ => panic!("Compiler error: meta spine contains non-variable"),
            })
            .collect();
        // We need to pass it the level it *will* be at after we wrap it in lambdas
        let to_lvl = (0..spine.len()).fold(self.size, |x, _| x.inc());
        let term = quote(val, to_lvl, &self);
        let term = term.check_solution(Spanned::new(meta, span), &meta_scope, to_lvl)?;
        // Actually wrap it in lambdas
        let term = (0..spine.len()).fold(term, |term, _| Term::Lam(Icit::Expl, Box::new(term)));

        // Reevaluating the term so we don't have to clone it to quote it, and it should inline solved metas as well
        let val = evaluate(term, &Env::new(self.size), &self);
        // Now add it to the solved metas
        match meta {
            Meta::Type(id) => {
                self.solved_globals
                    .push(RecSolution::Infered(id, span, val));
            }
            Meta::Local(def, idx) => {
                assert_eq!(def, self.def, "local meta escaped its definition!");
                // TODO should we do anything with the span we already have in `local_metas`, where it was introduced?
                self.local_metas[idx as usize] = MetaEntry::Solved(val, span);
            }
        }
        Ok(())
    }

    pub fn new_meta(&mut self, name: Option<Name>, span: Span) -> Term {
        use std::convert::TryInto;

        let meta = Meta::Local(
            self.def,
            self.local_metas
                .len()
                .try_into()
                .expect("Only 65535 metas allowed per definition"),
        );
        self.local_metas.push(MetaEntry::Unsolved(name, span));

        // Apply it to all the bound variables in scope
        self.size.apply_meta(Term::Var(Var::Meta(meta)))
    }

    /// Makes sure all local metas are solved.
    /// If some aren't, it reports errors to `db` and returns Err(()).
    pub fn check_locals(&mut self, db: &dyn Compiler) -> Result<(), ()> {
        let mut ret = Ok(());
        for entry in &self.local_metas {
            match entry {
                MetaEntry::Solved(_, _) => (),
                MetaEntry::Unsolved(name, span) => {
                    // TODO better meta formatting
                    let name = name.map_or("?hole".to_string(), |x| x.get(db));
                    db.report_error(Error::new(
                        self.cxt.file(db),
                        format!("Could not find solution for metavariable '{}'", name),
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

pub fn elaborate_def(db: &dyn Compiler, def: DefId) -> Result<ElabInfo, DefError> {
    let (predef_id, cxt) = db.lookup_intern_def(def);
    let predef = db.lookup_intern_predef(predef_id);
    let file = cxt.file(db);
    let mut mcxt = MCxt::new(cxt, def, db);
    let (term, ty): (Term, VTy) = match &*predef {
        PreDef::Val(_, ty, val) | PreDef::Impl(_, ty, val) => {
            match check(ty, &Val::Type, db, &mut mcxt) {
                Ok(ty) => {
                    let ty = evaluate(ty, &mcxt.env(), &mcxt);
                    match check(val, &ty, db, &mut mcxt) {
                        Ok(val) => Ok((val, ty)),
                        Err(e) => {
                            db.report_error(e.to_error(file, db));
                            Err(DefError::ElabError)
                        }
                    }
                }
                Err(e) => {
                    db.report_error(e.to_error(file, db));
                    // We can still try to infer the type
                    match infer(true, val, db, &mut mcxt) {
                        Ok(x) => Ok(x),
                        Err(e) => {
                            db.report_error(e.to_error(file, db));
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
                        db.report_error(e.to_error(file, db));
                        // TODO make a meta? or just call `infer()`?
                        Term::Error
                    }
                };
                let vty = evaluate(ty, &mcxt.env(), &mcxt);
                targs.push((*icit, vty.clone()));
                mcxt.define(*name, NameInfo::Local(vty), db);
            }
            let body_ty = match check(body_ty, &Val::Type, db, &mut mcxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db));
                    // TODO make a meta? or just call `infer()`?
                    Term::Error
                }
            };
            let vty = evaluate(body_ty, &mcxt.env(), &mcxt);
            let body = match check(body, &vty, db, &mut mcxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db));
                    return Err(DefError::ElabError);
                }
            };
            Ok((
                targs
                    .iter()
                    .rfold(body, |body, (icit, _)| Term::Lam(*icit, Box::new(body))),
                targs
                    .into_iter()
                    .rfold((vty, mcxt.size), |(to, size), (icit, from)| {
                        (
                            Val::Pi(
                                icit,
                                Box::new(from),
                                Clos(Box::new(Env::new(size)), Box::new(quote(to, size, &mcxt))),
                            ),
                            size.dec(),
                        )
                    })
                    .0,
            ))
        }
        PreDef::Type(_, _, _) => todo!("data types"),
        PreDef::Expr(e) => {
            if let Err(e) = infer(true, e, db, &mut mcxt) {
                db.report_error(e.to_error(file, db));
            }
            Err(DefError::NoValue)
        }
        PreDef::FunDec(_, from, to) => {
            for (_, _, from) in from {
                if let Err(e) = check(from, &Val::Type, db, &mut mcxt) {
                    db.report_error(e.to_error(file, db));
                }
            }
            if let Err(e) = check(to, &Val::Type, db, &mut mcxt) {
                db.report_error(e.to_error(file, db));
            }
            Err(DefError::NoValue)
        }
        PreDef::ValDec(_, ty) => {
            if let Err(e) = check(ty, &Val::Type, db, &mut mcxt) {
                db.report_error(e.to_error(file, db));
            }
            Err(DefError::NoValue)
        }
    }?;
    mcxt.solved_globals
        .push(RecSolution::Defined(predef_id, predef.span(), ty.clone()));
    match mcxt.check_locals(db) {
        Ok(()) => {
            let term = term.inline_metas(&mcxt, mcxt.size);
            let ty = ty.inline_metas(&mcxt);
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
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    NotFound(Spanned<Name>),
    NotFunction(Spanned<VTy>),
    Unify(Spanned<VTy>, VTy),
    MetaScope(Span, Meta, Name),
    MetaOccurs(Span, Meta),
}
impl TypeError {
    fn to_error(self, file: FileId, db: &dyn Compiler) -> Error {
        match self {
            TypeError::NotFound(n) => Error::new(
                file,
                format!("Name not found in scope: {}", n.get(db)),
                n.span(),
                "not found",
            ),
            TypeError::NotFunction(t) => Error::new(
                file,
                format!("Expected function type in application, but got: <TODO pretty val>"),
                t.span(),
                "not a function",
            ),
            TypeError::Unify(a, b) => Error::new(
                file,
                format!("Could not match types, expected <B>, got <A>"),
                a.span(),
                format!("expected <B>"),
            ),
            TypeError::MetaScope(s, m, n) => Error::new(
                file,
                format!(
                    "Solution for meta {:?} requires variable {}, which is not in the meta's scope",
                    m,
                    n.get(db)
                ),
                s,
                format!("solution found here"),
            ),
            TypeError::MetaOccurs(s, m) => Error::new(
                file,
                format!("Solution for meta {:?} would be recursive", m),
                s,
                format!("solution found here"),
            ),
        }
    }
}

/// A three-value logic type, useful for analysis with limited information.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TBool {
    Yes,
    No,
    Maybe,
}
impl TBool {
    /// Converts to a `bool`, panicking on `Maybe`.
    pub fn not_maybe(self) -> bool {
        match self {
            Yes => true,
            No => false,
            Maybe => panic!("Called `TBool::not_maybe()` on `Maybe`"),
        }
    }
}
pub use TBool::{Maybe, No, Yes};
impl std::ops::BitOr for TBool {
    type Output = TBool;

    fn bitor(self, rhs: TBool) -> TBool {
        match (self, rhs) {
            (Yes, _) | (_, Yes) => Yes,
            (No, No) => No,
            _ => Maybe,
        }
    }
}
impl std::ops::BitAnd for TBool {
    type Output = TBool;

    fn bitand(self, rhs: TBool) -> TBool {
        match (self, rhs) {
            (No, _) | (_, No) => No,
            (Yes, Yes) => Yes,
            _ => Maybe,
        }
    }
}
impl std::ops::BitAnd<bool> for TBool {
    type Output = TBool;

    fn bitand(self, rhs: bool) -> TBool {
        self & TBool::from(rhs)
    }
}
impl From<bool> for TBool {
    fn from(b: bool) -> TBool {
        match b {
            true => Yes,
            false => No,
        }
    }
}

impl Term {
    pub fn inline_metas(self, mcxt: &MCxt, l: Lvl) -> Self {
        match self {
            Term::Type => Term::Type,
            Term::Var(Var::Meta(m)) => match mcxt.get_meta(m) {
                Some(v) => quote(v, l, mcxt),
                None => Term::Var(Var::Meta(m)),
            },
            Term::Var(v) => Term::Var(v),
            Term::Lam(i, mut t) => {
                // Reuse Box
                *t = t.inline_metas(mcxt, l.inc());
                Term::Lam(i, t)
            }
            Term::Pi(i, mut from, mut to) => {
                *from = from.inline_metas(mcxt, l);
                *to = to.inline_metas(mcxt, l.inc());
                Term::Pi(i, from, to)
            }
            Term::Fun(mut from, mut to) => {
                *from = from.inline_metas(mcxt, l);
                *to = to.inline_metas(mcxt, l);
                Term::Fun(from, to)
            }
            Term::App(i, mut f, mut x) => {
                // We have to beta-reduce meta applications
                quote(evaluate(Term::App(i, f, x), &Env::new(l), mcxt), l, mcxt)
            }
            Term::Error => Term::Error,
        }
    }
}

impl Val {
    pub fn inline_metas(self, mcxt: &MCxt) -> Self {
        evaluate(quote(self, mcxt.size, mcxt), &mcxt.env(), mcxt)
    }
}

fn p_unify(
    a: Val,
    b: Val,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<TBool, TypeError> {
    Ok(match (a, b) {
        (Val::Error, _) | (_, Val::Error) => Yes,
        (Val::Type, Val::Type) => Yes,

        (Val::App(h, v), Val::App(h2, v2)) if h == h2 => {
            let mut r = Yes;
            for ((i, a), (i2, b)) in v.into_iter().zip(v2.into_iter()) {
                assert_eq!(i, i2);
                r = r & p_unify(a, b, span, db, mcxt)?;
            }
            r
        }

        // Since our terms are locally nameless (we're using De Bruijn levels), we automatically get alpha equivalence.
        // Also, we call `unify` instead of `p_unify` here so we can `inline()` the values we're creating here if necessary.
        (Val::Lam(_, cl), Val::Lam(_, cl2)) => {
            unify(cl.vquote(mcxt), cl2.vquote(mcxt), span, db, mcxt).map(|_| Yes)?
        }

        // If one side is a lambda, the other side just needs to unify to the same thing when we apply it to the same thing
        (Val::Lam(icit, cl), t) | (t, Val::Lam(icit, cl)) => {
            let var = Val::local(cl.env_size());
            unify(
                cl.apply(var.clone(), mcxt),
                t.app(icit, var, mcxt),
                span,
                db,
                mcxt,
            )
            .map(|_| Yes)?
        }

        (Val::Pi(i, ty, cl), Val::Pi(i2, ty2, cl2)) if i == i2 => {
            p_unify(*ty, *ty2, span, db, mcxt)?
                & unify(cl.vquote(mcxt), cl2.vquote(mcxt), span, db, mcxt).map(|_| Yes)?
        }
        (Val::Pi(Icit::Expl, ty, cl), Val::Fun(from, to))
        | (Val::Fun(from, to), Val::Pi(Icit::Expl, ty, cl)) => {
            // TODO: I'm not 100% this is right
            p_unify(*ty, *from, span, db, mcxt)?
                & unify(cl.vquote(mcxt), *to, span, db, mcxt).map(|_| Yes)?
        }
        (Val::Fun(a, b), Val::Fun(a2, b2)) => {
            p_unify(*a, *b, span, db, mcxt)? & p_unify(*a2, *b2, span, db, mcxt)?
        }

        // Solve metas
        // TODO make order not matter (compare metas?)
        (Val::App(Var::Meta(m), sp), t) | (t, Val::App(Var::Meta(m), sp)) => {
            mcxt.solve(span, m, &sp, t, db)?;
            Yes
        }

        // If the reason we can't unify is that one side is a top variable, then we can try again after inlining.
        (Val::App(Var::Top(_), _), _) | (_, Val::App(Var::Top(_), _)) => Maybe,

        // If that's not the reason, then we know inlining won't help.
        _ => No,
    })
}

/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn unify(
    a: Val,
    b: Val,
    span: Span,
    db: &dyn Compiler,
    mcxt: &mut MCxt,
) -> Result<(), TypeError> {
    match p_unify(a.clone(), b.clone(), span, db, mcxt)? {
        Yes => Ok(()),
        No => Err(TypeError::Unify(Spanned::new(a, span), b)),
        Maybe => {
            if let Yes = p_unify(inline(a.clone(), db), inline(b.clone(), db), span, db, mcxt)? {
                Ok(())
            } else {
                Err(TypeError::Unify(Spanned::new(a, span), b))
            }
        }
    }
}

fn insert_metas(insert: bool, term: Term, ty: VTy, span: Span, mcxt: &mut MCxt) -> (Term, VTy) {
    match ty {
        Val::Pi(Icit::Impl, arg, cl) if insert => {
            // TODO get the name here
            let meta = mcxt.new_meta(None, span);
            let vmeta = evaluate(meta.clone(), &mcxt.env(), mcxt);
            let ret = cl.apply(vmeta, mcxt);
            insert_metas(
                insert,
                Term::App(Icit::Impl, Box::new(term), Box::new(meta)),
                ret,
                span,
                mcxt,
            )
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
            Ok(insert_metas(insert, term, ty, pre.span(), mcxt))
        }
        Pre_::Lam(name, icit, ty, body) => {
            let ty = check(ty, &Val::Type, db, mcxt)?;
            let vty = evaluate(ty, &mcxt.env(), mcxt);
            // TODO Rc to get rid of the clone()?
            mcxt.define(*name, NameInfo::Local(vty.clone()), db);
            let (body, bty) = infer(true, body, db, mcxt)?;
            mcxt.undef(db);
            // TODO do we insert metas here?
            Ok((
                Term::Lam(*icit, Box::new(body)),
                Val::Pi(
                    *icit,
                    Box::new(vty),
                    // `inc()` since we're wrapping it in a lambda
                    Clos(
                        Box::new(mcxt.env()),
                        Box::new(quote(bty, mcxt.size.inc(), mcxt)),
                    ),
                ),
            ))
        }
        Pre_::Pi(name, icit, ty, ret) => {
            let ty = check(ty, &Val::Type, db, mcxt)?;
            // TODO Rc to get rid of the clone()?
            let vty = evaluate(ty.clone(), &mcxt.env(), mcxt);
            mcxt.define(*name, NameInfo::Local(vty), db);
            let ret = check(ret, &Val::Type, db, mcxt)?;
            mcxt.undef(db);
            Ok((Term::Pi(*icit, Box::new(ty), Box::new(ret)), Val::Type))
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

            let (term, ty) = match fty {
                Val::Pi(icit2, from, cl) => {
                    assert_eq!(*icit, icit2);

                    let x = check(x, &*from, db, mcxt)?;
                    // TODO Rc to get rid of the clone()?
                    let to = cl.apply(evaluate(x.clone(), &mcxt.env(), mcxt), mcxt);
                    Ok((Term::App(*icit, Box::new(f), Box::new(x)), to))
                }
                Val::Fun(from, to) => {
                    let x = check(x, &*from, db, mcxt)?;
                    Ok((Term::App(*icit, Box::new(f), Box::new(x)), *to))
                }
                // The type was already Error, so we'll leave it there, not introduce a meta
                Val::Error => Ok((Term::Error, Val::Error)),
                fty => return Err(TypeError::NotFunction(Spanned::new(fty, fspan))),
            }?;
            Ok(insert_metas(insert, term, ty, pre.span(), mcxt))
        }
        Pre_::Do(_) => todo!("elaborate do"),
        Pre_::Struct(_) => todo!("elaborate struct"),
        Pre_::Hole => Ok((
            mcxt.new_meta(None, pre.span()),
            evaluate(mcxt.new_meta(None, pre.span()), &mcxt.env(), mcxt),
        )),
    }
}

pub fn check(pre: &Pre, ty: &VTy, db: &dyn Compiler, mcxt: &mut MCxt) -> Result<Term, TypeError> {
    match (&**pre, ty) {
        (Pre_::Lam(n, i, ty, body), Val::Pi(i2, ty2, cl)) if i == i2 => {
            let vty = check(ty, &Val::Type, db, mcxt)?;
            let vty = evaluate(vty, &mcxt.env(), mcxt);
            unify(vty.clone(), (**ty2).clone(), pre.span(), db, mcxt)?;
            if mcxt.size != cl.env_size() {
                eprintln!("Warning: {:?} vs {:?}", mcxt.size, cl.env_size())
            }
            mcxt.define(*n, NameInfo::Local(vty), db);
            // TODO not clone ??
            let body = check(body, &cl.clone().vquote(mcxt), db, mcxt)?;
            mcxt.undef(db);
            Ok(Term::Lam(*i, Box::new(body)))
        }

        (Pre_::Lam(n, Icit::Expl, ty, body), Val::Fun(ty2, body_ty)) => {
            let vty = check(ty, &Val::Type, db, mcxt)?;
            let vty = evaluate(vty, &mcxt.env(), mcxt);
            unify(vty.clone(), (**ty2).clone(), pre.span(), db, mcxt)?;
            mcxt.define(*n, NameInfo::Local(vty), db);
            let body = check(body, &*body_ty, db, mcxt)?;
            mcxt.undef(db);
            Ok(Term::Lam(Icit::Expl, Box::new(body)))
        }

        // We implicitly insert lambdas so `\x.x : [a] -> a -> a` typechecks
        (_, Val::Pi(Icit::Impl, ty, cl)) => {
            // TODO should we preserve names further?
            mcxt.define(
                db.intern_name("_".to_string()),
                NameInfo::Local((**ty).clone()),
                db,
            );
            let body = check(pre, &cl.clone().vquote(mcxt), db, mcxt)?;
            Ok(Term::Lam(Icit::Impl, Box::new(body)))
        }

        _ => {
            let (term, i_ty) = infer(true, pre, db, mcxt)?;
            // TODO should we take `ty` by value?
            unify(ty.clone(), i_ty, pre.span(), db, mcxt)?;
            Ok(term)
        }
    }
}
