//! Bidirectional type checking
use crate::common::*;
use crate::elab::*;
use crate::error::*;
use crate::term::*;
use std::{
    collections::HashSet,
    ops::{Deref, DerefMut},
};

/// An error produced in type checking
#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    /// We couldn't synthesize a type for the given term
    Synth(STerm),
    ConsType(Spanned<Elab>, TypeId),
    WrongArity(usize, usize, Elab, Span),
    /// We wanted a `fun` but got a `move fun`
    MoveOnlyFun(STerm, Elab),
    /// We tried to apply the given term, but it's not a function
    /// The `Elab` here is the type, the `Term` is the argument we tried to apply it to
    NotFunction(Spanned<Elab>, Spanned<Term>),
    /// The first Elab needs to be a subtype of the second one, but it's not
    NotSubtype(Spanned<Elab>, Elab),
    /// `NotSubtype` with flipped span information
    NotSubtypeF(Elab, Spanned<Elab>),
    /// `NotSubtype(_, TypeN)`
    WrongUniverse(Spanned<Elab>, u32, u32),
    /// No match branch matched
    NoBranch(Elab, Vec<Spanned<Elab>>),
    /// We couldn't find a type for the given variable
    /// Currently, this only occurs when using bindings without a type, where we couldn't infer the type
    NotFound(Spanned<Sym>),
    /// We tried to access this field, but it's not there
    NoSuchField(Spanned<RawSym>, Elab),
    /// We tried to define a field twice in a struct
    DuplicateField(Spanned<RawSym>, Spanned<RawSym>),
}
impl TypeError {
    pub fn to_error(self, file: FileId, b: &impl HasBindings) -> Error {
        match self {
            TypeError::Synth(t) => Error::new(
                file,
                Doc::start("Type error: could not synthesize type for '")
                    .chain(t.pretty(b).style(Style::None))
                    .add("': try adding an annotation")
                    .style(Style::Bold),
                t.span(),
                "try adding an annotation here",
            ),
            TypeError::ConsType(t, id) => Error::new(
                file,
                Doc::start("Type error: invalid type for data constructor: '")
                    .chain(t.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                t.span(),
                Doc::start("allowed types are '")
                    .chain(id.pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(
                        Doc::start("fun")
                            .style(Style::Keyword)
                            .space()
                            .add("...")
                            .space()
                            .add("=>")
                            .space()
                            .chain(id.pretty(b))
                            .style(Style::None),
                    )
                    .style(Style::Note),
            ),
            TypeError::MoveOnlyFun(f, ty) => Error::new(
                file,
                Doc::start("Type error: expected copiable function '")
                    .chain(ty.unbind().pretty(b).style(Style::None).group())
                    .add("', found move-only function")
                    .style(Style::Bold),
                f.span(),
                Doc::start("try removing this ")
                    .chain(Doc::start("move").style(Style::Keyword))
                    .style(Style::Note),
            ),
            TypeError::NotFunction(f, x) => Error::new(
                file,
                Doc::start("Type error: not a function: '")
                    .chain(f.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                f.span(),
                Doc::start("this was applied to '")
                    .chain(x.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::WrongArity(expected, found, ty, span) => Error::new(
                file,
                Doc::start("Type error: mismatched arity: expected function with ")
                    .add(expected)
                    .add(if expected == 1 {
                        " parameter"
                    } else {
                        " parameters"
                    })
                    .add(", found function with ")
                    .add(found)
                    .add(if found == 1 {
                        " parameter"
                    } else {
                        " parameters"
                    })
                    .style(Style::Bold),
                span,
                Doc::start("expected type '")
                    .chain(ty.unbind().pretty(b).style(Style::None))
                    .add("' with ")
                    .add(expected)
                    .add(if expected == 1 {
                        " parameter"
                    } else {
                        " parameters"
                    }),
            ),
            TypeError::WrongUniverse(sub, m, n) => Error::new(
                file,
                Doc::start("Type error: type '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("' is not in universe ")
                    .add(n)
                    .add(" and so is not a subtype of Type")
                    .add(n)
                    .style(Style::Bold),
                sub.span(),
                Doc::start("this has type '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("', which is in universe ")
                    .add(m),
            ),
            TypeError::NotSubtype(sub, sup) => Error::new(
                file,
                Doc::start("Type error: could not match types '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                sub.span(),
                Doc::start("this has type '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::NotSubtypeF(sub, sup) => Error::new(
                file,
                Doc::start("Type error: could not match types '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                sup.span(),
                Doc::start("this has type '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::NotFound(s) => Error::new(
                file,
                Doc::start("Type error: could not find type for variable: '")
                    .chain(s.pretty(b))
                    .add("'")
                    .style(Style::Bold),
                s.span(),
                format!("type not found"),
            ),
            TypeError::NoSuchField(s, v) => Error::new(
                file,
                Doc::start("Type error: no such field '")
                    .chain(s.pretty(b))
                    .add("' on struct type '")
                    .chain(v.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                s.span(),
                format!("no such field"),
            ),
            TypeError::DuplicateField(x, y) => Error::new(
                file,
                Doc::start("Type error: multiple definitions of variable '")
                    .chain(x.pretty(b))
                    .add("' in struct or module")
                    .style(Style::Bold),
                x.span(),
                format!("first defined here"),
            )
            .with_label(file, y.span(), format!("redefined here")),
            TypeError::NoBranch(sub, sups) => {
                let mut e = Error::no_label(
                    Doc::start("Type error: no branch matched the type '")
                        .chain(sub.unbind().pretty(b).style(Style::None))
                        .add("'")
                        .style(Style::Bold),
                );
                for branch in sups {
                    e = e.with_label(
                        file,
                        branch.span(),
                        Doc::start("This branch has type '")
                            .chain(branch.unbind().pretty(b).style(Style::None))
                            .add("'")
                            .style(Style::Note)
                            .ansi_string(),
                    );
                }
                e
            }
        }
    }
}

pub enum Constraint {
    Subtype(Elab, Elab),
}
impl Constraint {
    pub fn cloned(&self, cln: &mut Cloner) -> Constraint {
        match self {
            Constraint::Subtype(a, b) => Constraint::Subtype(a.cloned(cln), b.cloned(cln)),
        }
    }
}

#[derive(Clone)]
pub struct TCtx<'a> {
    pub tys: HashMap<Sym, Arc<Elab>>,
    cons: Vec<(Span, Arc<Constraint>)>,
    pub metas: HashSet<Sym>,
    pub ectx: ECtx<'a>,
}
impl<'a> From<ECtx<'a>> for TCtx<'a> {
    fn from(ectx: ECtx<'a>) -> Self {
        TCtx {
            tys: HashMap::new(),
            cons: Vec::new(),
            metas: HashSet::new(),
            ectx,
        }
    }
}
impl<'a> TCtx<'a> {
    pub fn solve_constraints(&mut self) -> Result<(), TypeError> {
        for (span, c) in self.cons.split_off(0) {
            match &*c {
                Constraint::Subtype(a, b) => {
                    let mut cons = Vec::new();
                    if a.unify(b, self, &mut cons) {
                        self.apply_metas(cons);
                    } else {
                        return Err(TypeError::NotSubtype(
                            Spanned::new(a.cloned(&mut Cloner::new(self)), span),
                            b.cloned(&mut Cloner::new(self)),
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    pub fn apply_metas(&mut self, metas: impl IntoIterator<Item = (Sym, Elab)>) {
        for (k, v) in metas {
            #[cfg(feature = "logging")]
            eprintln!(
                "Meta {} := {}",
                k.pretty(self).ansi_string(),
                v.pretty(self).ansi_string()
            );

            if self.vals.contains_key(&k) {
                panic!("Meta {} already defined", k.pretty(self).ansi_string());
            }

            self.metas.remove(&k);
            self.set_val(k, v);
        }
    }

    pub fn new(db: &'a (impl Scoped + HasDatabase)) -> Self {
        TCtx {
            tys: HashMap::new(),
            cons: Vec::new(),
            metas: HashSet::new(),
            ectx: ECtx::new(db),
        }
    }

    pub fn ty(&self, k: Sym) -> Option<Arc<Elab>> {
        self.tys.get(&k).cloned().or_else(|| {
            self.database()
                .elab(self.scope(), k)
                .map(|x| Arc::new(x.get_type(self)))
        })
    }
    pub fn set_ty(&mut self, k: Sym, v: Elab) {
        self.tys.insert(k, Arc::new(v));
    }
}
impl<'a> Scoped for TCtx<'a> {
    fn scope(&self) -> ScopeId {
        self.ectx.scope()
    }
}
impl<'a> HasBindings for TCtx<'a> {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.database().bindings_ref()
    }
}
impl<'a> HasDatabase for TCtx<'a> {
    fn database(&self) -> &dyn MainGroupP {
        self.ectx.database()
    }
}
impl<'a> Deref for TCtx<'a> {
    type Target = ECtx<'a>;
    fn deref(&self) -> &ECtx<'a> {
        &self.ectx
    }
}
impl<'a> DerefMut for TCtx<'a> {
    fn deref_mut(&mut self) -> &mut ECtx<'a> {
        &mut self.ectx
    }
}

/// Attempts to come up with a type for a term, returning the elaborated term
pub fn synth(t: &STerm, tctx: &mut TCtx) -> Result<Elab, TypeError> {
    #[cfg(feature = "logging")]
    println!("synth ({})", t.pretty(tctx).ansi_string());

    match &**t {
        Term::Type(i) => Ok(Elab::Type(*i)),
        Term::Builtin(b) => Ok(Elab::Builtin(*b)),
        Term::Var(x) => {
            let ty = tctx
                .ty(*x)
                .map(|x| x.cloned(&mut Cloner::new(&tctx)))
                .ok_or_else(|| TypeError::NotFound(t.copy_span(*x)))?
                .whnf(tctx);
            Ok(Elab::Var(t.span(), *x, Box::new(ty)))
        }
        Term::I32(i) => Ok(Elab::I32(*i)),
        Term::Unit => Ok(Elab::Unit),
        Term::Pair(x, y) => {
            // TODO I don't think this covers dependent pairs
            let x = synth(x, tctx)?;
            let y = synth(y, tctx)?;
            Ok(Elab::Pair(Box::new(x), Box::new(y)))
        }
        Term::Struct(id, iv) => {
            if tctx.tys.keys().any(|k| t.uses(*k)) {
                // If it captures local variables, we compile in "struct mode"
                // TODO a note in "not found" error messages here that structs that capture variables are ordered
                let mut rv = Vec::new();
                for (k, v) in iv {
                    let v = synth(v, tctx)?;
                    let t = v.get_type(tctx);
                    tctx.set_ty(**k, t);
                    rv.push((**k, v));
                }

                Ok(Elab::StructInline(rv))
            } else {
                // Otherwise, compile in Salsa-enabled "module mode"
                let scope = ScopeId::Struct(*id, Box::new(tctx.scope()));
                tctx.database().add_mod(*id, tctx.scope().file(), iv);

                // Record any type errors inside the module
                for sym in tctx.database().symbols(scope.clone()).iter() {
                    tctx.database().elab(scope.clone(), **sym);
                }

                Ok(Elab::StructIntern(*id))
            }
        }
        Term::Data(tid, sid, ty, cons) => {
            let scope = ScopeId::Struct(*sid, Box::new(tctx.scope()));
            tctx.database().add_mod(
                *sid,
                tctx.scope().file(),
                &cons
                    .iter()
                    .map(|(k, id, t)| (k.clone(), k.copy_span(Term::Cons(*id, t.clone()))))
                    .collect(),
            );

            // Record any type errors in data constructors
            // for sym in tctx.database().symbols(scope.clone()).iter() {
            //     tctx.database().elab(scope.clone(), **sym);
            // }

            let ty = synth(ty, tctx)?;

            Ok(Elab::Data(*tid, *sid, Box::new(ty)))
        }
        Term::Cons(id, ty) => {
            let ty_span = ty.span();
            let mut ty = synth(ty, tctx)?.whnf(tctx);
            let did = tctx.bindings().tag_to_type(*id).unwrap();
            match &mut ty {
                // TODO `Pair a`
                Elab::Data(did2, _, _) if *did2 == did => (),
                Elab::Fun(_, _, v, _) if v.len() == 1 => {
                    let (a, b) = v.pop().unwrap();
                    let b = b.whnf(tctx);
                    v.push((a, b));
                    match &v[0].1.head() {
                        Elab::Data(did2, _, _) if *did2 == did => (),
                        _ => return Err(TypeError::ConsType(Spanned::new(ty, ty_span), did)),
                    }
                }
                _ => return Err(TypeError::ConsType(Spanned::new(ty, ty_span), did)),
            };
            Ok(Elab::Cons(*id, Box::new(ty)))
        }
        Term::App(fi, x) => {
            let f = synth(fi, tctx)?;
            let x = match f.get_type(tctx) {
                Elab::Fun(cl, _, v, _) => {
                    tctx.add_clos(&cl);
                    // We check the argument against a union of first parameter types across all branches
                    let from: Vec<_> = v.into_iter().map(|(mut x, _)| x.remove(0)).collect();
                    let from = Elab::Union(from).whnf(tctx).simplify_unions(tctx);
                    match check(x, &from, tctx) {
                        Ok(x) => x,
                        Err(e) => {
                            // We allow narrowing data constructors to subtypes of their arguments, e.g. in patterns
                            // So we allow you to apply it to a subtype of its arguments
                            let head = f.head().cloned(&mut Cloner::new(tctx)).whnf(tctx);
                            if let Elab::Cons(_, _) = head {
                                let x = synth(x, tctx)?;
                                if x.subtype_of(&from, tctx) {
                                    x
                                } else {
                                    return Err(e);
                                }
                            } else {
                                return Err(e);
                            }
                        }
                    }
                }
                Elab::Bottom => synth(x, tctx)?,
                a => {
                    return Err(TypeError::NotFunction(
                        fi.copy_span(a.cloned(&mut Cloner::new(&tctx))),
                        x.clone(),
                    ))
                }
            };
            Ok(Elab::App(Box::new(f), Box::new(x)))
        }
        Term::Project(r, m) => {
            let r = synth(r, tctx)?;
            let rt = r.get_type(tctx);
            match &r.get_type(tctx) {
                Elab::StructInline(v) => {
                    if let Some((_, val)) = v.iter().find(|(name, _)| name.raw() == **m) {
                        val.cloned(&mut Cloner::new(&tctx))
                    } else {
                        return Err(TypeError::NoSuchField(
                            m.clone(),
                            rt.cloned(&mut Cloner::new(&tctx)),
                        ));
                    }
                }
                _ => match r.whnf(tctx) {
                    Elab::Data(_, id, _) => {
                        for s in tctx
                            .database()
                            .symbols(ScopeId::Struct(id, Box::new(tctx.scope())))
                            .iter()
                        {
                            if s.raw() == **m {
                                if let Some(e) = tctx
                                    .database()
                                    .elab(ScopeId::Struct(id, Box::new(tctx.scope())), **s)
                                {
                                    return Ok(e.cloned(&mut Cloner::new(tctx)));
                                } else {
                                    break;
                                }
                            }
                        }
                        return Err(TypeError::NoSuchField(
                            m.clone(),
                            rt.cloned(&mut Cloner::new(&tctx)),
                        ));
                    }
                    _ => {
                        return Err(TypeError::NoSuchField(
                            m.clone(),
                            rt.cloned(&mut Cloner::new(&tctx)),
                        ))
                    }
                },
            };
            Ok(Elab::Project(Box::new(r), **m))
        }
        Term::Fun(m, iv) => {
            let mut rv = Vec::new();
            let mut rt = Vec::new();
            let mut rxs = Vec::new();
            let mut cln = Cloner::new(tctx);
            for (xs, y) in iv {
                while rxs.len() < xs.len() {
                    rxs.push(Vec::new());
                }
                let mut rx = Vec::new();
                for (x, tx) in xs.into_iter().zip(rxs.iter_mut()) {
                    // Make sure it's well typed before reducing it
                    let x = synth(x, tctx)?.whnf(tctx);
                    // Match it with itself to apply the types
                    x.match_types(&x, tctx);

                    tx.push(x.cloned(&mut cln));

                    rx.push(x);
                }

                let y = synth(y, tctx)?;
                // get_type() should always produce WHNF, so we don't need whnf() here
                let to = y.get_type(tctx);

                rt.push(to.cloned(&mut cln));
                rv.push((rx, y));
            }
            Ok(Elab::Fun(
                tctx.clos(t, *m),
                rxs.into_iter()
                    .map(|x| Elab::Union(x).simplify_unions(tctx))
                    .collect(),
                rv,
                Box::new(Elab::Union(rt).simplify_unions(tctx)),
            ))
        }
        Term::Block(v) => {
            let mut rv = Vec::new();
            for i in 0..v.len() {
                match &v[i] {
                    Statement::Expr(t) => {
                        if i + 1 != v.len() {
                            rv.push(ElabStmt::Expr(check(t, &Elab::Unit, tctx)?));
                        } else {
                            // last value
                            rv.push(ElabStmt::Expr(synth(t, tctx)?));
                        }
                    }
                    Statement::Def(Def(name, val)) => {
                        let val = synth(val, tctx)?;
                        let ty = val.get_type(tctx);
                        tctx.set_ty(**name, ty);
                        // Blocks can be dependent!
                        let val2 = val.cloned(&mut Cloner::new(&tctx)).whnf(tctx);
                        tctx.set_val(**name, val2);
                        rv.push(ElabStmt::Def(**name, val));
                    }
                }
            }
            Ok(Elab::Block(rv))
        }
        Term::The(ty, u) => {
            // Make sure it's well typed before reducing it
            let ty = synth(ty, tctx)?.whnf(tctx);
            let ue = check(u, &ty, tctx)?;
            Ok(ue)
        }
        Term::Binder(x, Some(ty)) => {
            let ty = synth(ty, tctx)?.whnf(tctx);
            // TODO switch to this everywhere instead of match_types(self)
            tctx.set_ty(*x, ty.cloned(&mut Cloner::new(tctx)));
            Ok(Elab::Binder(*x, Box::new(ty)))
        }
        Term::Binder(x, None) => Ok(Elab::Binder(*x, Box::new(Elab::Top))),
        Term::Union(iv) => {
            let mut rv = Vec::new();
            for val in iv {
                let val = synth(val, tctx)?;
                rv.push(val);
            }
            Ok(Elab::Union(rv).simplify_unions(tctx))
        }
        _ => Err(TypeError::Synth(t.clone())),
    }
}

/// Checks the given term against the given type, returning the elaborated term
pub fn check(term: &STerm, typ: &Elab, tctx: &mut TCtx) -> Result<Elab, TypeError> {
    #[cfg(feature = "logging")]
    {
        println!(
            "check ({}) :: ({})",
            term.pretty(tctx).ansi_string(),
            typ.pretty(tctx).ansi_string(),
        );
    }

    match (&**term, typ) {
        (Term::Pair(x, y), Elab::Pair(tx, ty)) => {
            let mut cln = Cloner::new(tctx);
            let (tx, ty) = (tx.cloned(&mut cln).whnf(tctx), ty.cloned(&mut cln).whnf(tctx));
            // TODO dependent pairs don't really work
            check(x, &tx, tctx)?;
            check(y, &ty, tctx)
        }

        // As far as we know, it could be any type
        (Term::Binder(s, None), _) /*if typ.subtype_of(&Elab::Type, &mut tctx.clone())*/ => {
            // As far as we know, it could be anything, so it's `Top`
            // We'll narrow it down with `update_binders()` later, if we can
            Ok(Elab::Binder(*s, Box::new(Elab::Top)))
        }

        (Term::Fun(m, v), Elab::Fun(cl, _, v2, _)) => {
            if *m && !cl.is_move {
                return Err(TypeError::MoveOnlyFun(term.clone(), typ.cloned(&mut Cloner::new(tctx))));
            }

            tctx.add_clos(cl);
            let mut cln = Cloner::new(tctx);
            let mut v2: Vec<_> = v2
                .iter()
                .map(|(x, y)| {
                    (
                        x.iter().map(|x| x.cloned(&mut cln)).collect::<Vec<_>>(),
                        y.cloned(&mut cln),
                    )
                })
                .collect();
            let mut v = v.clone();

            // To propagate a type error out of several nested closures
            let mut error: Option<TypeError> = None;
            // If the value has more parameters than the type, we curry the result type into the function type
            while v[0].0.len() > v2[0].0.len() {
                v2 = v2
                    .into_iter()
                    .flat_map(|(mut arg, body)| {
                        let body = body.whnf(tctx);
                        match body {
                            Elab::Fun(cl, _, v3, _) => {
                                tctx.add_clos(&cl);
                                v3
                                    .into_iter()
                                    .map(|(mut from, to)| {
                                        arg.append(&mut from);
                                        (
                                            arg.iter().map(|x| x.cloned(&mut cln)).collect(),
                                            to.cloned(&mut cln),
                                        )
                                    })
                                    .collect::<Vec<_>>()
                            }
                            _ => {
                                error = Some(TypeError::WrongArity(
                                    arg.len(),
                                    v[0].0.len(),
                                    typ.cloned(&mut cln),
                                    term.span(),
                                ));
                                Vec::new()
                            }
                        }
                    })
                    .collect();
                if error.is_some() {
                    break;
                }
            }
            if let Some(e) = error {
                return Err(e);
            }

            // If the type has more parameters than the value, we add an extra parameter and apply it to the body
            // `f : fun Int => Int = id Int` --> `f : fun Int => Int = fun x: => id Int x`
            // We store the arity before this transformation for error messages
            let initial_arity = v[0].0.len();
            while v[0].0.len() < v2[0].0.len() {
                for (arg, body) in &mut v {
                    let extra_param = tctx.bindings_mut().create("$curry".to_string());
                    arg.push(
                        arg.last()
                            .unwrap()
                            .copy_span(Term::Binder(extra_param, None)),
                    );
                    *body = body.copy_span(Term::App(
                        body.clone(),
                        arg.last().unwrap().copy_span(Term::Var(extra_param)),
                    ));
                }
            }
            debug_assert_eq!(v[0].0.len(), v2[0].0.len());

            let mut total_from = Vec::new();
            let mut total_to = Vec::new();
            for (from, to) in &v2 {
                // Accumulate overall argument and result types
                while total_from.len() < from.len() {
                    total_from.push(Vec::new());
                }
                for (i, v) in from.iter().zip(total_from.iter_mut()) {
                    v.push(i.cloned(&mut cln));
                }
                total_to.push(to.cloned(&mut cln));
            }

            // If the type has parameters with union types, flatten them into function branches so we can match more easily
            let v2: Vec<(Vec<Elab>, Elab, Option<Vec<(Sym, Elab)>>)> = v2
                .into_iter()
                .flat_map(|(from, to)| {
                    from.into_iter()
                        .map(|from| match from {
                            Elab::Union(v) => v.into_iter().map(|x| (x, None)).collect(),
                            // TODO better narrowing of GADTs based on type
                            Elab::App(_, _) | Elab::Data(_, _, _) => match from.head() {
                                Elab::Data(_, sid, _) => {
                                    let scope = ScopeId::Struct(*sid, Box::new(tctx.scope()));
                                    tctx.database()
                                        .symbols(scope.clone())
                                        .iter()
                                        .filter_map(|x| tctx.database().elab(scope.clone(), **x))
                                        .collect::<Vec<_>>()
                                        .into_iter()
                                        .filter_map(|cons| match cons.get_type(tctx) {
                                            Elab::Fun(_, _, mut v, _) => {
                                                if let Elab::Cons(_, _) = &*cons {

                                                } else {
                                                    panic!("not a constructor")
                                                };
                                                assert_eq!(v.len(), 1);
                                                let (args, result) = v.pop().unwrap();
                                                let mut tcons = Vec::new();
                                                let mut tctx = tctx.clone();
                                                tctx.metas.extend(from.fvs(&tctx));
                                                let mut cln = Cloner::new(&tctx);
                                                let cons = cons.cloned(&mut cln);
                                                let result = result.cloned(&mut cln);
                                                tctx.metas.extend(result.fvs(&tctx));
                                                if result.unify(&from, &tctx, &mut tcons) {
                                                    // [a, b, c]
                                                    // -> App(App(App(Cons(_), a), b), c)
                                                    Some((args
                                                        .into_iter()
                                                        .fold(cons, |f, x| Elab::App(Box::new(f), Box::new(x))), Some(tcons)))
                                                } else {
                                                    eprintln!("Skipping constructor {}: {} vs {}", cons.pretty(&tctx).ansi_string(), result.pretty(&tctx).ansi_string(), from.pretty(&tctx).ansi_string());
                                                    None
                                                }
                                            }
                                            t if t.overlap(&from, tctx) => Some((cons.cloned(&mut Cloner::new(tctx)), None)),
                                            _ => None,
                                        })
                                        .collect()
                                }
                                _ => vec![(from, None)],
                            }
                            from => vec![(from, None)],
                        })
                        //    fun (x:) (A | B) => x
                        // -> cases[[]], arg_cases[[x:], [A, B]]
                        // -> cases[[x2:]], arg_cases[[A, B]]
                        // -> cases[[x3:, A], [x4:, B]], arg_cases[]
                        // -> fun { x2: A => x3, x3: B => x3 }
                        .fold(vec![(Cloner::new(tctx), Vec::new(), None)], |cases: Vec<(Cloner, Vec<Elab>, Option<Vec<(Sym, Elab)>>)>, arg_cases: Vec<(Elab, Option<Vec<(Sym, Elab)>>)>| {
                            cases
                                .into_iter()
                                .flat_map(|(cln, x, v)| {
                                    arg_cases
                                        .iter()
                                        .map(|(y, v2)| {
                                            let mut cln = cln.clone();
                                            let mut x: Vec<_> =
                                                x.iter().map(|x| x.cloned(&mut cln)).collect();
                                            x.push(y.cloned(&mut cln));
                                            let v = if v.is_some() || v2.is_some() {
                                                Some(v.iter().chain(v2).flatten().map(|(k, v)| (cln.get(*k), v.cloned(&mut cln))).collect())
                                            } else {
                                                None
                                            };
                                            (cln, x, v)
                                        })
                                        .collect::<Vec<_>>()
                                })
                                .collect()
                        })
                        .into_iter()
                        .map(|(mut cln, x, v)| (x, to.cloned(&mut cln), v))
                        .collect::<Vec<_>>()
                })
                .collect();

            // Start by typechecking all parameters of all branches and marking them as not used yet
            let mut unused = Vec::new();
            for (args, body) in v {
                let mut ra = Vec::new();
                for a in args {
                    let e = synth(&a, tctx)?.whnf(tctx);
                    ra.push((e, a.span()));
                }
                unused.push((ra, body));
            }

            // Only put the branches we need based on the type in `used`
            let mut used: Vec<(Vec<(Elab, Span)>, Elab)> = Vec::new();
            // let mut total_from = Vec::new();
            // let mut total_to = Vec::new();
            for (from, to, metas) in v2 {
                // Accumulate overall argument and result types
                // while total_from.len() < from.len() {
                //     total_from.push(Vec::new());
                // }
                // for (i, v) in from.iter().zip(total_from.iter_mut()) {
                //     v.push(i.cloned(&mut cln));
                // }
                // total_to.push(to.cloned(&mut cln));

                let mut tctx = tctx.clone();
                if let Some(metas) = metas {
                    tctx.apply_metas(metas);
                }
                let mut errors: Vec<Vec<Spanned<Elab>>> =
                    (0..from.len()).map(|_| Vec::new()).collect();

                // Try the branches we already used first - they're higher priority
                let mut passed = false;
                for (args, _) in used.iter() {
                    let mut all_subtype = true;
                    // Go through the curried parameters and make sure each one matches
                    for ((i, f), (a, span)) in from.iter().enumerate().zip(args) {
                        if !f.subtype_of(&a, &mut tctx) {
                            errors[i].push(Spanned::new(a.cloned(&mut Cloner::new(&tctx)), *span));
                            all_subtype = false;
                            break;
                        }
                    }
                    if all_subtype {
                        passed = true;
                        break;
                    }
                }
                if passed {
                    continue;
                }

                // Now try the unused branches
                // We'll put any ones that didn't here and replace unused with it at the end
                let mut unused_next = Vec::new();
                let mut passed = false;
                for (args, body) in unused {
                    if passed {
                        unused_next.push((args, body));
                        continue;
                    }
                    let mut all_subtype = true;
                    let mut all_overlap = true;
                    let mut ra = Vec::new();
                    // Go through the curried parameters and make sure each one matches
                    for ((i, f), (mut a, span)) in from.iter().enumerate().zip(args) {
                        if !all_overlap {
                        } else if f.subtype_of(&a, &mut tctx){
                            // Update the types of binders in `xr` based on the type `y`
                            a.update_binders(f, &mut Cloner::new(&tctx));
                            // Add bindings in the argument to the context with types given by `y`
                            a.match_types(f, &mut tctx);
                            a = a.whnf(&mut tctx);
                        } else if f.overlap(&a, &tctx) {
                            // Still record the error in case nothing is a true subtype
                            errors[i].push(Spanned::new(a.cloned(&mut Cloner::new(&tctx)), span));
                            // Update the types of binders in `xr` based on the type `y`
                            a.update_binders(f, &mut Cloner::new(&tctx));
                            // Add bindings in the argument to the context with types given by `y`
                            a.match_types(f, &mut tctx);
                            a = a.whnf(&mut tctx);
                            all_subtype = false;
                        } else {
                            errors[i].push(Spanned::new(a.cloned(&mut Cloner::new(&tctx)), span));
                            all_subtype = false;
                            all_overlap = false;
                        }
                        ra.push((a, span));
                    }
                    if all_subtype {
                        passed = true;
                        // If all the parameters matched, this branch of the type is covered, so no errors yet
                        errors = Vec::new();
                    }
                    if all_overlap {
                        let to = to.cloned(&mut Cloner::new(&tctx)).whnf(&mut tctx);
                        let body = match check(&body, &to, &mut tctx) {
                            Ok(x) => x,
                            Err(TypeError::NotFunction(f, x)) => match &*x {
                                // We added a parameter for currying, but it didn't work
                                Term::Var(s) if tctx.bindings().resolve(*s) == "$curry" => return Err(TypeError::WrongArity(
                                    from.len(),
                                    initial_arity,
                                    typ.cloned(&mut cln),
                                    term.span(),
                                )),
                                _ => return Err(TypeError::NotFunction(f, x)),
                            }
                            Err(e) => return Err(e),
                        };

                        used.push((ra, body));
                    } else {
                        unused_next.push((ra, body));
                    }
                }
                unused = unused_next;

                for (i, v) in errors.into_iter().enumerate() {
                    if !v.is_empty() {
                        return Err(TypeError::NoBranch(from[i].cloned(&mut cln), v));
                    }
                }
            }
            // TODO give a warning if there's anything left in `unused`

            Ok(Elab::Fun(
                tctx.clos(term, *m),
                total_from.into_iter().map(|x| Elab::Union(x).simplify_unions(tctx)).collect(),
                used.into_iter()
                    .map(|(a, b)| (a.into_iter().map(|(x, _)| x).collect(), b))
                    .collect(),
                Box::new(Elab::Union(total_to).simplify_unions(tctx))
            )
                // Make sure the closure is updated
                .whnf(tctx))
        }
        (_, _) => {
            let t = synth(term, tctx)?;
            let ty = t.get_type(tctx);
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&typ, &mut tctx.clone()) {
                Ok(t)
            } else {
                match typ.unbind() {
                    Elab::Type(i) => Err(TypeError::WrongUniverse(
                        term.copy_span(ty.cloned(&mut Cloner::new(&tctx))),
                        ty.universe(tctx) - 1,
                        *i,
                    )),
                    _ => Err(TypeError::NotSubtype(
                        term.copy_span(ty.cloned(&mut Cloner::new(&tctx))),
                        typ.cloned(&mut Cloner::new(&tctx)),
                    )),
                }
            }
        }
    }
}

impl Elab {
    fn update_binders(&mut self, other: &Elab, cln: &mut Cloner) {
        use Elab::*;
        match (&mut *self, other) {
            // We don't want `x:y:T`, and we already called match_types()
            (_, Binder(_, t)) => {
                self.update_binders(t, cln);
            }
            (Binder(_, t), _) => {
                **t = other.cloned(cln);
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.update_binders(bx, cln);
                ay.update_binders(by, cln);
            }
            (App(af, ax), App(bf, bx)) => {
                af.update_binders(bf, cln);
                ax.update_binders(bx, cln);
            }
            _ => (),
        }
    }

    /// Like do_match(), but fills in the types instead of Elabs
    pub fn match_types(&self, other: &Elab, tctx: &mut TCtx) {
        use Elab::*;
        match (self, other) {
            // Since we match it against itself to apply binder types
            (Binder(na, _), Binder(nb, t)) if na == nb => {
                #[cfg(feature = "logging")]
                {
                    println!(
                        "tctx: {} : {}",
                        self.pretty(tctx).ansi_string(),
                        t.pretty(tctx).ansi_string()
                    );
                }

                let t = t.cloned(&mut Cloner::new(&tctx));
                tctx.set_ty(*na, t);
            }
            // This happens with GADTs - we know the binder has this value if this branch matched, but we need to propagate it
            // (_, Binder(s, _)) if tctx.val(*s).is_some() => {
            //     let v = tctx.val(*s).unwrap();
            //     self.do_match(&v, tctx);
            // }
            (Binder(s, t), _) => {
                #[cfg(feature = "logging")]
                {
                    println!(
                        "type: {} : {}",
                        self.pretty(tctx).ansi_string(),
                        other.pretty(tctx).ansi_string()
                    );
                }

                // For alpha-equivalence - we need symbols in our body to match symbols in the other body if they're defined as the same
                other.do_match(
                    &Var(
                        Span::empty(),
                        *s,
                        Box::new(t.cloned(&mut Cloner::new(&tctx))),
                    ),
                    &mut tctx.ectx,
                );

                let other = other.cloned(&mut Cloner::new(&tctx));
                tctx.set_ty(*s, other);
            }
            (Var(_, x, _), _) => {
                if let Some(x) = tctx.val(*x) {
                    x.match_types(other, tctx);
                }
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.match_types(bx, tctx);
                ay.match_types(by, tctx);
            }
            (App(af, ax), App(bf, bx)) => {
                af.match_types(bf, tctx);
                ax.match_types(bx, tctx);
            }
            _ => (),
        }
    }

    pub fn alpha_match(&self, other: &Elab, ectx: &mut ECtx) {
        use Elab::*;
        match (self, other) {
            (Binder(s, t), _) => {
                // For alpha-equivalence - we need symbols in our body to match symbols in the other body if they're defined as the same
                other.do_match(
                    &Var(
                        Span::empty(),
                        *s,
                        Box::new(t.cloned(&mut Cloner::new(&ectx))),
                    ),
                    ectx,
                );
            }
            (Var(_, x, _), _) => {
                if let Some(x) = ectx.val(*x) {
                    x.alpha_match(other, ectx);
                }
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.alpha_match(bx, ectx);
                ay.alpha_match(by, ectx);
            }
            (App(af, ax), App(bf, bx)) => {
                af.alpha_match(bf, ectx);
                ax.alpha_match(bx, ectx);
            }
            _ => (),
        }
    }

    /// Could this be a subtype of `sup`? What metavariable assignments would be necessary?
    pub fn unify(&self, sup: &Elab, tctx: &TCtx, cons: &mut Vec<(Sym, Elab)>) -> bool {
        match (self, sup) {
            (Elab::Bottom, _) => true,
            (_, Elab::Top) => true,
            (Elab::I32(n), Elab::I32(m)) => n == m,
            (Elab::I32(_), Elab::Builtin(Builtin::Int)) => true,
            (Elab::StructInline(sub), Elab::StructInline(sup)) => {
                // We DON'T do record subtyping, that's confusing and hard to compile efficiently
                sup.iter().all(|(n, sup)| sub.iter().find(|(n2, _)| n2.raw() == n.raw()).map_or(false, |(_, sub)| sub.unify(sup, tctx, cons)))
                    // so make sure there aren't any extra fields
                    && sub.iter().all(|(n, _)| sup.iter().any(|(n2, _)| n2.raw() == n.raw()))
            }
            (Elab::StructIntern(id), _) => ScopeId::Struct(*id, Box::new(tctx.scope()))
                .inline(tctx)
                .unify(sup, tctx, cons),
            (_, Elab::StructIntern(id)) => self.unify(
                &ScopeId::Struct(*id, Box::new(tctx.scope())).inline(tctx),
                tctx,
                cons,
            ),
            (Elab::Builtin(b), Elab::Builtin(c)) if b == c => true,
            (Elab::Unit, Elab::Unit) => true,
            // Two variables that haven't been resolved yet, but refer to the same definition
            (Elab::Var(_, x, _), Elab::Var(_, y, _)) if y == x => true,
            (Elab::Var(_, x, _), _) if tctx.database().elab(tctx.scope(), *x).is_some() => tctx
                .database()
                .elab(tctx.scope(), *x)
                .unwrap()
                .cloned(&mut Cloner::new(tctx))
                .unify(sup, tctx, cons),
            (_, Elab::Var(_, x, _)) if tctx.database().elab(tctx.scope(), *x).is_some() => self
                .unify(
                    &tctx
                        .database()
                        .elab(tctx.scope(), *x)
                        .unwrap()
                        .cloned(&mut Cloner::new(tctx)),
                    tctx,
                    cons,
                ),
            (Elab::Var(_, x, _), _) if tctx.vals.contains_key(x) => tctx
                .val(*x)
                .unwrap()
                .cloned(&mut Cloner::new(tctx))
                .unify(sup, tctx, cons),
            (_, Elab::Var(_, x, _)) if tctx.vals.contains_key(x) => self.unify(
                &tctx.val(*x).unwrap().cloned(&mut Cloner::new(tctx)),
                tctx,
                cons,
            ),
            (Elab::Var(_, x, _), _) if cons.iter().any(|(k, _)| k == x) => {
                let mut tcons = Vec::new();
                let b = cons
                    .iter()
                    .find(|(k, _)| k == x)
                    .unwrap()
                    .1
                    .unify(sup, tctx, &mut tcons);
                cons.append(&mut tcons);
                b
            }
            (_, Elab::Var(_, x, _)) if cons.iter().any(|(k, _)| k == x) => {
                let mut tcons = Vec::new();
                let b = self.unify(
                    &cons.iter().find(|(k, _)| k == x).unwrap().1,
                    tctx,
                    &mut tcons,
                );
                cons.append(&mut tcons);
                b
            }
            // Solve metavariables
            (Elab::Var(_, s, _), x) | (x, Elab::Var(_, s, _)) if tctx.metas.contains(s) => {
                cons.push((*s, x.cloned(&mut Cloner::new(tctx))));
                true
            }
            (Elab::App(f1, x1), Elab::App(f2, x2)) => {
                f1.unify(f2, tctx, cons) && x1.unify(x2, tctx, cons)
            }
            (Elab::Pair(ax, ay), Elab::Pair(bx, by)) => {
                ax.unify(bx, tctx, cons) && ay.unify(by, tctx, cons)
            }
            // (Type -> (Type, Type)) <: ((Type, Type) -> Type)
            // `fun` <: `move fun`
            (
                Elab::Fun(cl_a @ Clos { is_move: false, .. }, _, v_sub, _),
                Elab::Fun(cl_b @ Clos { is_move: false, .. }, _, v_sup, _),
            )
            | (
                Elab::Fun(cl_a, _, v_sub, _),
                Elab::Fun(cl_b @ Clos { is_move: true, .. }, _, v_sup, _),
            ) => {
                let mut tctx = tctx.clone();
                tctx.add_clos(cl_a);
                tctx.add_clos(cl_b);
                for (args_sup, to_sup) in v_sup.iter() {
                    let mut found = false;
                    for (args_sub, to_sub) in v_sub.iter() {
                        let mut tcons = Vec::new();
                        let mut all_subtype = true;
                        for (sup, sub) in args_sup.iter().zip(args_sub.iter()) {
                            // Function parameters are contravariant
                            if !sup.unify(sub, &tctx, &mut tcons) {
                                all_subtype = false;
                                break;
                            }
                            // Matching in either direction works, we have to check alpha equality
                            sub.alpha_match(sup, &mut tctx);
                        }

                        if !all_subtype {
                            break;
                        }

                        // Since types are only in weak-head normal form, we have to reduce the spines to compare them
                        let to_sup = to_sup.cloned(&mut Cloner::new(&tctx)).whnf(&mut tctx);
                        let to_sub = to_sub.cloned(&mut Cloner::new(&tctx)).whnf(&mut tctx);

                        if to_sub.unify(&to_sup, &tctx, &mut tcons) {
                            found = true;
                            cons.append(&mut tcons);
                            break;
                        }
                    }
                    if !found {
                        return false;
                    }
                }
                return true;
            }
            (Elab::Data(a, _, _), Elab::Data(b, _, _)) => a == b,
            (Elab::Cons(a, _), Elab::Cons(b, _)) if a == b => true,
            (Elab::Cons(_, t), Elab::Data(_, _, _)) => t.unify(sup, tctx, cons),
            (Elab::Data(_, sid, _), _) => {
                let scope = ScopeId::Struct(*sid, Box::new(tctx.scope()));
                let mut cln = Cloner::new(tctx);
                let sub =
                    Elab::Union(
                        tctx.database()
                            .symbols(scope.clone())
                            .iter()
                            .filter_map(|s| {
                                let x = tctx.database().elab(scope.clone(), **s)?;
                                let x = x.cloned(&mut cln);
                                match &x {
                                    Elab::Cons(_, t) => match &**t {
                                        Elab::Fun(_, _, v, _) => {
                                            assert_eq!(v.len(), 1);
                                            let (args, _) = &v[0];
                                            let args: Vec<_> =
                                                args.iter().map(|x| x.cloned(&mut cln)).collect();
                                            Some(args.into_iter().fold(x, |f, x| {
                                                Elab::App(Box::new(f), Box::new(x))
                                            }))
                                        }
                                        Elab::Data(_, _, _) => Some(x),
                                        _ => panic!("wrong type"),
                                    },
                                    _ => panic!("not cons"),
                                }
                            })
                            .collect(),
                    );
                sub.unify(sup, tctx, cons)
            }
            (_, Elab::Data(_, sid, _)) => {
                let scope = ScopeId::Struct(*sid, Box::new(tctx.scope()));
                let mut cln = Cloner::new(tctx);
                let sup =
                    Elab::Union(
                        tctx.database()
                            .symbols(scope.clone())
                            .iter()
                            .filter_map(|s| {
                                let x = tctx.database().elab(scope.clone(), **s)?;
                                let x = x.cloned(&mut cln);
                                match &x {
                                    Elab::Cons(_, t) => match &**t {
                                        Elab::Fun(_, _, v, _) => {
                                            assert_eq!(v.len(), 1);
                                            let (args, _) = &v[0];
                                            let args: Vec<_> =
                                                args.iter().map(|x| x.cloned(&mut cln)).collect();
                                            Some(args.into_iter().fold(x, |f, x| {
                                                Elab::App(Box::new(f), Box::new(x))
                                            }))
                                        }
                                        Elab::Data(_, _, _) => Some(x),
                                        _ => panic!("wrong type"),
                                    },
                                    _ => panic!("not cons"),
                                }
                            })
                            .collect(),
                    );
                self.unify(&sup, tctx, cons)
            }
            (Elab::Binder(_, t), _) => t.unify(sup, tctx, cons),
            (_, Elab::Binder(_, t)) => self.unify(t, tctx, cons),
            (Elab::Union(sub), Elab::Union(sup)) => {
                // If each type in `sub` has a supertype in `sup`, we're good
                let mut sub: Vec<_> = sub.iter().collect();
                for sup in sup.iter() {
                    let mut i = 0;
                    while i < sub.len() {
                        let x = sub[i];

                        let mut tcons = Vec::new();
                        if x.unify(&sup, tctx, &mut tcons) {
                            sub.remove(i);
                            cons.append(&mut tcons);
                        } else {
                            i += 1;
                        }
                    }
                }
                sub.is_empty()
            }
            (Elab::Union(v), _) => v.iter().all(|x| x.unify(sup, tctx, cons)),
            (_, Elab::Union(v)) => v.iter().any(|x| {
                let mut tcons = Vec::new();
                if self.unify(x, tctx, &mut tcons) {
                    cons.append(&mut tcons);
                    true
                } else {
                    false
                }
            }),
            // Higher universes contain lower ones
            (Elab::Type(a), Elab::Type(b)) => b >= a,
            // Due to singleton types, pretty much everything (except unions) can be its own type, so everything can be a type of types
            // So if it's in universe `N+1` or below, all it's values are in universe `N`, so it's a subtype of `TypeN`
            (_, Elab::Type(i)) => self.universe(tctx) <= i + 1,
            _ => false,
        }
    }

    pub fn has_type(&self, ty: &Elab, ectx: &mut ECtx) -> bool {
        let b = match (self, ty) {
            (Elab::I32(n), Elab::I32(m)) => n == m,
            (Elab::I32(_), Elab::Builtin(Builtin::Int)) => true,
            (Elab::StructInline(sub), Elab::StructInline(sup)) => {
                // We DON'T do record subtyping, that's confusing and hard to compile efficiently
                sup.iter().all(|(n, sup)| sub.iter().find(|(n2, _)| n2.raw() == n.raw()).map_or(false, |(_, sub)| sub.has_type(sup, ectx)))
                    // so make sure there aren't any extra fields
                    && sub.iter().all(|(n, _)| sup.iter().any(|(n2, _)| n2.raw() == n.raw()))
            }
            (Elab::StructIntern(id), _) => ScopeId::Struct(*id, Box::new(ectx.scope()))
                .inline(ectx)
                .has_type(ty, ectx),
            (_, Elab::StructIntern(id)) => self.has_type(
                &ScopeId::Struct(*id, Box::new(ectx.scope())).inline(ectx),
                ectx,
            ),
            (Elab::Unit, Elab::Unit) => true,
            (Elab::App(f, x), Elab::App(tf, tx)) => f.has_type(tf, ectx) && x.has_type(tx, ectx),
            (Elab::Var(_, x, _), _) if ectx.database().elab(ectx.scope(), *x).is_some() => ectx
                .database()
                .elab(ectx.scope(), *x)
                .unwrap()
                .cloned(&mut Cloner::new(ectx))
                .has_type(ty, ectx),
            (_, Elab::Var(_, x, _)) if ectx.database().elab(ectx.scope(), *x).is_some() => self
                .has_type(
                    &ectx
                        .database()
                        .elab(ectx.scope(), *x)
                        .unwrap()
                        .cloned(&mut Cloner::new(ectx)),
                    ectx,
                ),
            (Elab::Var(_, x, _), _) if ectx.vals.contains_key(x) => ectx
                .val(*x)
                .unwrap()
                .cloned(&mut Cloner::new(ectx))
                .has_type(ty, ectx),
            (_, Elab::Var(_, x, _)) if ectx.vals.contains_key(x) => {
                self.has_type(&ectx.val(*x).unwrap().cloned(&mut Cloner::new(ectx)), ectx)
            }
            (Elab::Pair(ax, ay), Elab::Pair(bx, by)) => {
                ax.has_type(bx, ectx) && ay.has_type(by, ectx)
            }
            (Elab::Binder(_, t), _) => t.has_type(ty, ectx),
            (_, Elab::Binder(_, t)) => self.has_type(t, ectx),
            (Elab::Cons(x, _), Elab::Cons(y, _)) => x == y,
            _ => false,
        };
        // This handles functions, unbound variables, etc.
        b || self.get_type(ectx).subtype_of(ty, ectx)
    }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality
    // TODO this is redundant with unify(), get rid of it
    pub fn subtype_of(&self, sup: &Elab, ectx: &mut ECtx) -> bool {
        match (self, sup) {
            (Elab::Bottom, _) => true,
            (_, Elab::Top) => true,
            (Elab::I32(n), Elab::I32(m)) => n == m,
            (Elab::I32(_), Elab::Builtin(Builtin::Int)) => true,
            (Elab::StructInline(sub), Elab::StructInline(sup)) => {
                // We DON'T do record subtyping, that's confusing and hard to compile efficiently
                sup.iter().all(|(n, sup)| sub.iter().find(|(n2, _)| n2.raw() == n.raw()).map_or(false, |(_, sub)| sub.subtype_of(sup, ectx)))
                    // so make sure there aren't any extra fields
                    && sub.iter().all(|(n, _)| sup.iter().any(|(n2, _)| n2.raw() == n.raw()))
            }
            (Elab::StructIntern(id), _) => ScopeId::Struct(*id, Box::new(ectx.scope()))
                .inline(ectx)
                .subtype_of(sup, ectx),
            (_, Elab::StructIntern(id)) => self.subtype_of(
                &ScopeId::Struct(*id, Box::new(ectx.scope())).inline(ectx),
                ectx,
            ),
            (Elab::Builtin(b), Elab::Builtin(c)) if b == c => true,
            (Elab::Unit, Elab::Unit) => true,
            (Elab::Var(_, x, _), _) if ectx.database().elab(ectx.scope(), *x).is_some() => ectx
                .database()
                .elab(ectx.scope(), *x)
                .unwrap()
                .cloned(&mut Cloner::new(ectx))
                .subtype_of(sup, ectx),
            (_, Elab::Var(_, x, _)) if ectx.database().elab(ectx.scope(), *x).is_some() => self
                .subtype_of(
                    &ectx
                        .database()
                        .elab(ectx.scope(), *x)
                        .unwrap()
                        .cloned(&mut Cloner::new(ectx)),
                    ectx,
                ),
            (Elab::Var(_, x, _), _) if ectx.vals.contains_key(x) => ectx
                .val(*x)
                .unwrap()
                .cloned(&mut Cloner::new(ectx))
                .subtype_of(sup, ectx),
            (_, Elab::Var(_, x, _)) if ectx.vals.contains_key(x) => {
                self.subtype_of(&ectx.val(*x).unwrap().cloned(&mut Cloner::new(ectx)), ectx)
            }
            (Elab::App(f1, x1), Elab::App(f2, x2)) => {
                f1.subtype_of(f2, ectx) && x1.subtype_of(x2, ectx)
            }
            (Elab::Pair(ax, ay), Elab::Pair(bx, by)) => {
                ax.subtype_of(bx, ectx) && ay.subtype_of(by, ectx)
            }
            // (Type -> (Type, Type)) <: ((Type, Type) -> Type)
            // `fun` <: `move fun`
            (
                Elab::Fun(cl_a @ Clos { is_move: false, .. }, _, v_sub, _),
                Elab::Fun(cl_b @ Clos { is_move: false, .. }, _, v_sup, _),
            )
            | (
                Elab::Fun(cl_a, _, v_sub, _),
                Elab::Fun(cl_b @ Clos { is_move: true, .. }, _, v_sup, _),
            ) => {
                ectx.add_clos(cl_a);
                ectx.add_clos(cl_b);
                for (args_sup, to_sup) in v_sup.iter() {
                    let mut found = false;
                    for (args_sub, to_sub) in v_sub.iter() {
                        let mut all_subtype = true;
                        for (sup, sub) in args_sup.iter().zip(args_sub.iter()) {
                            // Function parameters are contravariant
                            if !sup.subtype_of(sub, ectx) {
                                all_subtype = false;
                                break;
                            }
                            // Matching in either direction works, we have to check alpha equality
                            sub.alpha_match(sup, ectx);
                        }

                        if !all_subtype {
                            break;
                        }

                        // Since types are only in weak-head normal form, we have to reduce the spines to compare them
                        let to_sup = to_sup.cloned(&mut Cloner::new(ectx)).whnf(ectx);
                        let to_sub = to_sub.cloned(&mut Cloner::new(ectx)).whnf(ectx);

                        if to_sub.subtype_of(&to_sup, ectx) {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return false;
                    }
                }
                return true;
            }
            (Elab::Data(a, _, _), Elab::Data(b, _, _)) => a == b,
            (Elab::Cons(a, _), Elab::Cons(b, _)) if a == b => true,
            (Elab::Cons(_, t), Elab::Data(_, _, _)) => t.subtype_of(sup, ectx),
            (Elab::Data(_, sid, _), _) => {
                let scope = ScopeId::Struct(*sid, Box::new(ectx.scope()));
                let mut cln = Cloner::new(ectx);
                let sub =
                    Elab::Union(
                        ectx.database()
                            .symbols(scope.clone())
                            .iter()
                            .filter_map(|s| {
                                let x = ectx.database().elab(scope.clone(), **s)?;
                                let x = x.cloned(&mut cln).whnf(ectx);
                                match &x {
                                    Elab::Cons(_, t) => match &**t {
                                        Elab::Fun(_, _, v, _) => {
                                            assert_eq!(v.len(), 1);
                                            let (args, _) = &v[0];
                                            let args: Vec<_> =
                                                args.iter().map(|x| x.cloned(&mut cln)).collect();
                                            Some(args.into_iter().fold(x, |f, x| {
                                                Elab::App(Box::new(f), Box::new(x))
                                            }))
                                        }
                                        Elab::Data(_, _, _) => Some(x),
                                        _ => panic!("wrong type"),
                                    },
                                    _ => panic!("not cons"),
                                }
                            })
                            .collect(),
                    );
                sub.subtype_of(sup, ectx)
            }
            (_, Elab::Data(_, sid, _)) => {
                let scope = ScopeId::Struct(*sid, Box::new(ectx.scope()));
                let mut cln = Cloner::new(ectx);
                let sup =
                    Elab::Union(
                        ectx.database()
                            .symbols(scope.clone())
                            .iter()
                            .filter_map(|s| {
                                let x = ectx.database().elab(scope.clone(), **s)?;
                                let x = x.cloned(&mut cln).whnf(ectx);
                                match &x {
                                    Elab::Cons(_, t) => match &**t {
                                        Elab::Fun(_, _, v, _) => {
                                            assert_eq!(v.len(), 1);
                                            let (args, _) = &v[0];
                                            let args: Vec<_> =
                                                args.iter().map(|x| x.cloned(&mut cln)).collect();
                                            Some(args.into_iter().fold(x, |f, x| {
                                                Elab::App(Box::new(f), Box::new(x))
                                            }))
                                        }
                                        Elab::Data(_, _, _) => Some(x),
                                        _ => panic!("wrong type"),
                                    },
                                    _ => panic!("not cons"),
                                }
                            })
                            .collect(),
                    );
                self.subtype_of(&sup, ectx)
            }
            // Two variables that haven't been resolved yet, but refer to the same definition
            (Elab::Var(_, x, _), Elab::Var(_, y, _)) if y == x => true,
            (Elab::Binder(_, t), _) => t.subtype_of(sup, ectx),
            (_, Elab::Binder(_, t)) => self.subtype_of(t, ectx),
            (Elab::Union(sub), Elab::Union(sup)) => {
                // If each type in `sub` has a supertype in `sup`, we're good
                let mut sub: Vec<_> = sub.iter().collect();
                for sup in sup.iter() {
                    let mut i = 0;
                    while i < sub.len() {
                        let x = sub[i];

                        if x.subtype_of(&sup, ectx) {
                            sub.remove(i);
                        } else {
                            i += 1;
                        }
                    }
                }
                sub.is_empty()
            }
            (Elab::Union(v), _) => v.iter().all(|x| x.subtype_of(sup, ectx)),
            (_, Elab::Union(v)) => v.iter().any(|x| self.subtype_of(x, ectx)),
            // Higher universes contain lower ones
            (Elab::Type(a), Elab::Type(b)) => b >= a,
            // Due to singleton types, pretty much everything (except unions) can be its own type, so everything can be a type of types
            // So if it's in universe `N+1` or below, all it's values are in universe `N`, so it's a subtype of `TypeN`
            (_, Elab::Type(i)) => self.universe(ectx) <= i + 1,
            _ => false,
        }
    }
}
