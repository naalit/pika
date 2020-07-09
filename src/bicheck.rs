//! Bidirectional type checking
use crate::common::*;
use crate::elab::*;
use crate::error::*;
use crate::{affine::Mult, term::*};
use std::ops::{Deref, DerefMut};

/// An error produced in type checking
#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    /// We couldn't synthesize a type for the given term
    Synth(STerm),
    CantMatch(STerm, Elab),
    ConsType(Spanned<Elab>, TypeId),
    UnsolvedMeta(Spanned<Sym>),
    ImplicitLast(Span),
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
    NoMatch(Vec<Elab>, Span, Elab),
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
            TypeError::CantMatch(pat, ty) => Error::new(
                file,
                Doc::start("Type error: pattern '")
                    .chain(pat.pretty(b).style(Style::None))
                    .add("' is invalid for type '")
                    .chain(ty.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                pat.span(),
                Doc::start("cannot match type '")
                    .chain(ty.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Error),
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
                    .style(Style::Error),
            ),
            TypeError::UnsolvedMeta(meta) => {
                if meta.span() == Span::empty() {
                    Error::no_label(
                        Doc::start("Type error: could not find solution for implicit variable '")
                            .chain(meta.pretty(b))
                            .add("', try adding a type annotation"),
                    )
                } else {
                    Error::new(
                        file,
                        Doc::start("Type error: could not find solution for implicit variable '")
                            .chain(meta.pretty(b))
                            .add("', try adding a type annotation"),
                        meta.span(),
                        Doc::start("implicit search triggered here"),
                    )
                }
            }
            TypeError::ImplicitLast(span) => Error::new(
                file,
                "Type error: implicit parameters can only occur before at least one explicit parameter",
                span,
                "try moving this implicit earlier in the argument list, or adding an explicit parameter, maybe (), after this one",
            )
                .with_note("help: this rule exists so Pika always knows when to try to find an implicit: when you pass the next explicit argument"),
            TypeError::MoveOnlyFun(f, ty) => Error::new(
                file,
                Doc::start("Type error: expected copiable function '")
                    .chain(ty.unbind().pretty(b).style(Style::None).group())
                    .add("', found move-only function")
                    .style(Style::Bold),
                f.span(),
                Doc::start("try removing this ")
                    .chain(Doc::start("move").style(Style::Keyword))
                    .style(Style::Error),
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
                    .style(Style::Error),
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
                    })
                    .style(Style::Error),
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
                    .add(m)
                    .style(Style::Error),
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
                    .style(Style::Error),
            ),
            TypeError::NotSubtypeF(sub, sup) => Error::new(
                file,
                // This only happens for functions, so it's clearer as "Could not match 'fun X => _' and 'fun Y => _'"
                Doc::start("Type error: could not match types '")
                    .chain(Doc::start("fun").style(Style::Keyword))
                    .space()
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .space()
                    .add("=>")
                    .space()
                    .add("_")
                    .add("' and '")
                    .chain(Doc::start("fun").style(Style::Keyword))
                    .space()
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .space()
                    .add("=>")
                    .space()
                    .add("_")
                    .add("'")
                    .style(Style::Bold),
                sup.span(),
                Doc::start("this has type '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Error),
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
            TypeError::NoMatch(vals, span, ty) => Error::new(
                file,
                Doc::start("Type error: non-exhaustive match: no pattern matches ")
                    .chain(Doc::intersperse(
                        vals.iter().map(|x| {
                            Doc::start("'")
                                .chain(x.pretty(b).style(Style::None))
                                .add("'")
                        }),
                        Doc::start(",").space(),
                    ))
                    .add(" of type '")
                    .chain(ty.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                span,
                "no pattern matched",
            ),
            TypeError::DuplicateField(x, y) => Error::new(
                file,
                Doc::start("Type error: multiple definitions of variable '")
                    .chain(x.pretty(b))
                    .add("' in struct or module")
                    .style(Style::Bold),
                y.span(),
                format!("redefined here"),
            )
            .with_label(file, x.span(), format!("first defined here")),
        }
    }
}

#[derive(Clone)]
pub struct TCtx<'a> {
    pub tys: HashMap<Sym, Arc<Elab>>,
    pub metas: HashMap<Sym, Span>,
    pub ectx: ECtx<'a>,
}
impl<'a> From<ECtx<'a>> for TCtx<'a> {
    fn from(ectx: ECtx<'a>) -> Self {
        TCtx {
            tys: HashMap::new(),
            metas: HashMap::new(),
            ectx,
        }
    }
}
impl<'a> TCtx<'a> {
    pub fn solve_metas(&self) -> Vec<TypeError> {
        self.metas
            .iter()
            .map(|(s, span)| Spanned::new(*s, *span))
            .map(|x| TypeError::UnsolvedMeta(x))
            .collect()
    }

    /// This gives the metas Span::empty(), so should only be used on temporary `TCtx`s that you don't intend to call solve_metas() on
    pub fn extend_metas(&mut self, metas: impl IntoIterator<Item = Sym>) {
        self.metas
            .extend(metas.into_iter().map(|x| (x, Span::empty())))
    }

    pub fn apply_metas(&mut self, metas: impl IntoIterator<Item = (Sym, Elab)>) {
        for (k, v) in metas {
            // #[cfg(feature = "logging")]
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
            metas: HashMap::new(),
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

/// Typechecking case-of uses the same algorithm whether we have a goal type or not, so it's in its own function
fn check_case(
    val: &STerm,
    cases: &Vec<(STerm, STerm)>,
    mut tret: Option<Elab>,
    tctx: &mut TCtx,
) -> Result<Elab, TypeError> {
    use crate::pattern::TBool::*;

    // This is the span where we report non-exhaustive match errors
    let vspan = val.span();
    let val = synth(val, tctx)?;
    let tval = val.get_type(tctx);

    let mut uncovered = vec![Elab::Var(
        Span::empty(),
        tctx.bindings_mut().create("_".to_string()),
        Box::new(tval.cloned(&mut Cloner::new(tctx))),
    )];
    let mut rcases = Vec::new();
    for (pat, body) in cases {
        let mut cons = Vec::new();
        let pat = crate::pattern::to_pattern(pat, &tval, &mut cons, tctx).ok_or_else(|| {
            TypeError::CantMatch(pat.clone(), tval.cloned(&mut Cloner::new(tctx)))
        })?;

        let mut matched_any = false;
        let mut i = 0;
        // We don't want to apply substitutions introduced by patterns matching with uncovered!
        let mut ectx = ECtx::new(tctx);
        while i < uncovered.len() {
            match pat.matches(&uncovered[i], &mut ectx) {
                Yes => {
                    matched_any = true;
                    uncovered.remove(i);
                }
                Maybe => {
                    let x = &uncovered[i];
                    if let Some(mut v) = x.expand(tctx) {
                        uncovered.remove(i);
                        uncovered.append(&mut v);
                    } else {
                        // Since it might match, it's not redundant, but we'll need more to call this possibility covered
                        matched_any = true;
                        i += 1;
                    }
                }
                No => {
                    i += 1;
                }
            }
        }
        if !matched_any {
            // TODO real compiler warnings
            eprintln!(
                "warning: redundant pattern '{}'",
                pat.pretty(tctx).ansi_string()
            );
        }

        pat.apply_types(tctx);

        let body = if cons.is_empty() {
            if let Some(t) = &tret {
                check(body, t, tctx)?
            } else {
                let x = synth(body, tctx)?;
                tret = Some(x.get_type(tctx));
                x
            }
        } else {
            let mut tctx = tctx.clone();
            tctx.apply_metas(cons);

            if let Some(t) = &tret {
                check(body, t, &mut tctx)?
            } else {
                let x = synth(body, &mut tctx)?;
                tret = Some(x.get_type(&tctx));
                x
            }
        };
        rcases.push((pat, body));
    }
    if !uncovered.is_empty() {
        return Err(TypeError::NoMatch(uncovered, vspan, tval));
    }

    Ok(Elab::CaseOf(
        Box::new(val),
        rcases,
        // If an empty case typechecks, it has type Bottom
        Box::new(tret.unwrap_or(Elab::Bottom)),
    ))
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
            let mut ty = synth(ty, tctx)?.normal(tctx);
            let did = tctx.bindings().tag_to_type(*id).unwrap();
            match &mut ty {
                // TODO `Pair a`
                Elab::Data(did2, _, _) if *did2 == did => (),
                Elab::Fun(_, _, to) => match to.result().head() {
                    Elab::Data(did2, _, _) if *did2 == did => (),
                    _ => return Err(TypeError::ConsType(Spanned::new(ty, ty_span), did)),
                },
                _ => return Err(TypeError::ConsType(Spanned::new(ty, ty_span), did)),
            };
            Ok(Elab::Cons(*id, Box::new(ty)))
        }
        Term::App(fi, x) => {
            let f = synth(fi, tctx)?;

            fn check_app(
                ft: Elab,
                fs: Span,
                f: Elab,
                x: &STerm,
                tctx: &mut TCtx,
            ) -> Result<Elab, TypeError> {
                let x = match ft {
                    Elab::Fun(cl, from, to) => {
                        tctx.add_clos(&cl);
                        if cl.implicit {
                            let meta = match &*from {
                                // If it's named, which is common, use that, it makes errors nicer
                                Elab::Binder(s, _) => tctx.bindings_mut().fresh(*s),
                                _ => tctx.bindings_mut().create("_meta".into()),
                            };
                            // TODO keep track of the given type for instance argument style resolution

                            // It's more helpful to see the whole application where we decided to solve the implicit
                            let app_span = Span(fs.0, x.span().1);
                            tctx.metas.insert(meta, app_span);

                            let v = Elab::Var(fs, meta, from);
                            let from = match &v {
                                Elab::Var(_, _, from) => from,
                                _ => unreachable!(),
                            };
                            from.do_match(&v, tctx);
                            // Apply the function to the new meta
                            let f = Elab::App(Box::new(f), Box::new(v));
                            // We have to WHNF here it to make sure meta solutions and the `do_match` from earlier are propagated correctly
                            return check_app(*to, fs, f, x, tctx).map(|x| x.whnf(tctx));
                        } else {
                            let from = from.whnf(tctx);
                            check(x, &from, tctx)
                        }
                    }
                    Elab::Bottom => synth(x, tctx),
                    a => Err(TypeError::NotFunction(
                        Spanned::new(a.cloned(&mut Cloner::new(&tctx)), fs),
                        x.clone(),
                    )),
                }?;
                Ok(Elab::App(Box::new(f), Box::new(x)))
            }

            check_app(f.get_type(tctx), fi.span(), f, x, tctx)
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
        Term::CaseOf(val, cases) => check_case(val, cases, None, tctx),
        // We do currying here
        Term::Fun(m, args, body) => {
            let mut rargs = Vec::new();
            let mut rmult = Vec::new();
            for (implicit, a) in args {
                let a = synth(a, tctx)?.whnf(tctx);
                // Match it with itself to apply the types
                a.match_types(&a, tctx);
                rmult.push(a.multiplicity(tctx));
                rargs.push((*implicit, a));
            }
            if args.last().unwrap().0 {
                return Err(TypeError::ImplicitLast(args.last().unwrap().1.span()));
            }
            let body = synth(body, tctx)?;

            let tys = tctx.clos(t, *m, false).tys;
            // TODO optimize
            let mut tys: Vec<_> = (0..rargs.len())
                .map(|i| {
                    tys.iter()
                        .cloned()
                        .chain(
                            tctx.tys
                                .iter()
                                .filter(|(k, _)| rargs.iter().take(i).any(|(_, x)| x.binds(**k)))
                                .map(|(k, v)| (*k, v.clone())),
                        )
                        .collect()
                })
                .collect();
            let t = rargs
                .into_iter()
                .enumerate()
                .rfold(body, |body, (i, (implicit, arg))| {
                    Elab::Fun(
                        if i == 0 {
                            tctx.clos(t, *m, implicit)
                        } else {
                            Clos {
                                // If we passed a move-only argument, we'll need to capture it and make the curried function move-only
                                is_move: *m || rmult.iter().take(i).any(|x| *x == Mult::One),
                                implicit,
                                tys: tys.pop().unwrap(),
                                // We only need to capture values in the top-level closure, they'll be propagated by `whnf()` when we apply it
                                vals: Vec::new(),
                                span: t.span(),
                            }
                        },
                        Box::new(arg),
                        Box::new(body),
                    )
                });

            Ok(t)
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
        Term::Binder(x, None) => {
            let name = format!("<type of {}>", x.pretty(tctx).raw_string());
            let meta = tctx.bindings_mut().create(name);
            tctx.metas.insert(meta, t.span());
            Ok(Elab::Binder(
                *x,
                Box::new(Elab::Var(t.span(), meta, Box::new(Elab::Top))),
            ))
        }
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
            let (tx, ty) = (
                tx.cloned(&mut cln).whnf(tctx),
                ty.cloned(&mut cln).whnf(tctx),
            );
            // TODO dependent pairs don't really work
            check(x, &tx, tctx)?;
            check(y, &ty, tctx)
        }

        (Term::Fun(m, args, body), Elab::Fun(cl, from, to)) => {
            if *m && !cl.is_move {
                return Err(TypeError::MoveOnlyFun(
                    term.clone(),
                    typ.cloned(&mut Cloner::new(tctx)),
                ));
            }
            tctx.add_clos(cl);

            let (implicit, arg) = args.first().unwrap();
            let aspan = arg.span();
            let arg = synth(arg, tctx)?.whnf(tctx);

            let mut cln = Cloner::new(tctx);
            let from = from.cloned(&mut cln).whnf(tctx);
            let mut tcons = Vec::new();
            // Function parameters are contravariant
            if !from.unify(&arg, tctx, &mut tcons) {
                return Err(TypeError::NotSubtypeF(
                    from.cloned(&mut Cloner::new(tctx)),
                    Spanned::new(arg, aspan),
                ));
            }
            tctx.apply_metas(tcons);

            arg.match_types(&from, tctx);
            // This multiplicity check is turned off for now, because it doesn't really cooperate with metavariables and it's going to be redone soon
            // let mult = arg.multiplicity(tctx);

            let body = if args.len() > 1 {
                let span = Span(args[1].1.span().0, body.span().1);
                Spanned::new(
                    Term::Fun(
                        *m, /*|| mult == Mult::One*/
                        args.iter().skip(1).cloned().collect(),
                        body.clone(),
                    ),
                    span,
                )
            } else {
                body.clone()
            };

            let to = to.cloned(&mut cln).whnf(tctx);
            let body = match check(&body, &to, tctx) {
                Ok(body) => body,
                Err(TypeError::NotSubtype(a, b)) if a.arity() != b.arity() => {
                    let arity = typ.arity();
                    if arity != args.len() {
                        // This is an educated guess - it's possible that the error comes from something else
                        // For example, another function with the wrong arity inside this one
                        // Also, the arity detection we're using here marks e.g. (Nat -> Nat) as arity 1
                        // So it's not perfect, but it's better than "() is not a subtype of fun () => ()" for people who aren't used to currying
                        return Err(TypeError::WrongArity(
                            arity,
                            args.len(),
                            typ.cloned(&mut Cloner::new(tctx)),
                            term.span(),
                        ));
                    } else {
                        return Err(TypeError::NotSubtype(a, b));
                    }
                }
                Err(e) => return Err(e),
            };

            let clos = tctx.clos(term, *m, *implicit);
            // WHNF to capture any needed variables from the type closure
            Ok(Elab::Fun(clos, Box::new(arg), Box::new(body)).whnf(tctx))
        }

        (Term::CaseOf(val, cases), _) => {
            check_case(val, cases, Some(typ.cloned(&mut Cloner::new(tctx))), tctx)
        }

        (_, _) => {
            let t = synth(term, tctx)?;
            let ty = t.get_type(tctx);
            let mut tcons = Vec::new();
            // Is it guaranteed to be a `typ`?
            if ty.unify(&typ, &mut tctx.clone(), &mut tcons) {
                // If any metas were solved by this, add the solutions to the context
                tctx.apply_metas(tcons);
                Ok(t)
            } else {
                match typ.unbind() {
                    Elab::Type(i) => Err(TypeError::WrongUniverse(
                        term.copy_span(ty.cloned(&mut Cloner::new(&tctx))),
                        ty.universe(tctx) - 1,
                        *i,
                    )),
                    _ => Err(TypeError::NotSubtype(
                        // Full normal form is helpful for errors
                        term.copy_span(ty.cloned(&mut Cloner::new(&tctx)).normal(tctx)),
                        typ.cloned(&mut Cloner::new(&tctx)).normal(tctx),
                    )),
                }
            }
        }
    }
}

impl Elab {
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
                    x.cloned(&mut Cloner::new(&tctx)).match_types(other, tctx);
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
            (Elab::Var(_, s, _), x) | (x, Elab::Var(_, s, _)) if tctx.metas.contains_key(s) => {
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
                Elab::Fun(cl_a @ Clos { is_move: false, .. }, from_sub, to_sub),
                Elab::Fun(cl_b @ Clos { is_move: false, .. }, from_sup, to_sup),
            )
            | (
                Elab::Fun(cl_a, from_sub, to_sub),
                Elab::Fun(cl_b @ Clos { is_move: true, .. }, from_sup, to_sup),
            ) => {
                if cl_a.implicit != cl_b.implicit {
                    return false;
                }

                let mut tctx = tctx.clone();
                tctx.add_clos(cl_a);
                tctx.add_clos(cl_b);

                // Function parameters are contravariant
                if !from_sup.unify(from_sub, &tctx, cons) {
                    return false;
                }
                // Matching in either direction works, we have to check alpha equality
                from_sub.alpha_match(from_sup, &mut tctx);

                // Since types are only in weak-head normal form, we have to reduce the spines to compare them
                let to_sup = to_sup.cloned(&mut Cloner::new(&tctx)).whnf(&mut tctx);
                let to_sub = to_sub.cloned(&mut Cloner::new(&tctx)).whnf(&mut tctx);

                to_sub.unify(&to_sup, &tctx, cons)
            }
            (Elab::Data(a, _, _), Elab::Data(b, _, _)) => a == b,
            (Elab::Cons(a, _), Elab::Cons(b, _)) if a == b => true,
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
}
