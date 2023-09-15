use super::*;

impl ast::Expr {
    pub(super) fn as_let_def_pat(
        &self,
        db: &dyn Elaborator,
    ) -> Option<(Option<(bool, SName)>, Option<ast::Ty>)> {
        match self {
            ast::Expr::MutVar(v) => Some((Some((true, v.var()?.name(db))), None)),
            ast::Expr::Var(n) => Some((Some((false, n.name(db))), None)),
            ast::Expr::GroupedExpr(x) => x.expr().and_then(|x| x.as_let_def_pat(db)),
            ast::Expr::Binder(x) => {
                let (name, ty) = x
                    .pat()
                    .and_then(|x| x.expr())
                    .and_then(|x| x.as_let_def_pat(db))?;
                if ty.is_some() {
                    return None;
                }
                Some((name, x.ty()))
            }
            _ => None,
        }
    }
}

impl ast::Def {
    pub(super) fn elab_type(&self, def_id: Def, def_node: DefNode, cxt: &mut Cxt) -> Option<Val> {
        match self {
            ast::Def::LetDef(l) => match l.pat()?.expr()?.as_let_def_pat(cxt.db) {
                Some((_, Some(ty))) => Some(
                    ty.expr()?
                        .check(Val::Type, cxt, &CheckReason::UsedAsType)
                        .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                ),
                _ => {
                    // Infer the type from the value if possible
                    // TODO would it make sense to call def_elab() instead?
                    let ty = cxt.db.def_elab_n(def_id, def_node).result?.ty;
                    Some(
                        ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                            .eval(&mut cxt.env()),
                    )
                }
            },
            ast::Def::FunDef(x) => {
                let (_, ty) = infer_fun(
                    x.imp_par(),
                    x.exp_par().as_par(),
                    x.ret_ty().and_then(|x| x.expr()),
                    None,
                    x.span(),
                    cxt,
                );
                let ty = ty
                    .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                    .eval(&mut cxt.env());

                Some(ty)
            }
            ast::Def::TypeDef(_) => {
                // We usually can't know types of type arguments from just the signature
                // so in general we need to elaborate the constructor types as well
                let ty = cxt.db.def_elab_n(def_id, def_node).result?.ty;
                Some(
                    ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                )
            }
            ast::Def::TypeDefShort(_) => todo!(),
            ast::Def::TypeDefStruct(_) => todo!(),
        }
    }

    pub(super) fn elab(&self, def_id: Def, def_node: DefNode, cxt: &mut Cxt) -> Option<Definition> {
        match self {
            ast::Def::LetDef(x) => {
                match x.pat()?.expr()?.as_let_def_pat(cxt.db) {
                    Some((Some((m, name)), None)) => {
                        if m {
                            cxt.error(
                                x.pat()?.span(),
                                "Only 'let' definitions in blocks can be mutable",
                            );
                        }
                        let (body, ty) = x.body()?.expr()?.infer(cxt);
                        // inline metas in the term
                        let body = body.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                        Some(Definition {
                            name,
                            ty: Box::new(ty.quote(cxt.size(), Some(&cxt.mcxt))),
                            body: DefBody::Let(Box::new(Expr::Spanned(
                                x.body().unwrap().span(),
                                Box::new(body),
                            ))),
                            children: Vec::new(),
                        })
                    }
                    Some((Some((m, name)), Some(pty))) => {
                        if m {
                            cxt.error(
                                x.pat()?.span(),
                                "Only 'let' definitions in blocks can be mutable",
                            );
                        }
                        // We already elaborated the type, so avoid doing that twice
                        let ty = cxt.db.def_type_n(def_id, def_node).result?;
                        let body = x.body()?.expr()?.check(
                            ty.clone(),
                            cxt,
                            &CheckReason::GivenType(pty.span()),
                        );
                        let body = body.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                        Some(Definition {
                            name,
                            ty: Box::new(Expr::Spanned(
                                pty.span(),
                                Box::new(ty.quote(cxt.size(), Some(&cxt.mcxt))),
                            )),
                            body: DefBody::Let(Box::new(Expr::Spanned(
                                x.body().unwrap().span(),
                                Box::new(body),
                            ))),
                            children: Vec::new(),
                        })
                    }
                    Some((None, _)) => None,
                    None => {
                        cxt.error(
                            x.pat().unwrap().span(),
                            "Patterns are not allowed in let definitions outside of blocks",
                        );
                        None
                    }
                }
            }
            ast::Def::FunDef(x) => {
                if x.body().is_none() {
                    cxt.error(self.span(), "Function declarations aren't allowed in this context, a function body is required");
                }

                let (term, ty) = infer_fun(
                    x.imp_par(),
                    x.exp_par().as_par(),
                    x.ret_ty().and_then(|x| x.expr()),
                    x.body(),
                    x.span(),
                    cxt,
                );

                Some(Definition {
                    name: x.name()?.name(cxt.db),
                    ty: Box::new(ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))),
                    body: DefBody::Let(Box::new(term.eval_quote(
                        &mut cxt.env(),
                        cxt.size(),
                        Some(&cxt.mcxt),
                    ))),
                    children: Vec::new(),
                })
            }
            ast::Def::TypeDef(x) => {
                cxt.push();
                let (_, ty) = infer_fun(
                    x.imp_par(),
                    x.exp_par().as_par(),
                    Some(ast::Expr::Type(ast::Type::Val {
                        span: x.name().map_or_else(|| x.span(), |n| n.span()),
                        kw: None,
                    })),
                    None,
                    x.span(),
                    cxt,
                );

                let name = if let Some(name) = x.name() {
                    let name = name.name(cxt.db);
                    cxt.define(
                        name,
                        Var::Def(name, def_id),
                        ty.clone().eval(&mut cxt.env()),
                    );
                    name
                } else {
                    (cxt.db.name("_".into()), RelSpan::empty())
                };

                let default_rty = Val::var(Var::Def(name, def_id));
                let (ty_params, default_rty) = match &ty {
                    Expr::Fun(clos) if matches!(clos.class, Pi(_)) => {
                        let arg = clos
                            .clone()
                            .eval(&mut cxt.env())
                            .synthesize_args(cxt.size());
                        match &*clos.body {
                            Expr::Fun(clos2) if matches!(clos2.class, Pi(_)) => {
                                let mut env = cxt.env();
                                env.extend((0..clos.params.len()).map(|_| None));
                                let arg2 = clos2
                                    .clone()
                                    .eval(&mut env)
                                    .synthesize_args(cxt.size() + clos.params.len());
                                (
                                    clos.params.iter().chain(&clos2.params).cloned().collect(),
                                    // TODO these envs are slightly wrong
                                    default_rty
                                        .app(Elim::App(Impl, arg), &mut cxt.env())
                                        .app(Elim::App(Expl, arg2), &mut env),
                                )
                            }
                            _ => (
                                clos.params.clone(),
                                default_rty.app(
                                    Elim::App(clos.class.icit().unwrap(), arg),
                                    &mut cxt.env(),
                                ),
                            ),
                        }
                    }
                    _ => (Vec::new(), default_rty),
                };

                let mut ctors = Vec::new();
                let mut n_unnamed = 0;
                for c in x.cons() {
                    let split = match c.name().map(|x| x.name(cxt.db)) {
                        Some((n, _)) => SplitId::Named(n),
                        None => {
                            n_unnamed += 1;
                            SplitId::Idx(n_unnamed)
                        }
                    };
                    let span = c.name().map_or(RelSpan::empty(), |x| x.span());
                    // If a return type is not given, the type arguments are added as implicit parameters
                    // and all of them are applied to the type constructor for the return type.
                    // If the return type is given, nothing is implied and the types and parameters are as given.
                    let cty = if c.ret_ty().is_some() {
                        let (_, cty) = infer_fun(
                            c.imp_par(),
                            c.exp_par().as_par(),
                            c.ret_ty().and_then(|x| x.expr()),
                            None,
                            c.span(),
                            cxt,
                        );
                        fn head(t: &Expr) -> &Expr {
                            match t {
                                Expr::Elim(a, e) if matches!(&**e, Elim::App(_, _)) => head(a),
                                t => t,
                            }
                        }
                        let rty = match &cty {
                            Expr::Fun(clos) if matches!(clos.class, Pi(_)) => match &*clos.body {
                                Expr::Fun(clos2)
                                    if clos.class == Pi(Impl) && clos2.class == Pi(Expl) =>
                                {
                                    &clos2.body
                                }
                                rty => rty,
                            },
                            rty => rty,
                        };
                        match head(rty) {
                            Expr::Head(Head::Var(Var::Def(_, def))) if *def == def_id => (),
                            Expr::Error => (),
                            _ => cxt.error(
                                c.ret_ty().unwrap().span(),
                                Doc::start("Datatype constructor must return a value of its parent type, not").space().chain(rty.pretty(cxt.db))
                            ),
                        }
                        cty
                    } else {
                        cxt.push();

                        let mut implicit = ty_params.clone();
                        for par in &implicit {
                            cxt.define_local(
                                par.name,
                                par.ty.clone().eval(&mut cxt.env()),
                                None,
                                None,
                                false,
                            );
                        }
                        implicit.append(&mut check_params(
                            c.imp_par()
                                .into_iter()
                                .flat_map(|x| x.pars())
                                .flat_map(|x| {
                                    match x.par().and_then(|x| x.pat()).and_then(|x| x.expr()) {
                                        Some(x) => x.as_args(),
                                        None => vec![Err(x.span())],
                                    }
                                })
                                .collect(),
                            true,
                            ParamTys::Inferred,
                            &CheckReason::UsedAsType,
                            cxt,
                        ));
                        let explicit = c.exp_par().as_par().map_or(Vec::new(), |x| {
                            check_params(
                                x.par.as_args(),
                                x.pat,
                                ParamTys::Inferred,
                                &CheckReason::UsedAsType,
                                cxt,
                            )
                        });

                        let mut ty = default_rty.clone().quote(cxt.size(), Some(&cxt.mcxt));
                        if !explicit.is_empty() {
                            ty = Expr::Fun(EClos {
                                class: Pi(Expl),
                                params: explicit,
                                body: Box::new(ty),
                            });
                        }
                        if !implicit.is_empty() {
                            ty = Expr::Fun(EClos {
                                class: Pi(Impl),
                                params: implicit,
                                body: Box::new(ty),
                            });
                        }

                        cxt.pop();

                        ty
                    };
                    if let Some(name) = c.name().map(|x| x.name(cxt.db)) {
                        cxt.define(
                            name,
                            Var::Cons(name, cxt.db.cons_id(def_id, split)),
                            cty.clone().eval(&mut cxt.env()),
                        );
                    }
                    ctors.push((split, span, cty));
                }

                cxt.push_def_scope(def_id);
                let mut i = 0;
                let children = x
                    .block()
                    .map(|x| x.defs())
                    .unwrap_or_default()
                    .into_iter()
                    .map(|x| {
                        let split = x
                            .name(cxt.db)
                            .map(|(n, _)| SplitId::Named(n))
                            .unwrap_or_else(|| {
                                i += 1;
                                SplitId::Idx(i - 1)
                            });
                        let def_node = cxt.db.def_node((x, cxt.def_cxt()));
                        (split, def_node)
                    })
                    .collect();
                cxt.pop();

                cxt.pop();
                Some(Definition {
                    name: x.name()?.name(cxt.db),
                    // Inline metas in all types involved after elaborating the constructors
                    // since metas caused by inferred types of type arguments can be solved in ctors
                    ty: Box::new(ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))),
                    body: DefBody::Type(
                        ctors
                            .into_iter()
                            .map(|(s, span, ty)| {
                                (
                                    s,
                                    span,
                                    ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                                        .eval(&mut cxt.env()),
                                )
                            })
                            .collect(),
                    ),
                    children,
                })
            }
            ast::Def::TypeDefShort(_) => todo!(),
            ast::Def::TypeDefStruct(_) => todo!(),
        }
    }
}

impl ast::Def {
    pub fn name(&self, db: &dyn Elaborator) -> Option<SName> {
        match self {
            ast::Def::LetDef(x) => x
                .pat()
                .and_then(|x| x.expr())
                .and_then(|x| x.as_let_def_pat(db))
                .and_then(|(n, _)| n)
                .map(|(_, n)| n),
            ast::Def::FunDef(x) => x.name().map(|x| x.name(db)),
            ast::Def::TypeDef(x) => x.name().map(|x| x.name(db)),
            ast::Def::TypeDefShort(x) => x.name().map(|x| x.name(db)),
            ast::Def::TypeDefStruct(x) => x.name().map(|x| x.name(db)),
        }
    }
}

fn infer_fun(
    implicit: Option<ast::ImpPars>,
    explicit: Option<SomePar>,
    ret_ty: Option<ast::Expr>,
    body: Option<ast::Body>,
    span: RelSpan,
    cxt: &mut Cxt,
) -> (Expr, Expr) {
    // [a, b] [c, d] (e, f) => ...
    // -->
    // [a, b, c, d] => ((e, f) => ...)

    cxt.push();
    let implicit = check_params(
        implicit
            .into_iter()
            .flat_map(|x| x.pars())
            .flat_map(
                |x| match x.par().and_then(|x| x.pat()).and_then(|x| x.expr()) {
                    Some(x) => x.as_args(),
                    None => vec![Err(x.span())],
                },
            )
            .collect(),
        true,
        ParamTys::Inferred,
        &CheckReason::UsedAsType,
        cxt,
    );
    let explicit = explicit.map_or(Vec::new(), |x| {
        check_params(
            x.par.as_args(),
            x.pat,
            ParamTys::Inferred,
            &CheckReason::UsedAsType,
            cxt,
        )
    });

    cxt.record_deps();
    let bspan = body.as_ref().map_or(span, |x| x.span());
    let (body, bty) = match ret_ty {
        Some(bty) => {
            let span = bty.span();
            let bty = bty.check(Val::Type, cxt, &CheckReason::UsedAsType);
            let bty = bty.eval(&mut cxt.env());
            let body = body
                .and_then(|x| x.expr())
                .map(|x| x.check(bty.clone(), cxt, &CheckReason::GivenType(span)))
                .unwrap_or_else(|| {
                    // cxt.error(span, "Missing function body");
                    Expr::Error
                });
            (body, bty)
        }
        None => body
            .and_then(|x| x.expr())
            .map(|x| x.infer(cxt))
            .unwrap_or_else(|| {
                // cxt.error(span, "Missing function body");
                (Expr::Error, Val::Error)
            }),
    };
    cxt.finish_deps(bspan); // TODO what do we do with this borrow
    let bty = bty.quote(cxt.size(), None);
    cxt.pop();

    // We have to evaluate this outside of the scope
    let mut ty = if explicit.is_empty() {
        bty
    } else {
        Expr::Fun(EClos {
            class: Pi(Expl),
            params: explicit.clone(),
            body: Box::new(bty),
        })
    };
    if !implicit.is_empty() {
        ty = Expr::Fun(EClos {
            class: Pi(Impl),
            params: implicit.clone(),
            body: Box::new(ty),
        });
    }
    let mut term = if explicit.is_empty() {
        body
    } else {
        Expr::Fun(EClos {
            class: Lam(Expl),
            params: explicit,
            body: Box::new(body),
        })
    };
    if !implicit.is_empty() {
        term = Expr::Fun(EClos {
            class: Lam(Impl),
            params: implicit,
            body: Box::new(term),
        });
    }

    (term, ty)
}

struct SomePar {
    par: ast::Expr,
    pat: bool,
}
trait IsPar {
    fn as_par(self) -> Option<SomePar>;
}
impl IsPar for ast::PatPar {
    fn as_par(self) -> Option<SomePar> {
        Some(SomePar {
            par: self.pat()?.expr()?,
            pat: true,
        })
    }
}
impl IsPar for ast::TermPar {
    fn as_par(self) -> Option<SomePar> {
        Some(SomePar {
            par: self.expr()?,
            pat: false,
        })
    }
}
impl<T: IsPar> IsPar for Option<T> {
    fn as_par(self) -> Option<SomePar> {
        self.and_then(T::as_par)
    }
}

fn check_params(
    pars: Vec<Result<ast::Expr, RelSpan>>,
    pat: bool,
    tys: ParamTys,
    reason: &CheckReason,
    cxt: &mut Cxt,
) -> Vec<Par> {
    let err_missing = tys.err_missing();
    tys.zip_with(
        pars.into_iter()
            .flat_map(|x| match x {
                Ok(x) => x.as_args(),
                e => vec![e],
            })
            .collect::<Vec<_>>()
            .into_iter(),
    )
    .into_iter()
    .map(|(ty, mut x)| {
        let x = match x.len() {
            1 => x.pop().unwrap(),
            _ => todo!("probably should do pattern elaboration"),
        };
        if ty.is_none() && err_missing {
            let span = match x.as_ref() {
                Ok(x) => x.span(),
                Err(span) => *span,
            };
            let (_m, name) = x
                .as_ref()
                .ok()
                .and_then(|x| x.as_simple_pat(cxt.db))
                .and_then(|x| x.0)
                .unwrap_or_else(|| (false, (cxt.db.name("_".to_string()), span)));
            cxt.error(
                span,
                Doc::start("Lambda contains extra parameter ")
                    .add(cxt.db.lookup_name(name.0), Doc::COLOR1)
                    .add(" which is not present in expected type", ()),
            );
        }
        check_par(x, pat, ty.map(|x| (x, reason)), cxt)
    })
    .collect()
}

fn check_par(
    x: Result<ast::Expr, RelSpan>,
    pat: bool,
    expected_ty: Option<(Expr, &CheckReason)>,
    cxt: &mut Cxt,
) -> Par {
    let (m, par) = match x {
        Ok(ast::Expr::Binder(x)) => {
            let (name, ty) = x
                .pat()
                .and_then(|x| x.expr())
                .map(|x| {
                    x.as_simple_pat(cxt.db)
                        .unwrap_or_else(|| todo!("move non-trivial pats to rhs"))
                })
                .unwrap_or((None, None));
            let (m, name) =
                name.unwrap_or_else(|| (false, (cxt.db.name("_".to_string()), x.span())));
            if ty.is_some() {
                cxt.error(
                    x.pat().unwrap().span(),
                    "Binder '_: _' not allowed in pattern of another binder",
                );
            }
            let ty = x
                .ty()
                .and_then(|x| x.expr())
                .map(|x| x.check(Val::Type, cxt, &CheckReason::UsedAsType))
                .unwrap_or_else(|| {
                    cxt.error(
                        x.span(),
                        "Binder '_: _' missing type on right-hand side; use '_' to infer type",
                    );
                    Expr::Error
                });
            if let Some((expected_ty, reason)) = expected_ty {
                let ty = ty.clone().eval(&mut cxt.env());
                let expected_ty = expected_ty.clone().eval(&mut cxt.env());
                cxt.unify(ty, expected_ty, reason)
                    .unwrap_or_else(|e| cxt.error(x.span(), e));
            }
            (m, Par { name, ty })
        }
        Ok(x) if pat => {
            let (name, ty) = x
                .as_simple_pat(cxt.db)
                .unwrap_or_else(|| todo!("move non-trivial pats to rhs"));
            let (m, name) =
                name.unwrap_or_else(|| (false, (cxt.db.name("_".to_string()), x.span())));
            let ty = match ty.map(|x| x.check(Val::Type, cxt, &CheckReason::UsedAsType)) {
                Some(ty) => {
                    if let Some((expected_ty, reason)) = expected_ty {
                        let ty = ty.clone().eval(&mut cxt.env());
                        let expected_ty = expected_ty.clone().eval(&mut cxt.env());
                        cxt.unify(ty, expected_ty, reason)
                            .unwrap_or_else(|e| cxt.error(x.span(), e));
                    }
                    ty
                }
                None => expected_ty.map(|(x, _)| x).unwrap_or_else(|| {
                    cxt.mcxt
                        .new_meta(cxt.locals(), MetaBounds::new(Val::Type), x.span())
                }),
            };
            (m, Par { name, ty })
        }
        Ok(x) => {
            let ty = x.check(Val::Type, cxt, &CheckReason::UsedAsType);
            (
                false,
                Par {
                    name: (cxt.db.name("_".to_string()), x.span()),
                    ty,
                },
            )
        }
        Err(span) => {
            if let Some((ty, reason)) = expected_ty {
                let ty = ty.eval(&mut cxt.env());
                cxt.unify(Val::var(Var::Builtin(Builtin::UnitType)), ty, reason)
                    .unwrap_or_else(|e| cxt.error(span, e));
            }
            (
                false,
                Par {
                    name: (cxt.db.name("_".to_string()), span),
                    ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                },
            )
        }
    };
    // Define each parameter so it can be used by the types of the rest
    cxt.define_local(par.name, par.ty.clone().eval(&mut cxt.env()), None, None, m);
    par
}

impl ast::Pair {
    fn elab_sigma(&self, cxt: &mut Cxt) -> Result<Expr, TypeError> {
        {
            let (_, ty) = infer_fun(
                None,
                self.lhs().map(|par| SomePar { par, pat: false }),
                self.rhs(),
                None,
                self.span(),
                cxt,
            );
            match ty {
                Expr::Fun(mut clos) => {
                    if clos.params.len() != 1 {
                        panic!(
                            "not supported for now: more than one parameter in sigma type; got {}",
                            clos.params.len()
                        );
                    }
                    clos.class = Sigma;
                    return Ok(Expr::Fun(clos));
                }
                _ => unreachable!(),
            }
        }
    }
}

enum ParamTys<'a, 'b> {
    Impl(&'a mut VecDeque<&'b Par>),
    Expl(Expr),
    Inferred,
}
impl ParamTys<'_, '_> {
    fn err_missing(&self) -> bool {
        !matches!(self, ParamTys::Inferred)
    }

    fn zip_with<T>(self, it: impl ExactSizeIterator<Item = T>) -> Vec<(Option<Expr>, Vec<T>)> {
        match self {
            ParamTys::Inferred => it.map(|x| (None, vec![x])).collect(),
            ParamTys::Impl(v) => it
                .map(|x| (v.pop_front().map(|par| par.ty.clone()), vec![x]))
                .collect(),
            ParamTys::Expl(t) => {
                let len = it.len();
                let (t, vec) =
                    it.enumerate()
                        .fold((Some(t), Vec::new()), |(t, mut vec), (i, x)| match t {
                            Some(Expr::Fun(EClos {
                                class: Sigma,
                                mut params,
                                body,
                            })) if i + 1 != len => {
                                assert_eq!(params.len(), 1);
                                let ty = params.pop().unwrap().ty;
                                vec.push((Some(ty), vec![x]));
                                (Some(*body), vec)
                            }
                            Some(t) => {
                                vec.push((Some(t), vec![x]));
                                (None, vec)
                            }
                            None => {
                                vec.last_mut().unwrap().1.push(x);
                                (None, vec)
                            }
                        });
                if t.is_some() {
                    todo!("this should mean there were no parameters")
                }
                vec
            }
        }
    }
}

impl Expr {
    /// If `term` of type `ty` takes implicit parameters, insert metas to apply them.
    fn insert_metas(
        self,
        ty: Val,
        imp_args: Option<ast::ImpArgs>,
        span: RelSpan,
        cxt: &mut Cxt,
    ) -> (Expr, Val) {
        match ty {
            Val::Fun(clos) if clos.class == Pi(Impl) => {
                let mut args: VecDeque<_> = imp_args
                    .into_iter()
                    .flat_map(|x| x.args())
                    .flat_map(|x| x.expr().map(|x| x.as_args()).unwrap_or(vec![Err(x.span())]))
                    .collect();
                let mut targs: Vec<Expr> = Vec::new();
                let par_ty = clos.par_ty();
                let rty = clos.elab_with(|aty| match args.pop_front() {
                    Some(arg) => match arg {
                        Ok(arg) => {
                            let arg = arg.check(aty, cxt, &CheckReason::ArgOf(span));
                            targs.push(arg.clone());
                            arg.eval(&mut cxt.env())
                        }
                        Err(span) => {
                            if let Err(e) = cxt.unify(
                                Val::var(Var::Builtin(Builtin::UnitType)),
                                aty,
                                &CheckReason::ArgOf(span),
                            ) {
                                cxt.error(span, e);
                                Val::Error
                            } else {
                                targs.push(Expr::var(Var::Builtin(Builtin::Unit)));
                                Val::var(Var::Builtin(Builtin::Unit))
                            }
                        }
                    },
                    None => {
                        // Apply a new metavariable
                        let e = cxt.mcxt.new_meta(cxt.locals(), MetaBounds::new(aty), span);
                        targs.push(e.clone());
                        e.eval(&mut cxt.env())
                    }
                });
                let ty = par_ty.quote(cxt.size(), None);

                fn make_arg(
                    mut v: impl Iterator<Item = Expr>,
                    ty: Expr,
                    cxt: &Cxt,
                ) -> Option<Expr> {
                    let a = v.next()?;
                    let ty2 = match ty.clone() {
                        Expr::Fun(EClos {
                            class: Sigma, body, ..
                        }) => {
                            let mut env = cxt.env();
                            env.push(Some(Ok(a.clone().eval(&mut cxt.env()))));
                            body.eval_quote(&mut env, cxt.size(), None)
                        }
                        _ => Expr::Error,
                    };
                    match make_arg(v, ty2, cxt) {
                        Some(b) => Some(Expr::Pair(Box::new(a), Box::new(b), Box::new(ty))),
                        None => Some(a),
                    }
                }
                let arg = make_arg(targs.into_iter(), ty, cxt).unwrap();

                (
                    Expr::Elim(Box::new(self), Box::new(Elim::App(Impl, arg))),
                    rty,
                )
            }
            _ => (self, ty),
        }
    }
}

pub(super) fn resolve_member(
    lhs: Expr,
    mut lhs_ty: Val,
    member: ast::Member,
    cxt: &mut Cxt,
) -> (Expr, Val) {
    if let Some(name) = member.var().map(|x| x.name(cxt.db)) {
        lhs_ty.inline_head(&mut cxt.env(), &cxt.mcxt);
        match &lhs_ty {
            Val::Error => (),
            // TODO struct members
            // TODO methods
            _ => {
                let mut lhs_val = lhs.clone().eval(&mut cxt.env());
                lhs_val.inline_head(&mut cxt.env(), &cxt.mcxt);
                match lhs_val {
                    Val::Neutral(n) => match n.head() {
                        Head::Var(Var::Def(def_name, def)) => {
                            let edef = cxt.db.def_elab(def);
                            match edef
                                .as_ref()
                                .and_then(|x| x.result.as_ref())
                                .map(|x| &x.body)
                            {
                                Some(DefBody::Type(ctors)) => {
                                    if let Some((split, _, ty)) =
                                        ctors.iter().find(|(s, _, _)| *s == SplitId::Named(name.0))
                                    {
                                        return (
                                            Expr::var(Var::Cons(name, cxt.db.cons_id(def, *split))),
                                            ty.clone(),
                                        );
                                    } else if let Some((split, _)) = edef
                                        .unwrap()
                                        .result
                                        .unwrap()
                                        .children
                                        .into_iter()
                                        .find(|(s, _)| *s == SplitId::Named(name.0))
                                    {
                                        let def = cxt.db.def(DefLoc::Child(def, split));
                                        let ty = cxt
                                            .db
                                            .def_type(def)
                                            .and_then(|x| x.result)
                                            .unwrap_or(Val::Error);
                                        return (Expr::var(Var::Def(name, def)), ty);
                                    } else {
                                        cxt.error(
                                            member.span(),
                                            Doc::start("Type ")
                                                .add(cxt.db.lookup_name(def_name.0), Doc::COLOR2)
                                                .add(" has no member ", ())
                                                .add(cxt.db.lookup_name(name.0), Doc::COLOR1),
                                        );
                                        return (Expr::Error, Val::Error);
                                    }
                                }
                                _ => (),
                            }
                        }
                        _ => (),
                    },
                    _ => (),
                }
            }
        }
    }
    cxt.error(
        member.span(),
        Doc::start("Value of type '")
            .chain(
                lhs_ty
                    .clone()
                    .quote(cxt.size(), Some(&cxt.mcxt))
                    .pretty(cxt.db),
            )
            .add("' does not have members", ()),
    );
    (Expr::Error, Val::Error)
}

enum PlaceOrExpr {
    Place(Place),
    Expr(Expr, Val, Borrow, RelSpan),
}
enum Place {
    Var(VarEntry),
    Deref(Box<PlaceOrExpr>),
}
impl Place {
    fn ty(&self, cxt: &Cxt) -> Result<Val, TypeError> {
        match self {
            Place::Var(v) => Ok(v.ty(cxt)),
            Place::Deref(e) => {
                let ty = match &**e {
                    PlaceOrExpr::Place(t) => t.ty(cxt)?,
                    PlaceOrExpr::Expr(_, ty, _, _) => ty.clone(),
                };
                if let Val::RefType(_, ty) = ty {
                    Ok(*ty)
                } else {
                    Err(TypeError::Other(
                        Doc::start("Expected reference after unary *, got ")
                            .chain(ty.quote(cxt.size(), Some(&cxt.mcxt)).pretty(cxt.db)),
                    ))
                }
            }
        }
    }

    fn to_expr(self, cxt: &Cxt) -> Expr {
        match self {
            Place::Var(v) => Expr::var(v.var(cxt).cvt(cxt.size())),
            Place::Deref(e) => Expr::Deref(Box::new(match *e {
                PlaceOrExpr::Place(p) => p.to_expr(cxt),
                PlaceOrExpr::Expr(e, _, _, _) => e,
            })),
        }
    }

    /// Makes sure the access is valid, invalidating other borrows appropriately, and adds needed dependencies to the cxt
    fn try_access(&self, kind: AccessKind, cxt: &mut Cxt) -> Result<(), TypeError> {
        match self {
            Place::Var(v) => {
                let r = match kind {
                    AccessKind::Mut | AccessKind::Imm => {
                        let mutable = kind == AccessKind::Mut;
                        v.try_borrow(mutable, cxt).map_err(Into::into)
                    }
                    AccessKind::Move => v
                        .try_move(self.ty(cxt)?.quote(cxt.size(), Some(&cxt.mcxt)), cxt)
                        .map_err(Into::into),
                    AccessKind::Copy => Ok(()),
                };
                if let Some(borrow) = v.borrow(cxt) {
                    cxt.add_dep(borrow, v.access(kind));
                }
                r
            }
            Place::Deref(_) if kind == AccessKind::Move => {
                Err("Cannot move out of reference".into())
            } // TODO type information (make this a MoveError variant)
            Place::Deref(e) => {
                let ty = match &**e {
                    PlaceOrExpr::Place(p) => {
                        p.try_access(kind, cxt)?;
                        Cow::Owned(p.ty(cxt)?)
                    }
                    PlaceOrExpr::Expr(_, t, b, s) => {
                        cxt.add_dep(
                            *b,
                            Access {
                                kind,
                                name: cxt.db.name("<expression>".into()),
                                span: *s,
                            },
                        );
                        Cow::Borrowed(t)
                    }
                };
                match kind {
                    AccessKind::Mut | AccessKind::Imm => {
                        let mutable = kind == AccessKind::Mut;
                        match &*ty {
                            Val::RefType(m, _) => {
                                if mutable && !m {
                                    return Err(TypeError::Other(
                                        "Cannot mutate through an immutable reference".into(),
                                    ));
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    _ => (),
                }
                Ok(())
            }
        }
    }
}

impl ast::Expr {
    pub(super) fn check(&self, mut ty: Val, cxt: &mut Cxt, reason: &CheckReason) -> Expr {
        ty.inline_head(&mut cxt.env(), &cxt.mcxt);
        let result = || {
            match (self, ty) {
                (ast::Expr::GroupedExpr(x), ty) if x.expr().is_some() => {
                    Ok(x.expr().unwrap().check(ty, cxt, reason))
                }

                // Infer assumes (a, b) is a pair, so elaborate as sigma if checking against Type
                (ast::Expr::Pair(x), Val::Type) => x.elab_sigma(cxt),
                // Same for ()
                (ast::Expr::GroupedExpr(x), Val::Type) if x.expr().is_none() => {
                    Ok(Expr::var(Var::Builtin(Builtin::UnitType)))
                }

                // Check pair against sigma and lambda against pi
                (ast::Expr::Pair(x), Val::Fun(clos)) if clos.class == Sigma => {
                    assert_eq!(clos.params.len(), 1);
                    let ety = clos.clone().quote(cxt.size(), None);
                    let a = x.lhs().ok_or("Missing pair left-hand side value")?.check(
                        clos.par_ty(),
                        cxt,
                        reason,
                    );
                    // TODO make this lazy
                    let va = a.clone().eval(&mut cxt.env());
                    let bty = clos.apply(va);
                    let b = x
                        .rhs()
                        .ok_or("Missing pair right-hand side value")?
                        .check(bty, cxt, reason);
                    Ok(Expr::Pair(
                        Box::new(a),
                        Box::new(b),
                        Box::new(Expr::Fun(ety)),
                    ))
                }
                (ast::Expr::Lam(x), Val::Fun(clos)) if matches!(clos.class, Pi(_)) => {
                    // [a, b] [c, d] (e, f) => ...
                    // -->
                    // [a, b, c, d] => ((e, f) => ...)

                    let mut clos = clos.move_env(&mut cxt.env());

                    cxt.push();
                    let mut implicit_tys: VecDeque<_> = match clos.class.icit() {
                        Some(Impl) => clos.params.iter().collect(),
                        _ => VecDeque::new(),
                    };
                    let mut implicit: Vec<_> = check_params(
                        x.imp_par()
                            .into_iter()
                            .flat_map(|x| x.pars())
                            .map(|x| {
                                x.par()
                                    .and_then(|x| x.pat())
                                    .and_then(|x| x.expr())
                                    .ok_or_else(|| x.span())
                            })
                            .collect(),
                        true,
                        ParamTys::Impl(&mut implicit_tys),
                        reason,
                        cxt,
                    );
                    // Add any implicit parameters in the type but not the lambda to the lambda
                    // Make sure, however, that they can't actually be accessed by name by code in the lambda
                    for par in implicit_tys {
                        cxt.define_local(
                            (par.name.0.inaccessible(cxt.db), par.name.1),
                            par.ty.clone().eval(&mut cxt.env()),
                            None,
                            None,
                            false,
                        );
                        implicit.push(par.clone());
                    }
                    if !implicit.is_empty() {
                        // This is all fine since we keep cxt.size() at the level that the parameters expect
                        assert_eq!(cxt.size(), clos.env.size + clos.params.len());
                        let mut body = clos.body.eval(&mut cxt.env());
                        body.inline_head(&mut cxt.env(), &cxt.mcxt);
                        match body {
                            Val::Fun(c) if c.class == Pi(Expl) => {
                                clos = *c;
                                if clos.env.size != cxt.size() {
                                    clos = clos.move_env(&mut cxt.env());
                                }
                            }
                            body => {
                                if x.exp_par().is_some() {
                                    // TODO better error here (include type)
                                    return Err("Lambda contains explicit parameters which are not present in expected type".into());
                                } else {
                                    clos = VClos {
                                        class: Pi(Expl),
                                        params: Vec::new(),
                                        env: cxt.env(),
                                        body: body.quote(cxt.size(), None),
                                    }
                                }
                            }
                        }
                    }

                    let explicit = if let Some(e) = x.exp_par() {
                        check_params(
                            vec![e.pat().and_then(|e| e.expr()).ok_or_else(|| x.span())],
                            true,
                            ParamTys::Expl(clos.par_ty().quote(cxt.size(), None)),
                            reason,
                            cxt,
                        )
                    } else {
                        if !clos.params.is_empty() {
                            return Err(Doc::start("Expected explicit parameters of type '")
                                .chain(
                                    clos.par_ty()
                                        .quote(cxt.size(), Some(&cxt.mcxt))
                                        .pretty(cxt.db),
                                )
                                .add("'", ())
                                .into());
                        }
                        Vec::new()
                    };

                    assert_eq!(cxt.size(), clos.env.size + clos.params.len());
                    let bty = clos.body.eval(&mut cxt.env());
                    let body = x
                        .body()
                        .and_then(|x| x.expr())
                        .ok_or("Missing body for lambda")?
                        .check(bty, cxt, reason);
                    cxt.pop();

                    let mut term = if explicit.is_empty() {
                        body
                    } else {
                        Expr::Fun(EClos {
                            class: Lam(Expl),
                            params: explicit,
                            body: Box::new(body),
                        })
                    };
                    if !implicit.is_empty() {
                        term = Expr::Fun(EClos {
                            class: Lam(Impl),
                            params: implicit,
                            body: Box::new(term),
                        });
                    }
                    Ok(term)
                }

                // Propagate through case/do/etc.
                (ast::Expr::Case(case), ty) => {
                    let mut rty = Some((ty, reason.clone()));
                    let (scrutinee, case, cty) = case.elaborate(&mut rty, cxt);
                    Ok(Expr::Elim(
                        Box::new(scrutinee),
                        Box::new(Elim::Case(case, cty)),
                    ))
                }
                (ast::Expr::Do(d), ty) => {
                    let mut rty = Some((ty, reason.clone()));
                    let expr = d.elaborate(&mut rty, cxt);
                    Ok(expr)
                }

                // Insert implicit lambdas when checking against an implicit function type
                // TODO this should probably be off by default, or at least more restricted
                // But unfortunately it's kind of required for certain fancy dependent type things
                // (like dependent composition)
                (_, Val::Fun(clos)) if clos.class == Pi(Impl) => {
                    let clos = clos.move_env(&mut cxt.env());
                    let mut params = clos.params.clone();
                    let bty = clos.open(cxt.size());

                    cxt.push();
                    for i in &mut params {
                        i.name.0 = i.name.0.inaccessible(cxt.db);
                        cxt.define_local(
                            i.name,
                            i.ty.clone().eval(&mut cxt.env()),
                            None,
                            None,
                            false,
                        );
                    }

                    let body = self.check(bty, cxt, reason);

                    let clos = EClos {
                        class: Lam(Impl),
                        params,
                        body: Box::new(body),
                    };

                    cxt.pop();
                    Ok(Expr::Fun(clos))
                }

                // Autoref
                (_, Val::RefType(m, ty)) => {
                    let (x, xty) = match self.elab_place(cxt) {
                        Some(p) => {
                            let ty = p.ty(cxt)?;
                            (Ok(p), ty)
                        }
                        None => {
                            let (x, xty) = self.infer(cxt);
                            (Err(x), xty)
                        }
                    };

                    match cxt.unify(xty.clone(), Val::RefType(m, ty.clone()), reason) {
                        Ok(()) => return self.infer_check(Val::RefType(m, ty), cxt, reason),
                        Err(error) => {
                            if cxt.unify(xty.clone(), (*ty).clone(), reason).is_ok() {
                                // Autoref time
                            } else if !m
                                && cxt
                                    .unify(xty.clone(), Val::RefType(true, ty.clone()), reason)
                                    .is_ok()
                            {
                                // Degrade from mutable to immutable reference
                                // so we do nothing here, we're just immutably borrowing from the mutable reference
                            } else {
                                return Err(error.into());
                            }
                        }
                    }

                    match x {
                        Ok(place) => {
                            place.try_access(AccessKind::borrow(m), cxt)?;
                            Ok(Expr::Ref(m, Box::new(place.to_expr(cxt))))
                        }
                        Err(expr) => Ok(Expr::Ref(m, Box::new(expr))),
                    }
                }
                (_, ty) => self.infer_check(ty, cxt, reason),
            }
        };
        // TODO auto-applying implicits (probably? only allowing them on function calls is also an option to consider)
        match result() {
            Ok(x) => Expr::Spanned(self.span(), Box::new(x)),
            Err(e) => {
                cxt.error(self.span(), e);
                Expr::Error
            }
        }
    }

    fn infer_check(&self, ty: Val, cxt: &mut Cxt, reason: &CheckReason) -> Result<Expr, TypeError> {
        let (a, ity) = self.infer(cxt);
        let (a, ity) = match &ty {
            Val::Fun(clos) if clos.class == Pi(Impl) => (a, ity),
            _ => a.insert_metas(ity, None, self.span(), cxt),
        };
        cxt.unify(ity, ty, reason)?;
        Ok(a)
    }

    fn elab_place(&self, cxt: &mut Cxt) -> Option<Place> {
        match self {
            ast::Expr::Var(n) => {
                let entry = cxt.lookup(n.name(cxt.db))?;
                Some(Place::Var(entry))
            }
            ast::Expr::Deref(e) => {
                // Doesn't do type checking
                match e.expr()?.elab_place(cxt) {
                    Some(place) => Some(Place::Deref(Box::new(PlaceOrExpr::Place(place)))),
                    None => {
                        cxt.record_deps();
                        let (e, ty) = e.expr()?.infer(cxt);
                        let borrow = cxt.finish_deps(self.span())?;
                        Some(Place::Deref(Box::new(PlaceOrExpr::Expr(
                            e,
                            ty,
                            borrow,
                            self.span(),
                        ))))
                    }
                }
            }
            _ => None,
        }
    }

    pub fn as_args(self) -> Vec<Result<ast::Expr, RelSpan>> {
        match self {
            ast::Expr::GroupedExpr(ref x) => x
                .expr()
                .map(|x| x.as_args())
                .unwrap_or_else(|| vec![Err(x.span())]),
            ast::Expr::Pair(x) => {
                let mut v = x
                    .rhs()
                    .map(|x| x.as_args())
                    .unwrap_or_else(|| vec![Err(x.span())]);
                v.insert(0, x.lhs().ok_or(x.span()));
                v
            }
            _ => vec![Ok(self)],
        }
    }

    fn as_simple_pat(
        &self,
        db: &dyn Elaborator,
    ) -> Option<(Option<(bool, SName)>, Option<ast::Expr>)> {
        match self {
            ast::Expr::MutVar(x) => Some((Some((true, x.var()?.name(db))), None)),
            ast::Expr::Var(x) => Some((Some((false, x.name(db))), None)),
            ast::Expr::Binder(x) => {
                let (name, old_ty) = x.pat()?.expr()?.as_simple_pat(db)?;
                if old_ty.is_some() {
                    // ((x: A): B) is an error, let the actual pattern compilation code handle it
                    None
                } else {
                    Some((name, x.ty().and_then(|x| x.expr())))
                }
            }
            ast::Expr::GroupedExpr(x) => x
                .expr()
                .map(|x| x.as_simple_pat(db))
                // For (), we return this expression as the type, since it's identical syntactically
                .unwrap_or_else(|| {
                    Some((
                        Some((false, (db.name("_".to_string()), self.span()))),
                        Some(self.clone()),
                    ))
                }),
            _ => None,
        }
    }

    pub(super) fn infer(&self, cxt: &mut Cxt) -> (Expr, Val) {
        // TODO hopefully try {} blocks stabilize soon and this won't be necessary
        let mut result = || {
            Ok({
                match self {
                    ast::Expr::Var(name) => {
                        let name = name.name(cxt.db);
                        if name.0 == cxt.db.name("_".to_string()) {
                            let mty = cxt
                                .mcxt
                                .new_meta(cxt.locals(), MetaBounds::new(Val::Type), self.span())
                                .eval(&mut cxt.env());
                            let meta = cxt.mcxt.new_meta(
                                cxt.locals(),
                                MetaBounds::new(mty.clone()),
                                self.span(),
                            );
                            (meta, mty)
                        } else {
                            let entry = cxt.lookup(name).ok_or(TypeError::NotFound(name.0))?;
                            let ty = entry.ty(cxt);

                            let access = Access {
                                name: name.0,
                                span: name.1,
                                kind: AccessKind::copy_move(ty.can_copy(cxt)),
                            };
                            if access.kind == AccessKind::Move {
                                entry
                                    .try_move(ty.clone().quote(cxt.size(), Some(&cxt.mcxt)), cxt)?
                            } else if let Some(borrow) = entry.borrow(cxt) {
                                cxt.check_deps(borrow, access)?
                            }
                            // This expression depends on everything the variable depends on
                            if let Some(borrow) = entry.borrow(cxt) {
                                cxt.add_dep(borrow, access);
                            }

                            (Expr::var(entry.var(cxt).cvt(cxt.size())), ty)
                        }
                    }
                    ast::Expr::Lam(x) => {
                        let (term, ty) = infer_fun(
                            x.imp_par(),
                            x.exp_par().as_par(),
                            None,
                            x.body(),
                            x.span(),
                            cxt,
                        );
                        (term, ty.eval(&mut cxt.env()))
                    }
                    ast::Expr::Pi(x) => {
                        let (_, pi) = infer_fun(
                            x.imp_par(),
                            x.exp_par().as_par(),
                            x.body().and_then(|x| x.expr()),
                            None,
                            x.span(),
                            cxt,
                        );
                        (pi, Val::Type)
                    }
                    ast::Expr::Reference(x) => {
                        let x = x.expr().ok_or("Expected type of reference")?.check(
                            Val::Type,
                            cxt,
                            &CheckReason::UsedAsType,
                        );
                        (Expr::RefType(false, Box::new(x)), Val::Type)
                    }
                    ast::Expr::RefMut(x) => {
                        let x = x.expr().ok_or("Expected type of reference")?.check(
                            Val::Type,
                            cxt,
                            &CheckReason::UsedAsType,
                        );
                        (Expr::RefType(true, Box::new(x)), Val::Type)
                    }
                    ast::Expr::Deref(_) => {
                        let place = self.elab_place(cxt).ok_or("Expected reference after *")?;
                        let xty = place.ty(cxt)?;
                        // A bare deref must be a copy
                        place.try_access(AccessKind::Copy, cxt)?;
                        let x = place.to_expr(cxt);
                        if !xty.can_copy(cxt) {
                            match x.unspanned() {
                                Expr::Head(Head::Var(Var::Local((n, _), _))) => {
                                    return Err(MoveError::InvalidMove(
                                        Doc::start("Cannot move out of reference"),
                                        *n,
                                        Box::new(xty.quote(cxt.size(), Some(&cxt.mcxt))),
                                    )
                                    .into())
                                }
                                _ => {
                                    return Err(TypeError::Other(
                                        Doc::start("Cannot move out of reference of type ").chain(
                                            xty.quote(cxt.size(), Some(&cxt.mcxt)).pretty(cxt.db),
                                        ),
                                    ))
                                }
                            }
                        }
                        (x, xty)
                    }
                    ast::Expr::Assign(x) => {
                        let place = x
                            .lhs()
                            .ok_or("Missing left-hand side of assignment")?
                            .elab_place(cxt)
                            .ok_or("Cannot assign to expression")?;
                        let ty = place.ty(cxt)?;
                        place.try_access(AccessKind::Mut, cxt)?;
                        let expr = x
                            .rhs()
                            .ok_or("Missing right-hand side of assignment")?
                            .check(ty, cxt, &CheckReason::MustMatch(x.lhs().unwrap().span()));
                        (
                            Expr::Assign(Box::new(place.to_expr(cxt)), Box::new(expr)),
                            Val::var(Var::Builtin(Builtin::UnitType)),
                        )
                    }
                    ast::Expr::App(x) => {
                        let (mut lhs, mut lhs_ty) = x
                            .lhs()
                            .ok_or("Missing left-hand side of application")?
                            .infer(cxt);
                        lhs_ty.inline_head(&mut cxt.env(), &cxt.mcxt);
                        let mut lhs_span = x.lhs().unwrap().span();
                        if let Some(member) = x.member() {
                            (lhs, lhs_ty) = resolve_member(lhs, lhs_ty, member, cxt);
                        }

                        // First handle implicit arguments, then curry and apply explicits
                        let (lhs, lhs_ty) = lhs.insert_metas(lhs_ty, x.imp(), lhs_span, cxt);
                        lhs_span.end = x.imp().map(|x| x.span()).unwrap_or(lhs_span).end;

                        // Apply explicit arguments
                        if let Some(exp) = x.exp() {
                            match lhs_ty {
                                Val::Fun(clos) if matches!(clos.class, Pi(_)) => {
                                    let aty = clos.par_ty();
                                    let exp = exp.check(aty, cxt, &CheckReason::ArgOf(lhs_span));
                                    let vexp = exp.clone().eval(&mut cxt.env());
                                    let rty = clos.apply(vexp);
                                    (
                                        Expr::Elim(Box::new(lhs), Box::new(Elim::App(Expl, exp))),
                                        rty,
                                    )
                                }
                                Val::Error => {
                                    // Still try inferring the argument to catch errors
                                    let (exp, _) = exp.infer(cxt);
                                    (
                                        Expr::Elim(Box::new(lhs), Box::new(Elim::App(Expl, exp))),
                                        Val::Error,
                                    )
                                }
                                lhs_ty => {
                                    return Err(TypeError::NotFunction(
                                        lhs_ty.quote(cxt.size(), Some(&cxt.mcxt)),
                                        lhs_span,
                                    ))
                                }
                            }
                        } else {
                            (lhs, lhs_ty)
                        }
                    }
                    ast::Expr::Do(d) => {
                        let mut rty = None;
                        let expr = d.elaborate(&mut rty, cxt);
                        let rty = rty.map(|(x, _)| x).unwrap_or(Val::Error);
                        (expr, rty)
                    }
                    ast::Expr::Case(case) => {
                        let mut rty = None;
                        let (scrutinee, case, cty) = case.elaborate(&mut rty, cxt);
                        let rty = rty.map(|(x, _)| x).unwrap_or(Val::Error);
                        (
                            Expr::Elim(Box::new(scrutinee), Box::new(Elim::Case(case, cty))),
                            rty,
                        )
                    }
                    ast::Expr::Lit(l) => match l.to_literal(cxt) {
                        Ok(l) => (
                            Expr::Lit(l),
                            match l {
                                Literal::Int(_, ty) => match ty {
                                    Ok(t) => Val::var(Var::Builtin(Builtin::IntType(t))),
                                    Err((_, m)) => Val::var(Var::Meta(m)),
                                },
                                Literal::F64(_) => todo!(),
                                Literal::F32(_) => todo!(),
                                Literal::String(_) => Val::var(Var::Builtin(Builtin::StringType)),
                            },
                        ),
                        Err(e) => {
                            cxt.error(self.span(), e);
                            (Expr::Error, Val::Error)
                        }
                    },
                    ast::Expr::BinOp(x) => {
                        let tok = x.op().ok_or("Missing operator")?;
                        let tok = tok
                            .syntax()
                            .unwrap()
                            .children_with_tokens()
                            .find_map(|x| x.as_token().map(|x| x.kind()).filter(|x| x.is_binop()))
                            .unwrap_or(crate::parsing::SyntaxKind::Error);

                        match tok {
                            tok if ArithOp::from_tok(tok).is_some()
                                || CompOp::from_tok(tok).is_some() =>
                            {
                                let (a, ty) = x
                                    .a()
                                    .ok_or_else(|| {
                                        TypeError::Other(
                                            Doc::start("Missing left operand for operator ")
                                                .add(tok, Doc::COLOR1),
                                        )
                                    })?
                                    .infer(cxt);
                                let b = x
                                    .b()
                                    .ok_or_else(|| {
                                        TypeError::Other(
                                            Doc::start("Missing right operand for operator ")
                                                .add(tok, Doc::COLOR1),
                                        )
                                    })?
                                    .check(
                                        ty.clone(),
                                        cxt,
                                        &CheckReason::MustMatch(x.a().unwrap().span()),
                                    );
                                let (builtin, ret_ty) = ArithOp::from_tok(tok)
                                    .map(|x| (Builtin::ArithOp(x), ty.clone()))
                                    .or_else(|| {
                                        CompOp::from_tok(tok).map(|x| {
                                            (
                                                Builtin::CompOp(x),
                                                Val::var(Var::Builtin(Builtin::BoolType)),
                                            )
                                        })
                                    })
                                    .unwrap();
                                (
                                    Expr::Elim(
                                        Box::new(Expr::var(Var::Builtin(builtin))),
                                        Box::new(Elim::App(
                                            Expl,
                                            Expr::Pair(
                                                Box::new(a),
                                                Box::new(b),
                                                Box::new(Expr::Fun(EClos {
                                                    class: Sigma,
                                                    params: vec![Par {
                                                        name: (
                                                            cxt.db.name("_".into()),
                                                            x.a().unwrap().span(),
                                                        ),
                                                        ty: ty.clone().quote(cxt.size(), None),
                                                    }],
                                                    body: Box::new(
                                                        ty.clone().quote(cxt.size().inc(), None),
                                                    ),
                                                })),
                                            ),
                                        )),
                                    ),
                                    ret_ty,
                                )
                            }
                            tok => {
                                return Err(TypeError::Other(
                                    Doc::start("Invalid operator ").add(tok, Doc::COLOR1),
                                ))
                            }
                        }
                    }
                    ast::Expr::If(_) => todo!(),
                    ast::Expr::Box(_) => todo!(),
                    ast::Expr::Type(_) => (Expr::Type, Val::Type),
                    ast::Expr::GroupedExpr(e) => match e.expr() {
                        Some(e) => e.infer(cxt),
                        // Assume () is the unit value by default, it's only the unit type if it's checked against Type
                        None => (
                            Expr::var(Var::Builtin(Builtin::Unit)),
                            Val::var(Var::Builtin(Builtin::UnitType)),
                        ),
                    },
                    ast::Expr::Pair(x) => {
                        if let Some(ast::Expr::Binder(_)) = x.lhs() {
                            let term = x.elab_sigma(cxt)?;
                            return Ok((term, Val::Type));
                        }
                        // Infer a simple non-dependent pair type by default; inference is undecidable with sigma types
                        let (a, aty) = x.lhs().ok_or("missing left value in pair")?.infer(cxt);
                        let (b, bty) = x.rhs().ok_or("missing right value in pair")?.infer(cxt);
                        let aty = aty.quote(cxt.size(), None);
                        // bty is quoted inside of the sigma scope
                        let bty = bty.quote(cxt.size().inc(), None);
                        let ty = Expr::Fun(EClos {
                            class: Sigma,
                            params: vec![Par {
                                name: (cxt.db.name("_".to_string()), x.lhs().unwrap().span()),
                                ty: aty,
                            }],
                            body: Box::new(bty),
                        });
                        let vty = ty.clone().eval(&mut cxt.env());
                        (Expr::Pair(Box::new(a), Box::new(b), Box::new(ty)), vty)
                    }
                    ast::Expr::EffPat(_) => todo!(),
                    ast::Expr::Binder(_) => {
                        return Err(TypeError::Other(Doc::start(
                            "Binder '_: _' not allowed in this context",
                        )))
                    }
                    ast::Expr::MutVar(_) => {
                        return Err(TypeError::Other(Doc::start(
                            "'mut' not allowed in this context",
                        )))
                    }
                    ast::Expr::StructInit(_) => todo!(),
                }
            })
        };
        // TODO auto-applying implicits (probably? only allowing them on function calls is also an option to consider)
        match result() {
            Ok((x, t)) => (Expr::Spanned(self.span(), Box::new(x)), t),
            Err(e) => {
                cxt.error(self.span(), e);
                (Expr::Error, Val::Error)
            }
        }
    }
}

impl ast::Lit {
    pub(super) fn to_literal(&self, cxt: &mut Cxt) -> Result<Literal, String> {
        if let Some(l) = self.string() {
            // Process escape sequences to get the string's actual contents
            // This work is also done by the lexer, which then throws it away;
            // TODO move all error checking here and simplify the lexer code (same for numbers)
            let mut buf = String::new();
            let mut chars = l.text().chars().skip_while(|x| x.is_whitespace());
            loop {
                match chars.next() {
                    Some('"') => break,
                    Some('\\') => {
                        // Escape
                        match chars.next() {
                            Some('\\') => {
                                buf.push('\\');
                            }
                            Some('n') => {
                                buf.push('\n');
                            }
                            Some('t') => {
                                buf.push('\t');
                            }
                            _ => {
                                panic!("Invalid escape should have been caught in lexer");
                            }
                        }
                    }
                    Some(c) => buf.push(c),
                    None => {
                        panic!("Unclosed string should have been caught in lexer")
                    }
                }
            }
            Ok(Literal::String(cxt.db.name(buf)))
        } else if let Some(l) = self.int().or(self.float()) {
            let num = lex_number(l.text()).map_err(|e| format!("Invalid literal: {}", e))?;
            match num {
                NumLiteral::IPositive(i) => {
                    let meta = cxt
                        .mcxt
                        .unscoped_meta(MetaBounds::int_type(false, i), self.span());
                    Ok(Literal::Int(i, Err((false, meta))))
                }
                NumLiteral::INegative(i) => {
                    let meta = cxt
                        .mcxt
                        .unscoped_meta(MetaBounds::int_type(true, i as u64), self.span());
                    Ok(Literal::Int(i as u64, Err((true, meta))))
                }
                NumLiteral::Float(_) => todo!(),
            }
        } else {
            todo!("invalid literal: {:?}", self.syntax());
        }
    }
}
