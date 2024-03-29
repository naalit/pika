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

impl ast::Stmt {
    pub(super) fn elab_dec(&self, cxt: &mut Cxt) -> Option<(SName, Val)> {
        match self {
            ast::Stmt::Def(ast::Def::LetDef(l)) if l.body().is_some() => {
                cxt.error(l.span(), "Only declarations are allowed in this context");
                None
            }
            ast::Stmt::Def(ast::Def::FunDef(f)) if f.body().is_some() => {
                cxt.error(f.span(), "Only declarations are allowed in this context");
                None
            }
            ast::Stmt::Def(ast::Def::LetDef(l)) => match l.pat()?.expr()?.as_let_def_pat(cxt.db) {
                Some((Some((_, name)), Some(ty))) => Some((
                    name,
                    ty.expr()?
                        .check(Val::Type, cxt, CheckReason::UsedAsType)
                        .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                )),
                _ => {
                    cxt.error(l.span(), "Could not determine type of 'let' declaration");
                    None
                }
            },
            ast::Stmt::Expr(e @ ast::Expr::Binder(_)) => match e.as_let_def_pat(cxt.db) {
                Some((Some((_, name)), Some(ty))) => Some((
                    name,
                    ty.expr()?
                        .check(Val::Type, cxt, CheckReason::UsedAsType)
                        .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                )),
                _ => {
                    cxt.error(e.span(), "Could not determine type of field declaration");
                    None
                }
            },
            ast::Stmt::Def(ast::Def::FunDef(x)) => {
                let (_, ty) = infer_fun(
                    x.pars(),
                    x.ret_ty().and_then(|x| x.expr()),
                    None,
                    Some(CopyClass::Copy),
                    x.span(),
                    cxt,
                );
                let ty = ty
                    .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                    .eval(&mut cxt.env());

                Some((x.name()?.name(cxt.db), ty))
            }
            ast::Stmt::Def(ast::Def::TypeDef(_)) => {
                cxt.error(
                    self.span(),
                    "Type definitions are not allowed in this context",
                );
                None
            }
            _ => {
                cxt.error(self.span(), "Expressions are not allowed in this context");
                None
            }
        }
    }

    pub(super) fn elab_field(
        &self,
        cxt: &mut Cxt,
    ) -> Option<(SName, Result<(Expr, Val), ast::Expr>)> {
        match self {
            ast::Stmt::Def(ast::Def::LetDef(l)) => match l.pat()?.expr()?.as_let_def_pat(cxt.db) {
                Some((Some((_, name)), _)) => Some((name, Err(l.body()?.expr()?))),
                _ => None,
            },
            ast::Stmt::Def(ast::Def::FunDef(x)) => {
                let (expr, ty) = infer_fun(
                    x.pars(),
                    x.ret_ty().and_then(|x| x.expr()),
                    x.body(),
                    Some(CopyClass::Copy),
                    x.span(),
                    cxt,
                );
                let ty = ty
                    .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                    .eval(&mut cxt.env());

                Some((x.name()?.name(cxt.db), Ok((expr, ty))))
            }
            ast::Stmt::Def(ast::Def::TypeDef(_)) => {
                cxt.error(
                    self.span(),
                    "Type definitions are not allowed in this context",
                );
                None
            }
            ast::Stmt::Expr(e @ ast::Expr::Var(x)) => Some((x.name(cxt.db), Err(e.clone()))),
            ast::Stmt::Expr(ast::Expr::Binder(x)) => Some((
                x.pat()?.expr()?.as_let_def_pat(cxt.db)?.0?.1,
                Err(x.ty()?.expr()?),
            )),
            _ => None,
        }
    }
}

impl ast::Def {
    pub(super) fn elab_type(
        &self,
        def_id: Def,
        def_node: DefNode,
        cxt: &mut Cxt,
    ) -> Option<DefType> {
        match self {
            ast::Def::LetDef(l) => match l.pat()?.expr()?.as_let_def_pat(cxt.db) {
                Some((n, Some(ty))) => Some(DefType::new(
                    n.map_or(
                        (cxt.db.name("_".into()), l.pat()?.expr()?.span()),
                        |(_, n)| n,
                    ),
                    ty.expr()?
                        .check(Val::Type, cxt, CheckReason::UsedAsType)
                        .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                )),
                Some((Some((_, n)), _)) => {
                    // Infer the type from the value if possible
                    let ty = cxt.db.def_elab_n(def_id, def_node).result?.ty;
                    Some(DefType::new(
                        n,
                        ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                            .eval(&mut cxt.env()),
                    ))
                }
                _ => {
                    // Infer the type from the value if possible
                    let ty = cxt.db.def_elab_n(def_id, def_node).result?.ty;
                    Some(DefType::new(
                        (cxt.db.name("_".into()), l.pat()?.expr()?.span()),
                        ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                            .eval(&mut cxt.env()),
                    ))
                }
            },
            ast::Def::FunDef(x) => {
                // Return () by default
                let rty = x
                    .ret_ty()
                    .and_then(|x| x.expr())
                    .unwrap_or(ast::Expr::GroupedExpr(ast::GroupedExpr::Val {
                        span: x.name().map_or(self.span(), |x| x.span()),
                        expr: None,
                    }));
                let (_, ty) = infer_fun(
                    x.pars(),
                    Some(rty),
                    None,
                    Some(CopyClass::Copy),
                    x.span(),
                    cxt,
                );
                let ty = ty
                    .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                    .eval(&mut cxt.env());

                Some(DefType::new(
                    x.name()
                        .map_or((cxt.db.name("_".into()), x.span()), |x| x.name(cxt.db)),
                    ty,
                ))
            }
            ast::Def::TypeDef(_) | ast::Def::ImplDef(_) => {
                // We usually can't know types of type arguments from just the signature
                // so in general we need to elaborate the constructor types as well
                let def = cxt.db.def_elab_n(def_id, def_node).result?;
                Some(DefType {
                    name: def.name,
                    ty: def
                        .ty
                        .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                    is_trait: def.is_trait,
                    is_impl: def.is_impl,
                    children: def.children.into_iter().map(|x| x.0).collect(),
                    type_def: match def.body {
                        DefBody::Type(b) => Some(TypeDefKind::Type(b)),
                        DefBody::Struct(b) => Some(TypeDefKind::Struct(b)),
                        _ => None,
                    },
                })
            }
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
                            is_trait: false,
                            is_impl: false,
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
                        let ty = cxt.db.def_type_n(def_id, def_node).result?.ty;
                        let body = x.body()?.expr()?.check(
                            ty.clone(),
                            cxt,
                            CheckReason::GivenType(pty.span()),
                        );
                        let body = body.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                        Some(Definition {
                            name,
                            is_trait: false,
                            is_impl: false,
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

                // Return () by default
                let rty = x
                    .ret_ty()
                    .and_then(|x| x.expr())
                    .unwrap_or(ast::Expr::GroupedExpr(ast::GroupedExpr::Val {
                        span: x.name().map_or(self.span(), |x| x.span()),
                        expr: None,
                    }));

                let (term, ty) = infer_fun(
                    x.pars(),
                    Some(rty),
                    x.body(),
                    Some(CopyClass::Copy),
                    x.span(),
                    cxt,
                );

                Some(Definition {
                    name: x.name()?.name(cxt.db),
                    is_trait: false,
                    is_impl: false,
                    ty: Box::new(ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))),
                    body: DefBody::Let(Box::new(term.eval_quote(
                        &mut cxt.env(),
                        cxt.size(),
                        Some(&cxt.mcxt),
                    ))),
                    children: Vec::new(),
                })
            }
            ast::Def::ImplDef(x) => {
                let name = self
                    .name(cxt.db)
                    .unwrap_or((cxt.db.name("_".into()), x.span()));

                cxt.push();
                let pars = check_params(
                    x.pars().imp(),
                    ParamTys::Inferred(Impl),
                    CheckReason::UsedAsType,
                    None,
                    cxt,
                );

                let (body, ty) = x.body()?.expr()?.infer(cxt);
                match &ty {
                    Val::Neutral(n) if matches!(n.head(), Head::Var(Var::Def(_, d)) if cxt.db.def_type(d).and_then(|x| x.result).map_or(false, |x| x.is_trait)) => {
                        ()
                    }
                    _ => cxt.error(
                        x.span(),
                        Doc::start("`impl` used with non-trait '")
                            .chain(ty.clone().quote(cxt.size(), Some(&cxt.mcxt)).pretty(cxt.db))
                            .add("'", ()),
                    ),
                }
                // inline metas in the term
                let body = body.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                let ty = ty.quote(cxt.size(), Some(&cxt.mcxt));
                cxt.pop();

                let body = if pars.is_empty() {
                    body
                } else {
                    Expr::Fun(EClos {
                        class: Lam(Impl, CopyClass::Copy),
                        params: pars.clone(),
                        body: Box::new(body),
                    })
                };
                let ty = if pars.is_empty() {
                    ty
                } else {
                    Expr::Fun(EClos {
                        class: Pi(Impl, CopyClass::Copy),
                        params: pars,
                        body: Box::new(ty),
                    })
                };

                Some(Definition {
                    name,
                    is_trait: false,
                    is_impl: true,
                    ty: Box::new(ty),
                    body: DefBody::Let(Box::new(Expr::Spanned(
                        x.body().unwrap().span(),
                        Box::new(body),
                    ))),
                    children: Vec::new(),
                })
            }
            ast::Def::TypeDef(x) => {
                let is_trait = x
                    .syntax()
                    .unwrap()
                    .children_with_tokens()
                    .any(|x| x.kind() == crate::parsing::SyntaxKind::TraitKw);
                let span = x.name().map_or(x.span(), |x| x.span());

                cxt.push();
                let has_self = x
                    .pars()
                    .imp()
                    .and_then(|x| x.pars.first().cloned())
                    .and_then(|x| x.ok())
                    .and_then(|x| x.as_let_def_pat(cxt.db))
                    .and_then(|x| x.0)
                    .map_or(false, |(_, (n, _))| n == cxt.db.name("Self".into()));
                let (_, ty) = infer_fun(
                    TraitPars(
                        if is_trait && !has_self {
                            Some(Par::new((cxt.db.name("Self".into()), span), Expr::Type))
                        } else {
                            None
                        },
                        x.pars().imp(),
                    ),
                    Some(ast::Expr::Type(ast::Type::Val {
                        span: x.name().map_or_else(|| x.span(), |n| n.span()),
                        kw: None,
                    })),
                    None,
                    Some(CopyClass::Copy),
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
                    Expr::Fun(clos) if matches!(clos.class, Pi(_, _)) => {
                        let arg = clos
                            .clone()
                            .eval(&mut cxt.env())
                            .synthesize_args(cxt.size());
                        match &*clos.body {
                            Expr::Fun(clos2) if matches!(clos2.class, Pi(_, _)) => {
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

                let body = match x.body() {
                    Some(_) if x.pars().and_then(|x| x.exp()).is_some() => {
                        cxt.error(
                            x.pars().unwrap().exp().unwrap().span(),
                            "Type definitions can only have implicit parameters",
                        );
                        DefBody::Let(Box::new(Expr::Error))
                    }
                    // Tuple struct
                    None => {
                        // We manufacture a constructor with SplitId::Idx(0)
                        let cty = {
                            cxt.push();

                            let implicit = ty_params.clone();
                            for par in &implicit {
                                cxt.define_local(
                                    par.name,
                                    par.ty.clone().eval(&mut cxt.env()),
                                    None,
                                    None,
                                    false,
                                );
                            }
                            let explicit = check_params(
                                x.pars().exp(),
                                ParamTys::Inferred(Expl),
                                CheckReason::UsedAsType,
                                None,
                                cxt,
                            );

                            let mut ty = default_rty.clone().quote(cxt.size(), Some(&cxt.mcxt));
                            if !explicit.is_empty() {
                                ty = Expr::Fun(EClos {
                                    class: Pi(Expl, CopyClass::Copy),
                                    params: explicit,
                                    body: Box::new(ty),
                                });
                            }
                            if !implicit.is_empty() {
                                ty = Expr::Fun(EClos {
                                    class: Pi(Impl, CopyClass::Copy),
                                    params: implicit,
                                    body: Box::new(ty),
                                });
                            }

                            cxt.pop();

                            ty
                        };
                        let split = SplitId::Idx(0);
                        DefBody::Type(vec![(
                            split,
                            x.span(),
                            cty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                                .eval(&mut cxt.env()),
                        )])
                    }
                    // (G)ADT
                    Some(ast::TypeDefBody::TypeDefCtors(cons)) => {
                        let mut ctors = Vec::new();
                        let mut n_unnamed = 0;
                        for c in cons.cons() {
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
                                    c.pars(),
                                    c.ret_ty().and_then(|x| x.expr()),
                                    None,
                                    Some(CopyClass::Copy),
                                    c.span(),
                                    cxt,
                                );
                                fn head(t: &Expr) -> &Expr {
                                    match t {
                                        Expr::Elim(a, e) if matches!(&**e, Elim::App(_, _)) => {
                                            head(a)
                                        }
                                        t => t,
                                    }
                                }
                                let rty = match &cty {
                                    Expr::Fun(clos) if matches!(clos.class, Pi(_, _)) => {
                                        match &*clos.body {
                                            Expr::Fun(clos2)
                                                if matches!(clos.class, Pi(Impl, _))
                                                    && matches!(clos2.class, Pi(Expl, _)) =>
                                            {
                                                &clos2.body
                                            }
                                            rty => rty,
                                        }
                                    }
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
                                    c.pars().imp(),
                                    ParamTys::Inferred(Impl),
                                    CheckReason::UsedAsType,
                                    None,
                                    cxt,
                                ));
                                let explicit = check_params(
                                    c.pars().exp(),
                                    ParamTys::Inferred(Expl),
                                    CheckReason::UsedAsType,
                                    None,
                                    cxt,
                                );

                                let mut ty = default_rty.clone().quote(cxt.size(), Some(&cxt.mcxt));
                                if !explicit.is_empty() {
                                    ty = Expr::Fun(EClos {
                                        class: Pi(Expl, CopyClass::Copy),
                                        params: explicit,
                                        body: Box::new(ty),
                                    });
                                }
                                if !implicit.is_empty() {
                                    ty = Expr::Fun(EClos {
                                        class: Pi(Impl, CopyClass::Copy),
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
                        DefBody::Type(
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
                        )
                    }
                    // Struct
                    Some(ast::TypeDefBody::TypeDefStruct(s)) => {
                        let mut fields = Vec::new();
                        if is_trait {
                            cxt.push_trait_scope();
                        } else {
                            cxt.push();
                        }
                        for i in ty_params {
                            cxt.define_local(i.name, i.ty.eval(&mut cxt.env()), None, None, false);
                        }
                        cxt.push();
                        for i in s.fields().into_iter().flat_map(|x| x.fields()) {
                            if let Some((name, ty)) = i.elab_dec(cxt) {
                                cxt.define_local(name, ty.clone(), None, None, false);
                                fields.push((name, ty));
                            }
                        }
                        cxt.pop();
                        // Make sure to inline any relevant metas
                        let mut size = cxt.size();
                        let body = DefBody::Struct(
                            fields
                                .into_iter()
                                .map(|(name, ty)| {
                                    let r = (name, ty.quote(size, Some(&cxt.mcxt)));
                                    size += 1;
                                    r
                                })
                                .collect(),
                        );
                        cxt.pop();
                        body
                    }
                };

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
                    is_trait,
                    is_impl: false,
                    // Inline metas in all types involved after elaborating the constructors
                    // since metas caused by inferred types of type arguments can be solved in ctors
                    ty: Box::new(ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))),
                    body,
                    children,
                })
            }
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
            ast::Def::ImplDef(x) => x.name().map(|x| x.name(db)),
        }
    }
}

fn infer_fun(
    pars: impl HasPars,
    ret_ty: Option<ast::Expr>,
    body: Option<ast::Body>,
    copy_class: Option<CopyClass>,
    span: RelSpan,
    cxt: &mut Cxt,
) -> (Expr, Expr) {
    // [a, b] [c, d] (e, f) => ...
    // -->
    // [a, b, c, d] => ((e, f) => ...)

    cxt.push();
    let mut extra_pars: Vec<_> = pars.extra_imp().into_iter().cloned().collect();
    for i in &extra_pars {
        cxt.define_local(
            i.name,
            i.ty.clone().eval(&mut cxt.env()),
            None,
            None,
            i.mutable,
        );
    }
    let mut implicit = check_params(
        pars.imp(),
        ParamTys::Inferred(Impl),
        CheckReason::UsedAsType,
        None,
        cxt,
    );
    let explicit = check_params(
        pars.exp(),
        ParamTys::Inferred(Expl),
        CheckReason::UsedAsType,
        Some(&mut extra_pars),
        cxt,
    );
    extra_pars.append(&mut implicit);
    let implicit = extra_pars;

    // Variable accesses in the parameter types don't count as captures,
    // but accesses to the parameters inside the body don't count either
    // That's why we do this instead of pushing a capture scope (bc then that wouldn't include parameters)
    cxt.mark_top_scope_capture();
    // But we do want to consider the return type separate from the body, and the return type can't move/mutate parameters
    cxt.push();
    cxt.mark_top_scope_capture();

    cxt.record_deps();
    let mut had_capture_err = false;
    let bspan = body.as_ref().map_or(span, |x| x.span());
    let (body, bty) = match ret_ty {
        Some(bty) => {
            let span = bty.span();
            let bty = bty.check(Val::Type, cxt, CheckReason::UsedAsType);

            let captures = cxt.pop();
            let (captures_class, max_a) =
                captures.as_ref().map_or((CopyClass::Copy, None), |(_, x)| {
                    x.iter()
                        .fold((CopyClass::Copy, None), |(x, xa), (_, (y, a))| {
                            if *y > x {
                                (*y, Some(*a))
                            } else {
                                (x, xa)
                            }
                        })
                });
            if captures_class > CopyClass::Copy {
                let access = max_a.unwrap();
                cxt.error(bspan, MoveError::FunAccess(access, None, None));
                had_capture_err = true;
            }

            let bty = bty.eval(&mut cxt.env());
            let body = body
                .and_then(|x| x.expr())
                .map(|x| x.check(bty.clone(), cxt, CheckReason::GivenType(span)))
                .unwrap_or_else(|| {
                    // cxt.error(span, "Missing function body");
                    Expr::Error
                });
            (body, bty)
        }
        None => {
            cxt.pop();
            body.and_then(|x| x.expr())
                .map(|x| x.infer(cxt))
                .unwrap_or_else(|| {
                    // cxt.error(span, "Missing function body");
                    (Expr::Error, Val::Error)
                })
        }
    };
    let bty = bty.quote(cxt.size(), None);
    let captures = cxt.pop();
    let (captures_class, max_a) = captures.as_ref().map_or((CopyClass::Copy, None), |(_, x)| {
        x.iter()
            .fold((CopyClass::Copy, None), |(x, xa), (_, (y, a))| {
                if *y > x {
                    (*y, Some(*a))
                } else {
                    (x, xa)
                }
            })
    });
    if let Some(copy_class) = copy_class {
        if copy_class < captures_class && !had_capture_err {
            let access = max_a.unwrap();
            cxt.error(bspan, MoveError::FunAccess(access, Some(copy_class), None));
        }
    }
    let copy_class = copy_class.unwrap_or(captures_class);
    if let &Some((borrow, _)) = &captures {
        cxt.finish_closure_env(borrow, copy_class, span);
    }
    // This is the borrow of the returned expression, so we'll use this if we do dependency annotations
    cxt.finish_deps(bspan);

    // We have to evaluate this outside of the scope
    // TODO figure out how copy classes work with pi (can a pi type depend by-move on an argument? a capture?)
    let mut ty = if explicit.is_empty() {
        bty
    } else {
        Expr::Fun(EClos {
            class: Pi(Expl, copy_class),
            params: explicit.clone(),
            body: Box::new(bty),
        })
    };
    if !implicit.is_empty() {
        ty = Expr::Fun(EClos {
            class: Pi(Impl, copy_class),
            params: implicit.clone(),
            body: Box::new(ty),
        });
    }
    let mut term = if explicit.is_empty() {
        body
    } else {
        Expr::Fun(EClos {
            class: Lam(Expl, copy_class),
            params: explicit,
            body: Box::new(body),
        })
    };
    if !implicit.is_empty() {
        term = Expr::Fun(EClos {
            class: Lam(Impl, copy_class),
            params: implicit,
            body: Box::new(term),
        });
    }

    (term, ty)
}

#[derive(Clone, Debug)]
struct Pars {
    pars: Vec<Result<ast::Expr, RelSpan>>,
    pat: bool,
}

trait HasPars {
    fn exp(&self) -> Option<Pars>;
    fn imp(&self) -> Option<Pars>;
    fn extra_imp(&self) -> Option<&Par> {
        None
    }
}
impl<T: HasPars> HasPars for Option<T> {
    fn exp(&self) -> Option<Pars> {
        self.as_ref()?.exp()
    }

    fn imp(&self) -> Option<Pars> {
        self.as_ref()?.imp()
    }

    fn extra_imp(&self) -> Option<&Par> {
        self.as_ref()?.extra_imp()
    }
}
struct SigmaPars(Option<ast::Expr>);
impl HasPars for SigmaPars {
    fn exp(&self) -> Option<Pars> {
        Some(Pars {
            pars: vec![Ok(self.0.clone()?)],
            pat: false,
        })
    }

    fn imp(&self) -> Option<Pars> {
        None
    }
}
struct TraitPars(Option<Par>, Option<Pars>);
impl HasPars for TraitPars {
    fn exp(&self) -> Option<Pars> {
        None
    }

    fn imp(&self) -> Option<Pars> {
        self.1.clone()
    }

    fn extra_imp(&self) -> Option<&Par> {
        self.0.as_ref()
    }
}
impl HasPars for ast::FunPars {
    fn exp(&self) -> Option<Pars> {
        self.exp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: true })
    }

    fn imp(&self) -> Option<Pars> {
        self.imp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: true })
    }
}
impl HasPars for ast::TypePars {
    fn exp(&self) -> Option<Pars> {
        self.exp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: false })
    }

    fn imp(&self) -> Option<Pars> {
        self.imp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: true })
    }
}
impl HasPars for ast::PiPars {
    fn exp(&self) -> Option<Pars> {
        self.exp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: false })
    }

    fn imp(&self) -> Option<Pars> {
        self.imp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: false })
    }
}
impl HasPars for ast::ImplPars {
    fn exp(&self) -> Option<Pars> {
        None
    }

    fn imp(&self) -> Option<Pars> {
        self.imp()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .map(|pars| Pars { pars, pat: true })
    }
}

fn check_params(
    pars: Option<Pars>,
    tys: ParamTys,
    reason: CheckReason,
    mut extra_pars: Option<&mut Vec<Par>>,
    cxt: &mut Cxt,
) -> Vec<Par> {
    let Pars { pars, pat } = pars.unwrap_or(Pars {
        pars: Vec::new(),
        pat: false,
    });
    let err_missing = tys.err_missing();
    let mut first = true;
    let allow_impl = tys.allow_impl();
    tys.zip_with(pars.into_iter())
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
            check_par(
                x,
                pat,
                ty.map(|x| (x, reason)),
                if first {
                    first = false;
                    // Rust should make this easier
                    extra_pars.as_mut().map(|x| &mut **x)
                } else {
                    None
                },
                allow_impl,
                cxt,
            )
        })
        .collect()
}

impl ast::Expr {
    fn is_self_pat(&self, incl_ref: bool, cxt: &Cxt) -> bool {
        match self {
            ast::Expr::Reference(x) if incl_ref => {
                x.expr().map_or(false, |x| x.is_self_pat(false, cxt))
            }
            ast::Expr::RefMut(x) if incl_ref => {
                x.expr().map_or(false, |x| x.is_self_pat(false, cxt))
            }
            ast::Expr::MutVar(x) if incl_ref => x
                .var()
                .map_or(false, |x| x.name(cxt.db).0 == cxt.db.name("self".into())),
            ast::Expr::Var(x) => x.name(cxt.db).0 == cxt.db.name("self".into()),
            _ => false,
        }
    }

    fn as_self_pat(&self, ty: Expr) -> (bool, Expr) {
        match self {
            ast::Expr::Reference(_) => (false, Expr::RefType(false, Box::new(ty))),
            ast::Expr::RefMut(_) => (true, Expr::RefType(true, Box::new(ty))),
            ast::Expr::Var(_) => (false, ty),
            ast::Expr::MutVar(_) => (true, ty),
            _ => unreachable!(),
        }
    }
}

fn check_par(
    x: Result<ast::Expr, RelSpan>,
    pat: bool,
    expected_ty: Option<(Expr, CheckReason)>,
    extra_pars: Option<&mut Vec<Par>>,
    allow_impl: bool,
    cxt: &mut Cxt,
) -> Par {
    let par = match x {
        Ok(x) if x.is_self_pat(true, cxt) => {
            let (m, ty) = match cxt.resolve_self(x.span()) {
                Some(rty) if extra_pars.is_some() => {
                    let ty = rty.ty(cxt);
                    let (mut ty_params, rty) = match ty {
                        Val::Fun(clos) if matches!(clos.class, Pi(_, _)) => {
                            let before_size = cxt.size();
                            for i in &clos.params {
                                cxt.define_local(
                                    i.name,
                                    i.ty.clone().eval(&mut cxt.env()),
                                    None,
                                    None,
                                    false,
                                );
                            }
                            let arg = clos
                                .clone()
                                .synthesize_args(before_size)
                                .quote(cxt.size(), None);
                            (
                                clos.params.clone(),
                                Expr::Elim(
                                    Box::new(rty),
                                    Box::new(Elim::App(clos.class.icit().unwrap(), arg)),
                                ),
                            )
                        }
                        _ => (Vec::new(), rty),
                    };
                    extra_pars.unwrap().append(&mut ty_params);
                    x.as_self_pat(rty)
                }
                _ => {
                    cxt.error(x.span(), "`self` cannot be used in this context");
                    (false, Expr::Error)
                }
            };
            Par {
                name: (cxt.db.name("self".into()), x.span()),
                mutable: m,
                ty,
                is_impl: false,
            }
        }
        Ok(ast::Expr::ImplPat(x)) => {
            if !allow_impl {
                cxt.error(x.span(), "`impl` is only allowed in implicit arguments");
            }
            let ty = x
                .expr()
                .map(|x| x.check(Val::Type, cxt, CheckReason::UsedAsType))
                .unwrap_or(Expr::Error);

            match ty.clone().eval(&mut cxt.env()) {
                Val::Neutral(n) if matches!(n.head(), Head::Var(Var::Def(_, d)) if cxt.db.def_type(d).and_then(|x| x.result).map_or(false, |x| x.is_trait)) => {
                    ()
                }
                ty => cxt.error(
                    x.span(),
                    Doc::start("`impl` used with non-trait '")
                        .chain(ty.clone().quote(cxt.size(), Some(&cxt.mcxt)).pretty(cxt.db))
                        .add("'", ()),
                ),
            }

            Par {
                name: (cxt.db.name("_".to_string()), x.span()),
                ty,
                mutable: false,
                is_impl: true,
            }
        }
        Ok(ast::Expr::Binder(x)) => {
            let (name, ty) = x
                .pat()
                .and_then(|x| x.expr())
                .map(|x| {
                    x.as_simple_pat(cxt.db)
                        .unwrap_or_else(|| todo!("move non-trivial pats to rhs"))
                })
                .unwrap_or((None, None));
            let (mutable, name) =
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
                .map(|x| x.check(Val::Type, cxt, CheckReason::UsedAsType))
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
            Par {
                name,
                ty,
                mutable,
                is_impl: false,
            }
        }
        Ok(x) if pat => {
            let (name, ty) = x.as_simple_pat(cxt.db).unwrap_or_else(|| {
                todo!(
                    "move non-trivial pats to rhs ({})",
                    ast::Pretty::pretty(&x).to_string(false)
                )
            });
            let (mutable, name) =
                name.unwrap_or_else(|| (false, (cxt.db.name("_".to_string()), x.span())));
            let ty = match ty.map(|x| x.check(Val::Type, cxt, CheckReason::UsedAsType)) {
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
                    cxt.new_meta(
                        MetaBounds::new(Val::Type),
                        x.span(),
                        MetaSource::TypeOf(name.0),
                    )
                }),
            };
            Par {
                name,
                ty,
                mutable,
                is_impl: false,
            }
        }
        Ok(x) => {
            let ty = x.check(Val::Type, cxt, CheckReason::UsedAsType);

            Par::new((cxt.db.name("_".to_string()), x.span()), ty)
        }
        Err(span) => {
            if let Some((ty, reason)) = expected_ty {
                let ty = ty.eval(&mut cxt.env());
                cxt.unify(Val::var(Var::Builtin(Builtin::UnitType)), ty, reason)
                    .unwrap_or_else(|e| cxt.error(span, e));
            }
            Par::new(
                (cxt.db.name("_".to_string()), span),
                Expr::var(Var::Builtin(Builtin::UnitType)),
            )
        }
    };
    // Define each parameter so it can be used by the types of the rest
    cxt.define_local(
        par.name,
        par.ty.clone().eval(&mut cxt.env()),
        None,
        None,
        par.mutable,
    );
    par
}

impl ast::Pair {
    fn elab_sigma(&self, cxt: &mut Cxt) -> Result<Expr, TypeError> {
        {
            let (_, ty) = infer_fun(
                SigmaPars(self.lhs()),
                self.rhs(),
                None,
                None, // TODO copy classes for sigma
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
    Inferred(Icit),
}
impl ParamTys<'_, '_> {
    fn err_missing(&self) -> bool {
        !matches!(self, ParamTys::Inferred(_))
    }

    fn allow_impl(&self) -> bool {
        matches!(self, ParamTys::Impl(_) | ParamTys::Inferred(Impl))
    }

    fn zip_with<T>(self, it: impl ExactSizeIterator<Item = T>) -> Vec<(Option<Expr>, Vec<T>)> {
        match self {
            ParamTys::Inferred(_) => it.map(|x| (None, vec![x])).collect(),
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
    pub(super) fn insert_metas(
        self,
        ty: Val,
        imp_args: Option<ast::ImpArgs>,
        span: RelSpan,
        cxt: &mut Cxt,
    ) -> (Expr, Val) {
        match ty {
            Val::Fun(clos) if matches!(clos.class, Pi(Impl, _)) => {
                let mut args: VecDeque<_> = imp_args
                    .into_iter()
                    .flat_map(|x| x.args())
                    .flat_map(|x| x.expr().map(|x| x.as_args()).unwrap_or(vec![Err(x.span())]))
                    .collect();
                let mut targs: Vec<Expr> = Vec::new();
                let par_ty = clos.par_ty();
                let rty = clos.elab_with(|name, aty, is_impl| match args.pop_front() {
                    Some(arg) => match arg {
                        Ok(arg) => {
                            let arg = arg.check(aty, cxt, CheckReason::ArgOf(span));
                            targs.push(arg.clone());
                            arg.eval(&mut cxt.env())
                        }
                        Err(span) => {
                            if let Err(e) = cxt.unify(
                                Val::var(Var::Builtin(Builtin::UnitType)),
                                aty,
                                CheckReason::ArgOf(span),
                            ) {
                                cxt.error(span, e);
                                targs.push(Expr::Error);
                                Val::Error
                            } else {
                                targs.push(Expr::var(Var::Builtin(Builtin::Unit)));
                                Val::var(Var::Builtin(Builtin::Unit))
                            }
                        }
                    },
                    None => {
                        // Apply a new metavariable
                        let e = cxt.new_meta(
                            MetaBounds::new(aty).with_impl(is_impl),
                            span,
                            MetaSource::ArgOf(self.pretty(cxt.db), Some(name.0)),
                        );
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
            _ if imp_args.is_some() => {
                cxt.error(
                    span,
                    Doc::start("Value of type '")
                        .chain(ty.clone().quote(cxt.size(), Some(&cxt.mcxt)).pretty(cxt.db))
                        .add("' does not take implicit parameters", ()),
                );
                (self, ty)
            }
            _ => (self, ty),
        }
    }
}

pub(super) fn member_type(lhs: &Val, def: Def, idx: u64, cxt: &mut Cxt) -> Val {
    if let Some(TypeDefKind::Struct(fields)) = cxt
        .db
        .def_type(def)
        .and_then(|x| x.result)
        .and_then(|x| x.type_def)
    {
        let mut env = cxt.env();
        let lhs_ty = lhs.clone().quote(cxt.size(), Some(&cxt.mcxt)).ty(cxt);
        match cxt.db.def_type(def).and_then(|x| x.result).unwrap().ty {
            Val::Fun(clos) if matches!(clos.class, Pi(Impl, _)) => match lhs_ty {
                Val::Neutral(n) => {
                    assert!(matches!(n.head(), Head::Var(Var::Def(_, d)) if d == def));
                    for i in n.spine() {
                        match i {
                            Elim::App(Impl, x) => {
                                for (val, _) in x
                                    .clone()
                                    .zip_pair(&clos.params)
                                    .expect("TODO switch to using case or something")
                                {
                                    env.push(Some(Ok(val)));
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                Val::Error => return Val::Error,
                _ => unreachable!(),
            },
            _ => (),
        }
        for (i, (fname, fty)) in fields.iter().enumerate() {
            if i as u64 == idx {
                return fty.clone().eval(&mut env);
            }
            let val = lhs
                .clone()
                .app(Elim::Member(def, i as u64, *fname), &mut env);
            env.push(Some(Ok(val)));
        }
        Val::Error
    } else {
        Val::Error
    }
}

pub(super) fn resolve_member(lhs: PlaceOrExpr, member: ast::Member, cxt: &mut Cxt) -> PlaceOrExpr {
    match resolve_member_method(lhs, member, cxt) {
        Ok(x) => x,
        Err((l, _)) => {
            cxt.error(l.span(), "Method call not allowed here");
            PlaceOrExpr::Expr(Expr::Error, Val::Error, None, l.span())
        }
    }
}

// For a method, returns Err(self, method)
pub(super) fn resolve_member_method(
    lhs: PlaceOrExpr,
    member: ast::Member,
    cxt: &mut Cxt,
) -> Result<PlaceOrExpr, (PlaceOrExpr, Expr)> {
    let span = RelSpan::new(lhs.span().start, member.span().end);
    let mut lhs_ty = lhs.ty(cxt);
    let mut error = None;

    if let Some(name) = member.var().map(|x| x.name(cxt.db)) {
        lhs_ty.inline_head(&mut cxt.env(), &cxt.mcxt);
        match &lhs_ty {
            Val::Error => (),
            Val::RefType(_, _) => {
                return resolve_member_method(
                    PlaceOrExpr::Place(Place::Deref(Box::new(lhs))),
                    member,
                    cxt,
                )
            }
            Val::Neutral(n) => match n.head() {
                Head::Var(Var::Def(_, def)) => {
                    let edef = cxt.db.def_type(def);
                    // Struct fields
                    match edef
                        .as_ref()
                        .and_then(|x| x.result.as_ref())
                        .and_then(|x| x.type_def.as_ref())
                    {
                        Some(TypeDefKind::Struct(fields)) => {
                            if let Some((idx, (_, _))) = fields
                                .iter()
                                .enumerate()
                                .find(|(_, ((n, _), _))| *n == name.0)
                            {
                                return Ok(PlaceOrExpr::Place(Place::Member(
                                    Box::new(lhs),
                                    def,
                                    idx as u64,
                                    name,
                                )));
                            }
                        }
                        _ => (),
                    }
                    // Methods in `where` block
                    if let Some(split) = edef
                        .as_ref()
                        .and_then(|x| x.result.as_ref())
                        .and_then(|x| x.children.iter().find(|s| **s == SplitId::Named(name.0)))
                    {
                        let def = cxt.db.def(DefLoc::Child(def, *split));
                        // TODO check if it actually has a `self` parameter
                        return Err((lhs, Expr::var(Var::Def(name, def))));
                    }
                }
                _ => (),
            },
            _ => {
                let lhs = lhs
                    .clone()
                    .finish(AccessKind::as_move(lhs_ty.copy_class(cxt)), cxt);
                let mut lhs_val = lhs.clone().eval(&mut cxt.env());
                lhs_val.inline_head(&mut cxt.env(), &cxt.mcxt);
                match &lhs_val {
                    Val::Neutral(n) => match n.head() {
                        Head::Var(Var::Def(def_name, def)) => {
                            let edef = cxt.db.def_type(def);
                            match edef.as_ref().and_then(|x| x.result.as_ref()) {
                                Some(edef) => {
                                    match &edef.type_def {
                                        Some(TypeDefKind::Type(ctors)) => {
                                            if let Some((split, _, ty)) = ctors
                                                .iter()
                                                .find(|(s, _, _)| *s == SplitId::Named(name.0))
                                            {
                                                return Ok(PlaceOrExpr::Expr(
                                                    Expr::var(Var::Cons(
                                                        name,
                                                        cxt.db.cons_id(def, *split),
                                                    )),
                                                    ty.clone(),
                                                    None,
                                                    span,
                                                ));
                                            }
                                        }
                                        Some(TypeDefKind::Struct(fields)) if edef.is_trait => {
                                            if let Some((idx, (_, _))) = fields
                                                .iter()
                                                .enumerate()
                                                .find(|(_, ((n, _), _))| *n == name.0)
                                            {
                                                let (lhs, _) =
                                                    lhs.insert_metas(lhs_ty, None, span, cxt);
                                                let lhs_val = lhs.eval(&mut cxt.env());
                                                let meta = cxt.new_meta(
                                                    MetaBounds::new(lhs_val.clone())
                                                        .with_impl(true),
                                                    span,
                                                    MetaSource::ArgOf(
                                                        edef.name
                                                            .pretty(cxt.db)
                                                            .add('.', ())
                                                            .chain(name.pretty(cxt.db)),
                                                        None,
                                                    ),
                                                );
                                                return Ok(PlaceOrExpr::Place(Place::Member(
                                                    Box::new(PlaceOrExpr::Expr(
                                                        meta, lhs_val, None, span,
                                                    )),
                                                    def,
                                                    idx as u64,
                                                    name,
                                                )));
                                            }
                                        }
                                        _ => (),
                                    }
                                    if let Some(split) =
                                        edef.children.iter().find(|s| **s == SplitId::Named(name.0))
                                    {
                                        let def = cxt.db.def(DefLoc::Child(def, *split));
                                        let ty = cxt
                                            .db
                                            .def_type(def)
                                            .and_then(|x| x.result)
                                            .map_or(Val::Error, |x| x.ty);
                                        return Ok(PlaceOrExpr::Expr(
                                            Expr::var(Var::Def(name, def)),
                                            ty,
                                            None,
                                            span,
                                        ));
                                    } else {
                                        error = Some(
                                            Doc::start("Type ")
                                                .add(cxt.db.lookup_name(def_name.0), Doc::COLOR2)
                                                .add(" has no member ", ())
                                                .add(cxt.db.lookup_name(name.0), Doc::COLOR1),
                                        );
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

        // Look for trait methods in scope
        let mut trait_results = Vec::new();
        for trait_def in cxt.all_traits() {
            let edef = cxt.db.def_type(trait_def).unwrap().result.unwrap();

            match &edef.type_def {
                Some(TypeDefKind::Struct(fields)) => {
                    if let Some((idx, (_, _))) = fields
                        .iter()
                        .enumerate()
                        .find(|(_, ((n, _), _))| *n == name.0)
                    {
                        trait_results.push((edef.name, (trait_def, idx)));
                    }
                }
                _ => (),
            }
        }
        match trait_results.len() {
            0 => (),
            1 => {
                let (tname, (def, idx)) = trait_results.pop().unwrap();
                let tr = Expr::var(Var::Def(tname, def));
                let tr_ty = tr.ty(cxt);
                let (tr, _) = tr.insert_metas(tr_ty, None, span, cxt);
                let tr = tr.eval(&mut cxt.env());
                let meta = cxt.new_meta(
                    MetaBounds::new(tr.clone()).with_impl(true),
                    span,
                    MetaSource::ArgOf(
                        tname.pretty(cxt.db).add('.', ()).chain(name.pretty(cxt.db)),
                        None,
                    ),
                );
                let method = Expr::Elim(
                    Box::new(meta),
                    Box::new(Elim::Member(def, idx as u64, name)),
                );
                return Err((lhs, method));
            }
            _ => {
                error = Some(
                    Doc::start("Ambiguous trait method call '")
                        .chain(name.pretty(cxt.db))
                        .add("()': candidate traits include '", ())
                        .chain(trait_results[0].0.pretty(cxt.db))
                        .add("' and '", ())
                        .chain(trait_results[1].0.pretty(cxt.db))
                        .add("'", ()),
                );
            }
        }
    }

    cxt.error(
        member.span(),
        error.unwrap_or_else(|| {
            Doc::start("Value of type '")
                .chain(
                    lhs_ty
                        .clone()
                        .quote(cxt.size(), Some(&cxt.mcxt))
                        .pretty(cxt.db),
                )
                .add("' does not have members", ())
        }),
    );
    Ok(PlaceOrExpr::Expr(Expr::Error, Val::Error, None, span))
}

#[derive(Debug, Clone)]
pub enum PlaceOrExpr {
    Place(Place),
    Expr(Expr, Val, Option<Borrow>, RelSpan),
}
impl PlaceOrExpr {
    pub fn finish(self, kind: AccessKind, cxt: &mut Cxt) -> Expr {
        self.finish_and_borrow(kind, kind, cxt)
    }

    pub fn finish_and_borrow(
        self,
        access_kind: AccessKind,
        borrow_kind: AccessKind,
        cxt: &mut Cxt,
    ) -> Expr {
        match self {
            PlaceOrExpr::Place(place) => {
                place
                    .try_access_unborrowed(access_kind, cxt)
                    .unwrap_or_else(|e| cxt.error(place.span(), e));
                place.borrow(borrow_kind, cxt);
                place.to_expr(cxt)
            }
            PlaceOrExpr::Expr(e, _, b, span) => {
                if let Some(b) = b {
                    cxt.add_dep(
                        b,
                        Access {
                            kind: borrow_kind,
                            point: AccessPoint::Expr,
                            span,
                        },
                    );
                }
                e
            }
        }
    }

    fn to_expr(self, cxt: &Cxt) -> Expr {
        match self {
            PlaceOrExpr::Place(place) => place.to_expr(cxt),
            PlaceOrExpr::Expr(e, _, _, _) => e,
        }
    }

    pub fn ty(&self, cxt: &mut Cxt) -> Val {
        match self {
            PlaceOrExpr::Place(place) => place.ty(cxt).unwrap_or_else(|e| {
                cxt.error(place.span(), e);
                Val::Error
            }),
            PlaceOrExpr::Expr(_, ty, _, _) => ty.clone(),
        }
    }

    fn span(&self) -> RelSpan {
        match self {
            PlaceOrExpr::Place(place) => place.span(),
            PlaceOrExpr::Expr(_, _, _, s) => *s,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Place {
    Var(VarEntry),
    Deref(Box<PlaceOrExpr>),
    Member(Box<PlaceOrExpr>, Def, u64, SName),
}
impl Place {
    fn span(&self) -> RelSpan {
        match self {
            Place::Var(entry) => entry.access(AccessKind::Copy).span,
            Place::Deref(b) => b.span(),
            Place::Member(b, _, _, n) => RelSpan::new(b.span().start, n.1.end),
        }
    }

    fn ty(&self, cxt: &mut Cxt) -> Result<Val, TypeError> {
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
            Place::Member(e, def, idx, _) => {
                let lhs = e.clone().to_expr(cxt).eval(&mut cxt.env());
                Ok(member_type(&lhs, *def, *idx, cxt))
            }
        }
    }

    fn to_expr(self, cxt: &Cxt) -> Expr {
        match self {
            Place::Var(v) => Expr::var(v.var(cxt).cvt(cxt.size())),
            Place::Deref(e) => Expr::Elim(Box::new(e.to_expr(cxt)), Box::new(Elim::Deref)),
            Place::Member(e, def, idx, name) => Expr::Elim(
                Box::new(e.to_expr(cxt)),
                Box::new(Elim::Member(def, idx, name)),
            ),
        }
    }

    /// Makes sure the access is valid, invalidating other borrows appropriately, but does not add needed dependencies to the cxt
    fn try_access_unborrowed(&self, kind: AccessKind, cxt: &mut Cxt) -> Result<(), TypeError> {
        match self {
            Place::Var(v) => match kind {
                AccessKind::Mut | AccessKind::Imm => {
                    let mutable = kind == AccessKind::Mut;
                    v.try_borrow(mutable, mutable, cxt).map_err(Into::into)
                }
                AccessKind::Move => v
                    .try_move(self.ty(cxt)?.quote(cxt.size(), Some(&cxt.mcxt)), cxt)
                    .map_err(Into::into),
                AccessKind::Copy => Ok(()),
            },
            // Just forward on the access
            Place::Member(e, _, _, _) => match &**e {
                PlaceOrExpr::Place(p) => p.try_access_unborrowed(kind, cxt),
                _ => Ok(()),
            },
            Place::Deref(_) if kind == AccessKind::Move => {
                let ty = self.ty(cxt)?.quote(cxt.size(), Some(&cxt.mcxt));
                Err(MoveError::InvalidMove(
                    Doc::start("Cannot move out of reference"),
                    None,
                    Box::new(ty),
                )
                .into())
            }
            Place::Deref(e) => {
                let ty = match &**e {
                    PlaceOrExpr::Place(p) => {
                        p.try_access_unborrowed(kind, cxt)?;
                        Cow::Owned(p.ty(cxt)?)
                    }
                    PlaceOrExpr::Expr(_, t, _, _) => Cow::Borrowed(t),
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

    /// Adds needed dependencies to the cxt
    fn borrow(&self, kind: AccessKind, cxt: &mut Cxt) {
        match self {
            Place::Var(v) => {
                if let Some(borrow) = v.borrow(cxt) {
                    cxt.add_dep(borrow, v.access(kind));
                }
            }
            // Just forward on the access
            Place::Member(e, _, _, _) => match &**e {
                PlaceOrExpr::Place(p) => {
                    p.borrow(kind, cxt);
                }
                PlaceOrExpr::Expr(_, _, b, s) => {
                    if let Some(b) = b {
                        cxt.add_dep(
                            *b,
                            Access {
                                kind,
                                point: AccessPoint::Expr,
                                span: *s,
                            },
                        );
                    }
                }
            },
            Place::Deref(e) => match &**e {
                PlaceOrExpr::Place(p) => {
                    p.borrow(kind, cxt);
                }
                PlaceOrExpr::Expr(_, _, b, s) => {
                    if let Some(b) = b {
                        cxt.add_dep(
                            *b,
                            Access {
                                kind,
                                point: AccessPoint::Expr,
                                span: *s,
                            },
                        );
                    }
                }
            },
        }
    }

    /// Makes sure the access is valid, invalidating other borrows appropriately, and adds needed dependencies to the cxt
    fn try_access(&self, kind: AccessKind, cxt: &mut Cxt) -> Result<(), TypeError> {
        self.try_access_unborrowed(kind, cxt)?;
        self.borrow(kind, cxt);
        Ok(())
    }
}

impl ast::Expr {
    pub(super) fn check(&self, mut ty: Val, cxt: &mut Cxt, reason: CheckReason) -> Expr {
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
                (ast::Expr::Lam(x), Val::Fun(clos)) if matches!(clos.class, Pi(_, _)) => {
                    // [a, b] [c, d] (e, f) => ...
                    // -->
                    // [a, b, c, d] => ((e, f) => ...)
                    let ty = Val::Fun(clos.clone());

                    let mut clos = clos.move_env(&mut cxt.env());
                    let copy_class = clos.class.copy_class();

                    cxt.push();
                    cxt.record_deps();
                    let mut implicit_tys: VecDeque<_> = match clos.class.icit() {
                        Some(Impl) => clos.params.iter().collect(),
                        _ => VecDeque::new(),
                    };
                    let mut implicit: Vec<_> = check_params(
                        x.pars().imp(),
                        ParamTys::Impl(&mut implicit_tys),
                        reason,
                        None,
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
                            Val::Fun(c) if matches!(c.class, Pi(Expl, _)) => {
                                clos = *c;
                                if clos.env.size != cxt.size() {
                                    clos = clos.move_env(&mut cxt.env());
                                }
                            }
                            body => {
                                if x.pars().and_then(|x| x.exp()).is_some() {
                                    // TODO better error here (include type)
                                    return Err("Lambda contains explicit parameters which are not present in expected type".into());
                                } else {
                                    clos = VClos {
                                        class: Pi(Expl, copy_class),
                                        params: Vec::new(),
                                        env: cxt.env(),
                                        body: body.quote(cxt.size(), None),
                                    }
                                }
                            }
                        }
                    }

                    cxt.mark_top_scope_capture();
                    let copy_class2 = clos.class.copy_class();
                    cxt.push();

                    let (explicit, bty) = if x.pars().and_then(|x| x.exp()).is_some() {
                        (
                            check_params(
                                x.pars().exp(),
                                ParamTys::Expl(clos.par_ty().quote(cxt.size(), None)),
                                reason,
                                None,
                                cxt,
                            ),
                            clos.body.eval(&mut cxt.env()),
                        )
                    } else {
                        (
                            Vec::new(),
                            match clos.params.len() {
                                0 => clos.body.eval(&mut cxt.env()),
                                // Try to curry the explicit parameters onto the body
                                _ => Val::Fun(Box::new(clos)),
                            },
                        )
                    };

                    cxt.mark_top_scope_capture();

                    // let bty = clos.body.eval(&mut cxt.env());
                    let body = x
                        .body()
                        .and_then(|x| x.expr())
                        .ok_or("Missing body for lambda")?
                        .check(bty, cxt, reason);
                    let captures2 = cxt.pop();
                    let captures = cxt.pop();
                    if let &Some((borrow, _)) = &captures {
                        cxt.finish_closure_env(borrow, copy_class, self.span());
                    }
                    if let &Some((borrow, _)) = &captures2 {
                        cxt.finish_closure_env(borrow, copy_class2, self.span());
                    }
                    cxt.finish_deps(x.body().unwrap().span());
                    let access = captures2
                        .and_then(|(_, x)| {
                            x.into_iter().find_map(
                                |(_, (c, a))| if c > copy_class2 { Some(a) } else { None },
                            )
                        })
                        .or_else(|| {
                            captures
                                .filter(|_| !implicit.is_empty())
                                .and_then(|(_, x)| {
                                    x.into_iter().find_map(|(_, (c, a))| {
                                        if c > copy_class {
                                            Some(a)
                                        } else {
                                            None
                                        }
                                    })
                                })
                        });
                    if let Some(access) = access {
                        return Err(MoveError::FunAccess(
                            access,
                            Some(copy_class),
                            Some((ty.quote(cxt.size(), Some(&cxt.mcxt)), reason)),
                        )
                        .into());
                    }

                    let mut term = if explicit.is_empty() {
                        body
                    } else {
                        Expr::Fun(EClos {
                            class: Lam(Expl, copy_class2),
                            params: explicit,
                            body: Box::new(body),
                        })
                    };
                    if !implicit.is_empty() {
                        term = Expr::Fun(EClos {
                            class: Lam(Impl, copy_class),
                            params: implicit,
                            body: Box::new(term),
                        });
                    }
                    Ok(term)
                }

                // Propagate through case/do/etc.
                (ast::Expr::Match(case), ty) => {
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

                // Upgrade copy class of functions
                (_, Val::Fun(clos)) if matches!(clos.class, Pi(_, _)) => {
                    let (x, xty) = self.infer(cxt);
                    let (x, mut xty) = match clos.class {
                        Pi(Impl, _) => (x, xty),
                        _ => x.insert_metas(xty, None, self.span(), cxt),
                    };
                    match &mut xty {
                        Val::Fun(clos2)
                            if matches!(clos2.class, Pi(_, _))
                                && clos2.class.icit() == clos.class.icit()
                                && clos.class.copy_class() > clos2.class.copy_class() =>
                        {
                            clos2.class = Pi(clos2.class.icit().unwrap(), clos.class.copy_class());
                            cxt.unify(xty, Val::Fun(clos), reason)?
                        }
                        _ => cxt.unify(xty, Val::Fun(clos), reason)?,
                    }
                    Ok(x)
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

    fn infer_check(&self, ty: Val, cxt: &mut Cxt, reason: CheckReason) -> Result<Expr, TypeError> {
        let (a, ity) = self.infer(cxt);
        let (a, ity) = match &ty {
            Val::Fun(clos) if matches!(clos.class, Pi(Impl, _)) => (a, ity),
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
                        let borrow = cxt.finish_deps(self.span());
                        Some(Place::Deref(Box::new(PlaceOrExpr::Expr(
                            e,
                            ty,
                            Some(borrow),
                            self.span(),
                        ))))
                    }
                }
            }
            ast::Expr::App(x) if x.imp() == None && x.exp() == None && x.do_expr() == None => {
                let lhs = x.lhs()?.elab_unborrowed(cxt);
                let x = resolve_member(lhs, x.member()?, cxt);
                match x {
                    PlaceOrExpr::Place(place) => Some(place),
                    PlaceOrExpr::Expr(_, _, _, _) => None, // TODO this work gets duplicated
                }
            }
            _ => None,
        }
    }

    pub fn elab_unborrowed(&self, cxt: &mut Cxt) -> PlaceOrExpr {
        match self.elab_place(cxt) {
            Some(place) => PlaceOrExpr::Place(place),
            None => {
                cxt.record_deps();
                let (e, ty) = self.infer(cxt);
                let borrow = cxt.finish_deps(self.span());
                PlaceOrExpr::Expr(e, ty, Some(borrow), self.span())
            }
        }
    }

    pub fn as_args(self) -> Vec<Result<ast::Expr, RelSpan>> {
        self.as_args_(true)
    }

    pub fn as_args_(self, parens: bool) -> Vec<Result<ast::Expr, RelSpan>> {
        match self {
            ast::Expr::GroupedExpr(ref x) if parens => x
                .expr()
                .map(|x| x.as_args_(false))
                .unwrap_or_else(|| vec![Ok(self)]),
            ast::Expr::Pair(x) => {
                let mut v = x
                    .rhs()
                    .map(|x| x.as_args_(false))
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
                                .new_meta(MetaBounds::new(Val::Type), self.span(), MetaSource::Hole)
                                .eval(&mut cxt.env());
                            let meta = cxt.new_meta(
                                MetaBounds::new(mty.clone()),
                                self.span(),
                                MetaSource::Hole,
                            );
                            (meta, mty)
                        } else {
                            let entry = cxt.lookup(name).ok_or(TypeError::NotFound(name.0))?;
                            let ty = entry.ty(cxt);

                            let access = Access {
                                point: name.0.into(),
                                span: name.1,
                                kind: AccessKind::as_move(ty.copy_class(cxt)),
                            };
                            if access.kind == AccessKind::Move {
                                entry
                                    .try_move(ty.clone().quote(cxt.size(), Some(&cxt.mcxt)), cxt)?
                            } else if access.kind == AccessKind::Mut {
                                entry.try_borrow(true, false, cxt)?
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
                        let (term, ty) = infer_fun(x.pars(), None, x.body(), None, x.span(), cxt);
                        (term, ty.eval(&mut cxt.env()))
                    }
                    ast::Expr::Pi(x) => {
                        let copy_class = x
                            .class()
                            .filter(|x| x.refkw().is_some())
                            .map(|x| {
                                if x.mutkw().is_some() {
                                    CopyClass::Mut
                                } else {
                                    CopyClass::Copy
                                }
                            })
                            .unwrap_or(CopyClass::Move);
                        let (_, pi) = infer_fun(
                            x.pars(),
                            x.body().and_then(|x| x.expr()),
                            None,
                            Some(copy_class),
                            x.span(),
                            cxt,
                        );
                        (pi, Val::Type)
                    }
                    ast::Expr::Reference(x) => {
                        let x = x.expr().ok_or("Expected type of reference")?.check(
                            Val::Type,
                            cxt,
                            CheckReason::UsedAsType,
                        );
                        (Expr::RefType(false, Box::new(x)), Val::Type)
                    }
                    ast::Expr::RefMut(x) => {
                        let x = x.expr().ok_or("Expected type of reference")?.check(
                            Val::Type,
                            cxt,
                            CheckReason::UsedAsType,
                        );
                        (Expr::RefType(true, Box::new(x)), Val::Type)
                    }
                    ast::Expr::Deref(_) => {
                        let place = self.elab_place(cxt).ok_or("Expected reference after *")?;
                        let xty = place.ty(cxt)?;
                        place.try_access(AccessKind::as_move(xty.copy_class(cxt)), cxt)?;
                        let x = place.to_expr(cxt);
                        (x, xty)
                    }
                    ast::Expr::Assign(x) => {
                        let place = x
                            .lhs()
                            .ok_or("Missing left-hand side of assignment")?
                            .elab_place(cxt)
                            .ok_or("Cannot assign to expression")?;
                        let ty = place.ty(cxt)?;
                        let expr = x
                            .rhs()
                            .ok_or("Missing right-hand side of assignment")?
                            .check(ty, cxt, CheckReason::MustMatch(x.lhs().unwrap().span()));
                        // Don't borrow the lhs until after the rhs - this is important for e.g. `self.x = self.calc_x()`
                        place.try_access(AccessKind::Mut, cxt)?;
                        // TODO the lhs should now depend on any borrows in the rhs
                        (
                            Expr::Assign(Box::new(place.to_expr(cxt)), Box::new(expr)),
                            Val::var(Var::Builtin(Builtin::UnitType)),
                        )
                    }
                    ast::Expr::App(x) => {
                        cxt.record_deps();
                        let mut lhs = x
                            .lhs()
                            .ok_or("Missing left-hand side of application")?
                            .elab_unborrowed(cxt);
                        let mut self_arg = None;
                        let self_span = lhs.span();
                        if let Some(member) = x.member() {
                            lhs = match resolve_member_method(lhs.into(), member.clone(), cxt) {
                                Ok(lhs) => lhs,
                                Err((lhs, method)) => {
                                    let ty = method.ty(cxt);
                                    self_arg = Some(lhs);
                                    PlaceOrExpr::Expr(method, ty, None, member.span())
                                }
                            }
                        }
                        let mut lhs_ty = lhs.ty(cxt).inlined(cxt);
                        let mut lhs_span = lhs.span();
                        let mut lhs = lhs.finish_and_borrow(
                            AccessKind::as_ref(lhs_ty.copy_class(cxt)),
                            AccessKind::Copy,
                            cxt,
                        );

                        if x.exp().is_some() && self_arg.is_none() {
                            if let &Expr::Head(Head::Var(Var::Def(_, def))) = &lhs {
                                let edef = cxt.db.def_type(def);
                                match edef
                                    .as_ref()
                                    .and_then(|x| x.result.as_ref())
                                    .map(|x| (x.name, &x.type_def))
                                {
                                    Some((name, Some(TypeDefKind::Type(ctors))))
                                        if ctors.len() == 1 =>
                                    {
                                        let (split, _, ty) = ctors.first().unwrap();
                                        if *split == SplitId::Idx(0) {
                                            lhs = Expr::var(Var::Cons(
                                                name,
                                                cxt.db.cons_id(def, *split),
                                            ));
                                            lhs_ty = ty.clone();
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }

                        // First handle implicit arguments, then curry and apply explicits
                        let (lhs, lhs_ty) = lhs.insert_metas(lhs_ty, x.imp(), lhs_span, cxt);
                        lhs_span.end = x.imp().map(|x| x.span()).unwrap_or(lhs_span).end;

                        // Apply explicit arguments
                        let fun_name = match lhs.unspanned() {
                            Expr::Head(Head::Var(v)) => v.name(cxt.db),
                            _ => None,
                        };
                        let (expr, ty) = if let Some(mut exp) = x.exp() {
                            if let Some(block) = x.do_expr() {
                                // Reassociate to put the do block on the right side
                                exp = exp.as_args().into_iter().rev().fold(
                                    block.expr().ok_or("expected expression in do block")?,
                                    |acc, x| {
                                        let x = x.unwrap_or_else(|s| {
                                            ast::Expr::GroupedExpr(ast::GroupedExpr::Val {
                                                span: s,
                                                expr: None,
                                            })
                                        });
                                        let span = RelSpan::new(x.span().start, acc.span().end);
                                        ast::Expr::Pair(ast::Pair::Val {
                                            span,
                                            lhs: Some(Box::new(x)),
                                            rhs: Some(Box::new(acc)),
                                        })
                                    },
                                );
                            }
                            let (exp, rty) = match lhs_ty {
                                Val::Fun(clos) if matches!(clos.class, Pi(_, _)) => {
                                    let aty = clos.par_ty();
                                    let (self_arg, ety) = if let Some(mut self_arg) = self_arg {
                                        let (sty, eclos) = match aty {
                                            Val::Fun(clos) if clos.class == Sigma => {
                                                (clos.par_ty(), Some(clos))
                                            }
                                            aty => (aty, None),
                                        };
                                        // Insert proper ref and derefs
                                        loop {
                                            match (&sty, self_arg.ty(cxt)) {
                                                (Val::RefType(_, _), Val::RefType(_, _)) => break,
                                                (Val::RefType(m, _), _) => {
                                                    let ty = self_arg.ty(cxt);
                                                    cxt.record_deps();
                                                    let e = self_arg.finish(
                                                        AccessKind::as_ref(sty.copy_class(cxt)),
                                                        cxt,
                                                    );
                                                    let b = cxt.finish_deps(self_span);
                                                    self_arg = PlaceOrExpr::Expr(
                                                        Expr::Ref(*m, Box::new(e)),
                                                        Val::RefType(*m, Box::new(ty)),
                                                        Some(b),
                                                        self_span,
                                                    );
                                                    break;
                                                }
                                                (_, Val::RefType(_, _)) => {
                                                    self_arg = PlaceOrExpr::Place(Place::Deref(
                                                        Box::new(self_arg),
                                                    ));
                                                    continue;
                                                }
                                                _ => break,
                                            }
                                        }
                                        let pty = self_arg.ty(cxt);
                                        let kind = AccessKind::as_ref(sty.copy_class(cxt));
                                        cxt.unify(pty, sty, CheckReason::ArgOf(lhs_span))?;
                                        let self_arg = self_arg.finish(kind, cxt);
                                        (
                                            Some(self_arg.clone()),
                                            eclos.map(|x| x.apply(self_arg.eval(&mut cxt.env()))),
                                        )
                                    } else {
                                        (None, Some(aty))
                                    };
                                    let exp = match (ety, exp) {
                                        (None, ast::Expr::GroupedExpr(x)) if x.expr().is_none() => {
                                            self_arg.expect("pretty sure this case is impossible")
                                        }
                                        (None, x) => {
                                            cxt.error(
                                                x.span(),
                                                "Unexpected extra arguments to method call",
                                            );
                                            Expr::Error
                                        }
                                        (Some(ety), exp) => {
                                            let exp =
                                                exp.check(ety, cxt, CheckReason::ArgOf(lhs_span));
                                            match self_arg {
                                                Some(arg) => Expr::Pair(
                                                    Box::new(arg),
                                                    Box::new(exp),
                                                    Box::new(
                                                        clos.par_ty()
                                                            .quote(cxt.size(), Some(&cxt.mcxt)),
                                                    ),
                                                ),
                                                None => exp,
                                            }
                                        }
                                    };
                                    let vexp = exp.clone().eval(&mut cxt.env());
                                    let rty = clos.apply(vexp);
                                    (exp, rty)
                                }
                                Val::Error => {
                                    // Still try inferring the argument to catch errors
                                    let (exp, _) = exp.infer(cxt);
                                    (exp, Val::Error)
                                }
                                lhs_ty => {
                                    cxt.finish_deps(x.span());
                                    return Err(TypeError::NotFunction(
                                        lhs_ty.quote(cxt.size(), Some(&cxt.mcxt)),
                                        lhs_span,
                                    ));
                                }
                            };
                            (
                                Expr::Elim(Box::new(lhs), Box::new(Elim::App(Expl, exp))),
                                rty,
                            )
                        } else {
                            if self_arg.is_some() {
                                cxt.error(
                                    lhs_span,
                                    Doc::start("'").chain(lhs.pretty(cxt.db)).add(
                                        "' is a method, not a field; use parentheses () to call it",
                                        (),
                                    ),
                                );
                            }
                            (lhs, lhs_ty)
                        };
                        let arg_borrow = cxt.finish_deps(x.span());
                        let parents = arg_borrow.mutable_dependencies(cxt);
                        for (parent, mut access) in parents {
                            access.point = AccessPoint::Function(fun_name);
                            access.span = lhs_span;
                            arg_borrow.add_borrow(parent, access, cxt);
                        }
                        cxt.add_dep(
                            arg_borrow,
                            Access {
                                point: AccessPoint::Expr,
                                kind: AccessKind::Move,
                                span: x.span(),
                            },
                        );
                        (expr, ty)
                    }
                    ast::Expr::Do(d) => {
                        let mut rty = None;
                        let expr = d.elaborate(&mut rty, cxt);
                        let rty = rty.map(|(x, _)| x).unwrap_or(Val::Error);
                        (expr, rty)
                    }
                    ast::Expr::Match(case) => {
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
                                Literal::F64(_) => todo!("floats"),
                                Literal::F32(_) => todo!("floats"),
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
                                        CheckReason::MustMatch(x.a().unwrap().span()),
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
                                                    params: vec![Par::new(
                                                        (
                                                            cxt.db.name("_".into()),
                                                            x.a().unwrap().span(),
                                                        ),
                                                        ty.clone().quote(cxt.size(), None),
                                                    )],
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
                    ast::Expr::If(_) => todo!("if"),
                    ast::Expr::Box(_) => todo!("box"),
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
                            params: vec![Par::new(
                                (cxt.db.name("_".to_string()), x.lhs().unwrap().span()),
                                aty,
                            )],
                            body: Box::new(bty),
                        });
                        let vty = ty.clone().eval(&mut cxt.env());
                        (Expr::Pair(Box::new(a), Box::new(b), Box::new(ty)), vty)
                    }
                    ast::Expr::EffPat(_) => {
                        return Err(TypeError::Other(Doc::start(
                            "'eff' not allowed in this context",
                        )))
                    }
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
                    ast::Expr::ImplPat(_) => {
                        return Err(TypeError::Other(Doc::start(
                            "'impl' not allowed in this context",
                        )))
                    }
                    ast::Expr::StructInit(x) => {
                        let lhs = x
                            .lhs()
                            .ok_or("missing struct name")?
                            .check(Val::Type, cxt, CheckReason::UsedAsType)
                            .eval(&mut cxt.env());
                        match &lhs {
                            Val::Neutral(n) => match n.head() {
                                Head::Var(Var::Def(def_name, def)) => {
                                    if let Some(DefType {
                                        type_def: Some(TypeDefKind::Struct(fields)),
                                        is_trait,
                                        ty,
                                        ..
                                    }) = cxt.db.def_type(def).and_then(|x| x.result)
                                    {
                                        if is_trait {
                                            let self_arg = match n.spine().first() {
                                                Some(Elim::App(Impl, x)) => match ty {
                                                    Val::Fun(clos)
                                                        if matches!(clos.class, Pi(Impl, _)) =>
                                                    {
                                                        x.clone()
                                                            .zip_pair(&clos.params)
                                                            .unwrap()
                                                            .into_iter()
                                                            .next()
                                                            .unwrap()
                                                            .0
                                                    }
                                                    x => unreachable!("{:?}", x),
                                                },
                                                x => unreachable!("{:?}", x),
                                            };
                                            cxt.push_trait_impl_scope(self_arg);
                                        }

                                        let body = x.fields().ok_or("missing struct fields")?;
                                        let mut named = Vec::new();
                                        let mut vals: Vec<(usize, Val)> = Vec::new();
                                        let env = {
                                            let mut env = cxt.env();
                                            match cxt
                                                .db
                                                .def_type(def)
                                                .and_then(|x| x.result)
                                                .unwrap()
                                                .ty
                                            {
                                                Val::Fun(clos)
                                                    if matches!(clos.class, Pi(Impl, _)) =>
                                                {
                                                    assert!(
                                                        matches!(n.head(), Head::Var(Var::Def(_, d)) if d == def)
                                                    );
                                                    for i in n.spine() {
                                                        match i {
                                                                    Elim::App(Impl, x) => {
                                                                        for (val, _) in x
                                                                            .clone()
                                                                            .zip_pair(&clos.params)
                                                                            .expect("TODO switch to using case or something")
                                                                        {
                                                                            env.push(Some(Ok(val)));
                                                                        }
                                                                    }
                                                                    _ => unreachable!(),
                                                                }
                                                    }
                                                }
                                                _ => (),
                                            }
                                            env
                                        };
                                        for stmt in body.fields() {
                                            let (name, val) = stmt.elab_field(cxt).ok_or("Expression in struct literal must define a name and give it a value")?;
                                            let (idx, (fname, ety)) = fields
                                                .iter()
                                                .enumerate()
                                                .find(|(_, (n, _))| n.0 == name.0)
                                                .ok_or(
                                                    Doc::start("Struct ")
                                                        .chain(def_name.pretty(cxt.db))
                                                        .add(" has no member '", ())
                                                        .chain(name.pretty(cxt.db))
                                                        .add("'", ()),
                                                )?;
                                            let mut env = {
                                                let mut env = env.clone();

                                                for i in 0..idx {
                                                    env.push(
                                                        vals.iter()
                                                            .find(|(n, _)| *n == i)
                                                            .map(|(_, x)| Ok(x.clone())),
                                                    );
                                                }
                                                env
                                            };
                                            let ety = ety.clone().eval(&mut env);
                                            let val = match val {
                                                Ok((expr, ty)) => {
                                                    cxt.unify(
                                                        ty,
                                                        ety,
                                                        CheckReason::GivenType(fname.1),
                                                    )?;
                                                    expr
                                                }
                                                Err(expr) => expr.check(
                                                    ety,
                                                    cxt,
                                                    CheckReason::GivenType(fname.1),
                                                ),
                                            };
                                            vals.push((idx, val.clone().eval(&mut cxt.env())));
                                            named.push((name, val));
                                        }

                                        if is_trait {
                                            cxt.pop();
                                        }

                                        let ret = fields.iter().map(|(name, _)| {
                                            let mut found = None;
                                            for (n, e) in &named {
                                                if n.0 == name.0 {
                                                    if found.is_none() {
                                                        found = Some(e.clone());
                                                    } else {
                                                        cxt.error(n.1, Doc::start("Struct literal contains duplicate name '").chain(n.pretty(cxt.db)).add("'", ()));
                                                    }
                                                }
                                            }
                                            found.unwrap_or_else(|| {
                                                cxt.error(def_name.1, Doc::start("Struct literal missing field '").chain(name.pretty(cxt.db)).add("'", ()));
                                                Expr::Error
                                            })
                                        }).collect();
                                        let ety = lhs.clone().quote(cxt.size(), Some(&cxt.mcxt));
                                        return Ok((Expr::Struct(def, ret, Box::new(ety)), lhs));
                                    }
                                }
                                _ => (),
                            },
                            _ => (),
                        }
                        cxt.error(
                            x.lhs().unwrap().span(),
                            "Expected struct type before 'struct'",
                        );
                        (Expr::Error, Val::Error)
                    }
                }
            })
        };
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
                            Some(c) => {
                                return Err(format!("Invalid escape sequence \\{}", c));
                            }
                            None => panic!("Unclosed string should have been caught in lexer"),
                        }
                    }
                    Some(c) => buf.push(c),
                    None => panic!("Unclosed string should have been caught in lexer"),
                }
            }
            Ok(Literal::String(cxt.db.name(buf)))
        } else if let Some(l) = self.int().or(self.float()) {
            let num = lex_number(l.text()).map_err(|e| format!("Invalid literal: {}", e))?;
            match num {
                NumLiteral::IPositive(i) => {
                    let meta = cxt.mcxt.unscoped_meta(
                        MetaBounds::int_type(false, i),
                        self.span(),
                        MetaSource::Other(Doc::start("type of int literal")),
                    );
                    Ok(Literal::Int(i, Err((false, meta))))
                }
                NumLiteral::INegative(i) => {
                    let meta = cxt.mcxt.unscoped_meta(
                        MetaBounds::int_type(true, i as u64),
                        self.span(),
                        MetaSource::Other(Doc::start("type of int literal")),
                    );
                    Ok(Literal::Int(i as u64, Err((true, meta))))
                }
                NumLiteral::Float(_) => todo!("floats"),
            }
        } else {
            panic!("invalid literal: {:?}", self.syntax());
        }
    }
}
