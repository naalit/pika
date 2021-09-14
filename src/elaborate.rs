use crate::common::*;
use crate::term::*;
use std::sync::Arc;
use std::time::Instant;

mod mcxt;
pub use mcxt::*;
mod unify;
pub use unify::*;
mod errors;
pub use errors::*;

impl PreDef {
    /// Extracts the type given. If no type is given, returns a meta; if it doesn't typecheck, returns None and doesn't report the errors as they'll be caught in elaborate_def().
    pub fn given_type(&self, id: PreDefId, cxt: Cxt, db: &dyn Compiler) -> Option<VTy> {
        let mut mcxt = MCxt::new(cxt, MCxtType::Global(id), db);
        match self {
            PreDef::Typed(_, ty, _) => Some(ty.clone()),
            PreDef::Fun(_, args, rty, _, effs) | PreDef::FunDec(_, args, rty, effs) => {
                let mut rargs = Vec::new();
                elab_args(args, &mut rargs, &mut mcxt).ok()?;

                // TODO what to do with inferred effects?
                let effs: Result<_, _> = effs
                    .iter()
                    .flatten()
                    .map(|x| {
                        check(
                            x,
                            &Val::builtin(Builtin::Eff, Val::Type),
                            ReasonExpected::UsedInWith,
                            &mut mcxt,
                        )
                        .map(|x| x.evaluate(&mcxt.env(), &mcxt))
                    })
                    .collect();

                match check(rty, &Val::Type, ReasonExpected::UsedAsType, &mut mcxt)
                    .and_then(|a| effs.map(|b| (a, b)))
                {
                    Ok((rty, effs)) => {
                        let rty = rty.evaluate(&mcxt.env(), &mcxt);
                        let mut l = mcxt.size;
                        Some(
                            rargs
                                .into_iter()
                                .rfold((rty, effs), |(rty, effs), (name, i, xty)| {
                                    let rty = rty.quote(l, &mcxt);
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
                elab_args(ty_args, &mut rargs, &mut mcxt).ok()?;
                let mut l = mcxt.size;
                let ty_rty = if *is_eff {
                    Val::builtin(Builtin::Eff, Val::Type)
                } else {
                    Val::Type
                };
                Some(rargs.into_iter().rfold(ty_rty, |rty, (name, i, xty)| {
                    let rty = rty.quote(l, &mcxt);
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
                    MetaSource::LocalType(mcxt.db.intern_name("_".to_string())),
                    Term::Type,
                )
                .evaluate(&mcxt.env(), &mcxt),
            ),
            PreDef::ValDec(_, ty) | PreDef::Val(_, ty, _) | PreDef::Impl(_, ty, _) => {
                match check(ty, &Val::Type, ReasonExpected::UsedAsType, &mut mcxt) {
                    Ok(ty) => Some(ty.evaluate(&mcxt.env(), &mcxt)),
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
    let mut mcxt = MCxt::from_state(state, MCxtType::Local(def), db);

    let (term, ty) = match infer_def(&predef, def, &mut mcxt) {
        Ok(x) => x,
        Err(e) => {
            db.maybe_report_error(e.into_error(file, &mcxt));
            return Err(DefError::ElabError);
        }
    };

    if let Some(given_ty) = predef.given_type(predef_id, cxt, db) {
        if !unify(
            ty.clone(),
            given_ty.clone(),
            mcxt.size,
            predef.span(),
            &mut mcxt,
        )
        .unwrap_or_else(|e| {
            db.maybe_report_error(e.into_error(file, &mcxt));
            true
        }) {
            db.report_error(
                Error::new(
                    file,
                    Doc::start("Could not match type of ")
                        .add(
                            predef
                                .name()
                                .map(|x| x.get(db))
                                .unwrap_or_else(|| "<expression>".into()),
                        )
                        .add(": expected type ")
                        .debug(given_ty)
                        .add(" but got type ")
                        .chain(ty.pretty(&mcxt)),
                    predef.span(),
                    "defined here",
                )
                .with_note("this is probably a compiler error"),
            );
        }
    }

    let ret = match mcxt.check_locals() {
        Ok(()) => {
            let term = term.map(|x| x.inline_metas(&mcxt, cxt.size(db)));
            let ty = ty.inline_metas(cxt.size(db), &mcxt);

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
                term: term.map(Arc::new),
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
            let term = (**ret
                .term
                .as_ref()
                .expect("@[normalize] not allowed on declarations!"))
            .clone();

            let n_start = Instant::now();
            let _ = term.evaluate(&mcxt.env(), &mcxt).force(mcxt.size, &mcxt);
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

fn infer_def(def: &PreDef, id: DefId, mcxt: &mut MCxt) -> Result<(Option<Term>, VTy), TypeError> {
    match def {
        PreDef::Typed(def, ty, reason) => {
            let term = check_def(def, id, ty, reason.clone(), mcxt)?;
            Ok((term, ty.clone()))
        }
        PreDef::FunDec(_, _from, _to, _effs) => {
            // TODO: When function declarations are actually used, change this so they're dependent.
            todo!("function declarations")
            // for (_, _, from) in from {
            //     if let Err(e) = check(from, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
            //         mcxt.db.report_error(e.into_error(file, db, &mcxt));
            //     }
            // }
            // if let Err(e) = check(to, &Val::Type, ReasonExpected::UsedAsType, db, &mut mcxt) {
            //     mcxt.db.report_error(e.into_error(file, db, &mcxt));
            // }
            // Err(DefError::NoValue)
        }
        PreDef::ValDec(name, ty) => {
            if !mcxt.is_sig {
                return Err(TypeError::IllegalDec(name.span(), true));
            }
            let t = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let t = t.evaluate(&mcxt.env(), mcxt);
            Ok((None, t))
        }
        _ if mcxt.is_sig => Err(TypeError::IllegalDec(def.span(), false)),

        PreDef::Val(_, ty, val) | PreDef::Impl(_, ty, val) => {
            let tyspan = ty.span();
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let ty = ty.evaluate(&mcxt.env(), mcxt);
            let val = check(val, &ty, ReasonExpected::Given(tyspan), mcxt)?;
            Ok((Some(val), ty))
            // TODO multiple TypeErrors?
            // Err(e) => {
            //     mcxt.db.maybe_report_error(e.into_error(file, db, &mcxt));
            //     // The given type is invalid, but we can still try to infer the type
            //     match infer(true, val, db, &mut mcxt) {
            //         Ok(x) => Ok(x),
            //         Err(e) => {
            //             mcxt.db.maybe_report_error(e.into_error(file, db, &mcxt));
            //             Err(DefError::ElabError)
            //         }
            //     }
            // }
        }
        PreDef::Fun(_, args, body_ty, body, effs) => {
            // First, add the arguments to the environment
            let mut targs = Vec::new();
            elab_args(args, &mut targs, mcxt)?;

            // Then elaborate and evaluate the given return type
            let tyspan = body_ty.span();
            let body_ty = check(body_ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let vty = body_ty.evaluate(&mcxt.env(), mcxt);

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
                        mcxt,
                    )
                    .map(|x| x.evaluate(&mcxt.env(), mcxt))
                })
                .collect::<Result<_, _>>()?;
            // And last, check the function body against the return type
            let (body, vty, effs) =
                check_fun(body, vty, ReasonExpected::Given(tyspan), effs, open, mcxt)?;

            // Then construct the function term and type
            let effs_t: Vec<_> = effs
                .iter()
                // Decrease the size because the effects are outside the last pi type
                .map(|x| x.clone().quote(mcxt.size.dec(), mcxt))
                .collect();
            Ok((
                Some(
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
                                        Box::new(ty.clone().quote(size, mcxt)),
                                        Box::new(body),
                                        effs,
                                    ),
                                    size,
                                    Vec::new(),
                                )
                            },
                        )
                        .0,
                ),
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
                                        term: to.quote(size, mcxt),
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
                Some(Term::Var(
                    Var::Cons(id),
                    Box::new(ty.clone().quote(mcxt.size, mcxt)),
                )),
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
            elab_args(ty_args, &mut targs, mcxt)?;

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
                                term: to.quote(l, mcxt),
                                name: *n,
                            }),
                            Vec::new(),
                        ),
                        l.dec(),
                    )
                });
            let (predef_id, _) = mcxt.db.lookup_intern_def(id);
            mcxt.define(**name, NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()));

            // The context after adding the type arguments, used when evaluating constructors without
            // explicit return types, where all type arguments are implicitly in scope
            let cxt_after = mcxt.state();

            // Add the datatype's type to the context before adding the type arguments for use by cons types
            mcxt.set_state(cxt_before);
            mcxt.define(**name, NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()));
            let cxt_before = mcxt.state();

            let mut scope = Vec::new();

            // Go through the constructors and elaborate them
            let mut seen: HashMap<Name, Span> = HashMap::new();
            for (cname, args, cty) in ctors.iter(mcxt.db) {
                if let Some(&span) = seen.get(&cname) {
                    let file = mcxt.cxt.file(mcxt.db);
                    let e = Error::new(
                        file,
                        format!(
                            "Duplicate constructor name '{}' in type definition",
                            mcxt.db.lookup_intern_name(*cname)
                        ),
                        cname.span(),
                        "declared again here",
                    )
                    .with_label(file, span, "previously declared here");
                    mcxt.db.report_error(e);
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
                    let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
                    let vty = ty.evaluate(&mcxt.env(), mcxt);
                    cargs.push((name, icit, vty.clone()));
                    mcxt.define(name, NameInfo::Local(vty));
                }

                // If the user provided a return type for the constructor, typecheck it
                let (cty, eff_ty) = if let Some(cty) = cty {
                    let x = check(cty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
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
                        let ty_ty = ty_ty.clone().quote(size, mcxt);
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
                                        (*xty, rty.eval_quote(&mut env, size, mcxt))
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
                                let mut type_string = mcxt.db.lookup_intern_name(**name);
                                for (n, _, _) in &targs {
                                    type_string.push(' ');
                                    type_string.push_str(&mcxt.db.lookup_intern_name(*n));
                                }
                                let e = Error::new(
                                    mcxt.cxt.file(mcxt.db),
                                    "Constructor return type must be the type it's a part of",
                                    cty.span(),
                                    Doc::start("expected return type ")
                                        .chain(Doc::start(type_string).style(Style::None))
                                        .style(Style::Error),
                                );
                                mcxt.db.report_error(e);
                                return Err(TypeError::Sentinel);
                            }
                        }
                    }
                // If they didn't provide a return type, use the type constructor applied to all args
                } else {
                    if *is_eff {
                        let e = Error::new(
                            mcxt.cxt.file(mcxt.db),
                            format!(
                                "Effect constructor '{}' must declare return type",
                                mcxt.db.lookup_intern_name(*cname)
                            ),
                            cname.span(),
                            "this requires a return type",
                        )
                        .with_note("use the unit type `()` if it returns nothing");
                        mcxt.db.report_error(e);
                        continue;
                    }

                    // predef_id is for the type being declared
                    // Ty a b of C [a] [b] ... : Ty a b
                    // so Ix's decrease from left to right, and start at the first implicit argument
                    // which is right after the state cxt_before stores
                    let ty_ty = ty_ty.clone().quote(mcxt.size, mcxt);
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
                                            (*xty, rty.eval_quote(&mut env, mcxt.size, mcxt))
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
                                Box::new(from.quote(l.dec(), mcxt)),
                                Box::new(to),
                                eff.into_iter().collect(),
                            ),
                            None,
                            l.dec(),
                        )
                    },
                );

                let full_ty = full_ty.evaluate(&Env::new(cxt_before.size), mcxt);
                // .inline_metas(&mcxt);

                scope.push((cname.clone(), full_ty));
            }

            mcxt.set_state(cxt_before.clone());

            // Make sure to inline metas solved in constructor types
            let ty_ty = ty_ty.inline_metas(mcxt.size, mcxt);
            mcxt.undef();
            mcxt.define(**name, NameInfo::Other(Var::Rec(predef_id), ty_ty.clone()));
            let mut scope: Vec<_> = scope
                .into_iter()
                .map(|(cname, ty)| {
                    let ty = ty.inline_metas(mcxt.size, mcxt);
                    let def_id = mcxt.db.intern_def(
                        mcxt.db
                            .intern_predef(Arc::new(PreDef::Cons(cname.clone(), ty).into())),
                        cxt_before.clone(),
                    );
                    (*cname, def_id)
                })
                .collect();

            // Add definitions from the associated namespace
            // They need the type of the datatype we're defining
            // They also need the constructors, so we create a temporary scope.
            // Since Var::unify doesn't compare the scope ids, it works.
            let tscope = mcxt.db.intern_scope(Arc::new(scope.clone()));
            let assoc_cxt = mcxt.cxt.define(
                **name,
                NameInfo::Other(Var::Type(id, tscope), ty_ty.clone()),
                mcxt.db,
            );
            // And they have access to all the constructors in `scope` at the top level
            let assoc_cxt = scope.iter().fold(assoc_cxt, |cxt, &(n, v)| {
                cxt.define(n, NameInfo::Def(v), mcxt.db)
            });
            scope.extend(
                // The associated namespace can't directly use effects
                intern_block(
                    namespace.clone(),
                    mcxt.db,
                    CxtState::new(assoc_cxt, mcxt.db),
                )
                .into_iter()
                .filter_map(|id| {
                    let (pre, _) = mcxt.db.lookup_intern_def(id);
                    let pre = mcxt.db.lookup_intern_predef(pre);
                    // If it doesn't have a name, we don't include it in the Vec
                    // TODO: but then we don't elaborate it and check for errors. Does this ever happen?
                    pre.name().map(|n| (n, id))
                })
                .inspect(|(_, id)| {
                    // Report any errors
                    let _ = mcxt.db.elaborate_def(*id);
                }),
            );

            // Add the associated namespace, including constructors, to this term's children so they'll get lowered
            mcxt.children.extend(scope.iter().map(|&(_, id)| id));

            let scope = mcxt.db.intern_scope(Arc::new(scope));

            Ok((
                Some(Term::Var(
                    Var::Type(id, scope),
                    Box::new(ty_ty.clone().quote(mcxt.size, mcxt)),
                )),
                ty_ty,
            ))
        }
        PreDef::Expr(e) => infer(true, e, mcxt).map(|(x, t)| (Some(x), t)),
    }
}

fn check_def(
    def: &PreDef,
    id: DefId,
    ty: &VTy,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
) -> Result<Option<Term>, TypeError> {
    match def {
        PreDef::Val(_, ty2, val) | PreDef::Impl(_, ty2, val) => {
            let ty2 = check(ty2, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let ty2 = ty2.evaluate(&mcxt.env(), mcxt);
            try_unify(ty, &ty2, None, def.span(), reason.clone(), mcxt)?;
            let val = check(val, ty, reason, mcxt)?;
            Ok(Some(val))
        }
        // TODO functions
        _ => {
            let (term, i_ty) = infer_def(def, id, mcxt)?;
            try_unify(ty, &i_ty, term.as_ref(), def.span(), reason, mcxt)?;
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
) -> Result<(), TypeError> {
    if !unify(ty.clone(), i_ty.clone(), mcxt.size, span, mcxt)? {
        // Use an arity error if we got a function type but don't expect one
        match (&ty, &i_ty) {
            (Val::Clos(Pi, _, _, _), _) | (Val::Fun(_, _, _), _) => (),
            (_, Val::Fun(_, _, _)) | (_, Val::Clos(Pi, _, _, _))
                if matches!(term, Some(Term::App(_, _, _))) =>
            {
                let got = term.unwrap().spine_len();
                let hty = match term.cloned().unwrap().evaluate(&mcxt.env(), mcxt) {
                    Val::App(_, hty, _, _) => *hty,
                    _ => i_ty.clone(),
                };
                let exp = hty.arity(false);
                return Err(TypeError::WrongArity(Spanned::new(hty, span), exp, got));
            }
            _ => (),
        }
        Err(TypeError::Unify(
            Spanned::new(i_ty.clone().inline_metas(mcxt.size, mcxt), span),
            ty.clone().inline_metas(mcxt.size, mcxt),
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
) -> Result<(), TypeError> {
    for (name, icit, ty) in args {
        let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
        let vty = ty.evaluate(&mcxt.env(), mcxt);
        rargs.push((*name, *icit, vty.clone()));
        mcxt.define(*name, NameInfo::Local(vty));
    }
    Ok(())
}

/// If `term` of type `ty` takes implicit parameters, insert metas to apply them.
fn insert_metas(insert: bool, term: Term, ty: VTy, span: Span, mcxt: &mut MCxt) -> (Term, VTy) {
    match ty {
        Val::Clos(Pi, Icit::Impl, cl, effs) if insert => {
            let meta = mcxt.new_meta(
                None,
                span,
                MetaSource::ImplicitParam(cl.name),
                cl.ty.clone().quote(mcxt.size, mcxt),
            );
            // TODO effects when applying implicits
            assert!(
                effs.is_empty(),
                "effects when applying implicits not supported yet"
            );
            let vmeta = meta.clone().evaluate(&mcxt.env(), mcxt);
            let ret = (*cl).clone().apply(vmeta, mcxt);
            insert_metas(
                insert,
                Term::App(Icit::Impl, Box::new(term), Box::new(meta)),
                ret,
                span,
                mcxt,
            )
        }
        Val::App(h, hty, sp, g) if insert => match g.resolve(h, &sp, mcxt.size, mcxt) {
            Some(ty) => insert_metas(insert, term, ty, span, mcxt),
            None => (term, Val::App(h, hty, sp, g)),
        },
        Val::Arc(x) if insert => {
            let x = x.into_owned();
            insert_metas(insert, term, x, span, mcxt)
        }
        ty => (term, ty),
    }
}

pub fn infer(insert: bool, pre: &Pre, mcxt: &mut MCxt) -> Result<(Term, VTy), TypeError> {
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

        Pre_::Box(b, x) => {
            let x = check(x, &Val::Type, ReasonExpected::UsedInBox, mcxt)?;
            Ok((Term::Box(*b, Box::new(x)), Val::Type))
        }

        Pre_::BinOp(op, a, b) => {
            // If one side is a literal, use the type of the other side
            let (va, aty, b) = match infer(true, a, mcxt) {
                Ok((va, aty)) => (va, aty, b),
                Err(TypeError::UntypedLiteral(_)) => {
                    let (vb, bty) = infer(true, b, mcxt)?;
                    (vb, bty, a)
                }
                Err(e) => return Err(e),
            };
            // Check b against the type and inline metas first, to allow:
            // a : ?0, b : I32 --> `a + b` which solves ?0 to I32
            let b = check(b, &aty, ReasonExpected::MustMatch(a.span()), mcxt)?;
            let aty = aty.inline_metas(mcxt.size, mcxt);
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
                .map(|x| x.quote(mcxt.size, mcxt))
                .unwrap_or_else(|| ity.clone());
            let vrty = vrty.unwrap_or_else(|| ity.clone().evaluate(&mcxt.env(), mcxt));
            let fty = Term::Fun(
                Box::new(ity.clone()),
                Box::new(Term::Fun(Box::new(ity), Box::new(rty), Vec::new())),
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
                mcxt,
            )?;
            let b = check(
                b,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::LogicOp,
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
                mcxt,
            )?;
            let b = check(
                b,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::LogicOp,
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
                mcxt,
            )?;
            let yspan = yes.span();
            let (yes, ty) = infer(insert, yes, mcxt)?;
            let no = check(no, &ty, ReasonExpected::MustMatch(yspan), mcxt)?;
            let tty = ty.clone().quote(mcxt.size, mcxt);
            Ok((cond.make_if(yes, no, tty), ty))
        }

        Pre_::Var(name) => {
            // If its name is `_`, it's a hole
            if &mcxt.db.lookup_intern_name(*name) == "_" {
                return infer(insert, &pre.copy_span(Pre_::Hole(MetaSource::Hole)), mcxt);
            }

            let (term, ty) = match mcxt.lookup(*name) {
                Ok((v, ty)) => Ok((
                    Term::Var(v, Box::new(ty.clone().quote(mcxt.size, mcxt))),
                    ty,
                )),
                // If something else had a type error, try to keep going anyway and maybe catch more
                Err(DefError::ElabError) => Err(TypeError::Sentinel),
                Err(DefError::NoValue) => Err(TypeError::NotFound(pre.copy_span(*name))),
            }?;
            Ok(insert_metas(insert, term, ty, pre.span(), mcxt))
        }

        Pre_::Lam(name, icit, ty, body) => {
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt);
            // TODO Rc to get rid of the clone()?
            mcxt.define(*name, NameInfo::Local(vty.clone()));
            mcxt.eff_stack.push_scope(true, pre.span());

            let (body, bty) = infer(true, body, mcxt)?;
            let effs = mcxt.eff_stack.pop_scope();

            mcxt.undef();

            let effs_t = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt))
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
                        term: bty.quote(mcxt.size.inc(), mcxt),
                        name: *name,
                    }),
                    effs,
                ),
            ))
        }

        Pre_::Pi(name, icit, ty, ret, effs) => {
            let ty = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            // TODO Rc to get rid of the clone()?
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt);
            mcxt.define(*name, NameInfo::Local(vty));
            let ret = check(ret, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            mcxt.undef();

            let effs = effs
                .iter()
                .map(|x| {
                    check(
                        x,
                        &Val::builtin(Builtin::Eff, Val::Type),
                        ReasonExpected::UsedInWith,
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
            let from = check(from, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let to = check(to, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;

            let effs = effs
                .iter()
                .map(|x| {
                    check(
                        x,
                        &Val::builtin(Builtin::Eff, Val::Type),
                        ReasonExpected::UsedInWith,
                        mcxt,
                    )
                })
                .collect::<Result<_, _>>()?;

            Ok((Term::Fun(Box::new(from), Box::new(to), effs), Val::Type))
        }

        Pre_::App(icit, f, x) => {
            let fspan = f.span();
            // Don't insert metas in `f` if we're passing an implicit argument
            let (f, fty) = infer(*icit == Icit::Expl, f, mcxt)?;

            infer_app(f, fty, fspan, *icit, x, mcxt)
                .map(|(term, ty)| insert_metas(insert, term, ty, pre.span(), mcxt))
        }

        Pre_::Do(v) => {
            // We store the whole block in Salsa, then query the last expression
            let mut block = mcxt.elab_block(v.clone(), false)?;

            // Now query the last expression
            let mut ret_ty = None;
            let mut state = mcxt.state();
            if let Some(&last) = block.last() {
                let (pre_id, state2) = mcxt.db.lookup_intern_def(last);
                state = state2;
                // If it's not an expression, don't return anything
                if let PreDef::Expr(_) = &**mcxt.db.lookup_intern_predef(pre_id) {
                    if let Ok(info) = mcxt.db.elaborate_def(last) {
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
                    let predef = mcxt.db.intern_predef(Arc::new(PreDefAn::from(PreDef::Expr(
                        pre.copy_span(Pre_::Unit),
                    ))));
                    let unit_def = mcxt.db.intern_def(predef, state);
                    block.push(unit_def);
                    Val::builtin(Builtin::UnitType, Val::Type)
                }
            };
            let block = block
                .into_iter()
                .filter_map(|id| Some((id, mcxt.def_term(id)?)))
                .collect();
            Ok((Term::Do(block), ret_ty))
        }

        Pre_::Sig(v) => {
            let block = mcxt.elab_block(v.clone(), true)?;
            let mut names = HashMap::new();
            let struct_block: Vec<_> = block
                .into_iter()
                .filter_map(|id| {
                    let info = mcxt.db.elaborate_def(id).ok()?;
                    let (pre, _) = mcxt.db.lookup_intern_def(id);
                    let pre = mcxt.db.lookup_intern_predef(pre);
                    let name = pre.name().unwrap();
                    let span = pre.span();
                    if let Some(&span2) = names.get(&name) {
                        mcxt.db.report_error(
                            Error::new(
                                mcxt.cxt.file(mcxt.db),
                                format!(
                                    "Duplicate name {} in structure signature",
                                    name.get(mcxt.db)
                                ),
                                span,
                                "redefined here",
                            )
                            .with_label(
                                mcxt.cxt.file(mcxt.db),
                                span2,
                                "first definition is here",
                            ),
                        );
                        return None;
                    }
                    names.insert(name, span);
                    Some((id, name, (*info.typ).clone().quote(mcxt.size, mcxt)))
                })
                .collect();
            Ok((Term::Struct(StructKind::Sig, struct_block), Val::Type))
        }
        Pre_::Struct(v) => {
            let block = mcxt.elab_block(v.clone(), false)?;
            let mut names = HashMap::new();
            let (struct_block, sig_block) = block
                .into_iter()
                .filter_map(|id| {
                    let info = mcxt.db.elaborate_def(id).ok()?;
                    let (pre, _) = mcxt.db.lookup_intern_def(id);
                    let pre = mcxt.db.lookup_intern_predef(pre);
                    let name = pre.name().unwrap();
                    let span = pre.span();
                    if let Some(&span2) = names.get(&name) {
                        mcxt.db.report_error(
                            Error::new(
                                mcxt.cxt.file(mcxt.db),
                                format!("Duplicate name {} in structure", name.get(mcxt.db)),
                                span,
                                "redefined here",
                            )
                            .with_label(
                                mcxt.cxt.file(mcxt.db),
                                span2,
                                "first definition is here",
                            ),
                        );
                        return None;
                    }
                    names.insert(name, span);
                    let ty = (*info.typ).clone().quote(mcxt.size, mcxt);
                    Some(((id, name, (*info.term?).clone()), (id, name, ty)))
                })
                .unzip();
            let ty = Term::Struct(StructKind::Sig, sig_block);
            let term = Term::Struct(StructKind::Struct(Box::new(ty.clone())), struct_block);
            let vty = ty.evaluate(&mcxt.env(), mcxt);
            Ok((term, vty))
        }
        Pre_::StructShort(_) => todo!("elaborate short-form struct"),

        Pre_::Hole(source) => {
            let ty = mcxt.new_meta(None, pre.span(), MetaSource::HoleType, Term::Type);
            let vty = ty.clone().evaluate(&mcxt.env(), mcxt);
            Ok((mcxt.new_meta(None, pre.span(), *source, ty), vty))
        }

        Pre_::Dot(head, m) => {
            match infer(false, head, mcxt)
                .map(|(x, ty)| (x.inline_top(mcxt), ty.unbox(mcxt.size, mcxt)))?
            {
                (s, Val::Struct(StructKind::Sig, v)) => match v.iter().find(|&&(_, n, _)| n == **m)
                {
                    Some((_, _, ty)) => Ok(insert_metas(
                        insert,
                        Term::Dot(Box::new(s), **m),
                        ty.clone(),
                        pre.span(),
                        mcxt,
                    )),
                    None => Err(TypeError::MemberNotFound(
                        Span(head.span().0, m.span().1),
                        ScopeType::Struct,
                        **m,
                    )),
                },
                (Term::Var(Var::Builtin(Builtin::Bool), _), _) => {
                    let tbool = Term::Var(Var::Builtin(Builtin::Bool), Box::new(Term::Type));
                    let vbool = Val::builtin(Builtin::Bool, Val::Type);
                    match &*mcxt.db.lookup_intern_name(**m) {
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
                            ScopeType::Type(mcxt.db.intern_name("Bool".into())),
                            **m,
                        )),
                    }
                }
                (Term::Var(Var::Type(id, scope), _), _) => {
                    let scope = mcxt.db.lookup_intern_scope(scope);
                    for &(n, v) in scope.iter().rev() {
                        if n == **m {
                            match mcxt.db.elaborate_def(v) {
                                Ok(info) => {
                                    let fty: Val = info.typ.into_owned();
                                    let f = Term::Var(
                                        Var::Top(v),
                                        Box::new(fty.clone().quote(mcxt.size, mcxt)),
                                    );
                                    return Ok(insert_metas(insert, f, fty, pre.span(), mcxt));
                                }
                                Err(_) => return Err(TypeError::Sentinel),
                            }
                        }
                    }
                    Err(TypeError::MemberNotFound(
                        Span(head.span().0, m.span().1),
                        ScopeType::Type(
                            mcxt.db
                                .lookup_intern_predef(mcxt.db.lookup_intern_def(id).0)
                                .name()
                                .unwrap(),
                        ),
                        **m,
                    ))
                }
                (x, Val::App(Var::Type(id, scope), b, c, d)) => {
                    let xty = Val::App(Var::Type(id, scope), b, c, d);
                    let scope = mcxt.db.lookup_intern_scope(scope);
                    for &(n, v) in scope.iter().rev() {
                        if n == **m {
                            match mcxt.db.elaborate_def(v) {
                                Ok(info) => {
                                    let fty: Val = info.typ.into_owned();
                                    let f = Term::Var(
                                        Var::Top(v),
                                        Box::new(fty.clone().quote(mcxt.size, mcxt)),
                                    );
                                    let (f, fty) = insert_metas(true, f, fty, m.span(), mcxt);
                                    match &fty {
                                        Val::Fun(from, to, effs) => {
                                            if !unify(
                                                xty.clone(),
                                                (**from).clone(),
                                                mcxt.size,
                                                pre.span(),
                                                mcxt,
                                            )? {
                                                return Err(TypeError::Unify(
                                                    head.copy_span(xty),
                                                    (**from).clone(),
                                                    ReasonExpected::ArgOf(m.span(), fty),
                                                ));
                                            }

                                            let to = (**to).clone();
                                            for eff in effs {
                                                if !mcxt
                                                    .eff_stack
                                                    .try_eff(eff.clone(), &mut mcxt.clone())
                                                {
                                                    return Err(TypeError::EffNotAllowed(
                                                        pre.span(),
                                                        eff.clone(),
                                                        mcxt.eff_stack.clone(),
                                                    ));
                                                }
                                            }
                                            return Ok((
                                                Term::App(Icit::Expl, Box::new(f), Box::new(x)),
                                                to,
                                            ));
                                        }
                                        Val::Clos(Pi, Icit::Expl, clos, effs) => {
                                            let from = clos.ty.clone();
                                            if !unify(
                                                xty.clone(),
                                                from.clone(),
                                                mcxt.size,
                                                pre.span(),
                                                mcxt,
                                            )? {
                                                return Err(TypeError::Unify(
                                                    head.copy_span(xty),
                                                    from,
                                                    ReasonExpected::ArgOf(m.span(), fty),
                                                ));
                                            }

                                            let vx = x.clone().evaluate(&mcxt.env(), mcxt);
                                            let to = clos.clone().apply(vx, mcxt);
                                            for eff in effs {
                                                if !mcxt
                                                    .eff_stack
                                                    .try_eff(eff.clone(), &mut mcxt.clone())
                                                {
                                                    return Err(TypeError::EffNotAllowed(
                                                        pre.span(),
                                                        eff.clone(),
                                                        mcxt.eff_stack.clone(),
                                                    ));
                                                }
                                            }
                                            return Ok((
                                                Term::App(Icit::Expl, Box::new(f), Box::new(x)),
                                                to,
                                            ));
                                        }
                                        _ => todo!("error for this case"),
                                    }
                                }
                                Err(_) => return Err(TypeError::Sentinel),
                            }
                        }
                    }
                    Err(TypeError::MemberNotFound(
                        Span(head.span().0, m.span().1),
                        ScopeType::Type(
                            mcxt.db
                                .lookup_intern_predef(mcxt.db.lookup_intern_def(id).0)
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
                let (x, x_ty) = infer(true, x, mcxt)?;
                let mut x_effs = mcxt.eff_stack.pop_scope();
                let before_len = x_effs.len();
                x_effs.retain(|x| !matches!(x, Val::App(Var::Builtin(Builtin::IO), _, _, _)));
                if x_effs.len() != before_len {
                    // It had IO
                    if !mcxt.eff_stack.clone().try_eff(
                        Val::builtin(Builtin::IO, Val::builtin(Builtin::Eff, Val::Type)),
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
                let (x, x_ty) = infer(true, x, mcxt)?;
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
    mcxt: &mut MCxt,
) -> Result<(Term, VTy), TypeError> {
    let fty = fty.inline(mcxt.size, mcxt);
    let (term, ty) = match &fty {
        Val::Clos(Pi, icit2, cl, effs) => {
            assert_eq!(icit, *icit2);

            let span = Span(fspan.0, x.span().1);
            let x = check(x, &cl.ty, ReasonExpected::ArgOf(fspan, fty.clone()), mcxt)?;
            // TODO Rc to get rid of the clone()?
            let to = (**cl)
                .clone()
                .apply(x.clone().evaluate(&mcxt.env(), mcxt), mcxt);
            for eff in effs {
                if !mcxt.eff_stack.try_eff(eff.clone(), &mut mcxt.clone()) {
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
            let x = check(x, from, ReasonExpected::ArgOf(fspan, fty.clone()), mcxt)?;
            let to = (**to).clone();
            for eff in effs {
                if !mcxt.eff_stack.try_eff(eff.clone(), &mut mcxt.clone()) {
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
                (icit, f.head().clone().inline_top(mcxt))
            {
                let scope = mcxt.db.lookup_intern_scope(sid);
                let m = mcxt.db.intern_name(String::new());
                for &(n, v) in scope.iter() {
                    if n == m {
                        match mcxt.db.elaborate_def(v) {
                            Ok(info) => {
                                let mut fty =
                                    IntoOwned::<Val>::into_owned(info.typ).quote(mcxt.size, mcxt);
                                let mut f2 = Term::Var(Var::Top(v), Box::new(fty.clone()));
                                let mut f = f;
                                // Apply the constructor to all the type arguments
                                while let Term::App(i, f3, x) = f {
                                    f2 = Term::App(i, Box::new(f2), x.clone());
                                    match fty {
                                        Term::Clos(Pi, _, _, _, to, _) => {
                                            // Peel off one Pi to get the type of the next `f`.
                                            // It's dependent, so we need to add `x` to the environment.
                                            let mut env = mcxt.env();
                                            let x = x.evaluate(&env, mcxt);
                                            env.push(Some(x));
                                            // Then we evaluate-quote to so `fty` is in the context `enclosing`.
                                            fty =
                                                (*to).clone().eval_quote(&mut env, mcxt.size, mcxt)
                                        }
                                        _ => unreachable!(),
                                    };
                                    f = *f3;
                                }
                                let fty = fty.evaluate(&mcxt.env(), mcxt);

                                return infer_app(f2, fty, fspan, icit, x, mcxt);
                            }
                            Err(_) => return Err(TypeError::Sentinel),
                        }
                    }
                }
            }

            if let Term::App(_, _, _) = &f {
                let hty = f.head().ty(mcxt.size, mcxt).evaluate(&mcxt.env(), mcxt);
                let exp = hty.arity(false);
                return Err(TypeError::WrongArity(
                    Spanned::new(hty, Span(fspan.0, x.span().1)),
                    exp,
                    f.spine_len() + 1,
                ));
            }
            return Err(TypeError::NotFunction(Spanned::new(fty, fspan)));
        }
    }?;
    Ok((term, ty))
}

pub fn check(
    pre: &Pre,
    ty: &VTy,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
) -> Result<Term, TypeError> {
    match (&**pre, ty) {
        (_, Val::Arc(x)) => check(pre, x, reason, mcxt),

        // When checking () against Type, we know it's refering to the unit type
        (Pre_::Unit, Val::Type) => Ok(Term::Var(
            Var::Builtin(Builtin::UnitType),
            Box::new(Term::Type),
        )),

        (Pre_::Lam(n, i, ty, body), Val::Clos(Pi, i2, cl, effs)) if i == i2 => {
            let ty2 = &cl.ty;
            let ety = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let vty = ety.clone().evaluate(&mcxt.env(), mcxt);
            if !unify(vty.clone(), ty2.clone(), mcxt.size, pre.span(), mcxt)? {
                return Err(TypeError::Unify(ty.copy_span(vty), ty2.clone(), reason));
            }
            let bty = (**cl)
                .clone()
                .apply(Val::local(mcxt.size.next_lvl(), vty.clone()), mcxt);

            mcxt.define(*n, NameInfo::Local(vty));

            // TODO not clone ??
            let (body, _bty, effs) = check_fun(body, bty, reason, effs.clone(), false, mcxt)?;

            mcxt.undef();
            let effs = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt))
                .collect();
            Ok(Term::Clos(Lam, *n, *i, Box::new(ety), Box::new(body), effs))
        }

        (Pre_::Lam(n, Icit::Expl, ty, body), Val::Fun(ty2, body_ty, effs)) => {
            let ety = check(ty, &Val::Type, ReasonExpected::UsedAsType, mcxt)?;
            let vty = ety.clone().evaluate(&mcxt.env(), mcxt);
            if !unify(vty.clone(), (**ty2).clone(), mcxt.size, pre.span(), mcxt)? {
                return Err(TypeError::Unify(ty.copy_span(vty), (**ty2).clone(), reason));
            }
            mcxt.define(*n, NameInfo::Local(vty));
            let (body, _bty, effs) =
                check_fun(body, (**body_ty).clone(), reason, effs.clone(), false, mcxt)?;
            mcxt.undef();

            let effs = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt))
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
                let mut s = cl.name.get(mcxt.db);
                s.push('\'');
                mcxt.db.intern_name(s)
            };
            let bty = (**cl).clone().vquote(mcxt.size, mcxt);
            mcxt.define(name, NameInfo::Local(cl.ty.clone()));
            let (body, _bty, effs) = check_fun(pre, bty, reason, effs.clone(), false, mcxt)?;
            mcxt.undef();

            let ty = cl.ty.clone().quote(mcxt.size, mcxt);
            let effs = effs
                .iter()
                .map(|x| x.clone().quote(mcxt.size, mcxt))
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
        (Pre_::BinOp(op, a, b), _) if op.returns_arg_ty() && ty.is_concrete() => {
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
            let a = check(a, ty, reason.clone(), mcxt)?;
            let b = check(b, ty, reason, mcxt)?;
            let fty = Term::Fun(
                Box::new(ity.clone()),
                Box::new(Term::Fun(Box::new(ity.clone()), Box::new(ity), Vec::new())),
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
            match ty.clone().inline(mcxt.size, mcxt) {
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
                    ty.inline_metas(mcxt.size, mcxt),
                    reason,
                )),
            }
        }

        (Pre_::Case(is_catch, x, cases), _) => {
            let xspan = x.span();
            let (x, x_ty, x_effs) = if *is_catch {
                mcxt.eff_stack.push_scope(true, xspan);
                let (x, x_ty) = infer(true, x, mcxt)?;
                let mut x_effs = mcxt.eff_stack.pop_scope();
                let before_len = x_effs.len();
                x_effs.retain(|x| !matches!(x, Val::App(Var::Builtin(Builtin::IO), _, _, _)));
                if x_effs.len() != before_len {
                    // It had IO
                    if !mcxt.eff_stack.clone().try_eff(
                        Val::builtin(Builtin::IO, Val::builtin(Builtin::Eff, Val::Type)),
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
                let (x, x_ty) = infer(true, x, mcxt)?;
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
            )
            .map(|(x, _)| x)
        }

        (Pre_::If(cond, yes, no), _) => {
            let cond = check(
                cond,
                &Val::builtin(Builtin::Bool, Val::Type),
                ReasonExpected::IfCond,
                mcxt,
            )?;
            let yes = check(yes, ty, reason.clone(), mcxt)?;
            let no = check(no, ty, reason, mcxt)?;
            let tty = ty.clone().quote(mcxt.size, mcxt);
            Ok(cond.make_if(yes, no, tty))
        }

        (Pre_::Struct(v), Val::Struct(StructKind::Sig, tys)) => {
            if v.len() != tys.len() {
                let err = Error::new(
                    mcxt.cxt.file(mcxt.db),
                    format!(
                        "Wrong number of structure members, got {}, expected {} because of type",
                        v.len(),
                        tys.len(),
                    ),
                    pre.span(),
                    format!("expected {} structure members here", tys.len()),
                );
                let err = reason.add(err, mcxt.cxt.file(mcxt.db), mcxt);
                mcxt.db.report_error(err);
                return Err(TypeError::Sentinel);
            }
            let mut names = HashMap::new();
            let block = mcxt.elab_block_with(
                v.iter()
                    .map(|d| {
                        let name = d.name().unwrap();
                        let span = d.span();
                        let (def2, _, ty) =
                            tys.iter().find(|&&(_, n, _)| n == name).ok_or_else(|| {
                                let err = Error::new(
                                    mcxt.cxt.file(mcxt.db),
                                    Doc::start("Could not find structure member ")
                                        .add(name.get(mcxt.db))
                                        .add(" in expected type ")
                                        .chain(ty.pretty(mcxt).style(Style::None))
                                        .style(Style::Bold),
                                    d.span(),
                                    "unrecognized member",
                                );
                                let err = reason.clone().add(err, mcxt.cxt.file(mcxt.db), mcxt);
                                mcxt.db.report_error(err);
                                TypeError::Sentinel
                            })?;
                        if let Some(&span2) = names.get(&name) {
                            mcxt.db.report_error(
                                Error::new(
                                    mcxt.cxt.file(mcxt.db),
                                    format!(
                                        "Duplicate name {} in structure signature",
                                        name.get(mcxt.db)
                                    ),
                                    span,
                                    "redefined here",
                                )
                                .with_label(
                                    mcxt.cxt.file(mcxt.db),
                                    span2,
                                    "first definition is here",
                                ),
                            );
                            return Err(TypeError::Sentinel);
                        }
                        names.insert(name, span);
                        Ok((
                            PreDef::Typed(Box::new(d.clone()), ty.clone(), reason.clone()).into(),
                            Some((*def2, ty.clone().quote(mcxt.size, mcxt))),
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                false,
            )?;
            let (struct_block, sig_block) = block
                .into_iter()
                .filter_map(|id| {
                    let info = mcxt.db.elaborate_def(id).ok()?;
                    let (pre, _) = mcxt.db.lookup_intern_def(id);
                    let name = mcxt.db.lookup_intern_predef(pre).name().unwrap();
                    let ty = (*info.typ).clone().quote(mcxt.size, mcxt);
                    Some(((id, name, (*info.term?).clone()), (id, name, ty)))
                })
                .unzip();
            let ty = Term::Struct(StructKind::Sig, sig_block);
            let term = Term::Struct(StructKind::Struct(Box::new(ty)), struct_block);
            Ok(term)
        }
        _ => {
            if let Val::App(h, _, sp, g) = ty {
                if let Some(v) = g.resolve(*h, sp, mcxt.size, mcxt) {
                    return check(pre, &v, reason, mcxt);
                }
            }

            let (term, mut i_ty) = infer(true, pre, mcxt)?;

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
                            if unify(e.clone(), i.clone(), tcxt.size, Span::empty(), &mut tcxt)
                                .unwrap_or(false)
                            {
                                found = true;
                                break;
                            }
                        }
                        if found {
                            effs3.push(e);
                        } else if !mcxt.eff_stack.clone().try_eff(e.clone(), mcxt) {
                            return Err(TypeError::EffNotAllowed(
                                pre.span(),
                                e,
                                mcxt.eff_stack.clone(),
                            ));
                        }
                    }
                    *effs2 = effs3;
                }
                (_, _) => (),
            };

            try_unify(ty, &i_ty, Some(&term), pre.span(), reason, mcxt)?;
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
    mcxt: &mut MCxt,
) -> Result<(Term, VTy, Vec<Val>), TypeError> {
    let span = reason.span_or(body.span());
    mcxt.eff_stack.push_scope(open, span);
    for e in effs {
        mcxt.eff_stack.push_eff(e.clone());
    }
    let term = check(body, &rty, reason, mcxt)?;
    let effs = mcxt.eff_stack.pop_scope();
    Ok((term, rty, effs))
}
