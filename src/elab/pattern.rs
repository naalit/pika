use super::elaborate::DepMode::*;
use super::*;

mod input {
    use crate::elab::elaborate::resolve_member;

    use super::*;

    type SPattern = Spanned<Pattern>;
    #[derive(Clone, Debug)]
    pub(super) enum Pattern {
        /// (constructor, implicit args, explicit arg, return type, size at return type)
        Cons(
            PCons,
            Vec<(SPattern, Val)>,
            Option<Box<(SPattern, Val)>>,
            Val,
            Size,
        ),
        Pair(Box<SPattern>, Box<SPattern>, Size),
        Or(Vec<SPattern>),
        Var(SName),
        Typed(Box<SPattern>, Box<Val>),
        Any,
    }
    impl Pattern {
        pub(super) fn to_term(&self, db: &(impl Elaborator + ?Sized), size: &mut Size) -> Val {
            match self {
                Pattern::Cons(cons, iargs, eargs, _, _) => {
                    let mut term = match cons {
                        PCons::Lit(l) => Val::Lit(*l),
                        PCons::Cons(cons) => {
                            Val::var(Var::Cons((db.name("_".into()), RelSpan::empty()), *cons))
                        }
                    };
                    let iarg =
                        iargs
                            .iter()
                            .map(|x| x.0 .0.to_term(db, size))
                            .rfold(None, |acc, x| match acc {
                                None => Some(x),
                                Some(y) => {
                                    Some(Val::Pair(Box::new(x), Box::new(y), Box::new(Val::Error)))
                                }
                            });
                    if let Some(iarg) = iarg {
                        term = term.app(Elim::App(Impl, iarg), &mut Env::new(*size));
                    }
                    if let Some(earg) = eargs {
                        term = term.app(
                            Elim::App(Expl, earg.0 .0.to_term(db, size)),
                            &mut Env::new(*size),
                        );
                    }
                    term
                }
                Pattern::Pair(a, b, _) => {
                    *size += 1;
                    Val::Pair(
                        Box::new(a.0.to_term(db, size)),
                        Box::new(b.0.to_term(db, size)),
                        Box::new(Val::Error),
                    )
                }
                Pattern::Or(_) => Val::Error,
                Pattern::Var(n) => {
                    *size += 1;
                    Val::var(Var::Local(*n, size.dec().next_lvl()))
                }
                Pattern::Typed(a, _) => a.0.to_term(db, size),
                Pattern::Any => Val::Error,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub(super) struct Column {
        pub var: PVar,
        pub pat: SPattern,
    }

    pub(super) enum RemovedColumn {
        Nothing,
        Pair(Box<SPattern>, Box<SPattern>, Size, RelSpan),
        // TODO is this cons necessary?
        Yes(
            PCons,
            Vec<(SPattern, Val)>,
            Option<Box<(SPattern, Val)>>,
            Option<Env>,
        ),
        No,
    }

    #[derive(Clone, Debug)]
    pub(super) struct Row {
        pub columns: VecDeque<Column>,
        pub guard: Option<ast::Expr>,
        pub end_ipats: VecDeque<(PVar, IPat)>,
        pub body: Body,
    }
    impl Row {
        pub fn new(
            var: PVar,
            pat: Option<ast::Expr>,
            span: RelSpan,
            body: Option<ast::Expr>,
            cxt: &mut CaseElabCxt,
        ) -> Row {
            let pat = pat.map_or((Pattern::Any, span), |x| {
                x.to_pattern(cxt, &mut cxt.ecxt.size())
            });
            Row {
                columns: VecDeque::from(vec![Column { var, pat }]),
                guard: None,
                end_ipats: VecDeque::new(),
                body: cxt.add_body(body),
            }
        }

        pub fn make_env(&self, cxt: &CaseElabCxt) -> PEnv {
            let mut env = Vec::new();
            for (var, pat) in &self.end_ipats {
                match pat {
                    IPat::Var(n) => {
                        let ty = cxt.var_tys[var.0].0.clone();
                        env.push((*n, ty));
                    }
                    _ => (),
                }
            }
            env
        }
    }

    impl CaseElabCxt<'_, '_> {
        pub fn remove_column(
            &mut self,
            row: &mut Row,
            var: PVar,
            ty: &Val,
            reason: &CheckReason,
            target_cons: &mut Option<PCons>,
            env: &Env,
        ) -> RemovedColumn {
            match row.columns.iter().position(|c| c.var == var) {
                Some(i) => match &row.columns[i].pat.0 {
                    Pattern::Cons(cons, _iargs, _eargs, _rty, _) => {
                        if target_cons.is_none()
                            || matches!(target_cons, Some(tcons) if tcons == cons)
                        {
                            if target_cons.is_none() {
                                *target_cons = Some(cons.clone());
                            }
                            match row.columns.remove(i).unwrap() {
                                Column {
                                    pat: (Pattern::Cons(cons, iargs, eargs, rty, rsize), span),
                                    ..
                                } => {
                                    let mut env = env.clone();
                                    env.reset_to_size(rsize);
                                    while env.size < rsize {
                                        env.push(None);
                                    }
                                    match (rty.no_deps(), ty.no_deps()) {
                                        (Val::Neutral(a), Val::Neutral(b))
                                            if a.head() == b.head() =>
                                        {
                                            self.ecxt
                                                .mcxt
                                                .local_unify(
                                                    rty,
                                                    ty.clone(),
                                                    rsize,
                                                    &mut env,
                                                    reason,
                                                    true,
                                                )
                                                .unwrap_or_else(|e| self.ecxt.error(span, e))
                                        }
                                        _ => self
                                            .ecxt
                                            .mcxt
                                            .unify(
                                                rty.clone(),
                                                ty.clone(),
                                                rsize,
                                                env.clone(),
                                                reason,
                                                true,
                                            )
                                            .unwrap_or_else(|e| self.ecxt.error(span, e)),
                                    }
                                    RemovedColumn::Yes(cons, iargs, eargs, Some(env))
                                }
                                _ => unreachable!(),
                            }
                        } else {
                            RemovedColumn::No
                        }
                    }
                    Pattern::Typed(pat, pty) => {
                        self.ecxt
                            .mcxt
                            .unify(
                                (**pty).clone(),
                                // Ignore dependencies, like with let, except that the type for the variable
                                // comes from other code so it's already correct
                                ty.no_deps().clone(),
                                env.size,
                                env.clone(),
                                reason,
                                false,
                            )
                            .unwrap_or_else(|e| self.ecxt.error(row.columns[i].pat.1, e));
                        let pat = (**pat).clone();
                        row.columns[i].pat = pat;
                        self.remove_column(row, var, ty, reason, target_cons, env)
                    }
                    Pattern::Pair(_, _, _) => match row.columns.remove(i).unwrap() {
                        Column {
                            pat: (Pattern::Pair(a, b, size), span),
                            ..
                        } => RemovedColumn::Pair(a, b, size, span),
                        _ => unreachable!(),
                    },
                    Pattern::Or(_) => {
                        unreachable!("or patterns should have been removed before remove_column()")
                    }
                    Pattern::Var(v) => {
                        // The variable can't be used in the rest of the pattern
                        // and we don't want to define "real" variables that aren't used in other patterns
                        // so we push it to the end of the row
                        row.end_ipats.push_back((var, IPat::Var(*v)));
                        row.columns.remove(i);
                        RemovedColumn::Nothing
                    }
                    Pattern::Any => {
                        row.columns.remove(i);
                        RemovedColumn::Nothing
                    }
                },
                None => RemovedColumn::Nothing,
            }
        }
    }

    impl ast::Expr {
        fn to_pattern(&self, cxt: &mut CaseElabCxt, size: &mut Size) -> SPattern {
            let pat = match self {
                // TODO datatype constructors
                ast::Expr::Var(v) => {
                    *size += 1;
                    Pattern::Var(v.name(cxt.ecxt.db))
                }
                ast::Expr::App(x) => {
                    let (mut lhs, mut lhs_ty) = x
                        .lhs()
                        .map(|x| x.infer(cxt.ecxt))
                        .unwrap_or((Expr::Error, Val::Error));
                    if let Some(member) = x.member() {
                        (lhs, lhs_ty) = resolve_member(lhs, lhs_ty, member, cxt.ecxt);
                    }
                    let cons = match lhs {
                        Expr::Head(Head::Var(Var::Cons(_, cons))) => cons,
                        Expr::Error => return (Pattern::Any, self.span()),
                        _ => {
                            cxt.ecxt.error(
                                x.lhs().unwrap().span(),
                                "Expected a constructor in pattern",
                            );
                            return (Pattern::Any, self.span());
                        }
                    };
                    let start_size = *size;
                    let implicit = if let Some(args) = x.imp() {
                        match lhs_ty {
                            Val::Fun(clos) if clos.class == Pi(Impl) => {
                                let args: Vec<_> = args
                                    .args()
                                    .into_iter()
                                    .flat_map(|x| match x.expr() {
                                        Some(x) => x.as_args(),
                                        None => vec![Err(x.span())],
                                    })
                                    .collect();
                                if args.len() > clos.params.len() {
                                    cxt.ecxt.error(
                                        x.span(),
                                        "Extra implicit arguments to constructor in pattern",
                                    );
                                }
                                let args: Vec<_> = args
                                    .into_iter()
                                    .map(Some)
                                    .chain(std::iter::repeat(None))
                                    .zip(&clos.params)
                                    .map(|(a, b)| {
                                        let mut env = Env::new(*size);
                                        match a {
                                            Some(Ok(e)) => (
                                                (e.to_pattern(cxt, size)),
                                                (b.ty.clone().eval(&mut env)),
                                            ),
                                            Some(Err(span)) => {
                                                cxt.ecxt
                                                    .unify(
                                                        Val::var(Var::Builtin(Builtin::UnitType)),
                                                        b.ty.clone().eval(&mut env),
                                                        &CheckReason::ArgOf(
                                                            x.lhs().unwrap().span(),
                                                        ),
                                                    )
                                                    .unwrap_or_else(|e| cxt.ecxt.error(span, e));
                                                (
                                                    (Pattern::Any, span),
                                                    (Val::var(Var::Builtin(Builtin::UnitType))),
                                                )
                                            }
                                            None => {
                                                *size += 1;
                                                (
                                                    (
                                                        Pattern::Var((
                                                            cxt.ecxt.db.name("_".into()),
                                                            RelSpan::empty(),
                                                        )),
                                                        RelSpan::empty(),
                                                    ),
                                                    (b.ty.clone().eval(&mut env)),
                                                )
                                            }
                                        }
                                    })
                                    .collect();
                                let mut tsize = start_size;
                                let arg = args
                                    .iter()
                                    .map(|x| x.0 .0.to_term(cxt.ecxt.db, &mut tsize))
                                    .collect::<Vec<_>>()
                                    .into_iter()
                                    .rfold(None, |acc, x| match acc {
                                        None => Some(x),
                                        Some(y) => Some(Val::Pair(
                                            Box::new(x),
                                            Box::new(y),
                                            Box::new(Val::Error),
                                        )),
                                    })
                                    .unwrap();
                                lhs_ty = clos.apply(arg);
                                args
                            }
                            Val::Error => {
                                lhs_ty = Val::Error;
                                Vec::new()
                            }
                            lty => {
                                cxt.ecxt.error(
                                    args.span(),
                                    "Extra implicit arguments to constructor in pattern",
                                );
                                lhs_ty = lty;
                                Vec::new()
                            }
                        }
                    } else {
                        match lhs_ty {
                            Val::Fun(clos) if clos.class == Pi(Impl) => {
                                let args: Vec<_> = clos
                                    .params
                                    .iter()
                                    .map(|b| {
                                        *size += 1;
                                        (
                                            (
                                                Pattern::Var((
                                                    cxt.ecxt.db.name("_".into()),
                                                    RelSpan::empty(),
                                                )),
                                                RelSpan::empty(),
                                            ),
                                            (b.ty.clone().eval(&mut Env::new(*size))),
                                        )
                                    })
                                    .collect();
                                // This is correct since they're all var patterns
                                lhs_ty = clos.open(start_size);
                                args
                            }
                            _ => Vec::new(),
                        }
                    };
                    let start_size = *size;
                    let explicit = match (x.exp(), lhs_ty) {
                        (Some(args), Val::Fun(clos)) if clos.class == Pi(Expl) => {
                            let r = Some(Box::new((args.to_pattern(cxt, size), clos.par_ty())));
                            lhs_ty = clos.apply(
                                r.as_ref()
                                    .unwrap()
                                    .0
                                     .0
                                    .to_term(cxt.ecxt.db, &mut start_size.clone()),
                            );
                            r
                        }
                        (None, Val::Fun(clos)) => {
                            cxt.ecxt.error(
                                self.span(),
                                "Expected explicit arguments to constructor in pattern",
                            );
                            let r = Some(Box::new(((Pattern::Any, self.span()), clos.par_ty())));
                            lhs_ty = clos.apply(Val::Error);
                            r
                        }
                        (Some(_), lty) => {
                            cxt.ecxt.error(
                                self.span(),
                                "Extra explicit arguments to constructor in pattern",
                            );
                            lhs_ty = lty;
                            None
                        }
                        (_, lty) => {
                            lhs_ty = lty;
                            None
                        }
                    };
                    lhs_ty = lhs_ty.quote(*size, None).eval(&mut Env::new(*size));
                    Pattern::Cons(PCons::Cons(cons), implicit, explicit, lhs_ty, *size)
                }
                ast::Expr::Lit(l) => match l.to_literal(cxt.ecxt) {
                    Ok(l) => Pattern::Cons(
                        PCons::Lit(l),
                        Vec::new(),
                        None,
                        Expr::Lit(l).ty(cxt.ecxt),
                        *size,
                    ),
                    Err(e) => {
                        // TODO do we actually want to assume Any for malformed patterns?
                        cxt.ecxt.error(self.span(), e);
                        Pattern::Any
                    }
                },
                ast::Expr::GroupedExpr(x) => {
                    return x.expr().map_or(
                        (
                            Pattern::Typed(
                                Box::new((Pattern::Any, self.span())),
                                Box::new(Val::var(Var::Builtin(Builtin::UnitType))),
                            ),
                            self.span(),
                        ),
                        |x| x.to_pattern(cxt, size),
                    )
                }
                ast::Expr::Pair(x) => {
                    let start_size = *size;
                    *size += 1;
                    let a = x
                        .lhs()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt, size));
                    // We insert an extra variable so the type can depend on the lhs even if it's not bound in the pattern
                    let b = x
                        .rhs()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt, size));
                    Pattern::Pair(Box::new(a), Box::new(b), start_size)
                }
                // TODO are any other binops valid patterns?
                ast::Expr::BinOp(x)
                    if x.op().map_or(false, |x| {
                        x.syntax()
                            .unwrap()
                            .children_with_tokens()
                            .filter_map(|x| x.as_token().cloned())
                            .any(|x| x.kind() == crate::parsing::SyntaxKind::Bar)
                    }) =>
                {
                    let old_size = *size;
                    let a = x
                        .a()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt, size));
                    let new_size = *size;
                    *size = old_size;
                    let b = x
                        .b()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt, size));
                    if *size != new_size {
                        // TODO actually check that the variables have the same names and types
                        cxt.ecxt.error(
                            x.span(),
                            "Both sides of `|` pattern must bind the same variables",
                        );
                        return a;
                    }
                    Pattern::Or(vec![a, b])
                }
                ast::Expr::Binder(x) => {
                    let pat = x
                        .pat()
                        .and_then(|x| x.expr())
                        .map(|x| x.to_pattern(cxt, size))
                        .unwrap_or((Pattern::Any, x.span()));
                    match x.ty().and_then(|x| x.expr()).map(|x| {
                        x.check(Val::Type, cxt.ecxt, &CheckReason::UsedAsType, &mut Ignore)
                    }) {
                        Some(ty) => {
                            Pattern::Typed(Box::new(pat), Box::new(ty.eval(&mut cxt.ecxt.env())))
                        }
                        None => pat.0,
                    }
                }

                ast::Expr::EffPat(_) => todo!("eff patterns"),

                _ => {
                    cxt.ecxt.error(self.span(), "Expected pattern");
                    Pattern::Any
                }
            };
            (pat, self.span())
        }
    }

    impl ast::CaseBranch {
        pub(super) fn as_row(&self) -> (Option<ast::Expr>, RelSpan, Option<ast::Expr>) {
            (
                self.pat(),
                RelSpan::new(
                    self.span().start,
                    self.body()
                        .map(|x| x.span().start)
                        .unwrap_or(self.span().end),
                ),
                self.body().and_then(|x| x.expr()),
            )
        }
    }
}

// OUTPUT

type PEnv = Vec<(SName, Val)>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct PVar(usize);

/// A syntactically-irrefutable pattern
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum IPat {
    Pair(PVar, PVar),
    Var(SName),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Body(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum PCons {
    Lit(Literal),
    Cons(Cons),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Branch<T: IsTerm> {
    cons: PCons,
    iargs: Vec<PVar>,
    eargs: Option<PVar>,
    then: Box<DecNode<T>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Dec<T: IsTerm> {
    Success(Body),
    Failure,
    Guard(T::Clos, Body, Box<DecNode<T>>),
    Switch(PVar, Vec<Branch<T>>, Option<Box<DecNode<T>>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DecNode<T: IsTerm> {
    ipats: Vec<(PVar, IPat)>,
    dec: Dec<T>,
}

struct CaseElabCxt<'a, 'b> {
    ecxt: &'a mut Cxt<'b>,
    env_tys: HashMap<Body, (PEnv, bool, Env)>,
    var_tys: Vec<(Val, CheckReason)>,
    bodies: Vec<Option<ast::Expr>>,
}

impl CaseElabCxt<'_, '_> {
    fn pvar(&mut self, ty: Val, reason: CheckReason) -> PVar {
        let l = self.var_tys.len();
        self.var_tys.push((ty, reason));
        PVar(l)
    }

    fn add_body(&mut self, body: Option<ast::Expr>) -> Body {
        let l = self.bodies.len();
        self.bodies.push(body);
        Body(l)
    }

    fn column_select_heuristic(&self, top_row: &input::Row, rows: &[input::Row]) -> PVar {
        // Find the variable used by the most rows
        // TODO only use to left-to-right if GADT constructors are involved
        return top_row.columns[0].var;
        // top_row
        //     .columns
        //     .iter()
        //     .map(|c| {
        //         (
        //             c.var,
        //             rows.iter()
        //                 .filter(|x| x.columns.iter().any(|c2| c2.var == c.var))
        //                 .count(),
        //         )
        //     })
        //     .max_by_key(|&(_, b)| b)
        //     .unwrap()
        //     .0
    }

    fn compile_rows(
        &mut self,
        mut rows: Vec<input::Row>,
        reachable: bool,
        env: &Env,
    ) -> DecNode<Expr> {
        if rows.is_empty() {
            return DecNode {
                ipats: Vec::new(),
                dec: Dec::Failure,
            };
        }

        let row = &rows[0];

        // If the first row has no patterns, it will definitely match (modulo guards)
        // other rows are unreachable here, but may be reachable through another path so we figure that out later
        if row.columns.is_empty() {
            let row = rows.remove(0);
            if reachable || !self.env_tys.contains_key(&row.body) {
                self.env_tys
                    .insert(row.body, (row.make_env(self), reachable, env.clone()));
            } else {
                return DecNode {
                    ipats: Vec::new(),
                    dec: Dec::Failure,
                };
            }

            let dec = match &row.guard {
                Some(guard) => {
                    // Add all extra rows to the guard fallback
                    let guard = guard.check(
                        Val::var(Var::Builtin(Builtin::BoolType)),
                        &mut self.ecxt,
                        &CheckReason::Condition,
                        &mut Ignore,
                    );
                    let mut size = self.ecxt.size();
                    let params = self.env_tys[&row.body]
                        .0
                        .iter()
                        .map(|(n, ty)| Par {
                            name: *n,
                            ty: {
                                let ty = ty.clone().quote(size, None);
                                size += 1;
                                ty
                            },
                        })
                        .collect();
                    Dec::Guard(
                        EClos {
                            class: Lam(Expl),
                            params,
                            body: Box::new(guard),
                        },
                        row.body,
                        Box::new(self.compile_rows(rows, reachable, env)),
                    )
                }
                None => {
                    // We still want type errors in unreachable rows!
                    let _ = self.compile_rows(rows, false, env);
                    Dec::Success(row.body)
                }
            };
            return DecNode {
                ipats: row.end_ipats.into(),
                dec,
            };
        }

        let switch_var = self.column_select_heuristic(row, &rows);
        let (sty, sreason) = self.var_tys[switch_var.0].clone();

        if rows.iter().any(|x| {
            x.columns
                .iter()
                .any(|x| x.var == switch_var && matches!(x.pat.0, input::Pattern::Or(_)))
        }) {
            rows = rows
                .into_iter()
                .flat_map(|x| {
                    match x
                        .columns
                        .iter()
                        .find(|x| x.var == switch_var)
                        .map(|x| &x.pat.0)
                    {
                        Some(input::Pattern::Or(v)) => (0..v.len())
                            .map(|i| {
                                let mut x = x.clone();
                                for c in x.columns.iter_mut() {
                                    if c.var == switch_var {
                                        match &mut c.pat.0 {
                                            input::Pattern::Or(v) => {
                                                c.pat = v.swap_remove(i);
                                                break;
                                            }
                                            _ => unreachable!(),
                                        };
                                    }
                                }
                                x
                            })
                            .collect(),
                        _ => vec![x],
                    }
                })
                .collect();
        }

        let mut yes_cons = None;
        let mut yes_env = None;
        let (mut yes, mut no): (Vec<input::Row>, Vec<input::Row>) = Default::default();
        let mut iargs = Vec::new();
        let mut eargs = None;
        let mut start_ipats = Vec::new();

        for mut row in rows.iter().cloned() {
            match self.remove_column(&mut row, switch_var, &sty, &sreason, &mut yes_cons, env) {
                input::RemovedColumn::Yes(_cons, iargs2, eargs2, env) => {
                    if iargs.is_empty() && eargs.is_none() && yes_env.is_none() {
                        iargs.extend(
                            iargs2
                                .iter()
                                .map(|(_, ty)| self.pvar(ty.clone(), sreason.clone())),
                        );
                        eargs2
                            .as_deref()
                            .map(|(_, ty)| eargs = Some(self.pvar(ty.clone(), sreason.clone())));
                        yes_env = env;
                    }
                    row.columns.extend(
                        iargs2
                            .into_iter()
                            .zip(&iargs)
                            .map(|((pat, _), &var)| input::Column { pat, var }),
                    );
                    eargs2.map(|b| {
                        row.columns.push_back(input::Column {
                            pat: b.0,
                            var: eargs.unwrap(),
                        })
                    });
                    yes.push(row);
                }
                input::RemovedColumn::Pair(a, b, size, span) => {
                    // Make sure to share the PVars for all patterns that match on the same pair
                    assert!(yes_cons.is_none());
                    if iargs.is_empty() && eargs.is_none() {
                        let (va, vb) = match &sty {
                            Val::Fun(clos) if clos.class == Sigma => {
                                assert_eq!(clos.params.len(), 1);
                                let ta = clos.par_ty();
                                let tb = clos.clone().open(size);
                                let va = self.pvar(ta, sreason.clone());
                                let vb = self.pvar(tb, sreason.clone());
                                (va, vb)
                            }
                            Val::Error => (
                                self.pvar(Val::Error, sreason.clone()),
                                self.pvar(Val::Error, sreason.clone()),
                            ),
                            ty => {
                                // TODO include reason
                                self.ecxt.error(
                                    span,
                                    TypeError::InvalidPattern(
                                        "Tuple pattern invalid for type ".to_string(),
                                        ty.clone().quote(size, Some(&self.ecxt.mcxt)),
                                    ),
                                );
                                (
                                    self.pvar(Val::Error, sreason.clone()),
                                    self.pvar(Val::Error, sreason.clone()),
                                )
                            }
                        };
                        iargs.push(va);
                        iargs.push(vb);
                        start_ipats.push((switch_var, IPat::Pair(va, vb)));
                    }
                    // the sigma closure can capture the lhs, but it might not be a source-level variable in the pattern, e.g.
                    //     let x: (a: SomeStruct, a.someType) = ...
                    //     case x of
                    //         (SomeStruct { someType }, x) => ...
                    // there `x: a.someType`, so we need to materialize `a` as a "real" var, not just a PVar
                    // we do this by adding a '_' var IPat to the pattern
                    row.end_ipats.push_back((
                        iargs[0],
                        IPat::Var((self.ecxt.db.name("_".into()), RelSpan::empty())),
                    ));
                    row.columns.push_front(input::Column {
                        var: iargs[1],
                        pat: *b,
                    });
                    row.columns.push_front(input::Column {
                        var: iargs[0],
                        pat: *a,
                    });
                    yes.push(row);
                }
                input::RemovedColumn::No => {
                    no.push(row);
                }
                input::RemovedColumn::Nothing => {
                    // No tests on the switch variable, so it goes in both cases
                    yes.push(row.clone());
                    no.push(row);
                }
            }
        }

        let yes_env = yes_env.unwrap_or_else(|| env.clone());
        let mut yes = self.compile_rows(yes, reachable, &yes_env);

        match yes_cons {
            Some(yes_cons) => {
                let no = self.compile_rows(no, reachable, env);

                DecNode {
                    ipats: start_ipats,
                    dec: Dec::Switch(
                        switch_var,
                        vec![Branch {
                            cons: yes_cons,
                            iargs,
                            eargs,
                            then: Box::new(yes),
                        }],
                        Some(Box::new(no)),
                    ),
                }
            }
            None => {
                // The variable we're matching on turned out to be irrefutable, so we'll never get to `no`
                // `no` should actually have the same contents as `yes` since everything is irrefutable for this var
                // So prepend `start_ipats` onto `yes` and return that
                start_ipats.append(&mut yes.ipats);
                yes.ipats = start_ipats;
                yes
            }
        }
    }
}

mod coverage {
    use super::*;

    /// Represents a set of values that must be covered
    #[derive(Debug, Clone)]
    enum Cov {
        Any,
        Pair(PVar, PVar),
        Cons(PCons, Vec<PVar>, Option<PVar>),
        ConsSet(Vec<(PCons, bool)>),
    }
    impl PVar {
        fn pretty_cov(self, cov: &HashMap<PVar, Cov>, cxt: &CaseElabCxt) -> Doc {
            let c = cov.get(&self).unwrap_or(&Cov::Any);
            match c {
                Cov::Any => Doc::start('_'),
                Cov::Pair(a, b) => a
                    .pretty_cov(cov, cxt)
                    .nest(crate::pretty::Prec::App)
                    .add(',', ())
                    .space()
                    .chain(b.pretty_cov(cov, cxt).nest(crate::pretty::Prec::Pair))
                    .prec(crate::pretty::Prec::Pair),
                Cov::Cons(cons, iargs, eargs) => cons
                    .pretty(cxt.ecxt.db)
                    .chain(if iargs.is_empty() {
                        Doc::none()
                    } else {
                        Doc::none()
                            .space()
                            .add('[', ())
                            .chain(Doc::intersperse(
                                iargs.iter().map(|v| {
                                    v.pretty_cov(cov, cxt).nest(crate::pretty::Prec::Atom)
                                }),
                                Doc::start(',').space(),
                            ))
                            .add(']', ())
                    })
                    .chain(eargs.map_or(Doc::none(), |v| {
                        Doc::none()
                            .space()
                            .chain(v.pretty_cov(cov, cxt).nest(crate::pretty::Prec::Atom))
                    }))
                    .prec(crate::pretty::Prec::App),
                Cov::ConsSet(no) => {
                    let mut v: Vec<_> = no
                        .iter()
                        .map(|(c, has_args)| {
                            c.pretty(cxt.ecxt.db).chain(if *has_args {
                                Doc::none().space().add('_', ())
                            } else {
                                Doc::none()
                            })
                        })
                        .collect();
                    if v.len() > 1 {
                        Doc::intersperse(v, Doc::none().space().add('|', ()).space())
                    } else {
                        v.pop().unwrap().prec(crate::pretty::Prec::App)
                    }
                }
            }
        }
    }
    impl<T: IsTerm> DecNode<T> {
        /// Returns all possible sets of values that this DecNode *doesn't* cover.
        /// This basically works by recursing through the tree until it finds a success, which
        /// returns the empty set, or a failure, which returns the "path" to the current node,
        /// which is stored in `cov`.
        fn uncovered(
            &self,
            mut cov: HashMap<PVar, Cov>,
            cxt: &CaseElabCxt,
            mut size: Size,
        ) -> Vec<HashMap<PVar, Cov>> {
            for (v, p) in &self.ipats {
                match p {
                    IPat::Pair(a, b) => match cov.insert(*v, Cov::Pair(*a, *b)) {
                        Some(Cov::Pair(x, y)) if *a == x && *b == y => (),
                        Some(c) => panic!(
                            "Conflicting Cov for {}: old {:?} and {:?}",
                            *v,
                            c,
                            Cov::Pair(*a, *b)
                        ),
                        None => (),
                    },
                    IPat::Var(_) => size += 1,
                }
            }
            match &self.dec {
                Dec::Success(_) => Vec::new(),
                Dec::Failure => {
                    vec![cov]
                }
                Dec::Guard(_, _, fallback) => fallback.uncovered(cov, cxt, size),
                Dec::Switch(v, branches, fallback) => {
                    assert!(!branches.is_empty());
                    let cons = branches[0].cons;
                    let (vty, vreason) = &cxt.var_tys[v.0];
                    let existing_cons = match cov.get(v) {
                        Some(Cov::Cons(cons, _, _)) => Some(vec![*cons]),
                        Some(Cov::ConsSet(no)) => Some(no.iter().map(|(c, _)| *c).collect()),
                        _ => None,
                    };
                    match cons {
                        PCons::Lit(_) => fallback
                            .as_ref()
                            .map(|x| x.uncovered(cov.clone(), cxt, size))
                            .unwrap_or_else(|| vec![cov]),
                        PCons::Cons(cons) => {
                            let (def, _) = cxt.ecxt.db.lookup_cons_id(cons);
                            let all_ctors: Vec<_> = match cxt
                                .ecxt
                                .db
                                .def_elab(def)
                                .and_then(|d| d.result)
                                .map(|d| d.body)
                            {
                                Some(DefBody::Type(ctors)) => ctors
                                    .into_iter()
                                    .filter_map(|(s, _, ty)| {
                                        let mut size = size;
                                        let (rty, has_args) = match ty {
                                            Val::Fun(x) if matches!(x.class, Pi(_)) => {
                                                let class = x.class;
                                                let new_size = size + x.params.len();
                                                let rty = x.open(size);
                                                size = new_size;
                                                match rty {
                                                    Val::Fun(e) if e.class == Pi(Expl) => {
                                                        size += e.params.len();
                                                        (e.open(new_size), true)
                                                    }
                                                    rty => (rty, class == Pi(Expl)),
                                                }
                                            }
                                            ty => (ty, false),
                                        };
                                        if cxt
                                            .ecxt
                                            .mcxt
                                            .clone()
                                            .local_unify(
                                                rty,
                                                vty.clone(),
                                                size,
                                                &mut Env::new(size),
                                                vreason,
                                                true,
                                            )
                                            .is_err()
                                        {
                                            return None;
                                        }
                                        Some((
                                            PCons::Cons(cxt.ecxt.db.cons_id(def, s)),
                                            // Whether it has an explicit argument (show `Some _` or `None`)
                                            has_args,
                                        ))
                                    })
                                    .collect(),
                                // Should be caught already
                                _ => Vec::new(),
                            };
                            let mut cases = Vec::new();
                            let mut no = Vec::new();
                            // Go through all possible constructors, and for each one add uncovered values
                            // from either the corresponding branch or the fallback if no branch exists
                            for (cons, has_args) in all_ctors {
                                if let Some(existing_cons) = &existing_cons {
                                    if !existing_cons.contains(&cons) {
                                        continue;
                                    }
                                }
                                if let Some(branch) =
                                    branches.iter().find(|branch| branch.cons == cons)
                                {
                                    let mut cov = cov.clone();
                                    cov.insert(
                                        *v,
                                        Cov::Cons(branch.cons, branch.iargs.clone(), branch.eargs),
                                    );
                                    cases.extend(branch.then.uncovered(
                                        cov,
                                        cxt,
                                        size + branch.iargs.len() + branch.eargs.is_some() as _,
                                    ));
                                } else {
                                    no.push((cons, has_args));
                                }
                            }
                            // However, we only process the fallback once, using Cov::ConsSet which
                            // represents a union of several constructors
                            if !no.is_empty() {
                                if let Some(fallback) = fallback {
                                    let mut cov = cov.clone();
                                    cov.insert(*v, Cov::ConsSet(no));
                                    cases.extend(fallback.uncovered(cov, cxt, size));
                                }
                            }
                            cases
                        }
                    }
                }
            }
        }

        pub fn missing_patterns(&self, svar: PVar, cxt: &CaseElabCxt) -> Vec<Doc> {
            self.uncovered(HashMap::new(), &cxt, cxt.ecxt.size())
                .into_iter()
                .map(|cov| svar.pretty_cov(&cov, &cxt).nest(crate::pretty::Prec::App))
                .collect()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CaseOf<T: IsTerm> {
    svar: PVar,
    dec: DecNode<T>,
    rhs: Vec<T::Clos>,
}
impl CaseOf<Expr> {
    pub(super) fn make_simple_args(body: EClos) -> CaseOf<Expr> {
        let mut var_num = 0;
        let mut pvar = || {
            var_num += 1;
            PVar(var_num)
        };
        let (mut ipats, vrest) = body.params.iter().take(body.params.len() - 1).fold(
            (Vec::new(), PVar(0)),
            |(mut vec, var), Par { name, .. }| {
                let va = pvar();
                let vb = pvar();
                vec.push((var, IPat::Pair(va, vb)));
                vec.push((va, IPat::Var(*name)));
                (vec, vb)
            },
        );
        if let Some(Par { name, .. }) = body.params.last() {
            ipats.push((vrest, IPat::Var(*name)));
        }

        CaseOf {
            svar: PVar(0),
            dec: DecNode {
                ipats,
                dec: Dec::Success(Body(0)),
            },
            rhs: vec![body],
        }
    }
}

pub(super) fn elab_case(
    sty: Val,
    s_span: RelSpan,
    sreason: CheckReason,
    branches: impl IntoIterator<Item = (Option<ast::Expr>, RelSpan, Option<ast::Expr>)>,
    rty: &mut Option<(Val, CheckReason)>,
    ecxt: &mut Cxt,
) -> (CaseOf<Expr>, Expr) {
    let mut cxt = CaseElabCxt {
        ecxt,
        env_tys: HashMap::new(),
        var_tys: Vec::new(),
        bodies: Vec::new(),
    };
    let outer_size = cxt.ecxt.size();
    let svar = cxt.pvar(sty, sreason);
    let rows = branches
        .into_iter()
        .map(|(pat, span, body)| input::Row::new(svar, pat, span, body, &mut cxt))
        .collect();
    let dec = cxt.compile_rows(rows, true, &cxt.ecxt.env());
    let mut rhs = Vec::new();
    for (i, body) in cxt.bodies.iter().enumerate() {
        match cxt.env_tys.get(&Body(i)) {
            Some((penv, reachable, env)) => {
                if !reachable {
                    // If there's no body we have a bigger problem
                    if let Some(span) = body.as_ref().map(|x| x.span()) {
                        cxt.ecxt.warning(span, "Unreachable case branch");
                    }
                }
                let old_env = cxt.ecxt.env();
                cxt.ecxt.push();
                let mut params = Vec::new();
                for (name, ty) in penv {
                    params.push(Par {
                        name: *name,
                        ty: ty.clone().quote(cxt.ecxt.size(), None),
                    });
                    cxt.ecxt.define_local(*name, ty.clone(), None);
                }
                let mut env = env.clone();
                while env.size < cxt.ecxt.size() {
                    env.push(None);
                }
                cxt.ecxt.set_env(env);
                let body = match rty {
                    Some((rty, reason)) => body
                        .as_ref()
                        // TODO propagate DepMode?
                        .map_or(Expr::Error, |x| {
                            x.check(rty.clone(), cxt.ecxt, reason, &mut Exact)
                        }),
                    None => match body {
                        Some(body) => {
                            let (expr, ty) = body.infer(cxt.ecxt);
                            let ty = ty
                                .quote(cxt.ecxt.size(), Some(&cxt.ecxt.mcxt))
                                .eval(&mut cxt.ecxt.env());
                            let ty = if let Err(n) = ty.check_scope(outer_size) {
                                // TODO make an actual type error so more info can be included in different parts
                                cxt.ecxt.error(body.span(), Doc::start("Type of case branch result contains variable ")
                                    .add(cxt.ecxt.db.lookup_name(n), Doc::COLOR1)
                                    .add(", which isn't allowed to escape the case branch where it was bound", ()));
                                Val::Error
                            } else {
                                ty
                            };
                            *rty = Some((ty, CheckReason::MustMatch(body.span())));
                            expr
                        }
                        None => Expr::Error,
                    },
                };
                cxt.ecxt.pop();
                cxt.ecxt.set_env(old_env);
                rhs.push(EClos {
                    class: Lam(Expl),
                    params,
                    body: Box::new(body),
                });
            }
            None => panic!("env_tys has no entry for body {}", i),
        }
    }
    let missing = dec.missing_patterns(svar, &cxt);
    if !missing.is_empty() {
        cxt.ecxt.error(
            s_span,
            Doc::start("Missing patterns:")
                .space()
                .chain(Doc::intersperse(
                    missing,
                    Doc::none().space().add('|', ()).space(),
                )),
        );
    }
    (
        CaseOf { dec, svar, rhs },
        rty.as_ref()
            .map(|x| x.0.clone().quote(ecxt.size(), None))
            .unwrap_or(Expr::Error),
    )
}

impl ast::Case {
    pub(super) fn elaborate(
        &self,
        rty: &mut Option<(Val, CheckReason)>,
        ecxt: &mut Cxt,
    ) -> (Expr, CaseOf<Expr>, Expr) {
        let (scrutinee, sty) = self
            .scrutinee()
            .map(|x| x.infer(ecxt))
            .unwrap_or((Expr::Error, Val::Error));
        let (case_of, ty) = elab_case(
            sty,
            self.scrutinee().map_or_else(|| self.span(), |s| s.span()),
            CheckReason::MustMatch(self.scrutinee().map(|x| x.span()).unwrap_or(self.span())),
            self.branches().into_iter().map(|x| x.as_row()),
            rty,
            ecxt,
        );
        (scrutinee, case_of, ty)
    }
}

/// Desugars a `do` block to `case`, literally manufacturing a hierarchical AST and passing it to elab_case
/// ```pika
/// do
///   let (x, y) = something ()
///   do_stuff ()
///   x + y
/// -->
/// case something () of
///   (x, y) => case do_stuff () of
///      _ => x + y
/// ```
fn elab_block(
    block: &[ast::Stmt],
    span: RelSpan,
    rty: &mut Option<(Val, CheckReason)>,
    ecxt: &mut Cxt,
) -> Expr {
    if block.is_empty() {
        match rty {
            Some((rty, reason)) => {
                if let Err(e) = ecxt.unify(
                    Val::var(Var::Builtin(Builtin::UnitType)),
                    rty.clone(),
                    reason,
                ) {
                    ecxt.error(span, e);
                }
            }
            None => {
                *rty = Some((
                    Val::var(Var::Builtin(Builtin::UnitType)),
                    CheckReason::MustMatch(span),
                ));
            }
        }
        return Expr::var(Var::Builtin(Builtin::Unit));
    }

    let rest = if block.len() > 1 {
        Some(ast::Expr::Do(ast::Do::Val {
            span: RelSpan::new(block[1].span().start, block.last().unwrap().span().end),
            block: block[1..].to_vec(),
        }))
    } else {
        Some(ast::Expr::Do(ast::Do::Val {
            span: block[0].span(),
            block: Vec::new(),
        }))
    };

    match &block[0] {
        ast::Stmt::Expr(e) if block.len() == 1 => match rty {
            // TODO propagate DepMode?
            Some((rty, reason)) => e.check(rty.clone(), ecxt, reason, &mut Exact),
            None => {
                let (expr, ty) = e.infer(ecxt);
                *rty = Some((ty, CheckReason::MustMatch(e.span())));
                expr
            }
        },
        ast::Stmt::Expr(e) => {
            let (s, sty) = e.infer(ecxt);
            let (case, cty) = elab_case(
                sty,
                e.span(),
                CheckReason::MustMatch(e.span()),
                std::iter::once((None, e.span(), rest)),
                rty,
                ecxt,
            );
            Expr::Elim(Box::new(s), Box::new(Elim::Case(case, cty)))
        }
        ast::Stmt::Def(d) => match d {
            // only let is different in blocks
            ast::Def::LetDef(d) => {
                // TODO better way of getting type from pattern here
                let ty = match d.pat().and_then(|x| x.expr()).and_then(|x| match x {
                    ast::Expr::GroupedExpr(x) => x.expr(),
                    x => Some(x),
                }) {
                    Some(ast::Expr::Binder(x)) => x
                        .ty()
                        .and_then(|x| x.expr())
                        .map(|x| (x.span(), x))
                        .map(|(s, x)| {
                            (
                                x.check(Val::Type, ecxt, &CheckReason::UsedAsType, &mut Ignore),
                                s,
                            )
                        })
                        .map(|(x, s)| (x.eval(&mut ecxt.env()), s)),
                    _ => None,
                };
                let (body, ty, reason) = match ty {
                    Some((ty, span)) => match d.body().and_then(|x| x.expr()) {
                        Some(body) => {
                            let mut deps = Vec::new();
                            let body = body.check(
                                ty.clone(),
                                ecxt,
                                &CheckReason::GivenType(span),
                                &mut Forward(&mut deps),
                            );
                            // Add dependencies implicitly
                            let ty = if deps.is_empty() {
                                ty
                            } else {
                                Val::Dep(deps, Box::new(ty))
                            };
                            (body, ty, CheckReason::GivenType(span))
                        }
                        None => (Expr::Error, ty, CheckReason::GivenType(span)),
                    },
                    None => {
                        let (term, ty) = d
                            .body()
                            .and_then(|x| x.expr())
                            .map(|x| x.infer(ecxt))
                            .unwrap_or((Expr::Error, Val::Error));
                        (
                            term,
                            ty,
                            CheckReason::MustMatch(d.body().map(|x| x.span()).unwrap_or(d.span())),
                        )
                    }
                };
                let (case, cty) = elab_case(
                    ty,
                    d.pat().map_or_else(|| d.span(), |s| s.span()),
                    reason,
                    std::iter::once((d.pat().and_then(|x| x.expr()), d.span(), rest)),
                    rty,
                    ecxt,
                );
                Expr::Elim(Box::new(body), Box::new(Elim::Case(case, cty)))
            }
            _ => todo!("add child defs"),
        },
    }
}

impl ast::Do {
    pub(super) fn elaborate(&self, rty: &mut Option<(Val, CheckReason)>, ecxt: &mut Cxt) -> Expr {
        elab_block(&self.block(), self.span(), rty, ecxt)
    }
}

impl Dec<Val> {
    fn try_eval(
        &self,
        env: &mut HashMap<PVar, &Val>,
        params: &mut Vec<Option<Val>>,
    ) -> Option<Body> {
        match self {
            Dec::Success(b) => Some(*b),
            Dec::Failure => None,
            // TODO evaluate guards?
            Dec::Guard(_, _, _) => None,
            // TODO constructors
            Dec::Switch(_, _, _) => None,
        }
    }
}
impl DecNode<Val> {
    fn try_eval(
        &self,
        env: &mut HashMap<PVar, &Val>,
        params: &mut Vec<Option<Val>>,
    ) -> Option<Body> {
        for (var, pat) in &self.ipats {
            match pat {
                IPat::Pair(a, b) => match env.get(var) {
                    Some(Val::Pair(va, vb, _)) => {
                        env.insert(*a, va);
                        env.insert(*b, vb);
                    }
                    // Leave a and b unset, the body we pick might not use them
                    _ => (),
                },
                IPat::Var(_) => params.push(env.get(var).copied().cloned()),
            }
        }
        self.dec.try_eval(env, params)
    }
}
impl CaseOf<Val> {
    pub fn try_eval(&self, x: &Val) -> Option<Val> {
        let mut env = HashMap::new();
        env.insert(self.svar, x);
        let mut params = Vec::new();
        let body = self.dec.try_eval(&mut env, &mut params)?;
        let val = self.rhs[body.0].clone().apply_exact(params);
        if val.check_scope(self.rhs[body.0].env.size).is_ok() {
            Some(val)
        } else {
            None
        }
    }
}

impl std::fmt::Display for PVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}
impl IPat {
    pub(super) fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        match self {
            IPat::Pair(a, b) => Doc::start(a).add(',', ()).add(b, ()),
            IPat::Var(v) => v.pretty(db),
        }
    }
}
impl PCons {
    pub(super) fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        match self {
            PCons::Lit(l) => l.pretty(db),
            PCons::Cons(c) => match db.lookup_cons_id(*c) {
                (def, SplitId::Named(n)) => db
                    .def_name(def)
                    .map(|x| x.pretty(db).add('.', ()))
                    .unwrap_or(Doc::none())
                    .chain(n.pretty(db)),
                _ => Doc::start("{constructor}"),
            },
        }
    }
}
impl DecNode<Expr> {
    pub(super) fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        let mut doc = Doc::none();
        for (v, pat) in &self.ipats {
            doc = doc
                .add("let#", Doc::style_keyword())
                .space()
                .chain(pat.pretty(db))
                .space()
                .add('=', ())
                .space()
                .add(v, ())
                .hardline();
        }
        doc.chain(match &self.dec {
            Dec::Success(b) => Doc::none()
                .add("goto#", Doc::style_keyword())
                .space()
                .add(b.0, ()),
            Dec::Failure => Doc::none().add("fail#", Doc::style_keyword()),
            Dec::Guard(cond, yes, no) => Doc::none()
                .add("if", Doc::style_keyword())
                .space()
                .chain(cond.pretty(db))
                .space()
                .add("then", Doc::style_keyword())
                .space()
                .add("goto#", Doc::style_keyword())
                .space()
                .add(yes.0, ())
                .space()
                .add("else", Doc::style_keyword())
                .hardline()
                .chain(no.pretty(db))
                .indent(),
            Dec::Switch(v, branches, fallback) => Doc::none()
                .add("switch#", Doc::style_keyword())
                .space()
                .add(v, ())
                .space()
                .add("of", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    branches.iter().map(|x| {
                        x.cons
                            .pretty(db)
                            .space()
                            .add('[', ())
                            .chain(Doc::intersperse(
                                x.iargs.iter().map(|x| Doc::start(x)),
                                Doc::none().space(),
                            ))
                            .add(']', ())
                            .space()
                            .chain(x.eargs.map_or(Doc::none(), |x| Doc::start(x).space()))
                            .add("=>", ())
                            .space()
                            .chain(x.then.pretty(db).indent())
                    }),
                    Doc::none().hardline(),
                ))
                .chain(fallback.as_ref().map_or(Doc::none(), |x| {
                    Doc::none()
                        .hardline()
                        .add("_ => ", ())
                        .chain(x.pretty(db).indent())
                }))
                .indent(),
        })
    }
}
impl CaseOf<Expr> {
    pub(super) fn pretty<T: Elaborator + ?Sized>(&self, scrut: Doc, db: &T) -> Doc {
        Doc::none()
            .add("case", Doc::style_keyword())
            .hardline()
            .add("let#", Doc::style_keyword())
            .space()
            .add(self.svar, ())
            .space()
            .add('=', ())
            .space()
            .chain(scrut)
            .hardline()
            .chain(self.dec.pretty(db))
            .hardline()
            .add("where#", Doc::style_keyword())
            .chain(
                Doc::none()
                    .hardline()
                    .chain(Doc::intersperse(
                        self.rhs
                            .iter()
                            .enumerate()
                            .map(|(i, x)| Doc::start(i).add(" = ", ()).chain(x.pretty(db))),
                        Doc::none().hardline(),
                    ))
                    .indent(),
            )
            .indent()
    }
}

impl<T: IsTerm> Dec<T> {
    fn visit_mut<'a>(&'a mut self, func: &mut impl FnMut(&'a mut T::Clos)) {
        match self {
            Dec::Success(_) => (),
            Dec::Failure => (),
            Dec::Guard(guard, _, rest) => {
                func(guard);
                rest.dec.visit_mut(func);
            }
            Dec::Switch(_, branches, rest) => {
                for i in branches {
                    i.then.dec.visit_mut(func);
                }
                if let Some(rest) = rest {
                    rest.dec.visit_mut(func);
                }
            }
        }
    }
    fn visit<'a>(&'a self, func: &mut impl FnMut(&'a T::Clos)) {
        match self {
            Dec::Success(_) => (),
            Dec::Failure => (),
            Dec::Guard(guard, _, rest) => {
                func(guard);
                rest.dec.visit(func);
            }
            Dec::Switch(_, branches, rest) => {
                for i in branches {
                    i.then.dec.visit(func);
                }
                if let Some(rest) = rest {
                    rest.dec.visit(func);
                }
            }
        }
    }
}
impl<T: IsTerm> CaseOf<T> {
    pub fn visit_mut<'a>(&'a mut self, mut func: impl FnMut(&'a mut T::Clos)) {
        for i in &mut self.rhs {
            func(i);
        }
        self.dec.dec.visit_mut(&mut func);
    }
    pub fn visit<'a>(&'a self, mut func: impl FnMut(&'a T::Clos)) {
        // pub fn visit(&mut self, mut func: impl FnMut(&T::Clos)) {
        for i in &self.rhs {
            func(i);
        }
        self.dec.dec.visit(&mut func);
    }
}

impl<T: IsTerm> Dec<T> {
    fn map<U: IsTerm>(self, func: &mut impl FnMut(T::Clos) -> U::Clos) -> Dec<U> {
        match self {
            Dec::Success(b) => Dec::Success(b),
            Dec::Failure => Dec::Failure,
            Dec::Guard(x, b, rest) => Dec::Guard(func(x), b, Box::new(rest.map(func))),
            Dec::Switch(v, branches, rest) => Dec::Switch(
                v,
                branches.into_iter().map(|x| x.map(func)).collect(),
                rest.map(|x| Box::new(x.map(func))),
            ),
        }
    }
}
impl<T: IsTerm> DecNode<T> {
    fn map<U: IsTerm>(self, func: &mut impl FnMut(T::Clos) -> U::Clos) -> DecNode<U> {
        let DecNode { ipats, dec } = self;
        DecNode {
            ipats,
            dec: dec.map(func),
        }
    }
}
impl<T: IsTerm> Branch<T> {
    fn map<U: IsTerm>(self, func: &mut impl FnMut(T::Clos) -> U::Clos) -> Branch<U> {
        let Branch {
            cons,
            iargs,
            eargs,
            then,
        } = self;
        Branch {
            cons,
            iargs,
            eargs,
            then: Box::new(then.map(func)),
        }
    }
}
impl<T: IsTerm> CaseOf<T> {
    pub fn map<U: IsTerm>(self, mut func: impl FnMut(T::Clos) -> U::Clos) -> CaseOf<U> {
        let CaseOf { svar, dec, rhs } = self;
        CaseOf {
            svar,
            dec: dec.map(&mut func),
            rhs: rhs.into_iter().map(|x| func(x)).collect(),
        }
    }
}
