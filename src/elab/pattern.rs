// case f x of
//   One (12, b) => b + 2
//   One (a, b) => a * b
//   Two q => q
// -->
// let! _s = f x in
// case!
//   One (12, b) <- _s => b + 2
//   One (a, b) <- _s => a * b
//   Two q => q
// -->
// let# _s = f x in
// case# _s of
//   One _a => case!
//     (12, b) <- _a => b + 2
//     (a, b) <- _a => a * b
//   _ => case!
//     Two _a <- _s; q <- _a => q
// -->
// let# _s = f x in
// case# _s of
//   One _a => let! (_b, _c) = _a in
//             case!
//               12 <- _b; b <- _c => b + 2
//               a <- _b; b <- _c => a * b
//   _ => case!
//     Two _a <- _s; q <- _a => q
// -->
// let# _s = f x in
// case# _s of
//   One _a => let! (_b, _c) = _a in
//             case!
//               12 <- _b => let b = _c in b + 2
//               _ => let a = _b; b = _c in a * b
//   _ => case!
//     Two _a <- _s => let q = _a in q
// -->
// let# _s = f x in
// case# _s of
//   One _a => let# (_b, _c) = _a in
//             case# _b of
//               12 => let# b = _c in ret# b + 2
//               _ => let# a = _b; b = _c in ret# a * b
//   _ => case# _s of
//     Two _a => let# q = _a in ret# q
// -->
// let# _s = f x in
// case# _s of
//   One _a => let# (_b, _c) = _a in
//             case# _b of
//               12 => let# b = _c in ret# b + 2
//               _  => let# a = _b; b = _c in ret# a * b
//   Two _a => let# q = _a in ret# q
//
// but `let# a = _b` doesn't exist after elaboration, we just add a binding `a = Var::Local(_b.lvl)` or something
// whereas `let# (_b, _c) = _a` does need to persist in the elaboration output

// case x of
//   NoArgs, HasArgs a => a
//   HasArgs a, HasArgs b => a + b
//   q => 84
// -->
// let! _s = x in
// case!
//   (NoArgs, HasArgs a) <- _s => a
//   (HasArgs a, HasArgs b) <- _s => a + b
//   q <- _s => 84
// -->
// let! _s = x; (_a, _b) = _s in
// case!
//   NoArgs <- _a; HasArgs _d <- _b => let a = _d in a
//   HasArgs _c <- _a; HasArgs _d <- _b => let a = _c; b = _d in a + b
//   _ => let q = _s in 84
// -->
// // Doing _b first makes sense, but would mess up var levels
// // What if we have a special variable representation for this process that's translated to De Bruijn at the end?
// // so

// case x of
//   NoArgs, HasArgs a => a
//   HasArgs a, HasArgs b => a + b
//   q => 84
// -->
// let! %0 = x in
// case!
//   (NoArgs, HasArgs a) <- %0 => a
//   (HasArgs a, HasArgs b) <- %0 => a + b
//   q <- %0 => 84
// -->
// let! %0 = x; (%1, %2) = %0 in
// case!
//   NoArgs <- %1; HasArgs %3 <- %2 => let a = %3 in a
//   HasArgs %4 <- %1; HasArgs %5 <- %2 => let a = %4; b = %5 in a + b
//   _ => let q = %0 in 84
// -->
// let# %0 = x; (%1, %2) = %0 in
// case# %2 of
//   HasArgs %3 => case!
//     NoArgs <- %1 => let a = %3 in a
//     HasArgs %4 <- %1 => let a = %4; b = %3 in a + b // %5 merged with %3
//   _ => let q = %0 in ret# 84
// -->
// let# %0 = x; (%1, %2) = %0 in
// case# %2 of
//   HasArgs %3 => case# %1 of
//     NoArgs => let# a = %3 in ret# a
//     _ => case!
//       HasArgs %4 <- %1 => let! a = %4; b = %3 in a + b
//   _ => let# q = %0 in ret# 84
// -->
// let# %0 = x; (%1, %2) = %0 in
// case# %2 of
//   HasArgs %3 => case# %1 of
//     NoArgs => let# a = %3 in ret# a
//     _ => case# %1 of
//       HasArgs %4 => let# a = %4; b = %3 in ret# a + b
//   _ => let# q = %0 in ret# 84

// That's actually fine as a final representation - the only variables that are actually
//   added to the local context are ones in the source pattern.
// I'll say that _ should probably be turned into a name pattern rather than an Any, so it can be used implicitly
//   (e.g. existential types).
// But because a decision tree is self-contained, the variables inside it don't need to have any special properties.
// However, this might make it harder to use IPat in other contexts.
// Actually, not really, we just store Vec<IPat> and run the whole thing in order (in some sort of container of course).
// Or unify decision trees for case and patterns in pi/lam/sigma.

use super::*;

// INPUT

mod input {
    use super::*;

    type SPattern = Spanned<Pattern>;
    #[derive(Clone)]
    pub(super) enum Pattern {
        Cons(Cons, Vec<SPattern>),
        Pair(Box<SPattern>, Box<SPattern>),
        Or(Vec<SPattern>),
        Var(Name),
        Any,
    }

    #[derive(Clone)]
    pub(super) struct Column {
        pub var: PVar,
        pub pat: SPattern,
    }

    pub(super) enum RemovedColumn {
        Nothing,
        IPat(IPat),
        // TODO is this cons necessary?
        Yes(Cons, Vec<SPattern>),
        No,
    }

    #[derive(Clone)]
    pub(super) struct Row {
        pub columns: VecDeque<Column>,
        pub guard: Option<ast::Expr>,
        pub tyvars_size: Size,
        pub ty_ipats: Vec<(PVar, IPat)>,
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
            let pat = pat.map_or((Pattern::Any, span), |x| x.to_pattern(cxt));
            Row {
                columns: VecDeque::from(vec![Column { var, pat }]),
                guard: None,
                tyvars_size: cxt.ecxt.size(),
                ty_ipats: Vec::new(),
                end_ipats: VecDeque::new(),
                body: cxt.add_body(body),
            }
        }

        pub fn make_env(&self, cxt: &CaseElabCxt) -> PEnv {
            let mut env = Vec::new();
            for (var, pat) in self.ty_ipats.iter().chain(&self.end_ipats) {
                match pat {
                    IPat::Var(n) => {
                        let ty = cxt.var_tys[var.0].clone();
                        env.push((*n, ty));
                    }
                    _ => (),
                }
            }
            env
        }

        pub fn ipats(&self) -> Vec<(PVar, IPat)> {
            let mut vec = self.ty_ipats.clone();
            vec.extend(self.end_ipats.iter().cloned());
            vec
        }
    }

    impl CaseElabCxt<'_, '_> {
        pub fn remove_column(
            &mut self,
            row: &mut Row,
            var: PVar,
            ty: &Val,
            target_cons: &mut Option<Cons>,
        ) -> RemovedColumn {
            match row.columns.iter().position(|c| c.var == var) {
                Some(i) => match &row.columns[i].pat.0 {
                    Pattern::Cons(cons, _args) => match target_cons {
                        Some(tcons) => {
                            if tcons == cons {
                                match row.columns.remove(i).unwrap() {
                                    Column {
                                        pat: (Pattern::Cons(cons, args), _),
                                        ..
                                    } => RemovedColumn::Yes(cons, args),
                                    _ => unreachable!(),
                                }
                            } else {
                                RemovedColumn::No
                            }
                        }
                        None => {
                            *target_cons = Some(cons.clone());
                            match row.columns.remove(i).unwrap() {
                                Column {
                                    pat: (Pattern::Cons(cons, args), _),
                                    ..
                                } => RemovedColumn::Yes(cons, args),
                                _ => unreachable!(),
                            }
                        }
                    },
                    Pattern::Pair(_, _) => {
                        let (a, b, span) = match row.columns.remove(i).unwrap() {
                            Column {
                                pat: (Pattern::Pair(a, b), span),
                                ..
                            } => (*a, *b, span),
                            _ => unreachable!(),
                        };
                        let (va, vb) = match ty {
                            Val::Fun(clos) if clos.class == Sigma => {
                                // the sigma closure can capture the lhs, but it might not be a source-level variable in the pattern, e.g.
                                //     let x: (a: SomeStruct, a.someType) = ...
                                //     case x of
                                //         (SomeStruct { someType }, x) => ...
                                // there `x: a.someType`, so we need to materialize `a` as a "real" var, not just a PVar
                                // we do this by adding an IPat with the name from the sigma (`a` in this case) to the pattern
                                // however, these must go in order but before any other variables (since the types of those variables
                                // can depend on the values of earlier ones.) Hence `row.ty_ipats`.
                                assert_eq!(clos.params.len(), 1);
                                let ta = clos.par_ty();
                                let tb = clos.clone().open(row.tyvars_size);
                                let va = self.pvar(ta);
                                let vb = self.pvar(tb);
                                row.tyvars_size += clos.params.len();
                                row.ty_ipats.push((va, IPat::Var(clos.params[0].name)));
                                (va, vb)
                            }
                            Val::Error => (self.pvar(Val::Error), self.pvar(Val::Error)),
                            ty => {
                                self.ecxt.error(
                                    span,
                                    TypeError::InvalidPattern(
                                        "Tuple pattern invalid for type ".to_string(),
                                        ty.clone().quote(row.tyvars_size, Some(&self.ecxt.mcxt)),
                                    ),
                                );
                                (self.pvar(Val::Error), self.pvar(Val::Error))
                            }
                        };
                        row.columns.push_front(Column { var: vb, pat: b });
                        row.columns.push_front(Column { var: va, pat: a });
                        RemovedColumn::IPat(IPat::Pair(va, vb))
                    }
                    Pattern::Or(_) => {
                        unreachable!("or patterns should have been removed before remove_column()")
                    }
                    Pattern::Var(v) => {
                        // The variable can't be used in the rest of the pattern
                        // and we don't want to define "real" variables that aren't used in other patterns
                        // so we push it to the end of the row
                        row.end_ipats.push_front((var, IPat::Var(*v)));
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
        fn to_pattern(&self, cxt: &mut CaseElabCxt) -> SPattern {
            let pat = match self {
                // TODO type constructors
                ast::Expr::Var(v) => Pattern::Var(v.name(cxt.ecxt.db)),
                ast::Expr::App(_) => todo!(),
                // Manufacture a name instead of Pattern::Any, so type inference can use the value
                ast::Expr::Hole(_) => Pattern::Var(cxt.ecxt.db.name("_".to_string())),
                ast::Expr::Lit(l) => match l.to_literal(cxt.ecxt) {
                    Ok(l) => Pattern::Cons(Cons::Lit(l), Vec::new()),
                    Err(e) => {
                        // TODO do we actually want to assume Any for malformed patterns?
                        cxt.ecxt.error(self.span(), TypeError::Other(e));
                        Pattern::Any
                    }
                },
                // TODO verify that this actually has type ()
                ast::Expr::GroupedExpr(x) => {
                    return x
                        .expr()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt))
                }
                ast::Expr::Pair(x) => {
                    let a = x
                        .lhs()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt));
                    let b = x
                        .rhs()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt));
                    Pattern::Pair(Box::new(a), Box::new(b))
                }
                // TODO are any other binops valid patterns?
                ast::Expr::BinOp(x)
                    if x.op().map_or(false, |x| {
                        x.syntax()
                            .children_with_tokens()
                            .filter_map(|x| x.as_token().cloned())
                            .any(|x| x.kind() == crate::parsing::SyntaxKind::Bar)
                    }) =>
                {
                    let a = x
                        .a()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt));
                    let b = x
                        .a()
                        .map_or((Pattern::Any, self.span()), |x| x.to_pattern(cxt));
                    Pattern::Or(vec![a, b])
                }
                ast::Expr::Binder(_) => todo!("binder patterns"),

                ast::Expr::EffPat(_) => todo!("eff patterns"),

                _ => {
                    cxt.ecxt.error(
                        self.span(),
                        TypeError::Other("expected pattern".to_string()),
                    );
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
                self.span().start
                    ..self
                        .body()
                        .map(|x| x.span().start)
                        .unwrap_or(self.span().end),
                self.body().and_then(|x| x.expr()),
            )
        }
    }
}

// OUTPUT

type PEnv = Vec<(Name, Val)>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct PVar(usize);

/// A syntactically-irrefutable pattern
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum IPat {
    Pair(PVar, PVar),
    Var(Name),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Body(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Cons {
    Lit(Literal),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Branch<T: IsTerm> {
    cons: Cons,
    args: Vec<PVar>,
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
    env_tys: HashMap<Body, PEnv>,
    var_tys: Vec<Val>,
    bodies: Vec<Option<ast::Expr>>,
}

impl CaseElabCxt<'_, '_> {
    fn pvar(&mut self, ty: Val) -> PVar {
        let l = self.var_tys.len();
        self.var_tys.push(ty);
        PVar(l)
    }

    fn add_body(&mut self, body: Option<ast::Expr>) -> Body {
        let l = self.bodies.len();
        self.bodies.push(body);
        Body(l)
    }

    fn column_select_heuristic(&self, top_row: &input::Row, rows: &[input::Row]) -> PVar {
        // Find the variable used by the most rows
        // TODO switch to left-to-right if GADT constructors are involved
        top_row
            .columns
            .iter()
            .map(|c| {
                (
                    c.var,
                    rows.iter()
                        .filter(|x| x.columns.iter().any(|c2| c2.var == c.var))
                        .count(),
                )
            })
            .max_by_key(|&(_, b)| b)
            .unwrap()
            .0
    }

    fn compile_rows(&mut self, mut rows: Vec<input::Row>) -> DecNode<Expr> {
        if rows.is_empty() {
            // TODO find missing pattern and possibly emit error
            return DecNode {
                ipats: Vec::new(),
                dec: Dec::Failure,
            };
        }

        let row = &rows[0];

        // If the first row has no patterns, it will definitely match (modulo guards)
        // other rows are unreachable here, but may be reachable through another path so we figue that out later
        if row.columns.is_empty() {
            let row = rows.remove(0);
            self.env_tys.insert(row.body, row.make_env(self));

            let dec = match &row.guard {
                Some(guard) => {
                    // Add all extra rows to the guard fallback
                    let guard = guard.check(
                        Val::var(Var::Builtin(Builtin::BoolType)),
                        &mut self.ecxt,
                        &CheckReason::Condition,
                    );
                    let mut size = self.ecxt.size();
                    let params = self.env_tys[&row.body]
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
                        Box::new(self.compile_rows(rows)),
                    )
                }
                None => {
                    // We still want type errors in unreachable rows!
                    let _ = self.compile_rows(rows);
                    Dec::Success(row.body)
                }
            };
            return DecNode {
                // TODO is this the correct way to handle ty_ipats or should it be higher up in the tree?
                ipats: row.ipats(),
                dec,
            };
        }

        let switch_var = self.column_select_heuristic(row, &rows);
        let sty = self.var_tys[switch_var.0].clone();

        if rows.iter().any(|x| {
            x.columns
                .iter()
                .any(|x| x.var == switch_var && matches!(x.pat.0, input::Pattern::Or(_)))
        }) {
            rows = rows
                .to_vec()
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
                                                c.pat = v.remove(i);
                                            }
                                            _ => (),
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
        let (mut yes, mut no): (Vec<input::Row>, Vec<input::Row>) = Default::default();
        let mut args = Vec::new();
        let mut start_ipats = Vec::new();

        for mut row in rows.iter().cloned() {
            match self.remove_column(&mut row, switch_var, &sty, &mut yes_cons) {
                input::RemovedColumn::Yes(_cons, cargs) => {
                    if args.is_empty() {
                        todo!("find args types");
                        // args.extend((0..cargs.len()).map(|_| self.pvar()));
                    }
                    row.columns.extend(
                        cargs
                            .into_iter()
                            .zip(&args)
                            .map(|(pat, &var)| input::Column { pat, var }),
                    );
                    yes.push(row);
                }
                input::RemovedColumn::No => {
                    no.push(row);
                }
                input::RemovedColumn::IPat(ipat) => {
                    // It has patterns involving the switch variable, but doesn't actually depend on it
                    // However, columns after this one might depend on the pattern, so we can't put it at the end
                    // This row will go in both the yes and no branches, so we add the ipat to the start of this node
                    start_ipats.push((switch_var, ipat));
                    yes.push(row.clone());
                    no.push(row);
                }
                input::RemovedColumn::Nothing => {
                    // No tests on the switch variable, so it goes in both cases
                    yes.push(row.clone());
                    no.push(row);
                }
            }
        }

        let mut yes = self.compile_rows(yes);
        match yes_cons {
            Some(yes_cons) => {
                let no = self.compile_rows(no);

                DecNode {
                    ipats: start_ipats,
                    dec: Dec::Switch(
                        switch_var,
                        vec![Branch {
                            cons: yes_cons,
                            args,
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
    let svar = cxt.pvar(sty);
    let rows = branches
        .into_iter()
        .map(|(pat, span, body)| input::Row::new(svar, pat, span, body, &mut cxt))
        .collect();
    let dec = cxt.compile_rows(rows);
    let mut rhs = Vec::new();
    for (i, body) in cxt.bodies.into_iter().enumerate() {
        match cxt.env_tys.get(&Body(i)) {
            Some(env) => {
                cxt.ecxt.push();
                let mut params = Vec::new();
                for (name, ty) in env {
                    params.push(Par {
                        name: *name,
                        ty: ty.clone().quote(cxt.ecxt.size(), None),
                    });
                    cxt.ecxt.define_local(*name, ty.clone(), None);
                }
                let body = match rty {
                    Some((rty, reason)) => {
                        body.map_or(Expr::Error, |x| x.check(rty.clone(), cxt.ecxt, reason))
                    }
                    None => match body {
                        Some(body) => {
                            let (expr, ty) = body.infer(cxt.ecxt);
                            *rty = Some((ty, CheckReason::MustMatch(body.span())));
                            expr
                        }
                        None => Expr::Error,
                    },
                };
                cxt.ecxt.pop();
                rhs.push(EClos {
                    class: Lam(Expl),
                    params,
                    body: Box::new(body),
                });
            }
            None => {
                eprintln!("Warning: unreachable case branch!");
            }
        }
    }
    (
        CaseOf { dec, svar, rhs },
        // TODO quote with scope constraint
        // basically we need to reject this:
        //      (x: (a: Type, a)) => case x of
        //          (_, x) => x
        // (technically also possible is to type it as
        //      (x: (a: Type, a)) -> case x of
        //          (a, _) => a
        // but that falls apart when x is complicated; best to let the user check that if necessary.)
        //
        // it should also attempt to do e.g.
        //      ((a: I32, b: I32) => a + b) x
        //      : case x of { (a, b) => I32 }
        //      --> I32
        rty.as_ref().unwrap().0.clone().quote(ecxt.size(), None),
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
            self.branches().into_iter().map(|x| x.as_row()),
            rty,
            ecxt,
        );
        (scrutinee, case_of, ty)
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
            IPat::Var(v) => Doc::start(db.lookup_name(*v)),
        }
    }
}
impl Cons {
    pub(super) fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        match self {
            Cons::Lit(l) => l.pretty(db),
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
                            .chain(Doc::intersperse(
                                x.args.iter().map(|x| Doc::start(x)),
                                Doc::none().space(),
                            ))
                            .space()
                            .add("=>", ())
                            .space()
                            .chain(x.then.pretty(db).indent())
                    }),
                    Doc::none().hardline(),
                ))
                .chain(fallback.as_ref().map_or(Doc::none(), |x| {
                    Doc::start("_ => ").chain(x.pretty(db).indent())
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
        let Branch { cons, args, then } = self;
        Branch {
            cons,
            args,
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
