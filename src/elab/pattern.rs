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

    #[derive(Clone)]
    pub(super) enum Pattern {
        Cons(Cons, Vec<Pattern>),
        Pair(Box<Pattern>, Box<Pattern>),
        Or(Vec<Pattern>),
        Var(Name),
        Any,
    }

    #[derive(Clone)]
    pub(super) struct Column {
        pub var: PVar,
        pub pat: Pattern,
    }

    pub(super) enum RemovedColumn {
        Nothing,
        IPat(IPat),
        // TODO is this cons necessary?
        Yes(Cons, Vec<Pattern>),
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
                Some(i) => match &row.columns[i].pat {
                    Pattern::Cons(cons, _args) => match target_cons {
                        Some(tcons) => {
                            if tcons == cons {
                                match row.columns.remove(i).unwrap() {
                                    Column {
                                        pat: Pattern::Cons(cons, args),
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
                                    pat: Pattern::Cons(cons, args),
                                    ..
                                } => RemovedColumn::Yes(cons, args),
                                _ => unreachable!(),
                            }
                        }
                    },
                    Pattern::Pair(_, _) => {
                        let (a, b) = match row.columns.remove(i).unwrap() {
                            Column {
                                pat: Pattern::Pair(a, b),
                                ..
                            } => (*a, *b),
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
                                assert!(clos.params.implicit.is_empty());
                                assert_eq!(clos.params.explicit.len(), 1);
                                let ta = clos.params.explicit[0].ty.clone();
                                let tb = clos.clone().vquote(row.tyvars_size);
                                let va = self.pvar(ta);
                                let vb = self.pvar(tb);
                                row.tyvars_size += clos.params.len();
                                row.ty_ipats
                                    .push((va, IPat::Var(clos.params.explicit[0].name)));
                                (va, vb)
                            }
                            Val::Error => (self.pvar(Val::Error), self.pvar(Val::Error)),
                            _ => unreachable!(),
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
        fn to_pattern(&self, cxt: &mut CaseElabCxt) -> Pattern {
            match self {
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
                ast::Expr::GroupedExpr(x) => x.expr().map_or(Pattern::Any, |x| x.to_pattern(cxt)),
                ast::Expr::Tuple(x) => {
                    let a = x.lhs().map_or(Pattern::Any, |x| x.to_pattern(cxt));
                    let b = x.rhs().map_or(Pattern::Any, |x| x.to_pattern(cxt));
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
                    let a = x.a().map_or(Pattern::Any, |x| x.to_pattern(cxt));
                    let b = x.a().map_or(Pattern::Any, |x| x.to_pattern(cxt));
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
            }
        }
    }

    impl ast::CaseBranch {
        pub(super) fn to_row(&self, var: PVar, cxt: &mut CaseElabCxt) -> Row {
            let pat = self.pat().map_or(Pattern::Any, |x| x.to_pattern(cxt));
            Row {
                columns: VecDeque::from(vec![Column { var, pat }]),
                guard: None,
                tyvars_size: cxt.ecxt.size(),
                ty_ipats: Vec::new(),
                end_ipats: VecDeque::new(),
                body: cxt.add_body(self.body().and_then(|x| x.expr())),
            }
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
impl IPat {
    fn add_size(&self, start: Size) -> Size {
        match self {
            IPat::Pair(_, _) => start,
            IPat::Var(_) => start.inc(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Body(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Cons {
    Lit(Literal),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Branch {
    cons: Cons,
    args: Vec<PVar>,
    then: Box<DecNode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Dec {
    Success(Body),
    Failure,
    Guard(Expr, Body, Box<DecNode>),
    Switch(PVar, Vec<Branch>, Option<Box<DecNode>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DecNode {
    ipats: Vec<(PVar, IPat)>,
    dec: Dec,
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

    fn column_select_heuristic(&self, topRow: &input::Row, rows: &[input::Row]) -> PVar {
        // Find the variable used by the most rows
        // TODO switch to left-to-right if GADT constructors are involved
        topRow
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

    fn compile_rows(&mut self, mut rows: Vec<input::Row>) -> DecNode {
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
            // let size = row.end_ipats.iter().fold(self.ecxt.size(), |size, (_, i)| i.add_size(size));
            // self.env_tys.insert(row.body, size);
            self.env_tys.insert(row.body, row.make_env(self));

            let dec = match &row.guard {
                Some(guard) => {
                    // Add all extra rows to the guard fallback
                    let guard =
                        guard.check(Val::var(Var::Builtin(Builtin::BoolType)), &mut self.ecxt);
                    Dec::Guard(guard, row.body, Box::new(self.compile_rows(rows)))
                }
                None => Dec::Success(row.body),
            };
            return DecNode {
                ipats: row.end_ipats.into(),
                dec,
            };
        }

        let switch_var = self.column_select_heuristic(row, &rows);
        let sty = self.var_tys[switch_var.0].clone();

        if rows.iter().any(|x| {
            x.columns
                .iter()
                .any(|x| x.var == switch_var && matches!(x.pat, input::Pattern::Or(_)))
        }) {
            rows = rows
                .to_vec()
                .into_iter()
                .flat_map(|x| {
                    match x
                        .columns
                        .iter()
                        .find(|x| x.var == switch_var)
                        .map(|x| &x.pat)
                    {
                        Some(input::Pattern::Or(v)) => (0..v.len())
                            .map(|i| {
                                let mut x = x.clone();
                                for c in x.columns.iter_mut() {
                                    if c.var == switch_var {
                                        match &mut c.pat {
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

        let yes = self.compile_rows(yes);
        let no = self.compile_rows(no);

        DecNode {
            ipats: start_ipats,
            dec: Dec::Switch(
                switch_var,
                vec![Branch {
                    cons: yes_cons.unwrap(),
                    args,
                    then: Box::new(yes),
                }],
                Some(Box::new(no)),
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CaseRhs {
    size: Size,
    body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CaseOf {
    svar: PVar,
    dec: DecNode,
    rhs: Vec<CaseRhs>,
}

impl ast::Case {
    pub(super) fn elaborate(&self, rty: &mut Option<Val>, ecxt: &mut Cxt) -> (Expr, CaseOf) {
        let (scrutinee, sty) = self
            .scrutinee()
            .map(|x| x.infer(ecxt))
            .unwrap_or((Expr::Error, Val::Error));
        let mut cxt = CaseElabCxt {
            ecxt,
            env_tys: HashMap::new(),
            var_tys: Vec::new(),
            bodies: Vec::new(),
        };
        let svar = cxt.pvar(sty);
        let rows = self
            .branches()
            .into_iter()
            .map(|x| x.to_row(svar, &mut cxt))
            .collect();
        let dec = cxt.compile_rows(rows);
        let mut rhs = Vec::new();
        for (i, body) in cxt.bodies.into_iter().enumerate() {
            match cxt.env_tys.get(&Body(i)) {
                Some(env) => {
                    cxt.ecxt.push();
                    for (name, ty) in env {
                        cxt.ecxt.scope_mut().define_local(*name, ty.clone());
                    }
                    let expr = match rty {
                        Some(rty) => body.map_or(Expr::Error, |x| x.check(rty.clone(), cxt.ecxt)),
                        None => {
                            let (expr, ty) =
                                body.map_or((Expr::Error, Val::Error), |x| x.infer(cxt.ecxt));
                            *rty = Some(ty);
                            expr
                        }
                    };
                    rhs.push(CaseRhs {
                        size: cxt.ecxt.size(),
                        body: expr,
                    });
                }
                None => {
                    eprintln!("Warning: unreachable case branch!");
                }
            }
        }
        (scrutinee, CaseOf { dec, svar, rhs })
    }
}
