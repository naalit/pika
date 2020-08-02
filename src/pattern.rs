//! Facilities for creating, representing, matching, and lowering patterns in `case` expressions.
use crate::{
    bicheck::TCtx,
    common::*,
    term::{STerm, Term},
};

#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub enum Pat {
    /// Matches anything and binds it to a variable. Also stores the variable's type.
    Var(Sym, Elab),
    Pair(Box<Pat>, Box<Pat>),
    App(Box<Pat>, Box<Pat>),
    /// Matches a data constructor, often the head of an App. We store the type as well, like in Elab.
    Cons(TagId, Elab),
    Unit,
    I32(i32),
    /// Matches anything and ignores it
    Wild,
    // May add in the future:
    // - Struct patterns
    // - Union patterns
    // - @ patterns
}

/// Attempts to convert a term to a pattern; currently doesn't return any details of an error, but invalid patterns are usually caught during name binding anyway.
pub fn to_pattern(
    t: &STerm,
    ty: &Elab,
    constraints: &mut Vec<(Sym, Elab)>,
    tctx: &mut TCtx,
) -> Option<Pat> {
    match (&**t, ty) {
        (Term::Var(s), _) => {
            let ty = if constraints.is_empty() {
                ty.cloned(&mut Cloner::new(tctx))
            } else {
                let mut cln = Cloner::new(tctx);
                let mut tctx = tctx.clone();
                tctx.apply_metas(constraints.iter().map(|(k, v)| (*k, v.cloned(&mut cln))));
                ty.cloned(&mut cln).whnf(&mut tctx)
            };
            Some(Pat::Var(*s, ty))
        }
        (Term::Unit, Elab::Unit) => Some(Pat::Unit),
        (Term::I32(i), Elab::Builtin(Builtin::Int)) => Some(Pat::I32(*i)),
        (Term::Pair(x, y), Elab::Pair(tx, ty)) => Some(Pat::Pair(
            Box::new(to_pattern(x, tx, constraints, tctx)?),
            Box::new(to_pattern(y, ty, constraints, tctx)?),
        )),

        (Term::App(f, x), _) => {
            let pf = to_pattern(f, ty, constraints, tctx)?;
            let cty = match pf.head() {
                Pat::Cons(_, t) => t,
                _ => return None,
            };

            // App(App(_, _), _) <-> Fun(_, X, Fun(_, Y, _)) -> or = X
            // ->  App(_, _)     <->           Fun(_, Y, _)  -> or = Y
            // ->      _         <->                     _   ==> or@Y
            //
            //     App(_, _)     <-> Fun(_, X, Fun(_, Y, _)) -> or = X
            // ->      _         <->           Fun(_, Y, _)  ==> or@X
            //

            // App(App(_, _), _) <-> Fun(true, A, Fun(false, B, Fun(true, C, Fun(false, D, _)))) -> i = 1
            // App(App(_, _), _) <->              Fun(false, B, Fun(true, C, Fun(false, D, _)))  -> or = B, i = 0, li = 1
            //     App(_, _)     <->                            Fun(true, C, Fun(false, D, _))   -> or = B, i = 1, li = 1
            //     App(_, _)     <->                                         Fun(false, D, _)    -> or = D, i = 0, li = 1
            //         _         <->                                                       _     ==> or@Y, li@1

            // `implicits` tracks the number of implicit arguments since the last explicit one
            // `last_implicits` tracks the number of implicit arguments before the last explicit one
            fn match_len<'e>(
                a: &Term,
                b: &'e Elab,
                or: &'e Elab,
                implicits: u32,
                last_implicits: u32,
            ) -> Option<(&'e Elab, u32)> {
                match (a, b) {
                    (_, Elab::Fun(cl, _, to)) if cl.implicit => {
                        match_len(a, to, or, implicits + 1, last_implicits)
                    }
                    // Reset the implicits when we hit an explicit arg
                    // WAIT THAT'S THE WRONG THING! WHAT DO WE DO?
                    (Term::App(f, _), Elab::Fun(_, from, to)) => {
                        match_len(f, to, from, 0, implicits)
                    }
                    // They put an App but one wasn't needed
                    (Term::App(_, _), _) => None,
                    _ => Some((or, last_implicits)),
                }
            }

            let (tx, implicits) = match_len(t, &cty, &cty, 0, 0)?;
            let px = to_pattern(x, tx, constraints, tctx)?;

            let mut pf = pf;
            for _ in 0..implicits {
                // Add a wild pattern for each implicit; eventually it may be possible to match on them
                pf = Pat::App(Box::new(pf), Box::new(Pat::Wild));
            }

            Some(Pat::App(Box::new(pf), Box::new(px)))
        }
        (Term::Project(_, _), _) => match crate::bicheck::synth(t, tctx) {
            Ok(Elab::Cons(tid, t)) => {
                let t = t.cloned(&mut Cloner::new(&tctx));
                // Add constraints
                let mut tcons = Vec::new();
                let mut tctx = tctx.clone();
                tctx.extend_metas(ty.fvs(&tctx));
                let result = t.result();
                tctx.extend_metas(result.fvs(&tctx));
                if result.unify(&ty, &tctx, &mut tcons) {
                    constraints.append(&mut tcons);
                    Some(Pat::Cons(tid, t))
                } else {
                    eprintln!(
                        "Failed unification: '{}' with '{}'",
                        result.pretty(&tctx).ansi_string(),
                        ty.pretty(&tctx).ansi_string()
                    );
                    None
                }
            }
            // TODO should we propagate type errors out of here?
            _ => None,
        },
        _ => None,
    }
}

/// Three-value-logic: yes, maybe, no.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TBool {
    Yes,
    Maybe,
    No,
}
use std::collections::HashSet;
pub use TBool::*;
impl From<bool> for TBool {
    fn from(b: bool) -> TBool {
        if b {
            Yes
        } else {
            No
        }
    }
}
impl std::ops::BitAnd for TBool {
    type Output = TBool;
    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (_, No) | (No, _) => No,
            (Yes, Yes) => Yes,
            _ => Maybe,
        }
    }
}

impl Elab {
    fn expand_ty(&self, env: &(impl HasDatabase + Scoped)) -> Option<Vec<Elab>> {
        match self.head() {
            Elab::Data(_, s, _) => {
                let scope = ScopeId::Struct(*s, Box::new(env.scope()));
                let mut cln = Cloner::new(env);
                Some(
                    env.database()
                        .symbols(scope.clone())
                        .iter()
                        .map(|x| env.database().elab(scope.clone(), **x).unwrap())
                        .filter_map(|x| {
                            let ty = x.get_type(env);
                            let mut tctx = TCtx::new(env);
                            tctx.extend_metas(self.fvs(&tctx));
                            tctx.extend_metas(ty.result().fvs(&tctx));
                            let mut cons = Vec::new();
                            if !ty.result().unify(self, &mut tctx, &mut cons) {
                                return None;
                            }
                            tctx.apply_metas(cons);
                            Some(
                                match ty {
                                    Elab::App(_, _) | Elab::Data(_, _, _) => x.cloned(&mut cln),
                                    t @ Elab::Fun(_, _, _) => {
                                        fn expand_fun(
                                            s: Elab,
                                            f: Elab,
                                            cln: &mut Cloner,
                                            env: &impl HasBindings,
                                        ) -> Elab {
                                            match s {
                                                Elab::Fun(_, from, to) => {
                                                    let v = Elab::Var(
                                                        Span::empty(),
                                                        env.bindings_mut().create("_".to_string()),
                                                        from,
                                                    );
                                                    expand_fun(
                                                        *to,
                                                        Elab::App(Box::new(f), Box::new(v)),
                                                        cln,
                                                        env,
                                                    )
                                                }
                                                _ => f,
                                            }
                                        }

                                        expand_fun(t, x.cloned(&mut cln), &mut cln, env)
                                    }
                                    _ => panic!("wrong type {}", ty.pretty(env).ansi_string()),
                                }
                                .whnf(&mut tctx),
                            )
                        })
                        .collect(),
                )
            }

            _ => None,
        }
    }

    pub fn expand(&self, env: &(impl HasDatabase + Scoped)) -> Option<Vec<Elab>> {
        let x = match self {
            Elab::Var(_, _, t) => t.expand_ty(env),
            // These two try to expand both sides
            Elab::Pair(x, y) => {
                let vx = x.expand(env);
                let vy = y.expand(env);
                if vx.is_none() && vy.is_none() {
                    return None;
                }
                let mut cln = Cloner::new(env);
                // If one side can't be expanded but the other can, expand just the one side
                let vx = vx.unwrap_or_else(|| vec![x.cloned(&mut cln)]);
                let vy = vy.unwrap_or_else(|| vec![y.cloned(&mut cln)]);
                // Then make every possible combination of x and y's expansions
                Some(
                    vx.into_iter()
                        .flat_map(|x| {
                            vy.iter()
                                .map(|y| {
                                    Elab::Pair(
                                        Box::new(x.cloned(&mut cln)),
                                        Box::new(y.cloned(&mut cln)),
                                    )
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect(),
                )
            }
            Elab::App(x, y) => {
                let vx = x.expand(env);
                let vy = y.expand(env);
                if vx.is_none() && vy.is_none() {
                    return None;
                }
                let mut cln = Cloner::new(env);
                // If one side can't be expanded but the other can, expand just the one side
                let vx = vx.unwrap_or_else(|| vec![x.cloned(&mut cln)]);
                let vy = vy.unwrap_or_else(|| vec![y.cloned(&mut cln)]);
                // Then make every possible combination of x and y's expansions
                Some(
                    vx.into_iter()
                        .flat_map(|x| {
                            vy.iter()
                                .map(|y| {
                                    Elab::App(
                                        Box::new(x.cloned(&mut cln)),
                                        Box::new(y.cloned(&mut cln)),
                                    )
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect(),
                )
            }
            _ => None,
        };
        x
    }
}

use crate::backend::low::{CompOp, Expr, LCtx, Low, Ty, Val};

/// `f a b c` -> `[c, b, a]`.
/// Note that this iterator reverses the order of arguments.
pub struct SpineIter<'a>(&'a Pat);
impl<'a> SpineIter<'a> {
    pub fn reversed(self) -> std::iter::Rev<std::vec::IntoIter<&'a Pat>> {
        self.collect::<Vec<_>>().into_iter().rev()
    }
}
impl<'a> Iterator for SpineIter<'a> {
    type Item = &'a Pat;

    fn next(&mut self) -> Option<&'a Pat> {
        match self.0 {
            Pat::App(f, x) => {
                self.0 = f;
                Some(x)
            }
            _ => None,
        }
    }
}

impl Pat {
    /// `f a b c` -> `[c, b, a]`.
    /// Note that this iterator reverses the order of arguments.
    pub fn spine_iter(&self) -> SpineIter {
        SpineIter(self)
    }

    /// Adds the types of any variables bound by the pattern to the typing context
    pub fn apply_types(&self, tctx: &mut TCtx) {
        match self {
            Pat::Var(s, t) => tctx.set_ty(*s, t.cloned(&mut Cloner::new(tctx))),
            Pat::Pair(x, y) | Pat::App(x, y) => {
                x.apply_types(tctx);
                y.apply_types(tctx);
            }
            Pat::Cons(_, _) | Pat::Unit | Pat::I32(_) | Pat::Wild => (),
        }
    }

    pub fn cloned(&self, cln: &mut Cloner) -> Self {
        match self {
            Pat::Var(s, e) => {
                let fresh = cln.bindings_mut().fresh(*s);
                cln.set(*s, fresh);
                Pat::Var(fresh, e.cloned(cln))
            }
            Pat::Pair(x, y) => Pat::Pair(Box::new(x.cloned(cln)), Box::new(y.cloned(cln))),
            Pat::App(x, y) => Pat::App(Box::new(x.cloned(cln)), Box::new(y.cloned(cln))),
            Pat::Cons(id, ty) => Pat::Cons(*id, ty.cloned(cln)),
            Pat::Unit => Pat::Unit,
            Pat::I32(i) => Pat::I32(*i),
            Pat::Wild => Pat::Wild,
        }
    }

    /// Helper for `Elab::fvs`
    pub fn fvs_(&self, bound: &mut HashSet<Sym>, free: &mut Vec<Sym>) {
        match self {
            Pat::Var(x, t) => {
                bound.insert(*x);
                t.fvs_(bound, free);
            }
            Pat::Pair(x, y) | Pat::App(x, y) => {
                x.fvs_(bound, free);
                y.fvs_(bound, free);
            }
            Pat::Cons(_, t) => t.fvs_(bound, free),
            Pat::Unit | Pat::I32(_) | Pat::Wild => (),
        }
    }

    pub fn head(&self) -> &Self {
        match self {
            Pat::App(f, _) => f.head(),
            _ => self,
        }
    }

    /// How many `App` nodes are there chained together left-associatively?
    pub fn spine_len(&self) -> usize {
        match self {
            Pat::App(f, _) => f.spine_len() + 1,
            _ => 0,
        }
    }

    /// Matches this pattern against `x`, binding all variables and returning whether it matches.
    pub fn matches(&self, x: &Elab, ectx: &mut ECtx) -> TBool {
        match (self, x) {
            (Pat::Unit, _) | (Pat::Wild, _) => Yes,
            (Pat::I32(n), Elab::I32(m)) => (n == m).into(),
            (Pat::Pair(a1, b1), Elab::Pair(a2, b2)) => a1.matches(a2, ectx) & b1.matches(b2, ectx),
            (Pat::App(f1, x1), Elab::App(f2, x2)) => f1.matches(f2, ectx) & x1.matches(x2, ectx),
            (Pat::Var(s, _), _) => {
                ectx.set_val(*s, x.cloned(&mut Cloner::new(ectx)));
                Yes
            }
            (Pat::Cons(a, _), _) if x.cons().is_some() => (*a == x.cons().unwrap()).into(),
            // This is needed for matching constructors of different arity
            (Pat::App(_, _), _) if x.cons().is_some() => No,
            // This means we have a variable instead of a pair or constructor or something
            _ => Maybe,
        }
    }

    /// Returns a list of all variables bound by this pattern, with types.
    pub fn bound(&self) -> Vec<(Sym, &Elab)> {
        let mut bound = Vec::new();
        self.bound_(&mut bound);
        bound
    }

    /// Helper for `bound()`
    fn bound_<'a>(&'a self, bound: &mut Vec<(Sym, &'a Elab)>) {
        match self {
            Pat::Var(s, t) => bound.push((*s, t)),
            Pat::Pair(x, y) | Pat::App(x, y) => {
                x.bound_(bound);
                y.bound_(bound);
            }
            Pat::Cons(_, _) | Pat::Unit | Pat::I32(_) | Pat::Wild => (),
        }
    }

    pub fn cons(&self) -> Option<(TagId, &Elab)> {
        match self {
            Pat::Cons(id, t) => Some((*id, t)),
            Pat::App(f, _) => f.cons(),
            _ => None,
        }
    }

    pub fn uses(&self, s: Sym) -> bool {
        match self {
            Pat::Var(_, t) | Pat::Cons(_, t) => t.uses(s),
            Pat::Pair(x, y) | Pat::App(x, y) => x.uses(s) || y.uses(s),
            Pat::Unit | Pat::I32(_) | Pat::Wild => false,
        }
    }

    pub fn binds(&self, s: Sym) -> bool {
        match self {
            Pat::Var(x, _) => *x == s,
            Pat::Pair(x, y) | Pat::App(x, y) => x.binds(s) || y.binds(s),
            Pat::Unit | Pat::I32(_) | Pat::Cons(_, _) | Pat::Wild => false,
        }
    }

    /// Compile this pattern to code that binds all variables and runs `yes` if it matched, otherwise runs `no`.
    /// It applies any constraints to `lctx`, so you might want to clone that first.
    pub fn lower(&self, ty: &Elab, param: Val, lctx: &mut LCtx, yes: Low, no: Low) -> Low {
        match (self, ty) {
            (Pat::Cons(_, _), _) | (Pat::App(_, _), _) => {
                let (id, _) = self.cons().unwrap();

                // We do this before setting metas to make sure it includes all constructors
                let cps_ty = ty.cps_ty(lctx);

                let (idx, tag_width, cons_ty) = {
                    let v = ty
                        .valid_cons(lctx)
                        .unwrap_or_else(|| panic!("{}", ty.pretty(lctx).ansi_string()));

                    if v.is_empty() {
                        panic!(
                            "Empty type '{}' is not allowed",
                            ty.pretty(lctx).ansi_string()
                        );
                    }

                    let tag_width = crate::backend::low::tag_width(&v);

                    let (idx, (_, cons_ty, metas)) = v
                        .into_iter()
                        .enumerate()
                        .find(|(_, (x, _, _))| *x == id)
                        .unwrap();
                    for (k, v) in metas {
                        lctx.ectx.set_val(k, v);
                    }

                    (idx, tag_width, cons_ty)
                };

                let union_ty = if let Ty::Struct(v) = &cps_ty {
                    v[1].clone()
                } else {
                    unreachable!()
                };
                let payload_ty = if let Ty::Union(v) = &union_ty {
                    v[idx].clone()
                } else {
                    unreachable!()
                };

                let payload_union = lctx.next_val(union_ty.clone());
                let payload = lctx.next_val(payload_ty.clone());

                // We make roughly this:
                // ```
                // if cons matches {
                //  if a matches {
                //   if b matches {
                //    yes
                //   } else no
                //  } else no
                // } else no
                // ```

                // The arguments will share `no`, so make a continuation out of it and assign it to a variable
                // `() -> no`
                let vno = lctx.next_val(Ty::Cont);
                let cno =
                    crate::backend::low::make_cont(lctx.next_val(Ty::Unit), Ty::Unit, lctx, no);
                let vunit = lctx.next_val(Ty::Unit);

                let yes = self
                    .spine_iter()
                    .reversed()
                    .zip(cons_ty.args_iter().reversed().rev())
                    .enumerate()
                    .rfold(yes, |yes, (i, (pat, ty))| {
                        let ty = ty
                            .cloned(&mut Cloner::new(lctx))
                            .whnf(&mut lctx.ectx.clone());
                        let member = lctx.next_val(ty.cps_ty(lctx));
                        let rest =
                            pat.lower(&ty, member, lctx, yes, Low::ContCall(vno, Ty::Unit, vunit));
                        Low::Let(
                            member,
                            Expr::Project(payload_ty.clone(), payload, i as u32),
                            Box::new(rest),
                        )
                    });

                let yes = Low::Let(
                    payload_union,
                    Expr::Project(cps_ty.clone(), param, 1),
                    Box::new(Low::Let(
                        payload,
                        Expr::AsVariant(union_ty, payload_union, idx as u32),
                        Box::new(yes),
                    )),
                );

                let did_match = lctx.next_val(Ty::Int(1));
                let rest = Low::IfElse(
                    did_match,
                    Box::new(yes),
                    Box::new(Low::ContCall(vno, Ty::Unit, vunit)),
                );
                let rest = Low::Let(
                    vunit,
                    Expr::Unit,
                    Box::new(Low::Let(vno, cno, Box::new(rest))),
                );

                let idx_val = lctx.next_val(Ty::Int(tag_width));
                let tag_val = lctx.next_val(Ty::Int(tag_width));
                Low::Let(
                    idx_val,
                    Expr::IntConst(tag_width, idx as u64),
                    Box::new(Low::Let(
                        tag_val,
                        Expr::Project(cps_ty, param, 0),
                        Box::new(Low::Let(
                            did_match,
                            Expr::CompOp(idx_val, CompOp::Eq, tag_val),
                            Box::new(rest),
                        )),
                    )),
                )
            }
            (Pat::Var(x, _), _) => {
                let v = lctx.get(*x).unwrap();
                Low::Let(v, Expr::Val(param), Box::new(yes))
            }
            (Pat::I32(i), _) => {
                let did_match = lctx.next_val(Ty::Int(1));
                let vconst = lctx.next_val(Ty::Int(32));
                Low::Let(
                    vconst,
                    Expr::IntConst(32, *i as u64),
                    Box::new(Low::Let(
                        did_match,
                        Expr::CompOp(vconst, CompOp::Eq, param),
                        Box::new(Low::IfElse(did_match, Box::new(yes), Box::new(no))),
                    )),
                )
            }
            (Pat::Pair(pa, pb), Elab::Pair(ta, tb)) => {
                let cty = ty.cps_ty(lctx);
                let va = lctx.next_val(ta.cps_ty(lctx));
                let vb = lctx.next_val(tb.cps_ty(lctx));
                // The two lowered patterns are going to share `no`, so we `cont`-ify it
                let vno = lctx.next_val(Ty::Cont);
                let cno =
                    crate::backend::low::make_cont(lctx.next_val(Ty::Unit), Ty::Unit, lctx, no);
                let vunit = lctx.next_val(Ty::Unit);

                let b = pb.lower(
                    tb,
                    vb,
                    lctx,
                    yes,
                    Low::Let(
                        vunit,
                        Expr::Unit,
                        Box::new(Low::ContCall(vno, Ty::Unit, vunit)),
                    ),
                );
                let a = pa.lower(
                    ta,
                    va,
                    lctx,
                    b,
                    Low::Let(
                        vunit,
                        Expr::Unit,
                        Box::new(Low::ContCall(vno, Ty::Unit, vunit)),
                    ),
                );

                Low::Let(
                    vno,
                    cno,
                    Box::new(Low::Let(
                        va,
                        Expr::Project(cty.clone(), param, 0),
                        Box::new(Low::Let(
                            vb,
                            Expr::Project(cty.clone(), param, 1),
                            Box::new(a),
                        )),
                    )),
                )
            }
            (Pat::Pair(_, _), _) => {
                panic!("expected pair type, got {}", ty.pretty(lctx).ansi_string())
            }
            (Pat::Unit, _) | (Pat::Wild, _) => yes,
        }
    }
}

impl Pretty for Pat {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        match self {
            Pat::Var(s, t) => s
                .pretty(ctx)
                .add(":")
                .style(Style::Binder)
                .space()
                .chain(t.pretty(ctx))
                .prec(Prec::Term),
            Pat::Unit => Doc::start("()").style(Style::Literal),
            Pat::I32(i) => Doc::start(i).style(Style::Literal),
            Pat::Pair(x, y) => x
                .pretty(ctx)
                .add(",")
                .space()
                .chain(y.pretty(ctx))
                .prec(Prec::Term),
            Pat::App(f, x) => f
                .pretty(ctx)
                .nest(Prec::App)
                .space()
                .chain(x.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            Pat::Cons(tid, _) => tid.pretty(ctx).style(Style::Binder),
            Pat::Wild => Doc::start("_"),
        }
    }
}
