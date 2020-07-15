//! Facilities for creating, representing, matching, and lowering patterns in `case` expressions.
use crate::{
    bicheck::TCtx,
    common::*,
    term::{Builtin, STerm, Term},
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
            fn match_len<'e>(a: &Term, b: &'e Elab, or: &'e Elab) -> Option<&'e Elab> {
                match (a, b) {
                    (Term::App(f, _), Elab::Fun(_, from, to)) => match_len(f, to, from),
                    // They put an App but one wasn't needed
                    (Term::App(_, _), _) => None,
                    _ => Some(or),
                }
            }

            let tx = match_len(t, cty, cty)?;
            let px = to_pattern(x, tx, constraints, tctx)?;

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
                            // TODO do something with the meta solutions found eree
                            if !ty.result().unify(self, &mut tctx, &mut Vec::new()) {
                                return None;
                            }
                            Some(match ty {
                                Elab::Data(_, _, _) => x.cloned(&mut cln),
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
                                _ => panic!("wrong type"),
                            })
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

impl Pat {
    /// Adds the types of any variables bound by the pattern to the typing context
    pub fn apply_types(&self, tctx: &mut TCtx) {
        match self {
            Pat::Var(s, t) => tctx.set_ty(*s, t.cloned(&mut Cloner::new(tctx))),
            Pat::Pair(x, y) | Pat::App(x, y) => {
                x.apply_types(tctx);
                y.apply_types(tctx);
            }
            Pat::Cons(_, _) | Pat::Unit | Pat::I32(_) => (),
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
            Pat::Unit | Pat::I32(_) => (),
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

    pub fn matches(&self, x: &Elab, ectx: &mut ECtx) -> TBool {
        match (self, x) {
            (Pat::Unit, _) => Yes,
            (Pat::I32(n), Elab::I32(m)) => (n == m).into(),
            (Pat::Pair(a1, b1), Elab::Pair(a2, b2)) => a1.matches(a2, ectx) & b1.matches(b2, ectx),
            (Pat::App(f1, x1), Elab::App(f2, x2)) => f1.matches(f2, ectx) & x1.matches(x2, ectx),
            (Pat::Var(s, _), _) => {
                ectx.set_val(*s, x.cloned(&mut Cloner::new(ectx)));
                Yes
            }
            (Pat::Cons(a, _), Elab::Cons(b, _)) => (a == b).into(),
            // This means we have a variable instead of a pair or constructor or something
            _ => Maybe,
        }
    }

    // /// Compile this pattern to code that binds all variables and returns whether it matched
    // ///
    // /// This function clones `param`, so it should be a `LowIR::Local`
    // pub fn lower(&self, param: LowIR, lctx: &mut LCtx) -> LowIR {
    //     match self {
    //         Pat::Cons(id, ty) => {
    //             let sid = match ty.result().head() {
    //                 Elab::Data(_, sid, _) => *sid,
    //                 _ => panic!("wrong type"),
    //             };
    //             // TODO narrowing of GADT variants based on type, in LowIR
    //             let tag_size = tag_width(
    //                 &lctx
    //                     .database()
    //                     .symbols(ScopeId::Struct(sid, Box::new(lctx.scope()))),
    //             );
    //             if tag_size == 0 {
    //                 LowIR::BoolConst(true)
    //             } else {
    //                 let idx = lctx
    //                     .database()
    //                     .symbols(ScopeId::Struct(sid, Box::new(lctx.scope())))
    //                     .iter()
    //                     .enumerate()
    //                     .find(|(_, x)| x.raw() == lctx.bindings().tag_name(*id))
    //                     .unwrap()
    //                     .0 as u64;
    //                 let tag = LowIR::Project(Box::new(param), 0);
    //
    //                 LowIR::CompOp {
    //                     op: CompOp::Eq,
    //                     lhs: Box::new(LowIR::SizedIntConst(tag_size, idx)),
    //                     rhs: Box::new(tag.clone()),
    //                 }
    //             }
    //         }
    //         Pat::App(f, x) => {
    //             // We need to know where we are
    //             // If there aren't any `App`s ahead of us, we're at the first parameter
    //             let idx = f.spine_len();
    //             let x_param =
    //                 LowIR::Project(Box::new(LowIR::Project(Box::new(param.clone()), 1)), idx);
    //
    //             // Pass the parameter unchanged for the head, so it can extract the tag and make sure it matches
    //             let f = f.lower(param, lctx);
    //             let x = x.lower(x_param, lctx);
    //
    //             LowIR::BoolOp {
    //                 op: BoolOp::And,
    //                 lhs: Box::new(f),
    //                 rhs: Box::new(x),
    //             }
    //         }
    //         Pat::I32(i) => LowIR::CompOp {
    //             op: CompOp::Eq,
    //             // This does the necessary bit-fiddling to make it a u64 for use as a literal
    //             lhs: Box::new(Elab::I32(*i).as_low(lctx).unwrap()),
    //             rhs: Box::new(param),
    //         },
    //         Pat::Pair(x, y) => {
    //             let x_param = LowIR::Project(Box::new(param.clone()), 0);
    //             let y_param = LowIR::Project(Box::new(param), 1);
    //             let x = x.lower(x_param, lctx);
    //             let y = y.lower(y_param, lctx);
    //             LowIR::BoolOp {
    //                 op: BoolOp::And,
    //                 lhs: Box::new(x),
    //                 rhs: Box::new(y),
    //             }
    //         }
    //         // TODO the type should be able to match, e.g. in unions
    //         Pat::Var(s, t) => {
    //             let lty = t.as_low_ty(lctx);
    //             lctx.set_low_ty(*s, lty);
    //             LowIR::Let(*s, Box::new(param), Box::new(LowIR::BoolConst(true)))
    //         }
    //         // Unit always matches
    //         Pat::Unit => LowIR::BoolConst(true),
    //     }
    // }
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
                .chain(x.pretty(ctx).nest(Prec::Atom)),
            Pat::Cons(tid, _) => tid.pretty(ctx),
        }
    }
}
