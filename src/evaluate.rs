use crate::common::*;
use crate::elaborate::MCxt;
use crate::term::*;

impl Term {
    pub fn evaluate(self, env: &Env, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Term::Type => Val::Type,
            Term::Lit(x, t) => Val::Lit(x, t),
            Term::Var(Var::Local(ix), ty) => env.val(ix, *ty, mcxt, db),
            Term::Var(Var::Type(id, scope), ty) => {
                Val::datatype(id, scope, ty.evaluate(env, mcxt, db))
            }
            Term::Var(Var::Top(def), ty) => Val::top(def, ty.evaluate(env, mcxt, db)),
            Term::Var(Var::Rec(id), ty) => Val::rec(id, ty.evaluate(env, mcxt, db)),
            Term::Var(Var::Cons(id), ty) => Val::cons(id, ty.evaluate(env, mcxt, db)),
            Term::Var(Var::Builtin(b), ty) => Val::builtin(b, ty.evaluate(env, mcxt, db)),
            Term::Var(Var::Meta(meta), ty) => match mcxt.get_meta(meta) {
                Some(v) => v.evaluate(env, mcxt, db),
                None => Val::meta(meta, ty.evaluate(env, mcxt, db)),
            },
            Term::Clos(t, name, icit, ty, body, effs) => Val::Clos(
                t,
                icit,
                Box::new(Clos {
                    env: env.clone(),
                    term: *body,
                    ty: ty.evaluate(env, mcxt, db),
                    name,
                }),
                effs.into_iter()
                    .map(|x| x.evaluate(env, mcxt, db))
                    .collect(),
            ),
            Term::Fun(from, to, effs) => {
                let from = from.evaluate(env, mcxt, db);
                let to = to.evaluate(env, mcxt, db);
                let effs = effs
                    .into_iter()
                    .map(|x| x.evaluate(env, mcxt, db))
                    .collect();
                Val::Fun(Box::new(from), Box::new(to), effs)
            }
            Term::App(icit, f, x) => {
                let f = f.evaluate(env, mcxt, db);
                let x = x.evaluate(env, mcxt, db);
                f.app(Elim::App(icit, x), mcxt, db)
            }
            Term::Case(x, ty, cases, effs, rty) => {
                let x = x.evaluate(env, mcxt, db);
                x.app(Elim::Case(env.clone(), ty, cases, effs, rty), mcxt, db)
            }
            Term::Error => Val::Error,
            Term::Do(v) => Val::Do(env.clone(), v),
        }
    }

    /// Transfers this term from one context to another; equivalent to calling `term.evaluate(env, ...).quote(l, ...)`
    /// but faster and doesn't cause infinite recursion with `Lazy` values.
    pub fn eval_quote(self, env: &mut Env, at: Size, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Term::Type => Term::Type,
            Term::Lit(l, b) => Term::Lit(l, b),
            Term::Var(Var::Local(ix), ty) => env.val(ix, *ty, mcxt, db).quote(at, mcxt, db),
            Term::Var(Var::Meta(m), mut ty) => match mcxt.get_meta(m) {
                Some(v) => v.eval_quote(env, at, mcxt, db),
                None => {
                    *ty = ty.eval_quote(env, at, mcxt, db);
                    Term::Var(Var::Meta(m), ty)
                }
            },
            Term::Var(v, mut ty) => {
                *ty = ty.eval_quote(env, at, mcxt, db);
                Term::Var(v, ty)
            }
            Term::Clos(t, name, icit, mut ty, mut body, effs) => {
                let vty = ty.clone().evaluate(env, mcxt, db);
                *ty = ty.eval_quote(env, at, mcxt, db);

                env.push(Some(Val::local(at.next_lvl(), vty)));
                *body = body.eval_quote(env, at.inc(), mcxt, db);
                env.pop();

                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, at, mcxt, db))
                    .collect();
                Term::Clos(t, name, icit, ty, body, effs)
            }
            Term::Fun(mut a, mut b, effs) => {
                *a = a.eval_quote(env, at, mcxt, db);
                *b = b.eval_quote(env, at, mcxt, db);
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, at, mcxt, db))
                    .collect();
                Term::Fun(a, b, effs)
            }
            // We have to perform beta-reduction, so we manually evaluate and then quote again
            Term::App(icit, mut f, mut x) => {
                *f = f.eval_quote(env, at, mcxt, db);
                match *f {
                    Term::Clos(Lam, _n, _i, _ty, body, _effs) => {
                        let x = x.evaluate(env, mcxt, db);
                        env.push(Some(x));
                        let b = body.eval_quote(env, at, mcxt, db);
                        env.pop();
                        b
                    }
                    Term::Error => Term::Error,
                    _ => {
                        // No beta reduction necessary
                        *x = x.eval_quote(env, at, mcxt, db);
                        Term::App(icit, f, x)
                    }
                }
            }
            Term::Case(mut x, mut ty, cases, effs, mut rty) => {
                let vx = x.evaluate(env, mcxt, db);
                for (pat, body) in &cases {
                    use crate::pattern::MatchResult::*;
                    match pat.match_with(&vx, env.clone(), mcxt, db) {
                        Yes(mut env) => return body.clone().eval_quote(&mut env, at, mcxt, db),
                        No => continue,
                        Maybe => break,
                    }
                }
                *x = vx.quote(at, mcxt, db);
                *ty = ty.eval_quote(env, at, mcxt, db);
                *rty = rty.eval_quote(env, at, mcxt, db);
                let cases = cases
                    .into_iter()
                    .map(|(pat, body)| {
                        let mut env = env.clone();
                        let mut at = at;
                        let pat = pat.eval_quote(&mut env, &mut at, mcxt, db);
                        let body = body.eval_quote(&mut env, at, mcxt, db);
                        (pat, body)
                    })
                    .collect();
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, at, mcxt, db))
                    .collect();
                Term::Case(x, ty, cases, effs, rty)
            }
            Term::Error => Term::Error,
            Term::Do(v) => Term::Do(
                v.into_iter()
                    .map(|(id, term)| (id, term.eval_quote(env, at, mcxt, db)))
                    .collect(),
            ),
        }
    }
}

impl Val {
    /// If self is an App, resolve it recursively; only on the top level.
    pub fn inline(self, at: Size, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, hty, sp, g) => {
                if let Some(v) = g.resolve(h, &sp, at, db, mcxt) {
                    v.inline(at, db, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline(at, db, mcxt),
            x => x,
        }
    }

    /// Inlines Apps to expose Pi or Fun nodes giving it at least `n` arguments.
    /// Panics on failure.
    pub fn inline_args(self, n: usize, at: Size, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        if n == 0 {
            self
        } else {
            match self {
                Val::Fun(from, mut to, effs) => {
                    *to = to.inline_args(n - 1, at, db, mcxt);
                    Val::Fun(from, to, effs)
                }
                Val::Clos(Pi, i, cl, effs) => {
                    if n == 1 {
                        Val::Clos(Pi, i, cl, effs)
                    } else {
                        let name = cl.name;
                        let ty = cl.ty.clone();
                        let term = cl
                            .vquote(at, mcxt, db)
                            .inline_args(n - 1, at.inc(), db, mcxt)
                            .quote(at.inc(), mcxt, db);
                        Val::Clos(
                            Pi,
                            i,
                            Box::new(Clos {
                                env: Env::new(at),
                                term,
                                ty,
                                name,
                            }),
                            effs,
                        )
                    }
                }
                Val::App(h, hty, sp, g) => {
                    if let Some(v) = g.resolve(h, &sp, at, db, mcxt) {
                        v.inline_args(n, at, db, mcxt)
                    } else {
                        Val::App(h, hty, sp, g)
                    }
                }
                Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline_args(n, at, db, mcxt),
                v => unreachable!("{:?}", v),
            }
        }
    }

    /// Evaluates closures, inlines variables, and calls `force()` recursively, returning a term in normal form.
    /// This should never be used during normal compilation - it's only for benchmarking.
    pub fn force(self, at: Size, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::Type => Val::Type,
            Val::Lit(x, t) => Val::Lit(x, t),
            Val::Arc(x) => (*x).clone().force(at, db, mcxt),
            Val::App(h, mut hty, sp, g) => {
                *hty = hty.force(at, db, mcxt);
                if let Some(v) = g.resolve(h, &sp, at, db, mcxt) {
                    v.force(at, db, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Fun(mut a, mut b, effs) => {
                *a = a.force(at, db, mcxt);
                *b = b.force(at, db, mcxt);
                let effs = effs.into_iter().map(|x| x.force(at, db, mcxt)).collect();
                Val::Fun(a, b, effs)
            }
            Val::Error => Val::Error,
            Val::Do(env, v) => {
                let v = v
                    .into_iter()
                    .map(|(d, x)| {
                        (
                            d,
                            x.evaluate(&env, mcxt, db)
                                .force(env.size, db, mcxt)
                                .quote(env.size, mcxt, db),
                        )
                    })
                    .collect();
                Val::Do(env, v)
            }
            Val::Clos(t, i, mut cl, effs) => {
                cl.ty = cl.ty.force(at, db, mcxt);
                cl.term = (*cl)
                    .clone()
                    .vquote(at, mcxt, db)
                    .force(at.inc(), db, mcxt)
                    .quote(at.inc(), mcxt, db);
                let effs = effs.into_iter().map(|x| x.force(at, db, mcxt)).collect();
                Val::Clos(t, i, cl, effs)
            }
        }
    }

    /// Returns the result of applying `x` to `self`, beta-reducing if necessary.
    pub fn app(self, elim: Elim, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Val::App(h, hty, mut sp, g) => {
                if sp.is_empty() {
                    match elim.elim(Val::App(h, hty, sp, g), mcxt, db) {
                        Ok(v) => v,
                        Err((v, e)) => {
                            if let Val::App(h, hty, mut sp, g) = v {
                                sp.push(e);
                                Val::App(h, hty, sp, g)
                            } else {
                                unreachable!()
                            }
                        }
                    }
                } else {
                    sp.push(elim);
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Error => Val::Error,
            Val::Arc(a) => IntoOwned::<Val>::into_owned(a).app(elim, mcxt, db),
            x => match elim.elim(x, mcxt, db) {
                Ok(v) => v,
                Err((v, e)) => panic!(
                    "Error during evaluation: couldn't apply eliminator {:?} to value {:?}",
                    e, v
                ),
            },
            // TODO operators
            // Val::App(Var::Builtin(b), hty, mut sp, _) if sp.len() == 1 => {
            //     match b {
            //         Builtin::BinOp(op) => {
            //             if let Some(v) = op.eval(&sp[0].1, &x) {
            //                 v
            //             } else {
            //                 sp.push(elim);
            //                 // Throw away the old Glued, since that could have been resolved already
            //                 Val::App(Var::Builtin(b), hty, sp, Glued::new())
            //             }
            //         }
            //         _ => unreachable!(),
            //     }
            // }
        }
    }

    pub fn quote(self, at: Size, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Val::Type => Term::Type,
            Val::Lit(x, t) => Term::Lit(x, t),
            Val::App(h, hty, sp, g) => {
                // Inline the type to expose the Pi or Fun
                let hty = hty.inline_args(sp.len(), at, db, mcxt).quote(at, mcxt, db);
                let h = match h {
                    Var::Local(l) => match g.resolve(h, &sp, at, db, mcxt) {
                        Some(v) => return v.quote(at, mcxt, db),
                        None => Term::Var(Var::Local(at.to_ix(l)), Box::new(hty.clone())),
                    },
                    Var::Top(def) => Term::Var(Var::Top(def), Box::new(hty.clone())),
                    Var::Meta(meta) => match g.resolve(h, &sp, at, db, mcxt) {
                        Some(v) => return v.quote(at, mcxt, db),
                        None => Term::Var(Var::Meta(meta), Box::new(hty.clone())),
                    },
                    Var::Rec(id) => Term::Var(Var::Rec(id), Box::new(hty.clone())),
                    Var::Type(id, scope) => Term::Var(Var::Type(id, scope), Box::new(hty.clone())),
                    Var::Cons(id) => Term::Var(Var::Cons(id), Box::new(hty.clone())),
                    Var::Builtin(b) => Term::Var(Var::Builtin(b), Box::new(hty.clone())),
                };
                sp.into_iter()
                    .fold(h, |head, elim| elim.quote(head, at, mcxt, db))
            }
            Val::Do(mut env, v) => Term::Do(
                v.into_iter()
                    .map(|(d, t)| (d, t.eval_quote(&mut env, at, mcxt, db)))
                    .collect(),
            ),
            Val::Clos(t, icit, cl, effs) => Term::Clos(
                t,
                cl.name,
                icit,
                Box::new(cl.ty.clone().quote(at, mcxt, db)),
                Box::new(cl.quote(at, mcxt, db)),
                effs.into_iter().map(|x| x.quote(at, mcxt, db)).collect(),
            ),
            Val::Fun(from, to, effs) => Term::Fun(
                Box::new(from.quote(at, mcxt, db)),
                Box::new(to.quote(at, mcxt, db)),
                effs.into_iter().map(|x| x.quote(at, mcxt, db)).collect(),
            ),
            Val::Error => Term::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).quote(at, mcxt, db),
        }
    }
}

impl BinOp {
    pub fn eval(self, a: &Val, b: &Val) -> Option<Val> {
        let (a, t) = match a {
            Val::Lit(Literal::Positive(u), t) => (*u, *t),
            _ => return None,
        };
        let b = match b {
            Val::Lit(Literal::Positive(u), _) => *u,
            _ => return None,
        };
        Some(match self {
            BinOp::Add => Val::Lit(Literal::Positive(a + b), t),
            BinOp::Sub => Val::Lit(Literal::Positive(a - b), t),
            BinOp::Mul => Val::Lit(Literal::Positive(a * b), t),
            BinOp::Div => Val::Lit(Literal::Positive(a / b), t),
            BinOp::Exp => Val::Lit(Literal::Positive(a.pow(b as u32)), t),
            BinOp::Mod => Val::Lit(Literal::Positive(a % b), t),
            BinOp::BitAnd => Val::Lit(Literal::Positive(a & b), t),
            BinOp::BitOr => Val::Lit(Literal::Positive(a | b), t),
            BinOp::BitXor => Val::Lit(Literal::Positive(a ^ b), t),
            BinOp::BitShl => Val::Lit(Literal::Positive(a << b), t),
            BinOp::BitShr => Val::Lit(Literal::Positive(a >> b), t),
            BinOp::Eq => Val::boolean(a == b),
            BinOp::NEq => Val::boolean(a != b),
            BinOp::Lt => Val::boolean(a < b),
            BinOp::Gt => Val::boolean(a > b),
            BinOp::Leq => Val::boolean(a <= b),
            BinOp::Geq => Val::boolean(a >= b),
            BinOp::PipeL => return None,
            BinOp::PipeR => return None,
        })
    }
}

impl Term {
    /// If self is a Var::Top, inline it, and call inline_top on the result.
    pub fn inline_top(self, db: &dyn Compiler) -> Term {
        match self {
            Term::Var(Var::Top(id), _) => {
                if let Ok(info) = db.elaborate_def(id) {
                    (*info.term).clone().inline_top(db)
                } else {
                    self
                }
            }
            x => x,
        }
    }

    /// Shorthand for `eval_quote()` without changing levels
    pub fn inline_metas(self, mcxt: &MCxt, at: Size, db: &dyn Compiler) -> Self {
        self.eval_quote(&mut Env::new(at), at, mcxt, db)
    }
}

impl Val {
    pub fn inline_metas(self, at: Size, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match self {
            Val::Type => Val::Type,
            Val::Lit(x, t) => Val::Lit(x, t),
            Val::App(h, mut ty, sp, g) => {
                let h = match h {
                    Var::Meta(_) | Var::Local(_) => match g.resolve(h, &sp, at, db, mcxt) {
                        Some(v) => return v.inline_metas(at, mcxt, db),
                        None => h,
                    },
                    h => h,
                };
                let sp = sp
                    .into_iter()
                    .map(|e| e.inline_metas(at, mcxt, db))
                    .collect();
                *ty = ty.inline_metas(at, mcxt, db);
                // Reset the Glued in case it has metas inside
                Val::App(h, ty, sp, Glued::new())
            }
            Val::Do(env, v) => {
                let size = env.size;
                let v = v
                    .into_iter()
                    .map(|(d, t)| (d, t.inline_metas(mcxt, size, db)))
                    .collect();
                Val::Do(env, v)
            }
            Val::Clos(t, i, mut cl, effs) => {
                let cl_size = cl.env_size();
                cl.env.inline_metas(mcxt, db);
                cl.term = cl.term.inline_metas(mcxt, cl_size.inc(), db);
                cl.ty = cl.ty.inline_metas(at, mcxt, db);
                let effs = effs
                    .into_iter()
                    .map(|x| x.inline_metas(at, mcxt, db))
                    .collect();
                Val::Clos(t, i, cl, effs)
            }
            Val::Fun(mut from, mut to, effs) => {
                *from = from.inline_metas(at, mcxt, db);
                *to = to.inline_metas(at, mcxt, db);
                let effs = effs
                    .into_iter()
                    .map(|x| x.inline_metas(at, mcxt, db))
                    .collect();
                Val::Fun(from, to, effs)
            }
            Val::Error => Val::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).inline_metas(at, mcxt, db),
        }
    }
}

impl Elim {
    pub fn elim(self, head: Val, mcxt: &MCxt, db: &dyn Compiler) -> Result<Val, (Val, Elim)> {
        match self {
            Elim::App(i, x) => match head {
                Val::Clos(_arg_ty, j, cl, effs) => {
                    assert!(effs.is_empty(), "TODO: effects in evaluator");
                    assert_eq!(i, j);
                    Ok(cl.apply(x, mcxt, db))
                }
                _ => Err((head, Elim::App(i, x))),
            },
            Elim::Case(env, xty, cases, effs, rty) => {
                for (pat, body) in &cases {
                    use crate::pattern::MatchResult::*;
                    match pat.match_with(&head, env.clone(), mcxt, db) {
                        Yes(env) => return Ok(body.clone().evaluate(&env, mcxt, db)),
                        No => continue,
                        Maybe => return Err((head, Elim::Case(env, xty, cases, effs, rty))),
                    }
                }
                unreachable!()
            }
        }
    }

    pub fn inline_metas(self, at: Size, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match self {
            Elim::App(i, x) => Elim::App(i, x.inline_metas(at, mcxt, db)),
            Elim::Case(mut env, mut hty, branches, effs, mut ret_ty) => {
                let env_size = env.size;
                env.inline_metas(mcxt, db);
                let branches = branches
                    .into_iter()
                    .map(|(pat, term)| {
                        let mut env = Env::new(env_size);
                        let mut at = env_size;
                        (
                            pat.eval_quote(&mut env, &mut at, mcxt, db),
                            term.eval_quote(&mut env, at, mcxt, db),
                        )
                    })
                    .collect();
                *hty = hty.inline_metas(mcxt, env_size, db);
                let effs = effs
                    .into_iter()
                    .map(|x| x.inline_metas(mcxt, env_size, db))
                    .collect();
                *ret_ty = ret_ty.inline_metas(mcxt, env_size, db);
                Elim::Case(env, hty, branches, effs, ret_ty)
            }
        }
    }

    pub fn quote(self, head: Term, at: Size, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Elim::App(i, x) => {
                let x = x.quote(at, mcxt, db);
                Term::App(i, Box::new(head), Box::new(x))
            }
            Elim::Case(mut env, mut hty, branches, effs, mut ret_ty) => {
                *hty = hty.eval_quote(&mut env, at, mcxt, db);
                let branches = branches
                    .into_iter()
                    .map(|(pat, term)| {
                        let mut env = env.clone();
                        let mut at = at;
                        (
                            pat.eval_quote(&mut env, &mut at, mcxt, db),
                            term.eval_quote(&mut env, at, mcxt, db),
                        )
                    })
                    .collect();
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(&mut env, at, mcxt, db))
                    .collect();
                *ret_ty = ret_ty.eval_quote(&mut env, at, mcxt, db);
                Term::Case(Box::new(head), hty, branches, effs, ret_ty)
            }
        }
    }
}
