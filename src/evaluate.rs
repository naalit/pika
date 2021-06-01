use crate::common::*;
use crate::elaborate::MCxt;
use crate::term::*;

impl Term {
    pub fn evaluate(self, env: &Env, mcxt: &MCxt) -> Val {
        match self {
            Term::Type => Val::Type,
            Term::Lit(x, t) => Val::Lit(x, t),
            Term::Var(Var::Local(ix), ty) => env.val(ix, *ty, mcxt),
            Term::Var(Var::Type(id, scope), ty) => Val::datatype(id, scope, ty.evaluate(env, mcxt)),
            Term::Var(Var::Top(def), ty) => Val::top(def, ty.evaluate(env, mcxt)),
            Term::Var(Var::Rec(id), ty) => Val::rec(id, ty.evaluate(env, mcxt)),
            Term::Var(Var::Cons(id), ty) => Val::cons(id, ty.evaluate(env, mcxt)),
            Term::Var(Var::File(id), ty) => Val::file(id, ty.evaluate(env, mcxt)),
            Term::Var(Var::Builtin(b), ty) => Val::builtin(b, ty.evaluate(env, mcxt)),
            Term::Var(Var::Meta(meta), ty) => match mcxt.get_meta(meta) {
                Some(v) => v.evaluate(env, mcxt),
                None => Val::meta(meta, ty.evaluate(env, mcxt)),
            },
            Term::Clos(t, name, icit, ty, body, effs) => Val::Clos(
                t,
                icit,
                Box::new(Clos {
                    env: env.clone(),
                    term: *body,
                    ty: ty.evaluate(env, mcxt),
                    name,
                }),
                effs.into_iter().map(|x| x.evaluate(env, mcxt)).collect(),
            ),
            Term::Fun(from, to, effs) => {
                let from = from.evaluate(env, mcxt);
                let to = to.evaluate(env, mcxt);
                let effs = effs.into_iter().map(|x| x.evaluate(env, mcxt)).collect();
                Val::Fun(Box::new(from), Box::new(to), effs)
            }
            Term::App(icit, f, x) => {
                let f = f.evaluate(env, mcxt);
                let x = x.evaluate(env, mcxt);
                f.app(Elim::App(icit, x), mcxt)
            }
            Term::Case(x, ty, cases, effs, rty) => {
                let x = x.evaluate(env, mcxt);
                x.app(Elim::Case(env.clone(), ty, cases, effs, rty), mcxt)
            }
            Term::Do(v) => Val::Do(env.clone(), v),
            Term::Struct(k, v) => Val::Struct(
                match k {
                    StructKind::Struct(t) => StructKind::Struct(Box::new(t.evaluate(env, mcxt))),
                    StructKind::Sig => StructKind::Sig,
                },
                v.into_iter()
                    .map(|(d, n, t)| (d, n, t.evaluate(env, mcxt)))
                    .collect(),
            ),
            Term::Dot(x, m) => x.evaluate(env, mcxt).app(Elim::Dot(m), mcxt),
        }
    }

    /// Transfers this term from one context to another; equivalent to calling `term.evaluate(env, ...).quote(l, ...)`
    /// but faster and doesn't cause infinite recursion with `Lazy` values.
    pub fn eval_quote(self, env: &mut Env, at: Size, mcxt: &MCxt) -> Term {
        match self {
            Term::Type => Term::Type,
            Term::Lit(l, b) => Term::Lit(l, b),
            Term::Var(Var::Local(ix), ty) => env.val(ix, *ty, mcxt).quote(at, mcxt),
            Term::Var(Var::Meta(m), mut ty) => match mcxt.get_meta(m) {
                Some(v) => v.eval_quote(env, at, mcxt),
                None => {
                    *ty = ty.eval_quote(env, at, mcxt);
                    Term::Var(Var::Meta(m), ty)
                }
            },
            Term::Var(v, mut ty) => {
                *ty = ty.eval_quote(env, at, mcxt);
                Term::Var(v, ty)
            }
            Term::Clos(t, name, icit, mut ty, mut body, effs) => {
                let vty = ty.clone().evaluate(env, mcxt);
                *ty = ty.eval_quote(env, at, mcxt);

                env.push(Some(Val::local(at.next_lvl(), vty)));
                *body = body.eval_quote(env, at.inc(), mcxt);
                env.pop();

                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, at, mcxt))
                    .collect();
                Term::Clos(t, name, icit, ty, body, effs)
            }
            Term::Fun(mut a, mut b, effs) => {
                *a = a.eval_quote(env, at, mcxt);
                *b = b.eval_quote(env, at, mcxt);
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, at, mcxt))
                    .collect();
                Term::Fun(a, b, effs)
            }
            // We have to perform beta-reduction, so we manually evaluate and then quote again
            Term::App(icit, mut f, mut x) => {
                *f = f.eval_quote(env, at, mcxt);
                match *f {
                    Term::Clos(Lam, _n, _i, _ty, body, _effs) => {
                        let x = x.evaluate(env, mcxt);
                        env.push(Some(x));
                        let b = body.eval_quote(env, at, mcxt);
                        env.pop();
                        b
                    }
                    _ => {
                        // No beta reduction necessary
                        *x = x.eval_quote(env, at, mcxt);
                        Term::App(icit, f, x)
                    }
                }
            }
            Term::Case(mut x, mut ty, cases, effs, mut rty) => {
                let vx = x.evaluate(env, mcxt);
                for (pat, body) in &cases {
                    use crate::pattern::MatchResult::*;
                    match pat.match_with(&vx, env.clone(), mcxt) {
                        Yes(mut env) => return body.clone().eval_quote(&mut env, at, mcxt),
                        No => continue,
                        Maybe => break,
                    }
                }
                *x = vx.quote(at, mcxt);
                *ty = ty.eval_quote(env, at, mcxt);
                *rty = rty.eval_quote(env, at, mcxt);
                let cases = cases
                    .into_iter()
                    .map(|(pat, body)| {
                        let mut env = env.clone();
                        let mut at = at;
                        let pat = pat.eval_quote(&mut env, &mut at, mcxt);
                        let body = body.eval_quote(&mut env, at, mcxt);
                        (pat, body)
                    })
                    .collect();
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, at, mcxt))
                    .collect();
                Term::Case(x, ty, cases, effs, rty)
            }
            Term::Do(v) => Term::Do(
                v.into_iter()
                    .map(|(id, term)| (id, term.eval_quote(env, at, mcxt)))
                    .collect(),
            ),
            Term::Struct(k, v) => Term::Struct(
                match k {
                    StructKind::Struct(t) => {
                        StructKind::Struct(Box::new(t.eval_quote(env, at, mcxt)))
                    }
                    StructKind::Sig => StructKind::Sig,
                },
                v.into_iter()
                    .map(|(d, n, t)| (d, n, t.eval_quote(env, at, mcxt)))
                    .collect(),
            ),
            Term::Dot(mut x, m) => {
                *x = x.eval_quote(env, at, mcxt);
                Term::Dot(x, m)
            }
        }
    }
}

impl Val {
    /// If self is an App, resolve it recursively; only on the top level.
    pub fn inline(self, at: Size, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, hty, sp, g) => {
                if let Some(v) = g.resolve(h, &sp, at, mcxt) {
                    v.inline(at, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline(at, mcxt),
            x => x,
        }
    }

    /// Inlines Apps to expose Pi or Fun nodes giving it at least `n` arguments.
    /// Panics on failure.
    pub fn inline_args(self, n: usize, at: Size, mcxt: &MCxt) -> Val {
        if n == 0 {
            self
        } else {
            match self {
                Val::Fun(from, mut to, effs) => {
                    *to = to.inline_args(n - 1, at, mcxt);
                    Val::Fun(from, to, effs)
                }
                Val::Clos(Pi, i, cl, effs) => {
                    if n == 1 {
                        Val::Clos(Pi, i, cl, effs)
                    } else {
                        let name = cl.name;
                        let ty = cl.ty.clone();
                        let term = cl
                            .vquote(at, mcxt)
                            .inline_args(n - 1, at.inc(), mcxt)
                            .quote(at.inc(), mcxt);
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
                    if let Some(v) = g.resolve(h, &sp, at, mcxt) {
                        v.inline_args(n, at, mcxt)
                    } else {
                        Val::App(h, hty, sp, g)
                    }
                }
                Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline_args(n, at, mcxt),
                v => unreachable!("{:?}", v),
            }
        }
    }

    /// Evaluates closures, inlines variables, and calls `force()` recursively, returning a term in normal form.
    /// This should never be used during normal compilation - it's only for benchmarking.
    pub fn force(self, at: Size, mcxt: &MCxt) -> Val {
        match self {
            Val::Type => Val::Type,
            Val::Lit(x, t) => Val::Lit(x, t),
            Val::Arc(x) => (*x).clone().force(at, mcxt),
            Val::App(h, mut hty, sp, g) => {
                *hty = hty.force(at, mcxt);
                if let Some(v) = g.resolve(h, &sp, at, mcxt) {
                    v.force(at, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Fun(mut a, mut b, effs) => {
                *a = a.force(at, mcxt);
                *b = b.force(at, mcxt);
                let effs = effs.into_iter().map(|x| x.force(at, mcxt)).collect();
                Val::Fun(a, b, effs)
            }
            Val::Do(env, v) => {
                let v = v
                    .into_iter()
                    .map(|(d, x)| {
                        (
                            d,
                            x.evaluate(&env, mcxt)
                                .force(env.size, mcxt)
                                .quote(env.size, mcxt),
                        )
                    })
                    .collect();
                Val::Do(env, v)
            }
            Val::Struct(k, v) => Val::Struct(
                match k {
                    StructKind::Struct(t) => StructKind::Struct(Box::new(t.force(at, mcxt))),
                    StructKind::Sig => StructKind::Sig,
                },
                v.into_iter()
                    .map(|(d, n, t)| (d, n, t.force(at, mcxt)))
                    .collect(),
            ),
            Val::Clos(t, i, mut cl, effs) => {
                cl.ty = cl.ty.force(at, mcxt);
                cl.term = (*cl)
                    .clone()
                    .vquote(at, mcxt)
                    .force(at.inc(), mcxt)
                    .quote(at.inc(), mcxt);
                let effs = effs.into_iter().map(|x| x.force(at, mcxt)).collect();
                Val::Clos(t, i, cl, effs)
            }
        }
    }

    /// Returns the result of applying `x` to `self`, beta-reducing if necessary.
    pub fn app(self, elim: Elim, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, hty, mut sp, g) => {
                if sp.is_empty() {
                    match elim.elim(Val::App(h, hty, sp, g), mcxt) {
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
                } else if sp.len() == 1 {
                    match (h, &sp[0], &elim) {
                        (Var::Builtin(Builtin::BinOp(op)), Elim::App(_, a), Elim::App(_, b)) => {
                            if let Some(v) = op.eval(a, b) {
                                v
                            } else {
                                sp.push(elim);
                                Val::App(h, hty, sp, g)
                            }
                        }
                        _ => {
                            sp.push(elim);
                            Val::App(h, hty, sp, g)
                        }
                    }
                } else {
                    sp.push(elim);
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Arc(a) => IntoOwned::<Val>::into_owned(a).app(elim, mcxt),
            x => match elim.elim(x, mcxt) {
                Ok(v) => v,
                Err((v, e)) => panic!(
                    "Error during evaluation: couldn't apply eliminator {:?} to value {:?}",
                    e, v
                ),
            },
        }
    }

    pub fn quote(self, at: Size, mcxt: &MCxt) -> Term {
        match self {
            Val::Type => Term::Type,
            Val::Lit(x, t) => Term::Lit(x, t),
            Val::App(h, hty, sp, g) => {
                let hty = hty.quote(at, mcxt);
                let h = match h {
                    Var::Local(l) => match g.resolve(h, &sp, at, mcxt) {
                        Some(v) => return v.quote(at, mcxt),
                        None => Term::Var(Var::Local(at.to_ix(l)), Box::new(hty)),
                    },
                    Var::Top(def) => Term::Var(Var::Top(def), Box::new(hty)),
                    Var::Meta(meta) => match g.resolve(h, &sp, at, mcxt) {
                        Some(v) => return v.quote(at, mcxt),
                        None => Term::Var(Var::Meta(meta), Box::new(hty)),
                    },
                    Var::Rec(id) => Term::Var(Var::Rec(id), Box::new(hty)),
                    Var::Type(id, scope) => Term::Var(Var::Type(id, scope), Box::new(hty)),
                    Var::Cons(id) => Term::Var(Var::Cons(id), Box::new(hty)),
                    Var::File(id) => Term::Var(Var::File(id), Box::new(hty)),
                    Var::Builtin(b) => Term::Var(Var::Builtin(b), Box::new(hty)),
                };
                sp.into_iter()
                    .fold(h, |head, elim| elim.quote(head, at, mcxt))
            }
            Val::Do(mut env, v) => Term::Do(
                v.into_iter()
                    .map(|(d, t)| (d, t.eval_quote(&mut env, at, mcxt)))
                    .collect(),
            ),
            Val::Struct(k, v) => Term::Struct(
                match k {
                    StructKind::Struct(t) => StructKind::Struct(Box::new(t.quote(at, mcxt))),
                    StructKind::Sig => StructKind::Sig,
                },
                v.into_iter()
                    .map(|(d, n, t)| (d, n, t.quote(at, mcxt)))
                    .collect(),
            ),
            Val::Clos(t, icit, cl, effs) => Term::Clos(
                t,
                cl.name,
                icit,
                Box::new(cl.ty.clone().quote(at, mcxt)),
                Box::new(cl.quote(at, mcxt)),
                effs.into_iter().map(|x| x.quote(at, mcxt)).collect(),
            ),
            Val::Fun(from, to, effs) => Term::Fun(
                Box::new(from.quote(at, mcxt)),
                Box::new(to.quote(at, mcxt)),
                effs.into_iter().map(|x| x.quote(at, mcxt)).collect(),
            ),
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).quote(at, mcxt),
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
    pub fn inline_top(self, mcxt: &MCxt) -> Term {
        match self {
            Term::Var(Var::Top(id), _) => {
                if let Some(t) = mcxt.def_term(id) {
                    t.inline_top(mcxt)
                } else {
                    self
                }
            }
            x => x,
        }
    }

    /// Shorthand for `eval_quote()` without changing levels
    pub fn inline_metas(self, mcxt: &MCxt, at: Size) -> Self {
        self.eval_quote(&mut Env::new(at), at, mcxt)
    }
}

impl Val {
    pub fn inline_metas(self, at: Size, mcxt: &MCxt) -> Self {
        match self {
            Val::Type => Val::Type,
            Val::Lit(x, t) => Val::Lit(x, t),
            Val::App(h, mut ty, sp, g) => {
                let h = match h {
                    Var::Meta(_) | Var::Local(_) => match g.resolve(h, &sp, at, mcxt) {
                        Some(v) => return v.inline_metas(at, mcxt),
                        None => h,
                    },
                    h => h,
                };
                let sp = sp.into_iter().map(|e| e.inline_metas(at, mcxt)).collect();
                *ty = ty.inline_metas(at, mcxt);
                // Reset the Glued in case it has metas inside
                Val::App(h, ty, sp, Glued::new())
            }
            Val::Do(env, v) => {
                let size = env.size;
                let v = v
                    .into_iter()
                    .map(|(d, t)| (d, t.inline_metas(mcxt, size)))
                    .collect();
                Val::Do(env, v)
            }
            Val::Struct(k, v) => Val::Struct(
                match k {
                    StructKind::Struct(t) => StructKind::Struct(Box::new(t.inline_metas(at, mcxt))),
                    StructKind::Sig => StructKind::Sig,
                },
                v.into_iter()
                    .map(|(d, n, t)| (d, n, t.inline_metas(at, mcxt)))
                    .collect(),
            ),
            Val::Clos(t, i, mut cl, effs) => {
                let cl_size = cl.env_size();
                cl.env.inline_metas(mcxt);
                cl.term = cl.term.inline_metas(mcxt, cl_size.inc());
                cl.ty = cl.ty.inline_metas(at, mcxt);
                let effs = effs.into_iter().map(|x| x.inline_metas(at, mcxt)).collect();
                Val::Clos(t, i, cl, effs)
            }
            Val::Fun(mut from, mut to, effs) => {
                *from = from.inline_metas(at, mcxt);
                *to = to.inline_metas(at, mcxt);
                let effs = effs.into_iter().map(|x| x.inline_metas(at, mcxt)).collect();
                Val::Fun(from, to, effs)
            }
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).inline_metas(at, mcxt),
        }
    }
}

impl Elim {
    pub fn elim(self, head: Val, mcxt: &MCxt) -> Result<Val, (Val, Elim)> {
        match self {
            Elim::App(i, x) => match head {
                Val::Clos(_arg_ty, j, cl, effs) => {
                    assert!(effs.is_empty(), "TODO: effects in evaluator");
                    assert_eq!(i, j);
                    Ok(cl.apply(x, mcxt))
                }
                _ => Err((head, Elim::App(i, x))),
            },
            Elim::Case(env, xty, cases, effs, rty) => {
                for (pat, body) in &cases {
                    use crate::pattern::MatchResult::*;
                    match pat.match_with(&head, env.clone(), mcxt) {
                        Yes(env) => return Ok(body.clone().evaluate(&env, mcxt)),
                        No => continue,
                        Maybe => return Err((head, Elim::Case(env, xty, cases, effs, rty))),
                    }
                }
                unreachable!()
            }
            Elim::Dot(m) => match head {
                Val::Struct(StructKind::Struct(_), v) => v
                    .into_iter()
                    .find(|(_, n, _)| m == *n)
                    .map(|(_, _, x)| Ok(x))
                    .unwrap(),
                _ => Err((head, Elim::Dot(m))),
            },
        }
    }

    pub fn inline_metas(self, at: Size, mcxt: &MCxt) -> Self {
        match self {
            Elim::App(i, x) => Elim::App(i, x.inline_metas(at, mcxt)),
            Elim::Case(mut env, mut hty, branches, effs, mut ret_ty) => {
                let env_size = env.size;
                env.inline_metas(mcxt);
                let branches = branches
                    .into_iter()
                    .map(|(pat, term)| {
                        let mut env = Env::new(env_size);
                        let mut at = env_size;
                        (
                            pat.eval_quote(&mut env, &mut at, mcxt),
                            term.eval_quote(&mut env, at, mcxt),
                        )
                    })
                    .collect();
                *hty = hty.inline_metas(mcxt, env_size);
                let effs = effs
                    .into_iter()
                    .map(|x| x.inline_metas(mcxt, env_size))
                    .collect();
                *ret_ty = ret_ty.inline_metas(mcxt, env_size);
                Elim::Case(env, hty, branches, effs, ret_ty)
            }
            Elim::Dot(m) => Elim::Dot(m),
        }
    }

    pub fn quote(self, head: Term, at: Size, mcxt: &MCxt) -> Term {
        match self {
            Elim::App(i, x) => {
                let x = x.quote(at, mcxt);
                Term::App(i, Box::new(head), Box::new(x))
            }
            Elim::Case(mut env, mut hty, branches, effs, mut ret_ty) => {
                *hty = hty.eval_quote(&mut env, at, mcxt);
                let branches = branches
                    .into_iter()
                    .map(|(pat, term)| {
                        let mut env = env.clone();
                        let mut at = at;
                        (
                            pat.eval_quote(&mut env, &mut at, mcxt),
                            term.eval_quote(&mut env, at, mcxt),
                        )
                    })
                    .collect();
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(&mut env, at, mcxt))
                    .collect();
                *ret_ty = ret_ty.eval_quote(&mut env, at, mcxt);
                Term::Case(Box::new(head), hty, branches, effs, ret_ty)
            }
            Elim::Dot(m) => Term::Dot(Box::new(head), m),
        }
    }
}
