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
                Some(v) => v,
                None => Val::meta(meta, ty.evaluate(env, mcxt, db)),
            },
            Term::Lam(name, icit, ty, body) => Val::Lam(
                icit,
                Box::new(Clos {
                    env: env.clone(),
                    term: *body,
                    ty: ty.evaluate(env, mcxt, db),
                    name,
                }),
            ),
            Term::Pi(name, icit, ty, body, effs) => Val::Pi(
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
            Term::App(icit, f, _fty, x) => {
                let f = f.evaluate(env, mcxt, db);
                let x = x.evaluate(env, mcxt, db);
                f.app(icit, x, mcxt, db)
            }
            Term::Case(x, ty, cases, effs) => {
                let x = x.evaluate(env, mcxt, db);
                for (pat, body) in &cases {
                    use crate::pattern::MatchResult::*;
                    match pat.match_with(&x, env.clone(), mcxt, db) {
                        Yes(env) => return body.clone().evaluate(&env, mcxt, db),
                        No => continue,
                        Maybe => {
                            return Val::Lazy(Box::new(Lazy {
                                env: env.clone(),
                                term: Term::Case(
                                    Box::new(x.quote(env.size, mcxt, db)),
                                    ty,
                                    cases,
                                    effs,
                                ),
                            }))
                        }
                    }
                }
                unreachable!()
            }
            Term::Error => Val::Error,
            Term::If(cond, yes, no) => {
                match cond.evaluate(env, mcxt, db).inline(env.size, db, mcxt) {
                    Val::App(Var::Builtin(Builtin::True), _, _, _) => yes.evaluate(env, mcxt, db),
                    Val::App(Var::Builtin(Builtin::False), _, _, _) => no.evaluate(env, mcxt, db),
                    cond => Val::Lazy(Box::new(Lazy {
                        env: env.clone(),
                        term: Term::If(Box::new(cond.quote(env.size, mcxt, db)), yes, no),
                    })),
                }
            }
            // TODO: eventually we'll want to actually evaluate do blocks when necessary
            term @ Term::Do(_) => Val::Lazy(Box::new(Lazy {
                env: env.clone(),
                term,
            })),
        }
    }

    /// Transfers this term from one context to another; equivalent to calling `term.evaluate(env, ...).quote(l, ...)`
    /// but faster and doesn't cause infinite recursion with `Lazy` values.
    pub fn eval_quote(self, env: &mut Env, l: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Term::Type => Term::Type,
            Term::Lit(l, b) => Term::Lit(l, b),
            Term::Var(Var::Local(ix), ty) => env.val(ix, *ty, mcxt, db).quote(l, mcxt, db),
            Term::Var(Var::Meta(m), mut ty) => match mcxt.get_meta(m) {
                Some(v) => v.quote(l, mcxt, db),
                None => {
                    *ty = ty.eval_quote(env, l, mcxt, db);
                    Term::Var(Var::Meta(m), ty)
                }
            },
            Term::Var(v, mut ty) => {
                *ty = ty.eval_quote(env, l, mcxt, db);
                Term::Var(v, ty)
            }
            Term::Lam(name, icit, mut ty, mut body) => {
                *ty = ty.eval_quote(env, l, mcxt, db);
                env.push(Some(Val::local(
                    l.inc(),
                    ty.clone().evaluate(env, mcxt, db),
                )));
                *body = body.eval_quote(env, l.inc(), mcxt, db);
                env.pop();
                Term::Lam(name, icit, ty, body)
            }
            Term::Pi(name, icit, mut ty, mut body, effs) => {
                let vty = ty.clone().evaluate(env, mcxt, db);
                *ty = ty.eval_quote(env, l, mcxt, db);
                env.push(Some(Val::local(l.inc(), vty)));
                *body = body.eval_quote(env, l.inc(), mcxt, db);
                env.pop();
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, l, mcxt, db))
                    .collect();
                Term::Pi(name, icit, ty, body, effs)
            }
            Term::Fun(mut a, mut b, effs) => {
                *a = a.eval_quote(env, l, mcxt, db);
                *b = b.eval_quote(env, l, mcxt, db);
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, l, mcxt, db))
                    .collect();
                Term::Fun(a, b, effs)
            }
            // We have to perform beta-reduction, so we manually evaluate and then quote again
            Term::App(icit, f, _fty, x) => {
                let f = f.evaluate(env, mcxt, db);
                let x = x.evaluate(env, mcxt, db);
                f.app(icit, x, mcxt, db).quote(l, mcxt, db)
            }
            Term::Case(mut x, mut ty, cases, effs) => {
                let vx = x.evaluate(env, mcxt, db);
                for (pat, body) in &cases {
                    use crate::pattern::MatchResult::*;
                    match pat.match_with(&vx, env.clone(), mcxt, db) {
                        Yes(mut env) => return body.clone().eval_quote(&mut env, l, mcxt, db),
                        No => continue,
                        Maybe => break,
                    }
                }
                *x = vx.quote(l, mcxt, db);
                *ty = ty.eval_quote(env, l, mcxt, db);
                let cases = cases
                    .into_iter()
                    .map(|(pat, body)| {
                        let mut env = env.clone();
                        let mut l = l;
                        let pat = pat.eval_quote(&mut env, &mut l, mcxt, db);
                        let body = body.eval_quote(&mut env, l, mcxt, db);
                        (pat, body)
                    })
                    .collect();
                let effs = effs
                    .into_iter()
                    .map(|x| x.eval_quote(env, l, mcxt, db))
                    .collect();
                Term::Case(x, ty, cases, effs)
            }
            Term::If(mut cond, mut yes, mut no) => match cond
                .evaluate(env, mcxt, db)
                .inline(env.size, db, mcxt)
            {
                Val::App(Var::Builtin(Builtin::True), _, _, _) => yes.eval_quote(env, l, mcxt, db),
                Val::App(Var::Builtin(Builtin::False), _, _, _) => no.eval_quote(env, l, mcxt, db),
                vcond => {
                    *cond = vcond.quote(l, mcxt, db);
                    *yes = yes.eval_quote(env, l, mcxt, db);
                    *no = no.eval_quote(env, l, mcxt, db);
                    Term::If(cond, yes, no)
                }
            },
            Term::Error => Term::Error,
            Term::Do(v) => Term::Do(
                v.into_iter()
                    .map(|(id, term)| (id, term.eval_quote(env, l, mcxt, db)))
                    .collect(),
            ),
        }
    }
}

impl Val {
    /// If self is an App, resolve it recursively; only on the top level.
    pub fn inline(self, l: Lvl, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, hty, sp, g) => {
                if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                    v.inline(l, db, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            // Avoid infinite recursion
            Val::Lazy(cl) => match cl.evaluate(mcxt, db) {
                Val::Lazy(cl) => Val::Lazy(cl),
                v => v.inline(l, db, mcxt),
            },
            Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline(l, db, mcxt),
            x => x,
        }
    }

    /// Inlines Apps to expose Pi or Fun nodes giving it at least `n` arguments.
    /// Panics on failure.
    pub fn inline_args(self, n: usize, l: Lvl, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        if n == 0 {
            self
        } else {
            match self {
                Val::Fun(from, mut to, effs) => {
                    *to = to.inline_args(n - 1, l, db, mcxt);
                    Val::Fun(from, to, effs)
                }
                Val::Pi(i, cl, effs) => {
                    if n == 1 {
                        Val::Pi(i, cl, effs)
                    } else {
                        let name = cl.name;
                        let ty = cl.ty.clone();
                        let term = cl
                            .vquote(l.inc(), mcxt, db)
                            .inline_args(n - 1, l.inc(), db, mcxt)
                            .quote(l.inc(), mcxt, db);
                        Val::Pi(
                            i,
                            Box::new(Clos {
                                env: Env::new(l),
                                term,
                                ty,
                                name,
                            }),
                            effs,
                        )
                    }
                }
                Val::App(h, hty, sp, g) => {
                    if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                        v.inline_args(n, l, db, mcxt)
                    } else {
                        Val::App(h, hty, sp, g)
                    }
                }
                Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline_args(n, l, db, mcxt),
                v => unreachable!("{:?}", v),
            }
        }
    }

    /// Evaluates closures, inlines variables, and calls `force()` recursively, returning a term in normal form.
    /// This should never be used during normal compilation - it's only for benchmarking.
    pub fn force(self, l: Lvl, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::Type => Val::Type,
            Val::Lit(x, t) => Val::Lit(x, t),
            Val::Arc(x) => (*x).clone().force(l, db, mcxt),
            Val::App(h, mut hty, sp, g) => {
                *hty = hty.force(l, db, mcxt);
                if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                    v.force(l, db, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Fun(mut a, mut b, effs) => {
                *a = a.force(l, db, mcxt);
                *b = b.force(l, db, mcxt);
                let effs = effs.into_iter().map(|x| x.force(l, db, mcxt)).collect();
                Val::Fun(a, b, effs)
            }
            Val::Error => Val::Error,

            Val::Lazy(mut cl) => match (*cl).clone().evaluate(mcxt, db) {
                v @ Val::Lazy(_) => v,
                v => {
                    cl.term = v.force(l, db, mcxt).quote(l, mcxt, db);
                    Val::Lazy(cl)
                }
            },
            Val::Lam(i, mut cl) => {
                cl.ty = cl.ty.force(l, db, mcxt);
                cl.term = (*cl)
                    .clone()
                    .vquote(l.inc(), mcxt, db)
                    .force(l.inc(), db, mcxt)
                    .quote(l.inc(), mcxt, db);
                Val::Lam(i, cl)
            }
            Val::Pi(i, mut cl, effs) => {
                cl.ty = cl.ty.force(l, db, mcxt);
                cl.term = (*cl)
                    .clone()
                    .vquote(l.inc(), mcxt, db)
                    .force(l.inc(), db, mcxt)
                    .quote(l.inc(), mcxt, db);
                let effs = effs.into_iter().map(|x| x.force(l, db, mcxt)).collect();
                Val::Pi(i, cl, effs)
            }
        }
    }

    /// Returns the result of applying `x` to `self`, beta-reducing if necessary.
    pub fn app(self, icit: Icit, x: Val, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Val::App(Var::Builtin(b), hty, mut sp, _) if sp.len() == 1 => {
                match b {
                    Builtin::BinOp(op) => {
                        if let Some(v) = op.eval(&sp[0].1, &x) {
                            v
                        } else {
                            sp.push((icit, x));
                            // Throw away the old Glued, since that could have been resolved already
                            Val::App(Var::Builtin(b), hty, sp, Glued::new())
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Val::App(h, hty, mut sp, _) => {
                sp.push((icit, x));
                // Throw away the old Glued, since that could have been resolved already
                Val::App(h, hty, sp, Glued::new())
            }
            Val::Lam(_, cl) => cl.apply(x, mcxt, db),
            Val::Error => Val::Error,
            Val::Arc(a) => IntoOwned::<Val>::into_owned(a).app(icit, x, mcxt, db),
            _ => unreachable!(),
        }
    }

    pub fn quote(self, enclosing: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Val::Type => Term::Type,
            Val::Lit(x, t) => Term::Lit(x, t),
            Val::App(h, hty, sp, g) => {
                // Inline the type to expose the Pi or Fun
                let hty = hty
                    .inline_args(sp.len(), enclosing, db, mcxt)
                    .quote(enclosing, mcxt, db);
                let h = match h {
                    Var::Local(l) => match g.resolve_meta(h, &sp, mcxt, db) {
                        Some(v) => return v.quote(enclosing, mcxt, db),
                        None => Term::Var(Var::Local(l.to_ix(enclosing)), Box::new(hty.clone())),
                    },
                    Var::Top(def) => Term::Var(Var::Top(def), Box::new(hty.clone())),
                    Var::Meta(meta) => match g.resolve_meta(h, &sp, mcxt, db) {
                        Some(v) => return v.quote(enclosing, mcxt, db),
                        None => Term::Var(Var::Meta(meta), Box::new(hty.clone())),
                    },
                    Var::Rec(id) => Term::Var(Var::Rec(id), Box::new(hty.clone())),
                    Var::Type(id, scope) => Term::Var(Var::Type(id, scope), Box::new(hty.clone())),
                    Var::Cons(id) => Term::Var(Var::Cons(id), Box::new(hty.clone())),
                    Var::Builtin(b) => Term::Var(Var::Builtin(b), Box::new(hty.clone())),
                };
                sp.into_iter()
                    .fold((h, hty), |(f, fty), (icit, x)| {
                        let fty = fty.inline_top(db);
                        let rty = match &fty {
                            Term::Fun(_, to, _) => (**to).clone(),
                            Term::Pi(_, _, _, to, _) => {
                                // Peel off one Pi to get the type of the next `f`.
                                // It's dependent, so we need to add `x` to the environment.
                                let mut env = Env::new(enclosing);
                                env.push(Some(x.clone()));
                                // Then we evaluate-quote to so `rty` is in the context `enclosing`.
                                (**to).clone().eval_quote(&mut env, enclosing, mcxt, db)
                            }
                            _ => unreachable!(),
                        };
                        (
                            Term::App(
                                icit,
                                Box::new(f),
                                Box::new(fty),
                                Box::new(x.quote(enclosing, mcxt, db)),
                            ),
                            rty,
                        )
                    })
                    .0
            }
            Val::Lazy(cl) => cl.quote(enclosing, mcxt, db),
            Val::Lam(icit, cl) => Term::Lam(
                cl.name,
                icit,
                Box::new(cl.ty.clone().quote(enclosing, mcxt, db)),
                Box::new(cl.quote(enclosing, mcxt, db)),
            ),
            Val::Pi(icit, cl, effs) => Term::Pi(
                cl.name,
                icit,
                Box::new(cl.ty.clone().quote(enclosing, mcxt, db)),
                Box::new(cl.quote(enclosing, mcxt, db)),
                effs.into_iter()
                    .map(|x| x.quote(enclosing, mcxt, db))
                    .collect(),
            ),
            Val::Fun(from, to, effs) => Term::Fun(
                Box::new(from.quote(enclosing, mcxt, db)),
                Box::new(to.quote(enclosing, mcxt, db)),
                effs.into_iter()
                    .map(|x| x.quote(enclosing, mcxt, db))
                    .collect(),
            ),
            Val::Error => Term::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).quote(enclosing, mcxt, db),
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
    pub fn inline_metas(self, mcxt: &MCxt, l: Lvl, db: &dyn Compiler) -> Self {
        self.eval_quote(&mut Env::new(l), l, mcxt, db)
    }
}

impl Val {
    pub fn inline_metas(self, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match self {
            Val::Type => Val::Type,
            Val::Lit(x, t) => Val::Lit(x, t),
            Val::App(h, mut ty, sp, g) => {
                let h = match h {
                    Var::Meta(_) | Var::Local(_) => match g.resolve_meta(h, &sp, mcxt, db) {
                        Some(v) => return v.inline_metas(mcxt, db),
                        None => h,
                    },
                    h => h,
                };
                let sp = sp
                    .into_iter()
                    .map(|(i, x)| (i, x.inline_metas(mcxt, db)))
                    .collect();
                *ty = ty.inline_metas(mcxt, db);
                // Reset the Glued in case it has metas inside
                Val::App(h, ty, sp, Glued::new())
            }
            Val::Lazy(mut cl) => {
                let l = cl.env_size();
                cl.env.inline_metas(mcxt, db);
                cl.term = cl.term.inline_metas(mcxt, l, db);
                Val::Lazy(cl)
            }
            Val::Lam(i, mut cl) => {
                let l = cl.env_size();
                cl.env.inline_metas(mcxt, db);
                cl.term = cl.term.inline_metas(mcxt, l.inc(), db);
                cl.ty = cl.ty.inline_metas(mcxt, db);
                Val::Lam(i, cl)
            }
            Val::Pi(i, mut cl, effs) => {
                let l = cl.env_size();
                cl.env.inline_metas(mcxt, db);
                cl.term = cl.term.inline_metas(mcxt, l.inc(), db);
                cl.ty = cl.ty.inline_metas(mcxt, db);
                let effs = effs.into_iter().map(|x| x.inline_metas(mcxt, db)).collect();
                Val::Pi(i, cl, effs)
            }
            Val::Fun(mut from, mut to, effs) => {
                *from = from.inline_metas(mcxt, db);
                *to = to.inline_metas(mcxt, db);
                let effs = effs.into_iter().map(|x| x.inline_metas(mcxt, db)).collect();
                Val::Fun(from, to, effs)
            }
            Val::Error => Val::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).inline_metas(mcxt, db),
        }
    }
}
