use crate::common::*;
use crate::elaborate::MCxt;
use crate::term::*;

impl Term {
    pub fn evaluate(self, env: &Env, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Term::Type => Val::Type,
            Term::Var(Var::Local(ix), ty) => env.val(ix, *ty, mcxt, db),
            Term::Var(Var::Type(id, scope), ty) => {
                Val::datatype(id, scope, ty.evaluate(env, mcxt, db))
            }
            Term::Var(Var::Top(def), ty) => Val::top(def, ty.evaluate(env, mcxt, db)),
            Term::Var(Var::Rec(id), ty) => Val::rec(id, ty.evaluate(env, mcxt, db)),
            Term::Var(Var::Cons(id), ty) => Val::cons(id, ty.evaluate(env, mcxt, db)),
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
            Term::Pi(name, icit, ty, body) => Val::Pi(
                icit,
                Box::new(Clos {
                    env: env.clone(),
                    term: *body,
                    ty: ty.evaluate(env, mcxt, db),
                    name,
                }),
            ),
            Term::Fun(from, to) => {
                let from = from.evaluate(env, mcxt, db);
                let to = to.evaluate(env, mcxt, db);
                Val::Fun(Box::new(from), Box::new(to))
            }
            Term::App(icit, f, _fty, x) => {
                let f = f.evaluate(env, mcxt, db);
                let x = x.evaluate(env, mcxt, db);
                f.app(icit, x, mcxt, db)
            }
            Term::Case(x, _, cases) => {
                let x = x.evaluate(env, mcxt, db);
                for (pat, body) in cases {
                    if let Some(env) = pat.match_with(&x, env.clone(), mcxt, db) {
                        return body.evaluate(&env, mcxt, db);
                    }
                }
                unreachable!()
            }
            Term::Error => Val::Error,
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
                Val::Fun(from, mut to) => {
                    *to = to.inline_args(n - 1, l, db, mcxt);
                    Val::Fun(from, to)
                }
                Val::Pi(i, cl) => {
                    if n == 1 {
                        Val::Pi(i, cl)
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
                _ => unreachable!(),
            }
        }
    }

    /// Evaluates closures, inlines variables, and calls `force()` recursively, returning a term in normal form.
    /// This should never be used during normal compilation - it's only for benchmarking.
    pub fn force(self, l: Lvl, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::Type => Val::Type,
            Val::Arc(x) => (*x).clone().force(l, db, mcxt),
            Val::App(h, mut hty, sp, g) => {
                *hty = hty.force(l, db, mcxt);
                if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                    v.force(l, db, mcxt)
                } else {
                    Val::App(h, hty, sp, g)
                }
            }
            Val::Fun(mut a, mut b) => {
                *a = a.force(l, db, mcxt);
                *b = b.force(l, db, mcxt);
                Val::Fun(a, b)
            }
            Val::Error => Val::Error,

            Val::Lam(i, mut cl) => {
                cl.ty = cl.ty.force(l, db, mcxt);
                cl.term =
                    (*cl)
                        .clone()
                        .vquote(l, mcxt, db)
                        .force(l, db, mcxt)
                        .quote(l.inc(), mcxt, db);
                Val::Lam(i, cl)
            }
            Val::Pi(i, mut cl) => {
                cl.ty = cl.ty.force(l, db, mcxt);
                cl.term =
                    (*cl)
                        .clone()
                        .vquote(l, mcxt, db)
                        .force(l, db, mcxt)
                        .quote(l.inc(), mcxt, db);
                Val::Pi(i, cl)
            }
        }
    }

    /// Returns the result of applying `x` to `self`, beta-reducing if necessary.
    pub fn app(self, icit: Icit, x: Val, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
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
            Val::App(h, hty, sp, _) => {
                // Inline the type to expose the Pi or Fun
                let hty = hty
                    .inline_args(sp.len(), enclosing, db, mcxt)
                    .quote(enclosing, mcxt, db);
                let h = match h {
                    Var::Local(l) => {
                        Term::Var(Var::Local(l.to_ix(enclosing)), Box::new(hty.clone()))
                    }
                    Var::Top(def) => Term::Var(Var::Top(def), Box::new(hty.clone())),
                    Var::Meta(meta) => Term::Var(Var::Meta(meta), Box::new(hty.clone())),
                    Var::Rec(id) => Term::Var(Var::Rec(id), Box::new(hty.clone())),
                    Var::Type(id, scope) => Term::Var(Var::Type(id, scope), Box::new(hty.clone())),
                    Var::Cons(id) => Term::Var(Var::Cons(id), Box::new(hty.clone())),
                };
                sp.into_iter()
                    .fold((h, hty), |(f, fty), (icit, x)| {
                        let rty = match &fty {
                            Term::Fun(_, to) => (**to).clone(),
                            Term::Pi(_, _, _, to) => {
                                // Peel off one Pi to get the type of the next `f`.
                                // It's dependent, so we need to add `x` to the environment.
                                let mut env = Env::new(enclosing);
                                env.push(Some(x.clone()));
                                // Then we evaluate-quote to so `rty` is in the context `enclosing`.
                                (**to)
                                    .clone()
                                    .evaluate(&env, mcxt, db)
                                    .quote(enclosing, mcxt, db)
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
            Val::Lam(icit, cl) => Term::Lam(
                cl.name,
                icit,
                Box::new(cl.ty.clone().quote(enclosing, mcxt, db)),
                Box::new(cl.quote(enclosing, mcxt, db)),
            ),
            Val::Pi(icit, cl) => Term::Pi(
                cl.name,
                icit,
                Box::new(cl.ty.clone().quote(enclosing, mcxt, db)),
                Box::new(cl.quote(enclosing, mcxt, db)),
            ),
            Val::Fun(from, to) => Term::Fun(
                Box::new(from.quote(enclosing, mcxt, db)),
                Box::new(to.quote(enclosing, mcxt, db)),
            ),
            Val::Error => Term::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).quote(enclosing, mcxt, db),
        }
    }
}

impl Term {
    /// If self is a Var::Top, inline it (once).
    pub fn inline_top(self, db: &dyn Compiler) -> Term {
        match self {
            Term::Var(Var::Top(id), _) => {
                if let Ok(info) = db.elaborate_def(id) {
                    (*info.term).clone()
                } else {
                    self
                }
            }
            x => x,
        }
    }

    pub fn inline_metas(self, mcxt: &MCxt, l: Lvl, db: &dyn Compiler) -> Self {
        match self {
            Term::Type => Term::Type,
            Term::Var(Var::Meta(m), mut ty) => match mcxt.get_meta(m) {
                Some(v) => v.inline_metas(mcxt, db).quote(l, mcxt, db),
                None => {
                    *ty = ty.inline_metas(mcxt, l, db);
                    Term::Var(Var::Meta(m), ty)
                }
            },
            Term::Var(v, mut ty) => {
                *ty = ty.inline_metas(mcxt, l, db);
                Term::Var(v, ty)
            }
            Term::Lam(n, i, mut ty, mut t) => {
                // Reuse Boxes
                *ty = ty.inline_metas(mcxt, l, db);
                *t = t.inline_metas(mcxt, l.inc(), db);
                Term::Lam(n, i, ty, t)
            }
            Term::Pi(n, i, mut from, mut to) => {
                *from = from.inline_metas(mcxt, l, db);
                *to = to.inline_metas(mcxt, l.inc(), db);
                Term::Pi(n, i, from, to)
            }
            Term::Fun(mut from, mut to) => {
                *from = from.inline_metas(mcxt, l, db);
                *to = to.inline_metas(mcxt, l, db);
                Term::Fun(from, to)
            }
            Term::App(i, f, fty, x) => {
                // We have to beta-reduce meta applications
                Term::App(i, f, fty, x)
                    .evaluate(&Env::new(l), mcxt, db)
                    .inline_metas(mcxt, db)
                    .quote(l, mcxt, db)
            }
            Term::Case(mut x, mut ty, cases) => {
                *x = x.inline_metas(mcxt, l, db);
                *ty = ty.inline_metas(mcxt, l, db);
                let cases = cases
                    .into_iter()
                    .map(|(p, x)| (p.inline_metas(mcxt, db), x.inline_metas(mcxt, l, db)))
                    .collect();
                Term::Case(x, ty, cases)
            }
            Term::Error => Term::Error,
        }
    }
}

impl Val {
    pub fn inline_metas(self, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match self {
            Val::Type => Val::Type,
            Val::App(h, mut ty, sp, g) => {
                let h = match h {
                    Var::Meta(m) => match g.resolve_meta(h, &sp, mcxt, db) {
                        Some(v) => return v.inline_metas(mcxt, db),
                        None => Var::Meta(m),
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
            Val::Lam(i, mut cl) => {
                let l = cl.env_size();
                cl.env.inline_metas(mcxt, db);
                cl.term = cl.term.inline_metas(mcxt, l.inc(), db);
                cl.ty = cl.ty.inline_metas(mcxt, db);
                Val::Lam(i, cl)
            }
            Val::Pi(i, mut cl) => {
                let l = cl.env_size();
                cl.env.inline_metas(mcxt, db);
                cl.term = cl.term.inline_metas(mcxt, l.inc(), db);
                cl.ty = cl.ty.inline_metas(mcxt, db);
                Val::Pi(i, cl)
            }
            Val::Fun(mut from, mut to) => {
                *from = from.inline_metas(mcxt, db);
                *to = to.inline_metas(mcxt, db);
                Val::Fun(from, to)
            }
            Val::Error => Val::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).inline_metas(mcxt, db),
        }
    }
}
