use crate::common::*;
use crate::elaborate::MCxt;
use crate::term::*;

impl Term {
    pub fn evaluate(self, env: &Env, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Term::Type => Val::Type,
            Term::Var(Var::Local(ix)) => env.val(ix),
            Term::Var(Var::Type(id, scope)) => Val::datatype(id, scope),
            Term::Var(Var::Top(def)) => Val::top(def),
            Term::Var(Var::Rec(id)) => Val::rec(id),
            Term::Var(Var::Cons(id)) => Val::cons(id),
            Term::Var(Var::Meta(meta)) => match mcxt.get_meta(meta) {
                Some(v) => v,
                None => Val::meta(meta),
            },
            Term::Lam(n, icit, ty, body) => Val::Lam(
                icit,
                Box::new(ty.evaluate(env, mcxt, db)),
                Box::new(Clos(env.clone(), *body, n)),
            ),
            Term::Pi(n, icit, ty, body) => {
                let ty = ty.evaluate(env, mcxt, db);
                Val::Pi(icit, Box::new(ty), Box::new(Clos(env.clone(), *body, n)))
            }
            Term::Fun(from, to) => {
                let from = from.evaluate(env, mcxt, db);
                let to = to.evaluate(env, mcxt, db);
                Val::Fun(Box::new(from), Box::new(to))
            }
            Term::App(icit, f, x) => {
                let f = f.evaluate(env, mcxt, db);
                let x = x.evaluate(env, mcxt, db);
                f.app(icit, x, mcxt, db)
            }
            Term::Case(x, cases) => {
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
            Val::App(h, sp, g) => {
                if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                    v.inline(l, db, mcxt)
                } else {
                    Val::App(h, sp, g)
                }
            }
            Val::Arc(v) => IntoOwned::<Val>::into_owned(v).inline(l, db, mcxt),
            x => x,
        }
    }

    /// Evaluates closures, inlines variables, and calls `force()` recursively, returning a term in normal form.
    /// This should never be used during normal compilation - it's only for benchmarking.
    pub fn force(self, l: Lvl, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::Type => Val::Type,
            Val::Arc(x) => (*x).clone().force(l, db, mcxt),
            Val::App(h, sp, g) => {
                if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                    v.force(l, db, mcxt)
                } else {
                    Val::App(h, sp, g)
                }
            }
            Val::Fun(mut a, mut b) => {
                *a = a.force(l, db, mcxt);
                *b = b.force(l, db, mcxt);
                Val::Fun(a, b)
            }
            Val::Error => Val::Error,

            Val::Lam(i, mut ty, mut cl) => {
                *ty = ty.force(l, db, mcxt);
                cl.1 =
                    (*cl)
                        .clone()
                        .vquote(l, mcxt, db)
                        .force(l, db, mcxt)
                        .quote(l.inc(), mcxt, db);
                Val::Lam(i, ty, cl)
            }
            Val::Pi(i, mut ty, mut cl) => {
                *ty = ty.force(l, db, mcxt);
                cl.1 =
                    (*cl)
                        .clone()
                        .vquote(l, mcxt, db)
                        .force(l, db, mcxt)
                        .quote(l.inc(), mcxt, db);
                Val::Pi(i, ty, cl)
            }
        }
    }

    /// Returns the result of applying `x` to `self`, beta-reducing if necessary.
    pub fn app(self, icit: Icit, x: Val, mcxt: &MCxt, db: &dyn Compiler) -> Val {
        match self {
            Val::App(h, mut sp, _) => {
                sp.push((icit, x));
                // Throw away the old Glued, since that could have been resolved already
                Val::App(h, sp, Glued::new())
            }
            Val::Lam(_, _, cl) => cl.apply(x, mcxt, db),
            Val::Error => Val::Error,
            Val::Arc(a) => IntoOwned::<Val>::into_owned(a).app(icit, x, mcxt, db),
            _ => unreachable!(),
        }
    }

    pub fn quote(self, enclosing: Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Term {
        match self {
            Val::Type => Term::Type,
            Val::App(h, sp, _) => {
                let h = match h {
                    Var::Local(l) => Term::Var(Var::Local(l.to_ix(enclosing))),
                    Var::Top(def) => Term::Var(Var::Top(def)),
                    Var::Meta(meta) => Term::Var(Var::Meta(meta)),
                    Var::Rec(id) => Term::Var(Var::Rec(id)),
                    Var::Type(id, scope) => Term::Var(Var::Type(id, scope)),
                    Var::Cons(id) => Term::Var(Var::Cons(id)),
                };
                sp.into_iter().fold(h, |f, (icit, x)| {
                    Term::App(icit, Box::new(f), Box::new(x.quote(enclosing, mcxt, db)))
                })
            }
            Val::Lam(icit, ty, cl) => Term::Lam(
                cl.2,
                icit,
                Box::new(ty.quote(enclosing, mcxt, db)),
                Box::new(cl.quote(enclosing, mcxt, db)),
            ),
            Val::Pi(icit, ty, cl) => Term::Pi(
                cl.2,
                icit,
                Box::new(ty.quote(enclosing, mcxt, db)),
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
            Term::Var(Var::Top(id)) => {
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
            Term::Var(Var::Meta(m)) => match mcxt.get_meta(m) {
                Some(v) => v.inline_metas(mcxt, db).quote(l, mcxt, db),
                None => Term::Var(Var::Meta(m)),
            },
            Term::Var(v) => Term::Var(v),
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
            Term::App(i, f, x) => {
                // We have to beta-reduce meta applications
                Term::App(i, f, x)
                    .evaluate(&Env::new(l), mcxt, db)
                    .inline_metas(mcxt, db)
                    .quote(l, mcxt, db)
            }
            Term::Case(mut x, cases) => {
                *x = x.inline_metas(mcxt, l, db);
                let cases = cases
                    .into_iter()
                    .map(|(p, x)| (p.inline_metas(mcxt, db), x.inline_metas(mcxt, l, db)))
                    .collect();
                Term::Case(x, cases)
            }
            Term::Error => Term::Error,
        }
    }
}

impl Val {
    pub fn inline_metas(self, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match self {
            Val::Type => Val::Type,
            Val::App(h, sp, g) => {
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
                // Reset the Glued in case it has metas inside
                Val::App(h, sp, Glued::new())
            }
            Val::Lam(i, mut ty, mut cl) => {
                *ty = ty.inline_metas(mcxt, db);
                let l = cl.env_size();
                cl.0.inline_metas(mcxt, db);
                cl.1 = cl.1.inline_metas(mcxt, l.inc(), db);
                Val::Lam(i, ty, cl)
            }
            Val::Pi(i, mut ty, mut cl) => {
                *ty = ty.inline_metas(mcxt, db);
                let l = cl.env_size();
                cl.0.inline_metas(mcxt, db);
                cl.1 = cl.1.inline_metas(mcxt, l.inc(), db);
                Val::Pi(i, ty, cl)
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
