use crate::common::*;
use crate::elaborate::MCxt;
use crate::term::*;

impl Term {
    pub fn evaluate(self, env: &Env, mcxt: &MCxt) -> Val {
        match self {
            Term::Type => Val::Type,
            Term::Var(Var::Local(ix)) => env.val(ix),
            Term::Var(Var::Type(id)) => Val::datatype(id),
            Term::Var(Var::Top(def)) => Val::top(def),
            Term::Var(Var::Rec(id)) => Val::rec(id),
            Term::Var(Var::Meta(meta)) => match mcxt.get_meta(meta) {
                Some(v) => v,
                None => Val::meta(meta),
            },
            Term::Lam(n, icit, ty, body) => Val::Lam(
                icit,
                Box::new(ty.evaluate(env, mcxt)),
                Box::new(Clos(env.clone(), *body, n)),
            ),
            Term::Pi(n, icit, ty, body) => {
                let ty = ty.evaluate(env, mcxt);
                Val::Pi(icit, Box::new(ty), Box::new(Clos(env.clone(), *body, n)))
            }
            Term::Fun(from, to) => {
                let from = from.evaluate(env, mcxt);
                let to = to.evaluate(env, mcxt);
                Val::Fun(Box::new(from), Box::new(to))
            }
            Term::App(icit, f, x) => {
                let f = f.evaluate(env, mcxt);
                let x = x.evaluate(env, mcxt);
                f.app(icit, x, mcxt)
            }
            Term::Error => Val::Error,
        }
    }
}

impl Val {
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
                cl.1 = (*cl)
                    .clone()
                    .vquote(l, mcxt)
                    .force(l, db, mcxt)
                    .quote(l.inc(), mcxt);
                Val::Lam(i, ty, cl)
            }
            Val::Pi(i, mut ty, mut cl) => {
                *ty = ty.force(l, db, mcxt);
                cl.1 = (*cl)
                    .clone()
                    .vquote(l, mcxt)
                    .force(l, db, mcxt)
                    .quote(l.inc(), mcxt);
                Val::Pi(i, ty, cl)
            }
        }
    }

    /// Returns the result of applying `x` to `self`, beta-reducing if necessary.
    pub fn app(self, icit: Icit, x: Val, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, mut sp, _) => {
                sp.push((icit, x));
                // Throw away the old Glued, since that could have been resolved already
                Val::App(h, sp, Glued::new())
            }
            Val::Lam(_, _, cl) => cl.apply(x, mcxt),
            Val::Error => Val::Error,
            Val::Arc(a) => IntoOwned::<Val>::into_owned(a).app(icit, x, mcxt),
            _ => unreachable!(),
        }
    }

    pub fn quote(self, enclosing: Lvl, mcxt: &MCxt) -> Term {
        match self {
            Val::Type => Term::Type,
            Val::App(h, sp, _) => {
                let h = match h {
                    Var::Local(l) => Term::Var(Var::Local(l.to_ix(enclosing))),
                    Var::Top(def) => Term::Var(Var::Top(def)),
                    Var::Meta(meta) => Term::Var(Var::Meta(meta)),
                    Var::Rec(id) => Term::Var(Var::Rec(id)),
                    Var::Type(id) => Term::Var(Var::Type(id)),
                };
                sp.into_iter().fold(h, |f, (icit, x)| {
                    Term::App(icit, Box::new(f), Box::new(x.quote(enclosing, mcxt)))
                })
            }
            Val::Lam(icit, ty, cl) => Term::Lam(
                cl.2,
                icit,
                Box::new(ty.quote(enclosing, mcxt)),
                Box::new(cl.quote(enclosing, mcxt)),
            ),
            Val::Pi(icit, ty, cl) => Term::Pi(
                cl.2,
                icit,
                Box::new(ty.quote(enclosing, mcxt)),
                Box::new(cl.quote(enclosing, mcxt)),
            ),
            Val::Fun(from, to) => Term::Fun(
                Box::new(from.quote(enclosing, mcxt)),
                Box::new(to.quote(enclosing, mcxt)),
            ),
            Val::Error => Term::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).quote(enclosing, mcxt),
        }
    }
}

impl Term {
    pub fn inline_metas(self, mcxt: &MCxt, l: Lvl) -> Self {
        match self {
            Term::Type => Term::Type,
            Term::Var(Var::Meta(m)) => match mcxt.get_meta(m) {
                Some(v) => v.inline_metas(mcxt).quote(l, mcxt),
                None => {
                    println!("[T] Unsolved meta: {:?}", m);
                    Term::Var(Var::Meta(m))
                }
            },
            Term::Var(v) => Term::Var(v),
            Term::Lam(n, i, mut ty, mut t) => {
                // Reuse Boxes
                *ty = ty.inline_metas(mcxt, l);
                *t = t.inline_metas(mcxt, l.inc());
                Term::Lam(n, i, ty, t)
            }
            Term::Pi(n, i, mut from, mut to) => {
                *from = from.inline_metas(mcxt, l);
                *to = to.inline_metas(mcxt, l.inc());
                Term::Pi(n, i, from, to)
            }
            Term::Fun(mut from, mut to) => {
                *from = from.inline_metas(mcxt, l);
                *to = to.inline_metas(mcxt, l);
                Term::Fun(from, to)
            }
            Term::App(i, f, x) => {
                // We have to beta-reduce meta applications
                Term::App(i, f, x)
                    .evaluate(&Env::new(l), mcxt)
                    .inline_metas(mcxt)
                    .quote(l, mcxt)
            }
            Term::Error => Term::Error,
        }
    }
}

impl Val {
    pub fn inline_metas(self, mcxt: &MCxt) -> Self {
        match self {
            Val::Type => Val::Type,
            Val::App(h, sp, g) => {
                let h = match h {
                    Var::Meta(m) => match g.resolve_meta(h, &sp, mcxt) {
                        Some(v) => return v.inline_metas(mcxt),
                        None => {
                            println!("[V] Unsolved meta: {:?}", m);
                            Var::Meta(m)
                        }
                    },
                    h => h,
                };
                let sp = sp
                    .into_iter()
                    .map(|(i, x)| (i, x.inline_metas(mcxt)))
                    .collect();
                // Reset the Glued in case it has metas inside
                Val::App(h, sp, Glued::new())
            }
            Val::Lam(i, mut ty, mut cl) => {
                *ty = ty.inline_metas(mcxt);
                let l = cl.env_size();
                cl.0.inline_metas(mcxt);
                cl.1 = cl.1.inline_metas(mcxt, l.inc());
                Val::Lam(i, ty, cl)
            }
            Val::Pi(i, mut ty, mut cl) => {
                *ty = ty.inline_metas(mcxt);
                let l = cl.env_size();
                cl.0.inline_metas(mcxt);
                cl.1 = cl.1.inline_metas(mcxt, l.inc());
                Val::Pi(i, ty, cl)
            }
            Val::Fun(mut from, mut to) => {
                *from = from.inline_metas(mcxt);
                *to = to.inline_metas(mcxt);
                Val::Fun(from, to)
            }
            Val::Error => Val::Error,
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).inline_metas(mcxt),
        }
    }
}
