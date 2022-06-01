use std::sync::{Arc, RwLock};

use super::*;

#[derive(Debug, Clone)]
pub struct Neutral {
    head: Head<Lvl>,
    spine: Vec<Elim<Val>>,
    unfolded: Arc<RwLock<Option<Val>>>,
}
// Manual impls that ignore the glued unfolded value
impl PartialEq for Neutral {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.spine == other.spine
    }
}
impl Eq for Neutral {}
impl std::hash::Hash for Neutral {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.head.hash(state);
        self.spine.hash(state);
    }
}
impl Neutral {
    pub fn new(head: Head<Lvl>, spine: Vec<Elim<Val>>) -> Neutral {
        Neutral {
            head,
            spine,
            unfolded: Default::default(),
        }
    }

    pub fn head(&self) -> Head<Lvl> {
        self.head
    }

    pub fn spine(&self) -> &Vec<Elim<Val>> {
        &self.spine
    }

    pub fn app(&mut self, x: Elim<Val>) {
        // The glued storage from before no longer applies, create a new one
        self.unfolded = Default::default();
        self.spine.push(x);
    }

    pub fn into_parts(self) -> (Head<Lvl>, Vec<Elim<Val>>) {
        (self.head, self.spine)
    }

    pub fn resolve(self, env: &Env) -> Result<Val, Self> {
        let guard = self.unfolded.read().unwrap();
        if let Some(v) = &*guard {
            Ok(v.clone())
        } else {
            drop(guard);
            // TODO all these
            let head: Val = match self.head {
                Head::Var(Var::Local(_, _)) => return Err(self),
                Head::Var(Var::Builtin(_)) => return Err(self),
                Head::Var(Var::Meta(_)) => return Err(self),
                Head::Var(Var::Def(_)) => return Err(self),
            };
            let mut env = env.clone();
            let mut val = self
                .spine
                .into_iter()
                .fold(head, |head, elim| head.app(elim, &mut env));
            val.inline_head(&mut env);
            let guard = self.unfolded.write().unwrap();
            *guard = Some(val.clone());
            Ok(val)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clos {
    pub class: FunClass,
    pub params: Params<Val>,
    env: Env,
    body: Expr,
}
impl Clos {
    pub fn apply(self, args: Args<Val>) -> Val {
        let Clos { mut env, body, .. } = self;
        // TODO check args against params
        env.extend(args.into_iter().map(Some));
        body.eval(&mut env)
    }

    pub fn quote(self, size: Size) -> Expr {
        let Clos {
            class,
            params,
            mut env,
            body,
        } = self;
        let (args, _) = params.synthesize_args(size);
        let (params, size) = params.quote(size);
        env.extend(args.into_iter().map(Some));
        let body = body.eval(&mut env).quote(size);
        Expr::Fun {
            class,
            params,
            body: Box::new(body),
        }
    }

    pub fn vquote(self, size: Size) -> (Val, Size) {
        let (args, size) = self.params.synthesize_args(size);
        (self.apply(args), size)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Type,
    Neutral(Neutral),
    Fun(Box<Clos>),
    // Do(Vec<Stmt>),
    Lit(Literal),
    Pair(Box<Val>, Box<Val>),
    Error,
}
impl IsTerm for Val {
    type Clos = Clos;
    type Loc = Lvl;
}

impl Val {
    pub fn app(mut self, x: Elim<Val>, env: &mut Env) -> Val {
        match &mut self {
            Val::Neutral(neutral) => {
                neutral.app(x);
                return self;
            }
            Val::Error => return Val::Error,
            _ => (),
        }
        match x {
            Elim::App(args) => match self {
                Val::Fun(clos) => clos.apply(args),
                _ => unreachable!("Cannot resolve application to non-Lam"),
            },
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
    }

    pub fn var(var: Var<Lvl>) -> Self {
        Self::Neutral(Neutral::new(Head::Var(var), Vec::new()))
    }
}

impl Elim<Expr> {
    pub fn eval(self, env: &mut Env) -> Elim<Val> {
        match self {
            Elim::App(arg) => Elim::App(arg.eval(env)),
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
    }
}
impl Elim<Val> {
    pub fn quote(self, size: Size) -> Elim<Expr> {
        match self {
            Elim::App(arg) => Elim::App(arg.quote(size)),
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
    }
}

impl Pat {
    pub fn add_to_env(&self, env: &mut Env) {
        match self {
            Pat::Any => (),
            Pat::Var(_) => env.push(None),
        }
    }
}
impl Pat {
    pub fn add_to_size(&self, size: Size) -> Size {
        match self {
            Pat::Any => size,
            Pat::Var(_) => size.inc(),
        }
    }
}

impl Args<Expr> {
    pub fn eval(self, env: &mut Env) -> Args<Val> {
        let state = env.state();
        let Args { implicit, explicit } = self;
        let implicit = implicit.into_iter().map(|x| x.eval(env)).collect();
        let explicit = explicit.map(|x| Box::new(x.eval(env)));
        env.reset(state);
        Args { implicit, explicit }
    }
}
impl Args<Val> {
    pub fn apply(self, env: &mut Env) {
        for i in self.implicit {
            env.push(Some(i));
        }
        if let Some(a) = self.explicit {
            env.push(Some(*a));
        }
    }

    pub fn quote(self, size: Size) -> Args<Expr> {
        let Args { implicit, explicit } = self;
        let implicit = implicit.into_iter().map(|x| x.quote(size)).collect();
        let explicit = explicit.map(|x| Box::new(x.quote(size)));
        Args { implicit, explicit }
    }
}

impl Params<Expr> {
    /// Does not add anything to the env, only mutates it to keep internal Lvls correct
    pub fn eval(self, env: &mut Env) -> Params<Val> {
        let state = env.state();
        let Params { implicit, explicit } = self;
        let implicit = implicit
            .into_iter()
            .map(|Par { pat, ty }| {
                pat.add_to_env(env);
                Par {
                    pat,
                    ty: ty.eval(env),
                }
            })
            .collect();
        let explicit = explicit.map(|par| {
            let Par { pat, ty } = *par;
            pat.add_to_env(env);
            Box::new(Par {
                pat,
                ty: ty.eval(env),
            })
        });
        env.reset(state);
        Params { implicit, explicit }
    }
}
impl Pat {
    pub fn synthesize_arg(&self, size: Size) -> (Val, Size) {
        match self {
            // TODO is this correct? theoretically in unification this would mean the lambda can't use the param
            // so hopefully the Error should be ignored; but we don't actually check for that?
            Pat::Any => (Val::Error, size),
            Pat::Var(name) => (Val::var(Var::Local(*name, size.next_lvl())), size.inc()),
        }
    }
}
impl Params<Val> {
    pub fn synthesize_args(&self, size: Size) -> (Args<Val>, Size) {
        let Params { implicit, explicit } = self;
        let (implicit, mut size) =
            implicit
                .into_iter()
                .fold((Vec::new(), size), |(mut v, size), Par { pat, ty }| {
                    let (pat, size) = pat.synthesize_arg(size);
                    v.push(pat);
                    (v, size)
                });
        let explicit = explicit.as_ref().map(|par| {
            let Par { pat, .. } = &**par;
            let (pat, size2) = pat.synthesize_arg(size);
            size = size2;
            Box::new(pat)
        });
        (Args { implicit, explicit }, size)
    }

    pub fn quote(self, size: Size) -> (Params<Expr>, Size) {
        let Params { implicit, explicit } = self;
        let (implicit, mut size) =
            implicit
                .into_iter()
                .fold((Vec::new(), size), |(mut v, size), Par { pat, ty }| {
                    let size = pat.add_to_size(size);
                    v.push(Par {
                        pat,
                        ty: ty.quote(size),
                    });
                    (v, size)
                });
        let explicit = explicit.map(|par| {
            let Par { pat, ty } = *par;
            size = pat.add_to_size(size);
            Box::new(Par {
                pat,
                ty: ty.quote(size),
            })
        });
        (Params { implicit, explicit }, size)
    }
}

impl Expr {
    pub fn eval(self, env: &mut Env) -> Val {
        // TODO is there some way to be able to reuse Boxes? Expr and Val should be the same size
        match self {
            Expr::Type => Val::Type,
            Expr::Head(h) => match h {
                Head::Var(Var::Def(d)) => Val::var(Var::Def(d)),
                Head::Var(Var::Local(n, i)) => env.val(n, i),
                Head::Var(Var::Builtin(b)) => Val::var(Var::Builtin(b)),
                Head::Var(Var::Meta(m)) => Val::var(Var::Meta(m)),
            },
            Expr::Elim(x, e) => x.eval(env).app(e.eval(env), env),
            Expr::Fun {
                class,
                params,
                body,
            } => Val::Fun(Box::new(Clos {
                class,
                params: params.eval(env),
                env: env.clone(),
                body: *body,
            })),
            Expr::Lit(l) => Val::Lit(l),
            Expr::Pair(a, b) => Val::Pair(Box::new(a.eval(env)), Box::new(b.eval(env))),
            Expr::Error => Val::Error,
        }
    }
}

impl Val {
    pub fn quote(self, size: Size) -> Expr {
        match self {
            Val::Type => Expr::Type,
            Val::Neutral(neutral) => {
                // Don't resolve the neutral, we want the smallest term when quoting
                // TODO: we may want to inline metas though
                let (head, spine) = neutral.into_parts();
                let head = match head {
                    Head::Var(Var::Def(d)) => Expr::var(Var::Def(d)),
                    Head::Var(Var::Local(n, i)) => Expr::var(Var::Local(n, i.idx(size))),
                    Head::Var(Var::Builtin(b)) => Expr::var(Var::Builtin(b)),
                    Head::Var(Var::Meta(m)) => Expr::var(Var::Meta(m)),
                };
                spine.into_iter().fold(head, |head, elim| {
                    Expr::Elim(Box::new(head), Box::new(elim.quote(size)))
                })
            }
            Val::Fun(clos) => clos.quote(size),
            Val::Lit(_) => todo!(),
            Val::Pair(a, b) => Expr::Pair(Box::new(a.quote(size)), Box::new(b.quote(size))),
            Val::Error => Expr::Error,
        }
    }

    /// Unfolds the head of this value as much as possible, applying eliminators along the way.
    /// Does not recurse over anything - it doesn't affect spines, pairs, etc.
    pub fn inline_head(&mut self, env: &mut Env) {
        match self {
            Val::Neutral(n) => {
                let mut n2 = Neutral::new(Head::Var(Var::Builtin(Builtin::Unit)), Vec::new());
                std::mem::swap(n, &mut n2);
                match n2.resolve(env) {
                    Ok(x) => *self = x,
                    Err(n2) => *n = n2,
                }
            }
            _ => (),
        }
    }
}
