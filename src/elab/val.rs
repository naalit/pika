use super::*;

#[derive(Clone)]
pub struct Clos {
    env: Env,
    body: Expr,
}
#[derive(Clone)]
pub enum Val {
    Type,
    Neutral(Head<Lvl>, Vec<Elim<Val>>),
    Fun {
        class: FunClass,
        params: Params<Val>,
        body: Box<Clos>,
    },
    // Do(Vec<Stmt>),
    Lit(Literal),
    Sigma {
        left_ty: Box<Val>,
        left_name: Option<Name>,
        /// Has the left value in scope
        right_ty: Box<Clos>,
        right_name: Option<Name>,
    },
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
            Val::Neutral(_, spine) => {
                spine.push(x);
                return self;
            }
            Val::Error => return Val::Error,
            _ => (),
        }
        match x {
            Elim::App(args) => match self {
                Val::Fun {
                    class: Lam,
                    params: _,
                    body,
                } => {
                    let Clos {
                        mut env,
                        body,
                    } = *body;
                    args.apply(&mut env);
                    body.eval(&mut env)
                },
                _ => unreachable!("Cannot resolve application to non-Lam"),
            },
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
    }

    pub fn var(var: Var<Lvl>) -> Self {
        Self::Neutral(Head::Var(var), Vec::new())
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

impl Pat<Expr> {
    pub fn eval_and_bind(self, env: &mut Env) -> Pat<Val> {
        match self {
            Pat::Any => Pat::Any,
            Pat::Var { name, ty } => {
                env.push(None);
                Pat::Var { name, ty: ty.eval(env) }
            },
        }
    }
}

impl Args<Expr> {
    pub fn eval(self, env: &mut Env) -> Args<Val> {
        let state = env.state();
        let Args {
            implicit,
            explicit,
        } = self;
        let implicit = implicit.into_iter().map(|x| x.eval(env)).collect();
        let explicit = explicit.map(|x| Box::new(x.eval(env)));
        env.reset(state);
        Args {
            implicit,
            explicit,
        }
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
}

impl Params<Expr> {
    /// Does not add anything to the env, only mutates it to keep internal Lvls correct
    pub fn eval(self, env: &mut Env) -> Params<Val> {
        let state = env.state();
        let Params {
            implicit,
            explicit,
        } = self;
        let implicit = implicit.into_iter().map(|Par { pat, ty }| {
            Par {
                pat: pat.eval_and_bind(env),
                ty: ty.eval(env),
            }
        }).collect();
        let explicit = explicit.map(|par| {
            let Par { pat, ty } = *par;
            Box::new(Par {
                pat: pat.eval_and_bind(env),
                ty: ty.eval(env),
            })
        });
        env.reset(state);
        Params {
            implicit,
            explicit,
        }
    }
}

impl Expr {
    pub fn eval(self, env: &mut Env) -> Val {
        // TODO is there some way to be able to reuse Boxes? Expr and Val should be the same size
        match self {
            Expr::Type => Val::Type,
            Expr::Head(h) => match h {
                Head::Var(Var::Def()) => Val::var(Var::Def()),
                Head::Var(Var::Local(i)) => env.val(i),
                Head::Var(Var::Builtin(b)) => Val::var(Var::Builtin(b)),
                Head::Var(Var::Meta(m)) => Val::var(Var::Meta(m)),
            },
            Expr::Elim(x, e) => x.eval(env).app(e.eval(env), env),
            Expr::Fun {
                class,
                params,
                body,
            } => Val::Fun {
                class,
                params: params.eval(env),
                body: Box::new(Clos {
                    env: env.clone(),
                    body: *body,
                }),
            },
            Expr::Lit(l) => Val::Lit(l),
            Expr::Sigma {
                left_ty,
                left_name,
                right_ty,
                right_name,
            } => Val::Sigma {
                left_ty: Box::new(left_ty.eval(env)),
                left_name,
                right_ty: Box::new(Clos {
                    env: env.clone(),
                    body: *right_ty,
                }),
                right_name,
            },
            Expr::Pair(a, b) => Val::Pair(Box::new(a.eval(env)), Box::new(b.eval(env))),
            Expr::Error => Val::Error,
        }
    }
}
