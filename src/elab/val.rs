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
        // deal with argument number mismatch when passing values that aren't syntactically tuples:
        //
        // ((x, y) => ...) p where p : (A, B) -->
        // case p of (x, y) => ...
        //
        // ([a, b] (x, y) => ...) [t, u] p -->
        // (case p of (x, y) => ...) [t/a, u/b]
        let Clos { mut env, body, .. } = self;
        if let Some(imp) = args.implicit {
            match imp.zip_pair(&self.params.implicit) {
                Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
                Err(imp) => {
                    let imp_pars: Vec<_> = self.params.implicit.iter().map(|x| x.name).collect();
                    let exp_pars: Vec<_> = self.params.explicit.iter().map(|x| x.name).collect();
                    let body = match args.explicit {
                        Some(exp) => Expr::Elim(
                            Box::new(exp.quote(env.size + self.params.implicit.len())),
                            Box::new(Elim::Case(super::pattern::CaseOf::make_simple_args(
                                &exp_pars,
                                body,
                                env.size + self.params.implicit.len(),
                            ))),
                        ),
                        None => {
                            assert!(exp_pars.is_empty());
                            body
                        }
                    };
                    return imp.app(
                        Elim::Case(super::pattern::CaseOf::make_simple_args(
                            &imp_pars, body, env.size,
                        )),
                        &mut env,
                    );
                }
            }
        }
        if let Some(exp) = args.explicit {
            match exp.zip_pair(&self.params.explicit) {
                Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
                Err(exp) => {
                    let exp_pars: Vec<_> = self.params.explicit.iter().map(|x| x.name).collect();
                    return exp.app(
                        Elim::Case(super::pattern::CaseOf::make_simple_args(
                            &exp_pars, body, env.size,
                        )),
                        &mut env,
                    );
                }
            }
        }
        body.eval(&mut env)
    }

    pub fn quote(self, size: Size) -> Expr {
        let Clos {
            class,
            params,
            mut env,
            body,
        } = self;
        let args = params.synthesize_args(size);
        let params = params.quote(size);
        if let Some(imp) = args.implicit {
            match imp.zip_pair(&params.implicit) {
                Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
                Err(imp) => {
                    let imp_pars: Vec<_> = params.implicit.iter().map(|x| x.name).collect();
                    let exp_pars: Vec<_> = params.explicit.iter().map(|x| x.name).collect();
                    let body = match args.explicit {
                        Some(exp) => Expr::Elim(
                            Box::new(exp.quote(env.size + params.implicit.len())),
                            Box::new(Elim::Case(super::pattern::CaseOf::make_simple_args(
                                &exp_pars,
                                body,
                                env.size + params.implicit.len(),
                            ))),
                        ),
                        None => {
                            assert!(exp_pars.is_empty());
                            body
                        }
                    };
                    return Expr::Elim(
                        Box::new(imp.quote(env.size + params.implicit.len())),
                        Box::new(Elim::Case(super::pattern::CaseOf::make_simple_args(
                            &imp_pars, body, env.size,
                        ))),
                    );
                }
            }
        }
        if let Some(exp) = args.explicit {
            match exp.zip_pair(&params.explicit) {
                Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
                Err(exp) => {
                    let exp_pars: Vec<_> = params.explicit.iter().map(|x| x.name).collect();
                    return Expr::Elim(
                        Box::new(exp.quote(env.size)),
                        Box::new(Elim::Case(super::pattern::CaseOf::make_simple_args(
                            &exp_pars, body, env.size,
                        ))),
                    );
                }
            }
        }
        let body = body.eval(&mut env).quote(size + params.len());
        Expr::Fun {
            class,
            params,
            body: Box::new(body),
        }
    }

    pub fn vquote(self, size: Size) -> Val {
        let args = self.params.synthesize_args(size);
        self.apply(args)
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
    pub fn zip_pair<T>(self, with: &[T]) -> Result<Vec<(Val, &T)>, Val> {
        // ((x, y) => ...) p where p : (A, B) shouldn't panic
        // so first check that we have enough of the pair inlined
        let mut term = &self;
        for _ in 0..with.len() {
            match term {
                Val::Pair(a, rest) => {
                    term = rest;
                }
                Val::Error => (),
                _ => return Err(self),
            }
        }
        let mut v = Vec::new();
        let mut term = self;
        for x in &with[..with.len() - 1] {
            match term {
                Val::Pair(a, rest) => {
                    v.push((*a, x));
                    term = *rest;
                }
                Val::Error => v.push((Val::Error, x)),
                _ => unreachable!(),
            }
        }
        if let Some(x) = with.last() {
            v.push((term, x));
        }
        Ok(v)
    }

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

impl Args<Expr> {
    pub fn eval(self, env: &mut Env) -> Args<Val> {
        let state = env.state();
        let Args { implicit, explicit } = self;
        let implicit = implicit.map(|x| Box::new(x.eval(env)));
        let explicit = explicit.map(|x| Box::new(x.eval(env)));
        env.reset(state);
        Args { implicit, explicit }
    }
}
impl Args<Val> {
    pub fn quote(self, size: Size) -> Args<Expr> {
        let Args { implicit, explicit } = self;
        let implicit = implicit.map(|x| Box::new(x.quote(size)));
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
            .map(|Par { name, ty }| {
                env.push(None);
                Par {
                    name,
                    ty: ty.eval(env),
                }
            })
            .collect();
        let explicit = explicit
            .into_iter()
            .map(|Par { name, ty }| {
                env.push(None);
                Par {
                    name,
                    ty: ty.eval(env),
                }
            })
            .collect();
        env.reset(state);
        Params { implicit, explicit }
    }
}
impl Params<Val> {
    pub fn synthesize_args(&self, size: Size) -> Args<Val> {
        let Params { implicit, explicit } = self;
        let (implicit, mut size) =
            implicit
                .iter()
                .fold((None, size), |(term, size), Par { name, ty }| {
                    let var = Box::new(Val::var(Var::Local(*name, size.next_lvl())));
                    let term = match term {
                        Some(term) => Box::new(Val::Pair(var, term)),
                        None => var,
                    };
                    (Some(term), size)
                });
        let (explicit, _size) =
            explicit
                .iter()
                .fold((None, size), |(term, size), Par { name, ty }| {
                    let var = Box::new(Val::var(Var::Local(*name, size.next_lvl())));
                    let term = match term {
                        Some(term) => Box::new(Val::Pair(var, term)),
                        None => var,
                    };
                    (Some(term), size)
                });
        Args { implicit, explicit }
    }

    pub fn quote(self, size: Size) -> Params<Expr> {
        let Params { implicit, explicit } = self;
        let (implicit, size) =
            implicit
                .into_iter()
                .fold((Vec::new(), size), |(mut v, size), Par { name, ty }| {
                    v.push(Par {
                        name,
                        ty: ty.quote(size),
                    });
                    (v, size.inc())
                });
        let (explicit, _size) =
            explicit
                .into_iter()
                .fold((Vec::new(), size), |(mut v, size), Par { name, ty }| {
                    v.push(Par {
                        name,
                        ty: ty.quote(size),
                    });
                    (v, size.inc())
                });
        Params { implicit, explicit }
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
            Val::Lit(l) => Expr::Lit(l),
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
