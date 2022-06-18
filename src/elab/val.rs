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
    pub params: Vec<Par>,
    env: Env,
    body: Expr,
}
impl Clos {
    pub fn par_ty(&self) -> Val {
        let mut env = self.env.clone();
        self.params
            .iter()
            .fold(None, |term, Par { name, ty }| {
                let term = match term {
                    Some(term) => Box::new(Expr::Fun {
                        class: Sigma,
                        params: vec![Par {
                            name: *name,
                            ty: ty.clone(),
                        }],
                        body: term,
                    }),
                    None => Box::new(ty.clone()),
                };
                Some(term)
            })
            .unwrap()
            .eval(&mut env)
    }

    pub fn apply(self, arg: Val) -> Val {
        // deal with argument number mismatch when passing values that aren't syntactically tuples:
        //
        // ((x, y) => ...) p where p : (A, B) -->
        // case p of (x, y) => ...
        //
        // ([a, b] (x, y) => ...) [t, u] p -->
        // (case p of (x, y) => ...) [t/a, u/b]
        let Clos { mut env, body, .. } = self;
        match arg.zip_pair(&self.params) {
            Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
            Err(arg) => {
                let pars: Vec<_> = self.params.iter().map(|x| x.name).collect();
                return arg.app(
                    Elim::Case(super::pattern::CaseOf::make_simple_args(
                        &pars, body, env.size,
                    )),
                    &mut env,
                );
            }
        }
        body.eval(&mut env)
    }

    pub fn quote(self, size: Size) -> Expr {
        let arg = self.synthesize_args(size);
        let Clos {
            class,
            params,
            mut env,
            body,
        } = self;
        let params: Vec<_> = params
            .into_iter()
            .map(|Par { name, ty }| Par {
                name,
                ty: ty.eval(&mut env).quote(size),
            })
            .collect();
        match arg.zip_pair(&params) {
            Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
            Err(arg) => {
                let pars: Vec<_> = params.iter().map(|x| x.name).collect();
                return Expr::Elim(
                    Box::new(arg.quote(env.size)),
                    Box::new(Elim::Case(super::pattern::CaseOf::make_simple_args(
                        &pars, body, env.size,
                    ))),
                );
            }
        }
        let body = body.eval(&mut env).quote(size + params.len());
        Expr::Fun {
            class,
            params,
            body: Box::new(body),
        }
    }

    /// Add the parameters to the environment and then evaluate the closure body, "opening" or "entering" the closure.
    /// `size` is the size before adding any parameters.
    /// The size after calling `open` is `size + self.params.len()`.
    pub fn open(self, mut size: Size) -> Val {
        let Clos {
            class,
            params,
            mut env,
            body,
        } = self;
        for par in &params {
            env.push(Some(Val::var(Var::Local(par.name, size.next_lvl()))));
            size += 1;
        }
        body.eval(&mut env)
    }

    pub fn synthesize_args(&self, size: Size) -> Val {
        let (arg, _size) =
            self.params
                .iter()
                .fold((None, size), |(term, size), Par { name, ty }| {
                    let var = Box::new(Val::var(Var::Local(*name, size.next_lvl())));
                    let term = match term {
                        Some(term) => Box::new(Val::Pair(var, term)),
                        None => var,
                    };
                    (Some(term), size)
                });
        *arg.unwrap()
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
            Elim::App(icit, arg) => match self {
                Val::Fun(clos) => {
                    assert_eq!(clos.class.icit(), Some(icit));
                    clos.apply(arg)
                }
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
            Elim::App(icit, arg) => Elim::App(icit, arg.eval(env)),
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
    }
}
impl Elim<Val> {
    pub fn quote(self, size: Size) -> Elim<Expr> {
        match self {
            Elim::App(icit, arg) => Elim::App(icit, arg.quote(size)),
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
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
                params,
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
