use std::{
    collections::HashSet,
    sync::{Arc, RwLock},
};

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

    pub fn resolve(self, env: &Env, mcxt: &MetaCxt) -> Result<Val, Self> {
        let guard = self.unfolded.read().unwrap();
        if let Some(v) = &*guard {
            Ok(v.clone())
        } else {
            drop(guard);
            let (head, cache) = match self.head {
                Head::Var(Var::Local(_, l)) => match env.get(l.idx(env.size)) {
                    // Don't cache inlined locals since they're context-dependent
                    Some(v) => (v.clone(), false),
                    None => return Err(self),
                },
                // TODO resolve applicable builtins
                Head::Var(Var::Builtin(_)) => return Err(self),
                Head::Var(Var::Cons(_, _)) => return Err(self),
                Head::Var(Var::Meta(m)) => match mcxt.lookup(m) {
                    Some(e) => (e.eval(&mut env.clone()), true),
                    None => return Err(self),
                },
                Head::Var(Var::Def(_, d)) => {
                    match mcxt.db.def_elab(d).and_then(|x| x.result).map(|x| x.body) {
                        Some(DefBody::Let(body)) => (body.eval(&mut env.clone()), true),
                        _ => return Err(self),
                    }
                }
            };
            let mut env = if !cache {
                env.clone()
            } else {
                // If we're caching it, it can't depend on context at all
                Env::new(env.size)
            };
            let mut val = self
                .spine
                .into_iter()
                .fold(head, |head, elim| head.app(elim, &mut env));
            val.inline_head(&mut env, mcxt);
            if cache {
                let mut guard = self.unfolded.write().unwrap();
                *guard = Some(val.clone());
            }
            Ok(val)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VClos {
    pub class: FunClass,
    pub params: Vec<Par>,
    pub env: Env,
    pub body: Expr,
}
impl VClos {
    /// arg: argument type -> argument value
    pub fn elab_with(self, mut arg: impl FnMut(Val) -> Val) -> Val {
        let VClos {
            class: _,
            params,
            mut env,
            body,
        } = self;
        for par in params {
            let ty = par.ty.eval(&mut env);
            env.push(Some(arg(ty)));
        }
        body.eval(&mut env)
    }

    pub fn par_ty(&self) -> Val {
        let mut env = self.env.clone();
        self.params
            .iter()
            .rfold(None, |term, Par { name, ty }| {
                let term = match term {
                    Some(term) => Box::new(Expr::Fun(EClos {
                        class: Sigma,
                        params: vec![Par {
                            name: *name,
                            ty: ty.clone(),
                        }],
                        body: term,
                    })),
                    None => Box::new(ty.clone()),
                };
                Some(term)
            })
            .unwrap()
            .eval(&mut env)
    }

    pub fn apply_exact(self, args: Vec<Option<Val>>) -> Val {
        let VClos {
            class: _,
            params,
            mut env,
            body,
        } = self;
        assert_eq!(args.len(), params.len(), "apply_exact() not exact");
        env.extend(args);
        body.eval(&mut env)
    }

    pub fn apply(self, arg: Val) -> Val {
        // deal with argument number mismatch when passing values that aren't syntactically tuples:
        //
        // ((x, y) => ...) p where p : (A, B) -->
        // case p of (x, y) => ...
        //
        // ([a, b] (x, y) => ...) [t, u] p -->
        // (case p of (x, y) => ...) [t/a, u/b]
        let VClos { mut env, body, .. } = self;
        match arg.zip_pair(&self.params) {
            Ok(x) => env.extend(x.into_iter().map(|(x, _)| Some(x))),
            Err(arg) => {
                // let pars: Vec<_> = self.params.iter().map(|x| x.name).collect();
                return arg.app(
                    Elim::Case(
                        super::pattern::CaseOf::make_simple_args(EClos {
                            class: Lam(Expl),
                            params: self.params,
                            body: Box::new(body),
                        })
                        .map(|x| x.eval(&mut env)),
                        // TODO how do we find this return type?
                        Val::Error,
                    ),
                    &mut env,
                );
            }
        }
        body.eval(&mut env)
    }

    pub fn quote(self, mut size: Size, inline_metas: Option<&MetaCxt>) -> EClos {
        let VClos {
            class,
            params,
            mut env,
            body,
        } = self;
        let params: Vec<_> = params
            .into_iter()
            .map(|Par { name, ty }| {
                let par = Par {
                    name,
                    ty: ty.eval_quote(&mut env, size, inline_metas),
                };
                env.push(Some(Val::var(Var::Local(name, size.next_lvl()))));
                size += 1;
                par
            })
            .collect();
        let body = body.eval_quote(&mut env, size, inline_metas);
        EClos {
            class,
            params,
            body: Box::new(body),
        }
    }

    pub fn move_env(self, env: &mut Env) -> VClos {
        self.quote(env.size, None).eval(env)
    }

    /// Add the parameters to the environment and then evaluate the closure body, "opening" or "entering" the closure.
    /// `size` is the size before adding any parameters.
    /// The size after calling `open` is `size + self.params.len()`.
    pub fn open(self, mut size: Size) -> Val {
        let VClos {
            class: _,
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
        let (arg, _size) = self.params.iter().rfold(
            (None, size + self.params.len()),
            |(term, size), Par { name, ty: _ }| {
                let size = size.dec();
                let var = Box::new(Val::var(Var::Local(*name, size.next_lvl())));
                let term = match term {
                    // TODO get the actual type
                    Some(term) => Box::new(Val::Pair(var, term, Box::new(Val::Error))),
                    None => var,
                };
                (Some(term), size)
            },
        );
        *arg.unwrap()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Type,
    Neutral(Neutral),
    Fun(Box<VClos>),
    // Do(Vec<Stmt>),
    Lit(Literal),
    Pair(Box<Val>, Box<Val>, Box<Val>),
    Ref(bool, Box<Val>),
    Error,
}
impl IsTerm for Val {
    type Clos = VClos;
    type Loc = Lvl;
}

impl Val {
    pub fn zip_pair<T>(self, with: &[T]) -> Result<Vec<(Val, &T)>, Val> {
        // ((x, y) => ...) p where p : (A, B) shouldn't panic
        // so first check that we have enough of the pair inlined
        let mut term = &self;
        for _ in 0..with.len() - 1 {
            match term {
                Val::Pair(_, rest, _) => {
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
                Val::Pair(a, rest, _) => {
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
        match x {
            Elim::App(icit, arg) => match self {
                Val::Fun(clos) => {
                    assert_eq!(clos.class.icit(), Some(icit));
                    clos.apply(arg)
                }
                Val::Neutral(ref mut neutral) => {
                    neutral.app(Elim::App(icit, arg));
                    return self;
                }
                Val::Error => return Val::Error,
                _ => unreachable!("Cannot resolve application to non-Lam"),
            },
            Elim::Member(_) => todo!(),
            Elim::Case(ref case, _) => match case.try_eval(&self) {
                Some(v) => return v,
                None => match self {
                    Val::Neutral(ref mut neutral) => {
                        neutral.app(x);
                        return self;
                    }
                    Val::Error => return Val::Error,
                    x => todo!("couldn't eval case of {:?}", x),
                },
            },
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
            Elim::Case(case, ty) => Elim::Case(case.map(|x| x.eval(env)), ty.eval(env)),
        }
    }
}
impl Elim<Val> {
    pub fn quote(self, size: Size, inline_metas: Option<&MetaCxt>) -> Elim<Expr> {
        match self {
            Elim::App(icit, arg) => Elim::App(icit, arg.quote(size, inline_metas)),
            Elim::Member(_) => todo!(),
            Elim::Case(case, ty) => Elim::Case(
                case.map(|x| x.quote(size, inline_metas)),
                ty.quote(size, inline_metas),
            ),
        }
    }
}

impl EClos {
    pub fn eval(self, env: &mut Env) -> VClos {
        let EClos {
            class,
            params,
            body,
        } = self;
        VClos {
            class,
            params,
            env: env.clone(),
            body: *body,
        }
    }

    pub fn eval_quote_in_place(
        &mut self,
        env: &mut Env,
        mut size: Size,
        inline_metas: Option<&MetaCxt>,
    ) {
        let state = env.state();
        for i in &mut self.params {
            i.ty.eval_quote_in_place(env, size, inline_metas);
            env.push(Some(Val::var(Var::Local(i.name, size.next_lvl()))));
            size += 1;
        }
        self.body.eval_quote_in_place(env, size, inline_metas);
        env.reset(state);
    }
}

impl Expr {
    pub fn eval(self, env: &mut Env) -> Val {
        // TODO is there some way to be able to reuse Boxes? Expr and Val should be the same size
        match self {
            Expr::Type => Val::Type,
            Expr::Head(h) => match h {
                Head::Var(Var::Local(n, i)) => env.val(n, i),
                Head::Var(v) => Val::var(v.cvt(Size::zero())),
            },
            Expr::Elim(x, e) => x.eval(env).app(e.eval(env), env),
            Expr::Fun(clos) => Val::Fun(Box::new(clos.eval(env))),
            Expr::Lit(l) => Val::Lit(l),
            Expr::Pair(a, b, t) => Val::Pair(
                Box::new(a.eval(env)),
                Box::new(b.eval(env)),
                Box::new(t.eval(env)),
            ),
            Expr::Ref(m, x) => Val::Ref(m, Box::new(x.eval(env))),
            Expr::Error => Val::Error,
            Expr::Spanned(_, x) => x.eval(env),
        }
    }

    pub fn eval_quote_in_place(
        &mut self,
        env: &mut Env,
        size: Size,
        inline_metas: Option<&MetaCxt>,
    ) {
        match self {
            Expr::Type => (),
            Expr::Head(h) => match h {
                Head::Var(Var::Local(n, i)) => *self = env.val(*n, *i).quote(size, inline_metas),
                Head::Var(Var::Meta(m)) => match inline_metas {
                    Some(mcxt) => {
                        if let Some(expr) = mcxt.lookup(*m) {
                            *self = expr;
                            self.eval_quote_in_place(env, size, inline_metas);
                        }
                    }
                    None => (),
                },
                _ => (),
            },
            Expr::Ref(_, x) => x.eval_quote_in_place(env, size, inline_metas),
            Expr::Elim(f, e) => {
                f.eval_quote_in_place(env, size, inline_metas);
                match &mut **e {
                    // beta-reduce if possible
                    Elim::App(_, x) => match f.unspanned() {
                        Expr::Fun(clos) if matches!(clos.class, Lam(_)) => {
                            // TODO avoid these clones
                            let x = x.clone().eval(env);
                            *self = clos.clone().eval(env).apply(x).quote(size, inline_metas);
                        }
                        _ => x.eval_quote_in_place(env, size, inline_metas),
                    },
                    Elim::Member(_) => todo!(),
                    Elim::Case(case, ty) => {
                        case.visit_mut(|x| x.eval_quote_in_place(env, size, inline_metas));
                        ty.eval_quote_in_place(env, size, inline_metas);
                    }
                }
            }
            Expr::Fun(clos) => clos.eval_quote_in_place(env, size, inline_metas),
            Expr::Lit(Literal::Int(val, Err((_, meta)))) => match inline_metas {
                Some(mcxt) => {
                    if let Some(Expr::Head(Head::Var(Var::Builtin(Builtin::IntType(i))))) =
                        mcxt.lookup(*meta)
                    {
                        *self = Expr::Lit(Literal::Int(*val, Ok(i)));
                    }
                }
                None => (),
            },
            Expr::Lit(_) => (),
            Expr::Pair(a, b, t) => {
                a.eval_quote_in_place(env, size, inline_metas);
                b.eval_quote_in_place(env, size, inline_metas);
                t.eval_quote_in_place(env, size, inline_metas);
            }
            Expr::Error => (),
            Expr::Spanned(_, x) => x.eval_quote_in_place(env, size, inline_metas),
        }
    }

    /// More or less like `self.eval().quote()`, but doesn't beta-reduce.
    pub fn eval_quote(mut self, env: &mut Env, size: Size, inline_metas: Option<&MetaCxt>) -> Expr {
        self.eval_quote_in_place(env, size, inline_metas);
        self
    }

    fn unspanned(&self) -> &Expr {
        match self {
            Expr::Spanned(_, x) => x.unspanned(),
            x => x,
        }
    }
}

impl Val {
    pub fn quote(self, size: Size, inline_metas: Option<&MetaCxt>) -> Expr {
        match self {
            Val::Type => Expr::Type,
            Val::Neutral(neutral) => {
                let (head, spine) = neutral.into_parts();
                let mut inlined_meta = false;
                let head = match head {
                    // Don't resolve the neutral, we want the smallest term when quoting
                    Head::Var(Var::Meta(m)) => match inline_metas.and_then(|mcxt| mcxt.lookup(m)) {
                        Some(t) => {
                            inlined_meta = true;
                            t
                        }
                        None => Expr::var(Var::Meta(m)),
                    },
                    Head::Var(v) => Expr::var(v.cvt(size)),
                };
                let res = spine.into_iter().fold(head, |head, elim| {
                    Expr::Elim(Box::new(head), Box::new(elim.quote(size, inline_metas)))
                });
                if inlined_meta {
                    // Beta reduce + inline more metas
                    res.eval_quote(&mut Env::new(size), size, inline_metas)
                } else {
                    res
                }
            }
            Val::Ref(m, x) => Expr::Ref(m, Box::new(x.quote(size, inline_metas))),
            Val::Fun(clos) => Expr::Fun(clos.quote(size, inline_metas)),
            Val::Lit(l) => Expr::Lit(l),
            Val::Pair(a, b, t) => Expr::Pair(
                Box::new(a.quote(size, inline_metas)),
                Box::new(b.quote(size, inline_metas)),
                Box::new(t.quote(size, inline_metas)),
            ),
            Val::Error => Expr::Error,
        }
    }

    /// Unfolds the head of this value as much as possible, applying eliminators along the way.
    /// Does not recurse over anything - it doesn't affect spines, pairs, etc.
    pub fn inline_head(&mut self, env: &mut Env, mcxt: &MetaCxt) {
        match self {
            Val::Neutral(n) => {
                let mut n2 = Neutral::new(Head::Var(Var::Builtin(Builtin::Unit)), Vec::new());
                std::mem::swap(n, &mut n2);
                match n2.resolve(env, &mcxt) {
                    Ok(x) => *self = x,
                    Err(n2) => *n = n2,
                }
            }
            _ => (),
        }
    }

    pub fn can_copy(&self) -> bool {
        match self {
            Val::Type => true,
            Val::Neutral(n) => match n.head() {
                // Currently all builtin types are copyable
                Head::Var(Var::Builtin(_)) => true,
                Head::Var(Var::Meta(_)) => true, // TODO add a Copy constraint to the meta somehow
                _ => false,
            },
            Val::Fun(clos) => match clos.class {
                // TODO check if all components can be copied; may require eval-ing
                Sigma => false,
                // TODO separate function types for Fn, FnMut, FnOnce
                Lam(_) | Pi(_) => true,
            },
            Val::Lit(_) | Val::Pair(_, _, _) => unreachable!("not a type"),
            Val::Ref(m, _) => !m,
            Val::Error => true,
        }
    }

    pub fn check_scope(&self, size: Size) -> Result<(), Name> {
        match self {
            Val::Type => Ok(()),
            Val::Neutral(n) => {
                match n.head() {
                    Head::Var(Var::Local(n, l)) => {
                        if !l.in_scope(size) {
                            // The span on the name likely wouldn't help, since check_scope is
                            // generally used for inferred types
                            return Err(n.0);
                        }
                    }
                    _ => (),
                }
                n.spine().iter().fold(Ok(()), |acc, x| {
                    acc.and_then(|()| match x {
                        Elim::App(_, x) => x.check_scope(size),
                        Elim::Member(_) => todo!(),
                        Elim::Case(case, ty) => {
                            let mut res = Ok(());
                            case.visit(|x| {
                                if res.is_ok() {
                                    res = x.check_scope(size);
                                }
                            });
                            res.and_then(|()| ty.check_scope(size))
                        }
                    })
                })
            }
            Val::Ref(_, x) => x.check_scope(size),
            Val::Fun(clos) => clos.check_scope(size),
            Val::Lit(_) => Ok(()),
            Val::Pair(a, b, t) => {
                a.check_scope(size)?;
                b.check_scope(size)?;
                t.check_scope(size)
            }
            Val::Error => Ok(()),
        }
    }
}
impl VClos {
    pub fn check_scope(&self, size: Size) -> Result<(), Name> {
        let mut allowed = HashSet::new();
        for i in Size::zero().until(size) {
            allowed.insert(i.next_lvl());
        }
        for i in size.until(self.env.size) {
            if self.env.get(i.next_lvl().idx(self.env.size)).is_some() {
                allowed.insert(i.next_lvl());
            }
        }
        let mut inner_size = Size::zero();
        let mut size = self.env.size;
        for i in &self.params {
            i.ty.check_scope(&allowed, inner_size, size)?;
            inner_size += 1;
            size += 1;
        }
        self.body.check_scope(&allowed, inner_size, size)
    }
}
impl EClos {
    pub fn check_scope(
        &self,
        allowed: &HashSet<Lvl>,
        mut inner_size: Size,
        mut size: Size,
    ) -> Result<(), Name> {
        for i in &self.params {
            i.ty.check_scope(allowed, inner_size, size)?;
            inner_size += 1;
            size += 1;
        }
        self.body.check_scope(allowed, inner_size, size)
    }
}
impl Expr {
    pub fn check_scope(
        &self,
        allowed: &HashSet<Lvl>,
        inner_size: Size,
        size: Size,
    ) -> Result<(), Name> {
        match self {
            Expr::Type => Ok(()),
            Expr::Head(Head::Var(Var::Local(n, i))) => {
                if i.in_scope(inner_size) || allowed.contains(&i.lvl(size)) {
                    Ok(())
                } else {
                    Err(n.0)
                }
            }
            Expr::Head(_) => Ok(()),
            Expr::Elim(a, e) => {
                a.check_scope(allowed, inner_size, size)
                    .and_then(|()| match &**e {
                        Elim::App(_, x) => x.check_scope(allowed, inner_size, size),
                        Elim::Member(_) => todo!(),
                        Elim::Case(case, ty) => {
                            let mut res = Ok(());
                            case.visit(|x| {
                                if res.is_ok() {
                                    res = x.check_scope(allowed, inner_size, size);
                                }
                            });
                            res.and_then(|()| ty.check_scope(allowed, inner_size, size))
                        }
                    })
            }
            Expr::Ref(_, x) => x.check_scope(allowed, inner_size, size),
            Expr::Fun(c) => c.check_scope(allowed, inner_size, size),
            Expr::Lit(_) => Ok(()),
            Expr::Pair(a, b, t) => {
                a.check_scope(allowed, inner_size, size)?;
                b.check_scope(allowed, inner_size, size)?;
                t.check_scope(allowed, inner_size, size)
            }
            Expr::Spanned(_, x) => x.check_scope(allowed, inner_size, size),
            Expr::Error => Ok(()),
        }
    }
}
