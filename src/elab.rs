use crate::common::*;
use crate::term::Builtin;

#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub enum ElabStmt {
    Def(Sym, Elab),
    Expr(Elab),
}
impl ElabStmt {
    pub fn cloned<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Self {
        match self {
            ElabStmt::Def(s, x) => {
                let fresh = env.bindings_mut().fresh(*s);
                #[cfg(feature = "logging")]
                {
                    let b = &env.bindings();
                    println!(
                        "Renaming {}{} to {}{}",
                        b.resolve(*s),
                        s.num(),
                        b.resolve(fresh),
                        fresh.num()
                    );
                }
                let ty = x.get_type(env);
                env.set_val(*s, Elab::Var(fresh, Box::new(ty)));
                ElabStmt::Def(fresh, x.cloned(env))
            }
            ElabStmt::Expr(x) => ElabStmt::Expr(x.cloned(env)),
        }
    }
}

/// The language of elaborated terms, which have enough type information to reconstruct types pretty easily
///
/// For a term to get to here, it must be well typed
#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub enum Elab {
    Unit,                              // ()
    Binder(Sym, BElab),                // x: T
    Var(Sym, BElab),                   // (a, T) --> the T a
    I32(i32),                          // 3
    Type,                              // Type
    Builtin(Builtin),                  // Int
    Fun(Vec<(Vec<Elab>, Elab, Elab)>), // fun { a b => the T x; c d => the U y }
    App(BElab, BElab),                 // f x
    Pair(BElab, BElab),                // x, y
    Tag(TagId),                        // tag X
    StructIntern(StructId),            // struct { x := 3 }
    StructInline(Vec<(Sym, Elab)>),    // struct { x := 3 }
    Project(BElab, RawSym),            // r.m
    Block(Vec<ElabStmt>),              // do { x; y }
    Union(Vec<Elab>),                  // x | y
    Bottom,
    Top,
}
type BElab = Box<Elab>;

pub fn unionize_ty<T: MainGroup>(
    v: Vec<(Vec<Elab>, Elab, Elab)>,
    env: &TempEnv<T>,
) -> (Vec<Elab>, Elab) {
    let len = v.first().unwrap().0.len();
    let (args, ret) = v.into_iter().fold(
        ((0..len).map(|_| Vec::new()).collect::<Vec<_>>(), Vec::new()),
        |(mut accf, mut acct), (from, to, _)| {
            for (accf, from) in accf.iter_mut().zip(from) {
                accf.push(from);
            }
            acct.push(to);
            (accf, acct)
        },
    );
    let args = args
        .into_iter()
        .map(|v| Elab::Union(v).simplify_unions(env))
        .collect();
    let ret = Elab::Union(ret).simplify_unions(env);
    (args, ret)
}

impl Elab {
    /// Binders are usually confusing in type errors, so you can get rid of them
    pub fn unbind(&self) -> &Self {
        match self {
            Elab::Binder(_, x) => x,
            x => x,
        }
    }

    /// Are there any values that occupy both types `self` and `other`?
    /// Bottom doesn't count, of course, since it's not a value
    /// The same as "could a value of type `other` match `self`?" or vice versa
    pub fn overlap<T: MainGroup>(&self, other: &Elab, env: &TempEnv<T>) -> bool {
        match (self, other) {
            (Elab::Union(v), Elab::Union(v2)) => {
                v.iter().any(|x| v2.iter().any(|y| x.overlap(y, env)))
            }
            (Elab::Union(v), _) => v.iter().any(|x| x.overlap(other, env)),
            (_, Elab::Union(v)) => v.iter().any(|x| self.overlap(x, env)),
            _ => {
                self.subtype_of(other, &mut env.clone()) || other.subtype_of(self, &mut env.clone())
            }
        }
    }

    /// Instead of calling `Elab::union()` and over again, if you construct a union with several parts,
    /// call this after to simplify it in one pass
    pub fn simplify_unions<T: MainGroup>(mut self, env: &TempEnv<T>) -> Self {
        match &mut self {
            Elab::Union(v) => match v.len() {
                0 => self,
                1 => v.pop().unwrap(),
                _ => {
                    let mut env = env.clone();
                    let mut rv: Vec<Elab> = Vec::new();
                    for val in v.split_off(0) {
                        let mut i = 0;
                        let mut should_add = true;
                        while i < rv.len() {
                            let x = &rv[i];

                            // If `val` covers `x`'s case, we don't need `x`
                            if x.subtype_of(&val, &mut env) {
                                rv.remove(i);
                            } else {
                                i += 1;
                                // but if `x` covers `val`'s case, we don't need `val`
                                if val.subtype_of(x, &mut env) {
                                    should_add = false;
                                    break;
                                }
                            }
                        }
                        if should_add {
                            rv.push(val);
                        }
                    }

                    rv.sort_by(|x, y| x.partial_cmp(y).unwrap());

                    if rv.len() == 1 {
                        rv.pop().unwrap()
                    } else {
                        Elab::Union(rv)
                    }
                }
            },
            _ => self,
        }
    }

    /// Does this term reference this symbol at all?
    pub fn uses<T: MainGroup>(&self, s: Sym, env: &TempEnv<T>) -> bool {
        use Elab::*;
        match self {
            Type | Unit | I32(_) | Builtin(_) | Tag(_) | Top | Bottom => false,
            Var(x, ty) => *x == s || ty.uses(s, env),
            Fun(v) => v.iter().any(|(a, b, c)| {
                b.uses(s, env) || c.uses(s, env) || a.iter().any(|x| x.uses(s, env))
            }),
            App(x, y) | Pair(x, y) => x.uses(s, env) || y.uses(s, env),
            Binder(_, x) => x.uses(s, env),
            StructIntern(i) => {
                let scope = ScopeId::Struct(*i, Box::new(env.scope()));
                env.db.symbols(scope.clone()).iter().any(|sym| {
                    env.db
                        .elab(scope.clone(), **sym)
                        .map_or(false, |e| e.uses(s, env))
                })
            }
            StructInline(v) => v.iter().any(|(_, x)| x.uses(s, env)),
            Project(r, _) => r.uses(s, env),
            Block(v) => v.iter().any(|x| match x {
                ElabStmt::Def(_, e) => e.uses(s, env),
                ElabStmt::Expr(e) => e.uses(s, env),
            }),
            Union(v) => v.iter().any(|x| x.uses(s, env)),
        }
    }

    /// Reduce to full normal form, essentially recursively calling whnf()
    pub fn normal<T: MainGroup>(&mut self, env: &mut TempEnv<T>) {
        // Call whnf()
        self.whnf(env);
        // And recurse
        use Elab::*;
        match self {
            Type | Unit | I32(_) | Builtin(_) | Tag(_) | Bottom | Top => (),
            Var(_, ty) => ty.normal(env),
            Fun(v) => v.iter_mut().for_each(|(a, b, t)| {
                a.iter_mut().for_each(|a| a.normal(env));
                b.normal(env);
                t.normal(env);
            }),
            App(x, y) | Pair(x, y) => {
                x.normal(env);
                y.normal(env);
            }
            Binder(_, x) => x.normal(env),
            StructIntern(_) => (),
            StructInline(v) => v.iter_mut().for_each(|(_, x)| x.normal(env)),
            Project(r, _) => r.normal(env),
            Block(v) => v.iter_mut().for_each(|x| match x {
                ElabStmt::Def(_, e) => e.normal(env),
                ElabStmt::Expr(e) => e.normal(env),
            }),
            Union(v) => v.iter_mut().for_each(|x| x.normal(env)),
        }
    }

    /// Reduce to Weak-Head Normal Form, in place
    /// Returns whether the top-level structure changed
    ///
    /// This is like actual normal form, but we only perform one level of beta- or projection-reduction
    /// So we're guaranteed not to have `(\x.t)u` at the top level, but we could have e.g. `(\x.(\y.t)u)`
    /// This is the form we store types in, so if you need to compare types you'll need to call `whnf` recursively
    pub fn whnf<T: MainGroup>(&mut self, env: &mut TempEnv<T>) -> bool {
        match self {
            // Binders don't count as forms
            Elab::Binder(_, t) => t.whnf(env),
            // Unions don't either (no head)
            Elab::Union(v) => v
                .iter_mut()
                .map(|x| x.whnf(env))
                .collect::<Vec<_>>()
                .into_iter()
                .any(|x| x),
            Elab::Var(x, ty) => {
                if let Some(t) = env.val(*x) {
                    match &*t {
                        // Update to the new type, but don't re-look-up the var
                        Elab::Var(y, new_ty) if x == y => **ty = new_ty.cloned(env),
                        _ => {
                            *self = t.cloned(env);
                            return self.whnf(env);
                        }
                    }
                }
                false
            }
            Elab::App(f, x) => {
                // We recursively WHNF the head
                f.whnf(env);
                match &mut **f {
                    Elab::Fun(v) => {
                        x.whnf(env);
                        let mut rf = Vec::new();
                        // split_off(0) is like drain(..) but doesn't borrow v
                        for (mut args, mut body, to) in v.split_off(0) {
                            if x.get_type(env).subtype_of(args.first().unwrap(), env) {
                                let arg = args.remove(0);
                                arg.do_match(&x, env);
                                if args.is_empty() {
                                    body.whnf(env);
                                    *self = body;
                                    return true;
                                } else {
                                    rf.push((args, body, to));
                                }
                            }
                        }
                        *self = Elab::Fun(rf);
                        true
                    }
                    Elab::App(f, x2) => match &**f {
                        // This needs to be a binary operator, since that's the only builtin that takes two arguments
                        Elab::Builtin(b) => {
                            // Since we need them as i32s, we need to WHNF the arguments as well
                            x.whnf(env);
                            x2.whnf(env);
                            match (b, &**x2, &**x) {
                                (Builtin::Add, Elab::I32(n), Elab::I32(m)) => {
                                    *self = Elab::I32(n + m);
                                    true
                                }
                                (Builtin::Sub, Elab::I32(n), Elab::I32(m)) => {
                                    *self = Elab::I32(n - m);
                                    true
                                }
                                (Builtin::Mul, Elab::I32(n), Elab::I32(m)) => {
                                    *self = Elab::I32(n * m);
                                    true
                                }
                                (Builtin::Div, Elab::I32(n), Elab::I32(m)) => {
                                    *self = Elab::I32(n / m);
                                    true
                                }
                                _ => false,
                            }
                        }
                        _ => false,
                    },
                    // Still not a function
                    _ => false,
                }
            }
            Elab::Project(r, m) => {
                // We recursively WHNF the head
                r.whnf(env);
                match &**r {
                    Elab::StructIntern(i) => {
                        let scope = ScopeId::Struct(*i, Box::new(env.scope()));
                        for i in env.db.symbols(scope.clone()).iter() {
                            if i.raw() == *m {
                                let val = env.db.elab(scope.clone(), **i).unwrap();
                                *self = val.cloned(&mut env.clone());
                                return true;
                            }
                        }
                        panic!("not found")
                    }
                    Elab::StructInline(v) => {
                        let (_, val) = v.iter().find(|(name, _)| name.raw() == *m).unwrap();
                        *self = val.cloned(&mut env.clone());
                        true
                    }
                    // Still not a record
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Like `get_type()`, but looks up actual types for recursive calls. Should only be used after type checking.
    pub fn get_type_rec<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Elab {
        match (self.get_type(env), self) {
            (Elab::Bottom, Elab::Var(s, _)) => env.db.elab(env.scope(), *s).unwrap().get_type(env),
            (x, _) => x,
        }
    }

    /// Gets the "best" type of `self`.
    ///
    /// Note: It doesn't look things up in `env`, it only uses it for cloning.
    pub fn get_type<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Elab {
        use Elab::*;
        match self {
            Top => Type,
            Bottom => Type,
            Type => Type,
            Unit => Unit,
            I32(i) => I32(*i),
            Builtin(b) => b.get_type(),
            Tag(t) => Tag(*t),
            Var(_, t) => t.cloned(&mut env.clone()),
            Fun(v) => {
                let mut env = env.clone();
                Fun(v
                    .iter()
                    .map(|(from, _, to)| {
                        (
                            from.iter().map(|x| x.cloned(&mut env)).collect(),
                            to.cloned(&mut env),
                            Type,
                        )
                    })
                    .collect())
            }
            App(f, x) => match f.get_type(env) {
                Fun(v) => {
                    let mut rf = Vec::new();
                    let tx = x.get_type(env);
                    for (args, to, _) in v {
                        if tx.overlap(args.first().unwrap(), env) {
                            let mut env2 = env.clone();
                            let mut args: Vec<_> =
                                args.iter().map(|x| x.cloned(&mut env2)).collect();
                            let arg = args.remove(0);
                            arg.do_match(&x, env);

                            if args.is_empty() {
                                let mut to = to.cloned(&mut env2);
                                to.whnf(env);
                                return to;
                            } else {
                                let to = to.cloned(&mut env2);
                                rf.push((args, to, Type));
                            }
                        }
                    }
                    debug_assert_ne!(
                        rf.len(),
                        0,
                        "None of {} matched {}",
                        f.get_type(env).pretty(&env.bindings()).ansi_string(),
                        tx.pretty(&env.bindings()).ansi_string()
                    );
                    Fun(rf)
                }
                f @ Tag(_) | f @ App(_, _) => App(Box::new(f), Box::new(x.get_type(env))),
                // This triggers with recursive functions
                Bottom => Bottom,
                _ => panic!("not a function type"),
            },
            Pair(x, y) => Pair(Box::new(x.get_type(env)), Box::new(y.get_type(env))),
            Binder(_, x) => x.get_type(env),
            StructIntern(id) => {
                let scope = ScopeId::Struct(*id, Box::new(env.scope()));
                // TODO rename
                StructInline(
                    env.db
                        .symbols(scope.clone())
                        .iter()
                        .filter_map(|x| Some((**x, env.db.elab(scope.clone(), **x)?.get_type(env))))
                        .collect(),
                )
            }
            StructInline(v) => StructInline(v.iter().map(|(n, x)| (*n, x.get_type(env))).collect()),
            Project(r, m) => {
                if let StructInline(t) = r.get_type(env) {
                    t.iter()
                        .find(|(n, _)| n.raw() == *m)
                        .unwrap()
                        .1
                        .cloned(&mut env.clone())
                } else {
                    panic!("not a struct type")
                }
            }
            Block(v) => match v.last().unwrap() {
                ElabStmt::Def(_, _) => Unit,
                ElabStmt::Expr(e) => e.get_type(env),
            },
            // Unions can only be types, and the type of a union doesn't mean that much
            Union(_) => Type,
        }
    }

    /// Adds substitutions created by matching `other` with `self` (`self` is the pattern) to `ctx`
    /// Does not check if it's a valid match, that's the typechecker's job
    pub fn do_match<T: MainGroup>(&self, other: &Elab, env: &mut TempEnv<T>) {
        use Elab::*;
        match (self, other) {
            (Binder(s, _), _) => {
                let mut other = other.cloned(&mut env.clone());
                other.whnf(env);
                #[cfg(feature = "logging")]
                {
                    println!(
                        "Setting {} := {}",
                        s.pretty(&env.bindings()).ansi_string(),
                        other.pretty(&env.bindings()).ansi_string()
                    );
                }
                env.set_val(*s, other);
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.do_match(bx, env);
                ay.do_match(by, env);
            }
            (App(af, ax), App(bf, bx)) => {
                af.do_match(bf, env);
                ax.do_match(bx, env);
            }
            _ => (),
        }
    }

    /// Clones `self`. Unlike a normal clone, we freshen any bound variables (but not free variables)
    /// This means that other code doesn't have to worry about capture-avoidance, we do it here for free
    pub fn cloned<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Self {
        use Elab::*;
        match self {
            Var(s, t) => {
                if let Some(x) = env.vals.get(s).cloned() {
                    // Here's how this (`x == self`) happens:
                    // 1. We come up with a Elab using, say, x3. That Elab gets stored in Salsa's database.
                    // 2. We reset the Bindings, define x0, x1, and x2, and ask for the Elab again.
                    // 3. Salsa gives us the Elab from the database, which references x3. We call cloned() on it.
                    // 4. We see a bound variable, x3, and define a fresh variable to replace it with. The fresh variable is now also x3.
                    // 5. Now we want to replace x3 with x3, so we better not call cloned() recursively or we'll get stuck in a loop.
                    // Note, though, that this is expected behaviour and doesn't need fixing.
                    match &*x {
                        // We get and clone the new type, but we don't re-look-up the var
                        Elab::Var(y, t) if s == y => Var(*s, Box::new(t.cloned(env))),
                        _ => x.cloned(env),
                    }
                } else {
                    // Free variable
                    Var(*s, Box::new(t.cloned(env)))
                }
            }
            Top => Top,
            Bottom => Bottom,
            Unit => Unit,
            Type => Type,
            I32(i) => I32(*i),
            Builtin(b) => Builtin(*b),
            Tag(t) => Tag(*t),
            App(f, x) => App(Box::new(f.cloned(env)), Box::new(x.cloned(env))),
            // Rename bound variables
            // This case runs before any that depend on it, and the Elab has unique names
            Binder(s, t) => {
                let fresh = env.bindings_mut().fresh(*s);
                #[cfg(feature = "logging")]
                {
                    let b = &env.bindings();
                    println!(
                        "Renaming {}{} to {}{}",
                        b.resolve(*s),
                        s.num(),
                        b.resolve(fresh),
                        fresh.num()
                    );
                }
                let t2 = t.cloned(env);
                env.set_val(*s, Var(fresh, Box::new(t2)));
                Binder(fresh, Box::new(t.cloned(env)))
            }
            // All these allow bound variables, so we have to make sure they're done in order
            Fun(v) => Fun(v
                .iter()
                .map(|(a, b, c)| {
                    (
                        a.iter().map(|x| x.cloned(env)).collect(),
                        b.cloned(env),
                        c.cloned(env),
                    )
                })
                .collect()),
            Pair(x, y) => {
                let x = Box::new(x.cloned(env));
                let y = Box::new(y.cloned(env));
                Pair(x, y)
            }
            StructIntern(i) => {
                // Make sure renames propagate to any local variables we use in the struct
                if env.vals.keys().any(|k| self.uses(*k, env)) {
                    let scope = ScopeId::Struct(*i, Box::new(env.scope()));
                    // TODO rename definitions
                    StructInline(
                        env.db
                            .symbols(scope.clone())
                            .iter()
                            .filter_map(|x| {
                                Some((**x, env.db.elab(scope.clone(), **x)?.cloned(env)))
                            })
                            .collect(),
                    )
                } else {
                    // It doesn't capture any locals (that we're renaming), so we can leave it
                    StructIntern(*i)
                }
            }
            StructInline(v) => StructInline(
                v.into_iter()
                    .map(|(name, val)| {
                        let val = val.cloned(env);
                        let fresh = env.bindings_mut().fresh(*name);
                        #[cfg(feature = "logging")]
                        {
                            let b = &env.bindings();
                            println!(
                                "Renaming {}{} to {}{}",
                                b.resolve(*name),
                                name.num(),
                                b.resolve(fresh),
                                fresh.num()
                            );
                        }
                        let ty = val.get_type(env);
                        env.set_val(*name, Var(fresh, Box::new(ty)));
                        (fresh, val)
                    })
                    .collect(),
            ),
            Project(r, m) => Project(Box::new(r.cloned(env)), *m),
            Block(v) => Block(v.iter().map(|x| x.cloned(env)).collect()),
            Union(v) => Union(v.iter().map(|x| x.cloned(env)).collect()),
        }
    }
}

impl Pretty for Elab {
    type Context = Bindings;
    fn pretty(&self, ctx: &Bindings) -> Doc {
        match self {
            Elab::Unit => Doc::start("()").style(Style::Literal),
            Elab::Binder(x, t) => x
                .pretty(ctx)
                .add(":")
                .style(Style::Binder)
                .space()
                .chain(t.pretty(ctx))
                .prec(Prec::Term),
            Elab::Bottom => Doc::start("Empty"),
            Elab::Top => Doc::start("Any"),
            Elab::Var(s, _) => s.pretty(ctx),
            Elab::I32(i) => Doc::start(i).style(Style::Literal),
            Elab::Type => Doc::start("Type"),
            Elab::Builtin(b) => Doc::start(b),
            Elab::Fun(v) if v.len() == 1 => {
                let (args, body, _) = v.first().unwrap();
                let until_body = Doc::start("fun")
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
                        args.iter().map(|x| x.pretty(ctx).nest(Prec::Atom)),
                        Doc::none().line(),
                    ))
                    .indent()
                    .line()
                    .add("=>");
                Doc::either(
                    until_body
                        .clone()
                        .line()
                        .add("  ")
                        .chain(body.pretty(ctx).indent())
                        .group(),
                    until_body.space().chain(body.pretty(ctx).indent()).group(),
                )
                .prec(Prec::Term)
            }
            Elab::Fun(v) => pretty_block(
                "fun",
                v.iter().map(|(args, body, _)| {
                    let until_body = Doc::start("fun")
                        .style(Style::Keyword)
                        .line()
                        .chain(Doc::intersperse(
                            args.iter().map(|x| x.pretty(ctx).nest(Prec::Atom)),
                            Doc::none().line(),
                        ))
                        .indent()
                        .line()
                        .add("=>");
                    Doc::either(
                        until_body
                            .clone()
                            .line()
                            .add("  ")
                            .chain(body.pretty(ctx).indent())
                            .group(),
                        until_body.space().chain(body.pretty(ctx).indent()).group(),
                    )
                }),
            ),
            Elab::App(x, y) => x
                .pretty(ctx)
                .nest(Prec::App)
                .space()
                .chain(y.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            Elab::Pair(x, y) => Doc::start("(")
                .chain(x.pretty(ctx))
                .add(",")
                .space()
                .chain(y.pretty(ctx))
                .add(")")
                .prec(Prec::Atom),
            Elab::Tag(id) => id.pretty(ctx),
            Elab::StructIntern(i) => Doc::start("struct#").style(Style::Keyword).add(i.num()),
            Elab::StructInline(v) => pretty_block(
                "struct",
                v.iter().map(|(name, val)| {
                    name.pretty(ctx)
                        .style(Style::Binder)
                        .space()
                        .add(":=")
                        .line()
                        .chain(val.pretty(ctx))
                        .group()
                }),
            ),
            Elab::Block(v) => pretty_block(
                "do",
                v.iter().map(|s| match s {
                    ElabStmt::Expr(e) => e.pretty(ctx),
                    ElabStmt::Def(name, val) => name
                        .pretty(ctx)
                        .style(Style::Binder)
                        .space()
                        .add(":=")
                        .line()
                        .chain(val.pretty(ctx))
                        .group(),
                }),
            ),
            Elab::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).chain(m.pretty(ctx)),
            Elab::Union(v) => Doc::intersperse(
                v.iter().map(|x| x.pretty(ctx)),
                Doc::none().space().add("|").space(),
            ),
        }
    }
}
