use crate::common::*;
use crate::term::Builtin;

#[derive(Debug, PartialEq, Eq)]
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
/// For a term to get to here, it must be well typed
#[derive(Debug, PartialEq, Eq)]
pub enum Elab {
    Unit,                           // ()
    Binder(Sym, BElab),             // x: T
    Var(Sym, BElab),                // (a, T) --> the T a
    I32(i32),                       // 3
    Type,                           // Type
    Builtin(Builtin),               // Int
    Fun(BElab, BElab, BElab),       // (a, x, T) --> fn a => the T x
    App(BElab, BElab),              // f x
    Pair(BElab, BElab),             // x, y
    Tag(TagId),                     // tag X
    StructIntern(StructId),         // struct { x := 3 }
    StructInline(Vec<(Sym, Elab)>), // struct { x := 3 }
    Project(BElab, RawSym),         // r.m
    Block(Vec<ElabStmt>),           // do { x; y }
}
type BElab = Box<Elab>;

impl Elab {
    /// Does this term reference this symbol at all?
    pub fn uses<T: MainGroup>(&self, s: Sym, env: &TempEnv<T>) -> bool {
        use Elab::*;
        match self {
            Type | Unit | I32(_) | Builtin(_) | Tag(_) => false,
            Var(x, ty) => *x == s || ty.uses(s, env),
            Fun(a, b, c) => a.uses(s, env) || b.uses(s, env) || c.uses(s, env),
            // We don't beta-reduce here
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
        }
    }

    /// Reduce to full normal form, essentially recursively calling whnf()
    pub fn normal<T: MainGroup>(&mut self, env: &mut TempEnv<T>) {
        // Call whnf()
        self.whnf(env);
        // And recurse
        use Elab::*;
        match self {
            Type | Unit | I32(_) | Builtin(_) | Tag(_) => (),
            Var(_, ty) => ty.normal(env),
            Fun(a, b, c) => {
                a.normal(env);
                b.normal(env);
                c.normal(env);
            }
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
        }
    }

    /// Reduce to Weak-Head Normal Form, in place. This implies `update_all(env)`
    /// Returns whether the top-level structure changed
    ///
    /// This is like actual normal form, but we only perform one level of beta- or projection-reduction
    /// So we're guaranteed not to have `(\x.t)u` at the top level, but we could have e.g. `(\x.(\y.t)u)`
    /// This is the form we store types in, so if you need to compare types you'll need to call `whnf` recursively
    pub fn whnf<T: MainGroup>(&mut self, env: &mut TempEnv<T>) -> bool {
        match self {
            // Binders don't count as forms
            Elab::Binder(_, t) => t.whnf(env),
            Elab::Var(x, _) => {
                if let Some(t) = env.db.val(env.scope(), *x).or_else(|| env.val(*x)) {
                    if &*t != self {
                        *self = t.cloned(&mut env.clone());
                        return self.whnf(env);
                    }
                }
                false
            }
            Elab::App(f, x) => {
                // We recursively WHNF the head
                f.whnf(env);
                match &mut **f {
                    Elab::Fun(args, body, _) => {
                        args.do_match(&x, env);
                        body.whnf(env);
                        *self = body.cloned(env);
                        true
                    }
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

    pub fn get_type<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Elab {
        use crate::term::Builtin as B;
        use Elab::*;
        match self {
            Type => Type,
            Unit => Unit,
            I32(_) => Builtin(B::Int),
            Builtin(B::Int) => Type,
            Tag(t) => Tag(*t),
            Var(_, t) => t.cloned(&mut env.clone()),
            Fun(from, _, to) => {
                let mut env = env.clone();
                Fun(
                    Box::new(from.cloned(&mut env)),
                    Box::new(to.cloned(&mut env)),
                    Box::new(Type),
                )
            }
            App(f, x) => match f.get_type(env) {
                Fun(from, mut to, _) => {
                    from.do_match(x, env);
                    to.whnf(env);
                    *to
                }
                f @ Tag(_) | f @ App(_, _) => App(Box::new(f), Box::new(x.get_type(env))),
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
        }
    }

    /// Adds substitutions created by matching `other` with `self` (`self` is the pattern) to `ctx`
    /// Does not check if it's a valid match, that's the typechecker's job
    pub fn do_match<T: MainGroup>(&self, other: &Elab, env: &mut TempEnv<T>) {
        use Elab::*;
        match (self, other) {
            (Binder(s, _), _) => {
                let other = other.cloned(&mut env.clone());
                #[cfg(feature = "logging")]
                {
                    println!("Setting {}{}", env.bindings().resolve(*s), s.num());
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
                if let Some(x) = env.val(*s) {
                    // Here's how this happens:
                    // 1. We come up with a Elab using, say, x3. That Elab gets stored in Salsa's database.
                    // 2. We reset the Bindings, define x0, x1, and x2, and ask for the Elab again.
                    // 3. Salsa gives us the Elab from the database, which references x3. We call cloned() on it.
                    // 4. We see a bound variable, x3, and define a fresh variable to replace it with. The fresh variable is now also x3.
                    // 5. Now we want to replace x3 with x3, so we better not call cloned() recursively or we'll get stuck in a loop.
                    // Note, though, that this is expected behaviour and doesn't need fixing.
                    if &*x == self {
                        Var(*s, Box::new(t.cloned(env)))
                    } else {
                        x.cloned(env)
                    }
                } else {
                    // Free variable
                    Var(*s, Box::new(t.cloned(env)))
                }
            }
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
            Fun(f, x, t) => {
                let f = Box::new(f.cloned(env));
                let x = Box::new(x.cloned(env));
                let t = Box::new(t.cloned(env));
                Fun(f, x, t)
            }
            Pair(x, y) => {
                let x = Box::new(x.cloned(env));
                let y = Box::new(y.cloned(env));
                Pair(x, y)
            }
            StructIntern(i) => StructIntern(*i),
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
        }
    }
}

/// Handles prettifying curried functions
/// Does not yet prettify multiple args with the same type (`fun x y: Int => ...` is `fun (x: Int) (y: Int) => ...`)
fn pretty_fun<'a>(mut args: Vec<Doc<'a>>, body: &'a Elab, ctx: &Bindings) -> Doc<'a> {
    match body {
        Elab::Fun(arg, body, _) => {
            args.push(arg.pretty(ctx).nest(Prec::Atom));
            pretty_fun(args, body, ctx)
        }
        _ => {
            let until_body = Doc::start("fun")
                .style(Style::Keyword)
                .line()
                .chain(Doc::intersperse(args, Doc::none().line()))
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
            Elab::Var(s, _) => s.pretty(ctx),
            Elab::I32(i) => Doc::start(i).style(Style::Literal),
            Elab::Type => Doc::start("Type"),
            Elab::Builtin(b) => Doc::start(b),
            Elab::Fun(x, y, _) => pretty_fun(vec![x.pretty(ctx).nest(Prec::Atom)], y, ctx),
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
            Elab::StructInline(v) => Doc::either(
                Doc::start("struct")
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
                        v.iter().map(|(name, val)| {
                            name.pretty(ctx)
                                .style(Style::Binder)
                                .space()
                                .add(":=")
                                .line()
                                .chain(val.pretty(ctx))
                                .group()
                        }),
                        Doc::none().line(),
                    ))
                    .group()
                    .indent(),
                Doc::start("struct")
                    .style(Style::Keyword)
                    .space()
                    .add("{")
                    .space()
                    .chain(Doc::intersperse(
                        v.iter().map(|(name, val)| {
                            name.pretty(ctx)
                                .style(Style::Binder)
                                .space()
                                .add(":=")
                                .space()
                                .chain(val.pretty(ctx))
                                .group()
                        }),
                        Doc::start(";").space(),
                    ))
                    .space()
                    .add("}")
                    .group(),
            )
            .prec(Prec::Term),
            Elab::Block(v) => Doc::either(
                Doc::start("do")
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
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
                        Doc::none().line(),
                    ))
                    .group()
                    .indent(),
                Doc::start("do")
                    .style(Style::Keyword)
                    .space()
                    .add("{")
                    .space()
                    .chain(Doc::intersperse(
                        v.iter().map(|s| match s {
                            ElabStmt::Expr(e) => e.pretty(ctx),
                            ElabStmt::Def(name, val) => name
                                .pretty(ctx)
                                .style(Style::Binder)
                                .space()
                                .add(":=")
                                .space()
                                .chain(val.pretty(ctx))
                                .group(),
                        }),
                        Doc::start(";").space(),
                    ))
                    .space()
                    .add("}")
                    .group(),
            )
            .prec(Prec::Term),
            Elab::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).chain(m.pretty(ctx)),
        }
    }
}
