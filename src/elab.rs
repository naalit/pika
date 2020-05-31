use crate::common::*;
use crate::term::Builtin;


#[derive(Debug, PartialEq, Eq)]
pub enum ElabStmt {
    Def(Sym, Elab),
    Expr(Elab),
}
impl ElabStmt {
    pub fn cloned(&self, env: &mut TempEnv) -> Self {
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
    Unit,                               // ()
    Binder(Sym, BElab),                 // x: T
    Var(Sym, BElab),                    // (a, T) --> the T a
    I32(i32),                           // 3
    Type,                               // Type
    Builtin(Builtin),                   // Int
    Fun(BElab, BElab, BElab),           // (a, x, T) --> fn a => the T x
    App(BElab, BElab),                  // f x
    Pair(BElab, BElab),                 // x, y
    Struct(StructId, Vec<(Sym, Elab)>), // struct { x := 3 }
    Project(BElab, RawSym),             // r.m
    Block(Vec<ElabStmt>),                                 // do { x; y }
}
type BElab = Box<Elab>;

impl Elab {
    pub fn get_type(&self, env: &mut TempEnv) -> Elab {
        use crate::term::Builtin as B;
        use Elab::*;
        match self {
            Type => Type,
            Unit => Unit,
            I32(_) => Builtin(B::Int),
            Builtin(B::Int) => Type,
            Var(_, t) => t.cloned(&mut env.clone()),
            Fun(from, _, to) => Fun(
                Box::new(from.cloned(&mut env.clone())),
                Box::new(to.cloned(&mut env.clone())),
                Box::new(Type),
            ),
            App(f, _) => {
                if let Fun(_, to, _) = f.get_type(env) {
                    *to
                } else {
                    panic!("not a function type")
                }
            }
            Pair(x, y) => Pair(Box::new(x.get_type(env)), Box::new(y.get_type(env))),
            Binder(_, x) => x.get_type(env),
            // The `id` here is actually wrong, but I don't think anything currently uses it after this?
            Struct(id, v) => Struct(*id, v.iter().map(|(n, x)| (*n, x.get_type(env))).collect()),
            Project(r, m) => {
                if let Struct(_, t) = r.get_type(env) {
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
            }
        }
    }

    /// Adds substitutions created by matching `other` with `self` (`self` is the pattern) to `ctx`
    /// Does not check if it's a valid match, that's the typechecker's job
    pub fn do_match(&self, other: &Elab, env: &mut TempEnv) {
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
            // We will allow this for now, and see if it causes any problems
            (App(af, ax), App(bf, bx)) => {
                af.do_match(bf, env);
                ax.do_match(bx, env);
            }
            _ => (),
        }
    }

    /// Clones `self`. Unlike a normal clone, we freshen any bound variables (but not free variables)
    /// This means that other code doesn't have to worry about capture-avoidance, we do it here for free
    pub fn cloned(&self, env: &mut TempEnv) -> Self {
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
            Struct(i, v) => Struct(
                *i,
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

    /// If this `Elab` contains any free variables, we check to see if they have a Elab in the environment yet
    /// If they do, we perform the substitution, in place
    pub fn update(&mut self, env: &mut TempEnv) {
        match self {
            Elab::Var(x, _) => {
                if let Some(new) = env.val(*x) {
                    *self = new.cloned(env)
                } else if cfg!(feature = "logging") {
                    println!("No match for {}{}", env.bindings().resolve(*x), x.num());
                }
            }
            Elab::Binder(_, x) => x.update(env),
            Elab::App(f, x) => {
                f.update(env);
                x.update(env);
                match &mut **f {
                    Elab::Fun(args, body, _) => {
                        args.do_match(&x, env);
                        body.update(env);
                        *self = body.cloned(env);
                    }
                    // Still not a function
                    _ => (),
                }
            }
            Elab::Project(r, m) => {
                r.update(env);
                match &**r {
                    Elab::Struct(_, v) => {
                        let (_, val) = v.iter().find(|(name, _)| name.raw() == *m).unwrap();
                        *self = val.cloned(&mut env.clone());
                    }
                    // Still not a record
                    _ => (),
                }
            }
            Elab::Fun(x, y, z) => {
                x.update(env);
                y.update(env);
                z.update(env);
            }
            Elab::Pair(x, y) => {
                x.update(env);
                y.update(env);
            }
            _ => (),
        }
    }
}
impl CDisplay for Elab {
    fn fmt(&self, f: &mut std::fmt::Formatter, b: &Bindings) -> std::fmt::Result {
        match self {
            Elab::Unit => write!(f, "()"),
            Elab::Binder(x, t) => {
                write!(f, "{}{}: {}", b.resolve(*x), x.num(), WithContext(b, &**t))
            }
            Elab::Var(s, t) => write!(
                f,
                "(the ({}) {}{})",
                WithContext(b, &**t),
                b.resolve(*s),
                s.num()
            ),
            Elab::I32(i) => write!(f, "{}", i),
            Elab::Type => write!(f, "Type"),
            Elab::Builtin(b) => write!(f, "{:?}", b),
            Elab::Fun(x, y, to) => write!(
                f,
                "fun {} => the ({}) ({})",
                WithContext(b, &**x),
                WithContext(b, &**to),
                WithContext(b, &**y),
            ),
            Elab::App(x, y) => write!(f, "({})({})", WithContext(b, &**x), WithContext(b, &**y)),
            Elab::Pair(x, y) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
            Elab::Struct(i, v) => {
                write!(f, "struct_{} {{ ", i.num())?;
                for (name, val) in v.iter() {
                    write!(
                        f,
                        "{}{} := {}, ",
                        b.resolve(*name),
                        name.num(),
                        WithContext(b, &*val)
                    )?;
                }
                write!(f, "}}")
            }
                        Elab::Block(v) => {
                            write!(f, "do {{ ")?;
                            for s in v.iter() {
                                match s {
                                    ElabStmt::Expr(e) => write!(f, "{}; ", WithContext(b, e)),
                                    ElabStmt::Def(name, val) => write!(
                                        f,
                                        "{}{} := {}; ",
                                        b.resolve(*name),
                                        name.num(),
                                        WithContext(b, val)
                                    ),
                                }?;
                            }
                            write!(f, "}}")
                        }
            Elab::Project(r, m) => write!(f, "({}).{}", WithContext(b, &**r), b.resolve_raw(*m),),
        }
    }
}
