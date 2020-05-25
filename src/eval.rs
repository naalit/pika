use crate::common::*;
use crate::term::*;

impl Term {
    /// Evaluate a `Term` into its `Value` representation (i.e. normal form), given a context
    ///
    /// Note that this function can accept, and reduce, ill-typed terms, so always typecheck a `Term` before reducing it
    pub fn reduce(&self, db: &impl MainGroup, env: &mut TempEnv) -> Value {
        match self {
            Term::Unit => Value::Unit,
            Term::I32(i) => Value::I32(*i),
            Term::Type => Value::Type,
            Term::Builtin(b) => Value::Builtin(*b),
            Term::Var(s) => match db.val(env.file, *s).or_else(|| env.val(*s)) {
                Some(x) => x.cloned(&mut env.child()),
                // Free variable
                None => Value::Var(*s),
            },
            Term::Binder(s, t) => {
                Value::Binder(*s, t.as_ref().map(|t| Box::new(t.reduce(db, env))))
            }
            Term::The(_, t) => t.reduce(db, env),
            Term::Pair(x, y) => {
                Value::Pair(Box::new(x.reduce(db, env)), Box::new(y.reduce(db, env)))
            }
            Term::Fun(x, y) => Value::Fun(Box::new(x.reduce(db, env)), Box::new(y.reduce(db, env))),
            Term::App(f, x) => {
                let f = f.reduce(db, env);
                let x = x.reduce(db, env);
                match f {
                    Value::Fun(args, mut body) => {
                        args.do_match(&x, env);
                        body.update(env);
                        *body
                    }
                    // Neutral - we can't apply it yet
                    f => Value::App(Box::new(f), Box::new(x)),
                }
            }
        }
    }
}

type BVal = Box<Value>;
/// A term in normal form
///
/// Unlike `Term`s, values don't store source `Span`s. For that reason and others, errors should usually be found *before* reducing a `Term` to a `Value`.
#[derive(Debug, PartialEq, Eq)]
pub enum Value {
    Unit,                      // ()
    Binder(Sym, Option<BVal>), // x: T
    Var(Sym),                  // a
    I32(i32),                  // 3
    Type,                      // Type
    Builtin(Builtin),          // Int
    Fun(BVal, BVal),           // fn a => x
    /// Applicand must be neutral
    App(BVal, BVal), // f x
    Pair(BVal, BVal),          // x, y
}
impl Value {
    /// Adds substitutions created by matching `other` with `self` (`self` is the pattern) to `ctx`
    /// Does not check if it's a valid match, that's the typechecker's job
    pub fn do_match(&self, other: &Value, env: &mut TempEnv) {
        use Value::*;
        match (self, other) {
            (Binder(s, _), _) => {
                let other = other.cloned(env);
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
        use Value::*;
        match self {
            Var(s) => {
                if let Some(x) = env.val(*s) {
                    x.cloned(env)
                } else {
                    // Free variable
                    Var(*s)
                }
            }
            Unit => Unit,
            Type => Type,
            I32(i) => I32(*i),
            Builtin(b) => Builtin(*b),
            App(f, x) => App(Box::new(f.cloned(env)), Box::new(x.cloned(env))),
            // Rename bound variables
            // This case runs before any that depend on it, and the Value has unique names
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
                env.set_val(*s, Var(fresh));
                Binder(fresh, t.as_ref().map(|t| Box::new(t.cloned(env))))
            }
            // All these allow bound variables, so we have to make sure they're done in order
            Fun(f, x) => {
                let f = Box::new(f.cloned(env));
                let x = Box::new(x.cloned(env));
                Fun(f, x)
            }
            Pair(x, y) => {
                let x = Box::new(x.cloned(env));
                let y = Box::new(y.cloned(env));
                Pair(x, y)
            }
        }
    }

    /// If this `Value` contains any free variables, we check to see if they have a value in the environment yet
    /// If they do, we perform the substitution, in place
    pub fn update(&mut self, env: &mut TempEnv) {
        match self {
            Value::Var(x) => {
                if let Some(new) = env.val(*x) {
                    *self = new.cloned(env)
                } else if cfg!(feature = "logging") {
                    println!("No match for {}{}", env.bindings().resolve(*x), x.num());
                }
            }
            Value::Binder(_, Some(x)) => x.update(env),
            Value::App(f, x) => {
                f.update(env);
                x.update(env);
                match &mut **f {
                    Value::Fun(args, body) => {
                        args.do_match(&x, env);
                        body.update(env);
                        *self = body.cloned(env);
                    }
                    // Still not a function
                    _ => (),
                }
            }
            Value::Pair(x, y) | Value::Fun(x, y) => {
                x.update(env);
                y.update(env);
            }
            _ => (),
        }
    }
}
impl CDisplay for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter, b: &Bindings) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Binder(x, None) => write!(f, "({}{}:)", b.resolve(*x), x.num()),
            Value::Binder(x, Some(t)) => {
                write!(f, "{}{}: {}", b.resolve(*x), x.num(), WithContext(b, &**t))
            }
            Value::Var(s) => write!(f, "{}{}", b.resolve(*s), s.num()),
            Value::I32(i) => write!(f, "{}", i),
            Value::Type => write!(f, "Type"),
            Value::Builtin(b) => write!(f, "{:?}", b),
            Value::Fun(x, y) => write!(
                f,
                "fun {} => {}",
                WithContext(b, &**x),
                WithContext(b, &**y)
            ),
            Value::App(x, y) => write!(f, "({})({})", WithContext(b, &**x), WithContext(b, &**y)),
            Value::Pair(x, y) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
        }
    }
}
