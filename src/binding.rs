use std::collections::HashMap;
use std::num::NonZeroU32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sym(NonZeroU32);

#[derive(Clone, Debug)]
pub struct NameError(String);

/// Implements globally-unique binding - every bound variable is unique, and we can freshen them if we copy it
/// That means we don't ever have to worry about capture-avoidance outside of this module
#[derive(Default, Debug, Clone)]
pub struct Bindings {
    /// It's possible this is a memory problem (storing each string twice), but if so we'll deal with it then
    strings: HashMap<String, usize>,
    string_pool: Vec<String>,
    /// For every Sym(i), the corresponding string lives at string_pool[bindings[i - 1] as usize]
    /// -1 b/c it's a NonZeroU32, and it stores u32's for memory friendliness
    bindings: Vec<u32>,
}
impl Bindings {
    pub fn resolve_names<'p>(t: STree<'p>) -> Result<(Self, STerm), NameError> {
        let s = Bindings::default();
        let mut env = NEnv::new(s);
        let t = t
            .resolve_names(&mut env)
            .map_err(|x| NameError(x.to_string()))?;
        let s = env.bindings;
        Ok((s, t))
    }

    /// Create a new symbol. It's guaranteed to be unique to all other symbols created with create()
    pub fn create(&mut self, s: String) -> Sym {
        let i = self.strings.get(&s).cloned().unwrap_or_else(|| {
            let i = self.string_pool.len();
            self.strings.insert(s.clone(), i);
            self.string_pool.push(s);
            i
        });
        let u = self.bindings.len();
        self.bindings.push(i as u32);
        Sym(NonZeroU32::new(u as u32 + 1).expect("unreachable"))
    }

    /// This doesn't return an Option, because only the Bindings can create symbols, and it adds them to `self.bindings`
    /// Therefore, if you pass a symbol created by another Bindings instance, this may panic
    pub fn resolve(&self, s: Sym) -> &str {
        let pool_idx = *self.bindings.get(s.0.get() as usize - 1).expect("Symbol passed to resolve() too large, did you create it with a different Bindings instance?");
        self.string_pool
            .get(pool_idx as usize)
            .expect("unreachable")
    }
}

use crate::error::Spanned;
use crate::term::*;

/// The AST before name resolution
#[derive(Debug, Clone, PartialEq)]
pub enum ParseTree<'p> {
    Unit,                               // ()
    Let(&'p str, STree<'p>, STree<'p>), // let x = y in z
    Binder(&'p str, STree<'p>),         // x: T
    Var(&'p str),                       // a
    I32(i32),                           // 3
    Type,                               // Type
    Builtin(Builtin),                   // Int
    Fun(STree<'p>, STree<'p>),          // fn a => x
    App(STree<'p>, STree<'p>),          // f x
    Pair(STree<'p>, STree<'p>),         // x, y
}
type STree<'p> = Spanned<ParseTree<'p>>;

/// Implements scoping with a Vec instead of a HashMap. We search from the back.
struct NEnv<'p> {
    symbols: Vec<(&'p str, Sym)>,
    /// Stores the length of `symbols` where we left off in the enclosing scope
    /// That way, we don't have to do anything extra when we add to `symbols`, and we can just `resize()` it when we `pop()`
    scopes: Vec<usize>,
    bindings: Bindings,
}
impl<'p> NEnv<'p> {
    fn new(bindings: Bindings) -> Self {
        NEnv {
            symbols: Vec::new(),
            scopes: Vec::new(),
            bindings,
        }
    }

    fn get(&self, s: &str) -> Option<Sym> {
        self.symbols.iter().rfind(|(x, _)| *x == s).map(|(_, x)| *x)
    }

    fn push(&mut self) {
        self.scopes.push(self.symbols.len())
    }
    fn pop(&mut self) {
        let n = self.scopes.pop().expect("NEnv::pop() without a push()!");
        self.symbols.resize_with(n, || {
            panic!("NEnv::pop() got a scope longer than `symbols`!")
        });
    }

    /// Creates a new binding with a name
    fn create(&mut self, k: &'p str) -> Sym {
        let s = self.bindings.create(k.to_string());
        self.symbols.push((k, s));
        s
    }
}

impl<'p> STree<'p> {
    fn resolve_names(self, env: &mut NEnv<'p>) -> Result<STerm, &'p str> {
        use ParseTree::*;
        let span = self.span();
        Ok(Spanned::new(
            match self.try_unwrap().unwrap() {
                Unit => Term::Unit,
                Type => Term::Type,
                Builtin(b) => Term::Builtin(b),
                I32(i) => Term::I32(i),
                Var(x) => Term::Var(env.get(x).ok_or(x)?),
                Let(v, t, u) => {
                    env.push();
                    // Not recursive (yet, at least)
                    let t = t.resolve_names(env)?;
                    let v = env.create(v);
                    let u = u.resolve_names(env)?;
                    let l = Term::Let(v, t, u);
                    env.pop();
                    l
                }
                Binder(x, t) => {
                    // Binders aren't recursive in their types
                    let t = t.resolve_names(env)?;
                    Term::Binder(env.create(x), t)
                }
                Fun(arg, body) => {
                    env.push();
                    let arg = arg.resolve_names(env)?;
                    let body = body.resolve_names(env)?;
                    let f = Term::Fun(arg, body);
                    env.pop();
                    f
                }
                App(f, x) => Term::App(f.resolve_names(env)?, x.resolve_names(env)?),
                Pair(x, y) => {
                    // Pairs can be dependent, so we need a scope
                    env.push();
                    let x = x.resolve_names(env)?;
                    let y = y.resolve_names(env)?;
                    let p = Term::Pair(x, y);
                    env.pop();
                    p
                }
            },
            span,
        ))
    }
}
