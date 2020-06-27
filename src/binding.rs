use crate::common::*;
use crate::error::Spanned;
use crate::term::*;
use std::collections::HashMap;
use std::num::NonZeroU32;

/// Like a Sym, but it identifies a data constructor
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct TagId(NonZeroU32);
impl TagId {
    pub fn num(self) -> u32 {
        self.0.get() - 1
    }
}

/// Like a Sym, but it identifies a data type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct TypeId(NonZeroU32);
impl TypeId {
    pub fn num(self) -> u32 {
        self.0.get() - 1
    }
}

/// Like a Sym, but it identifies a record (= struct, module)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct StructId(NonZeroU32);
impl StructId {
    pub fn num(self) -> u32 {
        self.0.get() - 1
    }
}

/// Represents an interned string directly
///
/// Same size properties as Sym
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct RawSym(NonZeroU32);
impl RawSym {
    fn new(idx: usize) -> Self {
        RawSym(NonZeroU32::new(idx as u32 + 1).expect("unreachable"))
    }
    fn idx(self) -> usize {
        self.0.get() as usize - 1
    }
}

/// An index into the pool of interned strings held by a `Bindings` object
///
/// It's the size of a u32 but is optimized for things like `Option<Sym>` (because it has a `NonZeroU32` inside)
/// The 18 least significant bits represent the raw symbol (interned string), the top 14 the instance of that symbol
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct Sym(NonZeroU32);
impl Sym {
    fn from_parts(raw: RawSym, num: u32) -> Self {
        let idx = raw.idx();
        if idx >= 1 << 18 {
            panic!("Too many unique identifiers!");
        }
        if num >= 1 << 14 {
            panic!("Too many instances of identifier {}!", idx);
        }
        Sym(NonZeroU32::new((num << 18) | idx as u32 + 1).expect("unreachable"))
    }
    fn with_num(self, num: u32) -> Self {
        Sym::from_parts(self.raw(), num)
    }

    /// Gets the number corresponding to this symbol, so we can show the user that two symbols with the same name are distinct
    pub fn num(self) -> u32 {
        (self.0.get() - 1) >> 18
    }

    /// Gets the raw symbol corresponding to this symbol
    /// This can be used for comparing identifiers directly, as in record labels
    pub fn raw(self) -> RawSym {
        RawSym(NonZeroU32::new(((self.0.get() - 1) & ((1 << 18) - 1)) + 1).expect("unreachable"))
    }
}

impl Pretty for TypeId {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        let ctx = ctx.bindings();
        let raw = ctx.tags[(self.0.get() - 1) as usize];
        let name = ctx.resolve_raw(raw).to_owned();
        Doc::start(name)
    }
}
impl Pretty for TagId {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        let ctx = ctx.bindings();
        let raw = ctx.tags[(self.0.get() - 1) as usize];
        let name = ctx.resolve_raw(raw).to_owned();
        Doc::start(name)
    }
}
impl Pretty for RawSym {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        let name = ctx.bindings().resolve_raw(*self).to_owned();
        Doc::start(name)
    }
}
impl Pretty for Sym {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        let name = ctx.bindings().resolve(*self).to_owned();
        Doc::start(name)
    }
}

/// They used a variable that wasn't in scope
#[derive(Clone, Debug)]
pub struct NameError(Spanned<String>);
impl NameError {
    pub fn to_error(&self, file: FileId) -> Error {
        Error::new(
            file,
            format!("Error: variable not found: {}", *self.0),
            self.0.span(),
            "not found",
        )
    }
}

/// Implements globally-unique binding - every bound variable is unique, and we can freshen them if we copy it
/// That means we don't ever have to worry about capture-avoidance outside of this module and `Value::cloned()`
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Bindings {
    /// It's possible this is a memory problem (storing each string twice), but if so we'll deal with it then
    strings: HashMap<String, RawSym>,
    string_pool: Vec<String>,
    nums: HashMap<RawSym, u32>,
    /// Both `TagId`s and `TypeId`s use the same lookup table
    tags: Vec<RawSym>,
    tag_to_type: Vec<Option<TypeId>>,
}
impl Bindings {
    /// Don't do this if you're holding symbols somewhere!
    pub fn reset(&mut self) {
        let mut b = Bindings::default();
        std::mem::swap(&mut b, self);
        // We want the RawSyms to be the same
        let Bindings {
            strings,
            string_pool,
            ..
        } = b;
        self.strings = strings;
        self.string_pool = string_pool;
    }

    pub fn tag_name(&self, t: TagId) -> RawSym {
        self.tags[(t.0.get() - 1) as usize]
    }

    pub fn tag_to_type(&self, t: TagId) -> Option<TypeId> {
        self.tag_to_type[(t.0.get() - 1) as usize]
    }

    /// Interns a string (or gets it if it's already interned), returning the RawSym to it
    pub fn raw(&mut self, s: String) -> RawSym {
        self.strings.get(&s).cloned().unwrap_or_else(|| {
            let i = RawSym::new(self.string_pool.len());
            self.strings.insert(s.clone(), i);
            self.string_pool.push(s);
            i
        })
    }

    /// Creates a new symbol with the same name as `s`, but a fresh value
    pub fn fresh(&mut self, s: Sym) -> Sym {
        let u = self
            .nums
            .get_mut(&s.raw())
            .expect("Symbol not in Bindings!");
        *u += 1;
        s.with_num(*u - 1)
    }

    pub fn resolve_defs<'p>(&mut self, t: Vec<ParseDef<'p>>) -> Vec<Result<Def, NameError>> {
        let mut env = NEnv::new(self);
        t.into_iter()
            .map(|ParseDef(lhs, rhs)| {
                let lhs = lhs.copy_span(env.create(&lhs));
                (lhs, rhs)
            })
            // Define everything in the scope before resolving right hand sides
            .collect::<Vec<_>>()
            .into_iter()
            .map(|(lhs, rhs)| {
                let rhs = rhs
                    .resolve_names(&mut env)
                    .map_err(|x| NameError(x.copy_span(x.to_string())))?;
                Ok(Def(lhs, rhs))
            })
            .collect()
    }

    /// Create a new symbol. It's guaranteed to be unique to all other symbols created with create()
    pub fn create(&mut self, s: String) -> Sym {
        let raw = self.raw(s);
        let u = self.nums.entry(raw).or_insert(0);
        *u += 1;
        Sym::from_parts(raw, *u - 1)
    }

    /// This doesn't return an Option, because only the Bindings can create symbols, and it adds them to `self.bindings`
    /// Therefore, if you pass a symbol created by another Bindings instance, this may panic
    pub fn resolve(&self, s: Sym) -> &str {
        self.string_pool
            .get(s.raw().idx())
            .expect("String referred to by symbol not in Bindings interned string table!")
    }

    pub fn resolve_raw(&self, s: RawSym) -> &str {
        self.string_pool
            .get(s.idx())
            .expect("String referred to by symbol not in Bindings interned string table!")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseStmt<'p> {
    Def(ParseDef<'p>),
    Expr(STree<'p>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseDef<'p>(pub Spanned<&'p str>, pub Spanned<ParseTree<'p>>);

/// The AST before name resolution
///
/// This is what the parser generates. All names are stored as string slices
#[derive(Debug, Clone, PartialEq)]
pub enum ParseTree<'p> {
    Unit,                                        // ()
    The(STree<'p>, STree<'p>),                   // the T x
    Binder(&'p str, Option<STree<'p>>),          // x: T
    Var(&'p str),                                // a
    I32(i32),                                    // 3
    Type(u32),                                   // Type0
    Builtin(Builtin),                            // Int
    Fun(bool, Vec<(Vec<STree<'p>>, STree<'p>)>), // move? fn { a b => x; c d => y }
    App(STree<'p>, STree<'p>),                   // f x
    Pair(STree<'p>, STree<'p>),                  // x, y
    Struct(Vec<(Spanned<&'p str>, STree<'p>)>),  // struct { x := 3 }
    Project(STree<'p>, Spanned<&'p str>),        // r.m
    Block(Vec<ParseStmt<'p>>),                   // do { x; y }
    Union(Vec<STree<'p>>),                       // x | y
    Data {
        // type T of C a b
        name: Spanned<&'p str>,                   // Pair
        ty: STree<'p>,                            // fun Type => Type
        cons: Vec<(Spanned<&'p str>, STree<'p>)>, // (MkPair, fun (a:Type) a a => Pair a)
    },
}
type STree<'p> = Spanned<ParseTree<'p>>;

/// Implements scoping with a Vec instead of a HashMap. We search from the back, so we can use it like a stack.
struct NEnv<'p, 'b> {
    symbols: Vec<(&'p str, Sym)>,
    /// Stores the length of `symbols` where we left off in the enclosing scope
    /// That way, we don't have to do anything extra when we add to `symbols`, and we can just `resize()` it when we `pop()` the scope
    scopes: Vec<usize>,
    bindings: &'b mut Bindings,
    struct_id: u32,
}
impl<'p, 'b> NEnv<'p, 'b> {
    fn new(bindings: &'b mut Bindings) -> Self {
        NEnv {
            symbols: Vec::new(),
            scopes: Vec::new(),
            bindings,
            struct_id: 0,
        }
    }

    // The `TagId` and `TypeId` intern-spaces are the same
    fn next_tag(&mut self, k: &'p str, ty: Option<TypeId>) -> TagId {
        let raw = self.bindings.raw(k.to_string());
        self.bindings.tags.push(raw);
        self.bindings.tag_to_type.push(ty);
        TagId(NonZeroU32::new(self.bindings.tags.len() as u32).unwrap())
    }
    fn next_type(&mut self, k: &'p str) -> TypeId {
        let raw = self.bindings.raw(k.to_string());
        self.bindings.tags.push(raw);
        self.bindings.tag_to_type.push(None);
        TypeId(NonZeroU32::new(self.bindings.tags.len() as u32).unwrap())
    }

    fn next_struct(&mut self) -> StructId {
        self.struct_id += 1;
        StructId(NonZeroU32::new(self.struct_id).unwrap())
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
    fn resolve_names<'b>(self, env: &mut NEnv<'p, 'b>) -> Result<STerm, Spanned<&'p str>> {
        use ParseTree::*;
        let span = self.span();
        Ok(Spanned::new(
            match self.force_unwrap() {
                Data { name, ty, cons } => {
                    let id = env.next_type(*name);
                    let st = env.next_struct();
                    let ty = ty.resolve_names(env)?;

                    let mut rv = Vec::new();
                    for (name, ty) in cons {
                        let tag = env.next_tag(*name, Some(id));
                        let name = name.copy_span(env.create(*name));
                        let ty = ty.resolve_names(env)?;
                        rv.push((name, tag, ty));
                    }

                    Term::Data(id, st, ty, rv)
                }
                Unit => Term::Unit,
                Type(i) => Term::Type(i),
                Builtin(b) => Term::Builtin(b),
                I32(i) => Term::I32(i),
                Var(x) => Term::Var(env.get(x).ok_or(Spanned::new(x, span))?),
                The(t, u) => Term::The(t.resolve_names(env)?, u.resolve_names(env)?),
                Binder(x, t) => {
                    // Binders aren't recursive in their types
                    let t = t.map(|t| t.resolve_names(env)).transpose()?;
                    Term::Binder(env.create(x), t)
                }
                Fun(m, iv) => {
                    let mut rv = Vec::new();
                    for (args, body) in iv {
                        env.push();
                        let mut ra = Vec::new();
                        for a in args {
                            ra.push(a.resolve_names(env)?);
                        }
                        let body = body.resolve_names(env)?;
                        rv.push((ra, body));
                        env.pop();
                    }
                    Term::Fun(m, rv)
                }
                App(f, x) => Term::App(f.resolve_names(env)?, x.resolve_names(env)?),
                Pair(x, y) => {
                    // Pairs can be dependent, so we can have binders
                    // But, pairs don't have an isolated scope, their definitions leak out
                    let x = x.resolve_names(env)?;
                    let y = y.resolve_names(env)?;
                    Term::Pair(x, y)
                }
                Struct(iv) => {
                    env.push();
                    let mut rv = Vec::new();
                    // Declare all the names first, then resolve names in rhs's
                    let iv: Vec<_> = iv
                        .into_iter()
                        .map(|(name, val)| (name.copy_span(env.create(*name)), val))
                        .collect();
                    for (name, val) in iv {
                        let val = val.resolve_names(env)?;
                        rv.push((name, val));
                    }
                    env.pop();
                    Term::Struct(env.next_struct(), rv)
                }
                Project(r, m) => Term::Project(
                    r.resolve_names(env)?,
                    m.copy_span(env.bindings.raw(m.to_string())),
                ),
                Block(iv) => {
                    env.push();
                    let mut rv = Vec::new();
                    for i in iv {
                        match i {
                            ParseStmt::Expr(val) => {
                                rv.push(Statement::Expr(val.resolve_names(env)?));
                            }
                            ParseStmt::Def(ParseDef(name, val)) => {
                                let val = val.resolve_names(env)?;
                                let name = name.copy_span(env.create(*name));
                                rv.push(Statement::Def(Def(name, val)));
                            }
                        }
                    }
                    env.pop();
                    Term::Block(rv)
                }
                Union(mut iv) => {
                    let mut rv = Vec::new();
                    let first = iv.split_off(iv.len() - 1);
                    // There's only one, but this is easier
                    for val in first {
                        rv.push(val.resolve_names(env)?);
                    }
                    for val in iv {
                        rv.push(val.resolve_names(env)?);
                    }
                    Term::Union(rv)
                }
            },
            span,
        ))
    }
}
