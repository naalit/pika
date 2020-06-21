use crate::bicheck::*;
use crate::common::*;
use crate::elab::*;
use crate::error::*;
use crate::grammar::*;
use crate::lexer::Lexer;
use crate::low::*;
use crate::term::*;
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum ScopeId {
    File(FileId),
    /// Structs are always inside of another scope
    Struct(StructId, Box<ScopeId>),
}
impl ScopeId {
    /// There's always a file down there somewhere
    pub fn file(&self) -> FileId {
        match self {
            ScopeId::File(f) => *f,
            ScopeId::Struct(_, parent) => parent.file(),
        }
    }

    /// Inline the members of this scope into a StructInline
    pub fn inline(&self, db: &impl MainGroup) -> Elab {
        let mut env = db.temp_env(self.clone());
        let v = db
            .symbols(self.clone())
            .iter()
            .filter_map(|s| Some((**s, db.elab(self.clone(), **s)?.cloned(&mut env))))
            .collect();
        Elab::StructInline(v)
    }
}

/// An environment to store temporary mappings of symbols to types or Elabs
/// Used, for instance, for renaming bound variables and typing functions
pub struct TempEnv<'a, T: MainGroup> {
    pub db: &'a T,
    bindings: Arc<RwLock<Bindings>>,
    /// A TempEnv is associated with a scope, and stores the ScopeId
    pub scope: ScopeId,
    pub vals: HashMap<Sym, Arc<Elab>>,
    pub tys: HashMap<Sym, Arc<Elab>>,
    pub low_tys: HashMap<Sym, LowTy>,
}
impl<'a, T: MainGroup> Clone for TempEnv<'a, T> {
    fn clone(&self) -> TempEnv<'a, T> {
        TempEnv {
            scope: self.scope.clone(),
            vals: self.vals.clone(),
            tys: self.tys.clone(),
            low_tys: self.low_tys.clone(),
            bindings: self.bindings.clone(),
            db: self.db,
        }
    }
}
impl<'a, T: MainGroup> TempEnv<'a, T> {
    pub fn scope(&self) -> ScopeId {
        self.scope.clone()
    }

    /// Locks the global bindings object and returns a write guard
    /// Careful: you can't access the bindings from anywhere else if you're holding this object!
    pub fn bindings_mut(&mut self) -> RwLockWriteGuard<Bindings> {
        self.bindings.write().unwrap()
    }

    /// Locks the global bindings object and returns a read guard
    /// Unlike bindings_mut(), you can still access the bindings *immutably* from other places while this object is alive
    pub fn bindings(&self) -> RwLockReadGuard<Bindings> {
        self.bindings.read().unwrap()
    }

    /// Gets the monomorphization for the given named function with the given parameter type, if one exists
    pub fn mono(&self, f: Sym, x: &Elab) -> Option<(String, LowTy)> {
        let mut cloned = self.clone();
        self.db
            .monos()
            .get(&f)?
            .iter()
            .find(|v| {
                let (k, _, _) = &***v;
                x.subtype_of(k, &mut cloned)
            })
            .map(|x| (x.1.clone(), x.2.clone()))
    }

    /// Registers a monomorphization for the given named function with the given parameter type
    pub fn set_mono(&mut self, f: Sym, x: Elab, mono: String, ty: LowTy) {
        self.db
            .monos_mut()
            .entry(f)
            .or_insert_with(Vec::new)
            .push(Arc::new((x, mono, ty)));
    }

    /// Get a value from the environment. Checks the database if we don't have it
    pub fn val(&self, s: Sym) -> Option<Arc<Elab>> {
        self.vals
            .get(&s)
            .cloned()
            .or_else(|| self.db.elab(self.scope(), s))
    }
    /// Set a value in the environment. It should be in WHNF
    pub fn set_val(&mut self, k: Sym, v: Elab) {
        self.vals.insert(k, Arc::new(v));
    }
    /// Get the type of a symbol from the environment. Checks the database if we don't have it
    pub fn ty(&self, s: Sym) -> Option<Arc<Elab>> {
        self.tys.get(&s).cloned().or_else(|| {
            self.db
                .elab(self.scope(), s)
                .map(|x| Arc::new(x.get_type(&mut self.clone())))
        })
    }
    /// Set the type of a symbol in the environment. It should be in WHNF
    pub fn set_ty(&mut self, k: Sym, v: Elab) {
        self.tys.insert(k, Arc::new(v));
    }

    /// Get the type of a symbol from the environment. Checks the database if we don't have it
    pub fn low_ty(&self, s: Sym) -> Option<LowTy> {
        self.low_tys
            .get(&s)
            .cloned()
            .or_else(|| self.db.low_ty(self.scope(), s).ok())
    }
    /// Set the type of a symbol in the environment. It should be in WHNF
    pub fn set_low_ty(&mut self, k: Sym, v: LowTy) {
        self.low_tys.insert(k, v);
    }
}

/// Since queries can't access the database directly, this defines the interface they can use for accessing it
pub trait MainExt {
    type DB: MainGroup;

    fn monos(&self) -> RwLockReadGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>>;

    fn monos_mut(&self) -> RwLockWriteGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>>;

    /// Return a new handle to the global bindings object held by the database
    fn bindings(&self) -> Arc<RwLock<Bindings>>;

    /// Report an error to the user
    /// After calling this, queries should attempt to recover as much as possible and continue on
    fn error(&self, e: Error);

    /// Create a temporary environment associated with the given scope
    fn temp_env<'a>(&'a self, scope: ScopeId) -> TempEnv<'a, Self::DB>;

    /// Add a module to the struct table
    fn add_mod(&self, id: StructId, file: FileId, defs: &Vec<(Spanned<Sym>, STerm)>);

    /// Get a handle to the struct table
    fn struct_defs(&self, file: FileId, id: StructId) -> Option<Arc<Vec<Def>>>;
}

#[salsa::query_group(MainStorage)]
pub trait MainGroup: MainExt + salsa::Database {
    #[salsa::input]
    fn source(&self, file: FileId) -> Arc<String>;

    /// Lists all the definitions in this immediate scope (doesn't include parent scopes)
    fn defs(&self, scope: ScopeId) -> Arc<Vec<Def>>;

    /// Lists all the symbols defined in this immediate scope (doesn't include parent scopes)
    fn symbols(&self, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>>;

    /// Gets the raw term for a definition in this or a parent scope
    fn term(&self, scope: ScopeId, s: Sym) -> Option<Arc<STerm>>;

    /// Gets a definition, type-checked and elaborated
    fn elab(&self, scope: ScopeId, s: Sym) -> Option<Arc<Elab>>;

    /// If the given definition exists, get the name it would be given in code generation
    fn mangle(&self, scope: ScopeId, s: Sym) -> Option<String>;

    /// Lower a definition to a LowIR function with no arguments
    fn low_fun(&self, scope: ScopeId, s: Sym) -> Result<LowFun, LowError>;

    fn low_ty(&self, scope: ScopeId, s: Sym) -> Result<LowTy, LowError>;

    /// Lower a file to a LowIR module
    fn low_mod(&self, file: FileId) -> LowMod;

    /// Returns all scopes in this entire file, including the file scope, in order of definition with the file last
    fn child_scopes(&self, file: FileId) -> Arc<Vec<ScopeId>>;
}

fn child_scopes(db: &impl MainGroup, file: FileId) -> Arc<Vec<ScopeId>> {
    fn add_term(t: &Term, db: &impl MainGroup, v: &mut Vec<ScopeId>, scope: ScopeId) {
        match t {
            Term::Struct(s, _) => add_scope(db, v, ScopeId::Struct(*s, Box::new(scope))),
            Term::App(a, b) | Term::Pair(a, b) | Term::The(a, b) => {
                add_term(a, db, v, scope.clone());
                add_term(b, db, v, scope);
            }
            Term::Binder(_, Some(x)) | Term::Project(x, _) => add_term(x, db, v, scope),
            Term::Block(t) => t.iter().for_each(|x| match x {
                Statement::Expr(x) | Statement::Def(Def(_, x)) => add_term(x, db, v, scope.clone()),
            }),
            Term::Union(t) => t.iter().for_each(|x| add_term(x, db, v, scope.clone())),
            Term::Fun(t) => t.iter().for_each(|(args, body)| {
                args.iter().for_each(|x| add_term(x, db, v, scope.clone()));
                add_term(body, db, v, scope.clone());
            }),
            Term::Unit
            | Term::Var(_)
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Binder(_, None)
            | Term::Tag(_) => (),
        }
    }

    fn add_scope(db: &impl MainGroup, v: &mut Vec<ScopeId>, scope: ScopeId) {
        v.push(scope.clone());
        for Def(_, val) in db.defs(scope.clone()).iter() {
            add_term(val, db, v, scope.clone());
        }
    }

    let mut v = Vec::new();
    add_scope(db, &mut v, ScopeId::File(file));

    Arc::new(
        v.into_iter()
            .skip(1)
            .chain(std::iter::once(ScopeId::File(file)))
            .collect(),
    )
}

fn mangle(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<String> {
    // Return None if it doesn't exist
    let _term = db.term(scope.clone(), s)?;

    // We might mangle types too later

    let b = db.bindings();
    let b = b.read().unwrap();
    Some(format!("{}${}_{}", b.resolve(s), s.num(), scope.file()))
}

fn low_mod(db: &impl MainGroup, file: FileId) -> LowMod {
    for s in db.symbols(ScopeId::File(file)).iter() {
        db.elab(ScopeId::File(file), **s);
    }
    let funs = db
        .child_scopes(file)
        .iter()
        .flat_map(|s| {
            db.symbols(s.clone())
                .iter()
                .map(|n| (s.clone(), **n))
                .collect::<Vec<(ScopeId, Sym)>>()
        })
        .filter_map(|(scope, n)| db.low_fun(scope, n).ok())
        .collect();
    LowMod {
        name: String::from("test_mod"),
        funs,
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum LowError {
    NoElab,
    Polymorphic,
}

fn low_ty(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Result<LowTy, LowError> {
    let elab = db.elab(scope.clone(), s).ok_or(LowError::NoElab)?;

    let mut env = db.temp_env(scope.clone());
    // We don't want the struct defs, since we'll inline it if there are any
    env.tys = HashMap::new();
    let ty = elab.low_ty_of(&mut env).ok_or(LowError::Polymorphic)?;
    Ok(ty)
}

fn low_fun(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Result<LowFun, LowError> {
    let elab = db.elab(scope.clone(), s).ok_or(LowError::NoElab)?;

    let ret_ty = db.low_ty(scope.clone(), s)?;

    let name = db.mangle(scope.clone(), s).ok_or(LowError::NoElab)?;

    let mut env = db.temp_env(scope.clone());
    // We don't want the struct defs, since we'll inline it if there are any
    env.tys = HashMap::new();
    let body = elab.as_low(&mut env).ok_or(LowError::Polymorphic)?;

    Ok(LowFun { name, ret_ty, body })
}

fn symbols(db: &impl MainGroup, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>> {
    Arc::new(db.defs(scope).iter().map(|Def(x, _)| x.clone()).collect())
}

fn defs(db: &impl MainGroup, scope: ScopeId) -> Arc<Vec<Def>> {
    let r = match scope {
        ScopeId::File(file) => {
            // We reset the bindings when we get all the definitions so they're more reproducible and thus memoizable
            db.bindings().write().unwrap().reset();

            let parser = DefsParser::new();
            let s = db.source(file);
            Arc::new(match parser.parse(&s, Lexer::new(&s)) {
                Ok(x) => db
                    .bindings()
                    .write()
                    .unwrap()
                    .resolve_defs(x)
                    .into_iter()
                    .filter_map(|x| match x {
                        Ok(x) => Some(x),
                        Err(e) => {
                            db.error(e.to_error(file));
                            None
                        }
                    })
                    .collect(),
                Err(e) => {
                    db.error(Error::from_lalrpop(e, file));
                    Vec::new()
                }
            })
        }
        ScopeId::Struct(id, _) => db
            .struct_defs(scope.file(), id)
            .unwrap_or_else(|| Arc::new(Vec::new())),
    };

    let mut seen: Vec<Spanned<RawSym>> = Vec::new();
    for Def(sym, _) in r.iter() {
        if let Some(s) = seen.iter().find(|x| ***x == sym.raw()) {
            db.error(
                TypeError::DuplicateField(s.clone(), sym.copy_span(sym.raw()))
                    .to_error(scope.file(), &db.bindings().read().unwrap()),
            );
        } else {
            seen.push(sym.copy_span(sym.raw()));
        }
    }

    r
}

fn term(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<STerm>> {
    let r = db
        .defs(scope.clone())
        .iter()
        .find(|Def(x, _y)| **x == s)
        .map(|Def(_x, y)| Arc::new(y.clone()));
    if let None = r {
        if let ScopeId::Struct(_, parent) = scope {
            return db.term(*parent, s);
        }
    }
    r
}

fn elab(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<Elab>> {
    let term = db.term(scope.clone(), s)?;
    let mut env = db.temp_env(scope.clone());
    // If it calls itself recursively, assume it could be anything.
    // We'll run `simplify_unions` on it later, which should get rid of Bottom if there's a base case
    env.set_ty(s, Elab::Bottom);
    let e = synth(&term, &mut env);
    match e {
        Ok(e) => Some(Arc::new(e)),
        Err(e) => {
            db.error(e.to_error(scope.file(), &db.bindings().read().unwrap()));
            None
        }
    }
}

#[salsa::database(MainStorage)]
#[derive(Debug, Default)]
pub struct MainDatabase {
    runtime: salsa::Runtime<MainDatabase>,
    bindings: Arc<RwLock<Bindings>>,
    errors: RwLock<Vec<Error>>,
    scopes: RwLock<HashMap<(FileId, StructId), Arc<Vec<Def>>>>,
    monos: RwLock<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>>,
}

impl MainDatabase {
    pub fn has_errors(&self) -> bool {
        !self.errors.read().unwrap().is_empty()
    }

    pub fn emit_errors(&self) {
        self.errors
            .write()
            .unwrap()
            .drain(..)
            .for_each(|e| e.write().unwrap());
    }
}

impl salsa::Database for MainDatabase {
    fn salsa_runtime(&self) -> &salsa::Runtime<Self> {
        &self.runtime
    }

    fn salsa_runtime_mut(&mut self) -> &mut salsa::Runtime<Self> {
        &mut self.runtime
    }
}

impl MainExt for MainDatabase {
    type DB = Self;

    fn monos(&self) -> RwLockReadGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>> {
        self.monos.read().unwrap()
    }
    fn monos_mut(&self) -> RwLockWriteGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>> {
        self.monos.write().unwrap()
    }

    fn temp_env<'a>(&'a self, scope: ScopeId) -> TempEnv<'a, Self> {
        TempEnv {
            db: self,
            bindings: self.bindings(),
            scope,
            vals: HashMap::new(),
            tys: HashMap::new(),
            low_tys: HashMap::new(),
        }
    }

    fn bindings(&self) -> Arc<RwLock<Bindings>> {
        self.bindings.clone()
    }

    fn error(&self, error: Error) {
        self.errors.write().unwrap().push(error);
    }

    fn add_mod(&self, id: StructId, file: FileId, defs: &Vec<(Spanned<Sym>, STerm)>) {
        let defs = defs
            .iter()
            .map(|(name, val)| Def(name.clone(), val.clone()))
            .collect();
        self.scopes
            .write()
            .unwrap()
            .insert((file, id), Arc::new(defs));
    }

    fn struct_defs(&self, file: FileId, id: StructId) -> Option<Arc<Vec<Def>>> {
        self.scopes.read().unwrap().get(&(file, id)).cloned()
    }
}
