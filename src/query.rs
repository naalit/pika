use crate::bicheck::*;
use crate::binding::*;
use crate::codegen::*;
use crate::common::*;
use crate::elab::*;
use crate::error::*;
use crate::grammar::*;
use crate::lexer::Lexer;
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
}
impl<'a, T: MainGroup> Clone for TempEnv<'a, T> {
    fn clone(&self) -> TempEnv<'a, T> {
        TempEnv {
            scope: self.scope.clone(),
            vals: self.vals.clone(),
            tys: self.tys.clone(),
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

    /// Clones the TempEnv, creating a child environment in a struct
    pub fn child(&self, struct_id: StructId) -> TempEnv<'a, T> {
        TempEnv {
            scope: ScopeId::Struct(struct_id, Box::new(self.scope.clone())),
            ..self.clone()
        }
    }

    /// Get a value from the environment
    pub fn val(&self, s: Sym) -> Option<Arc<Elab>> {
        self.vals.get(&s).cloned()
    }
    /// Set a value in the environment. It should be in WHNF
    pub fn set_val(&mut self, k: Sym, v: Elab) {
        self.vals.insert(k, Arc::new(v));
    }
    /// Get the type of a symbol from the environment
    pub fn ty(&self, s: Sym) -> Option<Arc<Elab>> {
        self.tys.get(&s).cloned()
    }
    /// Set the type of a symbol in the environment. It should be in WHNF
    pub fn set_ty(&mut self, k: Sym, v: Elab) {
        self.tys.insert(k, Arc::new(v));
    }
}

/// Since queries can't access the database directly, this defines the interface they can use for accessing it
pub trait MainExt {
    type DB: MainGroup;

    /// Return a new handle to the global bindings object held by the database
    fn bindings(&self) -> Arc<RwLock<Bindings>>;

    /// Report an error to the user
    /// After calling this, queries should attempt to recover as much as possible and continue on
    fn error(&self, e: Error);

    /// Create a temporary environment associated with the given file
    fn temp_env<'a>(&'a self, scope: ScopeId) -> TempEnv<'a, Self::DB>;

    /// Do whatever needs to be done after name resolution
    ///
    /// Currently, this is just adding structs to the struct table
    fn process_defs(&self, v: &Vec<Def>);

    /// Get a handle to the struct table
    fn struct_defs(&self, id: StructId) -> Option<Arc<Vec<Def>>>;
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

    /// Gets a definition in Weak-Head Normal Form
    fn val(&self, scope: ScopeId, s: Sym) -> Option<Arc<Elab>>;

    /// If the given definition exists, get the name it would be given in code generation
    fn mangle(&self, scope: ScopeId, s: Sym) -> Option<String>;

    /// Lower a definition to a LowIR function with no arguments
    fn low_fun(&self, scope: ScopeId, s: Sym) -> Result<LowFun, LowError>;

    /// Lower a file to a LowIR module
    fn low_mod(&self, file: FileId) -> LowMod;
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
    let funs = db
        .symbols(ScopeId::File(file))
        .iter()
        .filter_map(|s| db.low_fun(ScopeId::File(file), **s).ok())
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

fn low_fun(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Result<LowFun, LowError> {
    let elab = db.elab(scope.clone(), s).ok_or(LowError::NoElab)?;
    let ty = elab.get_type(&mut db.temp_env(scope.clone()));

    let name = db.mangle(scope.clone(), s).ok_or(LowError::NoElab)?;

    let body = elab
        .as_low(&mut db.temp_env(scope))
        .ok_or(LowError::Polymorphic)?;
    let ret_ty = ty.as_low_ty();

    Ok(LowFun { name, ret_ty, body })
}

fn symbols(db: &impl MainGroup, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>> {
    Arc::new(db.defs(scope).iter().map(|Def(x, _)| x.clone()).collect())
}

fn defs(db: &impl MainGroup, scope: ScopeId) -> Arc<Vec<Def>> {
    match scope {
        ScopeId::File(file) => {
            // We reset the bindings when we get all the definitions so they're more reproducible and thus memoizable
            db.bindings().write().unwrap().reset();

            let parser = DefsParser::new();
            let s = db.source(file);
            let r = Arc::new(match parser.parse(&s, Lexer::new(&s)) {
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
            });
            db.process_defs(&r);
            r
        }
        ScopeId::Struct(id, _) => db.struct_defs(id).unwrap_or_else(|| Arc::new(Vec::new())),
    }
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

fn val(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<Elab>> {
    let x = db.elab(scope.clone(), s)?;
    let mut env = db.temp_env(scope);
    let mut x = x.cloned(&mut env.clone());
    x.whnf(&mut env);
    Some(Arc::new(x))
}

fn elab(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<Elab>> {
    let term = db.term(scope.clone(), s)?;
    let e = synth(&term, &mut db.temp_env(scope.clone()));
    match e {
        Ok(e) => Some(Arc::new(e)),
        Err(e) => {
            db.error(e.to_error(scope.file(), &db.bindings().read().unwrap()));
            None
        }
    }
}

#[salsa::database(MainStorage)]
#[derive(Default)]
pub struct MainDatabase {
    runtime: salsa::Runtime<MainDatabase>,
    bindings: Arc<RwLock<Bindings>>,
    errors: RwLock<Vec<Error>>,
    scopes: RwLock<HashMap<StructId, Arc<Vec<Def>>>>,
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

    fn temp_env<'a>(&'a self, scope: ScopeId) -> TempEnv<'a, Self> {
        TempEnv {
            db: self,
            bindings: self.bindings(),
            scope,
            vals: HashMap::new(),
            tys: HashMap::new(),
        }
    }

    fn bindings(&self) -> Arc<RwLock<Bindings>> {
        self.bindings.clone()
    }

    fn error(&self, error: Error) {
        self.errors.write().unwrap().push(error);
    }

    fn process_defs(&self, defs: &Vec<Def>) {
        // let mut scopes = self.scopes.write().unwrap();
        let scopes = &self.scopes;
        for Def(_, val) in defs {
            val.traverse(|t| match t {
                Term::Struct(id, v) => {
                    let v = v
                        .iter()
                        .map(|(name, val)| Def(name.clone(), val.clone()))
                        .collect();
                    scopes.write().unwrap().insert(*id, Arc::new(v));
                }
                _ => (),
            })
        }
    }

    fn struct_defs(&self, id: StructId) -> Option<Arc<Vec<Def>>> {
        self.scopes.read().unwrap().get(&id).cloned()
    }
}
