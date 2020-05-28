use crate::bicheck::*;
use crate::binding::*;
use crate::codegen::*;
use crate::common::*;
use crate::error::*;
use crate::eval::*;
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

/// An environment to store temporary mappings of symbols to types or values
/// Used, for instance, for renaming bound variables and typing functions
#[derive(Clone)]
pub struct TempEnv {
    bindings: Arc<RwLock<Bindings>>,
    /// A TempEnv is associated with a scope, and stores the ScopeId
    pub scope: ScopeId,
    pub vals: HashMap<Sym, Arc<Value>>,
    pub tys: HashMap<Sym, Arc<Value>>,
}
impl TempEnv {
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
    pub fn child(&self, struct_id: StructId) -> TempEnv {
        TempEnv {
            scope: ScopeId::Struct(struct_id, Box::new(self.scope.clone())),
            ..self.clone()
        }
    }

    pub fn val(&self, s: Sym) -> Option<Arc<Value>> {
        self.vals.get(&s).cloned()
    }
    pub fn set_val(&mut self, k: Sym, v: Value) {
        self.vals.insert(k, Arc::new(v));
    }
    pub fn ty(&self, s: Sym) -> Option<Arc<Value>> {
        self.tys.get(&s).cloned()
    }
    pub fn set_ty(&mut self, k: Sym, v: Value) {
        self.tys.insert(k, Arc::new(v));
    }
}

/// Since queries can't access the database directly, this defines the interface they can use for accessing it
pub trait MainExt {
    /// Return a new handle to the global bindings object held by the database
    fn bindings(&self) -> Arc<RwLock<Bindings>>;

    /// Report an error to the user
    /// After calling this, queries should attempt to recover as much as possible and continue on
    fn error(&self, e: Error);

    /// Create a temporary environment associated with the given file
    fn temp_env(&self, scope: ScopeId) -> TempEnv {
        TempEnv {
            bindings: self.bindings(),
            scope,
            vals: HashMap::new(),
            tys: HashMap::new(),
        }
    }

    /// Do whatever needs to be done after name resolution
    ///
    /// Currently, this is just adding structs to the struct table
    fn process_defs(&self, v: &Vec<Def>);

    fn struct_defs(&self, id: StructId) -> Option<Arc<Vec<Def>>>;
}

#[salsa::query_group(MainStorage)]
pub trait MainGroup: MainExt + salsa::Database {
    #[salsa::input]
    fn source(&self, file: FileId) -> Arc<String>;

    fn defs(&self, scope: ScopeId) -> Arc<Vec<Def>>;

    fn symbols(&self, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>>;

    fn term(&self, scope: ScopeId, s: Sym) -> Option<Arc<STerm>>;

    fn typ(&self, scope: ScopeId, s: Sym) -> Option<Arc<Value>>;

    fn val(&self, scope: ScopeId, s: Sym) -> Option<Arc<Value>>;

    fn mangle(&self, scope: ScopeId, s: Sym) -> Option<String>;

    fn low_fun(&self, scope: ScopeId, s: Sym) -> Option<LowFun>;

    fn low_mod(&self, file: FileId) -> LowMod;
}

fn mangle(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<String> {
    // Return None if it doesn't exist
    let _term = db.term(scope.clone(), s)?;
    // We might mangle types too later
    // let ty = db.typ(scope.clone(), s)?;

    let b = db.bindings();
    let b = b.read().unwrap();
    Some(format!("{}${}_{}", b.resolve(s), s.num(), scope.file()))
}

fn low_mod(db: &impl MainGroup, file: FileId) -> LowMod {
    let funs = db
        .symbols(ScopeId::File(file))
        .iter()
        .filter_map(|s| db.low_fun(ScopeId::File(file), **s))
        .collect();
    LowMod {
        name: String::from("test_mod"),
        funs,
    }
}

fn low_fun(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<LowFun> {
    let term = db.term(scope.clone(), s)?;
    let ty = db.typ(scope.clone(), s)?;

    let name = db.mangle(scope.clone(), s)?;

    let ret_ty = ty.as_low_ty();
    let body = term.as_low(db, &mut db.temp_env(scope));

    Some(LowFun { name, ret_ty, body })
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

fn val(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<Value>> {
    let term = db.term(scope.clone(), s)?;
    let val = term.reduce(db, &mut db.temp_env(scope));
    Some(Arc::new(val))
}

fn typ(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<Value>> {
    let term = db.term(scope.clone(), s)?;
    let ty = synth(&term, db, &mut db.temp_env(scope.clone()));
    match ty {
        Ok(ty) => Some(Arc::new(ty)),
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
