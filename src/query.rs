use crate::binding::*;
use crate::term::*;
use crate::grammar::*;
use crate::error::*;
use crate::eval::*;
use crate::bicheck::*;
use std::sync::Arc;
use std::collections::HashMap;
use std::sync::{RwLock, RwLockWriteGuard, RwLockReadGuard};

pub struct TempEnv {
    pub bindings: Arc<RwLock<Bindings>>,
    pub file: FileId,
    pub vals: HashMap<Sym, Arc<Value>>,
    pub tys: HashMap<Sym, Arc<Value>>,
}
impl TempEnv {
    pub fn bindings_mut(&mut self) -> RwLockWriteGuard<Bindings> {
        self.bindings.write().unwrap()
    }
    pub fn bindings(&self) -> RwLockReadGuard<Bindings> {
        self.bindings.read().unwrap()
    }
    pub fn child(&mut self) -> TempEnv {
        TempEnv {
            bindings: self.bindings.clone(),
            file: self.file,
            vals: self.vals.clone(),
            tys: self.tys.clone(),
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

pub trait HasContext {
    fn bindings(&self) -> Arc<RwLock<Bindings>>;
    fn error(&self, e: Error);

    fn temp_env(&self, file: FileId) -> TempEnv {
        TempEnv {
            bindings: self.bindings(),
            file,
            vals: HashMap::new(),
            tys: HashMap::new(),
        }
    }
}

#[salsa::query_group(MainStorage)]
pub trait MainGroup: HasContext + salsa::Database {
    #[salsa::input]
    fn source(&self, file: FileId) -> Arc<String>;

    fn defs(&self, file: FileId) -> Arc<Vec<Def>>;

    fn symbols(&self, file: FileId) -> Arc<Vec<Spanned<Sym>>>;

    fn term(&self, file: FileId, s: Sym) -> Option<Arc<STerm>>;

    fn typ(&self, file: FileId, s: Sym) -> Option<Arc<Value>>;

    fn val(&self, file: FileId, s: Sym) -> Option<Arc<Value>>;
}

fn symbols(db: &impl MainGroup, file: FileId) -> Arc<Vec<Spanned<Sym>>> {
    Arc::new(db.defs(file).iter().map(|Def(x, _)| x.clone()).collect())
}

fn defs(db: &impl MainGroup, file: FileId) -> Arc<Vec<Def>> {
    db.bindings().write().unwrap().reset();

    let parser = DefsParser::new();
    let s = db.source(file);
    Arc::new(match parser.parse(&s) {
        Ok(x) => db.bindings().write().unwrap().resolve_defs(x).into_iter().filter_map(|x| match x {
            Ok(x) => Some(x),
            Err(e) => {
                db.error(e.to_error(file));
                None
            }
        }).collect(),
        Err(e) => {
            db.error(Error::from_lalrpop(e, file));
            Vec::new()
        }
    })
}

fn term(db: &impl MainGroup, file: FileId, s: Sym) -> Option<Arc<STerm>> {
    db.defs(file).iter().find(|Def(x, _y)| **x == s).map(|Def(_x, y)| Arc::new(y.clone()))
}

fn val(db: &impl MainGroup, file: FileId, s: Sym) -> Option<Arc<Value>> {
    let term = db.term(file, s)?;
    let val = term.reduce(db, &mut db.temp_env(file));
    Some(Arc::new(val))
}

fn typ(db: &impl MainGroup, file: FileId, s: Sym) -> Option<Arc<Value>> {
    let term = db.term(file, s)?;
    let ty = synth(&term, db, &mut db.temp_env(file));
    match ty {
        Ok(ty) => {
            // let t2 = ty.cloned(db, file);
            Some(Arc::new(ty))
        }
        Err(e) => {
            db.error(e.to_error(file, &db.bindings().read().unwrap()));
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
}

impl MainDatabase {
    pub fn has_errors(&self) -> bool {
        !self.errors.read().unwrap().is_empty()
    }

    pub fn emit_errors(&self) {
        self.errors.write().unwrap().drain(..).for_each(|e| e.write().unwrap());
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

impl HasContext for MainDatabase {
    fn bindings(&self) -> Arc<RwLock<Bindings>> {
        self.bindings.clone()
    }

    fn error(&self, error: Error) {
        self.errors.write().unwrap().push(error);
    }
}
