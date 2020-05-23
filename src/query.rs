use crate::binding::*;
use crate::term::*;
use crate::grammar::*;
use crate::error::*;
use crate::eval::*;
use crate::bicheck::*;
use std::sync::Arc;
use std::collections::HashMap;
use std::sync::{RwLock, RwLockWriteGuard, RwLockReadGuard};

#[derive(Debug, PartialEq, Eq, Default)]
pub struct FileContext {
    pub bindings: Bindings,
    pub vals: HashMap<Sym, Value>,
    pub tys: HashMap<Sym, Value>,
}
impl FileContext {
    fn new(bindings: Bindings) -> Self {
        FileContext {
            bindings,
            vals: HashMap::new(),
            tys: HashMap::new(),
        }
    }

    /// Get a value from the environment, and call `cloned()` on it, returning the owned value
    pub fn val_cloned(&mut self, k: Sym) -> Option<Value> {
        if let Some(x) = self.vals.remove(&k) {
            let v = x.cloned(self);
            self.vals.insert(k, x);
            Some(v)
        } else {
            None
        }
    }

    /// Get a type from the `TEnv`, calling `cloned()` on it and returning the owned value
    /// Analogous to `Context::get_cloned()`
    pub fn ty_cloned(&mut self, s: Sym) -> Option<Value> {
        let x = self.tys.remove(&s)?;
        let t = x.cloned(self);
        self.tys.insert(s, x);
        Some(t)
    }
}

pub trait HasContext {
    fn ctx(&self) -> RwLockWriteGuard<FileContext>;
    fn error(&self, e: Error);
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
    db.ctx().bindings.reset();

    let parser = DefsParser::new();
    let s = db.source(file);
    Arc::new(match parser.parse(&s) {
        Ok(x) => db.ctx().bindings.resolve_defs(x).into_iter().filter_map(|x| match x {
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
    db.defs(file).iter().find(|Def(x, y)| **x == s).map(|Def(x, y)| Arc::new(y.clone()))
}

fn val(db: &impl MainGroup, file: FileId, s: Sym) -> Option<Arc<Value>> {
    let term = db.term(file, s)?;
    let val = term.reduce(&mut db.ctx());
    let val2 = val.cloned(&mut db.ctx());
    db.ctx().vals.insert(s, val2);
    Some(Arc::new(val))
}

fn typ(db: &impl MainGroup, file: FileId, s: Sym) -> Option<Arc<Value>> {
    let term = db.term(file, s)?;
    let ty = synth(&term, &mut db.ctx());
    match ty {
        Ok(ty) => {
            let t2 = ty.cloned(&mut db.ctx());
            db.ctx().tys.insert(s, t2);
            Some(Arc::new(ty))
        }
        Err(e) => {
            db.error(e.to_error(file, &db.ctx().bindings));
            None
        }
    }
}

#[salsa::database(MainStorage)]
#[derive(Default)]
pub struct MainDatabase {
    runtime: salsa::Runtime<MainDatabase>,
    pub ctx: Arc<RwLock<FileContext>>,
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
    fn ctx(&self) -> RwLockWriteGuard<FileContext> {
        self.ctx.write().unwrap()
    }

    fn error(&self, error: Error) {
        self.errors.write().unwrap().push(error);
    }
}
