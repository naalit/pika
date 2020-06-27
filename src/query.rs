use crate::bicheck::*;
use crate::binding::*;
use crate::common::{FileId, HasBindings, HasDatabase};
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
    pub fn inline(&self, db: &impl HasDatabase) -> Elab {
        let mut cln = Cloner::new(db);
        let v = db
            .database()
            .symbols(self.clone())
            .iter()
            .filter_map(|s| Some((**s, db.database().elab(self.clone(), **s)?.cloned(&mut cln))))
            .collect();
        Elab::StructInline(v)
    }
}

/// Since queries can't access the database directly, this defines the interface they can use for accessing it
pub trait MainExt: HasBindings {
    fn monos(&self) -> RwLockReadGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>>;

    fn monos_mut(&self) -> RwLockWriteGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>>;

    /// Report an error to the user
    /// After calling this, queries should attempt to recover as much as possible and continue on
    fn error(&self, e: Error);

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
            // This is only used for lowering, and data constructors aren't lowered
            Term::Data(_, _, _, _) => (),
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
            Term::Fun(_, t) => t.iter().for_each(|(args, body)| {
                args.iter().for_each(|x| add_term(x, db, v, scope.clone()));
                add_term(body, db, v, scope.clone());
            }),
            Term::Unit
            | Term::Var(_)
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Binder(_, None)
            | Term::Tag(_)
            | Term::Cons(_, _) => (),
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

    let scoped = (scope, db);
    let mut lctx = LCtx::new(&scoped);
    let ty = elab.low_ty_of(&mut lctx).ok_or(LowError::Polymorphic)?;
    Ok(ty)
}

fn low_fun(db: &impl MainGroup, scope: ScopeId, s: Sym) -> Result<LowFun, LowError> {
    let elab = db.elab(scope.clone(), s).ok_or(LowError::NoElab)?;

    let ret_ty = db.low_ty(scope.clone(), s)?;

    let name = db.mangle(scope.clone(), s).ok_or(LowError::NoElab)?;

    let scoped = (scope, db);
    let mut lctx = LCtx::new(&scoped);
    let body = elab.as_low(&mut lctx).ok_or(LowError::Polymorphic)?;

    Ok(LowFun { name, ret_ty, body })
}

fn symbols(db: &impl MainGroup, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>> {
    Arc::new(db.defs(scope).iter().map(|Def(x, _)| x.clone()).collect())
}

fn defs(db: &impl MainGroup, scope: ScopeId) -> Arc<Vec<Def>> {
    let r = match scope {
        ScopeId::File(file) => {
            // We reset the bindings when we get all the definitions so they're more reproducible and thus memoizable
            db.bindings_mut().reset();

            let parser = DefsParser::new();
            let s = db.source(file);
            Arc::new(match parser.parse(&s, Lexer::new(&s)) {
                Ok(x) => db
                    .bindings_mut()
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
                    .to_error(scope.file(), db),
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

    let scoped = (scope.clone(), db);
    let mut tctx = TCtx::new(&scoped);
    // If it calls itself recursively, assume it could be anything.
    // We'll run `simplify_unions` on it later, which should get rid of Bottom if there's a base case
    tctx.set_ty(s, Elab::Bottom);
    let e = synth(&term, &mut tctx);
    match e {
        Ok(e) => {
            if let Err(e) = e.check_affine(&mut crate::affine::ACtx::new(&scoped)) {
                db.error(e);
            }
            // We let it go anyway so we don't get "type not found" errors when borrow checking fails
            // We'll check if db.has_errors() before going too far
            Some(Arc::new(e))
        }
        Err(e) => {
            db.error(e.to_error(scope.file(), db));
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

impl HasBindings for MainDatabase {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        &self.bindings
    }
}

impl MainExt for MainDatabase {
    fn monos(&self) -> RwLockReadGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>> {
        self.monos.read().unwrap()
    }
    fn monos_mut(&self) -> RwLockWriteGuard<HashMap<Sym, Vec<Arc<(Elab, String, LowTy)>>>> {
        self.monos.write().unwrap()
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
