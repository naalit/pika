pub use crate::binding::*;
pub use crate::elab::*;
pub use crate::error::{Error, Span};
pub use crate::options::*;
pub use crate::printing::*;
pub use crate::query::*;
pub use std::collections::HashMap;
pub use std::sync::{Arc, RwLock};
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

pub type FileId = usize;

pub trait HasBindings {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>>;

    fn bindings_mut(&self) -> RwLockWriteGuard<Bindings> {
        self.bindings_ref().write().unwrap()
    }

    fn bindings(&self) -> RwLockReadGuard<Bindings> {
        self.bindings_ref().read().unwrap()
    }
}
impl<T: HasBindings> HasBindings for &T {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        (*self).bindings_ref()
    }
}
impl<T: HasBindings> HasBindings for &mut T {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        (**self).bindings_ref()
    }
}

pub use crate::error::Spanned;
use crate::low::{LowFun, LowMod, LowTy};
use crate::term::{Def, STerm};

pub trait MainGroupP: MainExt {
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
impl<T: MainGroup> MainGroupP for T {
    fn source(&self, file: FileId) -> Arc<String> {
        MainGroup::source(self, file)
    }
    fn defs(&self, scope: ScopeId) -> Arc<Vec<Def>> {
        MainGroup::defs(self, scope)
    }
    fn symbols(&self, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>> {
        MainGroup::symbols(self, scope)
    }
    fn term(&self, scope: ScopeId, s: Sym) -> Option<Arc<STerm>> {
        MainGroup::term(self, scope, s)
    }
    fn elab(&self, scope: ScopeId, s: Sym) -> Option<Arc<Elab>> {
        MainGroup::elab(self, scope, s)
    }
    fn mangle(&self, scope: ScopeId, s: Sym) -> Option<String> {
        MainGroup::mangle(self, scope, s)
    }
    fn low_fun(&self, scope: ScopeId, s: Sym) -> Result<LowFun, LowError> {
        MainGroup::low_fun(self, scope, s)
    }
    fn low_ty(&self, scope: ScopeId, s: Sym) -> Result<LowTy, LowError> {
        MainGroup::low_ty(self, scope, s)
    }
    fn low_mod(&self, file: FileId) -> LowMod {
        MainGroup::low_mod(self, file)
    }
    fn child_scopes(&self, file: FileId) -> Arc<Vec<ScopeId>> {
        MainGroup::child_scopes(self, file)
    }
}

pub trait HasDatabase: HasBindings {
    fn database(&self) -> &dyn MainGroupP;
}

pub trait Scoped {
    fn scope(&self) -> ScopeId;
}

// These three make it so `(scope, &database)` is `impl Scoped + HasDatabase`
impl<T: MainGroup> HasBindings for (ScopeId, &T) {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.1.bindings_ref()
    }
}
impl<T: MainGroup> HasDatabase for (ScopeId, &T) {
    fn database(&self) -> &dyn MainGroupP {
        self.1
    }
}
impl<T> Scoped for (ScopeId, T) {
    fn scope(&self) -> ScopeId {
        self.0.clone()
    }
}
