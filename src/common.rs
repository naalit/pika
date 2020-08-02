pub use crate::binding::*;
pub use crate::builtins::*;
pub use crate::elab::*;
pub use crate::error::{Error, Span};
pub use crate::options::*;
pub use crate::pattern::{Pat, TBool::*};
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
impl<T: HasBindings + ?Sized> HasBindings for &T {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        (*self).bindings_ref()
    }
}
impl<T: HasBindings + ?Sized> HasBindings for &mut T {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        (**self).bindings_ref()
    }
}

pub use crate::error::Spanned;
use crate::term::{Def, STerm};

pub trait HasDatabase: HasBindings {
    fn database(&self) -> &dyn MainGroup;
}

pub trait Scoped {
    fn scope(&self) -> ScopeId;
}

// These three make it so `(scope, &database)` is `impl Scoped + HasDatabase`
impl<T: MainGroup + ?Sized> HasBindings for (ScopeId, &T) {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.1.bindings_ref()
    }
}
// This has weird interactions with Sized, so &dyn works better than <T: MainGroup>
impl HasDatabase for (ScopeId, &dyn MainGroup) {
    fn database(&self) -> &dyn MainGroup {
        self.1
    }
}
impl<T> Scoped for (ScopeId, T) {
    fn scope(&self) -> ScopeId {
        self.0.clone()
    }
}
