pub use crate::binding::*;
pub use crate::elab::Cloner;
pub use crate::elab::Clos;
pub use crate::error::Error;
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
