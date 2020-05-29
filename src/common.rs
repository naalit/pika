pub use crate::binding::{Bindings, ParseTree, RawSym, StructId, Sym};
pub use crate::error::Error;
pub use crate::query::*;
use std::fmt;

pub type FileId = usize;

/// `std::fmt::Display`, but with context (`Bindings`)
pub trait CDisplay {
    fn fmt(&self, f: &mut fmt::Formatter, b: &Bindings) -> fmt::Result;
}
pub struct WithContext<'b, T>(pub &'b Bindings, pub T);

impl<'b, 'c, T: CDisplay> fmt::Display for WithContext<'b, &'c T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let WithContext(b, t) = self;
        t.fmt(f, b)
    }
}