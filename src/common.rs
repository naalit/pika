pub use crate::builtins::Builtin;
pub use crate::error::*;
pub use crate::lexer::Literal;
pub use crate::pretty::*;
pub use crate::query::*;
pub use crate::term::{BinOp, Term, Val, Var};
pub use std::collections::{HashMap, HashSet, VecDeque};
pub use std::sync::{Arc, RwLock};

/// A helper trait for accepting either owned or borrowed data, and cloning when necessary
pub trait IntoOwned<T> {
    fn into_owned(self) -> T;
}
impl<T> IntoOwned<T> for T {
    fn into_owned(self) -> T {
        self
    }
}
impl<T: Clone> IntoOwned<T> for &T {
    fn into_owned(self) -> T {
        self.clone()
    }
}
impl<T: Clone> IntoOwned<T> for Arc<T> {
    /// Tries to unwrap the Arc if it only has one user, otherwise clones.
    fn into_owned(self) -> T {
        Arc::try_unwrap(self).unwrap_or_else(|a| (*a).clone())
    }
}

/// A three-value logic type, useful for analysis with limited information.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TBool {
    Yes,
    No,
    Maybe,
}
impl TBool {
    /// Converts to a `bool`, panicking on `Maybe`.
    pub fn not_maybe(self) -> bool {
        match self {
            Yes => true,
            No => false,
            Maybe => panic!("Called `TBool::not_maybe()` on `Maybe`"),
        }
    }
}
pub use TBool::{Maybe, No, Yes};
impl std::ops::BitOr for TBool {
    type Output = TBool;

    fn bitor(self, rhs: TBool) -> TBool {
        match (self, rhs) {
            (Yes, _) | (_, Yes) => Yes,
            (No, No) => No,
            _ => Maybe,
        }
    }
}
impl std::ops::BitAnd for TBool {
    type Output = TBool;

    fn bitand(self, rhs: TBool) -> TBool {
        match (self, rhs) {
            (No, _) | (_, No) => No,
            (Yes, Yes) => Yes,
            _ => Maybe,
        }
    }
}
impl std::ops::BitAnd<bool> for TBool {
    type Output = TBool;

    fn bitand(self, rhs: bool) -> TBool {
        self & TBool::from(rhs)
    }
}
impl From<bool> for TBool {
    fn from(b: bool) -> TBool {
        match b {
            true => Yes,
            false => No,
        }
    }
}
