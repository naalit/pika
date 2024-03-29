use super::{metas::Meta, val::Val, Cons, Elaborator};
use crate::common::*;
use std::collections::VecDeque;

// De Brujin indices and levels
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Idx(u32);
impl Idx {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn zero() -> Idx {
        Idx(0)
    }

    pub fn lvl(self, size: Size) -> Lvl {
        assert!(
            self.0 + 1 <= size.0,
            "Can't access a variable (idx {}) that hasn't been bound yet (enclosing = {})!",
            self.0,
            size.0,
        );
        Lvl(size.0 - 1 - self.0)
    }

    pub fn in_scope(self, size: Size) -> bool {
        self.0 + 1 <= size.0
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct Lvl(u32);
impl Lvl {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn idx(self, size: Size) -> Idx {
        assert!(
            self.0 + 1 <= size.0,
            "Can't access a variable (lvl {}) that hasn't been bound yet (enclosing = {})!",
            self.0,
            size.0,
        );
        Idx(size.0 - 1 - self.0)
    }

    pub fn in_scope(self, size: Size) -> bool {
        self.0 + 1 <= size.0
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size(u32);
impl Size {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn zero() -> Size {
        Size(0)
    }

    pub fn next_lvl(self) -> Lvl {
        Lvl(self.0)
    }

    pub fn inc(self) -> Size {
        Size(self.0 + 1)
    }

    pub fn dec(self) -> Size {
        Size(self.0 - 1)
    }

    pub fn until(self, other: Size) -> impl Iterator<Item = Size> {
        (self.0..other.0).map(Size)
    }
}
impl std::ops::Add<usize> for Size {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Size(self.0 + rhs as u32)
    }
}
impl std::ops::AddAssign<usize> for Size {
    fn add_assign(&mut self, rhs: usize) {
        *self = *self + rhs;
    }
}

#[derive(Debug, Copy, Clone, Eq, Hash)]
pub enum Var<L> {
    Local(SName, L),
    Meta(Meta),
    Builtin(super::term::Builtin),
    Def(SName, Def),
    Cons(SName, Cons),
}
impl<T> Var<T> {
    pub fn as_local(self) -> Option<T> {
        match self {
            Var::Local(_, l) => Some(l),
            _ => None,
        }
    }

    pub fn with_sname(self, n: SName) -> Var<T> {
        match self {
            Var::Local(_, l) => Var::Local(n, l),
            Var::Def(_, d) => Var::Def(n, d),
            Var::Cons(_, d) => Var::Cons(n, d),
            Var::Meta(_) | Var::Builtin(_) => self,
        }
    }

    pub fn name(self, db: &dyn Elaborator) -> Option<Name> {
        match self {
            Var::Local(n, _) | Var::Def(n, _) | Var::Cons(n, _) => Some(n.0),
            Var::Meta(_) => None,
            Var::Builtin(b) => Some(b.name(db)),
        }
    }
}
impl Var<Lvl> {
    pub fn cvt(self, size: Size) -> Var<Idx> {
        match self {
            Var::Local(n, l) => Var::Local(n, l.idx(size)),
            Var::Meta(m) => Var::Meta(m),
            Var::Builtin(b) => Var::Builtin(b),
            Var::Def(n, d) => Var::Def(n, d),
            Var::Cons(n, d) => Var::Cons(n, d),
        }
    }
}
impl Var<Idx> {
    pub fn cvt(self, size: Size) -> Var<Lvl> {
        match self {
            Var::Local(n, l) => Var::Local(n, l.lvl(size)),
            Var::Meta(m) => Var::Meta(m),
            Var::Builtin(b) => Var::Builtin(b),
            Var::Def(n, d) => Var::Def(n, d),
            Var::Cons(n, d) => Var::Cons(n, d),
        }
    }
}
impl<L: PartialEq> PartialEq for Var<L> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Local(_, l1), Self::Local(_, r1)) => l1 == r1,
            (Self::Meta(l0), Self::Meta(r0)) => l0 == r0,
            (Self::Builtin(l0), Self::Builtin(r0)) => l0 == r0,
            (Self::Def(_, l0), Self::Def(_, r0)) => l0 == r0,
            _ => false,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct EnvState(Size);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Env {
    /// Since locals are De Bruijn indices, we store a `VecDeque`, push to the front and index normally.
    /// When elaborating, we often want to evaluate something without any locals, or just add one or two at the front.
    /// To make that efficient, we leave off the tail of `None`s, and if an index goes past the length, it's `None`.
    /// Also, we can use the environment for re-indexing locals - when we do this, we use the Err case
    vals: VecDeque<Option<Result<Val, Lvl>>>,
    pub size: Size,
}
impl Env {
    pub fn new(size: Size) -> Self {
        Env {
            vals: VecDeque::new(),
            size,
        }
    }

    pub fn state(&self) -> EnvState {
        EnvState(self.size)
    }
    pub fn reset(&mut self, state: EnvState) {
        self.reset_to_size(state.0);
    }

    pub fn reset_to_size(&mut self, size: Size) {
        for _ in size.until(self.size) {
            if self.vals.pop_front().is_none() {
                break;
            }
        }
        self.size = size.min(self.size);
    }

    pub fn get(&self, i: Idx) -> Option<&Result<Val, Lvl>> {
        self.vals.get(i.0 as usize).map(Option::as_ref).flatten()
    }

    pub fn get_as_val(&self, n: SName, i: Idx) -> Option<Val> {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .map(|x| x.unwrap_or_else(|l| Val::var(Var::Local(n, l))))
    }

    /// If it's not present, returns a local variable value
    pub fn val(&self, n: SName, i: Idx) -> Val {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .map(|x| x.unwrap_or_else(|l| Val::var(Var::Local(n, l))))
            .unwrap_or_else(|| Val::var(Var::Local(n, i.lvl(self.size))))
    }

    pub fn push(&mut self, v: Option<Result<Val, Lvl>>) {
        self.size = self.size.inc();
        if v.is_some() || !self.vals.is_empty() {
            self.vals.push_front(v);
        }
    }

    pub fn pop(&mut self) {
        self.size = self.size.dec();
        self.vals.pop_front();
    }

    pub fn replace(&mut self, i: Idx, v: Val) {
        assert!(i.in_scope(self.size));
        while self.vals.len() <= i.as_u32() as usize {
            self.vals.push_back(None);
        }
        self.vals[i.as_u32() as usize] = Some(Ok(v));
    }
}
impl Extend<Option<Val>> for Env {
    fn extend<T: IntoIterator<Item = Option<Val>>>(&mut self, iter: T) {
        for i in iter {
            self.push(i.map(Ok));
        }
    }
}
