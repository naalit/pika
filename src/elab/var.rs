use std::collections::VecDeque;
use super::val::Val;

// De Brujin indices and levels
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Idx(u32);
impl Idx {
    pub fn lvl(self, size: Size) -> Lvl {
        Lvl(size.0 - 1 - self.0)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Lvl(u32);
impl Lvl {
    pub fn idx(self, size: Size) -> Idx {
        Idx(size.0 - 1 - self.0)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Size(u32);
impl Size {
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
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Meta(u32);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Var<L> {
    Local(L),
    Meta(Meta),
    Builtin(super::term::Builtin),
    Def(),
}


#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct EnvState(usize);

#[derive(Clone)]
pub struct Env {
    /// Since locals are De Bruijn indices, we store a `VecDeque`, push to the front and index normally.
    /// When elaborating, we often want to evaluate something without any locals, or just add one or two at the front.
    /// To make that efficient, we leave off the tail of `None`s, and if an index goes past the length, it's `None`.
    vals: VecDeque<Option<Val>>,
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
        EnvState(self.vals.len())
    }
    pub fn reset(&mut self, state: EnvState) {
        let old = self.vals.len();
        let dif = state.0 - old;
        self.size.0 -= dif as u32;
        self.vals.truncate(state.0);
    }

    pub fn get(&self, i: Idx) -> Option<&Val> {
        self.vals
            .get(i.0 as usize)
            .map(Option::as_ref)
            .flatten()
    }

    /// If it's not present, returns a local variable value
    pub fn val(&self, i: Idx) -> Val {
        self.vals
            .get(i.0 as usize)
            .cloned()
            .flatten()
            .unwrap_or_else(|| Val::var(Var::Local(i.lvl(self.size))))
    }

    pub fn push(&mut self, v: Option<Val>) {
        self.size = self.size.inc();
        if v.is_some() || !self.vals.is_empty() {
            self.vals.push_front(v);
        }
    }

    pub fn pop(&mut self) {
        self.size = self.size.dec();
        self.vals.pop_front();
    }
}
