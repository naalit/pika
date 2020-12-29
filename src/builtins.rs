use crate::common::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    I32,
    I64,
    BinOp(BinOp),
}
impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Builtin::I32 => "I32",
            Builtin::I64 => "I64",
            Builtin::BinOp(b) => b.name(),
        }
    }

    pub fn pretty(self) -> Doc {
        Doc::start(self.name())
    }

    pub fn ty(self) -> Val {
        match self {
            Builtin::I32 | Builtin::I64 => Val::Type,
            Builtin::BinOp(b) => b.ty(),
        }
    }
}

pub fn define_builtins<T: ?Sized + Interner>(cxt: Cxt, db: &T) -> Cxt {
    use Builtin::*;
    let list = vec![I32, I64];

    let mut cxt = cxt;
    for b in list {
        let name = b.name();
        let ty = b.ty();
        cxt = cxt.define(
            db.intern_name(name.to_owned()),
            NameInfo::Other(Var::Builtin(b), ty),
            db,
        );
    }
    cxt
}
