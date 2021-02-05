use crate::common::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    I32,
    I64,
    BinOp(BinOp),
    Bool,
    True,
    False,
    Unit,
    UnitType,
}
impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Builtin::I32 => "I32",
            Builtin::I64 => "I64",
            Builtin::Bool => "Bool",
            Builtin::BinOp(b) => b.name(),
            Builtin::True => "True",
            Builtin::False => "False",
            Builtin::Unit => "()",
            Builtin::UnitType => "()",
        }
    }

    pub fn pretty(self) -> Doc {
        Doc::start(self.name())
    }

    pub fn ty(self) -> Val {
        match self {
            Builtin::I32 | Builtin::I64 | Builtin::Bool | Builtin::UnitType => Val::Type,
            Builtin::True | Builtin::False => Val::builtin(Builtin::Bool, Val::Type),
            Builtin::Unit => Val::builtin(Builtin::UnitType, Val::Type),
            Builtin::BinOp(b) => b.ty(),
        }
    }
}

pub fn define_builtins<T: ?Sized + Interner>(cxt: Cxt, db: &T) -> Cxt {
    use Builtin::*;
    let list = vec![I32, I64, Bool, True, False];

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
