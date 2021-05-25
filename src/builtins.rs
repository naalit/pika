use crate::common::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    I32,
    I64,
    F32,
    F64,
    String,
    BinOp(BinOp),
    Bool,
    True,
    False,
    Unit,
    UnitType,
    Eff,
    IO,
    Print,
    Puts,
}
impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Builtin::I32 => "I32",
            Builtin::I64 => "I64",
            Builtin::F32 => "F32",
            Builtin::F64 => "F64",
            Builtin::Bool => "Bool",
            Builtin::BinOp(b) => b.name(),
            Builtin::True => "True",
            Builtin::False => "False",
            Builtin::Unit => "()",
            Builtin::UnitType => "()",
            Builtin::Eff => "Eff",
            Builtin::IO => "IO",
            Builtin::Print => "print",
            Builtin::String => "String",
            Builtin::Puts => "puts",
        }
    }

    pub fn pretty(self) -> Doc {
        Doc::start(self.name())
    }

    pub fn ty(self) -> Val {
        match self {
            Builtin::I32
            | Builtin::I64
            | Builtin::F32
            | Builtin::F64
            | Builtin::String
            | Builtin::Bool
            | Builtin::UnitType
            | Builtin::Eff => Val::Type,
            Builtin::True | Builtin::False => Val::builtin(Builtin::Bool, Val::Type),
            Builtin::Unit => Val::builtin(Builtin::UnitType, Val::Type),
            Builtin::BinOp(b) => b.ty(),
            Builtin::IO => Val::builtin(Builtin::Eff, Val::Type),
            // print : I32 -> () with IO
            Builtin::Print => Val::Fun(
                Box::new(Val::builtin(Builtin::I32, Val::Type)),
                Box::new(Val::builtin(Builtin::UnitType, Val::Type)),
                vec![Val::builtin(
                    Builtin::IO,
                    Val::builtin(Builtin::Eff, Val::Type),
                )],
            ),
            // puts : String -> () with IO
            Builtin::Puts => Val::Fun(
                Box::new(Val::builtin(Builtin::String, Val::Type)),
                Box::new(Val::builtin(Builtin::UnitType, Val::Type)),
                vec![Val::builtin(
                    Builtin::IO,
                    Val::builtin(Builtin::Eff, Val::Type),
                )],
            ),
        }
    }
}

pub fn define_builtins<T: ?Sized + Interner>(cxt: Cxt, db: &T) -> Cxt {
    use Builtin::*;
    let list = vec![
        I32, I64, F32, F64, String, Bool, True, False, Eff, IO, Print, Puts,
    ];

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
