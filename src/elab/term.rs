use crate::pretty::Prec;

use super::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FunClass {
    /// Sigma types are treated identically to pi types in most cases:
    /// (P: T1, T2(P)) is equivalent for many purposes to (P: T1) -> T2(P).
    /// In a `Clos`, a sigma type may only have one, explicit, parameter.
    /// So their representation is the same (as is that for lambdas), and they're evaluated the same etc.
    /// TODO: we'll eventually annotate pis and probably lambdas with effects, but this will not happen for sigmas.
    Sigma,
    Lam(Icit),
    Pi(Icit),
}
impl FunClass {
    pub fn icit(self) -> Option<Icit> {
        match self {
            Sigma => None,
            Lam(i) => Some(i),
            Pi(i) => Some(i),
        }
    }
}
pub use FunClass::{Lam, Pi, Sigma};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Exp,
    Mod,
    // Bitwise are included here since the types match
    Ior,
    Xor,
    And,
    Shl,
    Shr,
}
impl ArithOp {
    pub fn from_tok(tok: crate::parsing::SyntaxKind) -> Option<ArithOp> {
        use crate::parsing::SyntaxKind as Tok;
        Some(match tok {
            Tok::Plus => ArithOp::Add,
            Tok::Minus => ArithOp::Sub,
            Tok::Times => ArithOp::Mul,
            Tok::Div => ArithOp::Div,
            Tok::Exp => ArithOp::Exp,
            Tok::Mod => ArithOp::Mod,
            Tok::Bar => ArithOp::Ior,
            Tok::Xor => ArithOp::Xor,
            Tok::LShift => ArithOp::Shl,
            Tok::RShift => ArithOp::Shr,
            Tok::BitAnd => ArithOp::And,
            _ => return None,
        })
    }
}
impl std::fmt::Display for ArithOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ArithOp::Add => "+",
            ArithOp::Sub => "-",
            ArithOp::Mul => "*",
            ArithOp::Div => "/",
            ArithOp::Exp => "**",
            ArithOp::Mod => "%",
            ArithOp::Ior => "|",
            ArithOp::Xor => "^^",
            ArithOp::And => "&",
            ArithOp::Shl => "<<",
            ArithOp::Shr => ">>",
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum CompOp {
    Eq,
    Ne,
    Gt,
    Lt,
    Ge,
    Le,
}
impl CompOp {
    pub fn from_tok(tok: crate::parsing::SyntaxKind) -> Option<CompOp> {
        use crate::parsing::SyntaxKind as Tok;
        Some(match tok {
            Tok::Gt => CompOp::Gt,
            Tok::GtE => CompOp::Ge,
            Tok::Lt => CompOp::Lt,
            Tok::LtE => CompOp::Le,
            Tok::Eq => CompOp::Eq,
            Tok::NEq => CompOp::Ne,
            _ => return None,
        })
    }
}
impl std::fmt::Display for CompOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CompOp::Eq => "==",
            CompOp::Ne => "!=",
            CompOp::Gt => ">",
            CompOp::Lt => "<",
            CompOp::Ge => ">=",
            CompOp::Le => "<=",
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Builtin {
    IntType(IntType),
    Unit,
    UnitType,
    StringType,
    BoolType,
    ArithOp(ArithOp),
    CompOp(CompOp),
}
impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Builtin::IntType(i) => write!(f, "{:?}", i),
            Builtin::Unit => write!(f, "()"),
            Builtin::UnitType => write!(f, "()"),
            Builtin::StringType => write!(f, "String"),
            Builtin::BoolType => write!(f, "Bool"),
            Builtin::ArithOp(op) => write!(f, "{}", op),
            Builtin::CompOp(op) => write!(f, "{}", op),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntType {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}
impl IntType {
    pub fn max(self) -> i128 {
        match self {
            IntType::U8 => u8::MAX as _,
            IntType::U16 => u16::MAX as _,
            IntType::U32 => u32::MAX as _,
            IntType::U64 => u64::MAX as _,
            IntType::I8 => i8::MAX as _,
            IntType::I16 => i16::MAX as _,
            IntType::I32 => i32::MAX as _,
            IntType::I64 => i64::MAX as _,
        }
    }

    pub fn min(self) -> i128 {
        match self {
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 => 0,
            IntType::I8 => i8::MIN as _,
            IntType::I16 => i16::MIN as _,
            IntType::I32 => i32::MIN as _,
            IntType::I64 => i64::MIN as _,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    /// Stores the u64 representation of the int, plus a bool for whether it's signed
    /// If the bool is true, then the actual value is obtained by a cast to i64
    Int(bool, u64),
    /// Stores a u64 representation of the bits of the f64
    F64(u64),
    /// Stores a u32 representation of the bits of the f32
    F32(u32),
    String(Name),
}
impl Literal {
    pub fn pretty<T: crate::parsing::Parser + ?Sized>(&self, db: &T) -> Doc {
        match self {
            Literal::Int(false, i) => Doc::start(i),
            Literal::Int(true, i) => Doc::start(*i as i64),
            Literal::F64(i) => Doc::start(f64::from_bits(*i)),
            Literal::F32(i) => Doc::start(f32::from_bits(*i)),
            Literal::String(s) => Doc::start(db.lookup_name(*s)),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Icit {
    Impl,
    Expl,
}
pub use self::Icit::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Par {
    pub name: Name,
    pub ty: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsDef {
    name: Name,
    // TODO ConsId or something
    implicit: Vec<Par>,
    explicit: Vec<Par>,
    ret_ty: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A let definition is different from a local let statement.
/// Let definitions are unordered, and can't contain patterns other than 'name' or 'name: ty'.
/// Local let statements are ordered, can contain arbitrary patterns, and create local variables rather than definitions.
pub struct Definition {
    pub name: Name,
    pub ty: Box<Expr>,
    pub body: Box<Expr>,
}

pub trait IsTerm {
    type Clos: std::fmt::Debug + Clone + PartialEq + Eq + std::hash::Hash;
    type Loc: std::fmt::Debug + Clone + Copy + PartialEq + Eq + std::hash::Hash;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Head<L> {
    Var(Var<L>),
}

/* AST -> Term mapping:
    Var,
    Lam, }
    Pi,  }-> one Fun term
    App, -> desugared and split into Member + App
    Do, -> maybe (partially) turned into recursive LetIn and Seq if that helps?
    Hole, -> turned into metavariable
    Case,
    Lit,
    Unit,  }
    BinOp, } -> builtins; and/or are desugared into if then case
    If, -> desugared into case
    Box, -> ? will be handled later
    Type,
    GroupedExpr, -> removed, if empty replaced by Unit
    Tuple, -> Sigma type as Fun or Pair term
    Binder, -> type, usually in Sigma
    StructInit, -> ? will be handled later
*/
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Elim<T: IsTerm> {
    App(Icit, T),
    // TODO probably use MemberId or something with a specific member of a specific type
    Member(Name),
    Case(super::pattern::CaseOf<T>),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Type,
    Head(Head<Idx>),
    Elim(Box<Expr>, Box<Elim<Expr>>),
    Fun {
        class: FunClass,
        params: Vec<Par>,
        body: Box<Expr>,
    },
    // Do(Vec<Stmt>),
    Lit(Literal),
    Pair(Box<Expr>, Box<Expr>),
    Error,
}
impl IsTerm for Expr {
    type Clos = Expr;
    type Loc = Idx;
}
fn pretty_bind<T: Elaborator + ?Sized>(n: Name, ty: Doc, db: &T, parens: bool) -> Doc {
    if db.name("_".to_string()) == n {
        ty
    } else {
        let doc = Doc::start(db.lookup_name(n)).add(':', ()).space().chain(ty);
        if parens {
            Doc::start('(').chain(doc).add(')', ())
        } else {
            doc
        }
    }
}
impl Expr {
    pub fn var(var: Var<Idx>) -> Self {
        Self::Head(Head::Var(var))
    }

    pub fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        match self {
            Expr::Type => Doc::none().add("Type", Doc::style_keyword()),
            Expr::Head(h) => match h {
                Head::Var(v) => match v {
                    Var::Local(name, _i) => Doc::start(db.lookup_name(*name)), //.add('.', ()).add(_i.as_u32(), ()),
                    Var::Meta(m) => Doc::start(m).style(Doc::style_literal()),
                    Var::Builtin(b) => Doc::start(b),
                    // TODO better way of doing this - e.g. take into account module paths
                    // also get rid of fallback
                    Var::Def(d) => Doc::start(
                        db.def_name(*d)
                            .map(|x| db.lookup_name(x))
                            .unwrap_or_else(|| format!("?{}", d.fallback_repr(db))),
                    ),
                },
            },
            Expr::Elim(a, b) => match &**b {
                Elim::App(icit, b) => a
                    .pretty(db)
                    .nest(Prec::App)
                    .chain(match icit {
                        Impl => Doc::none()
                            .space()
                            .add('[', ())
                            .chain(b.pretty(db))
                            .add(']', ()),
                        Expl => Doc::none().space().chain(b.pretty(db).nest(Prec::Atom)),
                    })
                    .prec(Prec::App),
                Elim::Member(m) => a
                    .pretty(db)
                    .add('.', ())
                    .add(db.lookup_name(*m), ())
                    .prec(Prec::App),
                Elim::Case(c) => c.pretty(a.pretty(db), db).prec(Prec::Term),
            },
            Expr::Fun {
                class,
                params,
                body,
            } => {
                let d_params = match class {
                    Pi(Impl) | Lam(Impl) => Doc::start('[')
                        .chain(Doc::intersperse(
                            params.iter().map(|x| {
                                Doc::start(db.lookup_name(x.name))
                                    .add(':', ())
                                    .space()
                                    .chain(x.ty.pretty(db).nest(Prec::App))
                            }),
                            Doc::start(',').space(),
                        ))
                        .add(']', ()),
                    Lam(Expl) => Doc::start('(')
                        .chain(Doc::intersperse(
                            params.iter().map(|x| {
                                Doc::start(db.lookup_name(x.name))
                                    .add(':', ())
                                    .space()
                                    .chain(x.ty.pretty(db).nest(Prec::App))
                            }),
                            Doc::start(',').space(),
                        ))
                        .add(')', ()),
                    Sigma | Pi(Expl) if params.len() == 1 => {
                        assert_eq!(params.len(), 1);
                        let x = &params[0];
                        pretty_bind(x.name, x.ty.pretty(db).nest(Prec::App), db, *class != Sigma)
                    }
                    Pi(Expl) => Doc::start('(')
                        .chain(Doc::intersperse(
                            params.iter().map(|x| {
                                pretty_bind(x.name, x.ty.pretty(db).nest(Prec::App), db, false)
                            }),
                            Doc::start(',').space(),
                        ))
                        .add(')', ()),
                    Sigma => unreachable!("params.len(): {}", params.len()),
                };
                match class {
                    Sigma => {
                        assert_eq!(params.len(), 1);
                        d_params
                            .add(',', ())
                            .space()
                            .chain(body.pretty(db).nest(Prec::Pair))
                            .prec(Prec::Pair)
                    }
                    Lam(_) => d_params
                        .space()
                        .add("=>", ())
                        .space()
                        .chain(body.pretty(db))
                        .prec(Prec::Term),
                    Pi(_) => d_params
                        .space()
                        .add("->", ())
                        .space()
                        .chain(body.pretty(db).nest(Prec::Pi))
                        .prec(Prec::Pi),
                }
            }
            Expr::Lit(l) => l.pretty(db).style(Doc::style_literal()),
            Expr::Pair(a, b) => a
                .pretty(db)
                .add(',', ())
                .space()
                .chain(b.pretty(db).nest(Prec::Pair))
                .prec(Prec::Pair),
            Expr::Error => Doc::none().add("%error", Doc::style_literal()),
        }
    }
}
