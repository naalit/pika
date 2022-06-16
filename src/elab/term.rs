use super::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FunClass {
    /// Sigma types are treated identically to pi types in most cases:
    /// (P: T1, T2(P)) is equivalent for many purposes to (P: T1) -> T2(P).
    /// In a `Clos`, a sigma type may only have one, explicit, parameter.
    /// So their representation is the same (as is that for lambdas), and they're evaluated the same etc.
    /// TODO: we'll eventually annotate pis and probably lambdas with effects, but this will not happen for sigmas.
    Sigma,
    Lam,
    Pi,
}
pub use FunClass::*;

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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    /// Stores the usize representation of the int
    /// Whether it's positive or negative can be thought of as stored in meta bounds elsewhere
    /// It will be reified during lowering by casting to its concrete type
    Int(usize),
    /// Stores a u64 representation of the bits of the f64
    F64(u64),
    /// Stores a u32 representation of the bits of the f32
    F32(u32),
    String(Name),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Par<T: IsTerm> {
    pub name: Name,
    pub ty: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Params<T: IsTerm> {
    pub implicit: Vec<Par<T>>,
    pub explicit: Vec<Par<T>>,
}
impl<T: IsTerm> Params<T> {
    pub fn len(&self) -> usize {
        self.implicit.len() + self.explicit.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Args<T: IsTerm> {
    pub implicit: Option<Box<T>>,
    pub explicit: Option<Box<T>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsDef {
    name: Name,
    // TODO ConsId or something
    params: Params<Expr>,
    ret_ty: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Definition {
    /// A let definition is different from a local let statement.
    /// Let definitions are unordered, and can't contain patterns other than 'name' or 'name: ty'.
    /// Local let statements are ordered, can contain arbitrary patterns, and create local variables rather than definitions.
    Let {
        name: Name,
        ty: Box<Expr>,
        body: Box<Expr>,
    },
    Fun {
        name: Name,
        params: Params<Expr>,
        ret_ty: Box<Expr>,
        effects: Vec<Expr>,
        body: Box<Expr>,
    },
    Type {
        name: Name,
        params: Params<Expr>,
        cons: Vec<ConsDef>,
        // TODO these should be interned
        where_block: Vec<Definition>,
    },
}

pub trait IsTerm {
    type Clos: Clone;
    type Loc: std::fmt::Debug + Clone + Copy + PartialEq;
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
    Tuple, -> Sigma type or Pair term
    Binder, -> type, usually in Sigma
    StructInit, -> ? will be handled later
    // Patterns parse as expressions
    // but they're not, so they don't appear here
    OrPat,
    EffPat
*/
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Elim<T: IsTerm> {
    App(Args<T>),
    // TODO probably use MemberId or something with a specific member of a specific type
    Member(Name),
    Case(super::pattern::CaseOf),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Type,
    Head(Head<Idx>),
    Elim(Box<Expr>, Box<Elim<Expr>>),
    Fun {
        class: FunClass,
        params: Params<Expr>,
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
impl Expr {
    pub fn var(var: Var<Idx>) -> Self {
        Self::Head(Head::Var(var))
    }
}
