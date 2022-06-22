#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    // Keywords
    FunKw,
    LetKw,
    ImplKw,
    DoKw,
    StructKw,
    SigKw,
    /// This is lowercase `type`
    TypeKw,
    CaseKw,
    OfKw,
    /// This is uppercase `Type`. TODO make it a builtin instead of a keyword?
    TypeTypeKw,
    WithKw,
    PureKw,
    WhereKw,
    CatchKw,
    AndKw,
    OrKw,
    IfKw,
    ThenKw,
    ElseKw,
    EffKw,
    BoxKw,
    UnboxKw,

    // Symbols the lexer recognizes as a "binary operator"
    Colon,     // :
    Equals,    // =
    Arrow,     // ->
    WideArrow, // =>
    Plus,      // +
    Minus,     // -
    Times,     // *
    Div,       // /
    Bar,       // |
    Dot,       // .
    Comma,     // ,
    Exp,       // **
    Mod,       // %
    Xor,       // ^^
    LShift,    // <<
    RShift,    // >>
    BitAnd,    // &
    Gt,        // >
    GtE,       // >=
    Lt,        // <
    LtE,       // <=
    Eq,        // ==
    NEq,       // !=
    LPipe,     // <|
    RPipe,     // |>

    // Tokens with a payload
    IntLit,
    FloatLit,
    Name,
    StringLit,

    // Other tokens
    Indent,
    Dedent,
    At,      // @
    POpen,   // (
    PClose,  // )
    SOpen,   // [
    SClose,  // ]
    COpen,   // {
    CClose,  // }
    Newline, // \n or ;
    /// Backslash is reserved but not used for anything right now
    /// It may eventually be used as a line continuation character, at the start of the line like wisp's '.'
    Backslash, // \

    Whitespace,
    Comment,
    Error,
    Eof,

    // Composite nodes
    /// A parameter where a bare name is a binding
    PatPar,
    /// A parameter where a bare name is a reference
    TermPar,

    Pat,
    Binder,
    Pair,
    App,

    ImpArg,
    ImpArgs,
    ImpPar,
    ImpPars,

    StructInit,
    Var,
    Member,
    Lam,
    Ty,
    Body,
    WithClause,
    Pi,
    Do,
    Hole,
    DotExpr,
    EffPat,
    Case,
    Lit,
    BinOpKind,
    BinOp,
    If,
    Box,
    Type,
    CaseBranch,
    GroupedExpr,

    LetDef,
    FunDef,
    TypeDef,
    TypeDefShort,
    TypeDefStruct,
    ConsDef,
    BlockDef,
    StructFields,

    // Top level node
    Root,
}
use SyntaxKind::*;

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PikaLang {}
impl rowan::Language for PikaLang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        assert!(raw.0 <= Root as u16);
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

pub type SyntaxNode = rowan::SyntaxNode<PikaLang>;
pub type SyntaxToken = rowan::SyntaxToken<PikaLang>;
