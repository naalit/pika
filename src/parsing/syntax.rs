#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    // Keywords
    Fun,
    Let,
    Impl,
    Do,
    Struct,
    Sig,
    /// This is lowercase `type`
    Type,
    Case,
    Of,
    /// This is uppercase `Type`. TODO make it a builtin instead of a keyword?
    TypeType,
    With,
    Pure,
    Where,
    Raise,
    Catch,
    And,
    Or,
    If,
    Then,
    Else,
    Eff,
    Box,
    Unbox,

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
    String,

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
    Error,

    // Composite nodes

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
enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        assert!(raw.0 <= Root as u16);
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}
