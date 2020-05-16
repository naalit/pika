use codespan_reporting::files::SimpleFiles;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term::{Config, emit};
use codespan_reporting::term::termcolor;
use std::ops::Range;
use lalrpop_util::{ParseError, lexer::Token};
use std::sync::{RwLock, Arc};

pub type FileId = usize;

lazy_static::lazy_static! {
    pub static ref FILES: RwLock<SimpleFiles<String, String>> = RwLock::new(SimpleFiles::new());

    pub static ref CONFIG: Config = Default::default();
    pub static ref WRITER: RwLock<termcolor::StandardStream> = RwLock::new(termcolor::StandardStream::stderr(termcolor::ColorChoice::Always));
}

#[derive(Clone, Debug, Copy, PartialEq, Hash, Eq)]
pub struct Span(pub usize, pub usize);
impl Into<Range<usize>> for Span {
    fn into(self) -> Range<usize> {
        self.0..self.1
    }
}
#[derive(Clone, Debug, PartialEq)]
struct SpannedInner<T>(T, Span);
/// Stores an Arc internally, and DerefMut calls Arc::make_mut()
/// i.e. behaves like a Box but with cheap cloning
#[derive(Clone, Debug, PartialEq)]
pub struct Spanned<T>(Arc<SpannedInner<T>>);
impl<T> Spanned<T> {
    pub fn empty(x: T) -> Self {
        Spanned::new(x, Span(0, 0))
    }
    pub fn new(x: T, span: Span) -> Self {
        Spanned(Arc::new(SpannedInner(x, span)))
    }
    pub fn span(&self) -> Span {
        (self.0).1
    }
    pub fn copy_span(&self, x: T) -> Self {
        Spanned::new(x, self.span())
    }
}
impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &(self.0).0
    }
}
impl<T: std::clone::Clone> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut std::sync::Arc::make_mut(&mut self.0).0
    }
}

// pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub struct Error(Diagnostic<usize>);
impl Error {
    pub fn new(
        file: FileId,
        primary: impl Into<String>,
        span: impl Into<Range<usize>>,
        secondary: impl Into<String>,
    ) -> Self {
        let d = Diagnostic::error()
            .with_message(primary)
            .with_labels(vec![Label::secondary(file, span).with_message(secondary)]);
        Error(d)
    }

    pub fn from_lalrpop<T>(e: ParseError<usize, Token, T>, file: usize) -> Self {
        let (message, span) = match e {
            ParseError::InvalidToken { location } => ("Invalid token".to_string(), location..location),
            ParseError::UnrecognizedEOF { location, expected } => (format!("Unexpected EOF, expected one of {:?}", expected), location..location),
            ParseError::UnrecognizedToken { token: (start, Token(_, s), end), expected } => (format!("Unexpected token {}, expected one of {:?}", s, expected), start..end),
            ParseError::ExtraToken { token: (start, Token(_, s), end) } => (format!("Unexpected token {}, expected EOF", s), start..end),
            ParseError::User { .. } => panic!("We don't give user errors!"),
        };
        Error::new(file, format!("Parse error: {}", message), span, message)
    }

    pub fn write(&self) -> std::io::Result<()> {
        emit(
            &mut *WRITER.write().unwrap(),
            &CONFIG,
            &*FILES.read().unwrap(),
            &self.0,
        )
    }
}
