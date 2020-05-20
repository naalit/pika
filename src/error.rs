use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::termcolor;
use codespan_reporting::term::{emit, Config};
use lalrpop_util::{lexer::Token, ParseError};
use std::ops::Range;
use std::sync::{Arc, RwLock};

pub type FileId = usize;

lazy_static::lazy_static! {
    pub static ref FILES: RwLock<SimpleFiles<String, String>> = RwLock::new(SimpleFiles::new());

    static ref CONFIG: Config = Default::default();
    static ref WRITER: RwLock<termcolor::StandardStream> = RwLock::new(termcolor::StandardStream::stderr(termcolor::ColorChoice::Always));
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
/// Stores an `Arc` internally, and DerefMut calls `Arc::make_mut()`
/// i.e. behaves like a `Box` but with cheap cloning
#[derive(Clone, Debug, PartialEq)]
pub struct Spanned<T>(Arc<SpannedInner<T>>);
impl<T> Spanned<T> {
    /// Calls `Arc::try_unwrap()``
    pub fn try_unwrap(self) -> Result<T, Self> {
        Arc::try_unwrap(self.0)
            .map(|SpannedInner(x, _)| x)
            .map_err(Spanned)
    }
    pub fn empty(x: T) -> Self {
        Spanned::new(x, Span(0, 0))
    }
    pub fn new(x: T, span: Span) -> Self {
        Spanned(Arc::new(SpannedInner(x, span)))
    }
    pub fn span(&self) -> Span {
        (self.0).1
    }
    pub fn copy_span<U>(&self, x: U) -> Spanned<U> {
        Spanned::new(x, self.span())
    }
}
impl<T: Clone> Spanned<T> {
    /// Like `try_unwrap()`, but never fails since it calls `Arc::make_mut()`, essentially cloning the value if unwrapping fails
    pub fn force_unwrap(mut self) -> T {
        drop(std::sync::Arc::make_mut(&mut self.0));
        self.try_unwrap().ok().unwrap()
    }

    /// Clones the underlying value, replacing the span with a new one
    pub fn with_span(&self, span: Span) -> Self {
        Spanned::new((self.0).0.clone(), span)
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

/// An error that can be emitted to the console, with messages and a source location
#[derive(Debug, Clone)]
pub struct Error(Diagnostic<usize>);
impl Error {
    /// Formats like this:
    /// ```text
    ///  error: <primary>
    ///   ┌─ <input>:1:17
    ///   │
    /// 1 │ let x = 32 + 54
    ///   │         -- <secondary>
    ///   │
    /// ```
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

    /// Add a label to the `Error`
    pub fn with_label(mut self, file: FileId, span: Span, msg: String) -> Self {
        self.0
            .labels
            .push(Label::secondary(file, span).with_message(msg));
        self
    }

    pub fn from_lalrpop<T>(e: ParseError<usize, Token, T>, file: usize) -> Self {
        let (message, span) = match e {
            ParseError::InvalidToken { location } => {
                ("Invalid token".to_string(), location..location)
            }
            ParseError::UnrecognizedEOF { location, expected } => (
                format!("Unexpected EOF, expected one of {:?}", expected),
                location..location,
            ),
            ParseError::UnrecognizedToken {
                token: (start, Token(_, s), end),
                expected,
            } => (
                format!("Unexpected token {}, expected one of {:?}", s, expected),
                start..end,
            ),
            ParseError::ExtraToken {
                token: (start, Token(_, s), end),
            } => (format!("Unexpected token {}, expected EOF", s), start..end),
            ParseError::User { .. } => panic!("We don't give user errors!"),
        };
        Error::new(file, format!("Parse error: {}", message), span, message)
    }

    /// Writes the error to the console
    pub fn write(&self) -> std::io::Result<()> {
        emit(
            &mut *WRITER.write().unwrap(),
            &CONFIG,
            &*FILES.read().unwrap(),
            &self.0,
        )
    }
}
