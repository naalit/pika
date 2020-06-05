use crate::common::*;
use crate::lexer::{LexError, Tok};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::{Files as FilesT, SimpleFile};
use codespan_reporting::term::termcolor;
use codespan_reporting::term::{emit, Config};
use lalrpop_util::ParseError;
use lazy_static::lazy_static;
use std::ops::Range;
use std::sync::{Arc, RwLock};

pub struct Files {
    files: Vec<SimpleFile<String, String>>,
}

impl Files {
    pub fn new() -> Files {
        Files { files: Vec::new() }
    }

    pub fn add(&mut self, name: String, source: String) -> FileId {
        let file_id = self.files.len();
        self.files.push(SimpleFile::new(name, source));
        file_id
    }

    /// Get the file corresponding to the given id.
    pub fn get(&self, file_id: FileId) -> Option<&SimpleFile<String, String>> {
        self.files.get(file_id)
    }

    pub fn set_source(&mut self, file_id: FileId, source: String) {
        let f = self.files.get_mut(file_id).unwrap();
        let name = f.name().to_string();
        *f = SimpleFile::new(name, source);
    }
}

impl<'a> FilesT<'a> for Files {
    type FileId = FileId;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&self, file_id: usize) -> Option<&str> {
        Some(self.get(file_id)?.name().as_ref())
    }

    fn source(&self, file_id: usize) -> Option<&str> {
        Some(self.get(file_id)?.source().as_ref())
    }

    fn line_index(&self, file_id: usize, byte_index: usize) -> Option<usize> {
        self.get(file_id)?.line_index((), byte_index)
    }

    fn line_range(&self, file_id: usize, line_index: usize) -> Option<Range<usize>> {
        self.get(file_id)?.line_range((), line_index)
    }
}

lazy_static! {
    pub static ref FILES: RwLock<Files> = RwLock::new(Files::new());
    static ref CONFIG: Config = Default::default();
    static ref WRITER: RwLock<termcolor::StandardStream> = RwLock::new(
        termcolor::StandardStream::stderr(termcolor::ColorChoice::Always)
    );
}

#[derive(Clone, Debug, Copy, PartialEq, Hash, Eq)]
pub struct Span(pub usize, pub usize);
impl Into<Range<usize>> for Span {
    fn into(self) -> Range<usize> {
        self.0..self.1
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SpannedInner<T>(T, Span);
/// Stores an `Arc` internally, and DerefMut calls `Arc::make_mut()`
/// i.e. behaves like a `Box` but with cheap cloning
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Spanned<T>(Arc<SpannedInner<T>>);
impl<T> Clone for Spanned<T> {
    fn clone(&self) -> Self {
        Spanned(self.0.clone())
    }
}
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
impl PartialEq for Error {
    fn eq(&self, other: &Error) -> bool {
        self.0.message == other.0.message
            && self
                .0
                .labels
                .iter()
                .zip(other.0.labels.iter())
                .fold(true, |acc, (a, b)| {
                    acc && a.style == b.style
                        && a.file_id == b.file_id
                        && a.range == b.range
                        && a.message == b.message
                })
            && self.0.notes == other.0.notes
            && self.0.code == other.0.code
            && self.0.severity == other.0.severity
    }
}

struct Alternatives(Vec<String>);
use std::fmt;
impl fmt::Display for Alternatives {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn to_err(x: &str) -> String {
            match x {
                r#""\n""# => "newline".to_string(),
                "INT_LIT" => "literal".to_string(),
                "NAME" => "identifier".to_string(),
                "INDENT" => "indent".to_string(),
                "DEDENT" => "dedent".to_string(),
                x => x.replace('"', "'"),
            }
        }

        if self.0.len() == 1 {
            return write!(f, "{}", to_err(&self.0[0]));
        }
        for i in 0..self.0.len() {
            if i == self.0.len() - 1 {
                write!(f, "or {}", to_err(&self.0[i]))?;
            } else {
                write!(f, "{}, ", to_err(&self.0[i]))?;
            }
        }
        Ok(())
    }
}

impl Eq for Error {}
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
        span: Span,
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

    pub fn from_lalrpop(e: ParseError<usize, Tok, Spanned<LexError>>, file: usize) -> Self {
        let (message, span) = match e {
            ParseError::InvalidToken { location } => {
                ("Invalid token".to_string(), Span(location, location))
            }
            ParseError::UnrecognizedEOF { location, expected } => (
                format!("Unexpected EOF, expected {}", Alternatives(expected)),
                Span(location, location),
            ),
            ParseError::UnrecognizedToken {
                token: (start, tok, end),
                expected,
            } => (
                format!("Unexpected {}, expected {}", tok, Alternatives(expected)),
                Span(start, end),
            ),
            ParseError::ExtraToken {
                token: (start, tok, end),
            } => (
                format!("Unexpected {}, expected EOF", tok),
                Span(start, end),
            ),
            ParseError::User { error } => (error.to_string(), error.span()),
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
