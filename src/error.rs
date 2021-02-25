//! The diagnostic reporting infrastructure.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::{Error as FError, Files as FilesT, SimpleFile};
use codespan_reporting::term::termcolor;
use codespan_reporting::term::{emit, Config};
use lazy_static::lazy_static;
use std::ops::Range;
use std::sync::RwLock;

pub type FileId = usize;

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

    fn name(&self, file_id: usize) -> Result<&str, FError> {
        Ok(self
            .get(file_id)
            .ok_or(FError::FileMissing)?
            .name()
            .as_ref())
    }

    fn source(&self, file_id: usize) -> Result<&str, FError> {
        Ok(self
            .get(file_id)
            .ok_or(FError::FileMissing)?
            .source()
            .as_ref())
    }

    fn line_index(&self, file_id: usize, byte_index: usize) -> Result<usize, FError> {
        self.get(file_id)
            .ok_or(FError::FileMissing)?
            .line_index((), byte_index)
    }

    fn line_range(&self, file_id: usize, line_index: usize) -> Result<Range<usize>, FError> {
        self.get(file_id)
            .ok_or(FError::FileMissing)?
            .line_range((), line_index)
    }
}

lazy_static! {
    pub static ref FILES: RwLock<Files> = RwLock::new(Files::new());
    static ref CONFIG: Config = Default::default();
    static ref WRITER: RwLock<termcolor::StandardStream> = RwLock::new(
        termcolor::StandardStream::stderr(termcolor::ColorChoice::Always)
    );
}

#[derive(Clone, Debug, Copy, PartialEq, Hash, Eq, PartialOrd)]
pub struct Span(pub usize, pub usize);
impl Span {
    pub fn empty() -> Self {
        Span(0, 0)
    }
}
impl Default for Span {
    fn default() -> Self {
        Span::empty()
    }
}
impl Into<Range<usize>> for Span {
    fn into(self) -> Range<usize> {
        self.0..self.1
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SpannedInner<T>(T, Span);
/// This stores a Box internally, so it can be used with recursive types.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Spanned<T>(Box<SpannedInner<T>>);
impl<T> Spanned<T> {
    /// You can't move out of a deref of `Spanned` like you can with `Box`, so use this instead.
    pub fn unwrap(self) -> T {
        (self.0).0
    }
    pub fn empty(x: T) -> Self {
        Spanned::new(x, Span(0, 0))
    }
    pub fn new(x: T, span: Span) -> Self {
        Spanned(Box::new(SpannedInner(x, span)))
    }
    pub fn span(&self) -> Span {
        (self.0).1
    }
    pub fn copy_span<U>(&self, x: U) -> Spanned<U> {
        Spanned::new(x, self.span())
    }
    /// Replaces the span with a new one, leaving the underlying value
    pub fn with_span(mut self, span: Span) -> Self {
        (self.0).1 = span;
        self
    }
}
impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &(self.0).0
    }
}
impl<T> std::ops::DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut (self.0).0
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

pub trait ToError {
    fn to_error(self, file: FileId) -> Error;
}

impl Eq for Error {}
impl Error {
    pub fn message(&mut self) -> &mut String {
        &mut self.0.message
    }

    pub fn no_label(message: impl Into<String>) -> Self {
        Error(Diagnostic::error().with_message(message))
    }

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
            .with_labels(vec![Label::primary(file, span).with_message(secondary)]);
        Error(d)
    }

    /// Add a note to the `Error`, which appears at the bottom unattached to any span
    pub fn with_note(mut self, msg: impl Into<String>) -> Self {
        self.0.notes.push(msg.into());
        self
    }

    /// Add a label to the `Error`
    pub fn with_label(mut self, file: FileId, span: Span, msg: impl Into<String>) -> Self {
        self.0
            .labels
            .push(Label::secondary(file, span).with_message(msg.into()));
        self
    }

    /// Writes the error to the console
    pub fn write(&self) -> Result<(), FError> {
        emit(
            &mut *WRITER.write().unwrap(),
            &CONFIG,
            &*FILES.read().unwrap(),
            &self.0,
        )
    }
}
