use codespan_reporting::files::SimpleFiles;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term::{Config, emit};
use codespan_reporting::term::termcolor;
use std::ops::Range;
use lalrpop_util::{ParseError, lexer::Token};
use std::sync::RwLock;

lazy_static::lazy_static! {
    pub static ref FILES: RwLock<SimpleFiles<String, String>> = RwLock::new(SimpleFiles::new());

    pub static ref CONFIG: Config = Default::default();
    pub static ref WRITER: RwLock<termcolor::StandardStream> = RwLock::new(termcolor::StandardStream::stderr(termcolor::ColorChoice::Always));
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub struct Error(Diagnostic<usize>);
impl Error {
    pub fn new(
        file: usize,
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
