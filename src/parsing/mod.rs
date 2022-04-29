//! PARSING
//! for incrementality reasons, this isn't quite a normal parsing system
//! we have three levels:
//!
//! source
//!    |
//!    V
//! splitter
//!    |
//!    |- store per-definition source in Salsa
//!    V
//! lexer
//!    |
//!    V
//! parser

pub mod lexer;
mod parser;
mod splitter;
mod syntax;
pub use syntax::*;

use crate::common::*;
use lsp_types::Url;
use ropey::Rope;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextSplit {
    pub name: Option<Name>,
    pub start_line: usize,
    pub abs_span: AbsSpan,
    pub text: Rope,
}

#[salsa::query_group(ParserDatabase)]
pub trait Parser {
    #[salsa::interned]
    fn file_id(&self, file: Url) -> File;

    #[salsa::interned]
    fn name(&self, name: String) -> Name;

    #[salsa::input]
    fn input_file(&self, file: File) -> Rope;

    #[salsa::invoke(splitter::split)]
    fn split(&self, file: File) -> Vec<TextSplit>;
}
