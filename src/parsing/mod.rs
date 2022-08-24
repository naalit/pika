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

pub mod ast;
mod lexer;
mod parser;
mod splitter;
mod syntax;
use std::fmt::Display;

pub use syntax::*;

use crate::common::*;
use lsp_types::Url;
use ropey::Rope;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FileLoc {
    Url(Url),
    Input,
}
impl FileLoc {
    pub fn to_url(self) -> Option<Url> {
        match self {
            FileLoc::Url(url) => Some(url),
            FileLoc::Input => None,
        }
    }
}
impl Display for FileLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FileLoc::Url(url) => write!(
                f,
                "{}",
                url.to_file_path()
                    .ok()
                    .unwrap()
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
            ),
            FileLoc::Input => write!(f, "<input>"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextSplit {
    pub name: Option<Name>,
    pub start_line: usize,
    pub abs_span: AbsSpan,
    pub text: Rope,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum SplitId {
    Named(Name),
    Idx(usize),
}
impl SplitId {
    pub fn name(self) -> Option<Name> {
        match self {
            SplitId::Named(n) => Some(n),
            SplitId::Idx(_) => None,
        }
    }
}

#[salsa::query_group(ParserDatabase)]
pub trait Parser {
    #[salsa::interned]
    fn file_id(&self, file: FileLoc) -> File;

    #[salsa::interned]
    fn name(&self, name: String) -> Name;

    #[salsa::input]
    fn input_file(&self, file: File) -> Rope;

    #[salsa::invoke(splitter::split)]
    fn all_splits(&self, file: File) -> Vec<TextSplit>;

    fn all_split_ids(&self, file: File) -> Vec<SplitId>;

    fn split(&self, file: File, id: SplitId) -> Option<TextSplit>;

    #[salsa::invoke(lexer::lexer_entry)]
    fn lex(&self, file: File, id: SplitId) -> Option<lexer::LexResult>;

    #[salsa::invoke(parser::parser_entry)]
    fn parse(&self, file: File, id: SplitId) -> Option<parser::ParseResult>;
}
pub trait ParserExt: Parser {
    fn split_span(&self, file: File, id: SplitId) -> Option<AbsSpan> {
        Some(self.split(file, id)?.abs_span)
    }

    fn split_at(&self, file: File, abs_pos: u32) -> Option<SplitId> {
        let splits = self.all_split_ids(file);
        for i in splits {
            if let Some(span) = self.split_span(file, i) {
                if span.1.contains(&abs_pos) {
                    return Some(i);
                }
            }
        }
        None
    }

    fn ast(&self, file: File, id: SplitId) -> Option<ast::Root> {
        let result = self.parse(file, id)?;
        ast::Root::cast(SyntaxNode::new_root(result.green))
    }

    fn inaccessible(&self, name: SName) -> SName {
        (name.0.inaccessible(self), name.1)
    }
}
impl<T: Parser + ?Sized> ParserExt for T {}

fn all_split_ids(db: &dyn Parser, file: File) -> Vec<SplitId> {
    db.all_splits(file)
        .into_iter()
        .enumerate()
        .map(|(i, x)| match x.name {
            Some(n) => SplitId::Named(n),
            None => SplitId::Idx(i),
        })
        .collect()
}

fn split(db: &dyn Parser, file: File, id: SplitId) -> Option<TextSplit> {
    let mut splits = db.all_splits(file);
    match id {
        SplitId::Named(name) => splits.into_iter().find(|x| x.name == Some(name)),
        SplitId::Idx(i) => {
            if i < splits.len() {
                Some(splits.swap_remove(i))
            } else {
                None
            }
        }
    }
}
