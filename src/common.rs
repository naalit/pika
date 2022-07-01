pub use std::collections::{HashMap, VecDeque};

pub use crate::parsing::{ast, FileLoc, ParserExt, SplitId};
pub use crate::pretty::Doc;
pub use ast::AstNode;

use ariadne::Color;
pub use ariadne::Fmt;
pub use std::borrow::Cow;

#[macro_export]
macro_rules! intern_key {
    ($n:ident) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
        pub struct $n(salsa::InternId);
        impl salsa::InternKey for $n {
            fn from_intern_id(id: salsa::InternId) -> Self {
                Self(id)
            }

            fn as_intern_id(&self) -> salsa::InternId {
                self.0
            }
        }
    };
}
intern_key!(File);
intern_key!(Name);
intern_key!(Def);

impl Name {
    pub fn inaccessible(self, db: &(impl crate::parsing::Parser + ?Sized)) -> Name {
        let str = db.lookup_name(self);
        db.name(format!("{}'", str))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefLoc {
    Root(File, SplitId),
    Child(Def, SplitId),
}

impl Def {
    pub fn fallback_repr<T: crate::elab::Elaborator + ?Sized>(self, db: &T) -> String {
        match db.lookup_def(self) {
            DefLoc::Root(file, split) => match split {
                SplitId::Named(n) => format!("{}.{}", db.lookup_file_id(file), db.lookup_name(n)),
                SplitId::Idx(i) => format!("{}.%{}", db.lookup_file_id(file), i),
            },
            DefLoc::Child(a, split) => match split {
                SplitId::Named(n) => format!("{}.{}", a.fallback_repr(db), db.lookup_name(n)),
                SplitId::Idx(i) => format!("{}.%{}", a.fallback_repr(db), i),
            },
        }
    }
}

pub type RelSpan = std::ops::Range<u32>;
pub type Spanned<T> = (T, RelSpan);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsSpan(pub File, pub std::ops::Range<u32>);
impl AbsSpan {
    pub fn add(&self, other: RelSpan) -> Self {
        AbsSpan(
            self.0.clone(),
            self.1.start + other.start..self.1.start + other.end,
        )
    }

    pub fn lsp_range(&self, files: &HashMap<File, ropey::Rope>) -> lsp_types::Range {
        let text = files.get(&self.0).unwrap();
        let start_line = text.char_to_line(self.1.start as usize);
        let start_line_start = text.line_to_char(start_line);
        let end_line = text.char_to_line(self.1.end as usize);
        let end_line_start = text.line_to_char(end_line);
        lsp_types::Range {
            start: lsp_types::Position {
                line: start_line as u32,
                character: self.1.start - start_line_start as u32,
            },
            end: lsp_types::Position {
                line: end_line as u32,
                character: self.1.end - end_line_start as u32,
            },
        }
    }
}
impl ariadne::Span for AbsSpan {
    type SourceId = File;

    fn source(&self) -> &Self::SourceId {
        &self.0
    }

    fn start(&self) -> usize {
        self.1.start as usize
    }

    fn end(&self) -> usize {
        self.1.end as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}
impl Severity {
    fn ariadne(self) -> ariadne::ReportKind {
        match self {
            Severity::Error => ariadne::ReportKind::Error,
            Severity::Warning => ariadne::ReportKind::Warning,
        }
    }

    fn lsp(self) -> lsp_types::DiagnosticSeverity {
        match self {
            Severity::Error => lsp_types::DiagnosticSeverity::ERROR,
            Severity::Warning => lsp_types::DiagnosticSeverity::WARNING,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: RelSpan,
    pub message: Doc,
    pub color: Option<Color>,
}
impl Label {
    fn ariadne(self, split_span: &AbsSpan) -> ariadne::Label<AbsSpan> {
        let span = split_span.add(self.span);
        let mut l = ariadne::Label::new(span).with_message(self.message.to_string(true));
        if let Some(color) = self.color {
            l = l.with_color(color);
        }
        l
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub severity: Severity,
    pub message_lsp: Option<Doc>,
    pub message: Doc,
    pub primary: Label,
    pub secondary: Vec<Label>,
    pub note: Option<Doc>,
}

impl Error {
    pub fn write_cli(self, split_span: &AbsSpan, cache: &mut FileCache) {
        let primary_span = split_span.add(self.primary.span.clone());
        let mut r = ariadne::Report::build(
            self.severity.ariadne(),
            primary_span.0,
            primary_span.1.start as usize,
        )
        .with_message(self.message.to_string(true))
        // The primary label appears first since it's the most important
        .with_label(self.primary.ariadne(split_span).with_order(-1));
        r.add_labels(self.secondary.into_iter().map(|x| x.ariadne(split_span)));
        if let Some(note) = self.note {
            r.set_note(note.to_string(true));
        }
        r.finish().eprint(cache).unwrap();
    }

    pub fn to_lsp(
        self,
        split_span: &AbsSpan,
        files: &HashMap<File, ropey::Rope>,
        db: &impl crate::parsing::Parser,
    ) -> lsp_types::Diagnostic {
        let span = split_span.add(self.primary.span);

        lsp_types::Diagnostic {
            range: span.lsp_range(files),
            severity: Some(self.severity.lsp()),
            code: None,
            code_description: None,
            source: None,
            message: self.message_lsp.unwrap_or(self.message).to_string(false),
            // TODO: in some cases we may also want separate NOTE-type diagnostics for secondary labels?
            related_information: Some(
                self.secondary
                    .into_iter()
                    .map(|x| lsp_types::DiagnosticRelatedInformation {
                        location: lsp_types::Location {
                            uri: db.lookup_file_id(split_span.0).to_url().unwrap(),
                            range: split_span.add(x.span).lsp_range(files),
                        },
                        message: x.message.to_string(false),
                    })
                    .collect(),
            ),
            // TODO: this is useful for deprecated or unnecessary code
            tags: None,
            data: None,
        }
    }
}

pub struct FileCache<'a> {
    files: HashMap<File, ariadne::Source>,
    db: &'a dyn crate::parsing::Parser,
}
impl<'a> FileCache<'a> {
    pub fn new(db: &'a dyn crate::parsing::Parser) -> Self {
        FileCache {
            files: HashMap::new(),
            db,
        }
    }
}

impl<'a> ariadne::Cache<File> for FileCache<'a> {
    fn fetch(&mut self, key: &File) -> Result<&ariadne::Source, Box<dyn std::fmt::Debug + '_>> {
        Ok(self
            .files
            .entry(key.clone())
            .or_insert_with(|| ariadne::Source::from(&self.db.input_file(*key).to_string())))
    }

    fn display<'b>(&self, key: &'b File) -> Option<Box<dyn std::fmt::Display + 'b>> {
        Some(Box::new(self.db.lookup_file_id(*key)) as _)
    }
}
