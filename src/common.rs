use std::collections::HashMap;

pub use crate::pretty::Doc;
use ariadne::Color;
pub use ariadne::Fmt;
use lsp_types::Url;

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

pub type RelSpan = std::ops::Range<usize>;
pub type Spanned<T> = (T, RelSpan);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbsSpan(pub File, pub std::ops::Range<usize>);
impl AbsSpan {
    pub fn add(&self, other: RelSpan) -> Self {
        AbsSpan(
            self.0.clone(),
            self.1.start + other.start..self.1.start + other.end,
        )
    }

    fn lsp_range(&self, files: &HashMap<File, ropey::Rope>) -> lsp_types::Range {
        let text = files.get(&self.0).unwrap();
        let start_line = text.char_to_line(self.1.start);
        let start_line_start = text.line_to_char(start_line);
        let end_line = text.char_to_line(self.1.end);
        let end_line_start = text.line_to_char(end_line);
        lsp_types::Range {
            start: lsp_types::Position {
                line: start_line as u32,
                character: self.1.start as u32 - start_line_start as u32,
            },
            end: lsp_types::Position {
                line: end_line as u32,
                character: self.1.end as u32 - end_line_start as u32,
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
        self.1.start()
    }

    fn end(&self) -> usize {
        self.1.end()
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

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug, PartialEq)]
pub struct Error {
    pub severity: Severity,
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
            primary_span.1.start,
        )
        .with_message(self.message.to_string(true))
        .with_label(self.primary.ariadne(split_span));
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
            message: self.message.to_string(false),
            // TODO: in some cases we may also want separate NOTE-type diagnostics for secondary labels?
            related_information: Some(
                self.secondary
                    .into_iter()
                    .map(|x| lsp_types::DiagnosticRelatedInformation {
                        location: lsp_types::Location {
                            uri: db.lookup_file_id(split_span.0),
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
        Ok(self.files.entry(key.clone()).or_insert_with(|| {
            ariadne::Source::from(
                &std::fs::read_to_string(self.db.lookup_file_id(*key).path()).unwrap(),
            )
        }))
    }

    fn display<'b>(&self, key: &'b File) -> Option<Box<dyn std::fmt::Display + 'b>> {
        Some(Box::new(
            self.db
                .lookup_file_id(*key)
                .to_file_path()
                .ok()?
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string(),
        ) as _)
    }
}
