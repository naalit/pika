pub use codespan_reporting::term::termcolor;
pub use pretty::RcDoc;
use std::sync::Arc;
use termcolor::*;

use crate::common::HasBindings;
pub use termcolor::{Color, ColorChoice, ColorSpec};

#[derive(PartialOrd, PartialEq, Eq, Ord, Clone, Copy)]
pub enum Prec {
    Term,
    App,
    Atom,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Style {
    Keyword,
    Literal,
    Binder,
    Symbol,
    Special,
    Bold,
    BoldRed,
    Error,
    Note,
    Comment,
    None,
}
impl Style {
    pub fn spec(self) -> ColorSpec {
        match self {
            Style::Keyword => spec(Color::Magenta, false),
            Style::Binder => spec(Color::Cyan, false),
            Style::Literal | Style::Error => spec(Color::Red, false),
            Style::Symbol => spec(Color::Green, false),
            Style::Special => spec(Color::Blue, true),
            Style::Bold => ColorSpec::new().set_bold(true).clone(),
            Style::BoldRed => spec(Color::Red, true),
            Style::Note => spec(Color::Blue, false),
            Style::Comment => ColorSpec::new()
                .set_fg(Some(Color::Black))
                .set_intense(true)
                .clone(),
            Style::None => ColorSpec::new(),
        }
    }
}

/// A wrapper around a `pretty::RcDoc` with precedence tracking and a different interface
#[derive(Clone)]
pub struct Doc {
    doc: RcDoc<'static, ColorSpec>,
    prec: Prec,
}

impl Into<String> for Doc {
    /// Calls `Doc::ansi_string()`. This is primarily for interop with codespan_reporting
    fn into(self) -> String {
        self.ansi_string()
    }
}

pub fn pretty_block(keyword: &str, v: impl IntoIterator<Item = Doc> + Clone) -> Doc {
    Doc::either(
        Doc::start(keyword)
            .style(Style::Keyword)
            .line()
            .chain(Doc::intersperse(v.clone(), Doc::none().line()))
            .indent(),
        Doc::start(keyword)
            .style(Style::Keyword)
            .space()
            .add("{")
            .space()
            .chain(Doc::intersperse(v, Doc::start(";").space()))
            .space()
            .add("}"),
    )
}

impl Doc {
    /// Render into a string with no newlines and no colors
    pub fn raw_string(self) -> String {
        let mut buffer = Buffer::no_color();
        buffer.reset().unwrap();
        self.group()
            .doc
            .render_colored(100000, &mut buffer)
            .unwrap();
        String::from_utf8(buffer.into_inner()).unwrap()
    }

    /// Render into a string with ANSI colors
    pub fn ansi_string(self) -> String {
        let mut buffer = Buffer::ansi();
        buffer.reset().unwrap();
        self.doc.render_colored(80, &mut buffer).unwrap();
        String::from_utf8(buffer.into_inner()).unwrap()
    }

    /// An empty `Doc`
    pub fn none() -> Self {
        Doc {
            doc: RcDoc::nil(),
            prec: Prec::Atom,
        }
    }

    /// Sets the highlighting style for what we have so far
    /// Implies `group()`
    pub fn style(self, ann: Style) -> Self {
        Doc {
            doc: self.doc.annotate(ann.spec()).group(),
            ..self
        }
    }

    /// Separates a list of `Doc`s with `sep`. It doesn't put `sep` at the beginning or end, just in between each one.
    ///
    /// `intersperse(&[a, b, c], s) = a.chain(s).chain(b).chain(s).chain(c)`
    pub fn intersperse(docs: impl IntoIterator<Item = Self>, sep: Self) -> Self {
        Doc {
            doc: RcDoc::intersperse(docs.into_iter().map(|x| x.doc), sep.doc),
            prec: Prec::Term,
        }
    }

    /// Marks what we have so far as being a group that we'd like to put on the same line
    /// When allocating lines, groups are kept together as much as possible
    pub fn group(self) -> Self {
        self.nest(Prec::Term)
    }

    /// Makes sure this Doc's precedence is at least as high as `prec`, putting parentheses around it if necessary
    /// Implies `group()`
    pub fn nest(self, prec: Prec) -> Self {
        if prec > self.prec {
            Doc {
                doc: RcDoc::text("(")
                    .append(self.doc)
                    .append(RcDoc::text(")"))
                    .group(),
                prec: Prec::Atom,
            }
        } else {
            Doc {
                doc: self.doc.group(),
                ..self
            }
        }
    }

    /// Create a new `Doc` representing the given object
    pub fn start<D: std::fmt::Display>(x: D) -> Self {
        Doc {
            doc: RcDoc::as_string(x),
            prec: Prec::Atom,
        }
    }

    /// Appends some text or an object to the `Doc`
    pub fn add<D: std::fmt::Display>(self, x: D) -> Self {
        let s = x.to_string();
        if s.chars().any(|x| {
            x.is_alphanumeric() || x == '\'' || x == '_' || x == '(' || x == ')' || x == ','
        }) {
            Doc {
                doc: self.doc.append(RcDoc::text(s)),
                ..self
            }
        } else if s.is_empty() {
            self
        } else {
            // It's not letters or numbers, must be a symbol
            Doc {
                doc: self
                    .doc
                    .append(RcDoc::text(s).annotate(Style::Symbol.spec())),
                ..self
            }
        }
    }

    /// Appends an object to the `Doc`, using the `Debug` formatter
    pub fn debug<D: std::fmt::Debug>(self, x: D) -> Self {
        let s = format!("{:?}", x);
        Doc {
            doc: self.doc.append(RcDoc::text(s)),
            ..self
        }
    }

    /// Appends another `Doc`
    /// You're responsible for decreasing the precedence to match
    pub fn chain(self, x: Self) -> Self {
        Doc {
            doc: self.doc.append(x.doc),
            ..self
        }
    }

    /// Sets the precedence of what we have so far
    pub fn prec(self, prec: Prec) -> Self {
        Doc { prec, ..self }
    }

    /// Appends a newline. Guaranteed to be a newline.
    pub fn hardline(self) -> Self {
        Doc {
            doc: self.doc.append(RcDoc::hardline()),
            ..self
        }
    }

    /// Marks that any line breaks in what we have so far should be indented another level
    pub fn indent(self) -> Self {
        Doc {
            doc: self.doc.nest(2),
            ..self
        }
    }

    /// Adds a break in a `group`, which might be a space or a newline
    pub fn line(self) -> Self {
        Doc {
            doc: self.doc.append(RcDoc::line()),
            ..self
        }
    }

    /// Appends a space
    pub fn space(self) -> Self {
        Doc {
            doc: self.doc.append(RcDoc::space()),
            ..self
        }
    }

    /// Creates a `Doc` displayed one way for multi-line, and another way for flat
    pub fn either(multi: Self, flat: Self) -> Self {
        Doc {
            doc: multi.doc.flat_alt(flat.doc).group(),
            prec: Prec::Term,
        }
    }
}

#[derive(Clone)]
pub struct Printer {
    writer: Arc<BufferWriter>,
    width: usize,
}
impl Printer {
    pub fn new(choice: ColorChoice, width: usize) -> Self {
        Printer {
            writer: Arc::new(BufferWriter::stderr(choice)),
            width,
        }
    }

    pub fn print(&self, doc: Doc) -> std::io::Result<()> {
        let mut buffer = self.writer.buffer();
        doc.doc.render_colored(self.width, &mut buffer)?;
        self.writer.print(&buffer)
    }
}

fn spec(col: Color, bold: bool) -> ColorSpec {
    let mut c = ColorSpec::new();
    c.set_fg(Some(col));
    c.set_bold(bold);
    c
}

pub trait Pretty {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc;
}

/// Like Pretty, but "standalone": doesn't require a `Bindings`.
pub trait SPretty {
    fn pretty(&self) -> Doc;
}

// impl<T: SPretty> Pretty for T {
//     fn pretty(&self, _ctx: &impl HasBindings) {
//         self.pretty()
//     }
// }
