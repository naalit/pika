pub use codespan_reporting::term::termcolor;
pub use pretty::RcDoc;
use std::sync::Arc;
use termcolor::*;

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
    Note,
    None,
}
impl Style {
    pub fn spec(self) -> ColorSpec {
        match self {
            Style::Keyword => spec(Color::Magenta, false),
            Style::Binder => spec(Color::Cyan, false),
            Style::Literal => spec(Color::Red, false),
            Style::Symbol => spec(Color::Green, false),
            Style::Special => spec(Color::Blue, true),
            Style::Bold => ColorSpec::new().set_bold(true).clone(),
            Style::Note => spec(Color::Blue, false),
            Style::None => ColorSpec::new(),
        }
    }
}

/// A wrapper around a `pretty::RcDoc` with precedence tracking and a different interface
#[derive(Clone)]
pub struct Doc<'a> {
    doc: RcDoc<'a, ColorSpec>,
    prec: Prec,
}

impl<'a> Into<String> for Doc<'a> {
    /// Calls `Doc::ansi_string()`
    fn into(self) -> String {
        self.ansi_string()
    }
}

impl<'a> Doc<'a> {
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
    pub fn style(self, ann: Style) -> Self {
        Doc {
            doc: self.doc.annotate(ann.spec()),
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
        if s.chars()
            .any(|x| x.is_alphanumeric() || x == '\'' || x == '_')
        {
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

    /// Appends another `Doc`
    /// You're responsible for decreasing the precedence to match
    pub fn chain(self, x: Doc<'a>) -> Self {
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
            doc: multi.doc.flat_alt(flat.doc),
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
    type Context;
    fn pretty(&self, ctx: &Self::Context) -> Doc;
}