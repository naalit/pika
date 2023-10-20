use std::collections::VecDeque;

use ariadne::Color;
use yansi::Style;

pub trait Pretty {
    fn pretty(&self, db: &(impl crate::elab::Elaborator + ?Sized)) -> Doc;
}

pub trait IntoStyle {
    fn into_style(self) -> Option<Style>;
}
impl IntoStyle for Style {
    fn into_style(self) -> Option<Style> {
        Some(self)
    }
}
impl IntoStyle for Color {
    fn into_style(self) -> Option<Style> {
        Some(Style::new(self))
    }
}
impl IntoStyle for () {
    fn into_style(self) -> Option<Style> {
        None
    }
}

#[derive(PartialOrd, PartialEq, Eq, Ord, Clone, Copy, Debug)]
pub enum Prec {
    Term,
    Pair,
    Pi,
    App,
    Atom,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DocEntry {
    String(String, Style),
    Break,
    Newline,
    Doc(Box<Doc>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Doc {
    data: VecDeque<DocEntry>,
    indent: usize,
    prec: Prec,
}
impl<T: std::fmt::Display + ?Sized> From<&T> for Doc {
    fn from(x: &T) -> Self {
        Doc::start(x)
    }
}
impl std::fmt::Display for Doc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf = String::new();
        self.clone().add_string(true, 0, &mut buf);
        f.write_str(&buf)
    }
}

impl Doc {
    // The first few colors from ariadne::ColorGenerator
    // This way we can access them anywhere more easily
    pub const COLOR1: ariadne::Color = ariadne::Color::Fixed(201);
    pub const COLOR2: ariadne::Color = ariadne::Color::Fixed(155);
    pub const COLOR3: ariadne::Color = ariadne::Color::Fixed(187);
    pub const COLOR4: ariadne::Color = ariadne::Color::Fixed(218);
    pub const COLOR5: ariadne::Color = ariadne::Color::Fixed(158);

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn style_keyword() -> Style {
        Color::Magenta.style()
    }

    pub fn style_literal() -> Style {
        Color::Cyan.style()
    }

    /// Applies `style` to any string data directly in this Doc.
    /// Does not apply to nested Docs.
    pub fn style(mut self, style: impl IntoStyle) -> Self {
        let style = style.into_style().unwrap_or_default();
        for i in &mut self.data {
            if let DocEntry::String(_, s) = i {
                *s = style;
            }
        }
        self
    }

    fn add_string(self, style: bool, indent: usize, buf: &mut String) {
        use std::fmt::Write;
        let indent = indent + self.indent;

        for i in self.data {
            match i {
                // TODO potentially switch to newline if necessary
                DocEntry::Break => buf.push(' '),
                DocEntry::Newline => {
                    buf.push('\n');
                    for _ in 0..indent {
                        buf.push(' ');
                    }
                }
                DocEntry::String(text, s) => {
                    if style {
                        write!(buf, "{}", s.paint(text)).unwrap();
                    } else {
                        buf.push_str(&text);
                    }
                }
                DocEntry::Doc(doc) => doc.add_string(style, indent, buf),
            }
        }
    }

    pub fn emit_stderr(self) {
        eprintln!("{}", self.to_string(true));
    }

    pub fn to_string(self, style: bool) -> String {
        let mut buf = String::new();
        self.add_string(style, 0, &mut buf);
        buf
    }

    /// An empty `Doc`
    pub fn none() -> Self {
        Doc {
            data: VecDeque::new(),
            indent: 0,
            prec: Prec::Atom,
        }
    }

    /// Separates a list of `Doc`s with `sep`. It doesn't put `sep` at the beginning or end, just in between each one.
    ///
    /// `intersperse(&[a, b, c], s) = a.chain(s).chain(b).chain(s).chain(c)`
    pub fn intersperse(docs: impl IntoIterator<Item = Self>, sep: Self) -> Self {
        let mut data = VecDeque::new();
        for i in docs {
            data.push_back(DocEntry::Doc(Box::new(i)));
            data.push_back(DocEntry::Doc(Box::new(sep.clone())));
        }
        data.pop_back();
        Doc {
            data,
            indent: 0,
            prec: Prec::Term,
        }
    }

    /// Makes sure this Doc's precedence is at least as high as `prec`, putting parentheses around it if necessary
    pub fn nest(mut self, prec: Prec) -> Self {
        if prec > self.prec {
            self.data
                .push_front(DocEntry::String("(".to_string(), Style::default()));
            self.data
                .push_back(DocEntry::String(")".to_string(), Style::default()));
            self.prec = Prec::Atom;
        }
        self
    }

    /// Create a new `Doc` representing the given object
    pub fn start<D: std::fmt::Display>(x: D) -> Self {
        Doc {
            data: std::iter::once(x)
                .map(|x| DocEntry::String(x.to_string(), Style::default()))
                .collect(),
            indent: 0,
            prec: Prec::Atom,
        }
    }

    /// Appends some text or an object to the `Doc`
    pub fn add<D: std::fmt::Display, S: IntoStyle>(mut self, x: D, style: S) -> Self {
        self.data.push_back(DocEntry::String(
            x.to_string(),
            style.into_style().unwrap_or_default(),
        ));
        self
    }

    /// Appends another `Doc`
    /// You're responsible for decreasing the precedence to match
    pub fn chain(mut self, x: Self) -> Self {
        self.data.push_back(DocEntry::Doc(Box::new(x)));
        self
    }

    /// Appends an object to the `Doc`, using the `Debug` formatter
    pub fn debug<D: std::fmt::Debug>(mut self, x: D) -> Self {
        let s = format!("{:?}", x);
        self.data.push_back(DocEntry::String(s, Style::default()));
        self
    }

    /// Sets the precedence of what we have so far
    pub fn prec(self, prec: Prec) -> Self {
        Doc { prec, ..self }
    }

    /// Appends a newline. Guaranteed to be a newline.
    pub fn hardline(mut self) -> Self {
        self.data.push_back(DocEntry::Newline);
        self
    }

    /// Marks that any line breaks in what we have so far should be indented another level
    pub fn indent(mut self) -> Self {
        self.indent += 4;
        // We need another doc so the indent doesn't extend farther
        Doc::none().chain(self)
    }

    /// Adds a break character, which might be a space or a newline
    pub fn brk(mut self) -> Self {
        self.data.push_back(DocEntry::Break);
        self
    }

    /// Appends a space
    pub fn space(self) -> Self {
        self.add(' ', ())
    }
}
