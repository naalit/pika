use crate::common::*;
use crate::pretty::Style;
use codespan_reporting::term::termcolor::{Buffer, ColorChoice, WriteColor};
use regex::Regex;
use rustyline::{
    completion::Completer,
    highlight::Highlighter,
    hint::Hinter,
    validate::{ValidationContext, ValidationResult, Validator},
    Editor, Helper,
};
use std::borrow::Cow::{self, Borrowed, Owned};
use std::io::Write;

struct ReplHelper {
    literal: Regex,
    keyword: Regex,
    symbol: Regex,
    comment: Regex,
}

impl Default for ReplHelper {
    fn default() -> Self {
        // Yes, we do have an actual lexer, but this is a little more flexible
        ReplHelper {
            literal: Regex::new(r"((^|\s)\d+)|\(\)").unwrap(),
            keyword: Regex::new(r"\b(do|type|case|of|raise|catch|with|pure|struct|sig|end|val|fun|where|impl|if|then|else|and|or)\b").unwrap(),
            symbol: Regex::new(r">=|<=|>|<|==|!=|\+\+|\+|-|\*\*|\*|/|\^\^|&|=>|\||->|\\|\.|=|:").unwrap(),
            comment: Regex::new(r"#.*$").unwrap(),
        }
    }
}

impl Completer for ReplHelper {
    type Candidate = String;
}

impl Hinter for ReplHelper {
    type Hint = String;
}

fn match_regex<'l>(
    slices: Vec<(&'l str, Style)>,
    regex: &Regex,
    style: Style,
    overrides: bool,
) -> Vec<(&'l str, Style)> {
    slices
        .into_iter()
        .flat_map(|(slice, old_style)| {
            if old_style == Style::Comment || (old_style != Style::None && !overrides) {
                return vec![(slice, old_style)];
            }
            let mut slices = Vec::new();
            let mut pos = 0;
            for m in regex.find_iter(slice) {
                slices.push((&slice[pos..m.start()], old_style));
                slices.push((&slice[m.range()], style));
                pos = m.end();
            }
            slices.push((&slice[pos..], old_style));
            slices
        })
        .collect()
}

impl Highlighter for ReplHelper {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        _default: bool,
    ) -> Cow<'b, str> {
        let mut buffer = Buffer::ansi();
        buffer.set_color(&Style::Special.spec()).unwrap();
        write!(buffer, "{}", prompt).unwrap();
        buffer.reset().unwrap();
        Owned(String::from_utf8(buffer.into_inner()).unwrap())
    }

    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        if line.is_empty() {
            Borrowed(line)
        } else {
            let slices = vec![(line, Style::None)];
            let slices = match_regex(slices, &self.comment, Style::Comment, true);
            let slices = match_regex(slices, &self.keyword, Style::Keyword, true);
            let slices = match_regex(slices, &self.symbol, Style::Symbol, true);
            let slices = match_regex(slices, &self.literal, Style::Literal, false);

            let mut buffer = Buffer::ansi();

            for (slice, style) in slices {
                buffer.set_color(&style.spec()).unwrap();
                write!(buffer, "{}", slice).unwrap();
            }

            Owned(String::from_utf8(buffer.into_inner()).unwrap())
        }
    }

    fn highlight_char(&self, _line: &str, _pos: usize) -> bool {
        true
    }
}

/// Allows multiline inputs
/// If the input ends in `do`, `struct`, `sig`, `of`, `where`, `=>`, `=`, or `:`, or the last line is indented, we wait for more input.
/// If the first line is blank, we wait for another blank line to allow mutual recursion.
impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        if ctx.input().trim().is_empty() {
            Ok(ValidationResult::Incomplete)
        } else {
            let l: Vec<_> = ctx.input().lines().collect();
            let first_line = l.first().unwrap().trim();
            if first_line.is_empty() && !ctx.input().ends_with('\n') {
                Ok(ValidationResult::Incomplete)
            } else if ctx.input().trim().ends_with("do")
                || ctx.input().trim().ends_with("of")
                || ctx.input().trim().ends_with("where")
                || ctx.input().trim().ends_with("struct")
                || ctx.input().trim().ends_with("sig")
                || ctx.input().trim().ends_with("=")
                || ctx.input().trim().ends_with(":")
                || ctx.input().trim().ends_with("=>")
                || l.last().unwrap().starts_with(" ")
            {
                Ok(ValidationResult::Incomplete)
            } else {
                Ok(ValidationResult::Valid(None))
            }
        }
    }
}

impl Helper for ReplHelper {}

pub fn run_repl() {
    // A simple REPL
    let rconfig = rustyline::Config::builder().auto_add_history(true).build();
    let mut rl = Editor::<ReplHelper>::with_config(rconfig);
    rl.set_helper(Some(ReplHelper::default()));

    let mut db = Database::default();
    let mut buf = String::new();
    let file = crate::error::FILES
        .write()
        .unwrap()
        .add("<input>".to_string(), buf.clone());
    let mut last_seen = None;
    let mut old_len = 0;

    let printer = Printer::new(ColorChoice::Auto, 80);

    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                let old_buf = buf.clone();

                buf.push_str(&line);
                buf.push('\n');
                FILES.write().unwrap().set_source(file, buf.clone());

                db.set_file_source(file, buf.clone());

                db.check_all(file);
                if db.num_errors() == 0 {
                    let mut started_yet = last_seen.is_none();
                    let defs = db.top_level(file);

                    printer
                        .print(if defs.len() - old_len > 1 {
                            Doc::start("-->").style(Style::Special).hardline()
                        } else if defs.len() - old_len == 1 {
                            Doc::start("-->").style(Style::Special).space()
                        } else {
                            Doc::none()
                        })
                        .unwrap();
                    old_len = defs.len();

                    for &i in &*defs {
                        if started_yet {
                            // Print out the type and value of each definition
                            let (pre_id, cxt) = db.lookup_intern_def(i);
                            let predef = db.lookup_intern_predef(pre_id);
                            let mcxt = crate::elaborate::MCxt::new(cxt, i, &db);
                            let info = db.elaborate_def(i).unwrap();
                            let val = (*info.term)
                                .clone()
                                .evaluate(&mcxt.env(), &mcxt, &db)
                                .force(mcxt.size, &db, &mcxt);
                            let d = match predef.name() {
                                Some(name) => crate::pretty::Doc::keyword("val")
                                    .space()
                                    .add(name.get(&db))
                                    .space()
                                    .add(":")
                                    .space()
                                    .chain(info.typ.pretty(&db, &mcxt))
                                    .space()
                                    .add("=")
                                    .space()
                                    .chain(val.pretty(&db, &mcxt))
                                    .line(),
                                None => val
                                    .pretty(&db, &mcxt)
                                    .space()
                                    .add(":")
                                    .space()
                                    .chain(info.typ.pretty(&db, &mcxt))
                                    .line(),
                            };
                            printer.print(d).unwrap();
                            last_seen = Some(i);
                        } else if last_seen.map_or(true, |x| x == i) {
                            started_yet = true;
                        }
                    }
                } else {
                    // If the line they just input had errors, throw it out
                    db.write_errors();
                    buf = old_buf;
                }
            }
        }
    }
}
