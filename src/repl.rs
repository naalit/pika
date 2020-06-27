use crate::binding::Sym;
use crate::common::{termcolor, Span};
use crate::elab::Cloner;
use crate::options::Options;
use crate::printing::*;
use crate::query::{MainDatabase, MainGroup, ScopeId};
use crate::{
    elab::{ECtx, Elab},
    error::FILES,
};
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
use termcolor::{Buffer, WriteColor};

struct ReplHelper {
    literal: Regex,
    keyword: Regex,
    symbol: Regex,
    binder: Regex,
    comment: Regex,
}

impl Default for ReplHelper {
    fn default() -> Self {
        // Yes, we do have an actual lexer, but this is a little more flexible
        // We can do binders, etc. without actually lexing them, and ignore lexer errors
        ReplHelper {
            literal: Regex::new(r"((^|\s)\d+)|\(\)").unwrap(),
            keyword: Regex::new(r"fun|struct|do|tag|the|move|type|of").unwrap(),
            symbol: Regex::new(r"=>|\.|=|:|\|").unwrap(),
            binder: Regex::new(r"([a-zA-Z_][a-zA-Z_0-9]*[\t ]*)+:").unwrap(),
            comment: Regex::new(r"#[^\n]*").unwrap(),
        }
    }
}

impl Completer for ReplHelper {
    type Candidate = String;
}

impl Hinter for ReplHelper {}

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
            let slices = match_regex(slices, &self.binder, Style::Binder, true);
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
/// If the first line is empty or ends in `do`, `struct`, `fun`, `=>`, or `=`, we'll allow more lines until a blank one
impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        if ctx.input().trim().is_empty() {
            Ok(ValidationResult::Incomplete)
        } else {
            let l: Vec<_> = ctx.input().lines().collect();
            let first_line = l.first().unwrap().trim();
            let is_multiline = first_line.is_empty()
                || (!first_line.contains('#')
                    && (first_line.ends_with("do")
                        || first_line.ends_with("struct")
                        || first_line.ends_with("fun")
                        || first_line.ends_with("of")
                        || first_line.ends_with("=>")
                        || first_line.ends_with("=")
                        || first_line.ends_with(":")));
            if is_multiline && !ctx.input().ends_with('\n') {
                Ok(ValidationResult::Incomplete)
            } else {
                Ok(ValidationResult::Valid(None))
            }
        }
    }
}

impl Helper for ReplHelper {}

pub fn run_repl(options: &Options) {
    // A simple REPL
    let rconfig = rustyline::Config::builder().auto_add_history(true).build();
    let mut rl = Editor::<ReplHelper>::with_config(rconfig);
    rl.set_helper(Some(ReplHelper::default()));

    let mut db = MainDatabase::default();
    let mut buf = String::new();
    let file = FILES
        .write()
        .unwrap()
        .add("<input>".to_string(), buf.clone());
    let mut seen_symbols = std::collections::HashSet::<Sym>::new();

    let printer = Printer::new(options.color.0, 80); //rl.dimensions().map_or(80, |x| x.0));

    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                let old_buf = buf.clone();
                let old_syms = seen_symbols.clone();

                buf.push_str(&line);
                buf.push('\n');
                FILES.write().unwrap().set_source(file, buf.clone());

                db.set_source(file, std::sync::Arc::new(buf.clone()));

                let mut first = true;

                for s in db.symbols(ScopeId::File(file)).iter() {
                    if !seen_symbols.contains(s) {
                        if let Some(elab) = db.elab(ScopeId::File(file), **s) {
                            seen_symbols.insert(**s);

                            if first {
                                printer
                                    .print(if line.contains("\n") {
                                        Doc::start("-->").style(Style::Special).hardline()
                                    } else {
                                        Doc::start("-->").style(Style::Special).space()
                                    })
                                    .unwrap();
                                first = false;
                            }

                            let scoped = (ScopeId::File(file), &db);
                            let mut ectx = ECtx::new(&scoped);
                            let ty = elab.get_type(&ectx);
                            ectx.set_val(
                                **s,
                                Elab::Var(
                                    Span::empty(),
                                    **s,
                                    Box::new(ty.cloned(&mut Cloner::new(&ectx))),
                                ),
                            );
                            let val = elab.cloned(&mut Cloner::new(&ectx)).normal(&mut ectx);

                            let doc = Doc::either(
                                s.pretty(&db)
                                    .style(Style::Binder)
                                    .line()
                                    .add(":")
                                    .space()
                                    .chain(ty.pretty(&db).group())
                                    .line()
                                    .add("=")
                                    .space()
                                    .chain(val.pretty(&db).group())
                                    .group()
                                    .indent(),
                                s.pretty(&db)
                                    .space()
                                    .add(":")
                                    .style(Style::Binder)
                                    .space()
                                    .chain(ty.pretty(&db))
                                    .space()
                                    .add("=")
                                    .space()
                                    .chain(val.pretty(&db))
                                    .group(),
                            )
                            .hardline();
                            printer.print(doc).unwrap();
                        }
                    }
                }

                if options.show_llvm {
                    // Generate LLVM and print out the module, for now
                    let module = db.low_mod(file);
                    let context = inkwell::context::Context::create();
                    let llvm = module.codegen(&mut crate::codegen::CodegenCtx::new(&context));
                    llvm.print_to_stderr();

                    // For now we verify it but don't run it
                    if let Err(e) = llvm.verify() {
                        println!("Verification error: {}", e);
                    }
                }

                // If the line they just input had errors, throw it out
                if db.has_errors() {
                    buf = old_buf;
                    seen_symbols = old_syms;
                }
                db.emit_errors();
            }
        }
    }
}
