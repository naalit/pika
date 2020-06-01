use crate::common::*;
use crate::error::FILES;
use rustyline::{
    completion::Completer,
    highlight::Highlighter,
    hint::Hinter,
    validate::{ValidationContext, ValidationResult, Validator},
    Editor, Helper,
};

struct ReplHelper;

impl Completer for ReplHelper {
    type Candidate = String;
}

impl Hinter for ReplHelper {}

impl Highlighter for ReplHelper {}

/// Allows multiline inputs
/// If the first line is empty or ends in `do`, `struct`, `=>`, or `=`, we'll allow more lines until a blank one
impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        if ctx.input().trim().is_empty() {
            Ok(ValidationResult::Incomplete)
        } else {
            let l: Vec<_> = ctx.input().lines().collect();
            if (l.first().unwrap().trim().is_empty() && !ctx.input().ends_with('\n'))
                || (!l.last().unwrap().contains('#')
                    && (ctx.input().trim().ends_with("do")
                        || ctx.input().trim().ends_with("struct")
                        || ctx.input().trim().ends_with("=>")
                        || ctx.input().trim().ends_with("=")))
            {
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
    rl.set_helper(Some(ReplHelper));

    let mut db = MainDatabase::default();
    let mut buf = String::new();
    let file = FILES
        .write()
        .unwrap()
        .add("<input>".to_string(), buf.clone());
    let mut seen_symbols = std::collections::HashSet::<Sym>::new();

    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                let old_buf = buf.clone();

                buf.push_str(&line);
                buf.push('\n');
                FILES.write().unwrap().set_source(file, buf.clone());

                db.set_source(file, std::sync::Arc::new(buf.clone()));

                for s in db.symbols(ScopeId::File(file)).iter() {
                    if !seen_symbols.contains(s) {
                        seen_symbols.insert(**s);
                        if let Some(elab) = db.elab(ScopeId::File(file), **s) {
                            let mut env = db.temp_env(ScopeId::File(file));
                            let ty = elab.get_type(&mut env);
                            let mut val = db
                                .val(ScopeId::File(file), **s)
                                .unwrap()
                                .cloned(&mut env.clone());
                            val.normal(&mut env);

                            let b = db.bindings();
                            let b = b.read().unwrap();
                            println!(
                                "{}{} : {} = {}",
                                b.resolve(**s),
                                s.num(),
                                WithContext(&b, &ty),
                                WithContext(&b, &val)
                            );
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
                }
                db.emit_errors();
            }
        }
    }
}
