mod affine;
mod bicheck;
mod binding;
mod codegen;
mod common;
mod elab;
mod error;
mod lexer;
mod low;
mod options;
mod pattern;
mod printing;
mod query;
mod repl;
mod term;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub grammar);

use crate::common::HasBindings;
use crate::error::FILES;
use crate::options::*;
use crate::printing::*;
use crate::query::*;
use crate::repl::*;
use arg::Args;
use bicheck::TCtx;
use std::fs::File;
use std::io::Read;
use std::time::Instant;

fn main() {
    // Skip the binary path
    let args: Vec<String> = std::env::args().skip(1).collect();
    match Options::from_args(args.iter().map(|x| &**x)) {
        Ok(options) => match options.command {
            Command::Repl => run_repl(&options),
            Command::Build | Command::Run => {
                let start_time = Instant::now();

                let printer = Printer::new(options.color.0, 80);

                let mut db = MainDatabase::default();
                db.set_options(options.clone());
                for i in &options.input_files {
                    let mut file = File::open(i).unwrap_or_else(|e| match e.kind() {
                        std::io::ErrorKind::NotFound => {
                            printer
                                .print(
                                    Doc::start("error")
                                        .style(Style::BoldRed)
                                        .add(": File not found: '")
                                        .add(i)
                                        .add("'")
                                        .style(Style::Bold)
                                        .hardline(),
                                )
                                .unwrap();
                            std::process::exit(1);
                        }
                        _ => {
                            printer
                                .print(
                                    Doc::start("error")
                                        .style(Style::BoldRed)
                                        .add(": Error opening file: '")
                                        .add(e)
                                        .add("'")
                                        .style(Style::Bold)
                                        .hardline(),
                                )
                                .unwrap();
                            std::process::exit(1);
                        }
                    });
                    let mut buf = String::new();
                    file.read_to_string(&mut buf).expect("Error reading file");
                    if !buf.ends_with('\n') {
                        buf.push('\n');
                    }

                    let file = FILES
                        .write()
                        .unwrap()
                        .add("<input>".to_string(), buf.clone());
                    db.set_source(file, std::sync::Arc::new(buf));

                    // The primary query, which calls others
                    let module = db.low_mod(file);

                    if db.has_errors() {
                        db.emit_errors();
                        std::process::exit(1)
                    }

                    if options.command == Command::Run || options.show_llvm {
                        // Generate LLVM
                        let context = inkwell::context::Context::create();
                        let llvm = module.codegen(&mut crate::codegen::CodegenCtx::new(&context));

                        if options.show_llvm {
                            llvm.print_to_stderr();
                        }

                        if let Err(e) = llvm.verify() {
                            printer
                                .print(
                                    Doc::start("error")
                                        .style(Style::BoldRed)
                                        .add(": LLVM verification error: ")
                                        .style(Style::Bold)
                                        .line()
                                        .add(e.to_string())
                                        .hardline(),
                                )
                                .unwrap();
                            std::process::exit(1);
                        } else {
                            printer
                                .print(
                                    Doc::start("Build successful in ")
                                        .debug(Instant::now() - start_time)
                                        .style(Style::Bold)
                                        .hardline(),
                                )
                                .unwrap();
                        }

                        if options.command == Command::Run {
                            let main_raw = db.bindings_mut().raw("main".to_string());
                            if let Some(main) = db
                                .symbols(ScopeId::File(file))
                                .iter()
                                .find(|x| x.raw() == main_raw)
                            {
                                let main_mangled = db.mangle(ScopeId::File(file), **main).unwrap();
                                let engine = llvm
                                    .create_jit_execution_engine(inkwell::OptimizationLevel::None)
                                    .expect("Failed to create LLVM execution engine");

                                let scoped = (ScopeId::File(file), &db);
                                let mut tctx = TCtx::new(&scoped);

                                use crate::elab::Elab;
                                use crate::term::Builtin;
                                match db
                                    .elab(ScopeId::File(file), **main)
                                    .unwrap()
                                    .get_type(&scoped)
                                {
                                    x if x.unify(
                                        &Elab::Builtin(Builtin::Int),
                                        &mut tctx,
                                        &mut Vec::new(),
                                    ) =>
                                    unsafe {
                                        let main_fun: inkwell::execution_engine::JitFunction<
                                            unsafe extern "C" fn() -> i32,
                                        > = engine.get_function(&main_mangled).unwrap();
                                        let result = main_fun.call();
                                        println!("{}", result);
                                    }
                                    x if x.unify(
                                        &Elab::Pair(
                                            Box::new(Elab::Builtin(Builtin::Int)),
                                            Box::new(Elab::Builtin(Builtin::Int)),
                                        ),
                                        &mut tctx,
                                        &mut Vec::new(),
                                    ) =>
                                    unsafe {
                                        // Rust aligns (i32, i32) differently than LLVM does, so values .1 and .3 in the result are padding
                                        let main_fun: inkwell::execution_engine::JitFunction<
                                            unsafe extern "C" fn() -> (i32, i32, i32, i32),
                                        > = engine.get_function(&main_mangled).unwrap();
                                        let result = main_fun.call();
                                        println!("({}, {})", result.0, result.2);
                                    }
                                    x => {
                                        printer.print(
                                            Doc::start("error")
                                                .style(Style::BoldRed)
                                                .add(": `main` can't return '")
                                                .chain(x.pretty(&db).group().style(Style::None))
                                                .add("'")
                                                .style(Style::Bold)
                                                .line()
                                                .chain(Doc::start("help: `main` can return either 'Int' or '(Int, Int)'").style(Style::Note))
                                                .hardline()
                                        ).unwrap();
                                        std::process::exit(1)
                                    }
                                }
                            } else {
                                printer
                                    .print(
                                        Doc::start("error")
                                            .style(Style::BoldRed)
                                            .add(": `run` command specified but no `main` found!")
                                            .style(Style::Bold)
                                            .hardline(),
                                    )
                                    .unwrap();
                                std::process::exit(1)
                            }
                        }
                    } else {
                        printer
                            .print(
                                Doc::start("Build successful in ")
                                    .debug(Instant::now() - start_time)
                                    .style(Style::Bold)
                                    .hardline(),
                            )
                            .unwrap();
                    }
                }
            }
        },
        Err(err) => match err {
            // We already emitted the error in the FromStr impl
            arg::ParseError::InvalidArgValue(_, _) => std::process::exit(1),
            err => {
                let printer = Printer::new(termcolor::ColorChoice::Auto, 80);
                printer
                    .print(
                        Doc::start("error")
                            .style(Style::BoldRed)
                            .add(": ")
                            .add(err)
                            .hardline()
                            .style(Style::Bold),
                    )
                    .unwrap();
                std::process::exit(1);
            }
        },
    }
}
