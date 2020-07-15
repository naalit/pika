mod affine;
mod bicheck;
mod binding;
// mod codegen;
mod common;
mod elab;
mod error;
mod lexer;
// mod low;
mod options;
mod pattern;
mod printing;
mod query;
mod repl;
mod term;
// mod cps;
mod backend;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub grammar);

use crate::error::FILES;
use crate::options::*;
use crate::printing::*;
use crate::query::*;
use crate::repl::*;
use arg::Args;
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
                        let llvm = module.llvm(&context);

                        // let fpm = inkwell::passes::PassManager::create(());
                        // fpm.add_verifier_pass();
                        // fpm.add_function_inlining_pass();
                        // fpm.add_instruction_combining_pass();
                        // fpm.add_gvn_pass();
                        // fpm.add_cfg_simplification_pass();
                        // fpm.run_on(&llvm);

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
                            let engine = llvm
                                .create_jit_execution_engine(inkwell::OptimizationLevel::None)
                                .expect("Failed to create LLVM execution engine");
                            engine.add_global_mapping(
                                &llvm.get_function("malloc").unwrap(),
                                crate::backend::malloc as usize,
                            );
                            engine.add_global_mapping(
                                &llvm.get_function("_pika_print_int").unwrap(),
                                crate::backend::_pika_print_int as usize,
                            );
                            if let Ok(main_fun) =
                                unsafe { engine.get_function::<unsafe extern "C" fn()>("_start") }
                            {
                                printer
                                    .print(
                                        Doc::start("Running `main`").style(Style::Bold).hardline(),
                                    )
                                    .unwrap();
                                unsafe {
                                    main_fun.call();
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
