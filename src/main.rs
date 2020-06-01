mod bicheck;
mod binding;
mod codegen;
mod common;
mod elab;
mod error;
mod lexer;
mod options;
mod query;
mod repl;
mod term;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub grammar);

use crate::common::*;
use crate::error::FILES;
use crate::repl::*;
use arg::Args;
use std::fs::File;
use std::io::Read;

fn main() {
    // Skip the binary path
    let args: Vec<String> = std::env::args().skip(1).collect();
    match Options::from_args(args.iter().map(|x| &**x)) {
        Ok(options) => {
            if options.input_files.is_empty() {
                run_repl(&options)
            } else {
                let mut db = MainDatabase::default();
                for i in &options.input_files {
                    let mut file = File::open(i).unwrap();
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

                    for s in db.symbols(ScopeId::File(file)).iter() {
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

                    if db.has_errors() {
                        db.emit_errors();
                        std::process::exit(1)
                    }
                }
            }
        }
        Err(err) => {
            eprintln!("{}", err);
            std::process::exit(1)
        }
    }
}
