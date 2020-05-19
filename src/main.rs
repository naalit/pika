mod term;
use term::*;
mod bicheck;
mod binding;
mod common;
mod error;
use common::*;

use lalrpop_util::*;
lalrpop_mod!(pub grammar);

fn main() {
    let config = rustyline::Config::builder().auto_add_history(true).build();
    let mut rl = rustyline::Editor::<()>::with_config(config);
    let parser = grammar::STermParser::new();
    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                let f = error::FILES
                    .write()
                    .unwrap()
                    .add("<input>".to_string(), line.clone());
                match parser.parse(&line) {
                    Ok(t) => {
                        let (binds, t) = Bindings::resolve_names(t).unwrap();
                        println!("{}", WithContext(&binds, &*t));
                        let ty = bicheck::synth(&t, &mut Env::new());
                        match ty {
                            Ok(ty) => println!("   : {}", WithContext(&binds, &*ty)),
                            Err(e) => e.to_error(f, &binds).write().unwrap(),
                        }
                    }
                    Err(e) => error::Error::from_lalrpop(e, f).write().unwrap(),
                }
            }
        }
    }
}
