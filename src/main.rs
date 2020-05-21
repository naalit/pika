mod bicheck;
mod binding;
mod common;
mod error;
mod term;
use common::*;
mod eval;

use lalrpop_util::*;
lalrpop_mod!(pub grammar);

fn main() {
    // A simple REPL
    let config = rustyline::Config::builder().auto_add_history(true).build();
    let mut rl = rustyline::Editor::<()>::with_config(config);
    let parser = grammar::STermParser::new();
    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                // Currently we create a new file for every line of input
                let f = error::FILES
                    .write()
                    .unwrap()
                    .add("<input>".to_string(), line.clone());
                // And also a new Bindings
                // Eventually we'll want to be able to define and then reuse names, so we'll need to change that
                match parser
                    .parse(&line)
                    .map_err(|x| error::Error::from_lalrpop(x, f))
                    .and_then(|x| Bindings::resolve_names(x).map_err(|x| x.to_error(f)))
                {
                    Ok((binds, t)) => {
                        let mut ctx = eval::Context::new(binds);
                        let tv = t.reduce(&mut ctx);
                        let binds = ctx.bindings;
                        println!("{}", WithContext(&binds, &tv));
                        let mut tenv = bicheck::TEnv::new(eval::Context::new(binds));
                        let ty = bicheck::synth(&t, &mut tenv);
                        let binds = tenv.ctx.bindings;
                        match ty {
                            Ok(ty) => println!("   : {}", WithContext(&binds, &ty)),
                            Err(e) => e.to_error(f, &binds).write().unwrap(),
                        }
                    }
                    Err(e) => e.write().unwrap(),
                }
            }
        }
    }
}
