mod term;
use term::*;
mod error;
mod bicheck;

use lalrpop_util::*;
lalrpop_mod!(pub grammar);

fn main() {
    let config = rustyline::Config::builder()
        .auto_add_history(true)
        .build();
    let mut rl = rustyline::Editor::<()>::with_config(config);
    let parser = grammar::STermParser::new();
    loop {
        let readline = rl.readline("> ");
        match readline {
            Err(_) => break,
            Ok(line) => {
                let f = error::FILES.write().unwrap().add("<input>".to_string(), line.clone());
                match parser.parse(&line) {
                    Ok(t) => {
                        println!("{}", *t);
                        let ty = bicheck::synth(&t, &mut Env::new());
                        match ty {
                            Ok(ty) => println!("   : {}", *ty),
                            Err(e) => e.to_error(f).write().unwrap(),
                        }
                    },
                    Err(e) => error::Error::from_lalrpop(e, f).write().unwrap(),
                }
            }
        }
    }
}
