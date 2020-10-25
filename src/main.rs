use lalrpop_util::lalrpop_mod;
use std::fs::File;
use std::io::{BufRead, Read};

pub mod elaborate;
pub mod error;
pub mod evaluate;
pub mod lexer;
pub mod pretty;
pub mod query;
pub mod term;
pub mod lower;
use query::*;

lalrpop_mod!(pub grammar);

fn main() {
    if let Some(file_name) = std::env::args().skip(1).next() {
        let mut file = File::open(file_name.clone()).unwrap();
        let mut buf = String::new();
        file.read_to_string(&mut buf).unwrap();
        if !buf.ends_with('\n') {
            buf.push('\n');
        }
        let mut db = Database::default();
        let id = error::FILES.write().unwrap().add(file_name, buf.clone());
        db.set_file_source(id, buf);
        db.check_all(id);
        if db.num_errors() == 0 {
            println!("File elaborated successfully!")
        } else {
            db.write_errors();
        }
    } else {
        // let mut buf = String::new();
        // loop {
        //     std::io::stdin().read_line(&mut buf).unwrap();
        //     if !buf.ends_with("\n\n") {
        //         continue;
        //     }
        //     match grammar::DefsParser::new().parse(buf.trim()) {
        //         Ok(_) => println!("Good!"),
        //         Err(e) => println!("Bad!\n\t{}", e),
        //     }
        //     buf = String::new();
        // }
    }
}
