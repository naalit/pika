use lalrpop_util::lalrpop_mod;
use std::fs::File;
use std::io::{BufRead, Read};

// TODO:
// - Write README
// - Make `test.pk` a better demo
// - COMMIT before changing compiler at all yet

pub mod elaborate;
pub mod error;
pub mod evaluate;
pub mod query;
pub mod term;
use query::*;

lalrpop_mod!(pub grammar); // synthesized by LALRPOP

fn main() {
    let mut buf = String::new();
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
        db.write_errors();
    } else {
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
