use arg::Args;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Command {
    Repl,
    Build,
    Run,
}
impl std::str::FromStr for Command {
    type Err = ();
    fn from_str(s: &str) -> Result<Command, ()> {
        let s = s.trim();
        match s {
            "repl" => Ok(Command::Repl),
            "build" => Ok(Command::Build),
            "run" => Ok(Command::Run),
            _ => {
                eprintln!("Unknown command: {}", s);
                Err(())
            }
        }
    }
}

#[derive(Args, Debug)]
///Pika compiler
///
///Commands:
///  repl           Start the Read-Eval-Print Loop
///  build          Build the given file(s)
///  run            Run the given file(s)
pub struct Options {
    #[arg(required)]
    pub command: Command,

    #[arg(long)]
    ///Should the REPL generate LLVM code and print it to stderr?
    pub show_llvm: bool,

    ///The files to compile
    pub input_files: Vec<String>,
}
