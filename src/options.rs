use crate::common::*;
use arg::Args;
use codespan_reporting::term::termcolor;

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
                let printer = Printer::new(termcolor::ColorChoice::Auto, 80);
                printer
                    .print(
                        Doc::start("error")
                            .style(Style::BoldRed)
                            .add(": Unknown command: '")
                            .add(s)
                            .add("'")
                            .style(Style::Bold)
                            .line()
                            .chain(
                                Doc::start("help: valid commands are 'repl', 'run', and 'build'")
                                    .style(Style::Note),
                            )
                            .hardline(),
                    )
                    .unwrap();
                Err(())
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ColorChoice(pub termcolor::ColorChoice);
impl std::str::FromStr for ColorChoice {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, ()> {
        let s = s.trim();
        match s {
            "none" => Ok(ColorChoice(termcolor::ColorChoice::Never)),
            "always" => Ok(ColorChoice(termcolor::ColorChoice::Always)),
            "auto" => Ok(ColorChoice(termcolor::ColorChoice::Auto)),
            _ => {
                eprintln!("Unknown color choice: {}", s);
                Err(())
            }
        }
    }
}
impl Default for ColorChoice {
    fn default() -> Self {
        ColorChoice(termcolor::ColorChoice::Auto)
    }
}

#[derive(Args, Debug, Clone)]
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
    ///Whether to use colors. One of `none`, `always`, `auto` (default)
    pub color: ColorChoice,

    #[arg(long = "show-llvm")]
    ///Should the REPL generate LLVM code and print it to stderr?
    pub show_llvm: bool,

    #[arg(long = "show-low-ir")]
    ///Show Pika's LowIR for each definition
    pub show_low_ir: bool,

    ///The files to compile
    pub input_files: Vec<String>,
}
