#[macro_use]
extern crate lalrpop_util;

use clap::{ArgEnum, Parser, Subcommand};
use std::path::Path;
use std::process::exit;

// module declarations
mod ast;
mod cfg;
mod paths;
mod see;
mod z3;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {
    /// How to load the program
    #[clap(arg_enum)]
    load_mode: LoadMode,
    // Filepath or program as string
    program: String,

    /// Print cfg in Dot format / print generated z3 formulas / verify program 
    #[clap(arg_enum)]
    mode: Mode,

    // Up to which depth program is evaluated
    #[clap(default_value_t = 40)]
    depth: paths::Depth,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ArgEnum)]
enum Mode {
    PrintCFG,
    PrintFormulas,
    VerifyProgram,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ArgEnum)]
enum LoadMode {
    File,
    String,
}

fn main() {
    let cli = Cli::parse();
    let exit = |(exit_code, result): (i32, String)| {
        println!("{}", result);
        exit(exit_code);
    };

    let program = match cli.load_mode {
        LoadMode::File => match see::load_program(cli.program) {
            Err(why) => exit(why),
            Ok(program) => program,
        },
        LoadMode::String => cli.program,
    };
    match cli.mode {
        Mode::PrintCFG => exit(see::print_cfg(&program)),
        Mode::PrintFormulas => exit(see::print_formulas(&program, cli.depth)),
        Mode::VerifyProgram => exit(see::print_verification(&program, cli.depth)),
    };
}
