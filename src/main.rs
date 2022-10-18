//! Binary 'jip' is a cmd-line tool for performing static analysis on programs written in the OOX language.
//! 

#[macro_use]
extern crate lalrpop_util;

use clap::{ArgEnum, Parser, Subcommand};
use see::ExitCode;
use std::process::exit;

// module declarations
mod ast;
mod cfg;
mod see;
mod z3;
mod shared;
mod bench;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {
    /// How to load the program
    #[clap(arg_enum)]
    load_mode: LoadMode,

    /// Filepath or program as string
    program: String,

    /// Print cfg in Dot format / print generated z3 formulas / verify program 
    #[clap(subcommand)]
    mode: Mode,


}

#[derive(Subcommand)]
enum Mode {
    /// Verify program and print result
    Verify {
        /// Up to which depth program is evaluated
        #[clap(default_value_t = 40)]
        depth: see::Depth,
    },
    /// Print cfg in Dot format
    PrintCFG,
    Benchmark {
        /// Lowest depth
        #[clap(default_value_t = 40)]
        start: see::Depth,
        /// Highest depth
        #[clap(default_value_t = 40)]
        end: see::Depth,
        /// Interval between depths
        #[clap(default_value_t = 10)]
        interval: see::Depth,
        
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ArgEnum)]
enum LoadMode {
    File,
    String,
}

fn main() {
    let cli = Cli::parse();
    let exit = |(exit_code, result): (ExitCode, String)| {
        println!("{}", result);
        exit(exit_code as i32);
    };

    // attempt to load program, and exit with exitcode and error if fails
    let program = match cli.load_mode {
        LoadMode::File => match see::load_program(cli.program) {
            Err(why) => exit(why),
            Ok(program) => program,
        },
        LoadMode::String => cli.program,
    };

    // if program loaded execute function corresponding to cmd and exit with the result
    match cli.mode {
        Mode::PrintCFG => exit(see::print_cfg(&program)),
        Mode::Verify {depth} => exit(see::print_verification(&program, depth)),
        Mode::Benchmark {start, end, interval} => exit(bench::bench(&program, start, end, interval)),
    };
}
