//! Binary 'jip' is a cmd-line tool for performing static analysis on programs written in the OOX language.
//!

#[macro_use]
extern crate lalrpop_util;

use clap::{ArgEnum, Parser, Subcommand};
use see::types::Depth;
use shared::{Config, ExitCode};
use std::process::exit;
// module declarations
mod ast;
mod cfg;
mod see;
mod shared;
mod symbolic;
mod z3;

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

/// BEWARE: flags are hardcoded in the test builder
#[derive(Subcommand)]
enum Mode {
    /// Verify program and print result
    Verify {
        /// Up to which depth program is evaluated
        #[clap(default_value_t = 40)]
        depth: Depth,
        /// Turns on the front end simplifier
        #[clap(short, long)]
        simplifier: bool,
        /// Report diagnostic information after succesful program verification
        #[clap(short, long)]
        verbose: bool,
    },
    /// Print cfg in Dot format
    PrintCFG,
    /// Measure time to verify a program.
    Bench {
        /// Given start depth s we measure verification time for depth s
        start: Depth,
        /// Gven end depth e we measure verification time for each depth between s and e with intervals of 5
        end: Option<Depth>,
        /// Given interval i we measure verification time for each depth between s and e with intervals of i
        #[clap(default_value_t = 5)]
        interval: Depth,
        /// Turns on the front end simplifier
        #[clap(short, long)]
        simplifier: bool,
    },
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
        Mode::Verify {
            depth,
            simplifier,
            verbose,
        } => {
            let config = Config {
                simplify: simplifier,
            };
            exit(see::print_verification(&program, depth, config, verbose))
        }
        Mode::Bench {
            start,
            end,
            interval,
            simplifier,
        } => {
            let config = Config {
                simplify: simplifier,
            };
            exit(see::bench(&program, start, end, interval, config))
        }
    };
}
