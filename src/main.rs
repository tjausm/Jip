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
    /// path to oox program
    path: String,

    /// Print cfg in Dot format / print generated z3 formulas / verify program
    #[clap(subcommand)]
    mode: Mode,

    /// number between 0 and 255 denoting how deep we should prune
    /// , 0 = no pruning, 127 = prune to 50% of depth and so on
    #[clap(default_value_t = 0)]
    prune_ratio: i8,

    /// Turns on the front end simplifier
    #[clap(short, long)]
    simplifier: bool,
}

#[derive(Subcommand)]
enum Mode {
    /// Verify program and print result
    Verify {
        /// Up to which depth program is evaluated
        #[clap(default_value_t = 40)]
        depth: Depth,

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
    let program = match see::load_program(cli.path) {
            Err(why) => exit(why),
            Ok(program) => program,
        };

    // if program loaded execute function corresponding to cmd and exit with the result
    match cli.mode {
        Mode::PrintCFG => exit(see::print_cfg(&program)),
        Mode::Verify { depth, verbose } => {
            let config = Config {
                simplify: cli.simplifier,
            };
            exit(see::print_verification(&program, depth, cli.prune_ratio, config, verbose))
        }
        Mode::Bench {
            start,
            end,
            interval,
        } => {
            let config = Config {
                simplify: cli.simplifier,
            };
            exit(see::bench(&program, cli.prune_ratio, start, end, interval, config))
        }
    };
}
