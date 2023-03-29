//! Binary 'jip' is a cmd-line tool for performing static analysis on programs written in the OOX language.
//!

#[macro_use]
extern crate lalrpop_util;

#[macro_use]
extern crate global_counter;

use clap::{Parser, Subcommand};
use shared::{Config, ExitCode, SolverType, Depth};
use std::process::exit;

// module declarations
mod ast;
mod cfg;
mod see;
mod shared;
mod smt_solver;
mod symbolic;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {
    /// path to oox program
    path: String,

    /// Print cfg in Dot format / print generated z3 formulas / verify program
    #[clap(subcommand)]
    mode: Mode,

    /// Turns on the front end simplifier
    #[clap(short, long)]
    simplifier: bool,

    /// Turns on array size inference & simplifier
    #[clap(short, long)]
    infer_size: bool,

    /// number between 0 and 127 denoting how deep we should prune
    /// , 0 = no pruning, 63 = prune to 50% of depth and so on
    #[clap(default_value_t = 0)]
    prune_ratio: i8,

    /// Passes the custom argument to call z3
    #[clap(long)]
    z3_arg: Option<String>,
    /// Passes the custom argument to call cvc4
    #[clap(long)]
    cvc4_arg: Option<String>,
    /// Passes the custom argument to call yices2
    #[clap(long)]
    yices2_arg: Option<String>,
}

#[derive(Subcommand)]
enum Mode {
    /// Verify program and print result
    Verify {
        /// Up to which depth program is evaluated
        #[clap(default_value_t = 50)]
        depth: Depth,

        /// Report detailed information about proceedings of SEE
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

fn main(){

    let cli = Cli::parse();
    let exit = |(exit_code, result): (ExitCode, String)| {
        println!("{}", result);
        exit(exit_code as i32);
    };

    let solver_type = match (cli.z3_arg, cli.cvc4_arg, cli.yices2_arg) {
        (Some(arg), _, _) => SolverType::Z3(arg),
        (_, Some(arg), _) => SolverType::CVC4(arg),
        (_, _, Some(arg)) => SolverType::Yices2(arg),
        (_, _, _) => SolverType::Default,
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
                simplify: cli.simplifier || cli.infer_size,
                infer_size: cli.infer_size,
                prune_ratio: cli.prune_ratio,
                solver_type: solver_type,
                verbose: verbose,
            };
            exit(see::print_verification(&program, depth, &config))
        }
        Mode::Bench {
            start,
            end,
            interval,
        } => {
            let config = Config {
                simplify: cli.simplifier || cli.infer_size,
                infer_size: cli.infer_size,
                prune_ratio: cli.prune_ratio,
                solver_type: solver_type,
                verbose: false,
            };
            exit(see::bench(&program, start, end, interval, &config))
        }
    };
}
