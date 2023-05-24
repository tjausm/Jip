//! Binary 'jip' is a cmd-line tool for performing static analysis on programs written in the OOX language.
//!

#[macro_use]
extern crate lalrpop_util;

#[macro_use]
extern crate global_counter;

use clap::{Parser, Subcommand};
use shared::{Config, Depth, ExitCode, SolverType, Timeout};
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

    /// Turns on the expression evaluator
    #[clap(short, long)]
    expression_evaluator: bool,

    /// The maximum number of iterations that the interval inference algorithm performs
    #[clap(short, long, default_value_t = 0)]
    infer_size: i8,

    /// The maximum size of a symbolic array, if none is set the size is symbolic
    #[clap(short, long)]
    symbolic_array_size: Option<i64>,

    /// Turns on formula caching
    #[clap(short, long)]
    formula_caching: bool,

    /// Turns on adaptive pruning
    #[clap(short, long)]
    adaptive_pruning: bool,

    /// Passes the custom argument to call z3
    #[clap(long)]
    z3_arg: Option<String>,
    /// Passes the custom argument to call cvc4
    #[clap(long)]
    cvc4_arg: Option<String>,
    /// Passes the custom argument to call yices2
    #[clap(long)]
    yices2_arg: Option<String>,
    /// Use z3's c++ api
    #[clap(long)]
    z3_api: bool,
}

#[derive(Subcommand)]
enum Mode {
    /// Verify program and print result
    Verify {
        /// The maximum verification depth
        #[clap(short)]
        depth: Option<Depth>,

        /// The maximum run-time in seconds
        #[clap(short)]
        timeout: Option<Timeout>,

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

fn main() {
    let cli = Cli::parse();
    let exit = |(exit_code, result): (ExitCode, String)| {
        println!("{}", result);
        exit(exit_code as i32);
    };

    let solver_type = match (cli.z3_arg, cli.cvc4_arg, cli.yices2_arg, cli.z3_api) {
        (Some(arg), _, _, _) => SolverType::Z3(arg),
        (_, Some(arg), _, _) => SolverType::CVC4(arg),
        (_, _, Some(arg), _) => SolverType::Yices2(arg),
        (_, _, _, true) => SolverType::Z3Api,
        (_, _, _, _) => SolverType::Default,
    };

    // attempt to load program, and exit with exitcode and error if fails
    let program = match see::load_program(cli.path) {
        Err(why) => exit(why),
        Ok(program) => program,
    };

    // if program loaded execute function corresponding to cmd and exit with the result
    match cli.mode {
        Mode::PrintCFG => exit(see::print_cfg(&program)),
        Mode::Verify {
            depth,
            timeout,
            verbose,
        } => {
            let config = Config {
                expression_evaluation: cli.expression_evaluator || cli.infer_size > 0,
                infer_size: cli.infer_size,
                symbolic_array_size: cli.symbolic_array_size,
                formula_caching: cli.formula_caching,
                adaptive_pruning: cli.adaptive_pruning,
                solver_type: solver_type,
                verbose: verbose,
            };
            exit(see::print_verification(&program, depth, timeout, &config))
        }
        Mode::Bench {
            start,
            end,
            interval,
        } => {
            let config = Config {
                expression_evaluation: cli.expression_evaluator || cli.infer_size > 0,
                infer_size: cli.infer_size,
                symbolic_array_size: cli.symbolic_array_size,
                formula_caching: cli.formula_caching,
                adaptive_pruning: cli.adaptive_pruning,
                solver_type: solver_type,
                verbose: false,
            };
            exit(see::bench(&program, start, end, interval, &config))
        }
    };
}
