//! Binary 'jip' is a cmd-line tool for performing static analysis on programs written in the OOX language.
//!

#[macro_use]
extern crate lalrpop_util;

#[macro_use]
extern crate global_counter;

use clap::{Parser, Subcommand};
use shared::{Config, Depth, ExitCode, SolverType, Rsmt2Arg};
use core::panic;
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

fn main() {
    let cli = Cli::parse();
    let exit = |(exit_code, result): (ExitCode, String)| {
        println!("{}", result);
        exit(exit_code as i32);
    };

    let solver_type = match (cli.z3_api, cli.z3_arg, cli.cvc4_arg, cli.yices2_arg) { 
        (true, _, _, _) => SolverType::Z3Api,
        (_, None, None, None) => panic!("No solver was specified"),
        (_, z3_arg, cvc4_arg, yices2_arg) => {
            let mut args = vec![];
            if let Some(arg) = z3_arg{
                args.push(Rsmt2Arg::Z3(arg));
            };
            if let Some(arg) = cvc4_arg{
                args.push(Rsmt2Arg::CVC4(arg));
            };
            if let Some(arg) = yices2_arg{
                args.push(Rsmt2Arg::Yices2(arg));
            };
            SolverType::Rsmt2(args)
        },
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
                expression_evaluation: cli.expression_evaluator || cli.infer_size > 0,
                infer_size: cli.infer_size,
                symbolic_array_size: cli.symbolic_array_size,
                formula_caching: cli.formula_caching,
                adaptive_pruning: cli.adaptive_pruning,
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
