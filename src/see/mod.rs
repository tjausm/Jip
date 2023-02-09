//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!
//!
lalrpop_mod!(#[allow(dead_code)] pub parser); // synthesized by LALRPOP and pass allow(dead_code) to avoid warning of mods only used in unit tests

pub(crate) mod types;
mod utils;

use crate::see::types::*;
use crate::see::utils::*;

use crate::ast::*;
use crate::cfg::types::{Action, Node};
use crate::cfg::{generate_cfg, generate_dot_cfg};
use crate::shared::Config;
use crate::shared::ExitCode;
use crate::shared::{panic_with_diagnostics, Diagnostics, Error};
use crate::sym_model::PathConstraints;
use crate::sym_model::SymMemory;

use rayon::ThreadPool;

use std::collections::VecDeque;
use std::fs;
use std::num::NonZeroI32;
use std::num::NonZeroUsize;
use std::sync::mpsc;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;
use std::sync::Arc;
use std::thread;
use std::time::Instant;

const PROG_CORRECT: &'static str = "Program is correct";

pub fn bench(
    program: &str,
    start: Depth,
    end: Option<Depth>,
    step: i32,
    config: Config,
) -> (ExitCode, String) {
    let end = end.unwrap_or(start) + 1;
    let depths = (start..end).step_by(step.try_into().unwrap());
    println!("d        time");

    for d in depths {
        let now = Instant::now();

        // Code block to measure.
        {
            match print_verification(program, d, config.clone(), false) {
                (ExitCode::Error, e) => return (ExitCode::Error, e),
                _ => (),
            }
        }
        println!("{}       {:?}", d, now.elapsed());
    }
    return (ExitCode::Valid, "Benchmark done!".to_owned());
}

fn print_result(r: Result<Diagnostics, Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Other(why)) => (ExitCode::Error, format!("{}", why)),
        Err(Error::Verification(why)) => (ExitCode::CounterExample, format!("{}", why)),
        Ok(_) => (ExitCode::Valid, PROG_CORRECT.to_string()),
    }
}

pub fn load_program(file_name: String) -> Result<String, (ExitCode, String)> {
    match fs::read_to_string(file_name) {
        Err(why) => Err(print_result(Err(Error::Other(format!("{}", why))))),
        Ok(content) => Ok(content),
    }
}

fn parse_program(program: &str) -> Program {
    match parser::ProgramParser::new().parse(program) {
        Ok(prog) => prog,
        Err(err) => panic_with_diagnostics(&format!("{}", err), &()),
    }
}

pub fn print_cfg(program: &str) -> (ExitCode, String) {
    let program = parse_program(program);
    (ExitCode::Valid, generate_dot_cfg(program))
}

pub fn print_verification(
    program: &str,
    d: Depth,
    config: Config,
    verbose: bool,
) -> (ExitCode, String) {
    let print_diagnostics = |d: Result<Diagnostics, _>| match d {
        Ok(Diagnostics {
            paths_explored: paths,
            z3_invocations,
        }) => format!(
            "\nPaths checked    {}\nZ3 invocations   {}",
            paths, z3_invocations
        ),
        _ => "".to_string(),
    };
    let result = verify_program(program, d, config);
    let (ec, r) = print_result(result.clone());
    if verbose {
        return (ec, format!("{}{}", r, print_diagnostics(result)));
    }
    return (ec, r);
}

fn verify_program(prog_string: &str, d: Depth, config: Config) -> Result<Diagnostics, Error> {
    let prog = parse_program(prog_string);
    let (start_node, cfg) = generate_cfg(prog.clone());

    // init Arcs for usage in the rayon::scope
    let retval_id = &"retval".to_string();
    let this_id = &"retval".to_string();
    let retval_id = Arc::new(retval_id);
    let this_id = Arc::new(this_id);
    let arc_cfg = Arc::new(&cfg);
    let arc_config = Arc::new(&config);

    //init diagnostic info and error placeholder
    let mut diagnostics = Diagnostics::default();
    let mut maybe_err: Option<Error> = None;

    // max n threads for all n cores (or 4 if we don't know how many cores there are)
    let max_threads = // this fuckery is necesarry to transform NonZeroUsize to i32.....
        thread::available_parallelism()
        .map(|i| usize::from(i))
        .unwrap_or(4_usize);
    let mut curr_threads = 0;

    // do concurrent bfs search using the threadpool in a rayon::scope
    // this guarantees that cfg/config/retval_id/this_id outlive the spawned threads
    rayon::scope(|s| {

        // push initial PathState
        let mut q: VecDeque<PathState> = VecDeque::new();
        q.push_back(PathState {
            sym_memory: SymMemory::new(prog.clone()),
            pc: PathConstraints::default(),
            d,
            curr_node: start_node,
        });

        // build transmitter and receiver to communicate info back to main thread
        let (tx, rx): (Sender<Msg>, Receiver<Msg>) = mpsc::channel();
        while !(q.is_empty() && curr_threads == 0) {
            //println!("{} {}", q.is_empty(), curr_threads);

            //copy transmitter to pass to closure
            if let Some(path_state) = q.pop_front() {
                // clone necesary data to prevent drops
                let tx = tx.clone();
                let arc_cfg = Arc::clone(&arc_cfg);
                let arc_config = Arc::clone(&arc_config);
                let (retval_id, this_id) = (Arc::clone(&retval_id), Arc::clone(&this_id));

                curr_threads += 1;
                s.spawn(move |_| {
                    
                    explore_node(
                        tx,
                        arc_cfg,
                        arc_config,
                        (retval_id, this_id),
                        Diagnostics::default(),
                        path_state,
                    )
                });
            };

            match rx.recv() {
                Ok(Msg::FinishedPath(new_diagnostics)) => {
                    diagnostics = diagnostics + new_diagnostics;
                    curr_threads -= 1;
                    
                },
                Ok(Msg::NewState(state)) => q.push_back(state),
                Ok(Msg::Err(err)) => {
                    maybe_err = Some(err);
                    return;
                }
                Err(err) => println!("{}", err),
            }
        };
    });

    if let Some(err) = maybe_err {
        return Err(err);
    }
    return Ok(diagnostics);
}

/// Contains parser tests since parser mod is auto-generated
#[cfg(test)]
pub mod tests {

    lalrpop_mod!(pub parser);

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
        assert!(parser::StatementsParser::new()
            .parse("divisible := (i * k == x);")
            .is_ok());
        assert!(parser::StatementsParser::new().parse("int x := 2;").is_ok());
    }

    #[test]
    fn expressions() {
        assert!(parser::VerificationExpressionParser::new()
            .parse("2 < 1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("!true && false")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("-1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("y && z || a")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 == 2 != 3")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 + 2 - 3 / 4 % 5 * 6")
            .is_ok());
    }
    #[test]
    fn declaration() {
        assert!(parser::StatementsParser::new().parse("int x;").is_ok());
    }
    #[test]
    fn statements() {
        assert!(parser::StatementsParser::new()
            .parse("int x; x := 2; if(true)x := 1; else x := 2;")
            .is_ok());
    }
    #[test]
    fn block() {
        assert!(parser::StatementsParser::new()
            .parse("if(true){x := 1; bool z;} else {y := 2; x := 2;}")
            .is_ok());
    }
    #[test]
    fn assume() {
        assert!(parser::StatementsParser::new()
            .parse("assume true;")
            .is_ok());
    }
    #[test]
    fn assert() {
        assert!(parser::StatementsParser::new()
            .parse("assert true;")
            .is_ok());
    }
    #[test]
    fn while_loop() {
        assert!(parser::StatementsParser::new()
            .parse("while (1 < 2) x := y;")
            .is_ok());
    }
    #[test]
    fn program() {
        assert!(parser::ProgramParser::new()
            .parse("class Main {static void main(){int x := 2;}}")
            .is_ok());
    }

    #[test]
    fn faulty_input() {
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
        assert!(parser::StatementsParser::new()
            .parse("if (x := 1) x := 1; else x := 2;")
            .is_err());
    }
}
