//! Share types and functions between modules
//!
//!
use std::fmt::Debug;
use std::panic;
use std::process::exit;
use clap::ArgEnum;
use uuid::Uuid;

/// Indicates if program is valid, counterexample was found or other error occured
pub enum ExitCode {
    Valid = 0,
    CounterExample = 1,
    Error = 2,
}

#[derive(Debug, Clone)]
pub enum Error {
    Verification(String),
    Other(String),
}

/// Either has a scope id or None if we are at the entry scope of the program
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: Option<Uuid>,
}


#[derive(Copy, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, ArgEnum)]
pub enum SolverType {
    Z3,
    Yices2,
    CVC4
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Config {
    pub simplify: bool,
    pub infer_size: bool,
    pub prune_ratio: i8,
    pub solver_type: SolverType,
    pub verbose: bool
}

#[derive(Clone)]
pub struct Diagnostics {
    pub paths_explored: i32,
    pub z3_invocations: i32,
}

impl Default for Diagnostics {
    fn default() -> Self {
        return Diagnostics {
            paths_explored: 0,
            z3_invocations: 0,
        };
    }
}

/// Panics with passed message and passed datastructure (intended for SymMemory)
#[track_caller]
pub fn panic_with_diagnostics<D: Debug>(msg: &str, sym_memory: &D) -> ! {
    //get location of panic call
    let panic_loc = panic::Location::caller();

    //print diagnostics
    print!(
        "Program panicked at {} {}:{}

With error:
{}

{:?}",
        panic_loc.file(),
        panic_loc.line(),
        panic_loc.column(),
        msg,
        sym_memory
    );

    exit(ExitCode::Error as i32);
}
