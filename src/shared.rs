//! Share types and functions between modules
//!
//!
use std::fmt::Debug;
use std::panic;
use std::process::exit;
/// Indicates if program is valid, counterexample was found or other error occured
pub enum ExitCode {
    Valid = 0,
    CounterExample = 1,
    Error = 2,
}

pub type Depth = i32;

pub type Feasible = bool;

#[derive(Debug, Clone)]
pub enum Error {
    Verification(String),
    Other(String),
}

/// Either has a scope id or None if we are at the entry scope of the program
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: Option<i32>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SolverType {
    Z3(String),
    Yices2(String),
    CVC4(String),
    Z3Api,
    Default,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Config {
    pub simplify: bool,
    pub infer_size: i8,
    pub formula_caching: bool,
    pub prune_ratio: i8,
    pub solver_type: SolverType,
    pub verbose: bool,
}

#[derive(Clone)]
pub struct Diagnostics {
    pub paths_explored: i32,
    pub z3_calls: i32,
}


impl Default for Diagnostics {
    fn default() -> Self {
        return Diagnostics {
            paths_explored: 0,
            z3_calls: 0,
        };
    }
}


global_counter!(SCOPE_COUNTER, i32, 1);
 pub struct ScopeCounter;

 impl ScopeCounter {
     /// returns a unique number
     pub fn new() -> i32 {
         let i = SCOPE_COUNTER.get_cloned();
         SCOPE_COUNTER.inc();
         i
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
