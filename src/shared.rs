//! Share types and functions between modules
//!
//!

use crate::z3::{SymStack, SymHeap};
use uuid::Uuid;
use std::panic;
use std::process::exit;

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

/// since main is unique we only have a scope.id outside of main
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: Option<Uuid>,
}

/// Panics with passed message and print diagnostic info
#[track_caller]
pub fn panic_with_diagnostics<'ctx>(msg: &str, sym_stack: Option<&SymStack<'ctx>>, sym_heap: Option<&SymHeap<'ctx>>) -> ! {
    //get location of panic call
    let panic_loc = panic::Location::caller();
    
    //print diagnostics
    print!(       
"Program panicked at {} {}:{}

With error:
{}

State of Sym-Stack:
{:?}

State of Sym-Heap:
{:?}",
        panic_loc.file(), panic_loc.line(), panic_loc.column(), msg, sym_stack, sym_heap
    );
    
    exit(ExitCode::Error as i32);
}