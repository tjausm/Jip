//! Share types and functions between modules
//!
//!

use crate::z3::{SymStack, SymHeap};

use uuid::Uuid;

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
pub fn custom_panic<'ctx>(msg: &str, sym_stack: Option<&SymStack<'ctx>>, sym_heap: Option<&SymHeap<'ctx>>) -> ! {
    panic!(
        "
    {}

    ENVIRONMENT
    
    Stack:
    {:?}

    Heap:
    {:?}
    ",
        msg, sym_stack, sym_heap
    )
}