//! Share types and functions between modules
//!
//!
use std::fmt::Debug;
use std::panic;
use std::process::exit;

use petgraph::stable_graph::NodeIndex;
use rustc_hash::FxHashSet;

use crate::cfg;
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
    pub expression_evaluation: bool,
    pub infer_size: i8,
    pub symbolic_array_size: Option<i64>,
    pub formula_caching: bool,
    pub adaptive_pruning: bool,
    pub solver_type: SolverType,
    pub verbose: bool,
}

#[derive(Clone)]
pub struct Diagnostics {
    pub reached_depth: i32,
    prune_p: Vec<u8>,
    pub paths_pruned: i32,
    pub paths_explored: i32,
    pub smt_calls: i32,
    pub cfg_coverage: CFGCoverage ,
}

#[derive(Clone)]
pub struct CFGCoverage {pub seen_nodes: FxHashSet<NodeIndex>,  pub total_nodes :usize}

impl CFGCoverage {
    pub fn new(total_nodes : usize) -> Self {
        CFGCoverage {seen_nodes: FxHashSet::default(), total_nodes}
    }

    pub fn seen(&mut self, node: NodeIndex){
        self.seen_nodes.insert(node);
    }

    /// return the coverage of the cfg as a percentage p : 0 <= p && p <= 100
    pub fn calculate(&self) -> f32 {
        let seen_usize = self.seen_nodes.len();
        let seen = seen_usize as f32;
        if seen == self.total_nodes as f32 {
            100.0
        } else if seen_usize == 0 {
            seen
        } else {
            seen / self.total_nodes as f32 * 100.0
        }
    }
}

impl Diagnostics {
    pub fn new(cfg_total_nodes: usize) -> Self {
        return Diagnostics {
            reached_depth: 0,
            prune_p: vec![],
            paths_pruned: 0,
            paths_explored: 0,
            smt_calls: 0,
            cfg_coverage: CFGCoverage::new(cfg_total_nodes),
        };
    }

    pub fn average_prune_p(&self) -> f64{
            let numbers : Vec<f64> = self.prune_p.clone().into_iter().map(|i| i.into()).collect();
            let sum : f64  = numbers.iter().sum();
            let count = numbers.len() as f64;
        
            if count > 0.0 {
                sum / count
            } else {
                0.0
            }
    }
    pub fn add_prune_p(&mut self, p: u8) {
        self.prune_p.push(p);
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
