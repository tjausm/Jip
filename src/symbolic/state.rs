use petgraph::stable_graph::NodeIndex;
use std::collections::VecDeque;

use crate::shared::Depth;

use super::{memory::SymMemory, expression::PathConstraints, ref_values::ArrSizes};

pub type PathState = ( SymMemory, PathConstraints, ArrSizes,  Depth,  NodeIndex);


pub enum Fork<Value> {
    No(Value),
    Yes(Value, PathState)
}

impl<Value> Fork<Value> {

    /// if there is a fork, push it to front of queue and return value
    pub fn straighten(self,  queue: &mut VecDeque<PathState>) -> Value{
        match self {
            Fork::No(v) => v,
            Fork::Yes(v, s) => {
                queue.push_front(s);
                v
            },
        }
    }

    pub fn map<F, A>(self, f: F) -> Fork<A>
        where F : Fn(Value) -> A
        {
            match self {
                Fork::No(v) => Fork::No(f(v)),
                Fork::Yes(v, s) => Fork::Yes(f(v), s),
            }
        } 
}