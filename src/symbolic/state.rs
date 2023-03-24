use petgraph::stable_graph::NodeIndex;

use crate::shared::Depth;

use super::{memory::SymMemory, expression::PathConstraints, ref_values::ArrSizes};

pub struct PathState(pub SymMemory, pub PathConstraints, pub ArrSizes, pub Depth, pub NodeIndex);


pub enum Fork<Value, NewState> {
    No(Value),
    Yes(Value, NewState)
}