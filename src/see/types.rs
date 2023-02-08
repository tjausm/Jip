use crate::{sym_model::{SymMemory, PathConstraints}, shared::{Error, Diagnostics}};
use petgraph::graph::NodeIndex;
/// Defines search depth for SEE
pub type Depth = i32;

pub struct PathState<'a> {
    pub sym_memory: SymMemory<'a>, 
    pub pc: PathConstraints, 
    pub d: Depth, 
    pub curr_node: NodeIndex
}

pub enum Msg<'a>{
    Err(Error),
    NewState(PathState<'a>),
    FinishedPath(Diagnostics),
}