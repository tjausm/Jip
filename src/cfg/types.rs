use crate::{ast::*, shared::Scope};
use petgraph::graph::{Graph, NodeIndex};
use rustc_hash::FxHashMap;
use std::hash::Hash;

pub enum Node {
    // From this node we initialize our fresh parameters & the base scope
    EnteringMain(Parameters),
    Statement(Statement),
    /// classname, methodname and list of expressions we assign to parameters
    EnterProcedure(Routine),
    /// classname, methodname and variable name we assign retval to
    LeaveProcedure(Routine),
    End,
}

/// describes the actions we have to perform upon traversing edge
#[derive(Clone)]
pub enum Action {
    EnterScope {
        to: Scope,
    },
    AssignArgs {
        params: Parameters,
        args: Vec<Expression>,
    },
    /// copy ref of object method is called on to 'this'
    DeclareThis {
        obj: Lhs,
        class: Identifier,
    },
    /// Initialise object of class on heap and make lhs a reference to object
    InitObj {
        from_class: Identifier,
        to: Lhs,
    },
    /// lifts value of retval 1 scope higher
    LiftRetval,
    LeaveScope {
        from: Scope,
    },
    /// From main a `require` functions as an `assume`, from all 'deeper' scopes the `require` functions as an `assert`.
    /// The `ensure` statement always functions like an `assume`.
    /// (check specifications before leaving scope to ensure it knows it's leaving from main scope)
    CheckSpecifications {
        specifications: Specifications,
    },
}

pub type Actions = Vec<Action>;

pub type CFG = Graph<Node, Actions>;

/// Maps the collection type routine (covering all methods & constructors) to a tuple of start- and endnode for the subgraph of that routine
pub type FunEnv = FxHashMap<Routine, (NodeIndex, NodeIndex)>;

/// Abstraction type over methods & constructors
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Routine {
    Method {
        class: Identifier,
        method: Identifier,
    },
    Constructor {
        class: Identifier,
    },
}

/// Map objectname to the class of said object e.g. c.increment() can only be performed if we know where to find the increment function
pub struct TypeStack(Vec<FxHashMap<Identifier, Class>>);

impl Default for TypeStack {
    fn default() -> Self {
        TypeStack(vec![FxHashMap::default()])
    }
}

impl TypeStack {
    pub fn insert(&mut self, obj_name: Identifier, value: Class) -> () {
        match self.0.last_mut() {
            Some(env) => {
                env.insert(obj_name, value);
            }
            None => (),
        };
    }

    pub fn get(&self, id: &Identifier) -> Option<Class> {
        for frame in self.0.iter().rev() {
            match frame.get(id) {
                Some(class) => return Some(class.clone()),
                None => (),
            }
        }
        return None;
    }

    pub fn push(&mut self) {
        self.0.push(FxHashMap::default())
    }

    pub fn pop(&mut self) {
        self.0.pop();
    }
}

/// Given a generated subgraph, this struct denotes the last node & and the Edge we need to use to extend it
#[derive(Clone)]
pub struct Start {
    pub node: NodeIndex,
    pub actions: Actions,
}
