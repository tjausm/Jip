//! Transforms object of the `Program` type to a Control Flow Graph (CFG)
//!
//! TODO: change cfg into mutable reference, instead of passing it around all the time
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use crate::shared::{
    get_class, get_from_env, get_method, get_methodcontent, insert_into_env, Error, Scope, print_short_id,
};
use petgraph::dot::Dot;
use petgraph::graph::{Graph, NodeIndex};
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::fmt;
use uuid::Uuid;

pub enum Node {
    EnteringMain(Parameters),
    Statement(Statement),
    /// classname, methodname and list of expressions we assign to parameters
    EnterMethod((Identifier, Identifier)),
    /// classname, methodname and variable name we assign retval to
    LeaveMethod((Identifier, Identifier)),
    End,
}

/// describes the actions we have to perform upon traversing edge
#[derive(Clone)]
pub enum Action {
    EnterScope {
        to: Scope,
    },
    // declare retval with correct type in current scope
    DeclareRetval {
        ty: Type
    },
    AssignArgs {
        params: Parameters,
        args: Vec<Expression>,
    },
    // assign reference in 'object' to this
    DeclareThis {object_id: Identifier},
    /// Initialise object of this class on heap and add reference of object to stack
    InitObj {
        class: Identifier,
        id: Identifier
    },
    /// lifts value of retval 1 scope higher
    LiftRetval,
    LeaveScope {
        from: Scope,
    },
}

type Edge = Vec<Action>;

pub type CFG = Graph<Node, Edge>;

/// Map identifier to clas, to know where to find invoked functions e.g. c.increment() can only be performed if we know where to find the increment function
type TypeEnv = Vec<FxHashMap<Identifier, Class>>;

/// Map tuple (class, method) to a tuple of start- and end-node for the subgraph of the method
type FunEnv = FxHashMap<(Identifier, Identifier), (NodeIndex, NodeIndex)>;

/// Given a generated subgraph, this struct denotes the last node & which edge comes from it should we want to extend it
#[derive(Clone)]
struct Start {
    node: NodeIndex,
    edge: Edge,
}

/// Transform node to unannotated start
fn to_start(node: NodeIndex) -> Start {
    return Start {
        node: node,
        edge: vec![],
    };
}

/// Generates cfg in vizualizable Dot format (visualizable at http://viz-js.com/)
pub fn generate_dot_cfg(program: Program) -> Result<String, Error> {
    match generate_cfg(program) {
        Ok((_, cfg)) => Ok(format!("{:?}", Dot::new(&cfg))),
        Err(why) => Err(why),
    }
}

// fuctions as the set-up for the recursive  stmts_to_cfg function
/// Returns cfg, and the start_node representing entry point of the program
pub fn generate_cfg(prog: Program) -> Result<(NodeIndex, CFG), Error> {
    //extract main.main method from program
    let main_method = get_method(&prog, "Main", "main")?;

    match main_method {
        Method::Static((Type::Void, id, args, body)) => {
            //initiate cfg
            let mut cfg: CFG = Graph::<Node, Vec<Action>>::new();
            let start = to_start(cfg.add_node(Node::EnteringMain(args.clone())));
            let end = cfg.add_node(Node::End);

            //initiate environments
            let mut ty_env: TypeEnv = vec![FxHashMap::default()];
            let mut f_env: FunEnv = FxHashMap::default();

            //generate the cfg
            let program_endings = stmts_to_cfg(
                &mut ty_env,
                &mut f_env,
                &prog,
                VecDeque::from(body.clone()),
                &mut cfg,
                vec![start.clone()],
                &(Scope {
                    id: None,
                    class: "Main".to_string(),
                    method: "main".to_string(),
                }),
                None,
            )?;

            //connect ending(s) of generated cfg to the 'end' node
            for p_end in program_endings {
                cfg.add_edge(p_end, end, vec![]);
            }

            return Ok((start.node, cfg));
        }
        _ => {
            return Err(Error::Semantics(
                "Couldn't find a 'static void main' method".to_string(),
            ))
        }
    }
}

fn get_constructor<'a>(prog: &'a Program, class_name: &str) -> Result<&'a Constructor, Error> {
    let class = get_class(prog, class_name)?;

    for m in class.1.iter() {
        match m {
            Member::Constructor(c) => return Ok(c),
            _ => continue,
        }
    }
    return Err(Error::Semantics(format!(
        "Class {} does not have a constructor",
        class_name
    )));
}

/// adds edges from all passed start nodes to first node it generates from stmts and adds edges from the last nodes it generates to the ending node if one is specified.
/// - **ty_env ->** map identifiers to classes, to know where to find invoked functions e.g. given object c, we can only perform c.increment() if we know the class of c
/// - **f_env ->**  map methods to the start and end of a functions subgraph
fn stmts_to_cfg<'a>(
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    mut stmts: VecDeque<Statement>,
    cfg: &mut CFG,
    starts: Vec<Start>,
    curr_scope: &Scope,
    scope_end: Option<NodeIndex>,
) -> Result<Vec<NodeIndex>, Error> {
    match stmts.pop_front() {
        Some(stmt) => match stmt {
            Statement::Block(stmts) => {
                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    VecDeque::from(*stmts),
                    cfg,
                    starts,
                    curr_scope,
                    scope_end,
                )
            }
            Statement::Ite((cond, s1, s2)) => {
                // add condition as assume and assume_not to the cfg
                let assume = Node::Statement(Statement::Assume(cond.clone()));
                let assume_not =
                    Node::Statement(Statement::Assume(Expression::Not(Box::new(cond))));
                let assume_start = to_start(cfg.add_node(assume));
                let assume_not_start = to_start(cfg.add_node(assume_not));
                //iterate over all starting nodes to lay edges
                for start in starts {
                    cfg.add_edge(start.node, assume_start.node, start.edge.clone());
                    cfg.add_edge(start.node, assume_not_start.node, start.edge);
                }

                // add the if and else branch to the cfg
                let if_ending = stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    VecDeque::from(vec![*s1]),
                    cfg,
                    vec![assume_start],
                    curr_scope,
                    scope_end,
                )?;

                let else_ending = stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    VecDeque::from(vec![*s2]),
                    cfg,
                    vec![assume_not_start],
                    curr_scope,
                    scope_end,
                )?;

                let all_endings: Vec<Start> = [if_ending, else_ending]
                    .concat()
                    .iter()
                    .map(|n| to_start(*n))
                    .collect();

                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    all_endings,
                    curr_scope,
                    scope_end,
                );
            }
            Statement::While((cond, body)) => {
                // add condition as assume and assume_not to the cfg
                let assume_node = cfg.add_node(Node::Statement(Statement::Assume(cond.clone())));
                let assume_not_node = cfg.add_node(Node::Statement(Statement::Assume(
                    Expression::Not(Box::new(cond)),
                )));

                // add edges from start node to assume and assume_not
                for start in starts {
                    cfg.add_edge(start.node, assume_node, start.edge.clone());
                    cfg.add_edge(start.node, assume_not_node, start.edge);
                }
                // calculate cfg for body of while and cfg for the remainder of the stmts
                let body_ending = stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    VecDeque::from(vec![*body]),
                    cfg,
                    vec![to_start(assume_node)],
                    curr_scope,
                    scope_end,
                )?;
                let end_remainder = stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![to_start(assume_not_node)],
                    curr_scope,
                    scope_end,
                )?;
                // add edges from end of while body to begin and edge from while body to rest of stmts
                for node in body_ending {
                    cfg.add_edge(node, assume_node, vec![]);
                    cfg.add_edge(node, assume_not_node, vec![]);
                }

                return Ok(end_remainder);
            }

            // generate
            Statement::Call(inv) => {
                let f_end = invocation_to_cfg(inv, ty_env, f_env, prog, cfg, starts)?;

                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![f_end],
                    curr_scope,
                    scope_end,
                );
            }

            Statement::Assignment((lhs, Rhs::Invocation(inv))) => {
                let f_end = invocation_to_cfg(inv, ty_env, f_env, prog, cfg, starts)?;

                let assign_retval = cfg.add_node(Node::Statement(Statement::Assignment((
                    lhs,
                    Rhs::Expression(Expression::Identifier("retval".to_string())),
                ))));

                cfg.add_edge(f_end.node, assign_retval, f_end.edge);

                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![to_start(assign_retval)],
                    curr_scope,
                    scope_end,
                );
            }
            // Statement::Assignment((lhs, Rhs::Newobject(id, args))) => {
            //     todo!(
            //         "initObj and make the lefthandside a reference
            //            add retval := this assignment upon leaving invocatio"
            //     );
            // }

            // for 'return x' we assign 'retval := x', add edge to scope_end and stop recursing
            Statement::Return(expr) => {
                let retval_assign = cfg.add_node(Node::Statement(Statement::Return(expr.clone())));
                for start in starts {
                    cfg.add_edge(start.node, retval_assign, start.edge);
                }
                match scope_end {
                    Some(scope_end) => {
                        cfg.add_edge(retval_assign, scope_end, vec![]);
                    }
                    None => {
                        return Err(Error::Semantics(format!(
                            " '{:?}' has no scope to return to.",
                            &Statement::Return(expr)
                        )))
                    }
                }
                return Ok(vec![]);
            }
            // split declareassign by prepending a declaration and assignment
            Statement::DeclareAssign((t, id, rhs)) => {
                stmts.push_front(Statement::Assignment((Lhs::Identifier(id.clone()), rhs)));
                stmts.push_front(Statement::Declaration((t, (&id).to_string())));

                return stmts_to_cfg(
                    ty_env, f_env, prog, stmts, cfg, starts, curr_scope, scope_end,
                );
            }

            // if no special case applies, add statement to cfg, let all start_nodes point to stmt, and make stmt start_node in next recursion step
            other => {
                // keep track of variable types, to know where to find nonstatic methods called on object
                match &other {
                    Statement::Declaration((Type::Classtype(class_name), id)) => {
                        let class = get_class(prog, class_name)?;
                        insert_into_env(ty_env, id.clone(), class.clone())
                    }
                    _ => (),
                }

                let stmt_node = cfg.add_node(Node::Statement(other));
                for start in starts {
                    cfg.add_edge(start.node, stmt_node, start.edge);
                }
                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![to_start(stmt_node)],
                    curr_scope,
                    scope_end,
                );
            }
        },
        //if stmt stack is empty we return ending node(s)
        None => {
            let start_nodes: Vec<NodeIndex> = starts.iter().map(|n| n.node).collect();
            return Ok(start_nodes);
        }
    }
}

/// function generalizes over static, non-static calls/invocations and constructor calls
/// 
fn invocation_to_cfg<'a>(
    (class_or_obj, method, args) : Invocation,
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    cfg: &mut CFG,
    starts: Vec<Start>,
) -> Result<Start, Error> {
    let class = get_class_name(ty_env, class_or_obj.clone());

    // collect information for the actions on the cfg edge
    let params = get_params(prog, &class, &method)?;
    
    let fun_scope = Scope {
        id: Some(Uuid::new_v4()),
        class: class.clone(),
        method: method.clone(),
    };
    let assign_args = Action::AssignArgs {
        params: params.clone(),
        args: args.clone(),
    };
    let enter_scope = Action::EnterScope {
        to: fun_scope.clone(),
    };

    // create subgraph for function if it does not exist yet
    let (f_start_node, f_end_node) =
        method_to_cfg(&class, &method, ty_env, f_env, prog, cfg, &fun_scope)?;

    for start in starts {
        cfg.add_edge(
            start.node,
            f_start_node,
            [vec![assign_args.clone(), enter_scope.clone()], start.edge].concat(),
        );
    }

    return Ok(Start {
        node: f_end_node,
        edge: vec![Action::LeaveScope {
            from: fun_scope.clone(),
        }],
    });
}

// returns (or builds) subgraph of a method/constructor
fn method_to_cfg<'a>(
    class: &String,
    method: &String,
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    cfg: &mut CFG,
    curr_scope: &Scope,
) -> Result<(NodeIndex, NodeIndex), Error> {
    // return function if it cfg is already generated
    match f_env.get(&(class.clone(), method.clone())) {
        Some(fun) => return Ok(*fun),
        _ => (),
    }

    // Check whether method exists and get body
    // if constructor get_constructorbody
    let (_, _, _, body) = get_methodcontent(prog, &class, &method)?;

    let enter_function = cfg.add_node(Node::EnterMethod((class.clone(), method.clone())));

    let leave_function = cfg.add_node(Node::LeaveMethod((class.clone(), method.clone())));

    //update environments
    ty_env.push(FxHashMap::default());
    f_env.insert(
        (class.clone(), method.clone()),
        (enter_function, leave_function),
    );

    //generate subgraph from function body starting from enter_function and ending at leave_function node
    let fun_endings = stmts_to_cfg(
        ty_env,
        f_env,
        prog,
        VecDeque::from(body.clone()),
        cfg,
        vec![to_start(enter_function)],
        curr_scope,
        Some(leave_function),
    )?;
    //leave ty_env scope after method body cfg is created
    ty_env.pop();
    //connect end of function to leave_function node
    for node in fun_endings {
        cfg.add_edge(node, leave_function, vec![]);
    }

    return Ok((enter_function, leave_function));
}

fn get_params<'a>(
    prog: &'a Program,
    class_name: &str,
    method_name: &str,
) -> Result<Parameters, Error> {
    let params: Parameters = get_methodcontent(prog, &class_name, &method_name)?
        .2
        .iter()
        .map(|(t,i)| (t.clone(), i.clone()))
        .collect();
    return Ok(params);
}

/// given a object- or classname returns the class_name
/// e.g. if we call o.f(), where the object o is of class O, calling get_class() will give us the objects class
fn get_class_name(ty_env: &TypeEnv, class_or_object: String) -> String {
    get_from_env(ty_env, &class_or_object)
        .map(|t| t.0)
        .unwrap_or(class_or_object)
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::EnteringMain(_) => write!(f, "Entering Main.main"),
            Node::Statement(stmt) => write!(f, "{:?}", stmt),
            Node::EnterMethod((object, method)) => {
                write!(f, "Entering {}.{}", object, method)
            }
            Node::LeaveMethod((object, method)) => {
                write!(f, "Leaving {}.{}", object, method)
            }
            Node::LeaveMethod((object, method)) => {
                write!(f, "Leaving {}.{}", object, method)
            }
            Node::EnterMethod((class, method)) => {
                write!(f, "Entering static {}.{}", class, method)
            }
            Node::LeaveMethod((class, method)) => {
                write!(f, "Leaving {}.{}", class, method)
            }
            Node::LeaveMethod((class, method)) => {
                write!(f, "Leaving {}.{}", class, method)
            }
            Node::End => {
                write!(f, "End")
            }
        }
    }
}

impl fmt::Debug for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Action::EnterScope {
                to: scope,
            } => {
                write!(f, "Entering scope {}", print_short_id(scope))
            }
            Action::AssignArgs { params, args } => {
                let ap_str = params
                    .iter()
                    .zip(args.iter())
                    .map(|((_, arg), param)| format!("{} = {:?}", arg, param))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "Assigning {}", ap_str)
            }
            Action::LeaveScope { from } => {
                write!(f, "Leaving scope {}", print_short_id(from))
            }
            Action::DeclareThis { object_id: this_object } => write!(f, "Entering non-static method"),
            Action::InitObj { class, id } => write!(f, "Init {} {} on heap", class, id),
           Action::LiftRetval  => write!(f, "Lifting retval"),
           Action::DeclareRetval { ty } => write!(f, "Declaring '{:?} retval'", ty),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use petgraph::algo::is_isomorphic;

    lalrpop_mod!(pub parser);

    fn parse_stmt(i: &str) -> Node {
        return Node::Statement(parser::StatementParser::new().parse(i).unwrap());
    }

    fn build_test(input: &str, correct_cfg: CFG) {
        let program_str = ["class Main { static void main () {", input, "} }"].join("");
        let program = parser::ProgramParser::new().parse(&program_str).unwrap();
        let (_, generated_cfg) = generate_cfg(program).unwrap();
        println!("Generated cfg: \n{:?}", Dot::new(&generated_cfg));
        println!("Correct cfg: \n{:?}", Dot::new(&correct_cfg));
        assert!(is_isomorphic(&generated_cfg, &correct_cfg));
    }

    #[test]
    fn straight() {
        let mut cfg = Graph::new();
        let a = cfg.add_node(Node::EnteringMain(vec![]));
        let b = cfg.add_node(parse_stmt("int x; "));
        let c = cfg.add_node(parse_stmt("arbitraryId := true;"));
        let d = cfg.add_node(Node::End);

        cfg.add_edge(a, b, vec![]);
        cfg.add_edge(b, c, vec![]);
        cfg.add_edge(c, d, vec![]);

        build_test("int x; arbitraryId := true;", cfg)
    }

    #[test]
    fn branch_and_block() {
        let mut cfg = Graph::new();
        let s = cfg.add_node(Node::EnteringMain(vec![]));
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(parse_stmt("int z;"));
        let f = cfg.add_node(Node::End);

        cfg.add_edge(s, a, vec![]);
        cfg.add_edge(a, c, vec![]);
        cfg.add_edge(c, e, vec![]);

        cfg.add_edge(s, b, vec![]);
        cfg.add_edge(b, d, vec![]);
        cfg.add_edge(d, e, vec![]);

        cfg.add_edge(e, f, vec![]);

        build_test("if (true) {int x;} else {int y; } int z;", cfg);
    }

    #[test]
    fn while_loop() {
        let mut cfg = Graph::new();
        let s = cfg.add_node(Node::EnteringMain(vec![]));
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(Node::End);

        cfg.add_edge(s, a, vec![]);
        cfg.add_edge(a, c, vec![]);
        cfg.add_edge(c, a, vec![]);
        cfg.add_edge(c, b, vec![]);

        cfg.add_edge(s, b, vec![]);
        cfg.add_edge(b, d, vec![]);

        cfg.add_edge(d, e, vec![]);

        build_test("while (true) int x; int y;", cfg);
    }
}
