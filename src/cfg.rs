//! Transforms object of the `Program` type to a Control Flow Graph (CFG)
//!
//! TODO: change cfg into mutable reference, instead of passing it around all the time
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use crate::shared::{
    get_class, get_from_env, get_method, get_methodcontent, insert_into_env, Error,
};
use petgraph::dot::Dot;
use petgraph::graph::{Graph, NodeIndex};
use std::collections::{HashMap, VecDeque};
use std::fmt;

pub enum Node {
    EnteringMain(Parameters),
    Statement(Statement),
    /// objectname, methodname and list of expressions we assign to parameters
    EnterMethod((Identifier, Identifier, Arguments)),
    /// objectname, methodname and variable name we assign retval to
    LeaveMethod((Identifier, Identifier, Option<Lhs>)),
    /// classname, methodname and list of expressions we assign to parameters
    EnterStaticMethod((Identifier, Identifier, Arguments)),
    /// classname, methodname and variable name we assign retval to
    LeaveStaticMethod((Identifier, Identifier, Option<Lhs>)),
    End,
}

pub enum Edge {
    /// methodname, list op parameters & arguments that function receives
    Call(Identifier, Vec<(Identifier, Expression)>),
    Other,
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::EnteringMain(_) => write!(f, "Entering Main.main"),
            Node::Statement(stmt) => write!(f, "{:?}", stmt),
            Node::EnterMethod((object, method, _)) => {
                write!(f, "Entering {}.{}", object, method)
            }
            Node::LeaveMethod((object, method, None)) => {
                write!(f, "Leaving {}.{}", object, method)
            }
            Node::LeaveMethod((object, method, Some(lhs))) => {
                write!(f, "Leaving {}.{}\n{:?} := retval", object, method, lhs)
            }
            Node::EnterStaticMethod((class, method, _)) => {
                write!(f, "Entering {}.{}", class, method)
            }
            Node::LeaveStaticMethod((class, method, None)) => {
                write!(f, "Leaving {}.{}", class, method)
            }
            Node::LeaveStaticMethod((class, method, Some(lhs))) => {
                write!(f, "Leaving {}.{}\n{:?} := retval", class, method, lhs)
            }
            Node::End => {
                write!(f, "End")
            }
        }
    }
}

impl fmt::Debug for Edge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Edge::Call(method, params_and_args) => {
                let ap_str  = params_and_args
                    .iter()
                    .map(|(arg, param)| format!("{} = {:?}", arg, param))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}({})", method, ap_str)
            },
            Edge::Other => write!(f, "")
        }
    }
}

pub type CFG = Graph<Node, Edge>;

/// Map identifier to clas, to know where to find invoked functions e.g. c.increment() can only be performed if we know where to find the increment function
type TypeEnv = Vec<HashMap<Identifier, Class>>;

/// Map tuple (class, method) to a tuple of start- and end-node for the subgraph of the method
type FunEnv = HashMap<(Identifier, Identifier), (NodeIndex, NodeIndex)>;

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
            let mut cfg: CFG = Graph::<Node, Edge>::new();
            let start = cfg.add_node(Node::EnteringMain(args.clone()));
            let end = cfg.add_node(Node::End);

            //initiate environments
            let mut ty_env: TypeEnv = vec![HashMap::new()];
            let mut f_env: FunEnv = HashMap::new();

            let (program_endings, mut cfg) = stmts_to_cfg(
                &mut ty_env,
                &mut f_env,
                &prog,
                VecDeque::from(body.clone()),
                cfg,
                vec![start],
                None,
            )?;

            for p_end in program_endings {
                cfg.add_edge(p_end, end, Edge::Other);
            }

            return Ok((start, cfg));
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

/// Recursively unpacks Statement and returns start and end of cfg and cfg itself
fn stmt_to_cfg(
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    stmt: Statement,
    mut cfg: CFG,
    start_node: NodeIndex,
    scope_end: Option<NodeIndex>,
) -> Result<(Vec<NodeIndex>, CFG), Error> {
    match stmt {
        Statement::Block(stmts) => {
            return stmts_to_cfg(
                ty_env,
                f_env,
                prog,
                VecDeque::from(*stmts),
                cfg,
                vec![start_node],
                scope_end,
            )
        }
        Statement::Return(expr) => {
            replace_return(&expr, &mut cfg, vec![start_node], scope_end)?;
            return Ok((vec![], cfg));
        }
        other => {
            let stmt_node = cfg.add_node(Node::Statement(other));
            cfg.add_edge(start_node, stmt_node, Edge::Other);
            return Ok((vec![stmt_node], cfg));
        }
    }
}

/// adds edges from all passed start nodes to first node it generates from stmts and adds edges from the last nodes it generates to the ending node if one is specified.
/// - **ty_env ->** map identifiers to classes, to know where to find invoked functions e.g. given object c, we can only perform c.increment() if we know the class of c
/// - **f_env ->**  map methods to the start and end of a functions subgraph
fn stmts_to_cfg<'a>(
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    mut stmts: VecDeque<Statement>,
    mut cfg: CFG,
    start_nodes: Vec<NodeIndex>,
    scope_end: Option<NodeIndex>,
) -> Result<(Vec<NodeIndex>, CFG), Error> {
    match stmts.pop_front() {
        Some(stmt) => match stmt {
            Statement::Ite((cond, s1, s2)) => {
                // add condition as assume and assume_not to the cfg
                let assume = Node::Statement(Statement::Assume(cond.clone()));
                let assume_not =
                    Node::Statement(Statement::Assume(Expression::Not(Box::new(cond))));
                let assume_node = cfg.add_node(assume);
                let assume_not_node = cfg.add_node(assume_not);
                //iterate over all starting nodes to lay edges
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, Edge::Other);
                    cfg.add_edge(start_node, assume_not_node, Edge::Other);
                }

                // add the if and else branch to the cfg
                let (if_ending, cfg) =
                    stmt_to_cfg(ty_env, f_env, prog, *s1, cfg, assume_node, scope_end)?;

                let (else_ending, cfg) =
                    stmt_to_cfg(ty_env, f_env, prog, *s2, cfg, assume_not_node, scope_end)?;

                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    [if_ending, else_ending].concat(),
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
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, Edge::Other);
                    cfg.add_edge(start_node, assume_not_node, Edge::Other);
                }
                // calculate cfg for body of while and cfg for the remainder of the stmts
                let (body_ending, cfg) =
                    stmt_to_cfg(ty_env, f_env, prog, *body, cfg, assume_node, scope_end)?;
                let (end_remainder, mut cfg) = stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![assume_not_node],
                    scope_end,
                )?;
                // add edges from end of while body to begin and edge from while body to rest of stmts
                for node in body_ending {
                    cfg.add_edge(node, assume_node, Edge::Other);
                    cfg.add_edge(node, assume_not_node, Edge::Other);
                }

                return Ok((end_remainder, cfg));
            }

            // generate
            Statement::Call((class_or_object, method, args)) => {
                
                // find classname if method is called on object
                let class = get_from_env(ty_env, class_or_object.clone())
                    .map(|t| t.0)
                    .unwrap_or(class_or_object);

                // collect information for CFG edge
                let params  = get_methodcontent(prog, &class, &method)?
                    .2
                    .iter()
                    .map(|e| e.1.clone());
                let copied_args = args
                    .iter()
                    .map(|a| a.clone());
                let params_and_args : Vec<(Identifier, Expression)> = params.zip(copied_args).collect();

                // create subgraph for function if it does not exist yet
                let (f_start_node, f_end_node, mut cfg) =
                    match f_env.get(&(class.clone(), method.clone())) {
                        Some((start_node, end_node)) => (*start_node, *end_node, cfg),
                        None => fun_to_cfg(&(class, method.clone(), args), None, ty_env, f_env, prog, cfg)?,
                    };

                for node in start_nodes {
                    cfg.add_edge(node, f_start_node, Edge::Call(method.clone(), params_and_args.clone()));
                }

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![f_end_node], scope_end);
            }

            // prepend function body and
            Statement::Assignment((lhs, Rhs::Invocation((class, method, args)))) => {
                // collect information for CFG edge
                let params  = get_methodcontent(prog, &class, &method)?
                    .2
                    .iter()
                    .map(|e| e.1.clone());
                let copied_args = args
                    .iter()
                    .map(|a| a.clone());
                let params_and_args : Vec<(Identifier, Expression)> = params.zip(copied_args).collect();
                
                
                let (f_start_node, f_end_node, mut cfg) =
                    match f_env.get(&(class.clone(), method.clone())) {
                        Some((start_node, end_node)) => (*start_node, *end_node, cfg),
                        None => {
                            fun_to_cfg(&(class, method.clone(), args), Some(lhs), ty_env, f_env, prog, cfg)?
                        }
                    };

                for node in start_nodes {
                    cfg.add_edge(node, f_start_node, Edge::Call(method.clone(), params_and_args.clone()));
                }

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![f_end_node], scope_end);
            }

            // replace assignment by this and prepend constructor call
            Statement::Assignment((lhs, Rhs::Newobject(class, arguments))) => {
                let constructor = get_constructor(prog, &class)?;
                // stmts.push_front(Statement::Call((class, consName, )));

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, start_nodes, scope_end);
            }

            // for 'return x' we assign 'retval := x' and stop recursing
            Statement::Return(expr) => {
                replace_return(&expr, &mut cfg, start_nodes, scope_end)?;
                return Ok((vec![], cfg));
            }
            // split declareassign by prepending a declaration and assignment
            Statement::DeclareAssign((t, id, rhs)) => {
                stmts.push_front(Statement::Assignment((Lhs::Identifier(id.clone()), rhs)));
                stmts.push_front(Statement::Declaration((t, (&id).to_string())));

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, start_nodes, scope_end);
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
                for start_node in start_nodes {
                    cfg.add_edge(start_node, stmt_node, Edge::Other);
                }
                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![stmt_node], scope_end);
            }
        },
        //if stmt stack is empty we return ending node(s)
        None => return Ok((start_nodes, cfg)),
    }
}

// add subgraph of given function to cfg
// insert
fn fun_to_cfg<'a>(
    call: &Invocation,
    assigns_to: Option<Lhs>,
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    mut cfg: CFG,
) -> Result<(NodeIndex, NodeIndex, CFG), Error> {
    let (class, method, args) = call;

    // Check whether method exists and it has enough args
    let (method_type, _, parameters, body) = get_methodcontent(prog, &class, &method)?;

    let enter_function = cfg.add_node(Node::EnterStaticMethod((
        class.clone(),
        method.clone(),
        args.clone(),
    )));

    let leave_function = cfg.add_node(Node::LeaveStaticMethod((
        class.clone(),
        method.clone(),
        assigns_to,
    )));

    //update environments
    ty_env.push(HashMap::new());
    f_env.insert(
        (class.clone(), method.clone()),
        (enter_function, leave_function),
    );

    //generate subgraph from function body starting from enter_function and ending at leave_function node
    let (fun_endings, mut cfg) = stmts_to_cfg(
        ty_env,
        f_env,
        prog,
        VecDeque::from(body.clone()),
        cfg,
        vec![enter_function],
        Some(leave_function),
    )?;
    //leave ty_env scope after method body cfg is created
    ty_env.pop();
    //connect end of function to leave_function node
    for node in fun_endings {
        cfg.add_edge(node, leave_function, Edge::Other);
    }

    return Ok((enter_function, leave_function, cfg));
}

/// Replaces 'return expr' by 'retval := expr' and edge between assignment and scope_end is added,
fn replace_return(
    expr: &Expression,
    cfg: &mut CFG,
    start_nodes: Vec<NodeIndex>,
    scope_end: Option<NodeIndex>,
) -> Result<(), Error> {
    let retval_assign = cfg.add_node(Node::Statement(Statement::Assignment((
        Lhs::Identifier("retval".to_string()),
        Rhs::Expression(expr.clone()),
    ))));
    for node in start_nodes {
        cfg.add_edge(node, retval_assign, Edge::Other);
    }
    match scope_end {
        Some(scope_end) => {
            cfg.add_edge(retval_assign, scope_end, Edge::Other);
            return Ok(());
        }
        None => {
            return Err(Error::Semantics(format!(
                " 'return {:?}' has no scope to return to.",
                &expr
            )))
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
        let mut cfg = Graph::<Node, Edge>::new();
        let a = cfg.add_node(Node::EnteringMain(vec![]));
        let b = cfg.add_node(parse_stmt("int x; "));
        let c = cfg.add_node(parse_stmt("arbitraryId := true;"));
        let d = cfg.add_node(Node::End);

        cfg.add_edge(a, b, Edge::Other);
        cfg.add_edge(b, c, Edge::Other);
        cfg.add_edge(c, d, Edge::Other);

        build_test("int x; arbitraryId := true;", cfg)
    }

    #[test]
    fn branch_and_block() {
        let mut cfg = Graph::<Node, Edge>::new();
        let s = cfg.add_node(Node::EnteringMain(vec![]));
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(parse_stmt("int z;"));
        let f = cfg.add_node(Node::End);

        cfg.add_edge(s, a, Edge::Other);
        cfg.add_edge(a, c, Edge::Other);
        cfg.add_edge(c, e, Edge::Other);

        cfg.add_edge(s, b, Edge::Other);
        cfg.add_edge(b, d, Edge::Other);
        cfg.add_edge(d, e, Edge::Other);

        cfg.add_edge(e, f, Edge::Other);

        build_test("if (true) {int x;} else {int y; } int z;", cfg);
    }

    #[test]
    fn while_loop() {
        let mut cfg = Graph::<Node, Edge>::new();
        let s = cfg.add_node(Node::EnteringMain(vec![]));
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(Node::End);

        cfg.add_edge(s, a, Edge::Other);
        cfg.add_edge(a, c, Edge::Other);
        cfg.add_edge(c, a, Edge::Other);
        cfg.add_edge(c, b, Edge::Other);

        cfg.add_edge(s, b, Edge::Other);
        cfg.add_edge(b, d, Edge::Other);

        cfg.add_edge(d, e, Edge::Other);

        build_test("while (true) int x; int y;", cfg);
    }
}
