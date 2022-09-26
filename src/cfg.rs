//! Transforms object of the `Program` type to a Control Flow Graph (CFG)
//!
//! TODO: change cfg into mutable reference, instead of passing it around all the time
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use crate::errors::Error;
use crate::shared::{get_from_env, insert_into_env};
use petgraph::dot::Dot;
use petgraph::graph::{Graph, NodeIndex};
use std::collections::{HashMap, VecDeque};
use std::fmt;

pub enum CfgNode {
    EnteringMain(Parameters),
    Statement(Statement),
    /// classname, methodname and list of expressions we assign to parameters
    EnterFunction((Identifier, Identifier, Arguments)),
    /// classname, methodname and variable name we assign retval to
    LeaveFunction((Identifier, Identifier, Option<Lhs>)),
    End,
}

impl fmt::Debug for CfgNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CfgNode::EnteringMain(_) => write!(f, "Entering Main.main"),
            CfgNode::Statement(stmt) => write!(f, "{:?}", stmt),
            CfgNode::EnterFunction((class, method, _)) => {
                write!(f, "Entering {}.{}", class, method)
            }
            CfgNode::LeaveFunction((class, method, None)) => write!(f, "Leaving {}.{}", class, method),
            CfgNode::LeaveFunction((class, method, Some(lhs))) => write!(f, "Leaving {}.{}\n{:?} := retval", class, method, lhs),
            CfgNode::End => write!(f, "End"),
        }
    }
}

pub type CFG = Graph<CfgNode, ()>;

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
    let main_class = get_class(&prog, "Main");
    let main_method = main_class.and_then(|class| get_method(&class, "main"));

    match main_method {
        Some(Method::Static((Type::Void, id, args, body))) => {
            //initiate cfg
            let mut cfg: CFG = Graph::<CfgNode, ()>::new();
            let start_node = cfg.add_node(CfgNode::EnteringMain(args.clone()));
            let end_cfg = cfg.add_node(CfgNode::End);

            //initiate environments
            let mut ty_env: TypeEnv = vec![HashMap::new()];
            let mut f_env: FunEnv = HashMap::new();

            let (_, cfg) = match stmts_to_cfg(
                &mut ty_env,
                &mut f_env,
                &prog,
                VecDeque::from(body.clone()),
                cfg,
                vec![start_node],
                end_cfg
            ) {
                Ok(res) => res,
                Err(why) => return Err(why),
            };
            return Ok((start_node, cfg));
        }
        _ => {
            return Err(Error::Semantics(
                "Couldn't find a 'Main class' and/or 'static void main' method in the 'Main' class"
                    .to_string(),
            ))
        }
    }
}

fn get_class<'a>(prog: &'a Program, class_name: &str) -> Option<&'a Class> {
    prog.iter().find(|(id, _)| id == class_name)
}

fn get_method<'a>(class: &'a Class, method_name: &str) -> Option<&'a Method> {
    for member in class.1.iter() {
        match member {
            Member::Method(method) => match method {
                Method::Nonstatic((_, id, _, _)) => {
                    if id == method_name {
                        return Some(method);
                    }
                }
                Method::Static((_, id, _, _)) => {
                    if id == method_name {
                        return Some(method);
                    }
                }
            },
            _ => (),
        }
    }
    return None;
}

fn get_methodcontent<'a>(
    prog: &'a Program,
    class_name: &str,
    method_name: &str,
) -> Option<&'a Methodcontent> {
    match get_class(&prog, &class_name) {
        Some(class) => match get_method(&class, &method_name) {
            Some(Method::Nonstatic(mc)) => return Some(mc),
            Some(Method::Static(mc)) => return Some(mc),
            None => return None,
        },
        None => return None,
    };
}

fn get_constructor<'a>(prog: &'a Program, class_name: &str) -> Option<&'a Constructor> {
    match get_class(&prog, &class_name) {
        Some((_, members)) => {
            for m in members.iter() {
                match m {
                    Member::Constructor(c) => return Some(c),
                    _ => continue,
                }
            }
        }
        None => return None,
    };
    return None;
}

/// Recursively unpacks Statement and returns start and end of cfg and cfg itself
fn stmt_to_cfg(
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    stmt: Statement,
    mut cfg: CFG,
    start_node: NodeIndex,
    end_cfg: NodeIndex
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
                end_cfg
            )
        }
        //TODO klopt dit?
        other => {
            let stmt_node = cfg.add_node(CfgNode::Statement(other));
            cfg.add_edge(start_node, stmt_node, ());
            return Ok((vec![stmt_node], cfg));
        }
    }
}

/// adds edges from all passed start nodes to first node it generates from stmts and adds edges from the last nodes it generates to the ending node if one is specified.
/// - **ty_env ->** map identifiers to classes, to know where to find invoked functions e.g. c.increment() can only be performed if we know where to find the increment function
/// - **f_env ->**  map methods to the start and end of a functions subgraph
fn stmts_to_cfg<'a>(
    ty_env: &mut TypeEnv,
    f_env: &mut FunEnv,
    prog: &Program,
    mut stmts: VecDeque<Statement>,
    mut cfg: CFG,
    start_nodes: Vec<NodeIndex>,
    scope_end: NodeIndex
) -> Result<(Vec<NodeIndex>, CFG), Error> {
    match stmts.pop_front() {
        Some(stmt) => match stmt {
            Statement::Ite((cond, s1, s2)) => {
                // add condition as assume and assume_not to the cfg
                let assume = CfgNode::Statement(Statement::Assume(cond.clone()));
                let assume_not =
                    CfgNode::Statement(Statement::Assume(Expression::Not(Box::new(cond))));
                let assume_node = cfg.add_node(assume);
                let assume_not_node = cfg.add_node(assume_not);
                //iterate over all starting nodes to lay edges
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, ());
                    cfg.add_edge(start_node, assume_not_node, ());
                }

                // add the if and else branch to the cfg
                let (if_ending, cfg) = match stmt_to_cfg(ty_env, f_env, prog, *s1, cfg, assume_node, scope_end)
                {
                    Ok(res) => res,
                    Err(why) => return Err(why),
                };
                let (else_ending, cfg) =
                    match stmt_to_cfg(ty_env, f_env, prog, *s2, cfg, assume_not_node, scope_end) {
                        Ok(res) => res,
                        Err(why) => return Err(why),
                    };
                return stmts_to_cfg(
                    ty_env,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    [if_ending, else_ending].concat(), scope_end
                );
            }
            Statement::While((cond, body)) => {
                // add condition as assume and assume_not to the cfg
                let assume_node = cfg.add_node(CfgNode::Statement(Statement::Assume(cond.clone())));
                let assume_not_node = cfg.add_node(CfgNode::Statement(Statement::Assume(
                    Expression::Not(Box::new(cond)),
                )));
                // add edges from start node to assume and assume_not
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, ());
                    cfg.add_edge(start_node, assume_not_node, ());
                }
                // calculate cfg for body of while and cfg for the remainder of the stmts
                let (body_ending, cfg) =
                    match stmt_to_cfg(ty_env, f_env, prog, *body, cfg, assume_node, scope_end) {
                        Ok(res) => res,
                        Err(why) => return Err(why),
                    };
                let (end_remainder, mut cfg) =
                    match stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![assume_not_node], scope_end) {
                        Ok(res) => res,
                        Err(why) => return Err(why),
                    };
                // add edges from end of while body to begin and edge from while body to rest of stmts
                for node in body_ending {
                    cfg.add_edge(node, assume_node, ());
                    cfg.add_edge(node, assume_not_node, ());
                }

                return Ok((end_remainder, cfg));
            }

            // generate
            Statement::Call((class, method, args)) => {
                let (f_start_node, f_end_node, mut cfg) = match f_env
                    .get(&(class.clone(), method.clone()))
                {
                    Some((start_node, end_node)) => (*start_node, *end_node, cfg),
                    None => {
                        match fun_to_cfg(&(class, method, args), None, ty_env, f_env, prog, cfg) {
                            Ok(res) => res,
                            Err(why) => return Err(why),
                        }
                    }
                };

                for node in start_nodes {
                    cfg.add_edge(node, f_start_node, ());
                }

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![f_end_node], scope_end);
            }

            // prepend function body and
            Statement::Assignment((lhs, Rhs::Invocation((class, method, args)))) => {
                let (f_start_node, f_end_node, mut cfg) =
                    match f_env.get(&(class.clone(), method.clone())) {
                        Some((start_node, end_node)) => (*start_node, *end_node, cfg),
                        None => match fun_to_cfg(
                            &(class, method, args),
                            Some(lhs),
                            ty_env,
                            f_env,
                            prog,
                            cfg,
                        ) {
                            Ok(res) => res,
                            Err(why) => return Err(why),
                        },
                    };

                for node in start_nodes {
                    cfg.add_edge(node, f_start_node, ());
                }

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![f_end_node], scope_end);
            }

            // replace assignment by this and prepend constructor call
            Statement::Assignment((lhs, Rhs::Newobject(class, arguments))) => {
                match get_constructor(prog, &class) {
                    Some((consName, args, body)) => {
                        // stmts.push_front(Statement::Call((class, consName, )));
                    }
                    None => {
                        return Err(Error::Semantics(format!(
                            "Class {} has no constructor",
                            &class
                        )))
                    }
                }

                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, start_nodes, scope_end);
            }

            // for 'return x' we assign 'retval := x' and stop recursing
            Statement::Return(expr) => {
                let retval_assign = cfg.add_node(CfgNode::Statement(Statement::Assignment((
                    Lhs::Identifier("retval".to_string()),
                    Rhs::Expression(expr),
                ))));
                for node in start_nodes {
                    cfg.add_edge(node, retval_assign, ());
                }
                cfg.add_edge(retval_assign, scope_end, ());
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
                        match get_class(prog, class_name) {
                            Some(class) => insert_into_env(ty_env, id.clone(), class.clone()),
                            None => {
                                return Err(Error::Semantics(format!(
                                    "Class {} does not exist",
                                    &class_name
                                )))
                            }
                        }
                    }
                    _ => (),
                }

                let stmt_node = cfg.add_node(CfgNode::Statement(other));
                for start_node in start_nodes {
                    cfg.add_edge(start_node, stmt_node, ());
                }
                return stmts_to_cfg(ty_env, f_env, prog, stmts, cfg, vec![stmt_node], scope_end);
            }
        },
        //if stmt stack is empty we connect to end_node and return
        None => {
            return Ok((start_nodes, cfg))},
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
    mut cfg: CFG
) -> Result<(NodeIndex, NodeIndex, CFG), Error> {
    let (class, method, args) = call;

    // Check whether method exists and it has enough args
    let (method_type, _, parameters, body) = match get_methodcontent(prog, &class, &method) {
        Some(ty_and_body) => ty_and_body,
        None => {
            return Err(Error::Semantics(format!(
                "Method {}.{} doesn't exist",
                class, method
            )))
        }
    };

    if parameters.len() != args.len() {
        return Err(Error::Semantics(format!(
            "A call of method {}.{} does not have correct number of arguments",
            class, method
        )));
    };

    let enter_function = cfg.add_node(CfgNode::EnterFunction((
        class.clone(),
        method.clone(),
        args.clone(),
    )));

    let leave_function = cfg.add_node(CfgNode::LeaveFunction((
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
    return match stmts_to_cfg(
        ty_env,
        f_env,
        prog,
        VecDeque::from(body.clone()),
        cfg,
        vec![enter_function],
        leave_function
    ) {
        Ok((fun_endings, mut cfg)) => {
            //leave ty_env scope after method body cfg is created
            ty_env.pop();
            //connect end of function to leave_function node
            for node in fun_endings {
                cfg.add_edge(node, leave_function, ());
            }
            
            Ok((enter_function, leave_function, cfg))
        }
        Err(why) => Err(why),
    };
}
#[cfg(test)]
mod tests {

    use super::*;
    use petgraph::algo::is_isomorphic;

    lalrpop_mod!(pub parser);

    fn parse_stmt(i: &str) -> CfgNode {
        return CfgNode::Statement(parser::StatementParser::new().parse(i).unwrap());
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
        let mut cfg = Graph::<CfgNode, ()>::new();
        let a = cfg.add_node(CfgNode::EnteringMain(vec![]));
        let b = cfg.add_node(parse_stmt("int x; "));
        let c = cfg.add_node(parse_stmt("arbitraryId := true;"));

        cfg.add_edge(a, b, ());
        cfg.add_edge(b, c, ());

        build_test("int x; arbitraryId := true;", cfg)
    }

    #[test]
    fn branch_and_block() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::EnteringMain(vec![]));
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(parse_stmt("int z;"));

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, e, ());

        cfg.add_edge(s, b, ());
        cfg.add_edge(b, d, ());
        cfg.add_edge(d, e, ());

        build_test("if (true) {int x;} else {int y; } int z;", cfg);
    }

    #[test]
    fn while_loop() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::EnteringMain(vec![]));
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, a, ());
        cfg.add_edge(c, b, ());

        cfg.add_edge(s, b, ());
        cfg.add_edge(b, d, ());

        build_test("while (true) int x; int y;", cfg);
    }
}
