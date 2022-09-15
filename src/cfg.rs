//! Transforms object of the `Program` type to a Control Flow Graph (CFG)
//! 
//! 
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use crate::errors::Error;
use petgraph::dot::Dot;
use petgraph::graph::{Graph, NodeIndex};
use std::fmt;
use std::iter::zip;

pub enum CfgNode {
    Start,
    Statement(Statement),
    EnterScope((Identifier, Identifier)),
    LeaveScope((Identifier, Identifier)),
    End,
}

impl fmt::Debug for CfgNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CfgNode::Start => write!(f, "Start"),
            CfgNode::Statement(stmt) => write!(f, "{:?}", stmt),
            CfgNode::EnterScope((class, method)) => write!(f, "Entering {}.{}", class, method),
            CfgNode::LeaveScope((class, method)) => write!(f, "Leaving {}.{}", class, method),
            CfgNode::End => write!(f, "End"),
        }
    }
}

pub type CFG = Graph<CfgNode, ()>;

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
            //generate declaration for all arguments passed to main function and append body
            let mut decl_and_body = args
                .iter()
                .map(|arg| Statement::Declaration(arg.clone()))
                .collect::<Statements>();
            decl_and_body.append(&mut body.clone());

            let mut cfg = Graph::<CfgNode, ()>::new();
            let start_node = cfg.add_node(CfgNode::Start);
            let end_node = cfg.add_node(CfgNode::End);

            let (_, _, cfg) =
                match stmts_to_cfg(&prog, decl_and_body, cfg, vec![start_node], Some(end_node)) {
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

/// Recursively unpacks Statement and returns start and end of cfg and cfg itself
fn stmt_to_cfg(
    prog: &Program,
    stmt: Statement,
    mut cfg: CFG,
    start_node: NodeIndex,
    end_node: Option<NodeIndex>,
) -> Result<(Vec<NodeIndex>, NodeIndex, CFG), Error> {
    match stmt {
        Statement::Block(stmts) => {
            return stmts_to_cfg(prog, *stmts, cfg, vec![start_node], end_node)
        }
        other => {
            let stmt_node = cfg.add_node(CfgNode::Statement(other));
            cfg.add_edge(start_node, stmt_node, ());
            match end_node {
                Some(end_node) => {
                    cfg.add_edge(stmt_node, end_node, ());
                    return Ok((vec![start_node], end_node, cfg));
                }
                None => return Ok((vec![start_node], stmt_node, cfg)),
            }
        }
    }
}

/// processes vec<Statement> in REVERSE order, 
/// adds edges from all passed start nodes to first node it generates from stmts
/// and adds edges from the last nodes it generates to the ending node if it is specified.
fn stmts_to_cfg(
    prog: &Program,
    mut stmts: Statements,
    mut cfg: CFG,
    start_nodes: Vec<NodeIndex>,
    ending_node: Option<NodeIndex>,
) -> Result<(Vec<NodeIndex>, NodeIndex, CFG), Error> {
    match stmts.len() > 0 {
        true => match stmts.remove(0) {
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
                let (_, if_ending, cfg) = match stmt_to_cfg(prog, *s1, cfg, assume_node, None) {
                    Ok(res) => res,
                    Err(why) => return Err(why),
                };
                let (_, else_ending, cfg) = match stmt_to_cfg(prog, *s2, cfg, assume_not_node, None)
                {
                    Ok(res) => res,
                    Err(why) => return Err(why),
                };
                return stmts_to_cfg(prog, stmts, cfg, vec![if_ending, else_ending], ending_node);
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
                let (_, body_ending, cfg) = match stmt_to_cfg(prog, *body, cfg, assume_node, None) {
                    Ok(res) => res,
                    Err(why) => return Err(why),
                };
                let (_, end_remainder, mut cfg) =
                    match stmts_to_cfg(prog, stmts, cfg, vec![assume_not_node], ending_node) {
                        Ok(res) => res,
                        Err(why) => return Err(why),
                    };
                // add edges from end of while body to begin and edge from while body to rest of stmts
                cfg.add_edge(body_ending, assume_node, ());
                cfg.add_edge(body_ending, assume_not_node, ());
                return Ok((vec![assume_node, assume_not_node], end_remainder, cfg));
            }

            //add declaration of new retval type
            //gen cfg of method body and link the ends up with existing cfg
            Statement::Call((class, method, args)) => {
                let (method_type, _, parameters, body) =
                    match get_methodcontent(prog, &class, &method) {
                        Some(ty_and_body) => ty_and_body,
                        None => {
                            return Err(Error::Semantics(format!(
                                "Method {}.{} doesn't exist",
                                class, method
                            )))
                        }
                    };

                let enter_scope =
                    cfg.add_node(CfgNode::EnterScope((class.clone(), method.clone())));

                let leave_scope =
                    cfg.add_node(CfgNode::LeaveScope((class.clone(), method.clone())));

                for start_node in start_nodes {
                    cfg.add_edge(start_node, enter_scope, ());
                }

                if (parameters.len() > args.len()) {
                    return Err(Error::Semantics(format!(
                        "A call of method {}.{} does not have enough arguments",
                        class, method
                    )));
                };
                if (parameters.len() < args.len()) {
                    return Err(Error::Semantics(format!(
                        "A call of method {}.{} has to many arguments",
                        class, method
                    )));
                };

                // assign the given arguments to the method parameters and prepend declarassigns to method body
                let mut declassigns_and_body = zip(parameters, args)
                    .map(|((ty, id), arg)| {
                        Statement::DeclareAssign((ty.clone(), id.clone(), Rhs::Expression(arg)))
                    })
                    .collect::<Statements>();
                declassigns_and_body.append(&mut body.clone());

                //generate cfg from body (assign and declare retval in case of non-void call)
                let (_, _, cfg) = match method_type {
                    Type::Void => match stmts_to_cfg(
                        prog,
                        declassigns_and_body,
                        cfg,
                        vec![enter_scope],
                        Some(leave_scope),
                    ) {
                        Ok(res) => res,
                        Err(why) => return Err(why),
                    },
                    ty => {
                        let declare_retval = cfg.add_node(CfgNode::Statement(
                            Statement::Declaration((method_type.clone(), "retval".to_string())),
                        ));
                        cfg.add_edge(enter_scope, declare_retval, ());
                        match stmts_to_cfg(
                            prog,
                            declassigns_and_body,
                            cfg,
                            vec![declare_retval],
                            Some(leave_scope),
                        ) {
                            Ok(res) => res,
                            Err(why) => return Err(why),
                        }
                    }
                };

                return stmts_to_cfg(prog, stmts, cfg, vec![leave_scope], ending_node);
            }
            // replace invocation by retval and prepend the function call
            Statement::Assignment((lhs, Rhs::Invocation((class, method, args)))) => {
                stmts.insert(
                    0,
                    Statement::Assignment((
                        lhs,
                        Rhs::Expression(Expression::Identifier("retval".to_string())),
                    )),
                );
                stmts.insert(0, Statement::Call((class, method, args)));

                return stmts_to_cfg(prog, stmts, cfg, start_nodes, ending_node);
            }
            Statement::Return(expr) => {
                stmts.insert(
                    0,
                    Statement::Assignment((
                        Lhs::Identifier("retval".to_string()),
                        Rhs::Expression(expr),
                    )),
                );
                return stmts_to_cfg(prog, stmts, cfg, start_nodes, ending_node);
            }
            // split declareassign by prepending a declaration and assignment
            Statement::DeclareAssign((t, id, rhs)) => {
                stmts.insert(0, Statement::Assignment((Lhs::Identifier(id.clone()), rhs)));
                stmts.insert(0, Statement::Declaration((t, (&id).to_string())));

                return stmts_to_cfg(prog, stmts, cfg, start_nodes, ending_node);
            }
            //add edge from start to stmt and recurse
            other => {
                let stmt_node = cfg.add_node(CfgNode::Statement(other));
                for start_node in start_nodes {
                    cfg.add_edge(start_node, stmt_node, ());
                }
                return stmts_to_cfg(prog, stmts, cfg, vec![stmt_node], ending_node);
            }
        },
        //if stmt stack is empty we connect to end_node and return
        false => match ending_node {
            Some(end_node) => {
                for start_node in &start_nodes {
                    cfg.add_edge(*start_node, end_node, ());
                }
                return Ok((start_nodes, end_node, cfg));
            }
            None => return Ok((start_nodes.clone(), start_nodes[0], cfg)),
        },
    }
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
        let a = cfg.add_node(CfgNode::Start);
        let b = cfg.add_node(parse_stmt("int x; "));
        let c = cfg.add_node(parse_stmt("arbitraryId := true;"));
        let d = cfg.add_node(CfgNode::End);

        cfg.add_edge(a, b, ());
        cfg.add_edge(b, c, ());
        cfg.add_edge(c, d, ());

        build_test("int x; arbitraryId := true;", cfg)
    }

    #[test]
    fn branch_and_block() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Start);
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(parse_stmt("int z;"));
        let f = cfg.add_node(CfgNode::End);

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, e, ());

        cfg.add_edge(s, b, ());
        cfg.add_edge(b, d, ());
        cfg.add_edge(d, e, ());

        cfg.add_edge(e, f, ());

        build_test("if (true) {int x;} else {int y; } int z;", cfg);
    }

    #[test]
    fn while_loop() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Start);
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(CfgNode::End);

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, a, ());
        cfg.add_edge(c, b, ());

        cfg.add_edge(s, b, ());
        cfg.add_edge(b, d, ());
        cfg.add_edge(d, e, ());

        build_test("while (true) int x; int y;", cfg);
    }
}
