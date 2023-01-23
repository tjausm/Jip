//! Transforms object of the `Program` type to a Control Flow Graph (CFG)
//!
//! TODO: change cfg into mutable reference, instead of passing it around all the time

pub(crate) mod types;
mod utils;

use crate::ast::*;
use crate::cfg::types::*;
use crate::cfg::utils::{get_classname, get_routine_content};
use crate::shared::{panic_with_diagnostics, Scope};
use petgraph::dot::Dot;
use petgraph::graph::{Graph, NodeIndex};
use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use uuid::Uuid;

/// Transform node to unannotated start
fn to_start(node: NodeIndex) -> Start {
    return Start {
        node: node,
        edge: vec![],
    };
}

/// Generates cfg in vizualizable Dot format (visualizable at http://viz-js.com/)
pub fn generate_dot_cfg(program: Program) -> String {
    format!("{:?}", Dot::new(&generate_cfg(program).1))
}

// fuctions as the set-up for the recursive  stmts_to_cfg function
/// Returns cfg, and the start_node representing entry point of the program
pub fn generate_cfg(prog: Program) -> (NodeIndex, CFG) {
    //extract main.main method from program
    let main_method = prog.get_methodcontent( &"Main".to_string(), &"main".to_string());

    match main_method {
        (Type::Void, _, args, body) => {
            //initiate cfg
            let mut cfg: CFG = Graph::<Node, Vec<Action>>::new();
            let start = to_start(cfg.add_node(Node::EnteringMain(args.clone())));
            let end = cfg.add_node(Node::End);

            //initiate environments
            let mut ty_stack: TypeStack = TypeStack::default();
            let mut f_env: FunEnv = FxHashMap::default();

            //insert objects passed to main in TypeStack
            for (ty, obj_name) in args {
                if let Type::Classtype(class_name) = ty {
                    let class = prog.get_class( &class_name).clone();
                    ty_stack.insert(obj_name.clone(), class)
                }
            }

            //generate the cfg
            let program_endings = stmts_to_cfg(
                &mut ty_stack,
                &mut f_env,
                &prog,
                VecDeque::from(body.clone()),
                &mut cfg,
                vec![start.clone()],
                &(Scope { id: None }),
                None,
            );

            //connect ending(s) of generated cfg to the 'end' node
            for p_end in program_endings {
                cfg.add_edge(p_end, end, vec![]);
            }

            return (start.node, cfg);
        }
        _ => panic_with_diagnostics("Couldn't find a 'static void main' method", None),
    }
}

/// adds edges from all passed start nodes to first node it generates from stmts and adds edges from the last nodes it generates to the ending node if one is specified.
/// - **ty_env ->** map identifiers to classes, to know where to find invoked functions e.g. given object c, we can only perform c.increment() if we know the class of c
/// - **f_env ->**  map methods to the start and end of a functions subgraph
fn stmts_to_cfg<'a>(
    ty_stack: &mut TypeStack,
    f_env: &mut FunEnv,
    prog: &Program,
    mut stmts: VecDeque<Statement>,
    cfg: &mut CFG,
    starts: Vec<Start>,
    curr_scope: &Scope,
    scope_end: Option<NodeIndex>,
) -> Vec<NodeIndex> {
    match stmts.pop_front() {
        Some(stmt) => match stmt {
            Statement::Block(stmts) => {
                return stmts_to_cfg(
                    ty_stack,
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
                    ty_stack,
                    f_env,
                    prog,
                    VecDeque::from(vec![*s1]),
                    cfg,
                    vec![assume_start],
                    curr_scope,
                    scope_end,
                );

                let else_ending = stmts_to_cfg(
                    ty_stack,
                    f_env,
                    prog,
                    VecDeque::from(vec![*s2]),
                    cfg,
                    vec![assume_not_start],
                    curr_scope,
                    scope_end,
                );

                let all_endings: Vec<Start> = [if_ending, else_ending]
                    .concat()
                    .iter()
                    .map(|n| to_start(*n))
                    .collect();

                return stmts_to_cfg(
                    ty_stack,
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
                    ty_stack,
                    f_env,
                    prog,
                    VecDeque::from(vec![*body]),
                    cfg,
                    vec![to_start(assume_node)],
                    curr_scope,
                    scope_end,
                );
                let end_remainder = stmts_to_cfg(
                    ty_stack,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![to_start(assume_not_node)],
                    curr_scope,
                    scope_end,
                );
                // add edges from end of while body to begin and edge from while body to rest of stmts
                for node in body_ending {
                    cfg.add_edge(node, assume_node, vec![]);
                    cfg.add_edge(node, assume_not_node, vec![]);
                }

                return end_remainder;
            }

            // generate
            Statement::Call((class_or_obj, method, args)) => {
                // get class_name if call is not-static and keep track of staticness
                let class = get_classname(&class_or_obj, &ty_stack);
                let is_static = class.clone() == class_or_obj;

                // // if nonstatic we pass action declareThis
                let append_actions = if is_static {
                    vec![]
                } else {
                    vec![Action::DeclareThis {
                        class: class.clone(),
                        obj: Lhs::Identifier(class_or_obj),
                    }]
                };

                let routine = Routine::Method {
                    class: class.to_string(),
                    method: method,
                };

                let f_end = routine_to_cfg(
                    routine,
                    append_actions,
                    args,
                    ty_stack,
                    f_env,
                    prog,
                    cfg,
                    starts,
                );

                return stmts_to_cfg(
                    ty_stack,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![f_end],
                    curr_scope,
                    scope_end,
                );
            }

            Statement::Assignment((lhs, Rhs::Invocation((class_or_obj, method_name, args)))) => {
                // get class_name if call is not-static and keep track of staticness
                let class = get_classname(&class_or_obj, &ty_stack);
                let is_static = class.clone() == class_or_obj;

                let (ty, _, _, _) = prog.get_methodcontent(&class, &method_name);

                // declare retval and if non-static declarethis
                let append_actions = if is_static {
                    vec![Action::DeclareRetval { ty: ty.clone() }]
                } else {
                    vec![
                        Action::DeclareRetval { ty: ty.clone() },
                        Action::DeclareThis {
                            class: class.clone(),
                            obj: Lhs::Identifier(class_or_obj.clone()),
                        },
                    ]
                };

                let routine = Routine::Method {
                    class: class.to_string(),
                    method: method_name,
                };

                let f_end = routine_to_cfg(
                    routine,
                    append_actions,
                    args,
                    ty_stack,
                    f_env,
                    prog,
                    cfg,
                    starts,
                );

                let assign_retval = cfg.add_node(Node::Statement(Statement::Assignment((
                    lhs,
                    Rhs::Expression(Expression::Identifier("retval".to_string())),
                ))));

                cfg.add_edge(
                    f_end.node,
                    assign_retval,
                    [vec![Action::LiftRetval], f_end.edge].concat(),
                );

                return stmts_to_cfg(
                    ty_stack,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![to_start(assign_retval)],
                    curr_scope,
                    scope_end,
                );
            }
            Statement::Assignment((lhs, Rhs::Newobject(class_name, args))) => {
                let class = prog.get_class( &class_name);

                // we pass actions InitObj and declareThis
                let append_actions = vec![
                    Action::InitObj {
                        from: class.clone(),
                        to: lhs.clone(),
                    },
                    Action::DeclareThis {
                        class: class_name.clone(),
                        obj: lhs.clone(),
                    },
                ];

                let routine = Routine::Constructor {
                    class: class_name.to_string(),
                };

                let f_end = routine_to_cfg(
                    routine,
                    append_actions,
                    args,
                    ty_stack,
                    f_env,
                    prog,
                    cfg,
                    starts,
                );

                return stmts_to_cfg(
                    ty_stack,
                    f_env,
                    prog,
                    stmts,
                    cfg,
                    vec![f_end],
                    curr_scope,
                    scope_end,
                );
            }

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
                    None => panic_with_diagnostics(
                        &format!(
                            " '{:?}' has no scope to return to.",
                            &Statement::Return(expr)
                        ),
                        None,
                    ),
                }
                return vec![];
            }
            // split declareassign by prepending a declaration and assignment
            Statement::DeclareAssign((t, id, rhs)) => {
                stmts.push_front(Statement::Assignment((Lhs::Identifier(id.clone()), rhs)));
                stmts.push_front(Statement::Declaration((t, (&id).to_string())));

                return stmts_to_cfg(
                    ty_stack, f_env, prog, stmts, cfg, starts, curr_scope, scope_end,
                );
            }

            // if no special case applies, add statement to cfg, let all start_nodes point to stmt, and make stmt start_node in next recursion step
            other => {
                // keep track of variable types, to know where to find nonstatic methods called on object
                match &other {
                    Statement::Declaration((Type::Classtype(class_name), id)) => {
                        let class = prog.get_class( class_name);
                        ty_stack.insert(id.clone(), class.clone())
                    }
                    _ => (),
                }

                let stmt_node = cfg.add_node(Node::Statement(other));
                for start in starts {
                    cfg.add_edge(start.node, stmt_node, start.edge);
                }
                return stmts_to_cfg(
                    ty_stack,
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
            return start_nodes;
        }
    }
}

/// function generalizes over static, non-static calls/invocations and constructor calls
fn routine_to_cfg<'a>(
    routine: Routine,
    append_incoming: Edge,
    args: Vec<Expression>,
    ty_stack: &mut TypeStack,
    f_env: &mut FunEnv,
    prog: &Program,
    cfg: &mut CFG,
    starts: Vec<Start>,
) -> Start {
    // collect information for the actions on the cfg edge
    let (params, _) = get_routine_content(prog, &routine);

    // put new frame on typeStack and keep track of the params accompanying classes
    ty_stack.push();
    for (ty, id) in params {
        match ty {
            Type::Classtype(class_name) => {
                let class = prog.get_class( class_name).clone();
                ty_stack.insert(id.clone(), class)
            }
            _ => (),
        }
    }

    let fun_scope = Scope {
        id: Some(Uuid::new_v4()),
    };
    let enter_scope = Action::EnterScope {
        to: fun_scope.clone(),
    };
    let assign_args = Action::AssignArgs {
        params: params.clone(),
        args: args.clone(),
    };

    // create subgraph for function if it does not exist yet
    let (f_start_node, f_end_node) =
        routinebody_to_cfg(routine, ty_stack, f_env, prog, cfg, &fun_scope);

    // update incoming actions with actions passed from start struct, and appendable actions from append_incoming
    for start in starts {
        cfg.add_edge(
            start.node,
            f_start_node,
            [
                start.edge,
                vec![enter_scope.clone(), assign_args.clone()],
                append_incoming.clone(),
            ]
            .concat(),
        );
    }

    // pop typeStack frame
    ty_stack.pop();

    return Start {
        node: f_end_node,
        edge: vec![Action::LeaveScope {
            from: fun_scope.clone(),
        }],
    };
}

// returns (or builds) subgraph of a method/constructor
fn routinebody_to_cfg<'a>(
    routine: Routine,
    ty_env: &mut TypeStack,
    f_env: &mut FunEnv,
    prog: &Program,
    cfg: &mut CFG,
    curr_scope: &Scope,
) -> (NodeIndex, NodeIndex) {
    // return function if it cfg is already generated
    match f_env.get(&routine) {
        Some(fun) => return *fun,
        _ => (),
    }

    // Check whether method exists and get body
    // if constructor get_constructorbody
    let (_, body) = get_routine_content(prog, &routine);

    let enter_function = cfg.add_node(Node::EnterRoutine(routine.clone()));

    let leave_function = cfg.add_node(Node::LeaveRoutine(routine.clone()));

    //update environments
    ty_env.push();
    f_env.insert(routine, (enter_function, leave_function));

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
    );
    //leave ty_env scope after method body cfg is created
    ty_env.pop();
    //connect end of function to leave_function node
    for node in fun_endings {
        cfg.add_edge(node, leave_function, vec![]);
    }

    return (enter_function, leave_function);
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
        let (_, generated_cfg) = generate_cfg(program);
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
