//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!

use crate::ast::*;
use crate::cfg::{generate_cfg, generate_dot_cfg, Action, Node};
use crate::shared::{Error, Scope};
use crate::z3::{
    check_path, expression_to_bool, expression_to_int, fresh_bool, fresh_int, get_from_stack,
    insert_into_stack, Frame, PathConstraint, Stack, Variable,
};

lalrpop_mod!(pub parser);
// synthesized by LALRPOP
use petgraph::graph::{EdgeReference, NodeIndex};
use petgraph::stable_graph::DefaultIx;
use petgraph::visit::EdgeRef;
use uuid::Uuid;
use z3::{Config, Context};

use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::fs;

const PROG_CORRECT: &'static str = "Program is correct";

/// Indicates if program is valid, counterexample was found or other error occured
pub enum ExitCode {
    Valid = 0,
    CounterExample = 1,
    Error = 2,
}

/// Defines search depth for SEE
pub type Depth = i32;

#[derive(Clone)]
struct Diagnostics {
    paths: i32,
    z3Invocations: i32,
}

fn print_result(r: Result<Diagnostics, Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Syntax(why)) => (ExitCode::Error, format!("Syntax error: {}", why)),
        Err(Error::Semantics(why)) => (ExitCode::Error, format!("Semantics error: {}", why)),
        Err(Error::Other(why)) => (ExitCode::Error, format!("{}", why)),
        Err(Error::Verification(why)) => (ExitCode::CounterExample, format!("{}", why)),
        Ok(_) => (ExitCode::Valid, PROG_CORRECT.to_string()),
    }
}

pub fn load_program(program: String) -> Result<String, (ExitCode, String)> {
    match fs::read_to_string(program) {
        Err(why) => Err(print_result(Err(Error::Other(format!("{}", why))))),
        Ok(content) => Ok(content),
    }
}

fn parse_program(program: &str) -> Result<Program, Error> {
    match parser::ProgramParser::new().parse(program) {
        Err(parse_err) => return Err(Error::Syntax(format!("{}", parse_err))),
        Ok(program) => return Ok(program),
    }
}

pub fn print_cfg(program: &str) -> (ExitCode, String) {
    match parse_program(program) {
        Err(parse_err) => print_result(Err(parse_err)),
        Ok(stmts) => match generate_dot_cfg(stmts) {
            Ok(cfg) => (ExitCode::Valid, cfg),
            Err(sem_err) => print_result(Err(sem_err)),
        },
    }
}

pub fn print_verification(program: &str, d: Depth, verbose: bool) -> (ExitCode, String) {
    let print_diagnostics = |d: Result<Diagnostics, _>| match d {
        Ok(Diagnostics {
            paths,
            z3Invocations,
        }) => format!(
            "\nPaths checked    {}\nZ3 invocations   {}",
            paths, z3Invocations
        ),
        _ => "".to_string(),
    };
    let result = verify_program(program, d);
    let (ec, r) = print_result(result.clone());

    if (verbose) {
        return (ec, format!("{}{}", r, print_diagnostics(result)));
    }
    return (ec, r);
}

fn verify_program(prog_string: &str, d: Depth) -> Result<Diagnostics, Error> {
    //init diagnostic info
    let mut diagnostics = Diagnostics {
        paths: 0,
        z3Invocations: 0,
    };

    // init retval such that it outlives env
    let retval_id = &"retval".to_string();

    let prog = parse_program(prog_string)?;
    let (start_node, cfg) = generate_cfg(prog.clone())?;

    let z3_cfg = Config::new();
    let ctx = Context::new(&z3_cfg);

    //init our bfs through the cfg
    let mut q: VecDeque<(Stack, Vec<PathConstraint>, Depth, NodeIndex)> = VecDeque::new();
    let main = Frame {
        scope: Scope {
            id: None
        },
        env: FxHashMap::default(),
    };
    q.push_back((vec![main.clone()], vec![], d, start_node));

    // Assert -> build & verify z3 formula, return error if disproven
    // Assume -> build & verify z3 formula, stop evaluating pad if disproven
    // assignment -> evaluate rhs and update env
    // then we enque all connected nodes, till d=0 or we reach end of cfg
    while let Some((mut envs, mut pc, d, curr_node)) = q.pop_front() {
        if d == 0 {
            continue;
        }

        match &cfg[curr_node] {
            // add all parameters of main as free variables to env
            Node::EnteringMain(parameters) => {
                for p in parameters {
                    match p {
                        (Type::Int, id) => {
                            insert_into_stack(&mut envs, &id, fresh_int(&ctx, id.clone()))
                        }
                        (Type::Bool, id) => {
                            insert_into_stack(&mut envs, &id, fresh_bool(&ctx, id.clone()))
                        }
                        (ty, id) => {
                            return Err(Error::Semantics(format!(
                                "Can't call main with parameter {} of type {:?}",
                                id, ty
                            )))
                        }
                    }
                }
            }

            Node::Statement(stmt) => {
                match stmt {
                    Statement::Declaration((ty, id)) => match ty {
                        Type::Int => {
                            insert_into_stack(&mut envs, &id, fresh_int(&ctx, id.clone()));
                        }
                        Type::Bool => {
                            insert_into_stack(&mut envs, &id, fresh_bool(&ctx, id.clone()));
                        }
                        weird_type => {
                            return Err(Error::Semantics(format!(
                                "Declaring a var of type {:?} isn't possible",
                                weird_type
                            )))
                        }
                    },
                    Statement::Assume(expr) => {
                        let ast = expression_to_bool(&ctx, &envs, &expr)?;
                        pc.push(PathConstraint::Assume(ast));
                    }

                    // return err if is invalid else continue
                    Statement::Assert(expr) => match expression_to_bool(&ctx, &envs, &expr) {
                        Err(why) => return Err(why),
                        Ok(ast) => {
                            diagnostics.z3Invocations = diagnostics.z3Invocations + 1;

                            pc.push(PathConstraint::Assert(ast));
                            match check_path(&ctx, &pc) {
                                Err(why) => return Err(why),
                                Ok(_) => (),
                            }
                        }
                    },
                    Statement::Assignment((Lhs::Identifier(id), Rhs::Expression(expr))) => {
                        assign_expr(&ctx, &mut envs, &id, &expr)?;
                    }
                    Statement::Return(expr) => {
                        match envs.last() {
                            Some(anScope)
                                if anScope.scope.id == main.scope.id =>
                            {
                                continue
                            }
                            _ => (),
                        }
                        assign_expr(&ctx, &mut envs, retval_id, &expr)?;
                    }
                    _ => (),
                }
            }
            Node::End => diagnostics.paths = diagnostics.paths + 1,
            _ => (),
        }

        'q_nodes: for edge in cfg.edges(curr_node) {
            // clone new env to perform actions on
            let mut stack = envs.clone();

            // perform all actions in an edge and enque the result
            for action in edge.weight() {
                match action {
                    Action::EnterScope { to: scope } => stack.push(Frame {
                        scope: scope.clone(),
                        env: FxHashMap::default(),
                    }),
                    Action::DeclareRetval { ty } => {
                        // declare retval with correct type in new scope
                        match ty {
                            Type::Int => insert_into_stack(
                                &mut stack,
                                retval_id,
                                fresh_int(&ctx, "retval".to_string()),
                            ),
                            Type::Bool => insert_into_stack(
                                &mut stack,
                                retval_id,
                                fresh_bool(&ctx, "retval".to_string()),
                            ),
                            _ => (),
                        }
                    }
                    Action::AssignArgs { params, args } => {
                        let variables = params_to_vars(&ctx, &mut stack, params, &args)?;

                        for (id, var) in variables {
                            insert_into_stack(&mut stack, id, var);
                        }
                    }
                    Action::DeclareThis { class, ref_id: object } => {
                        todo!("Enter previous scope, retreive this_object and assign to this")
                    }
                    Action::InitObj { from: class, to: id } => {
                        todo!("Init new object")
                    }
                    // lift retval 1 scope up
                    Action::LiftRetval => {
                        match get_from_stack(&stack, retval_id) {
                            Some(retval) => {
                                let higher_frame = stack.len() - 2;
                                match stack.get_mut(higher_frame) {
                                    Some(frame) => {frame.env.insert(retval_id, retval);},
                                    None => {return Err(Error::Semantics("Can't return from main scope".to_owned()));}
                                }},
                            None => {return Err(Error::Semantics("Can't lift retval to a higher scope".to_owned()));},
                        };
                    }
                    // if we can leave over this edge pop scope otherwise dismiss path pe
                    Action::LeaveScope { from: to_scope } => match stack.last() {
                        Some(env) if env.scope == *to_scope => {stack.pop();},
                        _ => continue 'q_nodes,
                    },
                }
            }
            let next = edge.target();
            q.push_back((stack, pc.clone(), d - 1, next));
        }
    }
    return Ok(diagnostics);
}

/// Assigns an expression to an identifier in the passed environment
fn assign_expr<'ctx>(
    ctx: &'ctx Context,
    env: &mut Stack<'ctx>,
    id: &'ctx Identifier,
    expr: &'ctx Expression,
) -> Result<(), Error> {
    match get_from_stack(&env, id) {
        None => {
            return Err(Error::Semantics(format!(
                "Assignment {} := {:?} failed because variable {} is undeclared",
                id, expr, id
            )));
        }
        Some(Variable::Int(_)) => {
            let ast = expression_to_int(&ctx, &env, &expr)?;
            insert_into_stack(env, &id, Variable::Int(ast));
        }

        Some(Variable::Bool(_)) => {
            let ast = expression_to_bool(&ctx, &env, &expr)?;
            insert_into_stack(env, &id, Variable::Bool(ast));
        }
    };
    return Ok(());
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
fn params_to_vars<'ctx>(
    ctx: &'ctx Context,
    env: &mut Stack<'ctx>,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
) -> Result<Vec<(&'ctx String, Variable<'ctx>)>, Error> {
    let mut params_iter = params.iter();
    let mut args_iter = args.iter();
    let mut variables = vec![];

    loop {
        match (params_iter.next(), args_iter.next()) {
            (Some((Type::Int, id)), Some(expr)) => {
                let expr = expression_to_int(ctx, env, expr)?;
                variables.push((id, Variable::Int(expr)));
            }
            (Some((Type::Bool, id)), Some(expr)) => {
                let expr = expression_to_bool(ctx, env, expr)?;
                variables.push((id, Variable::Bool(expr)));
            }
            (Some((ty, _)), Some(_)) => {
                return Err(Error::Semantics(format!(
                    "Argument of type {:?} are not implemented",
                    ty
                )))
            }
            (Some((_, param)), None) => {
                return Err(Error::Semantics(format!(
                    "Missing an argument for parameter {:?} in a method call",
                    param
                )))
            }
            (None, Some(expr)) => {
                return Err(Error::Semantics(format!(
                    "Expression {:?} has no parameter it can be assigned to in a method call",
                    expr
                )))
            }
            (None, None) => break,
        }
    }
    return Ok(variables);
}

/// Contains parser tests since parser mod is auto-generated
#[cfg(test)]
mod tests {

    lalrpop_mod!(pub parser);

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
        assert!(parser::StatementsParser::new()
            .parse("divisible := (i * k == x);")
            .is_ok());
        assert!(parser::StatementsParser::new().parse("int x := 2;").is_ok());
    }

    #[test]
    fn expressions() {
        assert!(parser::VerificationExpressionParser::new()
            .parse("2 < 1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("!true && false")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("-1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("y && z || a")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 == 2 != 3")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 + 2 - 3 / 4 % 5 * 6")
            .is_ok());
    }
    #[test]
    fn declaration() {
        assert!(parser::StatementsParser::new().parse("int x;").is_ok());
    }
    #[test]
    fn statements() {
        assert!(parser::StatementsParser::new()
            .parse("int x; x := 2; if(true)x := 1; else x := 2;")
            .is_ok());
    }
    #[test]
    fn block() {
        assert!(parser::StatementsParser::new()
            .parse("if(true){x := 1; bool z;} else {y := 2; x := 2;}")
            .is_ok());
    }
    #[test]
    fn assume() {
        assert!(parser::StatementsParser::new()
            .parse("assume true;")
            .is_ok());
    }
    #[test]
    fn assert() {
        assert!(parser::StatementsParser::new()
            .parse("assert true;")
            .is_ok());
    }
    #[test]
    fn while_loop() {
        assert!(parser::StatementsParser::new()
            .parse("while (1 < 2) x := y;")
            .is_ok());
    }
    #[test]
    fn Program() {
        assert!(parser::ProgramParser::new()
            .parse("class Main {static void main(){int x := 2;}}")
            .is_ok());
    }

    #[test]
    fn faulty_input() {
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
        assert!(parser::StatementsParser::new()
            .parse("if (x := 1) x := 1; else x := 2;")
            .is_err());
    }
}
