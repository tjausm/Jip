//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!

use crate::ast::*;
use crate::cfg::{generate_cfg, generate_dot_cfg, CfgNode};
use crate::shared::{get_from_env, get_methodcontent, insert_into_env, Error};
use crate::z3::*;

lalrpop_mod!(pub parser); // synthesized by LALRPOP
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use z3::{Config, Context};

use std::collections::HashMap;
use std::collections::VecDeque;
use std::fs;
use std::rc::Rc;

const PROG_CORRECT: &str = "Program is correct";

/// 0 = validated program, 1 = validation error, 2 = all other errors
pub type ExitCode = i32;

/// Defines search depth for SEE
pub type Depth = i32;

fn print_result(r: Result<(), Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Syntax(why)) => (2, format!("Syntax error: {}", why)),
        Err(Error::Semantics(why)) => (2, format!("Semantics error: {}", why)),
        Err(Error::Other(why)) => (2, format!("{}", why)),
        Err(Error::Verification(why)) => (1, format!("{}", why)),
        Ok(_) => (0, PROG_CORRECT.to_string()),
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
            Ok(cfg) => (0, cfg),
            Err(sem_err) => print_result(Err(sem_err)),
        },
    }
}

pub fn print_verification(program: &str, d: Depth) -> (ExitCode, String) {
    return print_result(verify(program, d));
}

fn verify(prog_string: &str, d: Depth) -> Result<(), Error> {
    let prog = parse_program(prog_string)?;
    let (start_node, cfg) = generate_cfg(prog.clone())?;

    let z3_cfg = Config::new();
    let ctx = Context::new(&z3_cfg);

    //init our bfs through the cfg
    let mut q: VecDeque<(Environment, Vec<PathConstraint>, Depth, NodeIndex)> = VecDeque::new();
    q.push_back((vec![HashMap::new()], vec![], d, start_node));

    // Assert -> build & verify z3 formula, return error if disproven
    // Assume -> build & verify z3 formula, stop evaluating pad if disproven
    // assignment -> evaluate rhs and update env
    // then we enque all connected nodes, till d=0 or we reach end of cfg
    while let Some(triple) = q.pop_front() {
        match triple {
            (_, _, 0, _) => continue,
            (mut env, mut pc, d, node_index) => {
                match &cfg[node_index] {
                    // add all parameters of main as free variables to env
                    CfgNode::EnteringMain(parameters) => {
                        for p in parameters {
                            match p {
                                (Type::Int, id) => {
                                    insert_into_env(&mut env, &id, fresh_int(&ctx, id.clone()))
                                }
                                (Type::Bool, id) => {
                                    insert_into_env(&mut env, &id, fresh_bool(&ctx, id.clone()))
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

                    CfgNode::Statement(stmt) => {
                        match stmt {
                            Statement::Declaration((ty, id)) => match ty {
                                Type::Int => {
                                    insert_into_env(&mut env, &id, fresh_int(&ctx, id.clone()));
                                }
                                Type::Bool => {
                                    insert_into_env(&mut env, &id, fresh_bool(&ctx, id.clone()));
                                }
                                weird_type => {
                                    return Err(Error::Semantics(format!(
                                        "Declaring a var of type {:?} isn't possible",
                                        weird_type
                                    )))
                                }
                            },
                            //add assumes to path (TODO: when can we stop exploring a path?)
                            //or print path in path printing mode
                            Statement::Assume(expr) => {
                                match expression_to_bool(&ctx, &env, &expr) {
                                    Err(why) => return Err(why),
                                    Ok(ast) => pc.push(PathConstraint::Assume(ast)),
                                }
                            }
                            Statement::Assert(expr) => {
                                match expression_to_bool(&ctx, &env, &expr) {
                                    Err(why) => return Err(why),
                                    Ok(ast) => match solve_constraints(&ctx, &pc, &ast) {
                                        Err(why) => return Err(why),
                                        Ok(_) => pc.push(PathConstraint::Assert(ast)),
                                    },
                                }
                            }
                            Statement::Assignment((Lhs::Identifier(id), Rhs::Expression(expr))) => {
                                match get_from_env(&env, id) {
                                    None => {
                                        return Err(Error::Semantics(format!(
                                            "Variable {} is undeclared",
                                            id
                                        )))
                                    }
                                    Some(Variable::Int(_)) => {
                                        let ast = match expression_to_int(&ctx, &env, &expr) {
                                            Ok(ast) => ast,
                                            Err(why) => return Err(why),
                                        };
                                        insert_into_env(&mut env, &id, Variable::Int(ast));
                                    }

                                    Some(Variable::Bool(_)) => {
                                        match expression_to_bool(&ctx, &env, &expr) {
                                            Ok(ast) => {
                                                insert_into_env(&mut env, &id, Variable::Bool(ast))
                                            }
                                            Err(why) => return Err(why),
                                        };
                                    }

                                    Some(Variable::Object(..)) => todo!("Assigning objects not yet implemented"),
                                        
                                }
                            }
                            _ => (),
                        }
                    }
                    CfgNode::EnterFunction((class, method, args)) => {
                        // TODO: this should be different for static and non-static methods
                        let (ty, _, params, _) = get_methodcontent(&prog, class, method)?;
                        let variables =
                            params_to_vars(&ctx, &mut env, &params, &args, class, method)?;

                        env.push(HashMap::new());

                        // declare retval with correct type in new scope
                        match ty {
                            Type::Int => insert_into_env(&mut env, &"retval".to_string(), fresh_int(&ctx, "retval".to_string())),
                            Type::Bool => insert_into_env(&mut env, &"retval".to_string(), fresh_bool(&ctx, "retval".to_string())),
                            _ => (),
                        }

                        for (id, var) in variables {
                            insert_into_env(&mut env, id, var);
                        }
                    }
                    CfgNode::LeaveFunction((class, method, return_to)) => {
                        let retval = get_from_env(&env, &"retval".to_string());
                        env.pop();
                        match (return_to, retval) {
                            (Some(Lhs::Identifier(id)), Some(retval)) => (),
                            (Some(Lhs::Accessfield(..)), Some(retval)) => todo!("assigning objects not implemented"),
                            (None, None) => (),
                            (None, Some(_)) => return  Err(Error::Semantics(format!(" Can't assign return value of method {}.{} is invalid", class, method))),
                            (Some(lhs), None) => return  Err(Error::Semantics(format!(" Can't assign void method {}.{} to {:?}", class, method, lhs))),
                        }
                    }
                    _ => (),
                }
                //enqueue all connected nodes with the updated env and constraints
                for edge in cfg.edges(node_index) {
                    let next = edge.target();
                    q.push_back((env.clone(), pc.clone(), d - 1, next));
                }
            }
        }
    }
    return Ok(());
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
fn params_to_vars<'ctx>(
    ctx: &'ctx Context,
    env: &mut Environment<'ctx>,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
    class: &String,
    method: &String,
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
            (Some(_), None) => {
                return Err(Error::Semantics(format!(
                    "One or more arguments are missing in a call of method {}.{}",
                    class, method
                )))
            }
            (None, Some(_)) => {
                return Err(Error::Semantics(format!(
                    "One or more arguments too much in a call of method {}.{}",
                    class, method
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
