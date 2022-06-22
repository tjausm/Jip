use crate::ast::{Expression, Program, Statement, Type, Rhs, Lhs};
use crate::cfg::{generate_cfg, generate_dot_cfg, CfgNode};
use crate::errors::Error;
use crate::paths::{generate_execution_paths, Depth};
use crate::z3::{print_formula, expression_to_bool, expression_to_int, Identifier, Variable};

lalrpop_mod!(pub parser); // synthesized by LALRPOP
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use z3::ast::{Bool, Int};
use z3::{Config, Context, SatResult, Solver};

use std::collections::HashMap;
use std::collections::VecDeque;
use std::fs;
use std::rc::Rc;

const PROG_CORRECT: &str = "Program is correct";

// 0 = validated program, 1 = validation error, 2 = all other errors
pub type ExitCode = i32;

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

pub fn print_cfg(program: &str) -> (ExitCode, String) {
    match parse_program(program) {
        Err(parse_err) => print_result(Err(parse_err)),
        Ok(stmts) => match generate_dot_cfg(stmts) {
            Ok(cfg) => (0, cfg),
            Err(sem_err) => print_result(Err(sem_err)),
        },
    }
}

pub fn print_formulas(program: &str, d: Depth) -> (ExitCode, String) {
    match parse_program(program) {
        Err(parse_err) => return print_result(Err(parse_err)),
        Ok(stmts) => match generate_cfg(stmts) {
            Ok((start_node, cfg)) => {
                for path in generate_execution_paths(start_node, cfg, d) {
                    match print_formula(path) {
                        Ok(formula) => println!("{}", formula),
                        Err(err) => return print_result(Err(err)),
                    }
                }
            }
            Err(sem_err) => return print_result(Err(sem_err)),
        },
    }
    //if all formulas are printed we end with success exitcode and empty msg
    return (0, "".to_string());
}

pub fn print_verification(program: &str, d: Depth) -> (ExitCode, String) {
    return print_result(verify(program, d));
}

fn parse_program(program: &str) -> Result<Program, Error> {
    match parser::ProgramParser::new().parse(program) {
        Err(parse_err) => return Err(Error::Syntax(format!("{}", parse_err))),
        Ok(program) => return Ok(program),
    }
}

fn verify(program: &str, d: Depth) -> Result<(), Error> {
    let (start_node, cfg) = match parse_program(program) {
        Err(parse_error) => return Err(parse_error),
        Ok(prog) => match generate_cfg(prog) {
            Ok(cfg) => cfg,
            Err(semantics_error) => return Err(semantics_error),
        },
    };

    //TODO: what happens if we use the same z3 ctx for all solving
    //init the 'accounting' z3 needs
    let z3_cfg = Config::new();
    let ctx = Context::new(&z3_cfg);

    let mut q: VecDeque<(HashMap<&Identifier, Variable>, Depth, NodeIndex)> = VecDeque::new();
    q.push_back((HashMap::new(), d, start_node));

    while let Some(triple) = q.pop_front() {
        match triple {
            (_, 0, _) => continue,
            (mut env, d, node_index) => {
                
                match &cfg[node_index] {
                    // enqueue all starting statements of program
                    CfgNode::Start => {
                        for edge in cfg.edges(node_index) {
                            let next = edge.target();
                            q.push_back((env.clone(), d, next));
                        }
                    }
                    // Assert -> build & verify z3 formula, return error if disproven
                    // Assume -> build & verify z3 formula, stop evaluating pad if disproven
                    // assignment -> evaluate rhs and update env
                    CfgNode::Statement(stmt) => {
                            match stmt {
                                Statement::Declaration((ty, id)) => match (env.contains_key(id), ty) {
                                    (true, _) => {
                                        return Err(Error::Semantics(format!(
                                            "Variable {} is declared twice",
                                            id
                                        )))
                                    }
                                    (_, Type::Int) => {
                                        env.insert(
                                            &id,
                                            Variable::Int(Int::new_const(&ctx, id.clone())),
                                        );
                                    }
                                    (_, Type::Bool) => {
                                        env.insert(
                                            &id,
                                            Variable::Bool(Bool::new_const(&ctx, id.clone())),
                                        );
                                    }
                                    (_, weird_type) => {
                                        return Err(Error::Semantics(format!(
                                            "Declaring a var of type {:?} isn't possible",
                                            weird_type
                                        )))
                                    }
                                },
                                //if assume is disproven we stop exploring
                                Statement::Assume(expr) => match verify_expression(&ctx, &env, &expr) {
                                    Err(_) => continue,
                                    _ => (),
                                },
                                //if assert is disproven we stop exploring
                                Statement::Assert(expr) => match verify_expression(&ctx, &env, &expr) {
                                    Err(why) => return Err(why),
                                    _ => (),
                                },
                                //if assert is disproven we stop exploring
                                Statement::Assignment((Lhs::Identifier(id), Rhs::Expr(expr))) => 
                                    match env.get(id) {
                                    None =>  
                                    return Err(Error::Semantics(format!(
                                        "Variable {} is undeclared",
                                        id
                                    ))),
                                    Some(Variable::Int(_)) => {
                                        let ast = match expression_to_int(&ctx, Rc::new(&env), &expr) {
                                            Ok(ast) => ast,
                                            Err(why) => return Err(why),
                                        };
                                        env.insert(id, Variable::Int(ast));
                                    }

                                    Some(Variable::Bool(_)) => {   
                                        match expression_to_bool(&ctx, Rc::new(&env), &expr) {
                                            Ok(ast) => env.insert(id, Variable::Bool(ast)),
                                            Err(why) => return Err(why),
                                        };
                                    }
                                },
                                _ => (),
                            }
                        
                        for edge in cfg.edges(node_index) {
                            let next = edge.target();
                            q.push_back((env.clone(), d - 1, next));
                        }
                    }
                    // if end node is reached path is pushed to result vec
                    CfgNode::End => return Ok(()),
                }
            }
        }
    }
    return Ok(());
}

fn verify_expression<'ctx>(
    ctx: &'ctx Context,
    env: &'ctx HashMap<&Identifier, Variable<'ctx>>,
    expr: &Expression,
) -> Result<(), Error> {
    panic!("not implemented")
}

// put parser test here since parser mod is auto-generated
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
