//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!

lalrpop_mod!(pub parser);// synthesized by LALRPOP

pub(crate) mod types;
mod utils;

use crate::see::types::*;
use crate::see::utils::*;

use crate::ast::*;
use crate::cfg::{generate_cfg, generate_dot_cfg};
use crate::cfg::types::{Action, Node};
use crate::shared::ExitCode;
use crate::shared::{Error, panic_with_diagnostics};
use crate::z3::SymMemory;
use crate::z3::bindings::{check_path, expr_to_bool, expr_to_int, fresh_bool, fresh_int, PathConstraint};
use crate::z3::symModel::{ReferenceValue, SymExpression};



use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use uuid::Uuid;
use z3::{Config, Context};

use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::fs;

const PROG_CORRECT: &'static str = "Program is correct";

fn print_result(r: Result<Diagnostics, Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Other(why)) => (ExitCode::Error, format!("{}", why)),
        Err(Error::Verification(why)) => (ExitCode::CounterExample, format!("{}", why)),
        Ok(_) => (ExitCode::Valid, PROG_CORRECT.to_string()),
    }
}

pub fn load_program(file_name: String) -> Result<String, (ExitCode, String)> {
    match fs::read_to_string(file_name) {
        Err(why) => Err(print_result(Err(Error::Other(format!("{}", why))))),
        Ok(content) => Ok(content),
    }
}

fn parse_program(program: &str) -> Program {
    match parser::ProgramParser::new().parse(program) {
        Ok(prog) => prog,
        Err(err) => panic_with_diagnostics(&format!("{}", err), &()) 
    }
}

pub fn print_cfg(program: &str) -> (ExitCode, String) {
        let program = parse_program(program);
        (ExitCode::Valid, generate_dot_cfg(program))
}

pub fn print_verification(program: &str, d: Depth, verbose: bool) -> (ExitCode, String) {
    let print_diagnostics = |d: Result<Diagnostics, _>| match d {
        Ok(Diagnostics {
            paths,
            z3_invocations,
        }) => format!(
            "\nPaths checked    {}\nZ3 invocations   {}",
            paths, z3_invocations
        ),
        _ => "".to_string(),
    };
    let result = verify_program(program, d);
    let (ec, r) = print_result(result.clone());

    if verbose {
        return (ec, format!("{}{}", r, print_diagnostics(result)));
    }
    return (ec, r);
}

fn verify_program(prog_string: &str, d: Depth) -> Result<Diagnostics, Error> {
    //init diagnostic info
    let mut diagnostics = Diagnostics {
        paths: 0,
        z3_invocations: 0,
    };

    // init retval and this such that it outlives env
    let retval_id = &"retval".to_string();
    let this_id = &"this".to_string();

    let prog = parse_program(prog_string);
    let (start_node, cfg) = generate_cfg(prog.clone());

    let z3_cfg = Config::new();
    let ctx = Context::new(&z3_cfg);

    //init our bfs through the cfg
    let mut q: VecDeque<(SymMemory, Vec<PathConstraint>, Depth, NodeIndex)> =
        VecDeque::new();

    q.push_back((
        SymMemory::new(prog.clone(), &ctx),
        vec![],
        d,
        start_node,
    ));

    // Assert -> build & verify z3 formula, return error if disproven
    // Assume -> build & verify z3 formula, stop evaluating pad if disproven
    // assignment -> evaluate rhs and update env
    // then we enque all connected nodes, till d=0 or we reach end of cfg
    while let Some((mut sym_memory, mut pc, d, curr_node)) = q.pop_front() {
        if d == 0 {
            continue;
        }

        match &cfg[curr_node] {
            // add all parameters of main as free variables to env
            Node::EnteringMain(parameters) => {
                for p in parameters {
                    match p {
                        (Type::Int, id) => {
                            sym_memory.stack_insert(&id, fresh_int(&ctx, id.clone()))
                        }
                        (Type::Bool, id) => {
                            sym_memory.stack_insert(&id,  fresh_bool(&ctx, id.clone()))
                        },
                        (Type::ClassType(ty), id) => {
                            let r = Uuid::new_v4();
                            sym_memory.stack_insert(id, SymExpression::Ref((Type::ClassType(ty.clone()), r)));
                            sym_memory.heap_insert(r, ReferenceValue::UninitializedObj(prog.get_class(ty).clone()));
                        },
                        (ty, id) => panic_with_diagnostics(
                            &format!("Can't call main with parameter {} of type {:?}", id, ty),
                            &sym_memory
                        ),
                    }
                }
            }

            Node::Statement(stmt) => {
                match stmt {
                    Statement::Declaration((ty, id)) => match ty {
                        Type::Int => {
                            sym_memory.stack_insert(&id, fresh_int(&ctx, id.clone()));
                        }
                        Type::Bool => {
                            sym_memory.stack_insert(&id,  fresh_bool(&ctx, id.clone()));
                        },
                        ty => {
                            let r = Uuid::new_v4();
                            sym_memory.stack_insert(&id,  SymExpression::Ref((ty.clone(), r)))
                        },
                        
                    },
                    Statement::Assume(expr) => {
                        let ast = expr_to_bool(&ctx, &sym_memory, &expr);
                        pc.push(PathConstraint::Assume(ast));
                    }

                    // return err if is invalid else continue
                    Statement::Assert(expr) =>   {
                        let ast = expr_to_bool(&ctx, &sym_memory, &expr);

                        diagnostics.z3_invocations = diagnostics.z3_invocations + 1;

                        pc.push(PathConstraint::Assert(ast));
                        match check_path(&ctx, &pc) {
                            Err(why) => return Err(why),
                            Ok(_) => (),
                            
                        }
                    }
                    Statement::Assignment((lhs, rhs)) => {
                        // get lhs type
                        // parse expression variable
                        // assign to id in stack
                        lhs_from_rhs(&ctx, &mut sym_memory, lhs, rhs);
                    }
                    Statement::Return(expr) => {

                        // stop path if current scope `id == None`, indicating we are in main scope
                        if sym_memory.current_scope().id == None {continue};

                        // evaluate return expression with type of retval and add to stack
                        match sym_memory.stack_get(retval_id) {
                            Some(SymExpression::Int(_)) => {
                                let ast = expr_to_int(&ctx, &sym_memory, &expr);
                                sym_memory.stack_insert(
                                    retval_id,
                                    SymExpression::Int(ast),
                                );
                            }

                            Some(SymExpression::Bool(_)) => {
                                let ast = expr_to_bool(&ctx, &sym_memory, &expr);
                                sym_memory.stack_insert(
                                    retval_id,
                                    SymExpression::Bool(ast),
                                );
                            }
                            Some(SymExpression::Ref(_)) => {
                                match expr {
                                    Expression::Identifier(id) => match sym_memory.stack_get( id) {
                                        Some(SymExpression::Ref(r)) => sym_memory.stack_insert(retval_id, SymExpression::Ref(r)),
                                        Some(expr) => panic_with_diagnostics(&format!("Can't return '{:?}' as a referencevalue", expr), &sym_memory),
                                        None => panic_with_diagnostics(&format!("{} is undeclared", id), &sym_memory),
                                    },
                                    _ => panic_with_diagnostics(&format!("Can't return expression '{:?}'", expr), &sym_memory),
                                }
                            },
                            None => panic_with_diagnostics(&format!("retval is undeclared in expression 'return {:?}'", expr), &sym_memory),  
                        }
                    }
                    _ => (),
                }
            }
            Node::End => diagnostics.paths = diagnostics.paths + 1,
            _ => (),
        }

        'q_nodes: for edge in cfg.edges(curr_node) {
            // clone new stack and heap for each edge we travel to
            let mut sym_memory= sym_memory.clone();

            // perform all actions in an edge and enque the result
            for action in edge.weight() {
                match action {
                    Action::EnterScope { to: scope } => sym_memory.stack_push(scope.clone()),
                    Action::DeclareRetval { ty } => {
                        // declare retval with correct type in new scope
                        match ty {
                            Type::Int => sym_memory.stack_insert(
                                
                                retval_id,
                                fresh_int(&ctx, "retval".to_string()),
                            ),
                            Type::Bool => sym_memory.stack_insert(
                                
                                retval_id,
                                fresh_bool(&ctx, "retval".to_string()),
                            ),
                            Type::ClassType(ty) => sym_memory.stack_insert(
                                
                                retval_id,
                                SymExpression::Ref((Type::ClassType(ty.clone()), Uuid::nil())),
                            ),
                            Type::Void => panic!("Cannot declare retval of type void"),
                            Type::ArrayType(_) => todo!(),
                        }
                    }
                    Action::AssignArgs { params, args } => {
                        let variables =
                            params_to_vars(&ctx,  &mut sym_memory, &params, &args);

                        for (id, var) in variables {
                            sym_memory.stack_insert( id, var);
                        }
                    }
                    Action::DeclareThis { class, obj } => match obj {
                        Lhs::Identifier(id) => match sym_memory.stack_get( id) {
                            Some(SymExpression::Ref(r)) => sym_memory.stack_insert(
                                
                                this_id,
                                SymExpression::Ref(r),
                            ),
                            Some(_) => panic_with_diagnostics(
                                &format!("{} is not of type {}", id, class),
                                &sym_memory
                            ),
                            None => panic_with_diagnostics(
                                &format!("Variable {} is undeclared", id),
                                &sym_memory,
                            ),
                        },
                        Lhs::AccessField(_, _) => {
                            todo!("assigning objects to accesfields not implemented")
                        }
                        Lhs::AccessArray(_, _) => todo!(),
                    },
                    Action::InitObj {
                        from: class,
                        to: lhs,
                    } => {
                        // make an empty object
                        let obj = sym_memory.init_object(class);

                        // get reference r and map r to initialized object on heap
                        match lhs {
                            Lhs::Identifier(id) => {
                                match sym_memory.stack_get( id) {
                                    Some(SymExpression::Ref((_, r))) => {sym_memory.heap_insert(r, obj);},
                                    _ => panic_with_diagnostics(&format!("Can't initialize '{} {}' because no reference is declared on the stack", class.0, id), &sym_memory),
                                };
                            }
                            Lhs::AccessField(_, _) => todo!(),
                            Lhs::AccessArray(_, _) => todo!(),
                        };
                    }
                    // lift retval 1 scope up
                    Action::LiftRetval => {
                        match sym_memory.stack_get( retval_id) {
                            Some(retval) => sym_memory.stack_insert_below(retval_id, retval),
                            None => panic_with_diagnostics(
                                "Can't lift retval to a higher scope",
                                &sym_memory,
                            ),
                        };
                    }
                    // if we can leave over this edge pop scope otherwise dismiss path 
                    Action::LeaveScope { from: to_scope } => 
                    if *sym_memory.current_scope() == *to_scope {sym_memory.stack_pop()} else {continue 'q_nodes},
                }
            }
            let next = edge.target();
            q.push_back((sym_memory, pc.clone(), d - 1, next));
        }
    }
    return Ok(diagnostics);
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
    fn program() {
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
