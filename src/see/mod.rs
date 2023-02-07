//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!
//!
lalrpop_mod!(#[allow(dead_code)] pub parser); // synthesized by LALRPOP and pass allow(dead_code) to avoid warning of mods only used in unit tests

pub(crate) mod types;
mod utils;

use crate::see::types::*;
use crate::see::utils::*;

use crate::ast::*;
use crate::cfg::types::{Action, Node};
use crate::cfg::{generate_cfg, generate_dot_cfg};
use crate::shared::Config;
use crate::shared::ExitCode;
use crate::shared::{panic_with_diagnostics, Diagnostics, Error};
use crate::sym_model::PathConstraints;
use crate::sym_model::{ReferenceValue, SymExpression, SymMemory, SymValue};
use crate::z3;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use uuid::Uuid;

use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::fs;
use std::time::Instant;

const PROG_CORRECT: &'static str = "Program is correct";

pub fn bench(
    program: &str,
    start: Depth,
    end: Option<Depth>,
    step: i32,
    config: Config,
) -> (ExitCode, String) {
    let end = end.unwrap_or(start) + 1;
    let depths = (start..end).step_by(step.try_into().unwrap());
    println!("d        time");

    for d in depths {
        let now = Instant::now();

        // Code block to measure.
        {
            match print_verification(program, d, config.clone(), false) {
                (ExitCode::Error, e) => return (ExitCode::Error, e),
                _ => (),
            }
        }
        println!("{}       {:?}", d, now.elapsed());
    }
    return (ExitCode::Valid, "Benchmark done!".to_owned());
}

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
        Err(err) => panic_with_diagnostics(&format!("{}", err), &()),
    }
}

pub fn print_cfg(program: &str) -> (ExitCode, String) {
    let program = parse_program(program);
    (ExitCode::Valid, generate_dot_cfg(program))
}

pub fn print_verification(
    program: &str,
    d: Depth,
    config: Config,
    verbose: bool,
) -> (ExitCode, String) {
    let print_diagnostics = |d: Result<Diagnostics, _>| match d {
        Ok(Diagnostics {
            paths_explored: paths,
            z3_invocations,
        }) => format!(
            "\nPaths checked    {}\nZ3 invocations   {}",
            paths, z3_invocations
        ),
        _ => "".to_string(),
    };
    let result = verify_program(program, d, config);
    let (ec, r) = print_result(result.clone());
    if verbose {
        return (ec, format!("{}{}", r, print_diagnostics(result)));
    }
    return (ec, r);
}

fn verify_program(prog_string: &str, d: Depth, config: Config) -> Result<Diagnostics, Error> {
    //init diagnostic info
    let mut diagnostics = Diagnostics::default();

    // init retval and this such that it outlives env
    let retval_id = &"retval".to_string();
    let this_id = &"this".to_string();

    let prog = parse_program(prog_string);
    let (start_node, cfg) = generate_cfg(prog.clone());

    //init our bfs through the cfg
    let mut q: VecDeque<(SymMemory, PathConstraints, Depth, NodeIndex)> = VecDeque::new();
    q.push_back((
        SymMemory::new(prog.clone()),
        PathConstraints::default(),
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
                        (Type::Int, id) => sym_memory.stack_insert_free_var(Type::Int, id),
                        (Type::Bool, id) => sym_memory.stack_insert_free_var(Type::Bool, id),
                        (Type::Classtype(ty), id) => {
                            let r = Uuid::new_v4();
                            sym_memory.stack_insert(
                                id,
                                SymExpression::Ref((Type::Classtype(ty.clone()), r)),
                            );
                            sym_memory.heap_insert(r, ReferenceValue::UninitializedObj(ty.clone()));
                        }
                        (ty, id) => panic_with_diagnostics(
                            &format!("Can't call main with parameter {} of type {:?}", id, ty),
                            &sym_memory,
                        ),
                    }
                }
            }

                Node::Statement(stmt) => {
                match stmt {
                    Statement::Declaration((ty, id)) => match ty {
                        Type::Int => {
                            sym_memory.stack_insert(&id, SymExpression::Int(SymValue::Uninitialized));
                        }
                        Type::Bool => {
                            sym_memory.stack_insert(&id,  SymExpression::Bool(SymValue::Uninitialized));
                        },
                        Type::Classtype(ty) => {
                            let r = Uuid::new_v4();
                            sym_memory.stack_insert(&id,  SymExpression::Ref((Type::Classtype(ty.clone()), r)))
                        },
                        Type::Void => panic!("Panic should never trigger, parser doesn't accept void type in declaration"),
                    },
                    Statement::Assume(assumption) => if !assume(config.simplify, &mut sym_memory, assumption, &mut pc) {continue},
                    Statement::Assert(assertion) =>   assert(config.simplify, &mut sym_memory, assertion, &mut pc, &mut diagnostics)?,
                    Statement::Assignment((lhs, rhs)) => {
                        lhs_from_rhs(&mut sym_memory, lhs, rhs);
                    }
                    Statement::Return(expr) => {

                        // stop path if current scope `id == None`, indicating we are in main scope
                        if sym_memory.get_scope(0).id == None {continue};

                        // evaluate return expression with type of retval and add to stack
                        match sym_memory.stack_get(retval_id) {
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
                            Some(SymExpression::Bool(_)) => {
                                sym_memory.stack_insert(
                                    retval_id,
                                    SymExpression::Int(SymValue::Expr(expr.clone())),
                                );
                            },
                            Some(SymExpression::Int(_)) => {sym_memory.stack_insert(retval_id,SymExpression::Int(SymValue::Expr(expr.clone())),);},
                            None => panic_with_diagnostics(&format!("retval is undeclared in expression 'return {:?}'", expr), &sym_memory),  
                        }
                    }
                    _ => (),
                }
            }
            Node::End => diagnostics.paths_explored = diagnostics.paths_explored + 1,
            _ => (),
        }

        'q_nodes: for edge in cfg.edges(curr_node) {
            // clone new stack and heap for each edge we travel to
            let mut sym_memory = sym_memory.clone();

            // perform all actions in an edge and enque the result
            for action in edge.weight() {
                match action {
                    Action::EnterScope { to: scope } => sym_memory.stack_push(scope.clone()),
                    Action::DeclareRetval { ty } => {
                        // declare retval with correct type in new scope
                        match ty {
                            Type::Int => sym_memory.stack_insert(
                                retval_id,
                                SymExpression::Int(SymValue::Uninitialized),
                            ),
                            Type::Bool => sym_memory.stack_insert(
                                retval_id,
                                SymExpression::Bool(SymValue::Uninitialized),
                            ),
                            Type::Classtype(ty) => sym_memory.stack_insert(
                                retval_id,
                                SymExpression::Ref((Type::Classtype(ty.clone()), Uuid::nil())),
                            ),
                            Type::Void => panic!("Cannot declare retval of type void"),
                        }
                    }
                    Action::AssignArgs { params, args } => {
                        let variables = params_to_vars(&mut sym_memory, &params, &args);

                        for (id, var) in variables {
                            sym_memory.stack_insert(id, var);
                        }
                    }
                    Action::DeclareThis { class, obj } => match obj {
                        Lhs::Identifier(id) => match sym_memory.stack_get(id) {
                            Some(SymExpression::Ref(r)) => {
                                sym_memory.stack_insert(this_id, SymExpression::Ref(r))
                            }
                            Some(_) => panic_with_diagnostics(
                                &format!("{} is not of type {}", id, class),
                                &sym_memory,
                            ),
                            None => panic_with_diagnostics(
                                &format!("Variable {} is undeclared", id),
                                &sym_memory,
                            ),
                        },
                        Lhs::Accessfield(_, _) => {
                            todo!("assigning objects to accesfields not implemented")
                        }
                    },
                    Action::InitObj {
                        from: (class, members),
                        to: lhs,
                    } => {
                        // make an empty object
                        let mut fields = FxHashMap::default();

                        // map all fields to symbolic values
                        for member in members {
                            match member {
                                Member::Field((ty, field)) => match ty {
                                    Type::Int => {
                                        fields.insert(
                                            field.clone(),
                                            (
                                                Type::Int,
                                                SymExpression::Int(SymValue::Uninitialized),
                                            ),
                                        );
                                    }
                                    Type::Bool => {
                                        (fields.insert(
                                            field.clone(),
                                            (
                                                Type::Bool,
                                                SymExpression::Bool(SymValue::Uninitialized),
                                            ),
                                        ),);
                                    }
                                    Type::Classtype(class) => {
                                        // insert uninitialized object to heap
                                        let (ty, r) =
                                            (Type::Classtype(class.to_string()), Uuid::new_v4());
                                        sym_memory.heap_insert(
                                            r,
                                            ReferenceValue::UninitializedObj(class.to_string()),
                                        );
                                        fields.insert(
                                            field.clone(),
                                            (
                                                Type::Classtype(class.to_string()),
                                                SymExpression::Ref((ty, r)),
                                            ),
                                        );
                                    }
                                    Type::Void => panic_with_diagnostics(
                                        &format!("Type of {}.{} can't be void", class, field),
                                        &sym_memory,
                                    ),
                                },
                                _ => (),
                            }
                        }

                        // get reference r and map r to initialized object on heap
                        match lhs {
                            Lhs::Identifier(id) => {
                                match sym_memory.stack_get( id) {
                                    Some(SymExpression::Ref((_, r))) => {sym_memory.heap_insert(r, ReferenceValue::Object((class.to_string(), fields)));},
                                    _ => panic_with_diagnostics(&format!("Can't initialize '{} {}' because no reference is declared on the stack", class, id), &sym_memory),
                                };
                            }
                            Lhs::Accessfield(_, _) => todo!(),
                        };
                    }
                    // lift retval 1 scope up
                    Action::LiftRetval => {
                        match sym_memory.stack_get(retval_id) {
                            Some(retval) => sym_memory.stack_insert_below(retval_id, retval),
                            None => panic_with_diagnostics(
                                "Can't lift retval to a higher scope",
                                &sym_memory,
                            ),
                        };
                    }
                    // if we can leave over this edge pop scope otherwise dismiss path
                    Action::LeaveScope { from: to_scope } => {
                        if *sym_memory.get_scope(0) == *to_scope {
                            sym_memory.stack_pop()
                        } else {
                            continue 'q_nodes;
                        }
                    }

                    // From main a `require` functions as an `assume`,
                    // from all 'deeper' scopes the require functions as an `assert`. The `ensure` statement always functions like an `assume`.
                    Action::CheckSpecifications { specifications } => {
                        let from_main_scope = sym_memory.get_scope(0).id == None
                            || sym_memory.get_scope(1).id == None;

                        for specification in specifications {
                            match (specification, from_main_scope) {
                                // if require is called outside main scope we assert
                                (Specification::Requires(assertion), false) => assert(config.simplify, &mut sym_memory, assertion, &mut pc, &mut diagnostics)?,
                                // otherwise process we assume
                                (spec, _) => {
                                    let assumption = match spec {
                                        Specification::Requires(expr) => expr,
                                        Specification::Ensures(expr) => expr,
                                    };
                                    if !assume(config.simplify, &mut sym_memory, assumption, &mut pc) {continue};
                                }
                            };
                        }
                    }
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
pub mod tests {

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
