//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!
//!

lalrpop_mod!(#[allow(dead_code)] pub parser); // synthesized by LALRPOP and pass allow(dead_code) to avoid warning of mods only used in unit tests

pub(crate) mod types;
mod utils;

use crate::ast::*;
use crate::cfg::types::{Action, Node};
use crate::cfg::{generate_cfg, generate_dot_cfg};
use crate::see::types::*;
use crate::see::utils::*;
use crate::shared::Config;
use crate::shared::ExitCode;
use crate::shared::{panic_with_diagnostics, Diagnostics, Error};
use crate::smt_solver::Solver;
use crate::symbolic::memory::SymMemory;
use crate::symbolic::model::{PathConstraints, ReferenceValue, SymExpression, SymType};
use colored::Colorize;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashMap;
use uuid::Uuid;

use std::collections::VecDeque;
use std::fs;
use std::time::Instant;

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
            match verify_program(program, d,  config.clone(), false) {
                Ok(_) => (),
                r => return print_result(r),
            }
        }
        println!("{}       {:?}", d, now.elapsed());
    }
    return (ExitCode::Valid, "Benchmark done!".to_owned());
}

fn print_result(r: Result<Diagnostics, Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Other(why)) => (
            ExitCode::Error,
            format!("{} {}", "Error:".red().bold(), why),
        ),
        Err(Error::Verification(why)) => (
            ExitCode::CounterExample,
            format!("{} {}", "Counter-example:".red().bold(), why),
        ),
        Ok(d) => {
            let mut msg = "".to_string();
            if d.paths_explored == 0 {
                msg.push_str(&format!("{} Jip has not finished exploring any paths. Is your search depth high enough? And are you sure the program terminates?\n", "Warning: ".yellow().bold()))
            }
            msg.push_str(&format!(
                "{}\nPaths checked    {}\nZ3 invocations   {}",
                "Program is correct".green().bold(),
                d.paths_explored,
                d.z3_invocations
            ));
            (ExitCode::Valid, msg)
        }
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
    let result = verify_program(program, d, config, verbose);
    print_result(result.clone())
}

/// prints the verbose debug info
fn print_debug(node: &Node, sym_memory: &SymMemory, pc: &PathConstraints) {
    let print_node = format!("{:?}", node);
    let print_pc = format!("Path constraints -> {:?}", pc.combine_over_true());
    let print_sym_memory = format!("{:?}", sym_memory);

    let dump_state = match node {
        Node::Statement(Statement::Assert(_)) => true,
        Node::Statement(Statement::Assignment((_, Rhs::AccessArray(_, _)))) => true,
        _ => false,
    };
    if dump_state {
        println!("{}\n\n{}\n\n{}", print_node, print_pc, print_sym_memory)
    } else {
        println!("{}", print_node);
    }
}

fn verify_program(
    prog_string: &str,
    d: Depth,
    config: Config,
    verbose: bool,
) -> Result<Diagnostics, Error> {
    let prune_coefficient = f64::from(config.prune_ratio) / f64::from(i8::MAX);
    let prune_depth = (f64::from(d) - f64::from(d) * prune_coefficient) as i32;

    //init diagnostic info
    let mut diagnostics = Diagnostics::default();

    //init solver
    let mut solver = Solver::new(config.solver_type);

    // init retval and this such that it outlives env
    let retval_id = &"retval".to_string();
    let this_id = &"this".to_string();

    let prog = parse_program(prog_string);
    let (start_node, cfg) = generate_cfg(prog.clone());

    //init our bfs through the cfg
    let mut q: VecDeque<(SymMemory, PathConstraints, Depth, NodeIndex)> = VecDeque::new();
    q.push_back((SymMemory::new(), PathConstraints::default(), d, start_node));

    // Assert -> build & verify z3 formula, return error if disproven
    // Assume -> build & verify z3 formula, stop evaluating pad if disproven
    // assignment -> evaluate rhs and update env
    // then we enque all connected nodes, till d=0 or we reach end of cfg
    while let Some((mut sym_memory, mut pc, d, curr_node)) = q.pop_front() {
        if d == 0 {
            continue;
        }

        if verbose {
            print_debug(&cfg[curr_node], &sym_memory, &pc);
        };

        match &cfg[curr_node] {
            // add all parameters of main as free variables to env
            Node::EnteringMain(parameters) => {
                for parameter in parameters {
                    match parameter {
                        (Type::Int, id) => sym_memory.stack_insert_free_var(Type::Int, id),
                        (Type::Bool, id) => sym_memory.stack_insert_free_var(Type::Bool, id),
                        (Type::ArrayType(ty), id) => {
                            let arr = sym_memory.init_array(
                                *ty.clone(),
                                SymExpression::FreeVariable(SymType::Int, format!("|#{}|", id)),
                            );
                            let r = sym_memory.heap_insert(None, arr);
                            sym_memory
                                .stack_insert(id, SymExpression::Reference(parameter.0.clone(), r));
                        }
                        (Type::ClassType(ty), id) => {
                            let class = prog.get_class(ty);
                            let r = sym_memory
                                .heap_insert(None, ReferenceValue::UninitializedObj(class.clone()));
                            sym_memory
                                .stack_insert(id, SymExpression::Reference(parameter.0.clone(), r));
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
                            sym_memory.stack_insert(&id, SymExpression::Uninitialized);
                        }
                        Type::Bool => {
                            sym_memory.stack_insert(&id, SymExpression::Uninitialized);
                        }
                        ty => {
                            let r = Uuid::new_v4();
                            sym_memory.stack_insert(&id, SymExpression::Reference(ty.clone(), r))
                        }
                    },
                    Statement::Assume(assumption) => {
                        if !assume(
                            config.simplify,
                            d > prune_depth,
                            &mut sym_memory,
                            &mut solver,
                            assumption,
                            &mut pc,
                            &mut diagnostics,
                        ) {
                            continue;
                        }
                    }
                    Statement::Assert(assertion) => assert(
                        config.simplify,
                        &mut sym_memory,
                        &mut solver,
                        assertion,
                        &mut pc,
                        &mut diagnostics,
                    )?,
                    Statement::Assignment((lhs, rhs)) => {
                        lhs_from_rhs(&mut solver, &pc, config.simplify, &mut sym_memory, lhs, rhs)?;
                    }
                    Statement::Return(expr) => {
                        // stop path if current scope `id == None`, indicating we are in main scope
                        if sym_memory.get_scope(0).id == None {
                            continue;
                        };

                        // add return value to stack
                        sym_memory
                            .stack_insert(retval_id, SymExpression::new(&FxHashMap::default(), &sym_memory, expr.clone()));
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
                    Action::AssignArgs { params, args } => {
                        let variables = params_to_vars(&mut sym_memory, &params, &args);

                        for (id, var) in variables {
                            sym_memory.stack_insert(id, var);
                        }
                    }
                    Action::DeclareThis { class, obj } => match obj {
                        Lhs::Identifier(id) => match sym_memory.stack_get(id) {
                            Some(SymExpression::Reference(Type::ClassType(lhs_class), r)) if class == &lhs_class => sym_memory.stack_insert(this_id, SymExpression::Reference(Type::ClassType(lhs_class), r)),
                        
                            Some(_) => panic_with_diagnostics(
                                &format!("{} is not of type {}", id, class),
                                &sym_memory,
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
                        // get reference r, init object, and insert into heap under reference
                        match lhs {
                            Lhs::Identifier(id) => {
                                match sym_memory.stack_get( id) {
                                    Some(SymExpression::Reference(_, r)) => {
                                        // make an empty object
                                        let obj = sym_memory.init_object(r, class.clone());
                                        // insert into heap
                                        sym_memory.heap_insert(Some(r), obj);},
                                    _ => panic_with_diagnostics(&format!("Can't initialize '{} {}' because no reference is declared on the stack", class.0, id), &sym_memory),
                                };
                            }
                            Lhs::AccessField(_, _) => todo!(),
                            Lhs::AccessArray(_, _) => todo!(),
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
                                (Specification::Requires(assertion), false) => assert(
                                    config.simplify,
                                    &mut sym_memory,
                                    &mut solver,
                                    assertion,
                                    &mut pc,
                                    &mut diagnostics,
                                )?,
                                // otherwise process we assume
                                (spec, _) => {
                                    let assumption = match spec {
                                        Specification::Requires(expr) => expr,
                                        Specification::Ensures(expr) => expr,
                                    };
                                    if !assume(
                                        config.simplify,
                                        prune_depth < d,
                                        &mut sym_memory,
                                        &mut solver,
                                        assumption,
                                        &mut pc,
                                        &mut diagnostics,
                                    ) {
                                        continue;
                                    };
                                }
                            };
                        }
                    }
                    _ => ()
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
