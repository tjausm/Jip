//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!
//!

lalrpop_mod!(#[allow(dead_code)] pub parser); // synthesized by LALRPOP and pass allow(dead_code) to avoid warning of mods only used in unit tests

mod utils;

use crate::ast::*;
use crate::cfg::types::{Action, Node};
use crate::cfg::{generate_cfg, generate_dot_cfg};
use crate::see::utils::*;
use crate::shared::{Config};
use crate::shared::ExitCode;
use crate::shared::{panic_with_diagnostics, Depth, Diagnostics, Error};
use crate::smt_solver::Solver;
use crate::symbolic::expression::{PathConstraints, SymExpression, SymType};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::{ArrSizes,  SymRefType, LazyReference, Reference, EvaluatedRefs};

use colored::Colorize;
use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use std::collections::VecDeque;
use std::fs;
use std::time::Instant;

type Trace<'a> = Vec<&'a Node>;

pub fn bench(
    program: &str,
    start: Depth,
    end: Option<Depth>,
    step: i32,
    config: &Config,
) -> (ExitCode, String) {
    let end = end.unwrap_or(start) + 1;
    let depths = (start..end).step_by(step.try_into().unwrap());
    println!("d           time (s)    paths expl. z3 calls");
    for depth in depths {
        let now = Instant::now();
        let dia;
        // Code block to measure.
        {
            match verify_program(program, depth, &config) {
                Ok(d) => dia = d,
                r => return print_result(r),
            }
        }

        // format duration to string of length 5
        let dur = now.elapsed();
        let time = format!("{:?},{:0<3}", dur.as_secs(), dur.as_millis());
        println!(
            "{:<12}{:<12}{:<12}{:<12}",
            depth,
            &time[0..5],
            dia.paths_explored,
            dia.z3_calls
        );
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
                d.z3_calls
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

pub fn print_verification(program: &str, d: Depth, config: &Config) -> (ExitCode, String) {
    let result = verify_program(program, d, config);
    print_result(result.clone())
}

/// prints the verbose debug info
fn print_debug(node: &Node, sym_memory: &SymMemory, pc: &PathConstraints, arr_sizes: &ArrSizes, trace: &Trace) {
    let print_node = format!("{:?}", node);
    let print_sym_memory = format!("{:?}", sym_memory);
    let print_ranges = format!("{:?}", arr_sizes);
    let print_trace = format!("trace: {:?}", trace);

    let pc = pc.combine_over_true();
    let print_pc = format!("Path constraints -> {:?}", pc);

    let dump_state = match node {
        Node::Statement(Statement::Assert(_)) => true,
        Node::Statement(Statement::Assume(_)) => true,
        _ => false,
    };
    if dump_state {
        println!(
            "{}\n\n{}\n\n{}\n\n{}\n\n{}",
            print_node, print_trace, print_pc, print_ranges, print_sym_memory
        );
    } else {
        println!("{}", print_node);
    }
}

fn verify_program(prog_string: &str, d: Depth, config: &Config) -> Result<Diagnostics, Error> {
    let prune_coefficient = f64::from(config.prune_ratio) / f64::from(i8::MAX);
    let prune_depth = (f64::from(d) - f64::from(d) * prune_coefficient) as i32;

    //init diagnostic info
    let mut diagnostics = Diagnostics::default();

    //init solver
    let mut solver = Solver::new(&config);

    // init retval and this such that it outlives env
    let retval_id = &"retval".to_string();
    let this_id = &"this".to_string();

    let prog = parse_program(prog_string);
    let (start_node, cfg) = generate_cfg(prog.clone());

    //init our bfs through the cfg
    let mut q: VecDeque<(SymMemory, PathConstraints, ArrSizes, EvaluatedRefs, Depth, NodeIndex, Trace)> = VecDeque::new();
    q.push_back((
        SymMemory::new(prog.clone()),
        PathConstraints::default(),
        ArrSizes::default(),
        FxHashSet::default(),
        d,
        start_node,
        vec![]
    ));

    // enque all connected nodes, till d=0 or we reach end of cfg
    'q_states: while let Some((mut sym_memory, mut pc, mut sizes, mut eval_refs, d, curr_node, mut trace)) = q.pop_front() {
        if d == 0 {
            continue;
        }

        if config.verbose {
            trace.push(&cfg[curr_node]);
            print_debug(&cfg[curr_node], &sym_memory, &pc, &sizes, &trace);
        };

        match &cfg[curr_node] {
            // add all parameters of main as free variables to env
            Node::EnteringMain(parameters) => {
                for parameter in parameters {
                    match parameter {
                        (Type::Int, id) => sym_memory.stack_insert(
                            id.clone(),
                            SymExpression::FreeVariable(SymType::Int, id.clone()),
                        ),
                        (Type::Bool, id) => sym_memory.stack_insert(
                            id.clone(),
                            SymExpression::FreeVariable(SymType::Bool, id.clone()),
                        ),
                        (Type::Array(ty), id) => {
                            let r = Reference::new();
                            let size =
                                SymExpression::FreeVariable(SymType::Int, format!("#{:?}", r));
                            let sym_ty = match &**ty {
                                Type::Int => SymType::Int,
                                Type::Bool => SymType::Bool,
                                Type::Class(id) => SymType::Ref(SymRefType::Object(id.clone())),
                                Type::Array(_) => {
                                    todo!("2+ dimensional arrays are not yet supported")
                                }
                                Type::Void => panic_with_diagnostics(
                                    "Can't pass an array of type void as argument to main()",
                                    &sym_memory,
                                ),
                            };
                            let arr = sym_memory.init_array(sym_ty.clone(), size, true);
                            sym_memory.heap_insert(Some(r), arr);
                            sym_memory.stack_insert(id.clone(), SymExpression::Reference(r));
                        }
                        (Type::Class(class_name), id) => {
                            let lr = LazyReference::new(class_name.clone());
                            sym_memory.stack_insert(id.clone(), SymExpression::LazyReference(lr));
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
                            sym_memory.stack_insert(id.clone(), SymExpression::Uninitialized)
                        }
                        Type::Bool => {
                            sym_memory.stack_insert(id.clone(), SymExpression::Uninitialized)
                        }
                        _ => sym_memory
                            .stack_insert(id.clone(), SymExpression::Reference(Reference::new())),
                    },
                    Statement::Assume(assumption) => {
                        if !assume(
                            &mut sym_memory,
                            &mut pc,
                            &mut sizes,
                            d > prune_depth,
                            &mut solver,
                            assumption,
                            &mut diagnostics,
                        ) {
                            continue;
                        }
                    }
                    Statement::Assert(assertion) => assert(
                        &mut sym_memory,
                        &mut pc,
                        &mut sizes,
                        &mut solver,
                        assertion,
                        &mut diagnostics,
                    )?,
                    Statement::Assignment((lhs, rhs)) => {
                        // try assignment, stop exploring path if it's infeasible
                        if !lhs_from_rhs(
                            &mut sym_memory,
                            &pc,
                            &mut sizes,
                            &mut eval_refs,
                            &mut solver,
                            &mut diagnostics,
                            lhs,
                            rhs,
                        )? {continue};
                    }
                    Statement::Return(expr) => {
                        // stop path if current scope `id == None`, indicating we are in main scope
                        if sym_memory.get_scope(0).id == None {
                            continue;
                        };

                        // add return value to stack
                        sym_memory.stack_insert(
                            retval_id.clone(),
                            SymExpression::new(&sym_memory, expr.clone()),
                        );
                    }
                    _ => (),
                }
            }
            Node::End => {
                diagnostics.paths_explored = diagnostics.paths_explored + 1;
                continue 'q_states;
            }
            _ => (),
        }

        'q_edges: for edge in cfg.edges(curr_node) {
            // clone new stack and heap for each edge we travel to
            let mut sym_memory = sym_memory.clone();

            // perform all actions in an edge and enque the result
            for action in edge.weight() {
                match action {
                    Action::EnterScope { to: scope } => sym_memory.stack_push(scope.clone()),
                    Action::AssignArgs { params, args } => {
                        let mut params_iter = params.iter();
                        let mut args_iter = args.iter();
                        loop {
                            match (params_iter.next(), args_iter.next()) {
                                (Some((_, arg_id)), Some(expr)) => {
                                    let sym_expr = SymExpression::new(&sym_memory, expr.clone());
                                    sym_memory.stack_insert(arg_id.clone(), sym_expr);
                                },
                                (Some((_, param)), None) => panic_with_diagnostics(
                                    &format!(
                                        "Missing an argument for parameter {:?} in a method call",
                                        param
                                    ),
                                    &sym_memory,
                                ),
                                (None, Some(expr)) => panic_with_diagnostics(
                                    &format!(
                                        "Expression {:?} has no parameter it can be assigned to in a method call",
                                        expr
                                    ),
                                    &sym_memory,
                                ),
                                (None, None) => break,
                            }
                        }
                    }
                    Action::DeclareThis { class, obj } => match obj {
                        Lhs::Identifier(id) => {
                            // possibly fork
                            let val = sym_memory
                                .stack_get(id);

                            match val {
                                Some(SymExpression::Reference(_)) => sym_memory
                                    .stack_insert(this_id.clone(), val.unwrap()),
                                Some(SymExpression::LazyReference(_)) => sym_memory
                                    .stack_insert(this_id.clone(), val.unwrap()),

                                Some(ty) => panic_with_diagnostics(
                                    &format!(
                                        "{} is not of type {} but of type {:?}",
                                        id, class, ty
                                    ),
                                    &sym_memory,
                                ),
                                None => panic_with_diagnostics(
                                    &format!("Variable {} is undeclared", id),
                                    &sym_memory,
                                ),
                            }
                        }
                        Lhs::AccessField(obj_name, field) => {
                            match sym_memory.heap_access_object(&pc, &sizes, &mut eval_refs, &mut solver, &mut diagnostics, obj_name, field, None)? {
                                Some(SymExpression::Reference(r)) => sym_memory.stack_insert(this_id.to_string(), SymExpression::Reference(r)),
                                None => continue 'q_edges,                
                                _ => panic_with_diagnostics(&format!("Can't access field {}.{}", obj_name, field), &sym_memory),
                            };
                        }
                        Lhs::AccessArray(arr_name, index) => {
                            let expr = sym_memory.heap_access_array(
                                &pc,
                                &sizes,
                                &mut solver,
                                &mut diagnostics,
                                arr_name,
                                index.clone(),
                                None,
                            )?;
                            match expr {
                                    SymExpression::Reference(r) => sym_memory.stack_insert(this_id.to_string(), SymExpression::Reference(r)),
                                    _ => panic_with_diagnostics(&format!("Can't assign '{} this' because there is no reference at {}[{:?}]", class, arr_name, index), &sym_memory),
                                };
                        }
                    },
                    Action::InitObj {
                        from_class,
                        to: lhs,
                    } => {
                        // get reference r, init object, and insert into heap under reference
                        match lhs {
                            Lhs::Identifier(id) => 
                                match sym_memory.stack_get(id) {
                                    Some(SymExpression::Reference(r)) => {
                                        // make an empty object and insert into heap
                                        let obj = sym_memory.init_object(from_class.clone());
                                        sym_memory.heap_insert(Some(r), obj);
                                    },
                                    Some(SymExpression::LazyReference(lr)) => {
                                        // release lazy reference and initialize object
                                        let r = match lr.release(&mut diagnostics, &mut solver,  &pc, &sizes, &mut eval_refs, &sym_memory)? {
                                            Some(r) => r,
                                            _ => continue 'q_edges
                                        };
                                        let obj = sym_memory.init_object(from_class.clone());
                                        sym_memory.heap_insert(Some(r), obj);
                                    },
                                    _ => panic_with_diagnostics(&format!("Can't initialize '{} {}' because it has not been declared yet", from_class, id), &sym_memory),
                                },
                            
                            Lhs::AccessField(obj_name, field) => {
                                match sym_memory.heap_access_object(&pc, &sizes, &mut eval_refs, &mut solver, &mut diagnostics, obj_name, field, None)? {
                                    Some(SymExpression::Reference(r)) => {
                                        // make an empty object and insert into heap
                                        let obj = sym_memory.init_object( from_class.clone());
                                        sym_memory.heap_insert(Some(r), obj);
                                    },
                                    None => continue 'q_edges,
                                    _ => panic_with_diagnostics(&format!("Can't initialize '{}' because there is no reference at {}.{}", from_class, obj_name, field), &sym_memory),
                                };
                            }
                            Lhs::AccessArray(arr_name, index) => {
                                let expr = sym_memory.heap_access_array(
                                    &pc,
                                    &sizes,
                                    &mut solver,
                                    &mut diagnostics,
                                    arr_name,
                                    index.clone(),
                                    None,
                                )?;
                                match expr {
                                    SymExpression::Reference(r) => {
                                        // make an empty object and insert into heap
                                        let obj = sym_memory.init_object(from_class.clone());
                                        sym_memory.heap_insert(Some(r), obj);
                                    },
                                    _ => panic_with_diagnostics(&format!("Can't initialize '{}' because there is no reference at {}[{:?}]", from_class, arr_name, index), &sym_memory),
                                };
                            }
                        };
                    }
                    // lift retval 1 scope up
                    Action::LiftRetval => {
                        let expr = sym_memory
                            .stack_get(retval_id);

                        match expr {
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
                            continue 'q_edges;
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
                                    &mut sym_memory,
                                    &mut pc,
                                    &mut sizes,
                                    &mut solver,
                                    assertion,
                                    &mut diagnostics,
                                )?,
                                // otherwise process we assume
                                (spec, _) => {
                                    let assumption = match spec {
                                        Specification::Requires(expr) => expr,
                                        Specification::Ensures(expr) => expr,
                                    };
                                    if !assume(
                                        &mut sym_memory,
                                        &mut pc,
                                        &mut sizes,
                                        prune_depth < d,
                                        &mut solver,
                                        assumption,
                                        &mut diagnostics,
                                    ) {
                                        continue;
                                    };
                                }
                            };
                        }
                    }
                    _ => (),
                }
            }
            let next = edge.target();
            q.push_back((sym_memory, pc.clone(), sizes.clone(), eval_refs.clone(), d - 1, next, trace.clone()));
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
