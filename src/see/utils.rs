use std::path::Path;
use std::sync::mpsc::Sender;
use std::thread;

use crate::ast::*;
use crate::cfg::types::{Action, Node};
use crate::shared::{panic_with_diagnostics, Diagnostics};
use crate::shared::{Config, Error};
use crate::sym_model::{
    PathConstraints, ReferenceValue, Substituted, SymExpression, SymMemory, SymValue,
};
use crate::z3;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Graph;
use uuid::Uuid;

use rustc_hash::FxHashMap;

use super::types::{Depth, Msg, PathState};

pub fn type_lhs<'ctx>(sym_memory: &mut SymMemory<'ctx>, lhs: &'ctx Lhs) -> Type {
    match lhs {
        Lhs::Accessfield(obj, field) => match sym_memory.heap_get_field(obj, field) {
            SymExpression::Bool(_) => Type::Bool,
            SymExpression::Int(_) => Type::Int,
            SymExpression::Ref((ty, _)) => ty,
        },
        Lhs::Identifier(id) => match sym_memory.stack_get(id) {
            Some(SymExpression::Bool(_)) => Type::Bool,
            Some(SymExpression::Int(_)) => Type::Int,
            Some(SymExpression::Ref((ty, _))) => ty,
            None => panic_with_diagnostics(
                &format!("Can't type '{}' because it is undeclared on the stack", id),
                &sym_memory,
            ),
        },
    }
}

/// returns the symbolic expression rhs refers to
pub fn parse_rhs<'a, 'b>(sym_memory: &mut SymMemory<'a>, ty: &Type, rhs: &'a Rhs) -> SymExpression {
    match rhs {
        Rhs::Accessfield(obj_name, field_name) => {
            sym_memory.heap_get_field(obj_name, field_name).clone()
        }

        Rhs::Expression(expr) => match ty {
            Type::Int => {
                SymExpression::Int(SymValue::Expr(sym_memory.substitute_expr(expr.clone())))
            }

            Type::Bool => {
                SymExpression::Bool(SymValue::Expr(sym_memory.substitute_expr(expr.clone())))
            }
            Type::Classtype(class) => match expr {
                Expression::Identifier(id) => match sym_memory.stack_get(id) {
                    Some(SymExpression::Ref((ty, r))) => SymExpression::Ref((ty, r)),
                    Some(_) => panic_with_diagnostics(
                        &format!("Trying to parse '{:?}' of type {:?}", rhs, ty),
                        &sym_memory,
                    ),
                    None => panic_with_diagnostics(&format!("TODO: think of error"), &sym_memory),
                },
                _ => panic_with_diagnostics(
                    &format!("Can't evaluate {:?} to type {}", rhs, class),
                    &sym_memory,
                ),
            },
            Type::Void => panic_with_diagnostics(
                &format!(
                    "Can't evaluate rhs expression of the form {:?} to type void",
                    rhs
                ),
                &sym_memory,
            ),
        },
        _ => panic_with_diagnostics(
            &format!("Rhs of the form {:?} should not be in the cfg", rhs),
            &sym_memory,
        ),
    }
}

// gets type of lhs, parses expression on rhs and assign value of rhs to lhs on stack / heap
pub fn lhs_from_rhs<'a>(sym_memory: &mut SymMemory<'a>, lhs: &'a Lhs, rhs: &'a Rhs) -> () {
    let ty = type_lhs(sym_memory, lhs);
    let var = parse_rhs(sym_memory, &ty, rhs);
    match lhs {
        Lhs::Accessfield(obj_name, field_name) => {
            sym_memory.heap_update_field(obj_name, field_name, var)
        }
        Lhs::Identifier(id) => sym_memory.stack_insert(id, var),
    }
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
pub fn params_to_vars<'ctx>(
    sym_memory: &mut SymMemory<'ctx>,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
) -> Vec<(&'ctx String, SymExpression)> {
    let mut params_iter = params.iter();
    let mut args_iter = args.iter();
    let mut variables = vec![];

    loop {
        match (params_iter.next(), args_iter.next()) {
            (Some((Type::Int, arg_id)), Some(expr)) => {
                variables.push((
                    arg_id,
                    SymExpression::Int(SymValue::Expr(sym_memory.substitute_expr(expr.clone()))),
                ));
            }
            (Some((Type::Bool, arg_id)), Some(expr)) => {
                variables.push((
                    arg_id,
                    SymExpression::Bool(SymValue::Expr(sym_memory.substitute_expr(expr.clone()))),
                ));
            }
            (Some((Type::Classtype(class), arg_id)), Some(expr)) => {
                let err = |class, arg_id, expr| {
                    panic_with_diagnostics(
                        &format!(
                            "Can't assign argument '{} {}' value '{:?}'",
                            class, arg_id, expr
                        ),
                        &sym_memory,
                    )
                };
                match expr {
                    Expression::Identifier(param_id) => match sym_memory.stack_get(param_id) {
                        Some(SymExpression::Ref(r)) => {
                            variables.push((arg_id, SymExpression::Ref(r)))
                        }
                        _ => return err(class, arg_id, expr),
                    },
                    _ => return err(class, arg_id, expr),
                }
            }
            (Some((ty, _)), Some(_)) => panic_with_diagnostics(
                &format!("Argument of type {:?} are not implemented", ty),
                &sym_memory,
            ),
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
    return variables;
}

/// handles the assertion in the SEE (used in `assert` and `require` statements)
pub fn assert(
    simplify: bool,
    sym_memory: &mut SymMemory,
    assertion: &Expression,
    pc: &mut PathConstraints,
    diagnostics: &mut Diagnostics,
) -> Result<(), Error> {
    let subt_assertion = sym_memory.substitute_expr(assertion.clone());

    // add (simplified) assertion
    if simplify {
        let simple_assertion = sym_memory.simplify_expr(subt_assertion);
        //let simple_assertion = assertion;
        match simple_assertion {
            Substituted(Expression::Literal(Literal::Boolean(true))) => (),
            _ => pc.push_assertion(simple_assertion),
        }
    } else {
        pc.push_assertion(subt_assertion);
    };

    // calculate (simplified) constraints
    let mut constraints = pc.combine();
    if simplify {
        constraints = sym_memory.simplify_expr(constraints)
    };
    match constraints {
        Substituted(Expression::Literal(Literal::Boolean(true))) => return Ok(()),
        _ => (),
    }

    // if we have not solved by now, invoke z3
    diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
    z3::verify_constraints(&pc, &sym_memory)
}
/// handles the assume in the SEE (used in `assume`, `require` and `ensure` statements)
/// returns false if assumption is infeasible and can be dropped
pub fn assume(
    simplify: bool,
    sym_memory: &mut SymMemory,
    assumption: &Expression,
    pc: &mut PathConstraints,
) -> bool {
    let subt_assumption = sym_memory.substitute_expr(assumption.clone());

    if simplify {
        let simple_assumption = sym_memory.simplify_expr(subt_assumption);
        match simple_assumption {
            Substituted(Expression::Literal(Literal::Boolean(false))) => return false,
            Substituted(Expression::Literal(Literal::Boolean(true))) => (),
            //_ => sym_memory.add_assume(simple_assumption.clone(), pc),
            _ => pc.push_assumption(simple_assumption),
        };
    } else {
        pc.push_assumption(subt_assumption);
    };
    return true;
}

// Assert -> build & verify z3 formula, return error if disproven
// Assume -> build & verify z3 formula, stop evaluating pad if disproven
// assignment -> evaluate rhs and update env
// then we enque all connected nodes, till d=0 or we reach end of cfg
pub fn explore_path<'a>(
    tx: Sender<Msg<'a>>,
    cfg: &'a Graph<Node, Vec<Action>>,
    config: &Config,
    (retval_id, this_id): (&'a String, &'a String),
    mut diagnostics: Diagnostics,
    PathState {
        mut sym_memory,
        mut pc,
        d,
        curr_node,
    }: PathState<'a>,
) {
    if d == 0 {
        return;
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
                        sym_memory
                            .stack_insert(id, SymExpression::Ref((Type::Classtype(ty.clone()), r)));
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
                    Statement::Assume(assumption) => 
                        if !assume(config.simplify, &mut sym_memory, assumption, &mut pc) 
                            {
                                tx.send(Msg::FinishedPath(diagnostics)); 
                                return;
                            },
                    Statement::Assert(assertion) =>  match assert(config.simplify, &mut sym_memory, assertion, &mut pc, &mut diagnostics) {
                        Err(err) => {
                            tx.send(Msg::Err(err)); 
                            return
                        },
                        _ => ()
                    },
                    Statement::Assignment((lhs, rhs)) => {
                        lhs_from_rhs(&mut sym_memory, lhs, rhs);
                    }
                    Statement::Return(expr) => {

                        // stop path if current scope `id == None`, indicating we are in main scope
                        if sym_memory.get_scope(0).id == None {};

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
                                    SymExpression::Int(SymValue::Expr(sym_memory.substitute_expr(expr.clone()))),
                                );
                            },
                            Some(SymExpression::Int(_)) => {sym_memory.stack_insert(retval_id,SymExpression::Int(SymValue::Expr(sym_memory.substitute_expr(expr.clone()))),);},
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
                        Type::Int => sym_memory
                            .stack_insert(retval_id, SymExpression::Int(SymValue::Uninitialized)),
                        Type::Bool => sym_memory
                            .stack_insert(retval_id, SymExpression::Bool(SymValue::Uninitialized)),
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
                                        (Type::Int, SymExpression::Int(SymValue::Uninitialized)),
                                    );
                                }
                                Type::Bool => {
                                    (fields.insert(
                                        field.clone(),
                                        (Type::Bool, SymExpression::Bool(SymValue::Uninitialized)),
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
                    let from_main_scope =
                        sym_memory.get_scope(0).id == None || sym_memory.get_scope(1).id == None;

                    for specification in specifications {
                        match (specification, from_main_scope) {
                            // if require is called outside main scope we assert
                            (Specification::Requires(assertion), false) => match assert(
                                config.simplify,
                                &mut sym_memory,
                                assertion,
                                &mut pc,
                                &mut diagnostics,
                            ) {
                                Err(err) => {
                                    tx.send(Msg::Err(err));
                                    return;
                                },
                                _ => (),
                            },
                            // otherwise process we assume
                            (spec, _) => {
                                let assumption = match spec {
                                    Specification::Requires(expr) => expr,
                                    Specification::Ensures(expr) => expr,
                                };
                                if !assume(config.simplify, &mut sym_memory, assumption, &mut pc) {
                                    continue;
                                };
                            }
                        };
                    }
                }
            }
        }
        let next = edge.target();
        tx.send(Msg::NewState(PathState { sym_memory, pc: pc.clone(), d: d - 1, curr_node: next }));
    }
    tx.send(Msg::FinishedPath(diagnostics));
}
