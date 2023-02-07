use crate::ast::*;
use crate::shared::Error;
use crate::z3;
use crate::shared::{panic_with_diagnostics, Diagnostics};
use crate::sym_model::{SymExpression, SymMemory, SymValue, PathConstraints};

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
            Type::Int => SymExpression::Int(SymValue::Expr(expr.clone())),

            Type::Bool => SymExpression::Bool(SymValue::Expr(expr.clone())),
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
                variables.push((arg_id, SymExpression::Int(SymValue::Expr(expr.clone()))));
            }
            (Some((Type::Bool, arg_id)), Some(expr)) => {
                variables.push((arg_id, SymExpression::Bool(SymValue::Expr(expr.clone()))));
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
pub fn assert(simplify: bool, sym_memory: &mut SymMemory, assertion: &Expression, pc: &mut PathConstraints, diagnostics: &mut Diagnostics) -> Result<(), Error>{
    println!("{:?}", pc.get_constraints());
    if simplify {
        let simple_assertion = sym_memory.simplify_expr(assertion.clone());
        //let simple_assertion = assertion;
        match simple_assertion {
            Expression::Literal(Literal::Boolean(false)) => {
                sym_memory.add_assert(simple_assertion.clone(), pc);
                match z3::verify_constraints(&pc, &sym_memory) {
                    Ok(_) => 
                        panic_with_diagnostics(
                            &format!(
"Oh no, the front end simplifier simplified the following to false:

Pathconstraints:
{:?}

Simplified Pathconstraints
{:?}

Expression:
{:?}

But z3 was not able to find a counterexample",
                                    pc.get_constraints(),
                                    sym_memory.simplify_expr(pc.get_constraints()),
                                    assertion
                                ), 
                            &sym_memory),
                    Err(err) => return Err(err),
                }
            },
            Expression::Literal(Literal::Boolean(true)) => (),
            _ => {
                //sym_memory.add_assert(simple_assertion.clone(), pc);
                sym_memory.add_assert(simple_assertion, pc);
                diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
                z3::verify_constraints(&pc, &sym_memory)?;
            }
            }
        }
    else{
        sym_memory.add_assert(assertion.clone(), pc);
        diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
        z3::verify_constraints(&pc, &sym_memory)?;
    };
    Ok(())
}
/// handles the assume in the SEE (used in `assume`, `require` and `ensure` statements)
/// returns false if assumption is infeasible and can be dropped
pub fn assume(simplify: bool, sym_memory: &mut SymMemory, assumption: &Expression, pc: &mut PathConstraints) -> bool{
    println!("{:?}", pc.get_constraints());
    if simplify {
        let simple_assumption = sym_memory.simplify_expr(assumption.clone());
        match simple_assumption{
            Expression::Literal(Literal::Boolean(false)) => return false,
            Expression::Literal(Literal::Boolean(true)) => (),
            //_ => sym_memory.add_assume(simple_assumption.clone(), pc),
            _ => sym_memory.add_assume(simple_assumption, pc),

        };
    } else {
        sym_memory.add_assume(assumption.clone(), pc);
    };
    return true
}