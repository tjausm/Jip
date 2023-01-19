use z3::Context;

use crate::ast::*;
use crate::shared::{
    panic_with_diagnostics, Reference, ReferenceValue, SymMemory, SymbolicExpression,
};
use crate::z3::{expr_to_bool, expr_to_int};

pub fn type_lhs<'ctx>(sym_memory: &SymMemory<'ctx>, lhs: &'ctx Lhs) -> Type {
    match lhs {
        Lhs::Accessfield(obj, field) => match sym_memory.heap_get_field(obj, field) {
            SymbolicExpression::Bool(_) => Type::Bool,
            SymbolicExpression::Int(_) => Type::Int,
            SymbolicExpression::Ref((ty, _)) => ty
        },
        Lhs::Identifier(id) => match sym_memory.stack_get(id) {
            Some(SymbolicExpression::Bool(_)) => Type::Bool,
            Some(SymbolicExpression::Int(_)) => Type::Int,
            Some(SymbolicExpression::Ref((ty, _))) => ty,
            None => panic_with_diagnostics(
                &format!("Can't type '{}' because it is undeclared on the stack", id),
                Some(&sym_memory),
            ),
        },
    }
}

/// returns the symbolic expression rhs refers to
pub fn parse_rhs<'a, 'b>(
    ctx: &'a Context,
    sym_memory: &SymMemory<'a>,
    ty: &Type,
    rhs: &'a Rhs,
) -> SymbolicExpression<'a> {
    match rhs {
        Rhs::Accessfield(obj_name, field_name) => todo!(),//sym_memory.heap_get_field(obj_name, field_name).clone(),
        Rhs::Expression(expr) => match ty {
            Type::Int => {
                let ast = expr_to_int(&ctx, &sym_memory, &expr);
                SymbolicExpression::Int(ast)
            }

            Type::Bool => {
                let ast = expr_to_bool(&ctx, &sym_memory, &expr);
                SymbolicExpression::Bool(ast)
            }
            Type::Classtype(class) => match expr {
                Expression::Identifier(id) => match sym_memory.stack_get(id) {
                    Some(SymbolicExpression::Ref((ty, r))) => SymbolicExpression::Ref((ty, r)),
                    Some(_) => {
                        panic_with_diagnostics(&format!("TODO: think of error"), Some(&sym_memory))
                    }
                    None => {
                        panic_with_diagnostics(&format!("TODO: think of error"), Some(&sym_memory))
                    }
                },
                _ => panic_with_diagnostics(
                    &format!("Can't evaluate {:?} to type {}", rhs, class),
                    Some(&sym_memory),
                ),
            },
            Type::Void => panic_with_diagnostics(
                &format!(
                    "Can't evaluate rhs expression of the form {:?} to type void",
                    rhs
                ),
                Some(&sym_memory),
            ),
        },
        _ => panic_with_diagnostics(
            &format!("Rhs of the form {:?} should not be in the cfg", rhs),
            Some(&sym_memory),
        ),
    }
}

/// assigns value from rhs to lhs
pub fn lhs_from_rhs<'a>(
    ctx: &'a Context,
    sym_memory: &mut SymMemory<'a>,
    lhs: &'a Lhs,
    rhs: &'a Rhs,
) -> () {
    let ty = type_lhs(&sym_memory, lhs);
    let var = parse_rhs(&ctx, sym_memory, &ty, rhs);
    match lhs {
        Lhs::Accessfield(obj_name, field_name) => sym_memory.heap_update_field(obj_name, field_name, var),
        Lhs::Identifier(id) => sym_memory.stack_insert(id, var),
    }
}

/// move function into memory module
fn initialize_referencevalue(r: Reference, ty: Type, sym_heap: &mut SymMemory) {
    todo!("Initialize fields and return reference to new object on the heap")
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
pub fn params_to_vars<'ctx>(
    ctx: &'ctx Context,
    sym_memory: &mut SymMemory<'ctx>,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
) -> Vec<(&'ctx String, SymbolicExpression<'ctx>)> {
    let mut params_iter = params.iter();
    let mut args_iter = args.iter();
    let mut variables = vec![];

    loop {
        match (params_iter.next(), args_iter.next()) {
            (Some((Type::Int, arg_id)), Some(expr)) => {
                let expr = expr_to_int(ctx, sym_memory, expr);
                variables.push((arg_id, SymbolicExpression::Int(expr)));
            }
            (Some((Type::Bool, arg_id)), Some(expr)) => {
                let expr = expr_to_bool(ctx, sym_memory, expr);
                variables.push((arg_id, SymbolicExpression::Bool(expr)));
            }
            (Some((Type::Classtype(class), arg_id)), Some(expr)) => {
                let err = |class, arg_id, expr| {
                    panic_with_diagnostics(
                        &format!(
                            "Can't assign argument '{} {}' value '{:?}'",
                            class, arg_id, expr
                        ),
                        Some(&sym_memory),
                    )
                };
                match expr {
                    Expression::Identifier(param_id) => match sym_memory.stack_get(param_id) {
                        Some(SymbolicExpression::Ref(r)) => {
                            variables.push((arg_id, SymbolicExpression::Ref(r)))
                        }
                        _ => return err(class, arg_id, expr),
                    },
                    _ => return err(class, arg_id, expr),
                }
            }
            (Some((ty, _)), Some(_)) => panic_with_diagnostics(
                &format!("Argument of type {:?} are not implemented", ty),
                Some(&sym_memory),
            ),
            (Some((_, param)), None) => panic_with_diagnostics(
                &format!(
                    "Missing an argument for parameter {:?} in a method call",
                    param
                ),
                Some(&sym_memory),
            ),
            (None, Some(expr)) => panic_with_diagnostics(
                &format!(
                    "Expression {:?} has no parameter it can be assigned to in a method call",
                    expr
                ),
                Some(&sym_memory),
            ),
            (None, None) => break,
        }
    }
    return variables;
}
