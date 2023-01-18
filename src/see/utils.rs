use z3::Context;

use crate::ast::*;
use crate::shared::{custom_panic, Error};
use crate::z3::{SymStack, SymHeap, SymbolicExpression, ReferenceValue, get_from_stack, expression_to_int, expression_to_bool, insert_into_stack};


pub fn type_lhs<'ctx>(sym_stack: &SymStack<'ctx>, sym_heap: &SymHeap<'ctx>, lhs: &'ctx Lhs) -> Type {
    match lhs {
        Lhs::Accessfield(obj, field) => match get_from_stack(&sym_stack, obj) {
            Some(SymbolicExpression::Ref((ty, r))) => match sym_heap.get(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (ty, _) = match fields.get(field) {
                        Some(field) => field,
                        None => custom_panic(
                            &format!(
                                "Can't type field '{}.{}' because it does not exist",
                                obj, field
                            ),
                            Some(&sym_stack),
                            Some(&sym_heap),
                        ),
                    };
                    return ty.clone();
                }
                Some(ReferenceValue::Uninitialized(ty)) => {
                    todo!("searching through program to get type of uninitialized fields")
                }
                Some(ReferenceValue::Array(_)) => custom_panic(
                    &format!(
                        "Can't type '{}.{}' because the reference of '{}' points to an array",
                        obj, field, obj
                    ),
                    Some(&sym_stack),
                    Some(&sym_heap),
                ),
                None => custom_panic(
                    &format!(
                    "Can't type '{}.{}' because reference of '{}' points to nothing on the heap",
                    obj, field, obj
                ),
                    Some(&sym_stack),
                    Some(&sym_heap),
                ),
            },
            _ => custom_panic(
                &format!(
                    "Can't type '{}.{}' because {} is not a reference",
                    obj, field, obj
                ),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
        },
        Lhs::Identifier(id) => match get_from_stack(sym_stack, id) {
            Some(SymbolicExpression::Bool(_)) => Type::Bool,
            Some(SymbolicExpression::Int(_)) => Type::Int,
            Some(SymbolicExpression::Ref((ty, _))) => ty,
            None => custom_panic(
                &format!("Can't type '{}' because it is undeclared on the stack", id),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
        },
    }
}

/// returns the symbolic expression rhs refers to
pub fn parse_rhs<'ctx>(
    ctx: &'ctx Context,
    sym_stack: &SymStack<'ctx>,
    sym_heap: &SymHeap<'ctx>,
    ty: &Type,
    rhs: &'ctx Rhs,
) -> SymbolicExpression<'ctx> {
    match rhs {
        Rhs::Accessfield(obj_name, field_name) => match get_from_stack(sym_stack, obj_name) {
            Some(SymbolicExpression::Ref((_, r))) => match sym_heap.get(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (_, value) = match fields.get(field_name) {
                        Some(field) => field,
                        None => custom_panic(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            Some(&sym_stack),
                            Some(&sym_heap),
                        ),
                    };
                    return value.clone();
                }

                _ => custom_panic(
                    &format!(
                        "Reference of {} not found on heap while parsing rhs {:?}",
                        obj_name, rhs
                    ),
                    Some(&sym_stack),
                    Some(&sym_heap),
                ),
            },
            _ => custom_panic(
                &format!("{} is not a reference", obj_name),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
        },
        Rhs::Expression(expr) => match ty {
            Type::Int => {
                let ast = expression_to_int(&ctx, &sym_stack, &expr);
                SymbolicExpression::Int(ast)
            }

            Type::Bool => {
                let ast = expression_to_bool(&ctx, &sym_stack, &expr);
                SymbolicExpression::Bool(ast)
            }
            Type::Classtype(class) => match expr {
                Expression::Identifier(id) => match get_from_stack(sym_stack, id) {
                    Some(SymbolicExpression::Ref((ty, r))) => SymbolicExpression::Ref((ty, r)),
                    Some(_) => {
                        custom_panic(&format!("TODO: think of error"), Some(&sym_stack), Some(&sym_heap))
                    }
                    None => custom_panic(&format!("TODO: think of error"), Some(&sym_stack), Some(&sym_heap)),
                },
                _ => custom_panic(
                    &format!("Can't evaluate {:?} to type {}", rhs, class),
                    Some(&sym_stack),
                    Some(&sym_heap),
                ),
            },
            Type::Void => custom_panic(
                &format!(
                    "Can't evaluate rhs expression of the form {:?} to type void",
                    rhs
                ),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
        },
        _ => custom_panic(
            &format!("Rhs of the form {:?} should not be in the cfg", rhs),
            Some(&sym_stack),
            Some(&sym_heap),
        ),
    }
}

/// assigns value from rhs to lhs
pub fn lhs_from_rhs<'ctx>(
    ctx: &'ctx Context,
    sym_stack: &mut SymStack<'ctx>,
    sym_heap: &mut SymHeap<'ctx>,
    lhs: &'ctx Lhs,
    rhs: &'ctx Rhs,
) -> Result<(), Error> {
    let ty = type_lhs(&sym_stack, &sym_heap, lhs);
    let var = parse_rhs(&ctx, sym_stack, sym_heap, &ty, rhs);
    match lhs {
        Lhs::Accessfield(obj_name, field_name) => match get_from_stack(sym_stack, obj_name) {
            Some(SymbolicExpression::Ref((ty, r))) => match sym_heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (ty, _) = match fields.get(field_name) {
                        Some(field) => field,
                        None => custom_panic(&format!(
                            "Field {} does not exist on {}",
                            field_name, obj_name
                        ), Some(&sym_stack), Some(&sym_heap))
                    };
                    fields.insert(field_name, (ty.clone(), var));
                    Ok(())
                }
                _ => custom_panic(
                    &format!(
                        "Reference of {} not found on heap while doing assignment {:?} := {:?}",
                        obj_name, lhs, rhs
                    ),
                    Some(&sym_stack),
                    Some(&sym_heap),
                ),
            },
            _ => custom_panic(
                &format!("{} is not a reference", obj_name),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
        },
        Lhs::Identifier(id) => Ok(insert_into_stack(sym_stack, id, var)),
    }
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
pub fn params_to_vars<'ctx>(
    ctx: &'ctx Context,
    sym_stack: &mut SymStack<'ctx>,
    sym_heap: &SymHeap<'ctx>,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
) -> Vec<(&'ctx String, SymbolicExpression<'ctx>)> {
    let mut params_iter = params.iter();
    let mut args_iter = args.iter();
    let mut variables = vec![];

    loop {
        match (params_iter.next(), args_iter.next()) {
            (Some((Type::Int, arg_id)), Some(expr)) => {
                let expr = expression_to_int(ctx, sym_stack, expr);
                variables.push((arg_id, SymbolicExpression::Int(expr)));
            }
            (Some((Type::Bool, arg_id)), Some(expr)) => {
                let expr = expression_to_bool(ctx, sym_stack, expr);
                variables.push((arg_id, SymbolicExpression::Bool(expr)));
            }
            (Some((Type::Classtype(class), arg_id)), Some(expr)) => {
                let err = |class, arg_id, expr| {
                    custom_panic(
                        &format!(
                            "Can't assign argument '{} {}' value '{:?}'",
                            class, arg_id, expr
                        ),
                        Some(&sym_stack),
                        Some(&sym_heap),
                    )
                };
                match expr {
                    Expression::Identifier(param_id) => match get_from_stack(sym_stack, param_id) {
                        Some(SymbolicExpression::Ref(r)) => {
                            variables.push((arg_id, SymbolicExpression::Ref(r)))
                        }
                        _ => return err(class, arg_id, expr),
                    },
                    _ => return err(class, arg_id, expr),
                }
            }
            (Some((ty, _)), Some(_)) => custom_panic(
                &format!("Argument of type {:?} are not implemented", ty),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
            (Some((_, param)), None) => custom_panic(
                &format!(
                    "Missing an argument for parameter {:?} in a method call",
                    param
                ),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
            (None, Some(expr)) => custom_panic(
                &format!(
                    "Expression {:?} has no parameter it can be assigned to in a method call",
                    expr
                ),
                Some(&sym_stack),
                Some(&sym_heap),
            ),
            (None, None) => break,
        }
    }
    return variables;
}
