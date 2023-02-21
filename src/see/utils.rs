use ::z3::Context;

use crate::ast::*;
use crate::shared::Error;
use crate::shared::{panic_with_diagnostics, Diagnostics};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::model::{PathConstraints, Substituted, SymExpression, SymValue};
use crate::z3;

pub fn type_lhs<'ctx>(sym_memory: &mut SymMemory, lhs: &'ctx Lhs) -> Type {
    match lhs {
        Lhs::AccessField(obj, field) => match sym_memory.heap_access_object(obj, field, None) {
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
        Lhs::AccessArray(arr_name, index) => match sym_memory.stack_get(arr_name) {
            Some(SymExpression::Ref((Type::ArrayType(inner_ty), _))) => *inner_ty,
            _ => panic_with_diagnostics(
                &format!(
                    "Can't type '{}[{:?}]' because {} is not on the stack as an array",
                    arr_name, index, arr_name
                ),
                &sym_memory,
            ),
        },
    }
}

/// returns the symbolic expression rhs refers to
pub fn parse_rhs<'a, 'b>(
    ctx: &Context,
    pc: &PathConstraints,
    simplify: bool,
    sym_memory: &mut SymMemory,
    ty: &Type,
    rhs: &'a Rhs,
) -> Result<SymExpression, Error> {
    match rhs {
        Rhs::AccessField(obj_name, field_name) => Ok(sym_memory
            .heap_access_object(obj_name, field_name, None)
            .clone()),

        // generate reference, build arrayname from said reference, insert array into heap and return reference
        Rhs::NewArray(ty, len) => {
            let subt_len = Substituted::new(sym_memory, len.clone());
            let arr = sym_memory.init_array(ty.clone(), subt_len);
            let r = sym_memory.heap_insert(None, arr);
            Ok(SymExpression::Ref((ty.clone(), r)))
        }

        Rhs::AccessArray(arr_name, index) => {
            sym_memory.heap_access_array(ctx, pc, simplify, arr_name, index.clone(), None)
        }

        Rhs::Expression(expr) => match ty {
            Type::Int => Ok(SymExpression::Int(SymValue::Expr(Substituted::new(
                &sym_memory,
                expr.clone(),
            )))),

            Type::Bool => Ok(SymExpression::Bool(SymValue::Expr(Substituted::new(
                &sym_memory,
                expr.clone(),
            )))),
            // otherwise parse as ref
            _ => match expr {
                Expression::Identifier(id) => match sym_memory.stack_get(id) {
                    Some(SymExpression::Ref((ty, r))) => Ok(SymExpression::Ref((ty, r))),
                    Some(_) => panic_with_diagnostics(
                        &format!("Trying to parse '{:?}' of type {:?}", rhs, ty),
                        &sym_memory,
                    ),
                    None => panic_with_diagnostics(&format!("TODO: think of error"), &sym_memory),
                },
                _ => panic_with_diagnostics(
                    &format!("Can't evaluate {:?} as referencevalue", rhs),
                    &sym_memory,
                ),
            },
        },
        _ => panic_with_diagnostics(
            &format!(
                "Rhs of the form {:?} with type {:?} should not be in the cfg",
                rhs, ty
            ),
            &sym_memory,
        ),
    }
}

// gets type of lhs, parses expression on rhs and assign value of rhs to lhs on stack / heap
pub fn lhs_from_rhs<'a>(
    ctx: &Context,
    pc: &PathConstraints,
    simplify: bool,
    sym_memory: &mut SymMemory,
    lhs: &'a Lhs,
    rhs: &'a Rhs,
) -> Result<(), Error> {
    let ty = type_lhs(sym_memory, lhs);
    let var = parse_rhs(ctx, pc, simplify, sym_memory, &ty, rhs)?;
    match lhs {
        Lhs::Identifier(id) => sym_memory.stack_insert(id, var),
        Lhs::AccessField(obj_name, field_name) => {
            sym_memory.heap_access_object(obj_name, field_name, Some(var));
        }
        Lhs::AccessArray(arr_name, index) => {
            sym_memory.heap_access_array(ctx, pc, simplify, arr_name, index.clone(), Some(var))?;
        }
    };
    Ok(())
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
pub fn params_to_vars<'ctx>(
    sym_memory: &mut SymMemory,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
) -> Vec<(&'ctx String, SymExpression)> {
    let mut params_iter = params.iter();
    let mut args_iter = args.iter();
    let mut variables = vec![];

    let err = |ty, arg_id, expr| {
        panic_with_diagnostics(
            &format!(
                "Can't assign argument '{} {}' value '{:?}'",
                ty, arg_id, expr
            ),
            &sym_memory,
        )
    };

    loop {
        match (params_iter.next(), args_iter.next()) {
            (Some((Type::Int, arg_id)), Some(expr)) => {
                variables.push((
                    arg_id,
                    SymExpression::Int(SymValue::Expr(Substituted::new(&sym_memory, expr.clone()))),
                ));
            }
            (Some((Type::Bool, arg_id)), Some(expr)) => {
                variables.push((
                    arg_id,
                    SymExpression::Bool(SymValue::Expr(Substituted::new(
                        &sym_memory,
                        expr.clone(),
                    ))),
                ));
            }
            (Some((Type::ArrayType(ty), arg_id)), Some(expr)) => match expr {
                Expression::Identifier(param_id) => match sym_memory.stack_get(param_id) {
                    Some(SymExpression::Ref(r)) => variables.push((arg_id, SymExpression::Ref(r))),
                    _ => return err(&format!("{:?}[]", ty), arg_id, expr),
                },
                _ => return err(&format!("{:?}[]", ty), arg_id, expr),
            },
            (Some((Type::ClassType(class), arg_id)), Some(expr)) => match expr {
                Expression::Identifier(param_id) => match sym_memory.stack_get(param_id) {
                    Some(SymExpression::Ref(r)) => variables.push((arg_id, SymExpression::Ref(r))),
                    _ => return err(class, arg_id, expr),
                },
                _ => return err(class, arg_id, expr),
            },
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
    ctx: &Context,
    simplify: bool,
    sym_memory: &mut SymMemory,
    assertion: &Expression,
    pc: &mut PathConstraints,
    diagnostics: &mut Diagnostics,
) -> Result<(), Error> {
    let subt_assertion = Substituted::new(&sym_memory, assertion.clone());

    // add (simplified) assertion
    if simplify {
        let simple_assertion = sym_memory.simplify_expr(subt_assertion);
        //let simple_assertion = assertion;
        match simple_assertion.get() {
            Expression::Literal(Literal::Boolean(true)) => (),
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
    match constraints.get() {
        Expression::Literal(Literal::Boolean(true)) => return Ok(()),
        _ => (),
    }

    // if we have not solved by now, invoke z3
    diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
    z3::verify_constraints(ctx, &pc, &sym_memory)
}

/// handles the assume in the SEE (used in `assume`, `require` and `ensure` statements)
/// returns false if assumption is infeasible and can be dropped
pub fn assume(
    ctx: &Context,
    simplify: bool,
    use_z3: bool,
    sym_memory: &mut SymMemory,
    assumption: &Expression,
    pc: &mut PathConstraints,
    diagnostics: &mut Diagnostics,
) -> bool {
    let subt_assumption = Substituted::new(&sym_memory, assumption.clone());

    if simplify {
        let simple_assumption = sym_memory.simplify_expr(subt_assumption);
        match simple_assumption.get() {
            Expression::Literal(Literal::Boolean(false)) => return false,
            Expression::Literal(Literal::Boolean(true)) => (),
            //_ => sym_memory.add_assume(simple_assumption.clone(), pc),
            _ => pc.push_assumption(simple_assumption),
        };
    } else {
        pc.push_assumption(subt_assumption);
    };

    // if we have not solved by now, invoke z3
    if use_z3{
        diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
        return z3::verify_constraints(ctx, &pc, &sym_memory).is_ok();
    }

    return true;
}
