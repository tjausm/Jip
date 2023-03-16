use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Diagnostics};
use crate::shared::{Config, Error};
use crate::smt_solver::Solver;
use crate::symbolic::expression::{PathConstraints, SymExpression};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::Ranges;

/// returns the symbolic expression rhs refers to
pub fn parse_rhs<'a, 'b>(
    sym_memory: &mut SymMemory,
    pc: &PathConstraints,
    ranges: &Ranges,
    solver: &mut Solver,
    diagnostics: &mut Diagnostics,
    rhs: &'a Rhs,
) -> Result<SymExpression, Error> {
    match rhs {
        Rhs::AccessField(obj_name, field_name) => Ok(sym_memory
            .heap_access_object(obj_name, field_name, None)
            .clone()),

        // generate reference, build arrayname from said reference, insert array into heap and return reference
        Rhs::NewArray(ty, len) => {
            let size_expr = SymExpression::new(&sym_memory, len.clone());
            let arr = sym_memory.init_array(ty.clone(), size_expr);
            let r = sym_memory.heap_insert(None, arr);
            Ok(SymExpression::Reference(ty.clone(), r))
        }

        Rhs::AccessArray(arr_name, index) => sym_memory.heap_access_array(
            &pc,
            ranges,
            solver,
            diagnostics,
            arr_name,
            index.clone(),
            None,
        ),

        Rhs::Expression(expr) => Ok(SymExpression::new(&sym_memory, expr.clone())),
        _ => panic_with_diagnostics(
            &format!("Rhs of the form {:?} should not be in the cfg", rhs),
            &sym_memory,
        ),
    }
}

// gets type of lhs, parses expression on rhs and assign value of rhs to lhs on stack / heap
pub fn lhs_from_rhs<'a>(
    sym_memory: &mut SymMemory,
    pc: &PathConstraints,
    ranges: &Ranges,
    solver: &mut Solver,
    diagnostics: &mut Diagnostics,
    config: Config,
    lhs: &'a Lhs,
    rhs: &'a Rhs,
) -> Result<(), Error> {
    let var = parse_rhs(sym_memory, pc, ranges, solver, diagnostics, rhs)?;
    match lhs {
        Lhs::Identifier(id) => sym_memory.stack_insert(id, var),
        Lhs::AccessField(obj_name, field_name) => {
            sym_memory.heap_access_object(obj_name, field_name, Some(var));
        }
        Lhs::AccessArray(arr_name, index) => {
            sym_memory.heap_access_array(
                &pc,
                &ranges,
                solver,
                diagnostics,
                arr_name,
                index.clone(),
                Some(var),
            )?;
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
            (Some((Type::ArrayType(ty), arg_id)), Some(expr)) => match expr {
                Expression::Identifier(param_id) => match sym_memory.stack_get(param_id) {
                    Some(SymExpression::Reference(ty, r)) => {
                        variables.push((arg_id, SymExpression::Reference(ty, r)))
                    }
                    _ => return err(&format!("{:?}[]", ty), arg_id, expr),
                },
                _ => return err(&format!("{:?}[]", ty), arg_id, expr),
            },
            (Some((Type::ClassType(class), arg_id)), Some(expr)) => match expr {
                Expression::Identifier(param_id) => match sym_memory.stack_get(param_id) {
                    Some(SymExpression::Reference(ty, r)) => {
                        variables.push((arg_id, SymExpression::Reference(ty, r)))
                    }
                    _ => return err(class, arg_id, expr),
                },
                _ => return err(class, arg_id, expr),
            },
            (Some((_, arg_id)), Some(expr)) => {
                variables.push((arg_id, SymExpression::new(&sym_memory, expr.clone())));
            }
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
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    ranges: &mut Ranges,
    config: Config,
    solver: &mut Solver,
    assertion: &Expression,
    diagnostics: &mut Diagnostics,
) -> Result<(), Error> {
    let mut sym_assertion = SymExpression::new(&sym_memory, assertion.clone());

    // update ranges
    if config.infer_size {
        ranges.infer_ranges(&sym_assertion);
    }

    // add (inferred  and / orsimplified) assertion
    if config.simplify {
        let simple_assertion = sym_assertion.simplify();
        //let simple_assertion = assertion;
        match simple_assertion {
            SymExpression::Literal(Literal::Boolean(true)) => (),
            _ => pc.push_assertion(simple_assertion),
        }
    } else {
        pc.push_assertion(sym_assertion);
    };

    // calculate (inferred and / or simplified) constraints
    let mut constraints = pc.combine_over_true();
    if config.infer_size {
        constraints = ranges.substitute_sizeof(constraints);
    };
    if config.simplify {
        constraints = constraints.simplify()
    };
    match constraints {
        SymExpression::Literal(Literal::Boolean(true)) => return Ok(()),
        _ => (),
    }

    // if we have not solved by now, invoke z3
    diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
    solver.verify_constraints(&pc)
}

/// handles the assume in the SEE (used in `assume`, `require` and `ensure` statements)
/// returns false if assumption is infeasible and can be dropped
pub fn assume(
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    ranges: &mut Ranges,
    config: Config,
    use_z3: bool,
    solver: &mut Solver,
    assumption: &Expression,
    diagnostics: &mut Diagnostics,
) -> bool {
    let sym_assumption = SymExpression::new(&sym_memory, assumption.clone());

    if config.infer_size {
        ranges.infer_ranges(&sym_assumption);
    }

    if config.simplify {
        let simple_assumption = sym_assumption.simplify();

        //  let z3_subt = smt_solver::expression_unsatisfiable(ctx, &subt_assumption, sym_memory);
        //  let z3_simple = smt_solver::expression_unsatisfiable(ctx, &simple_assumption, sym_memory);
        //  println!("\nsubt_assumption: {:?}\n z3_subt: {:?}\n simplified: {:?}\n z3_simplified: {:?}\n", subt_assumption, z3_subt, simple_assumption, z3_simple);

        match simple_assumption {
            SymExpression::Literal(Literal::Boolean(false)) => return false,
            SymExpression::Literal(Literal::Boolean(true)) => (),
            _ => pc.push_assumption(simple_assumption),
        };
    } else {
        pc.push_assumption(sym_assumption.clone());
    };

    let mut constraints = pc.conjunct();
    if config.infer_size {
        constraints = ranges.substitute_sizeof(constraints);
    };
    if config.simplify {
        constraints = constraints.simplify()
    };

    // return false if expression always evaluates to false
    match (use_z3, constraints) {
        // if is unsatisfiable return false
        (_, SymExpression::Literal(Literal::Boolean(false))) => return false,
        // if z3 confirms it is unsatisfiable, we must return false again
        (true, _) => {
            diagnostics.z3_invocations = diagnostics.z3_invocations + 1;
            !solver.expression_unsatisfiable(&pc.conjunct())
            
        }
        // if either not proved or z3 is turned off we just return true and go on
        (false, _) => true
    }


}
