use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Diagnostics, Feasible};
use crate::shared::{Config, Error};
use crate::smt_solver::Solver;
use crate::symbolic::expression::{PathConstraints, SymExpression, SymType};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::{ArrSizes, SymRefType, EvaluatedRefs};

/// returns the symbolic expression rhs refers to, or None if we encounter a lazy object on an infeasible path
pub fn parse_rhs<'a, 'b>(
    sym_memory: &mut SymMemory,
    pc: &PathConstraints,
    arr_sizes: &mut ArrSizes,
    eval_refs: &mut EvaluatedRefs,
    solver: &mut Solver,
    diagnostics: &mut Diagnostics,
    rhs: &'a Rhs,
) -> Result<Option<SymExpression>, Error> {
    match rhs {
        Rhs::AccessField(obj_name, field_name) => sym_memory
            .heap_access_object(
                pc,
                arr_sizes,
                eval_refs,
                solver,
                diagnostics,
                obj_name,
                field_name,
                None,
            )
            ,

        // generate reference, build arrayname from said reference, insert array into heap and return reference
        Rhs::NewArray(ty, len) => {
            let sym_ty = match ty {
                Type::Int => SymType::Int,
                Type::Bool => SymType::Bool,
                Type::Class(id) => SymType::Ref(SymRefType::Object(id.clone())),
                Type::Array(_) => todo!("2+ dimensional arrays are not yet supported"),
                Type::Void => {
                    panic_with_diagnostics("Can't initialize an an array of type void", &sym_memory)
                }
            };
            let size_expr = SymExpression::new(&sym_memory, len.clone());
            let arr = sym_memory.init_array(sym_ty, size_expr, false);
            let r = sym_memory.heap_insert(None, arr);
            Ok(Some(SymExpression::Reference(r)))
        }

        Rhs::AccessArray(arr_name, index) => sym_memory.heap_access_array(
            &pc,
            arr_sizes,
            solver,
            diagnostics,
            arr_name,
            index.clone(),
            None,
        ).map(|v| Some(v)),

        Rhs::Expression(expr) => Ok(Some(SymExpression::new(&sym_memory, expr.clone()))),
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
    arr_sizes: &mut ArrSizes,
    eval_refs: &mut EvaluatedRefs,
    solver: &mut Solver,
    diagnostics: &mut Diagnostics,
    lhs: &'a Lhs,
    rhs: &'a Rhs,
) -> Result<Feasible, Error> {
    let var = match parse_rhs(sym_memory, pc, arr_sizes, eval_refs, solver, diagnostics, rhs)? {
        Some(var) => var,
        _ => return Ok(false),
    };
    match lhs {
        Lhs::Identifier(id) => {
            sym_memory.stack_insert(id.to_string(), var);
            Ok(true)
        }
        Lhs::AccessField(obj_name, field_name) => match sym_memory.heap_access_object(
            pc,
            arr_sizes,
            eval_refs,
            solver,
            diagnostics,
            obj_name,
            field_name,
            Some(var),
        )? {
            Some(_) => Ok(true),
            None => Ok(false),
        },

        Lhs::AccessArray(arr_name, index) => sym_memory
            .heap_access_array(
                &pc,
                arr_sizes,
                solver,
                diagnostics,
                arr_name,
                index.clone(),
                Some(var),
            )
            .map(|_| true),
    }
}

/// handles the assertion in the SEE (used in `assert` and `require` statements)
pub fn assert(
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    arr_sizes: &mut ArrSizes,
    config: &Config,
    solver: &mut Solver,
    assertion: &Expression,
    diagnostics: &mut Diagnostics,
) -> Result<(), Error> {
    let sym_assertion = SymExpression::new(&sym_memory, assertion.clone());

    // update arr_sizes
    if config.infer_size {
        arr_sizes.update_inference(sym_assertion.clone());
    }

    // add (inferred  and / orsimplified) assertion
    if config.simplify {
        let simple_assertion = sym_assertion.simplify(Some(&arr_sizes));
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
    if config.simplify {
        constraints = constraints.simplify(Some(arr_sizes))
    };
    match constraints {
        SymExpression::Literal(Literal::Boolean(true)) => return Ok(()),
        _ => (),
    }
    // if we have not solved by now, invoke z3
    diagnostics.z3_calls = diagnostics.z3_calls + 1;

    solver.verify_constraints(constraints)
}

/// handles the assume in the SEE (used in `assume`, `require` and `ensure` statements)
/// returns false if assumption is infeasible and can be dropped
pub fn assume(
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    arr_sizes: &mut ArrSizes,
    config: &Config,
    use_z3: bool,
    solver: &mut Solver,
    assumption: &Expression,
    diagnostics: &mut Diagnostics,
) -> bool {
    let sym_assumption = SymExpression::new(&sym_memory, assumption.clone());

    // update sizes if it's turned on
    if config.infer_size {
        arr_sizes.update_inference(sym_assumption.clone());
    }
    if config.simplify {
        let simple_assumption = sym_assumption.simplify(Some(arr_sizes));

        match simple_assumption {
            SymExpression::Literal(Literal::Boolean(false)) => return false,
            SymExpression::Literal(Literal::Boolean(true)) => (),
            _ => pc.push_assumption(simple_assumption),
        };
    } else {
        pc.push_assumption(sym_assumption.clone());
    };

    let mut constraints = pc.conjunct();
    if config.simplify {
        constraints = constraints.simplify(Some(arr_sizes))
    };

    // return false if expression always evaluates to false
    match (use_z3, &constraints) {
        // if is unsatisfiable return false
        (_, SymExpression::Literal(Literal::Boolean(false))) => return false,
        // if z3 confirms it is unsatisfiable, we must return false again
        (true, _) => {
            diagnostics.z3_calls = diagnostics.z3_calls + 1;
            !solver.expression_unsatisfiable(&constraints).is_ok()
        }
        // if either not proved or z3 is turned off we just return true and go on
        (false, _) => true,
    }
}
