use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, Feasible};
use crate::smt_solver::SolverEnv;
use crate::symbolic::expression::{PathConstraints, SymExpression, SymType};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::{EvaluatedRefs, IntervalMap, SymRefType};

/// returns the symbolic expression rhs refers to, or None if we encounter a lazy object on an infeasible path
pub fn parse_rhs<'a, 'b>(
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    i: &mut IntervalMap,
    eval_refs: &mut EvaluatedRefs,
    solver: &mut SolverEnv,
    rhs: &'a Rhs,
) -> Result<Option<SymExpression>, Error> {
    match rhs {
        Rhs::AccessField(obj_name, field_name) => sym_memory
            .heap_access_object(
                pc,
                i,
                eval_refs,
                solver,
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
            pc,
            i,
            solver,
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
    pc: &mut PathConstraints,
    i: &mut IntervalMap,
    eval_refs: &mut EvaluatedRefs,
    solver: &mut SolverEnv,
    lhs: &'a Lhs,
    rhs: &'a Rhs,
) -> Result<Feasible, Error> {
    let mut var = match parse_rhs(sym_memory, pc, i, eval_refs, solver, rhs)? {
        Some(var) => var,
        _ => return Ok(false),
    };

    if solver.config.expression_evaluation {
        var = var.eval(i, Some(eval_refs));
    }

    match lhs {
        Lhs::Identifier(id) => {
            sym_memory.stack_insert(id.to_string(), var);
            Ok(true)
        }
        Lhs::AccessField(obj_name, field_name) => match sym_memory.heap_access_object(
            pc,
            i,
            eval_refs,
            solver,
            obj_name,
            field_name,
            Some(var),
        )? {
            Some(_) => Ok(true),
            None => Ok(false),
        },

        Lhs::AccessArray(arr_name, index) => sym_memory
            .heap_access_array(pc, i, solver, arr_name, index.clone(), Some(var))
            .map(|_| true),
    }
}

/// handles the assertion in the SEE (used in `assert` and `require` statements)
pub fn assert(
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    i: &mut IntervalMap,
    eval_refs: &EvaluatedRefs,
    solver: &mut SolverEnv,
    assertion: &Expression,
) -> Result<(), Error> {
    let mut sym_assertion = SymExpression::new(&sym_memory, assertion.clone());
    let config = &solver.config;

    // temporarly push assumption and infer updated intervalmap from pathconstraints
    if config.infer_size > 0 {
        sym_assertion = sym_assertion.eval(i, Some(eval_refs));
        pc.push_assumption(sym_assertion.clone());
        i.iterative_inference(&pc.conjunct(), config.infer_size);
        pc.pop();
    }

    // add (inferred  and / or simplified) assertion
    if config.expression_evaluation {
        let simple_assertion = sym_assertion.eval(i, Some(eval_refs));
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
    if config.expression_evaluation {
        constraints = constraints.eval(i, Some(eval_refs))
    };
    match constraints {
        SymExpression::Literal(Literal::Boolean(true)) => return Ok(()),
        _ => (),
    }

    match solver.verify_expr(&SymExpression::Not(Box::new(constraints)), sym_memory, i) {
        Some(model) => {
            return Err(Error::Verification(format!(
                "Following input violates one of the assertion:\n{:?}",
                model
            )))
        }
        None => Ok(()),
    }
}

/// handles the assume in the SEE (used in `assume`, `require` and `ensure` statements)
/// returns false if assumption is infeasible and can be dropped
/// prunes path using z3 if prune is set to true
pub fn assume(
    sym_memory: &mut SymMemory,
    pc: &mut PathConstraints,
    i: &mut IntervalMap,
    eval_refs: &EvaluatedRefs,
    prune: bool,
    solver: &mut SolverEnv,
    assumption: &Expression,
) -> bool {
    let mut sym_assumption = SymExpression::new(&sym_memory, assumption.clone());
    let config = &solver.config;

    // push assumption and infer updated intervalmap from pathconstraints
    if (config.infer_size > 0) {
        sym_assumption = sym_assumption.eval(i, Some(eval_refs));
        pc.push_assumption(sym_assumption.clone());
        i.iterative_inference(&pc.conjunct(), config.infer_size);
        pc.pop();
    }

    if config.expression_evaluation {
        let simple_assumption = sym_assumption.clone().eval(i, Some(eval_refs));

        match simple_assumption {
            SymExpression::Literal(Literal::Boolean(false)) => return false,
            SymExpression::Literal(Literal::Boolean(true)) => (),
            _ => pc.push_assumption(simple_assumption),
        };
    } else {
        pc.push_assumption(sym_assumption.clone());
    };

    let mut constraints = pc.conjunct();
    if config.expression_evaluation {
        constraints = constraints.eval(i, Some(eval_refs))
    };

    // return false if expression always evaluates to false
    match (prune, &constraints) {
        // if is unsatisfiable return false, if always satisfiable return true
        (_, SymExpression::Literal(Literal::Boolean(false))) => false,
        (_, SymExpression::Literal(Literal::Boolean(true))) => true,
        // if z3 finds a satisfying model return true, otherwise return false
        (true, _) => {
            let res = solver.verify_expr(&constraints, sym_memory, i);
            res.is_some()
        }
        // if either not proved or z3 is turned off we just return true and go on
        (false, _) => true,
    }
}
