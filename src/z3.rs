//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
use std::collections::HashSet;

use rsmt2::print::{IdentParser, ModelParser};
use rsmt2::{self, Solver, SmtRes};
use rustc_hash::FxHashSet;
use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error};
use crate::symbolic::model::{PathConstraints, SymExpression, SymType};

//---------------------//
// smt-solver bindings //
//--------------------//


#[derive(Clone, Copy)]
struct Parser;

impl<'a> IdentParser<String, String, & 'a str> for Parser {
    fn parse_ident(self, input: & 'a str) -> SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, input: & 'a str) -> SmtRes<String> {
        Ok("".to_string())
    }
}

impl<'a> ModelParser<String, String, String, & 'a str> for Parser {
    fn parse_value(
      self, input: & 'a str,
      ident: & String, _: & [ (String, String) ], _: & String,
    ) -> SmtRes<String> {
      Ok(format!("  {} -> {}\n", ident, input))
    }
}

pub enum SMTResult {
    Valid,
    Invalid(String)
}

/// Combine pathconstraints to assert `pc ==> length > index` == always true
pub fn check_length<'ctx>(
    pc: &PathConstraints,
    length: &'ctx SymExpression,
    index: &'ctx SymExpression,
) -> Result<(), Error> {
    todo!();
    let length_gt_index = SymExpression::GT(Box::new(length.clone()), Box::new(index.clone()));

    // build new path constraints and get z3 bool
    // let mut pc = pc.clone();
    // pc.push_assertion(length_gt_index);
    // let constraints = pc.combine_over_true();
    // let (l, fv_l)ength_gt_index = expr_to_bool(ctx, &constraints);

    // match verify_expr(ctx, &length_gt_index) {
    //     (SatResult::Unsat, _) => return Ok(()),
    //     (SatResult::Sat, Some(model)) => {
    //         return Err(Error::Verification(format!(
    //             "Following input could (potentially) accesses an array out of bounds:\n{:?}",
    //             model
    //         )));
    //     }
    //     _ => {
    //         return Err(Error::Verification(
    //             "Huh, verification gave an unkown result".to_string(),
    //         ))
    //     }
    // }
}

/// Combine the constraints in reversed order and check correctness using z3
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn verify_constraints<'a>(
    path_constraints: &PathConstraints
) -> Result<(), Error> {
    todo!();
    //transform too z3 boolean
    let constraint_expr = path_constraints.combine_over_true();

    // let constraints = expr_to_bool(&ctx, &constraint_expr);

    // match verify_expr(ctx, &constraints) {
    //     (SatResult::Unsat, _) => return Ok(()),
    //     (SatResult::Sat, Some(model)) => {
    //         return Err(Error::Verification(format!(
    //             "Following input violates one of the assertion:\n{:?}",
    //             model
    //         )));
    //     }
    //     _ => {
    //         return Err(Error::Verification(
    //             "Huh, verification gave an unkown result".to_string(),
    //         ))
    //     }
    // }
}
/// returns true if an expression can never be satisfied
pub fn expression_unsatisfiable<'a>(
    expression: &SymExpression,
) -> bool {
    todo!()
    //negate assumption and try to find counter-example
    //no counter-example for !assumption means assumption is never true
    // let assumption_ast = expr_to_bool(&ctx, expression).not();

    // match verify_expr(ctx, &assumption_ast) {
    //     (SatResult::Unsat, _) => true,
    //     _ => false,
    // }
}

/// returns error if there exists a counterexample for given formula
/// in other words, given formula `a > b`, counterexample: a -> 0, b -> 0
fn verify_expr<'ctx>(expr: &SymExpression) -> SMTResult {
    let mut solver = rsmt2::Solver::default_z3(()).unwrap();

    let (expr_str, fvs) = expr_to_str(expr);
    for fv in fvs{
        match fv {
            (SymType::Bool, id) => todo!(),
            (SymType::Int, id) => todo!(),
            (SymType::Ref(_), id) => todo!()
        }
    }

    solver.assert(expr_str);

    // either return valid or get model and format it
   if solver.check_sat().unwrap() {
         SMTResult::Valid
   } else {
        let model = solver.get_model().unwrap();
        let model_str = "";
        for var in model {
            model_str = &format!("{}{}\n", model_str, var.3);
        }
        SMTResult::Invalid(model_str.to_owned())
   }

}


/// returns an expression as RSMT parseable string
/// with a set of all it's free variables  
fn expr_to_str<'a>(
    expr: &'a SymExpression,
) -> (String, FxHashSet<(SymType, String)>) {

    match expr {
        SymExpression::And(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            return (format!("(and {} {})", l, r), fv_l);
        }
        SymExpression::Or(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(or {} {})", l, r), fv_l);
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(=> {} {})", l, r), fv_l);
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(= {} {})", l, r), fv_l);
        }
        SymExpression::NE(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(distinct {} {})", l, r), fv_l);
        }
        SymExpression::LT(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(< {} {})", l, r), fv_l);
        }
        SymExpression::GT(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(> {} {})", l, r), fv_l);
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(>= {} {})", l, r), fv_l);
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(<= {} {})", l, r), fv_l);
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(+ {} {})", l, r), fv_l);
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(- {} {})", l, r), fv_l);
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(* {} {})", l, r), fv_l);
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(/ {} {})", l, r), fv_l);
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let (l, fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

fv_l.extend(fv_r);return (format!("(% {} {})", l, r), fv_l);
        }
        SymExpression::Negative(expr) => {
            let (expr, fv) = expr_to_str(expr);

        return (format!("(- {})", expr), fv);
        }
        SymExpression::Not(expr) => {
            let (expr, fv) = expr_to_str(expr);

    return (format!("(! {})", expr), fv);
        }
        SymExpression::FreeVariable(ty, id) =>{ 
            let fv = FxHashSet::default();
            fv.insert((ty.clone(), id.clone()));
            (format!("({})", id), fv)},
        SymExpression::Literal(Literal::Integer(n)) => (format!("{}", n), FxHashSet::default()),
        SymExpression::Literal(Literal::Boolean(b)) => (format!("{}", b), FxHashSet::default()),
        SymExpression::Reference(_, r) => (format!("{}", r.as_u64_pair().0), FxHashSet::default()),
        otherwise => {
            panic_with_diagnostics(
                &format!(
                    "Expressions of the form {:?} are not parseable to a z3 ast",
                    otherwise
                ),
                &()
            );
        }
    }
}