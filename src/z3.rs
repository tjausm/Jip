//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error};
use crate::symbolic::model::{PathConstraints, SymExpression, SymType};
use rsmt2::print::{IdentParser, ModelParser};
use rsmt2::{self, SmtRes, Solver};
use rustc_hash::FxHashSet;

//---------------------//
// smt-solver bindings //
//--------------------//

#[derive(Clone, Copy)]
struct Parser;

impl<'a> IdentParser<String, String, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<String> {
        Ok("".to_string())
    }
}

impl<'a> ModelParser<String, String, String, &'a str> for Parser {
    fn parse_value(
        self,
        input: &'a str,
        ident: &String,
        _: &[(String, String)],
        _: &String,
    ) -> SmtRes<String> {
        Ok(format!("  {} -> {}  ", ident, input))
    }
}

#[derive(PartialEq)]
pub enum SmtResult {
    Unsat,
    Sat(String),
}

/// Combine pathconstraints to assert `pc ==> length > index` == always true
pub fn check_length<'ctx>(
    pc: &PathConstraints,
    length: &'ctx SymExpression,
    index: &'ctx SymExpression,
) -> Result<(), Error> {
    //append length > index to PathConstraints and try to falsify
    let length_gt_index = SymExpression::GT(Box::new(length.clone()), Box::new(index.clone()));
    let mut pc = pc.clone();
    pc.push_assertion(length_gt_index);
    let constraints = pc.combine_over_true();

    match verify_expr(&SymExpression::Not(Box::new(constraints))) {
        (SmtResult::Unsat) => return Ok(()),
        (SmtResult::Sat(model)) => {
            return Err(Error::Verification(format!(
                "Following input could (potentially) accesses an array out of bounds:\n{}",
                model
            )));
        }
        _ => {
            return Err(Error::Verification(
                "Huh, verification gave an unkown result".to_string(),
            ))
        }
    }
}

/// Combine the constraints in reversed order and check correctness using z3
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn verify_constraints<'a>(path_constraints: &PathConstraints) -> Result<(), Error> {
    //negate assumption and try to find counter-example
    let constraints = path_constraints.combine_over_true();

    match verify_expr(&SymExpression::Not(Box::new(constraints))) {
        (SmtResult::Unsat) => return Ok(()),
        (SmtResult::Sat(model)) => {
            return Err(Error::Verification(format!(
                "Following input violates one of the assertion:\n{}",
                model
            )));
        }
        _ => {
            return Err(Error::Verification(
                "Huh, verification gave an unkown result".to_string(),
            ))
        }
    }
}
/// returns true if an expression can never be satisfied
pub fn expression_unsatisfiable<'a>(expression: &SymExpression) -> bool {
    //negate assumption and try to find counter-example
    //no counter-example for !assumption means assumption is never true
    match verify_expr(expression) {
        SmtResult::Unsat => true,
        _ => false,
    }
}

/// returns error if there exists a counterexample for given formula
/// in other words, given formula `a > b`, counterexample: a -> 0, b -> 0
fn verify_expr<'ctx>(expr: &SymExpression) -> SmtResult {
    let mut solver = rsmt2::Solver::default_z3(Parser).unwrap();

    let (expr_str, fvs) = expr_to_str(expr);
    for fv in fvs {
        match fv {
            (SymType::Bool, id) => solver.declare_const(id, "Bool").unwrap(),
            (SymType::Int, id) => solver.declare_const(id, "Int").unwrap(),
            (SymType::Ref(_), id) => solver.declare_const(id, "Int").unwrap(),
        }
    }

    solver.assert(expr_str.clone());

    //either return Sat(formated model) or Unsat
    if solver.check_sat().unwrap() {
        let model = solver.get_model().unwrap();
        let mut model_str = "".to_string();
        for var in model {
            model_str.push_str(&var.3);
        }

        // println!("{:?}", expr);
        // println!("{}", expr_str);
        // println!("{}", model_str);
        SmtResult::Sat(model_str.to_owned())
    }else{
        SmtResult::Unsat
    }
}

/// returns an expression as RSMT parseable string
/// with a set of all it's free variables  
fn expr_to_str<'a>(expr: &'a SymExpression) -> (String, FxHashSet<(SymType, String)>) {
    match expr {
        SymExpression::And(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            return (format!("(and {} {})", l, r), fv_l);
        }
        SymExpression::Or(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(or {} {})", l, r), fv_l);
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(=> {} {})", l, r), fv_l);
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(= {} {})", l, r), fv_l);
        }
        SymExpression::NE(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(distinct {} {})", l, r), fv_l);
        }
        SymExpression::LT(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(< {} {})", l, r), fv_l);
        }
        SymExpression::GT(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(> {} {})", l, r), fv_l);
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(>= {} {})", l, r), fv_l);
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(<= {} {})", l, r), fv_l);
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(+ {} {})", l, r), fv_l);
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(- {} {})", l, r), fv_l);
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(* {} {})", l, r), fv_l);
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(/ {} {})", l, r), fv_l);
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let (l, mut fv_l) = expr_to_str(l_expr);
            let (r, fv_r) = expr_to_str(r_expr);

            fv_l.extend(fv_r);
            return (format!("(mod {} {})", l, r), fv_l);
        }
        SymExpression::Negative(expr) => {
            let (expr, fv) = expr_to_str(expr);

            return (format!("(- {})", expr), fv);
        }
        SymExpression::Not(expr) => {
            let (expr, fv) = expr_to_str(expr);

            return (format!("(not {})", expr), fv);
        }
        SymExpression::FreeVariable(ty, id) => {
            let mut fv = FxHashSet::default();
            fv.insert((ty.clone(), id.clone()));
            (format!("{}", id), fv)
        }
        SymExpression::Literal(Literal::Integer(n)) => (format!("{}", n), FxHashSet::default()),
        SymExpression::Literal(Literal::Boolean(b)) => (format!("{}", b), FxHashSet::default()),
        SymExpression::Reference(_, r) => (format!("{}", r.as_u64_pair().0), FxHashSet::default()),
        otherwise => {
            panic_with_diagnostics(
                &format!(
                    "Expressions of the form {:?} are not parseable to a z3 ast",
                    otherwise
                ),
                &(),
            );
        }
    }
}
#[cfg(test)]
mod tests {

    use rustc_hash::FxHashMap;

    use crate::symbolic::memory::SymMemory;

    use super::*;
    lalrpop_mod!(pub parser);

    #[test]
    fn test_solving() {
        let p = parser::VerificationExpressionParser::new();
        let expr = p
            .parse("!(((1 >= 0) && (2 > 0)) ==> ((((1 + 2) >= 1) && ((1 + 2) >= 1)) && true))")
            .unwrap();

        let se = SymExpression::new(&FxHashMap::default(), &SymMemory::new(), expr);
        let sat = verify_expr(&se);

        assert!(sat == SmtResult::Unsat);
        println!("end");
    }
}
