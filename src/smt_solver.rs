//! Encode expressions into the smt-lib format to test satisfiability using the chosen backend

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, SolverType, Config};
use crate::symbolic::expression::{PathConstraints, SymExpression, SymType};
use crate::symbolic::ref_values::{ArrSize, Boundary};
use rsmt2::print::ModelParser;
use rsmt2::{self, SmtConf, SmtRes};
use rustc_hash::FxHashSet;

#[derive(PartialEq)]
pub enum SmtResult {
    Unsat,
    Sat(String),
}

#[derive(Clone, Copy)]
struct Parser;

impl<'a> rsmt2::print::IdentParser<String, String, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> rsmt2::SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, _: &'a str) -> rsmt2::SmtRes<String> {
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
        Ok(format!("{} -> {}", ident, input))
    }
}

pub struct Solver {
    s: rsmt2::Solver<Parser>,
    pub config: Config
}

impl Solver {
    /// Creates a new solver using the configured backend.
    /// For both Yices and Cvc we pas a set of flags to make them work with the rust interface
    pub fn new(config: &Config) -> Solver {
        let conf = match &config.solver_type {
            SolverType::Z3(arg) => SmtConf::z3(arg),
            SolverType::Yices2(arg) => {
                let mut conf = SmtConf::yices_2(arg);
                conf.option("--incremental"); //add support for scope popping and pushing from solver
                conf.option("--interactive"); //add support for scope popping and pushing from solvercargo
                conf
            }
            SolverType::CVC4(arg) => {
                let mut conf = SmtConf::cvc4(arg);
                conf.option("--incremental"); //add support for scope popping and pushing from solver
                conf.option("--rewrite-divk"); //add support for `div` and `mod` operators (not working)
                conf
            }
            SolverType::Default => SmtConf::default_z3(),
        };

        let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
        solver.set_option(":print-success", "false").unwrap(); //turn off automatic succes printing in yices2
        solver.produce_models().unwrap();
        solver.set_logic(rsmt2::Logic::QF_NIA).unwrap(); //set logic to quantifier free non-linear arithmetics
        Solver { s: solver, config: config.clone() }
    }

    /// Combine pathconstraints to assert `pc ==> length > index` == always true
    pub fn verify_array_access<'a>(
        &mut self,
        pc: &PathConstraints,
        size_of: &'a SymExpression,
        index: &'a SymExpression,
    ) -> Result<(), Error> {
        //append length > index to PathConstraints and try to falsify
        let length_gt_index = SymExpression::GT(Box::new(size_of.clone()), Box::new(index.clone()));
        let mut pc = pc.clone();
        pc.push_assertion(length_gt_index);
        let constraints = pc.combine_over_true();

        match self.verify_expr(&SymExpression::Not(Box::new(constraints))) {
            SmtResult::Unsat => return Ok(()),
            SmtResult::Sat(model) => {
                return Err(Error::Verification(format!(
                    "Following input could (potentially) accesses an array out of bounds:\n{}",
                    model
                )));
            }
        }
    }

    /// given a set of pathconstraints combined over true, method returns a counterexample to violate them if there is one
    /// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
    pub fn verify_constraints<'a>(&mut self, constraints: SymExpression) -> Result<(), Error> {
        match self.verify_expr(&SymExpression::Not(Box::new(constraints))) {
            SmtResult::Unsat => return Ok(()),
            SmtResult::Sat(model) => {
                return Err(Error::Verification(format!(
                    "Following input violates one of the assertion:\n{}",
                    model
                )));
            }
        }
    }
    /// returns true if an expression can never be satisfied
    pub fn expression_unsatisfiable<'a>(&mut self, expression: &SymExpression) -> bool {
        //negate assumption and try to find counter-example
        //no counter-example for !assumption means assumption is never true
        match self.verify_expr(expression) {
            SmtResult::Unsat => true,
            _ => false,
        }
    }

    /// returns error if there exists a counterexample for given formula
    /// in other words, given formula `a > b`, counterexample: a -> 0, b -> 0
    fn verify_expr(&mut self, expr: &SymExpression) -> SmtResult {
        self.s.push(1).unwrap();

        let (expr_str, fvs, assertions) = expr_to_str(expr);
        for fv in fvs {
            match fv {
                (SymType::Bool, id) => self.s.declare_const(id, "Bool").unwrap(),
                (SymType::Int, id) => self.s.declare_const(id, "Int").unwrap(),
                (SymType::Ref(_), id) => self.s.declare_const(id, "Int").unwrap(),
            }
        }
        for assertion in assertions {
            self.s.assert(assertion).unwrap();
        }

        self.s.assert(expr_str.clone()).unwrap();
        let satisfiable = match self.s.check_sat() {
            Ok(b) => b,
            Err(err) => panic_with_diagnostics(
                &format!(
                    "Received backend error: {}\nWhile evaluating formula '{:?}'",
                    err, expr_str
                ),
                &(),
            ),
        };

        let model = self.s.get_model();
        self.s.pop(1).unwrap();
        //either return Sat(formated model) or Unsat
        if satisfiable {
            let mut model_str = "".to_string();
            match model {
                Ok(model) => {
                    for var in model {
                        model_str = format!("{}{}\n", model_str, var.3);
                    }
                }
                Err(err) => model_str = format!("Error during model parsing: {:?}", err),
            };

            SmtResult::Sat(model_str.to_owned())
        } else {
            SmtResult::Unsat
        }
    }
}

/// returns an expression as RSMT parseable string
/// with a set of all it's free variables  
fn expr_to_str<'a>(
    expr: &'a SymExpression,
) -> (String, FxHashSet<(SymType, String)>, FxHashSet<String>) {
    match expr {
        SymExpression::And(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(and {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Or(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(or {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(=> {} {})", l, r), fv_l, a_l);
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::NE(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(distinct {} {})", l, r), fv_l, a_l);
        }
        SymExpression::LT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(< {} {})", l, r), fv_l, a_l);
        }
        SymExpression::GT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(> {} {})", l, r), fv_l, a_l);
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(>= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(<= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(+ {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(- {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(* {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(div {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_str(l_expr);
            let (r, fv_r, a_r) = expr_to_str(r_expr);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(mod {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Negative(expr) => {
            let (expr, fv, a) = expr_to_str(expr);

            return (format!("(- {})", expr), fv, a);
        }
        SymExpression::Not(expr) => {
            let (expr, fv, a) = expr_to_str(expr);

            return (format!("(not {})", expr), fv, a);
        }
        SymExpression::FreeVariable(ty, id) => {
            let mut fv = FxHashSet::default();
            fv.insert((ty.clone(), id.clone()));
            (format!("{}", id), fv, FxHashSet::default())
        }
        SymExpression::SizeOf(_, _, size_expr, Some(s)) => match s {
            ArrSize::Point(n) => expr_to_str(&SymExpression::Literal(Literal::Integer(*n))),
            ArrSize::Range(Boundary::Known(min), Boundary::Known(max)) => {
                let (expr, fv, mut a) = expr_to_str(size_expr);
                a.insert(format!("(<= {} {})", min, expr));
                a.insert(format!("(<= {} {})", expr, max));
                return (expr, fv, a);
            }
            ArrSize::Range(Boundary::Known(min), _) => {
                let (expr, fv, mut a) = expr_to_str(size_expr);
                a.insert(format!("(<= {} {})", min, expr));
                return (expr, fv, a);
            }
            ArrSize::Range(_, Boundary::Known(max)) => {
                let (expr, fv, mut a) = expr_to_str(size_expr);
                a.insert(format!("(<= {} {})", expr, max));
                return (expr, fv, a);
            }
            _ => expr_to_str(size_expr),
        },
        SymExpression::SizeOf(_, _, size_expr, None) => expr_to_str(size_expr),
        SymExpression::Literal(Literal::Integer(n)) => {
            (format!("{}", n), FxHashSet::default(), FxHashSet::default())
        }
        SymExpression::Literal(Literal::Boolean(b)) => {
            (format!("{}", b), FxHashSet::default(), FxHashSet::default())
        }
        SymExpression::Reference(r) => (
            format!("{}", r.as_u64_pair().0),
            FxHashSet::default(),
            FxHashSet::default(),
        ),

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


    use crate::symbolic::memory::SymMemory;

    use super::*;
    lalrpop_mod!(pub parser);

    #[test]
    fn test_solving() {
        let p = parser::VerificationExpressionParser::new();
        let expr = p
            .parse("!(((1 >= 0) && (2 > 0)) ==> ((((1 + 2) >= 1) && ((1 + 2) >= 1)) && true))")
            .unwrap();

        //let se = SymExpression::new(&SymMemory::new(Program(vec![])), expr);
        // todo!()
        // let sat = verify_expr(&se);

        // assert!(sat == SmtResult::Unsat);
        // println!("end");
    }
}
