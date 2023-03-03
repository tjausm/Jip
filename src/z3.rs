//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Config, Context, Model, SatResult, Solver};

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error};
use crate::symbolic::model::{PathConstraints, SymExpression, SymType};

//--------------//
// z3 bindings //
//-------------//

pub fn build_ctx() -> (Config, Context) {
    let z3_cfg = z3::Config::new();
    let ctx = z3::Context::new(&z3_cfg);
    (z3_cfg, ctx)
}

/// Combine pathconstraints to assert `pc ==> length > index` == always true
pub fn check_length<'ctx>(
    ctx: &'ctx Context,
    pc: &PathConstraints,
    length: &'ctx SymExpression,
    index: &'ctx SymExpression,
) -> Result<(), Error> {
    let length_gt_index = SymExpression::GT(Box::new(length.clone()), Box::new(index.clone()));

    // build new path constraints and get z3 bool
    let mut pc = pc.clone();
    pc.push_assertion(length_gt_index);
    let constraints = pc.combine_over_true();
    let length_gt_index = expr_to_bool(ctx, &constraints);

    match check_ast(ctx, &length_gt_index) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            return Err(Error::Verification(format!(
                "Following input could (potentially) accesses an array out of bounds:\n{:?}",
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
pub fn verify_constraints<'a>(
    ctx: &'a Context,
    path_constraints: &PathConstraints
) -> Result<(), Error> {
    //transform too z3 boolean
    let constraint_expr = path_constraints.combine_over_true();

    let constraints = expr_to_bool(&ctx, &constraint_expr);

    match check_ast(ctx, &constraints) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            return Err(Error::Verification(format!(
                "Following input violates one of the assertion:\n{:?}",
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
pub fn expression_unsatisfiable<'a>(
    ctx: &'a Context,
    expression: &SymExpression,
) -> bool {
    //negate assumption and try to find counter-example
    //no counter-example for !assumption means assumption is never true
    let assumption_ast = expr_to_bool(&ctx, expression).not();

    match check_ast(ctx, &assumption_ast) {
        (SatResult::Unsat, _) => true,
        _ => false,
    }
}

/// returns error if there exists a counterexample for given formula
/// in other words, given formula `a > b`, counterexample: a -> 0, b -> 0
fn check_ast<'ctx>(ctx: &'ctx Context, ast: &Bool) -> (SatResult, Option<Model<'ctx>>) {
    let solver = Solver::new(&ctx);
    solver.assert(&ast.not());
    (solver.check(), solver.get_model())
}

fn expr_to_int<'ctx, 'a>(
    ctx: &'ctx Context,
    expr: &'a SymExpression,
) -> Int<'ctx> {
    return unwrap_as_int(expr_to_dynamic(&ctx,  expr));
}

fn expr_to_bool<'ctx, 'a>(
    ctx: &'ctx Context,
    expr: &'a SymExpression,
) -> Bool<'ctx> {
    return unwrap_as_bool(expr_to_dynamic(&ctx,  expr));
}

fn expr_to_dynamic<'ctx, 'a>(
    ctx: &'ctx Context,
    expr: &'a SymExpression,
) -> Dynamic<'ctx> {
    match expr {
        SymExpression::And(l_expr, r_expr) => {
            let l = expr_to_bool(ctx,  l_expr);
            let r = expr_to_bool(ctx,  r_expr);

            return Dynamic::from(Bool::and(ctx, &[&l, &r]));
        }
        SymExpression::Or(l_expr, r_expr) => {
            let l = expr_to_bool(ctx,  l_expr);
            let r = expr_to_bool(ctx,  r_expr);

            return Dynamic::from(Bool::or(ctx, &[&l, &r]));
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let l = expr_to_bool(ctx,  l_expr);
            let r = expr_to_bool(ctx,  r_expr);

            return Dynamic::from(l.implies(&r));
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let l = expr_to_dynamic(ctx,  l_expr);
            let r = expr_to_dynamic(ctx,  r_expr);

            return Dynamic::from(l._eq(&r));
        }
        SymExpression::NE(l_expr, r_expr) => {
            let l = expr_to_dynamic(ctx,  l_expr);
            let r = expr_to_dynamic(ctx,  r_expr);

            return Dynamic::from(l._eq(&r).not());
        }
        SymExpression::LT(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(l.lt(&r));
        }
        SymExpression::GT(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(l.gt(&r));
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(l.ge(&r));
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(l.le(&r));
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(ast::Int::add(&ctx, &[&l, &r]));
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(ast::Int::sub(&ctx, &[&l, &r]));
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(ast::Int::mul(&ctx, &[&l, &r]));
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(l.div(&r));
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let l = expr_to_int(ctx,  l_expr);
            let r = expr_to_int(ctx,  r_expr);

            return Dynamic::from(l.modulo(&r));
        }
        SymExpression::Negative(expr) => {
            let e = expr_to_int(ctx,  expr);

            return Dynamic::from(e.unary_minus());
        }
        SymExpression::Not(expr) => {
            let expr = expr_to_bool(ctx,  expr);

            return Dynamic::from(expr.not());
        }
        SymExpression::FreeVariable(ty, id) => match ty {
            SymType::Bool => Dynamic::from(Bool::new_const(ctx, id.clone())),
            SymType::Int => Dynamic::from(Int::new_const(ctx, id.clone())),
            SymType::Ref(_) => Dynamic::from(Int::new_const(ctx, id.clone())),
        },
        SymExpression::Literal(Literal::Integer(n)) => Dynamic::from(ast::Int::from_i64(ctx, *n)),
        SymExpression::Literal(Literal::Boolean(b)) => Dynamic::from(ast::Bool::from_bool(ctx, *b)),
        SymExpression::Reference(_, r) => {
            Dynamic::from(ast::Int::from_u64(ctx, r.as_u64_pair().0))
        }
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



fn unwrap_as_bool(d: Dynamic) -> Bool {
    match d.as_bool() {
        Some(b) => b,
        None => panic_with_diagnostics(&format!("{} is not of type Bool", d), &()),
    }
}



fn unwrap_as_int(d: Dynamic) -> Int {
    match d.as_int() {
        Some(b) => b,
        None => panic_with_diagnostics(&format!("{} is not of type Int", d), &()),
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use z3::Config;

    #[test]
    fn test_solving() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let x = Int::new_const(&ctx, "x");
        let y = Int::new_const(&ctx, "y");
        let solver = Solver::new(&ctx);
        solver.assert(&x.gt(&y));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn manual_max() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let x = ast::Real::new_const(&ctx, "x");
        let y = ast::Real::new_const(&ctx, "y");
        let z = ast::Real::new_const(&ctx, "z");
        let x_plus_y = ast::Real::add(&ctx, &[&x, &y]);
        let x_plus_z = ast::Real::add(&ctx, &[&x, &z]);
        let substitutions = &[(&y, &z)];
        assert!(x_plus_y.substitute(substitutions) == x_plus_z);
    }
    #[test]
    fn exist_example() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);

        let x = ast::Int::new_const(&ctx, "x");
        let one = ast::Int::from_i64(&ctx, 1);

        let exists: ast::Bool = ast::exists_const(
            &ctx,
            &[&x],
            &[],
            &x._eq(&one), // hier gaat expression in
        )
        .try_into()
        .unwrap();

        println!("{:?}", exists);

        solver.assert(&exists.not());
    }
}
