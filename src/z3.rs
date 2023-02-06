//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
//!

use std::rc::Rc;
use std::{fmt, path};
use uuid::Uuid;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Config, Context, SatResult, Solver};

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error};
use crate::sym_model::{PathConstraints, SymExpression, SymMemory};

//--------------//
// z3 bindings //
//-------------//

/// Combine the constraints in reversed order and check correctness using z3
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn verify_constraints<'a>(
    path_constraints: &PathConstraints,
    sym_memory: &SymMemory<'a>,
) -> Result<(), Error> {
    //initialise fresh context
    let z3_cfg = Config::new();
    let ctx = Context::new(&z3_cfg);

    // combine constraints over true
    let lit_true = Box::new(Expression::Literal(Literal::Boolean(true)));
    let constraint_expr = match path_constraints.get_constraints() {
        Expression::Implies(l_expr, r_expr) => {
            Expression::Implies(l_expr, Box::new(Expression::And(r_expr, lit_true)))
        }
        Expression::And(l_expr, r_expr) => {
            Expression::And(l_expr, Box::new(Expression::And(r_expr, lit_true)))
        }
        otherwise => otherwise,
    };

    //transform too z3 boolean
    let constraints = expr_to_bool(&ctx, sym_memory, &constraint_expr);

    println!("{}", constraints.not());

    let solver = Solver::new(&ctx);
    solver.assert(&constraints.not());
    let result = solver.check();
    let model = solver.get_model();

    //println!("{:?}", model);

    match (result, model) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            return Err(Error::Verification(format!(
                "Following counter-example was found:\n{:?}",
                model
            )));
        }
        _ => {
            return Err(Error::Verification(
                "Huh, verification gave an unkown result".to_string(),
            ))
        }
    };
}

fn expr_to_int<'ctx>(
    ctx: &'ctx Context,
    env: &SymMemory<'ctx>,
    expr: &'ctx Expression,
) -> Int<'ctx> {
    return unwrap_as_int(expr_to_dynamic(&ctx, Rc::new(env), expr));
}

fn expr_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: &SymMemory<'ctx>,
    expr: &'ctx Expression,
) -> Bool<'ctx> {
    return unwrap_as_bool(expr_to_dynamic(&ctx, Rc::new(env), expr));
}

fn expr_to_dynamic<'ctx, 'a>(
    ctx: &'ctx Context,
    sym_memory: Rc<&SymMemory<'a>>,
    expr: &'a Expression,
) -> Dynamic<'ctx> {
    match expr {
        Expression::Exists(id, expr) => {
            let l = Int::fresh_const(ctx, id);
            let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, expr));

            return Dynamic::from(ast::exists_const(&ctx, &[&l], &[], &r));
        }
        Expression::And(l_expr, r_expr) => {
            let l = unwrap_as_bool(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(Bool::and(ctx, &[&l, &r]));
        }
        Expression::Or(l_expr, r_expr) => {
            let l = unwrap_as_bool(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(Bool::or(ctx, &[&l, &r]));
        }
        Expression::Implies(l_expr, r_expr) => {
            let l = unwrap_as_bool(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.implies(&r));
        }
        Expression::EQ(l_expr, r_expr) => {
            let l = expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_dynamic(ctx, sym_memory, r_expr);

            return Dynamic::from(l._eq(&r));
        }
        Expression::NE(l_expr, r_expr) => {
            let l = expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_dynamic(ctx, sym_memory, r_expr);

            return Dynamic::from(l._eq(&r).not());
        }
        Expression::LT(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.lt(&r));
        }
        Expression::GT(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.gt(&r));
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.ge(&r));
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.le(&r));
        }
        Expression::Plus(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(ast::Int::add(&ctx, &[&l, &r]));
        }
        Expression::Minus(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(ast::Int::sub(&ctx, &[&l, &r]));
        }
        Expression::Multiply(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(ast::Int::mul(&ctx, &[&l, &r]));
        }
        Expression::Divide(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.div(&r));
        }
        Expression::Mod(l_expr, r_expr) => {
            let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
            let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

            return Dynamic::from(l.modulo(&r));
        }
        Expression::Negative(expr) => {
            let e = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), expr));

            return Dynamic::from(e.unary_minus());
        }
        Expression::Not(expr) => {
            let expr = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, expr));

            return Dynamic::from(expr.not());
        }
        // type variable using stack or substitute one level deep??
        Expression::Identifier(id) => match sym_memory.stack_get(id) {
            Some(SymExpression::Bool(_)) => Dynamic::from(Bool::new_const(ctx, id.clone())),
            Some(SymExpression::Int(_)) => Dynamic::from(Int::new_const(ctx, id.clone())),
            Some(sym_expr) => panic_with_diagnostics(
                &format!("{:?} is not parseable to a z3 ast", sym_expr),
                &sym_memory,
            ),
            None => panic_with_diagnostics(&format!("{} is undeclared", id), &sym_memory),
        },
        Expression::Literal(Literal::Integer(n)) => Dynamic::from(ast::Int::from_i64(ctx, *n)),
        Expression::Literal(Literal::Boolean(b)) => Dynamic::from(ast::Bool::from_bool(ctx, *b)),
        otherwise => {
            panic_with_diagnostics(
                &format!(
                    "Expressions of the form {:?} are not parseable to a z3 ast",
                    otherwise
                ),
                &sym_memory,
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
