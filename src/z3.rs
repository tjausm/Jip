//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3

use std::rc::Rc;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Config, Context, SatResult, Solver};

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error};
use crate::symbolic::model::{PathConstraints, SymExpression, Substituted};
use crate::symbolic::memory::SymMemory;

//--------------//
// z3 bindings //
//-------------//

pub fn build_ctx() -> (Config, Context) {
    let z3_cfg = z3::Config::new();
    let ctx = z3::Context::new(&z3_cfg);
    (z3_cfg, ctx)
}

/// Checks if `always length > index` for usage in array accessing
pub fn check_length<'ctx>(
    ctx: &'ctx Context,
    length: &'ctx Substituted,
    index: &'ctx Substituted,
    sym_memory: &SymMemory<'ctx>,
) -> Result<(), Error> {
    let length = expr_to_int(ctx, sym_memory, &length.0);
    let index =  expr_to_int(ctx, sym_memory, &index.0);
    let length_gt_index = length.gt(&index);

    check_ast(ctx, &length_gt_index)
}

/// Combine the constraints in reversed order and check correctness using z3
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn verify_constraints<'a>(
    ctx: &'a Context,
    path_constraints: &PathConstraints,
    sym_memory: &SymMemory<'a>,
) -> Result<(), Error> {
    //transform too z3 boolean
    let constraint_expr = path_constraints.combine();
    let constraints = expr_to_bool(&ctx, sym_memory, &constraint_expr.0);

    check_ast(ctx, &constraints)
}

// returns error if there exists a counterexample for given formula
fn check_ast<'ctx>(ctx: &'ctx Context, ast: &Bool) -> Result<(), Error> {
    let solver = Solver::new(&ctx);
    solver.assert(&ast.not());
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
