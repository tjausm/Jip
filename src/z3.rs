//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3

use std::rc::Rc;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Config, Context, Model, SatResult, Solver};

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::model::{PathConstraints, Substituted, SymExpression, SymValue};

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
    length: &'ctx Substituted,
    index: &'ctx Substituted,
    sym_memory: &SymMemory,
) -> Result<(), Error> {
    // combine in expression of form 'length > index'
    let to_gt = |len| Expression::GT(Box::new(len), Box::new(index.get().clone()));
    let length_gt_index = length.clone().map(to_gt);

    // build new path constraints and get z3 bool
    let mut pc = pc.clone();
    pc.push_assertion(length_gt_index);
    let constraints = pc.combine_over_true();
    let length_gt_index = expr_to_bool(ctx, Rc::new(sym_memory), constraints.get());

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
    path_constraints: &PathConstraints,
    sym_memory: &SymMemory,
) -> Result<(), Error> {
    //transform too z3 boolean
    let constraint_expr = path_constraints.combine_over_true();
    let constraints = expr_to_bool(&ctx, Rc::new(sym_memory), &constraint_expr.get());

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
    expression: &Substituted,
    sym_memory: &SymMemory,
) -> bool {
    //negate assumption and try to find counter-example
    //no counter-example for !assumption means assumption is never true
    let assumption_ast = expr_to_bool(&ctx, Rc::new(sym_memory), expression.get()).not();

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
    sym_memory: Rc<&SymMemory>,
    expr: &'a Expression,
) -> Int<'ctx> {
    return unwrap_as_int(expr_to_dynamic(&ctx, sym_memory, expr));
}

fn expr_to_bool<'ctx, 'a>(
    ctx: &'ctx Context,
    sym_memory: Rc<&SymMemory>,
    expr: &'a Expression,
) -> Bool<'ctx> {
    return unwrap_as_bool(expr_to_dynamic(&ctx, sym_memory, expr));
}

fn expr_to_dynamic<'ctx, 'a>(
    ctx: &'ctx Context,
    sym_memory: Rc<&SymMemory>,
    expr: &'a Expression,
) -> Dynamic<'ctx> {
    match expr {
        Expression::Forall(arr, index, value, expr) => {

            return Dynamic::from(forall_to_bool(
                ctx,
                sym_memory,
                arr,
                index,
                value,
                expr,
            ));
        }
        Expression::And(l_expr, r_expr) => {
            let l = expr_to_bool(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_bool(ctx, sym_memory, r_expr);

            return Dynamic::from(Bool::and(ctx, &[&l, &r]));
        }
        Expression::Or(l_expr, r_expr) => {
            let l = expr_to_bool(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_bool(ctx, sym_memory, r_expr);

            return Dynamic::from(Bool::or(ctx, &[&l, &r]));
        }
        Expression::Implies(l_expr, r_expr) => {
            let l = expr_to_bool(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_bool(ctx, sym_memory, r_expr);

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
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(l.lt(&r));
        }
        Expression::GT(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(l.gt(&r));
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(l.ge(&r));
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(l.le(&r));
        }
        Expression::Plus(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(ast::Int::add(&ctx, &[&l, &r]));
        }
        Expression::Minus(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(ast::Int::sub(&ctx, &[&l, &r]));
        }
        Expression::Multiply(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(ast::Int::mul(&ctx, &[&l, &r]));
        }
        Expression::Divide(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(l.div(&r));
        }
        Expression::Mod(l_expr, r_expr) => {
            let l = expr_to_int(ctx, Rc::clone(&sym_memory), l_expr);
            let r = expr_to_int(ctx, sym_memory, r_expr);

            return Dynamic::from(l.modulo(&r));
        }
        Expression::Negative(expr) => {
            let e = expr_to_int(ctx, Rc::clone(&sym_memory), expr);

            return Dynamic::from(e.unary_minus());
        }
        Expression::Not(expr) => {
            let expr = expr_to_bool(ctx, sym_memory, expr);

            return Dynamic::from(expr.not());
        }
        // type variable using stack or substitute one level deep??
        Expression::Identifier(id) => match sym_memory.stack_get(id) {
            Some(SymExpression::Bool(SymValue::Expr(expr))) => {
                expr_to_dynamic(ctx, sym_memory, &expr.get())
            }
            Some(SymExpression::Int(SymValue::Expr(expr))) => {
                expr_to_dynamic(ctx, sym_memory, &expr.get())
            }
            Some(sym_expr) => panic_with_diagnostics(
                &format!("{:?} is not parseable to a z3 ast", sym_expr),
                &sym_memory,
            ),
            None => panic_with_diagnostics(&format!("{} is undeclared", id), &sym_memory),
        },
        Expression::FreeVariable(ty, id) => match ty {
            Type::Bool => Dynamic::from(Bool::new_const(ctx, id.clone())),
            Type::Int => Dynamic::from(Int::new_const(ctx, id.clone())),
            _ => panic_with_diagnostics(
                &format!("Free variable can't be of type {:?}", ty),
                &sym_memory,
            ),
        },
        Expression::Literal(Literal::Integer(n)) => Dynamic::from(ast::Int::from_i64(ctx, *n)),
        Expression::Literal(Literal::Boolean(b)) => Dynamic::from(ast::Bool::from_bool(ctx, *b)),
        Expression::Literal(Literal::Ref(r)) => {
            Dynamic::from(ast::Int::from_u64(ctx, r.1.as_u64_pair().0))
        }
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

fn forall_to_bool<'ctx, 'a>(
    ctx: &'ctx Context,
    sym_memory: Rc<&SymMemory>,
    arr_name: &Identifier,
    index: &Identifier,
    value: &Identifier,
    expr: &'a Expression,
) -> Bool<'ctx> {
    let (_, arr, len) = sym_memory.heap_get_array(arr_name).clone();
    let index_id = Expression::Identifier(index.clone());

    // foreach (i, v) pair in arr:
    // - C = for each[i |-> index, v |-> value]expr && C
    // - O = index != i && O
    let mut c = Expression::Literal(Literal::Boolean(true));
    let mut o = Expression::Literal(Literal::Boolean(true));
    for (i, v) in arr.into_iter() {

        // using Expressions `apply_when` functions we substitute the identifiers of index and value
        // with the expressions of given (i,v) pair in array
        let substitute_with_iv_pair = |expr: Expression| {
            
            let c_panic = || panic_with_diagnostics("Should not trigger", &sym_memory);
            
            match expr {
                Expression::Identifier(id) if &id == index => i.get().clone(),
                Expression::Identifier(id) if &id == value => match v.clone() {
                    SymExpression::Int(v) => match v {
                        SymValue::Expr(e) => e.get().clone(),
                        _ => c_panic()
                    },
                    SymExpression::Bool(v) => match v {
                        SymValue::Expr(e) => e.get().clone(),
                        _ => c_panic()
                    },
                    SymExpression::Ref(_) => c_panic(),
                },
                _ => expr
            }
        };
        let is_index_or_value = |expr: &Expression| {
            match expr {
                Expression::Identifier(id) if id == index => true,
                Expression::Identifier(id) if id == value => true,
                _ => false   
            }
        };
        let expr = &expr.clone().apply_when(substitute_with_iv_pair, is_index_or_value);
        
        let s = Substituted::new(&sym_memory, expr.clone()).get().clone();
        
        c = Expression::And(Box::new(s), Box::new(c));

        let ne = Expression::NE(Box::new(index_id.clone()), Box::new(i.get().clone()));
        o = Expression::And(Box::new(ne), Box::new(o));
    }

    // E = index >= 0 && O && index < #arr ==> expr
    let iGeq0 = Expression::GEQ(
        Box::new(index_id.clone()),
        Box::new(Expression::Literal(Literal::Integer(0))),
    );
    let iLtLen = Expression::LT(Box::new(index_id.clone()), Box::new(len.get().clone()));
    let e = Expression::Literal(Literal::Boolean(true));

    expr_to_bool(
        ctx,
        sym_memory,
        &Expression::And(Box::new(c), Box::new(e)),
    )
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
