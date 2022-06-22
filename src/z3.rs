extern crate z3;

use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Config, Context, SatResult, Solver};

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::errors::Error;

pub type Identifier = String;

#[derive(Debug, Clone)]
pub enum Variable<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
}

pub type Environment<'a> =  HashMap<&'a Identifier, Variable<'a>>;

//return error if there is a true negation of given expression
pub fn verify_bool<'ctx>(
    ctx: &'ctx Context,
    env: &'ctx Environment<'ctx>,
    formula: &Bool<'ctx>,
) -> Result<(), Error> {
    let solver = Solver::new(&ctx);
    solver.assert(&formula);
    let result = solver.check();
    let model = solver.get_model();

    match (result, model) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            return Err(Error::Verification(format!(
                "Following configuration violates program:\n{:?}",
                model
            )))
        }
        _ => {
            return Err(Error::Verification(
                "Huh, verification gave an unkown result".to_string(),
            ))
        }
    };
}

pub fn expression_to_int<'ctx>(
    ctx: &'ctx Context,
    env: &Environment<'ctx>,
    expr: &Expression,
) -> Result<Int<'ctx>, Error> {
    return expression_to_dynamic(ctx, Rc::new(env), expr).and_then(as_int_or_error);
}

pub fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: &Environment<'ctx>,
    expr: &Expression,
) -> Result<Bool<'ctx>, Error> {
    return expression_to_dynamic(ctx, Rc::new(env), expr).and_then(as_bool_or_error);
}

fn expression_to_dynamic<'ctx>(
    ctx: &'ctx Context,
    env: Rc<&Environment<'ctx>>,
    expr: &Expression,
) -> Result<Dynamic<'ctx>, Error> {
    match expr {
        Expression::And(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_bool_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_bool_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(Bool::and(ctx, &[&l, &r]))),
                Err(why) => return Err(why),
            }
        }
        Expression::Or(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_bool_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_bool_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(Bool::or(ctx, &[&l, &r]))),
                Err(why) => return Err(why),
            }
        }
        Expression::EQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_dynamic(ctx, env, r_expr);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l._eq(&r))),
                Err(why) => return Err(why),
            }
        }
        Expression::NE(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_dynamic(ctx, env, r_expr);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l._eq(&r).not())),
                Err(why) => return Err(why),
            }
        }
        Expression::LT(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l.lt(&r))),
                Err(why) => Err(why),
            }
        }
        Expression::GT(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l.gt(&r))),
                Err(why) => Err(why),
            }
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l.ge(&r))),
                Err(why) => Err(why),
            }
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l.le(&r))),
                Err(why) => Err(why),
            }
        }
        Expression::Plus(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(ast::Int::add(&ctx, &[&l, &r]))),
                Err(why) => return Err(why),
            }
        }
        Expression::Minus(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(ast::Int::sub(&ctx, &[&l, &r]))),
                Err(why) => return Err(why),
            }
        }
        Expression::Multiply(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(ast::Int::mul(&ctx, &[&l, &r]))),
                Err(why) => return Err(why),
            }
        }
        Expression::Divide(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l.div(&r))),
                Err(why) => return Err(why),
            }
        }
        Expression::Mod(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error);
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error);

            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Dynamic::from(l.modulo(&r))),
                Err(why) => return Err(why),
            }
        }
        Expression::Negative(expr) => {
            let e = expression_to_dynamic(ctx, Rc::clone(&env), expr).and_then(as_int_or_error);

            match e {
                Ok(e) => return Ok(Dynamic::from(e.unary_minus())),
                Err(why) => return Err(why),
            }
        }
        Expression::Not(expr) => {
            let expr = expression_to_dynamic(ctx, env, expr).and_then(as_bool_or_error);

            match expr {
                Ok(expr) => return Ok(Dynamic::from(expr.not())),
                Err(err) => return Err(err),
            }
        }

        Expression::Identifier(id) => match env.get(id) {
            Some(var) => match var {
                Variable::Int(i) => {
                    //klopt dit, moet ik niet de reference naar de variable in de env passen?
                    return Ok(Dynamic::from(i.clone()));
                }
                _ => {
                    return Err(Error::Semantics(format!(
                        "can't convert {:?} to an int",
                        var
                    )));
                }
            },
            None => {
                return Err(Error::Semantics(format!("Variable {} is undeclared", id)));
            }
        },
        Expression::Literal(Literal::Integer(n)) => {
            return Ok(Dynamic::from(ast::Int::from_i64(ctx, *n)))
        }
        otherwise => {
            return Err(Error::Semantics(format!(
                "Expressions of the form {:?} should not be in an expression",
                otherwise
            )));
        }
    }
}

//flatten result to ok, or the first error encountered
fn flatten_tupple<'ctx, A>((l, r): (Result<A, Error>, Result<A, Error>)) -> Result<(A, A), Error> {
    match (l, r) {
        (Ok(l), Ok(r)) => return Ok((l, r)),
        (Ok(l), Err(r_err)) => return Err(r_err),
        (Err(l_err), _) => return Err(l_err),
    }
}

fn as_bool_or_error<'ctx>(d: Dynamic<'ctx>) -> Result<Bool<'ctx>, Error> {
    match d.as_bool() {
        Some(b) => Ok(b),
        None => Err(Error::Semantics(format!("{} is not of type Bool", d))),
    }
}

fn as_int_or_error<'ctx>(d: Dynamic<'ctx>) -> Result<Int<'ctx>, Error> {
    match d.as_int() {
        Some(b) => Ok(b),
        None => Err(Error::Semantics(format!("{} is not of type Int", d))),
    }
}

#[cfg(test)]
mod tests {

    use super::*;

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
}
