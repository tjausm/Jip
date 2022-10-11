//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
//! 

extern crate z3;

use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Context, SatResult, Solver};

use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use crate::ast::*;
use crate::shared::{Error};
pub type Identifier = String;


#[derive(Debug, Clone)]
pub enum Variable<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
    Object(HashMap<&'a Identifier, Variable<'a>>) // mapping field -> variable
}

#[derive(Debug, Clone)]
pub struct AnScope<'a> {
    pub class: Identifier,
    pub method: Identifier,
    pub env: HashMap<&'a Identifier, Variable<'a>>
} 

/// Environment where each scope is annotated with method it belongs to

pub type AnEnvironment<'a> = Vec<AnScope<'a>>;

#[derive(Clone)]
pub enum PathConstraint<'a> {
    Assume(Bool<'a>),
    Assert(Bool<'a>),
}

impl fmt::Debug for PathConstraint<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathConstraint::Assume(pc) => write!(f, "{}", pc),
            PathConstraint::Assert(pc) => write!(f, "{}", pc),
        }
    }
}

pub fn insert_into_anEnv<'a>(env: &mut AnEnvironment<'a>, id: &'a Identifier, var: Variable<'a>) -> () {
    match env.last_mut() {
        Some(s) => {
            s.env.insert(id, var);
        }
        None => (),
    };
}

pub fn get_from_anEnv<'a>(
    env: &AnEnvironment<'a>,
    id: &'a Identifier,
) -> Option<Variable<'a>> {
    for s in env.iter().rev() {
        match s.env.get(&id) {
            Some(var) => return Some(var.clone()),
            None => (),
        }
    }
    return None;
}

pub fn fresh_int<'ctx>(ctx: &'ctx Context, id: String) -> Variable<'ctx> {
    return Variable::Int(Int::new_const(&ctx, id));
}

pub fn fresh_bool<'ctx>(ctx: &'ctx Context, id: String) -> Variable<'ctx> {
    return Variable::Bool(Bool::new_const(&ctx, id));
}

pub fn fresh_object<'ctx>(ctx: &'ctx Context, class: Class, id: String) -> Variable<'ctx> {
    // TODO: initiate fields hier?
    return Variable::Object(HashMap::new());
}

/// Combine the constraints in reversed order and check correctness
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn solve_constraints<'ctx>(
    ctx: &'ctx Context,
    path_constraints: &Vec<PathConstraint<'ctx>>,
    formula: &Bool<'ctx>,
) -> Result<(), Error> {
    let mut constraints = formula.clone();

    //reverse loop and combine constraints
    for constraint in path_constraints.iter().rev() {
        match constraint {
            PathConstraint::Assert(c) => constraints = Bool::and(&ctx, &[&c, &constraints]),
            PathConstraint::Assume(c) => constraints = Bool::implies(&c, &constraints),
        }
    }

    //println!("{}", constraints.not());

    let solver = Solver::new(&ctx);
    solver.assert(&constraints.not());
    let result = solver.check();
    let model = solver.get_model();

    //println!("{:?}", model);

    match (result, model) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            let x = format!("{:?}", model);
            println!("{}",x);
            return Err(Error::Verification(format!(
                "Following configuration violates program:\n{:?}",
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

pub fn expression_to_int<'ctx>(
    ctx: &'ctx Context,
    env: &AnEnvironment<'ctx>,
    expr: &'ctx Expression,
) -> Result<Int<'ctx>, Error> {
    return expression_to_dynamic(&ctx, Rc::new(env), expr).and_then(as_int_or_error);
}

pub fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: &AnEnvironment<'ctx>,
    expr: &'ctx Expression,
) -> Result<Bool<'ctx>, Error> {
    return expression_to_dynamic(&ctx, Rc::new(env), expr).and_then(as_bool_or_error);
}

fn expression_to_dynamic<'ctx, 'b>(
    ctx: &'ctx Context,
    env: Rc<&AnEnvironment<'ctx>>,
    expr: &'ctx Expression,
) -> Result<Dynamic<'ctx>, Error> {
    match expr {
        Expression::And(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_bool_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(Bool::and(ctx, &[&l, &r])));
        }
        Expression::Or(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_bool_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(Bool::or(ctx, &[&l, &r])));
        }
        Expression::EQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr)?;
            let r = expression_to_dynamic(ctx, env, r_expr)?;

            return Ok(Dynamic::from(l._eq(&r)));
        }
        Expression::NE(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr)?;
            let r = expression_to_dynamic(ctx, env, r_expr)?;

            return Ok(Dynamic::from(l._eq(&r).not()));
        }
        Expression::LT(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.lt(&r)));
        }
        Expression::GT(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.gt(&r)));
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.ge(&r)));
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.le(&r)));
        }
        Expression::Plus(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(ast::Int::add(&ctx, &[&l, &r])));
        }
        Expression::Minus(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(ast::Int::sub(&ctx, &[&l, &r])));
        }
        Expression::Multiply(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(ast::Int::mul(&ctx, &[&l, &r])));
        }
        Expression::Divide(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.div(&r)));
        }
        Expression::Mod(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&env), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, env, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.modulo(&r)));
        }
        Expression::Negative(expr) => {
            let e = expression_to_dynamic(ctx, Rc::clone(&env), expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(e.unary_minus()))
        }
        Expression::Not(expr) => {
            let expr = expression_to_dynamic(ctx, env, expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(expr.not()));
        }

        Expression::Identifier(id) => match get_from_anEnv(&env, id) {
            Some(var) => match var {
                Variable::Int(i) => {
                    //klopt dit, moet ik niet de reference naar de variable in de env passen?
                    return Ok(Dynamic::from(i.clone()));
                }
                Variable::Bool(b) => {
                    //klopt dit, moet ik niet de reference naar de variable in de env passen?
                    return Ok(Dynamic::from(b.clone()));
                }
                _ => todo!("Variable type not implemented")
            },
            None => {
                return Err(Error::Semantics(format!("Variable {} is undeclared", id)));
            }
        },
        Expression::Literal(Literal::Integer(n)) => {
            return Ok(Dynamic::from(ast::Int::from_i64(ctx, *n)))
        }
        Expression::Literal(Literal::Boolean(b)) => {
            return Ok(Dynamic::from(ast::Bool::from_bool(ctx, *b)))
        }
        otherwise => {
            return Err(Error::Semantics(format!(
                "Expressions of the form {:?} are not valid",
                otherwise
            )));
        }
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
}
