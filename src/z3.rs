//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
//!

extern crate z3;

use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Context, SatResult, Solver};
use rustc_hash::FxHashMap;
use std::fmt;
use std::rc::Rc;

use crate::ast::*;
use crate::shared::{Error, Scope};
pub type Identifier = String;

#[derive(Debug, Clone)]
pub enum Variable<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
    Ref
}

/// Environment where each environment is annotated with the scope it belongs to
#[derive(Debug, Clone)]
pub struct Frame<'a> {
    pub scope: Scope,
    pub env: FxHashMap<&'a Identifier, Variable<'a>>
} 

pub type Stack<'a> = Vec<Frame<'a>>;

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

pub fn insert_into_stack<'a>(env: &mut Stack<'a>, id: &'a Identifier, var: Variable<'a>) -> () {
    match env.last_mut() {
        Some(s) => {
            s.env.insert(id, var);
        }
        None => (),
    };
}

pub fn get_from_stack<'a>(env: &Stack<'a>, id: &'a Identifier) -> Option<Variable<'a>> {
    for s in env.iter().rev() {
        match s.env.get(&id) {
            Some(var) => return Some(var.clone()),
            None => (),
        }
    }
    return None;
}

/// casts identifier directly to dynamic z3 ast value from stack
pub fn get_dyn_from_stack<'a>(stack: &Stack<'a>, id: &'a Identifier) -> Result<Dynamic<'a>, Error> {
    let err = Error::Semantics(format!("Variable {} is undeclared", id));
    match get_from_stack(stack, id).ok_or(err)? {
        Variable::Int(i) => {
            return Ok(Dynamic::from(i.clone()));
        }
        Variable::Bool(b) => {
            return Ok(Dynamic::from(b.clone()));
        }
        Variable::Ref => todo!()
    }
}

pub fn fresh_int<'ctx>(ctx: &'ctx Context, id: String) -> Variable<'ctx> {
    return Variable::Int(Int::new_const(&ctx, id));
}

pub fn fresh_bool<'ctx>(ctx: &'ctx Context, id: String) -> Variable<'ctx> {
    return Variable::Bool(Bool::new_const(&ctx, id));
}

/// Combine the constraints in reversed order and check correctness
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn check_path<'ctx>(
    ctx: &'ctx Context,
    path_constraints: &Vec<PathConstraint<'ctx>>
) -> Result<(), Error> {
    let mut constraints = Bool::from_bool(ctx, true);

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

pub fn expression_to_int<'ctx>(
    ctx: &'ctx Context,
    env: &Stack<'ctx>,
    expr: &'ctx Expression,
) -> Result<Int<'ctx>, Error> {
    return expression_to_dynamic(&ctx, Rc::new(env), expr).and_then(as_int_or_error);
}

pub fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: &Stack<'ctx>,
    expr: &'ctx Expression,
) -> Result<Bool<'ctx>, Error> {
    return expression_to_dynamic(&ctx, Rc::new(env), expr).and_then(as_bool_or_error);
}

fn expression_to_dynamic<'ctx, 'b>(
    ctx: &'ctx Context,
    stack: Rc<&Stack<'ctx>>,
    expr: &'ctx Expression,
) -> Result<Dynamic<'ctx>, Error> {
    match expr {
        Expression::Exists(id, expr) => {
            let l = Int::fresh_const(ctx, id);
            let r = expression_to_dynamic(ctx, stack, expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(ast::exists_const(&ctx, &[&l], &[], &r)));
        }
        Expression::And(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_bool_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(Bool::and(ctx, &[&l, &r])));
        }
        Expression::Or(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_bool_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(Bool::or(ctx, &[&l, &r])));
        }
        Expression::EQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&stack), l_expr)?;
            let r = expression_to_dynamic(ctx, stack, r_expr)?;

            return Ok(Dynamic::from(l._eq(&r)));
        }
        Expression::NE(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&stack), l_expr)?;
            let r = expression_to_dynamic(ctx, stack, r_expr)?;

            return Ok(Dynamic::from(l._eq(&r).not()));
        }
        Expression::LT(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.lt(&r)));
        }
        Expression::GT(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.gt(&r)));
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.ge(&r)));
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.le(&r)));
        }
        Expression::Plus(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(ast::Int::add(&ctx, &[&l, &r])));
        }
        Expression::Minus(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(ast::Int::sub(&ctx, &[&l, &r])));
        }
        Expression::Multiply(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(ast::Int::mul(&ctx, &[&l, &r])));
        }
        Expression::Divide(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.div(&r)));
        }
        Expression::Mod(l_expr, r_expr) => {
            let l =
                expression_to_dynamic(ctx, Rc::clone(&stack), l_expr).and_then(as_int_or_error)?;
            let r = expression_to_dynamic(ctx, stack, r_expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(l.modulo(&r)));
        }
        Expression::Negative(expr) => {
            let e =
                expression_to_dynamic(ctx, Rc::clone(&stack), expr).and_then(as_int_or_error)?;

            return Ok(Dynamic::from(e.unary_minus()));
        }
        Expression::Not(expr) => {
            let expr = expression_to_dynamic(ctx, stack, expr).and_then(as_bool_or_error)?;

            return Ok(Dynamic::from(expr.not()));
        }
        Expression::Identifier(id) => get_dyn_from_stack(&stack, id),
        Expression::Literal(Literal::Integer(n)) => Ok(Dynamic::from(ast::Int::from_i64(ctx, *n))),
        Expression::Literal(Literal::Boolean(b)) => {
            Ok(Dynamic::from(ast::Bool::from_bool(ctx, *b)))
        }
        otherwise => {
            return Err(Error::Semantics(format!(
                "Expressions of the form {:?} are not parseable to a z3 ast",
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
    use z3::{Config, FuncDecl};

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
