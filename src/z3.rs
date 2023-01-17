//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
//!

extern crate z3;

use rustc_hash::FxHashMap;
use std::fmt;
use std::rc::Rc;
use uuid::Uuid;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Context, SatResult, Solver};

use crate::ast::*;
use crate::shared::{custom_panic, Error, Scope};
pub type Identifier = String;

pub type Reference = Uuid;

#[derive(Debug, Clone)]
pub enum SymbolicExpression<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
    Ref((Type, Reference)),
}

pub type Object<'a> = (
    Type,
    FxHashMap<&'a Identifier, (Type, SymbolicExpression<'a>)>,
);

pub type Array<'a> = (Type, Vec<SymbolicExpression<'a>>);

#[derive(Debug, Clone)]
pub enum ReferenceValue<'a> {
    Object(Object<'a>),
    Array(Array<'a>),
    Uninitialized(Type),
}

#[derive(Debug, Clone)]
pub struct Frame<'a> {
    pub scope: Scope,
    pub env: FxHashMap<&'a Identifier, SymbolicExpression<'a>>,
}

/// Stack of scope-annotated frames
pub type SymStack<'a> = Vec<Frame<'a>>;

pub type SymHeap<'a> = FxHashMap<Reference, ReferenceValue<'a>>;

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

pub fn insert_into_stack<'a>(
    env: &mut SymStack<'a>,
    id: &'a Identifier,
    var: SymbolicExpression<'a>,
) -> () {
    match env.last_mut() {
        Some(s) => {
            s.env.insert(id, var);
        }
        None => (),
    };
}

pub fn get_from_stack<'a>(
    env: &SymStack<'a>,
    id: &'a Identifier,
) -> Option<SymbolicExpression<'a>> {
    if id == "null" {
        return Some(SymbolicExpression::Ref((Type::Void, Uuid::nil())));
    };

    for s in env.iter().rev() {
        match s.env.get(&id) {
            Some(var) => return Some(var.clone()),
            None => (),
        }
    }
    return None;
}

/// Insert either object, object field, array or array item
pub fn insert_into_heap<'a>(
    env: &mut SymStack<'a>,
    id: &'a Identifier,
    var: SymbolicExpression<'a>,
) -> () {
    todo!("");
}

pub fn get_from_heap<'a>(env: &SymStack<'a>, id: &'a Identifier) -> Option<SymbolicExpression<'a>> {
    todo!("")
}

/// casts identifier directly to dynamic z3 ast value from stack
pub fn get_dyn_from_stack<'a>(
    ctx: &'a Context,
    sym_stack: &SymStack<'a>,
    id: &'a Identifier,
) -> Dynamic<'a> {
    match get_from_stack(sym_stack, id) {
        Some(SymbolicExpression::Int(i)) => Dynamic::from(i.clone()),
        Some(SymbolicExpression::Bool(b)) => Dynamic::from(b.clone()),
        Some(SymbolicExpression::Ref((_, r))) => {
            Dynamic::from(Int::from_u64(ctx, r.as_u64_pair().0))
        }
        None => custom_panic(
            &format!("Variable {} is undeclared", id),
            Some(sym_stack),
            None,
        ),
    }
}

pub fn fresh_int<'ctx>(ctx: &'ctx Context, id: String) -> SymbolicExpression<'ctx> {
    return SymbolicExpression::Int(Int::new_const(&ctx, id));
}

pub fn fresh_bool<'ctx>(ctx: &'ctx Context, id: String) -> SymbolicExpression<'ctx> {
    return SymbolicExpression::Bool(Bool::new_const(&ctx, id));
}

/// Combine the constraints in reversed order and check correctness
/// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
pub fn check_path<'ctx>(
    ctx: &'ctx Context,
    path_constraints: &Vec<PathConstraint<'ctx>>,
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
    env: &SymStack<'ctx>,
    expr: &'ctx Expression,
) -> Int<'ctx> {
    return unwrap_as_int(expression_to_dynamic(&ctx, Rc::new(env), expr));
}

pub fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: &SymStack<'ctx>,
    expr: &'ctx Expression,
) -> Bool<'ctx> {
    return unwrap_as_bool(expression_to_dynamic(&ctx, Rc::new(env), expr));
}

fn expression_to_dynamic<'ctx, 'b>(
    ctx: &'ctx Context,
    stack: Rc<&SymStack<'ctx>>,
    expr: &'ctx Expression,
) -> Dynamic<'ctx> {
    match expr {
        Expression::Exists(id, expr) => {
            let l = Int::fresh_const(ctx, id);
            let r = unwrap_as_bool(expression_to_dynamic(ctx, stack, expr));

            return Dynamic::from(ast::exists_const(&ctx, &[&l], &[], &r));
        }
        Expression::And(l_expr, r_expr) => {
            let l = unwrap_as_bool(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_bool(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(Bool::and(ctx, &[&l, &r]));
        }
        Expression::Or(l_expr, r_expr) => {
            let l = unwrap_as_bool(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_bool(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(Bool::or(ctx, &[&l, &r]));
        }
        Expression::EQ(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&stack), l_expr);
            let r = expression_to_dynamic(ctx, stack, r_expr);

            return Dynamic::from(l._eq(&r));
        }
        Expression::NE(l_expr, r_expr) => {
            let l = expression_to_dynamic(ctx, Rc::clone(&stack), l_expr);
            let r = expression_to_dynamic(ctx, stack, r_expr);

            return Dynamic::from(l._eq(&r).not());
        }
        Expression::LT(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(l.lt(&r));
        }
        Expression::GT(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(l.gt(&r));
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(l.ge(&r));
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(l.le(&r));
        }
        Expression::Plus(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(ast::Int::add(&ctx, &[&l, &r]));
        }
        Expression::Minus(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(ast::Int::sub(&ctx, &[&l, &r]));
        }
        Expression::Multiply(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(ast::Int::mul(&ctx, &[&l, &r]));
        }
        Expression::Divide(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(l.div(&r));
        }
        Expression::Mod(l_expr, r_expr) => {
            let l = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), l_expr));
            let r = unwrap_as_int(expression_to_dynamic(ctx, stack, r_expr));

            return Dynamic::from(l.modulo(&r));
        }
        Expression::Negative(expr) => {
            let e = unwrap_as_int(expression_to_dynamic(ctx, Rc::clone(&stack), expr));

            return Dynamic::from(e.unary_minus());
        }
        Expression::Not(expr) => {
            let expr = unwrap_as_bool(expression_to_dynamic(ctx, stack, expr));

            return Dynamic::from(expr.not());
        }
        Expression::Identifier(id) => get_dyn_from_stack(ctx, &stack, id),
        Expression::Literal(Literal::Integer(n)) => Dynamic::from(ast::Int::from_i64(ctx, *n)),
        Expression::Literal(Literal::Boolean(b)) => Dynamic::from(ast::Bool::from_bool(ctx, *b)),
        otherwise => {
            custom_panic(
                &format!(
                    "Expressions of the form {:?} are not parseable to a z3 ast",
                    otherwise
                ),
                None,
                None,
            );
        }
    }
}

fn unwrap_as_bool<'ctx>(d: Dynamic<'ctx>) -> Bool<'ctx> {
    match d.as_bool() {
        Some(b) => b,
        None => custom_panic(&format!("{} is not of type Bool", d), None, None),
    }
}

fn unwrap_as_int<'ctx>(d: Dynamic<'ctx>) -> Int<'ctx> {
    match d.as_int() {
        Some(b) => b,
        None => custom_panic(&format!("{} is not of type Int", d), None, None),
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
