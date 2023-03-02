//! Intermediate model to encode & modify ast before we call z3
//!

use core::fmt;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

use crate::{ast::*, shared::panic_with_diagnostics, symbolic::memory::SymMemory};
use rustc_hash::FxHashMap;
use uuid::Uuid;

#[derive(Clone)]
pub struct PathConstraints {
    constraints: Vec<PathConstraint>,
}

#[derive(Clone)]
pub enum PathConstraint {
    Assert(Substituted),
    Assume(Substituted),
}

impl Default for PathConstraints {
    fn default() -> Self {
        PathConstraints {
            constraints: vec![],
        }
    }
}

impl PathConstraints {

    /// combine constraints over true as follows: `assume(a), assert(b) -> a ==> b && true`
    pub fn combine_over_true<'a>(&'a self) -> Substituted {
        let mut constraints = Expression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(Substituted { expr }) => {
                    constraints = Expression::And(Box::new(expr.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(Substituted { expr }) => {
                    constraints =
                        Expression::Implies(Box::new(expr.clone()), Box::new(constraints));
                }
            }
        }
        return Substituted { expr: constraints };
    }
    /// combine constraints as a conjunction as follows: `assume(a), assert(b) -> a && b`
    pub fn conjuct<'a>(&'a self) -> Substituted {
        let mut constraints = Expression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(Substituted { expr }) => {
                    constraints = Expression::And(Box::new(expr.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(Substituted { expr }) => {
                    constraints =
                        Expression::And(Box::new(expr.clone()), Box::new(constraints));
                }
            }
        }
        return Substituted { expr: constraints };
    }

    /// adds a new constraint
    pub fn push_assertion(&mut self, s: Substituted) {
        self.constraints.push(PathConstraint::Assert(s));
    }
    /// adds a new constraint
    pub fn push_assumption(&mut self, s: Substituted) {
        self.constraints.push(PathConstraint::Assume(s));
    }
}

/// containertype to indicate substitution of variables has already occured on expression
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Substituted {
    expr: Expression,
}

impl Substituted {
    /// generate a substituted expression from given expression
    pub fn new(sym_memory: &SymMemory, expr: Expression) -> Self {
        let apply = |expr| partial_apply(sym_memory, expr);

        return Substituted {
            expr: expr.apply_when(apply, when),
        };



        fn when(expr: &Expression) -> bool{
            match expr{
                Expression::Identifier(_) => true,
                Expression::ArrLength(_) => true,
                _ => false
            }
        }

        fn partial_apply(sym_memory: &SymMemory, expr: Expression) -> Expression{
            let apply = |expr| partial_apply(sym_memory, expr);

            match expr{
                Expression::Identifier(id) => match sym_memory.stack_get(&id) {
                    Some(SymExpression::Bool(SymValue::Expr(Substituted { expr }))) => {
                         expr.apply_when(apply, when)
                    }
                    Some(SymExpression::Int(SymValue::Expr(Substituted { expr }))) => {
                        expr.apply_when(apply, when)
                    }
                    Some(SymExpression::Ref(r)) => Expression::Literal(Literal::Ref(r)),
                    Some(sym_expr) => panic_with_diagnostics(
                        &format!(
                            "identifier {} with value {:?} can't be substituted",
                            id, sym_expr
                        ),
                        sym_memory,
                    ),
                    None => panic_with_diagnostics(&format!("{} was not declared", id), sym_memory),
                },
                Expression::ArrLength(arr_name) => {
                    sym_memory.heap_get_arr_length(&arr_name).get().clone()
                }
                _ => expr
            }
        }
    }

    /// be cautious that `f` doesn't introduce unsubstitued values in the inner-expression
    pub fn map<F>(self, mut f: F) -> Self
    where
        F: FnMut(Expression) -> Expression,
    {
        Substituted { expr: f(self.expr) }
    }

    pub fn get(&self) -> &Expression {
        &self.expr
    }

    pub fn mk_freevar(ty: Type, name: Identifier) -> Substituted {
        Substituted {
            expr: Expression::FreeVariable(ty, name),
        }
    }
}

pub type Reference = Uuid;

#[derive( Clone)]
pub enum SymValue {
    Uninitialized,
    Expr(Substituted),
}

#[derive(Clone)]
pub enum SymExpression {
    Int(SymValue),
    Bool(SymValue),
    Ref((Type, Reference)),
}

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (Identifier, FxHashMap<Identifier, (Type, SymExpression)>);

/// Consists of type, a mapping from expression to symbolic expression and Substituted expression representing length
pub type Array = (Type, FxHashMap<Substituted, SymExpression>, Substituted);

#[derive(Clone)]
pub enum ReferenceValue {
    Object(Object),
    Array(Array),
    /// Takes classname as input
    UninitializedObj(Class),
}

/// Intermediate type use to implement custom `Hash` for Expression
/// while also using the default hasher for the 'base values'
#[derive(Hash)]
enum HashExpression {
    Plus(Vec<u64>),
    Multiply(Vec<u64>),
    Divide(u64, u64),
    Mod(u64, u64),
    Negative(u64),
    Identifier(Identifier),
    Literal(Literal),
    ArrLength(Identifier),
}

fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}
fn map_hash<T: Hash>(v: &Vec<T>) -> Vec<u64> {
    v.into_iter()
        .map(|t| calculate_hash(&t))
        .collect::<Vec<u64>>()
}

impl Hash for Expression {
    fn hash<H: Hasher>(&self, state: &mut H) {
        fn collect_sum(expr: Expression) -> Vec<Expression> {
            match expr {
                Expression::Plus(l_expr, r_expr) => {
                    let mut sum = collect_sum(*l_expr);
                    sum.append(&mut collect_sum(*r_expr));
                    sum
                }
                Expression::Minus(l_expr, r_expr) => collect_sum(Expression::Plus(
                    l_expr,
                    Box::new(Expression::Negative(r_expr)),
                )),
                _ => vec![expr],
            }
        }

        fn collect_mult(expr: Expression) -> Vec<Expression> {
            match expr {
                Expression::Multiply(l_expr, r_expr) => {
                    let mut mult = collect_mult(*l_expr);
                    mult.append(&mut collect_mult(*r_expr));
                    mult
                }
                _ => vec![expr],
            }
        }

        match self {
            Expression::Plus(_, _) => {
                let sum = collect_sum(self.clone());
                let mut hashed_sum = map_hash(&sum);
                hashed_sum.sort();
                HashExpression::Plus(hashed_sum).hash(state)
            }
            Expression::Multiply(_, _) => {
                let mult = collect_mult(self.clone());
                let mut hashed_mult = map_hash(&mult);
                hashed_mult.sort();
                HashExpression::Multiply(hashed_mult).hash(state)
            }
            Expression::Minus(l_expr, r_expr) => Expression::Plus(
                l_expr.clone(),
                Box::new(Expression::Negative(r_expr.clone())),
            )
            .hash(state),
            Expression::Divide(l_expr, r_expr) => {
                HashExpression::Divide(calculate_hash(&*l_expr), calculate_hash(&*r_expr))
                    .hash(state)
            }
            Expression::Mod(l_expr, r_expr) => {
                HashExpression::Mod(calculate_hash(&*l_expr), calculate_hash(&*r_expr)).hash(state)
            }
            Expression::Negative(expr) => {
                HashExpression::Negative(calculate_hash(&*expr)).hash(state)
            }
            Expression::Identifier(id) => HashExpression::Identifier(id.clone()).hash(state),
            Expression::Literal(lit) => HashExpression::Literal(lit.clone()).hash(state),
            Expression::ArrLength(id) => HashExpression::ArrLength(id.clone()).hash(state),
            _ => panic_with_diagnostics(&format!("Cannot hash expression {:?}", self), &()),
        }
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        calculate_hash(&self) == calculate_hash(other)
    }
}
impl Eq for Expression {}

impl fmt::Debug for SymValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymValue::Uninitialized => write!(f, "Uninitialized"),
            SymValue::Expr(expr) => write!(f, "{:?}", expr.get()),
        }
    }
}
impl fmt::Debug for SymExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymExpression::Int(val) => write!(f, "{:?}", val),
            SymExpression::Bool(val) => write!(f, "{:?}", val),
            SymExpression::Ref(r) => write!(f, "{:?}", r),
        }
    }
}

impl fmt::Debug for PathConstraints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.combine_over_true())
    }
}
impl fmt::Debug for Substituted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.get())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    lalrpop_mod!(pub parser);

    fn parse(i: &str) -> Expression {
        return parser::VerificationExpressionParser::new()
            .parse(i)
            .unwrap();
    }

    #[test]
    fn sum_expr_equivalence() {
        let e1 = parse("1+2+3");
        let e2 = parse("3+2+1");
        let e3 = parse("2+3+1");
        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(calculate_hash(&e1) == calculate_hash(&e3));
    }
    #[test]
    fn mult_expr_equivalence() {
        let e1 = parse("2*3*4+5-1");
        let e2 = parse("3*2*4+5-1");
        let e3 = parse("2*3*4+(-1)+5");

        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(calculate_hash(&e1) == calculate_hash(&e3));
    }
    #[test]
    fn more_expr_equivalence() {
        let e1 = parse("(7*4+5/8%5)+3");
        let e2 = parse("3+(4*7+5/8%5)");
        assert!(calculate_hash(&e1) == calculate_hash(&e2));
    }
    #[test]
    fn int_comparison() {
        let e1 = parse("1");
        let e2 = parse("1");
        let e3 = parse("123");
        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(calculate_hash(&e2) != calculate_hash(&e3));
    }
    #[test]
    fn arrlength_not_equivalent() {
        let e1 = parse("#a");
        let e2 = parse("a");
        assert!(calculate_hash(&e1) != calculate_hash(&e2));
    }
    #[test]
    fn literal_not_equivalent() {
        let e1 = parse("false");
        let e2 = parse("true");
        assert!(calculate_hash(&e1) != calculate_hash(&e2));
    }

    #[test]
    fn deterministic_sort() {
        let one = parse("1");
        let id = parse("id");
        let negative = parse("-1");
        let three = parse("0+1+2*3/3");

        // construct some random arrays with these expressions
        let vec1 = vec![negative.clone(), three.clone(), id.clone(), one.clone()];
        let vec2 = vec![negative.clone(), one.clone(), id.clone(), three.clone()];
        let vec3 = vec![three.clone(), id.clone(), negative.clone(), one.clone()];
        let vec4 = vec![id, negative, one, three];

        let mut vec1 = map_hash(&vec1);
        vec1.sort();
        let mut vec2 = map_hash(&vec2);
        vec2.sort();
        let mut vec3 = map_hash(&vec3);
        vec3.sort();
        let mut vec4 = map_hash(&vec4);
        vec4.sort();

        // check if arrays are equal after sorting
        assert!(vec1 == vec2);
        assert!(vec1 == vec3);
        assert!(vec1 == vec4);
    }
}
