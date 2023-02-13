//! Intermediate model to encode & modify ast before we call z3
//!

use rustc_hash::FxHashMap;
use uuid::Uuid;
use crate::ast::*;

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
    pub fn combine<'a>(&'a self) -> Substituted {
        let mut constraints = Expression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(Substituted(assertion)) => {
                    constraints =
                        Expression::And(Box::new(assertion.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(Substituted(assumption)) => {
                    constraints =
                        Expression::Implies(Box::new(assumption.clone()), Box::new(constraints));
                }
            }
        }
        return Substituted(constraints);
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
#[derive(Debug, Clone)]
pub struct Substituted(pub Expression);

/// Containertype containing normalized expression.
/// Given 3 expressions `e1 = 1+2+3`, `e2 = 3+2+1` and `e1 = 2+3+1`
/// then `Normalized(e1) == Normalized(e2)`, `Normalized(e2) == Normalized(e3)` and so on
pub struct Normalized(pub Substituted);

pub type Reference = Uuid;

#[derive(Debug, Clone)]
pub enum SymValue {
    Uninitialized,
    Expr(Substituted),
}

#[derive(Debug, Clone)]
pub enum SymExpression {
    Int(SymValue),
    Bool(SymValue),
    Ref((Type, Reference)),
}

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (Identifier, FxHashMap<Identifier, (Type, SymExpression)>);

/// Consists of type, concrete array and Substituted expression representing length
pub type Array = (Type, Vec<SymExpression>, Substituted);

#[derive(Debug, Clone)]
pub enum ReferenceValue {
    Object(Object),
    Array(Array),
    /// Takes classname as input
    UninitializedObj(Class),
}
