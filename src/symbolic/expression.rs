//! Symbolic types representing the values on the stack while symbolically executing a program
//!

use core::fmt;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

use rustc_hash::FxHashMap;

use super::ref_values::{
    EvaluatedRefs, Interval, IntervalMap, Reference, ReferenceValue, SymRefType,
};
use crate::{ast::*, shared::panic_with_diagnostics, symbolic::memory::SymMemory};

#[derive(Clone)]
pub struct PathConstraints {
    constraints: Vec<PathConstraint>,
}

#[derive(Clone)]
pub enum PathConstraint {
    Assert(Expression),
    Assume(Expression),
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
    pub fn combine_over_true(&self) -> Expression {
        let mut constraints = Expression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(expr) => {
                    constraints = Expression::And(Box::new(expr.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(expr) => {
                    constraints =
                        Expression::Implies(Box::new(expr.clone()), Box::new(constraints));
                }
            }
        }

        return constraints;
    }
    /// combine constraints as a conjunction as follows: `assume(a), assert(b) -> a && b`
    pub fn conjunct(&self) -> Expression {
        let mut constraints = Expression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(expr) => {
                    constraints = Expression::And(Box::new(expr.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(expr) => {
                    constraints = Expression::And(Box::new(expr.clone()), Box::new(constraints));
                }
            }
        }

        return constraints;
    }

    /// adds a new constraint
    pub fn push_assertion(&mut self, assertion: Expression) {
        self.constraints.push(PathConstraint::Assert(assertion));
    }
    /// adds a new constraint
    pub fn push_assumption(&mut self, assumption: Expression) {
        self.constraints.push(PathConstraint::Assume(assumption));
    }
    /// pops top most constraint
    pub fn pop(&mut self) {
        self.constraints.pop();
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SymType {
    Int,
    Bool,
    Ref(SymRefType),
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub enum Expression {
    Implies(Box<Expression>, Box<Expression>),
    Forall(Forall),
    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),
    EQ(Box<Expression>, Box<Expression>),
    NE(Box<Expression>, Box<Expression>),
    LT(Box<Expression>, Box<Expression>),
    GT(Box<Expression>, Box<Expression>),
    GEQ(Box<Expression>, Box<Expression>),
    LEQ(Box<Expression>, Box<Expression>),
    Plus(Box<Expression>, Box<Expression>),
    Minus(Box<Expression>, Box<Expression>),
    Multiply(Box<Expression>, Box<Expression>),
    Divide(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),
    Negative(Box<Expression>),
    Not(Box<Expression>),
    Literal(Literal),
    FreeVariable(SymType, Identifier),
    Reference(Reference),
    Uninitialized,
}

impl Expression {
    /// destructs forall and exists quantifiers and then
    /// generates a substituted expression from it
    pub fn substitute(sym_memory: &SymMemory, expr: OOXExpression) -> Self {
        match expr {
            OOXExpression::Forall(arr_name, index, value, inner_expr) => {
                let r = match sym_memory.stack_get(&arr_name) {
                    Some(Expression::Reference(r)) => r,
                    Some(_) => panic_with_diagnostics(
                        &format!(
                            "In '{:?}' identifier {} is not a reference",
                            inner_expr, arr_name
                        ),
                        &sym_memory,
                    ),
                    None => panic_with_diagnostics(
                        &format!(
                            "In '{:?}' identifier {} is not declared",
                            inner_expr, arr_name
                        ),
                        &sym_memory,
                    ),
                };
                Expression::Forall(Forall::new(
                    r,
                    index,
                    value,
                    *inner_expr,
                    sym_memory.clone(),
                ))
            }
            OOXExpression::Exists(_arr_name, _index, _value, _expr) => todo!(),
            OOXExpression::Identifier(id) => match sym_memory.stack_get(&id) {
                Some(sym_expr) => sym_expr,
                _ => panic_with_diagnostics(&format!("{} was not declared", id), &sym_memory),
            },
            OOXExpression::SizeOf(arr_name) => match sym_memory.stack_get(&arr_name) {
                Some(Expression::Reference(r)) => match sym_memory.heap_get_unsafe(&r) {
                    ReferenceValue::Array((_, _, size, _)) => size.clone(),
                    _ => panic_with_diagnostics(
                        &format!("{} is not an array", arr_name),
                        &sym_memory,
                    ),
                },
                _ => {
                    panic_with_diagnostics(&format!("{} is not a reference", arr_name), &sym_memory)
                }
            },
            OOXExpression::Implies(l, r) => Expression::Implies(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::And(l, r) => Expression::And(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Or(l, r) => Expression::Or(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::EQ(l, r) => Expression::EQ(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::NE(l, r) => Expression::NE(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::LT(l, r) => Expression::LT(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::GT(l, r) => Expression::GT(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::GEQ(l, r) => Expression::GEQ(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::LEQ(l, r) => Expression::LEQ(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Plus(l, r) => Expression::Plus(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Minus(l, r) => Expression::Minus(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Multiply(l, r) => Expression::Multiply(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Divide(l, r) => Expression::Divide(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Mod(l, r) => Expression::Mod(
                Box::new(Expression::substitute(sym_memory, *l)),
                Box::new(Expression::substitute(sym_memory, *r)),
            ),
            OOXExpression::Negative(expr) => {
                Expression::Negative(Box::new(Expression::substitute(sym_memory, *expr)))
            }
            OOXExpression::Not(expr) => {
                Expression::Not(Box::new(Expression::substitute(sym_memory, *expr)))
            }
            OOXExpression::Literal(lit) => Expression::Literal(lit),
        }
    }

    /// front end simplifier, only pass eval_refs if it makes sense to evaluate the lazy refs
    pub fn eval(self, i: &IntervalMap, eval_refs: Option<&EvaluatedRefs>) -> Self {
        match &self {
            Expression::And(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (Expression::Literal(Literal::Boolean(false)), _) => {
                        Expression::Literal(Literal::Boolean(false))
                    }
                    (_, Expression::Literal(Literal::Boolean(false))) => {
                        Expression::Literal(Literal::Boolean(false))
                    }
                    (
                        Expression::Literal(Literal::Boolean(true)),
                        Expression::Literal(Literal::Boolean(true)),
                    ) => Expression::Literal(Literal::Boolean(true)),
                    (l_simple, r_simple) => {
                        Expression::And(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Or(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (Expression::Literal(Literal::Boolean(true)), _) => {
                        Expression::Literal(Literal::Boolean(true))
                    }
                    (_, Expression::Literal(Literal::Boolean(true))) => {
                        Expression::Literal(Literal::Boolean(true))
                    }
                    (l_simple, r_simple) => {
                        Expression::Or(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Implies(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (Expression::Literal(Literal::Boolean(false)), _) => {
                        Expression::Literal(Literal::Boolean(true))
                    }
                    (_, Expression::Literal(Literal::Boolean(true))) => {
                        Expression::Literal(Literal::Boolean(true))
                    }
                    (
                        Expression::Literal(Literal::Boolean(_)),
                        Expression::Literal(Literal::Boolean(_)),
                    ) => Expression::Literal(Literal::Boolean(false)),
                    (l_simple, r_simple) => {
                        Expression::Implies(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            // simplify not equal to equal
            Expression::NE(l, r) => Expression::Not(Box::new(Expression::EQ(
                Box::new(*l.clone()),
                Box::new(*r.clone()),
            )))
            .eval(i, eval_refs),
            Expression::EQ(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    // if lit or fv are equal => true
                    (Expression::Literal(l_lit), Expression::Literal(r_lit)) => {
                        Expression::Literal(Literal::Boolean(l_lit == r_lit))
                    }
                    (
                        Expression::FreeVariable(_, l_fv),
                        Expression::FreeVariable(__, r_fv),
                    ) if l_fv == r_fv => Expression::Literal(Literal::Boolean(true)),

                    (l_simple, r_simple) => {
                        match (Interval::infer(&l_simple, i), Interval::infer(&r_simple, i)) {
                            //check if intervals have no intersection
                            (Interval(a, b), Interval(d, c)) if b < d || c < a => {
                                Expression::Literal(Literal::Boolean(false))
                            }
                            _ => Expression::EQ(Box::new(l_simple), Box::new(r_simple)),
                        }
                    }
                }
            }

            // Define LEQ, GT and GEQ in terms of LT
            Expression::LEQ(l, r) => Expression::Not(Box::new(Expression::LT(
                Box::new(*r.clone()),
                Box::new(*l.clone()),
            )))
            .eval(i, eval_refs),
            Expression::GT(l, r) => Box::new(Expression::LT(
                Box::new(*r.clone()),
                Box::new(*l.clone()),
            ))
            .eval(i, eval_refs),
            Expression::GEQ(l, r) => Expression::Not(Box::new(Expression::LT(
                Box::new(*l.clone()),
                Box::new(*r.clone()),
            )))
            .eval(i, eval_refs),
            Expression::LT(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Boolean(l_lit < r_lit)),
                    (l_simple, r_simple) => {
                        match (Interval::infer(&l_simple, i), Interval::infer(&r_simple, i)) {
                            //check if intervals have no intersection
                            (Interval(_a, b), Interval(c, _d)) if b < c => {
                                Expression::Literal(Literal::Boolean(true))
                            }
                            (Interval(a, _b), Interval(_c, d)) if d < a => {
                                Expression::Literal(Literal::Boolean(false))
                            }
                            _ => Expression::LT(Box::new(l_simple), Box::new(r_simple)),
                        }
                    }
                }
            }
            Expression::Plus(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit + r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Plus(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Minus(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit - r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Minus(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Multiply(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit * r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Multiply(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Divide(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit / r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Divide(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Mod(l, r) => {
                match (l.clone().eval(i, eval_refs), r.clone().eval(i, eval_refs)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit % r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Mod(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Not(expr) => match expr.clone().eval(i, eval_refs) {
                Expression::Not(inner_expr) => inner_expr.clone().eval(i, eval_refs),
                Expression::Literal(Literal::Boolean(b)) => {
                    Expression::Literal(Literal::Boolean(!b))
                }
                simple_expr => Expression::Not(Box::new(simple_expr)),
            },
            Expression::Negative(expr) => match expr.clone().eval(i, eval_refs) {
                Expression::Negative(inner_expr) => inner_expr.clone().eval(i, eval_refs),
                Expression::Literal(Literal::Integer(n)) => {
                    Expression::Literal(Literal::Integer(-n))
                }
                expr => Expression::Negative(Box::new(expr)),
            },
            Expression::Literal(_) => self,
            //evaluate point interval
            Expression::FreeVariable(_, _x) => match Interval::infer(&self, i) {
                Interval(a, b) if a == b && a.is_finite() => {
                    Expression::Literal(Literal::Integer(a.finite().unwrap()))
                }
                _ => self,
            },
            Expression::Reference(r) => match (r, eval_refs) {
                (Reference::Evaluated(_), _) => self,
                (Reference::Lazy { r, class: _ }, Some(er)) if er.contains(r) => {
                    Expression::Reference(Reference::Evaluated(*r))
                }
                _ => self,
            },
            Expression::Forall(_) => self,
            Expression::Uninitialized => panic_with_diagnostics(
                "There is an uninitialized value in an expression. Did you declare all variables?",
                &self,
            ),
        }
    }
}

#[derive(Clone)]
pub struct Forall {
    r: Reference,
    index: Identifier,
    value: Identifier,
    inner_expr: OOXExpression,
    captured_memory: SymMemory,
}

// randomize hashing if Forall is involved in Expression
impl Hash for Forall {
    fn hash<H: Hasher>(&self, state: &mut H) {
        rand::random::<u64>().hash(state)
    }
}
impl PartialEq for Forall {
    fn eq(&self, other: &Self) -> bool {
        false
    }
}
impl Eq for Forall {}

impl Forall {
    fn new(
        r: Reference,
        index: Identifier,
        value: Identifier,
        inner_expr: OOXExpression,
        captured_memory: SymMemory,
    ) -> Self {
        Self {
            r,
            index,
            value,
            inner_expr,
            captured_memory,
        }
    }

    /// destructs a `Expression::forall(arr, index, value)` statement using the following algorithm:
    /// ``` ignore
    /// // asserts expression holds for all values in array
    /// let mut c = true
    /// for (i, v) in arr { c = c && [i |->index, v |-> value] in expr}     /// // substitute (i,v) into expression
    ///
    /// // asserts expression holds for all values > 0 and < #arr that are not in symbolic array
    /// o = true
    /// for (i,v) in arr {o = index != i && o}
    /// e = (0 < index && o && index < #arr && value == 0 ==> expr
    ///
    /// return c && e
    /// ```
    pub fn construct(&self, current_memory: &SymMemory) -> Expression {
        let (r, index, value, inner_expr, captured_memory) = (
            &self.r,
            &self.index,
            &self.value,
            &self.inner_expr,
            &self.captured_memory,
        );
        let index_id = Expression::FreeVariable(SymType::Int, index.clone());

        let (sym_ty, arr, _size_expr, _) = match current_memory.heap_get_unsafe(r) {
            ReferenceValue::Array(a) => a,
            _ => todo!(),
        };

        // foreach (i, v) pair in arr:
        // - C = for each[i |-> index, v |-> value]expr && C
        // - O = index != i && O
        let mut c = Expression::Literal(Literal::Boolean(true));
        let mut o = Expression::Literal(Literal::Boolean(true));
        for (i, v) in arr.into_iter() {
            // we insert index and value substitutions into stack
            // and build a new inner_expression with said substitutions
            let mut extended_memory = captured_memory.clone();
            extended_memory.stack_insert(index.clone(), i.clone());
            extended_memory.stack_insert(value.clone(), v.clone());

            c = Expression::And(
                Box::new(c),
                Box::new(Expression::substitute(&extended_memory, inner_expr.clone())),
            );

            let ne = Expression::NE(Box::new(index_id.clone()), Box::new(i.clone()));
            o = Expression::And(Box::new(ne), Box::new(o));
        }

        // E = index >= 0 && O && index < #arr ==> expr
        let i_geq_0 = Expression::GEQ(
            Box::new(index_id.clone()),
            Box::new(Expression::Literal(Literal::Integer(0))),
        );

        // get size from heap and make i < size expression
        let size = match current_memory.heap_get_unsafe(r) {
            ReferenceValue::Array((_, _, size, _)) => size,
            _ => todo!(),
        };

        let i_lt_size = Expression::LT(Box::new(index_id.clone()), Box::new(size.clone()));

        // build inner expression with index and value as freevars
        let mut extended_memory = captured_memory.clone();
        extended_memory.stack_insert(
            index.clone(),
            Expression::FreeVariable(SymType::Int, index.clone()),
        );
        extended_memory.stack_insert(
            value.clone(),
            Expression::FreeVariable(sym_ty.clone(), value.clone()),
        );
        let inner_expr = Expression::substitute(&extended_memory, inner_expr.clone());

        let e = Expression::Implies(
            Box::new(Expression::And(
                Box::new(i_geq_0),
                Box::new(Expression::And(Box::new(o), Box::new(i_lt_size))),
            )),
            Box::new(inner_expr),
        );

        Expression::And(Box::new(c), Box::new(e))
    }
}
/// Intermediate type use to implement custom `Hash` for Expression
/// while also using the default hasher for the 'base values'
#[derive(Hash, Debug, Eq, PartialEq)]
pub enum NormalizedExpression {
    Plus(Vec<NormalizedExpression>),
    Multiply(Vec<NormalizedExpression>),
    Divide(Box<NormalizedExpression>, Box<NormalizedExpression>),
    Mod(Box<NormalizedExpression>, Box<NormalizedExpression>),
    Negative(Box<NormalizedExpression>),
    FreeVariable(SymType, Identifier),
    Reference(Reference),
    Literal(Literal),
    Implies(Box<NormalizedExpression>, Box<NormalizedExpression>),
    And(Vec<NormalizedExpression>),
    Or(Vec<NormalizedExpression>),
    EQ(Box<NormalizedExpression>, Box<NormalizedExpression>),
    NE(Box<NormalizedExpression>, Box<NormalizedExpression>),
    LT(Box<NormalizedExpression>, Box<NormalizedExpression>),
    GT(Box<NormalizedExpression>, Box<NormalizedExpression>),
    GEQ(Box<NormalizedExpression>, Box<NormalizedExpression>),
    LEQ(Box<NormalizedExpression>, Box<NormalizedExpression>),
    Not(Box<NormalizedExpression>),
    Weird(u64), // when something is not normalizable make it weird with a random number e.g. forall expressions
}

impl Expression {

    pub fn normalize(&self) -> NormalizedExpression {
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
        fn collect_and(expr: Expression) -> Vec<Expression> {
            match expr {
                Expression::And(l_expr, r_expr) => {
                    let mut conj = collect_mult(*l_expr);
                    conj.append(&mut collect_mult(*r_expr));
                    conj
                }
                _ => vec![expr],
            }
        }
        fn collect_or(expr: Expression) -> Vec<Expression> {
            match expr {
                Expression::Or(l_expr, r_expr) => {
                    let mut or = collect_mult(*l_expr);
                    or.append(&mut collect_mult(*r_expr));
                    or
                }
                _ => vec![expr],
            }
        }

        match self {
            Expression::Plus(_, _) => {
                let c = 
                    collect_sum(self.clone())
                    .into_iter()
                    .map(|e| e.normalize())
                    .collect();

                NormalizedExpression::Plus(sort_by_hash(c))
            }
            Expression::Multiply(_, _) => {
                let c = 
                    collect_mult(self.clone())
                    .into_iter()
                    .map(|e| e.normalize())
                    .collect();
                NormalizedExpression::Multiply(sort_by_hash(c))
            }
            Expression::And(_, _) => {
                let c = 
                    collect_and(self.clone())
                    .into_iter()
                    .map(|e| e.normalize())
                    .collect();
                NormalizedExpression::And(sort_by_hash(c))
            }
            Expression::Or(_, _) => {
                let c = 
                    collect_or(self.clone())
                    .into_iter()
                    .map(|e| e.normalize())
                    .collect();
                NormalizedExpression::Or(sort_by_hash(c))
            }
            Expression::Minus(l_expr, r_expr) => {
                let (n_l_expr, n_r_expr) = (l_expr.normalize(), r_expr.normalize());
                let sorted = sort_by_hash(vec![
                    n_l_expr,
                    NormalizedExpression::Negative(Box::new(n_r_expr)),
                ]);
                NormalizedExpression::Plus(sorted)
            }
            Expression::Divide(l_expr, r_expr) => NormalizedExpression::Divide(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),

            Expression::Mod(l_expr, r_expr) => NormalizedExpression::Mod(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::Negative(expr) => {
                NormalizedExpression::Negative(Box::new(expr.normalize()))
            }
            Expression::FreeVariable(ty, id) => {
                NormalizedExpression::FreeVariable(ty.clone(), id.clone())
            }
            Expression::Reference(r) => NormalizedExpression::Reference(r.clone()),
            Expression::Literal(lit) => NormalizedExpression::Literal(*lit),
            Expression::Implies(l_expr, r_expr) => NormalizedExpression::Implies(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::EQ(l_expr, r_expr) => NormalizedExpression::EQ(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::NE(l_expr, r_expr) => NormalizedExpression::NE(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::LT(l_expr, r_expr) => NormalizedExpression::LT(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::GT(l_expr, r_expr) => NormalizedExpression::GT(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::GEQ(l_expr, r_expr) => NormalizedExpression::GEQ(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::LEQ(l_expr, r_expr) => NormalizedExpression::LEQ(
                Box::new(l_expr.normalize()),
                Box::new(r_expr.normalize()),
            ),
            Expression::Not(expr) => NormalizedExpression::Not(Box::new(expr.normalize())),
            _ => NormalizedExpression::Weird(rand::random()),
        }
    }
}
fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

// sorts any vector of value based on their hash value
fn sort_by_hash<T: Hash>(v: Vec<T>) -> Vec<T> {
    let mut annotated_v = v
        .into_iter()
        .map(|t| (calculate_hash(&t), t))
        .collect::<Vec<(u64, T)>>();
    annotated_v.sort_by_key(|tuple| tuple.0);
    annotated_v.into_iter().map(|(_, t)| t).collect::<Vec<T>>()
}

impl fmt::Debug for PathConstraints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.combine_over_true())
    }
}
impl fmt::Debug for Forall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "forall {:?}, {}, {} : {:?}",
            self.r, self.index, self.value, self.inner_expr
        )
    }
}

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Implies(l_expr, r_expr) => write!(f, "({:?} ==> {:?})", l_expr, r_expr),
            Expression::Forall(forall) => {
                write!(f, "{:?}", forall)
            }
            Expression::And(l_expr, r_expr) => write!(f, "({:?} && {:?})", l_expr, r_expr),
            Expression::Or(l_expr, r_expr) => write!(f, "({:?} || {:?})", l_expr, r_expr),
            Expression::EQ(l_expr, r_expr) => write!(f, "({:?} == {:?})", l_expr, r_expr),
            Expression::NE(l_expr, r_expr) => write!(f, "({:?} != {:?})", l_expr, r_expr),
            Expression::LT(l_expr, r_expr) => write!(f, "({:?} < {:?})", l_expr, r_expr),
            Expression::GT(l_expr, r_expr) => write!(f, "({:?} > {:?})", l_expr, r_expr),
            Expression::GEQ(l_expr, r_expr) => write!(f, "({:?} >= {:?})", l_expr, r_expr),
            Expression::LEQ(l_expr, r_expr) => write!(f, "({:?} <= {:?})", l_expr, r_expr),
            Expression::Plus(l_expr, r_expr) => write!(f, "({:?} + {:?})", l_expr, r_expr),
            Expression::Minus(l_expr, r_expr) => write!(f, "({:?} - {:?})", l_expr, r_expr),
            Expression::Multiply(l_expr, r_expr) => write!(f, "({:?} * {:?})", l_expr, r_expr),
            Expression::Divide(l_expr, r_expr) => write!(f, "({:?} / {:?})", l_expr, r_expr),
            Expression::Mod(l_expr, r_expr) => write!(f, "({:?} % {:?})", l_expr, r_expr),
            Expression::Negative(expr) => write!(f, "-{:?}", expr),
            Expression::Not(expr) => write!(f, "!{:?}", expr),
            Expression::Literal(Literal::Boolean(val)) => write!(f, "{:?}", val),
            Expression::Literal(Literal::Integer(val)) => write!(f, "{:?}", val),
            Expression::FreeVariable(_, fv) => write!(f, "{}", fv),
            Expression::Reference(r) => write!(f, "{:?}", r),
            Expression::Uninitialized => write!(f, "Uninitialized"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    lalrpop_mod!(pub parser);

    fn parse(i: &str) -> Expression {
        let expr = parser::VerificationExpressionParser::new()
            .parse(i)
            .unwrap();
        Expression::substitute(&SymMemory::new(Program(vec![])), expr)
    }

    #[test]
    fn sum_expr_equivalence() {
        let e1 = parse("1+2+3").normalize();
        let e2 = parse("3+2+1").normalize();
        let e3 = parse("2+3+1").normalize();
        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(calculate_hash(&e1) == calculate_hash(&e3));
        assert!(format!("{:?}", e1) == format!("{:?}", e2) );
        assert!(format!("{:?}", e1)  == format!("{:?}", e3) );
    }
    #[test]
    fn mult_expr_equivalence() {
        let e1 = parse("2*3*4+5-1").normalize();
        let e2 = parse("3*2*4+5-1").normalize();
        let e3 = parse("2*3*4+(-1)+5").normalize();

        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(calculate_hash(&e1) == calculate_hash(&e3));
        assert!(format!("{:?}", e1) == format!("{:?}", e2) );
        assert!(format!("{:?}", e1)  == format!("{:?}", e3) );
    }
    #[test]
    fn more_expr_equivalence() {
        let e1 = parse("(7*4+5/8%5)+3").normalize();
        let e2 = parse("3+(4*7+5/8%5)").normalize();
        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(format!("{:?}", e1) == format!("{:?}", e2) );
    }
    #[test]
    fn int_comparison() {
        let e1 = parse("1").normalize();
        let e2 = parse("1").normalize();
        let e3 = parse("123").normalize();
        assert!(calculate_hash(&e1) == calculate_hash(&e2));
        assert!(calculate_hash(&e2) != calculate_hash(&e3));
        assert!(format!("{:?}", e1) == format!("{:?}", e2) );
        assert!(format!("{:?}", e1)  != format!("{:?}", e3) );
    }
}
