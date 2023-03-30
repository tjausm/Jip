//! Symbolic types representing the values on the stack while symbolically executing a program
//!

use core::fmt;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

use super::ref_values::{ArrSize, ArrSizes, Array, LazyReference, Reference, SymRefType, ReferenceValue};
use crate::{ast::*, shared::panic_with_diagnostics, symbolic::memory::SymMemory};

#[derive(Clone)]
pub struct PathConstraints {
    constraints: Vec<PathConstraint>,
}

#[derive(Clone)]
pub enum PathConstraint {
    Assert(SymExpression),
    Assume(SymExpression),
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
    pub fn combine_over_true(&self) -> SymExpression {
        let mut constraints = SymExpression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(expr) => {
                    constraints = SymExpression::And(Box::new(expr.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(expr) => {
                    constraints =
                        SymExpression::Implies(Box::new(expr.clone()), Box::new(constraints));
                }
            }
        }

        return constraints;
    }
    /// combine constraints as a conjunction as follows: `assume(a), assert(b) -> a && b`
    pub fn conjunct(&self) -> SymExpression {
        let mut constraints = SymExpression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(expr) => {
                    constraints = SymExpression::And(Box::new(expr.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(expr) => {
                    constraints = SymExpression::And(Box::new(expr.clone()), Box::new(constraints));
                }
            }
        }

        return constraints;
    }

    /// adds a new constraint
    pub fn push_assertion(&mut self, assertion: SymExpression) {
        self.constraints.push(PathConstraint::Assert(assertion));
    }
    /// adds a new constraint
    pub fn push_assumption(&mut self, assumption: SymExpression) {
        self.constraints.push(PathConstraint::Assume(assumption));
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SymType {
    Int,
    Bool,
    Ref(SymRefType),
}




#[derive(Clone)]
pub enum SymExpression {
    Implies(Box<SymExpression>, Box<SymExpression>),
    Forall(Forall),
    Exists(Identifier, Identifier, Identifier, Box<Expression>),
    And(Box<SymExpression>, Box<SymExpression>),
    Or(Box<SymExpression>, Box<SymExpression>),
    EQ(Box<SymExpression>, Box<SymExpression>),
    NE(Box<SymExpression>, Box<SymExpression>),
    LT(Box<SymExpression>, Box<SymExpression>),
    GT(Box<SymExpression>, Box<SymExpression>),
    GEQ(Box<SymExpression>, Box<SymExpression>),
    LEQ(Box<SymExpression>, Box<SymExpression>),
    Plus(Box<SymExpression>, Box<SymExpression>),
    Minus(Box<SymExpression>, Box<SymExpression>),
    Multiply(Box<SymExpression>, Box<SymExpression>),
    Divide(Box<SymExpression>, Box<SymExpression>),
    Mod(Box<SymExpression>, Box<SymExpression>),
    Negative(Box<SymExpression>),
    Not(Box<SymExpression>),
    Literal(Literal),
    FreeVariable(SymType, Identifier),
    SizeOf(Reference, Box<SymExpression>, Option<ArrSize>),
    Reference(Reference),
    LazyReference(LazyReference),
    Uninitialized,
}

impl SymExpression {
    /// destructs forall and exists quantifiers and then
    /// generates a substituted expression from it
    pub fn new(sym_memory: &SymMemory, expr: Expression) -> Self {
        match expr {
            Expression::Forall(arr_name, index, value, inner_expr) => {
                let r = match sym_memory.stack_get(&arr_name){
                    Some(SymExpression::Reference(r)) => r,
                    Some(_) => panic_with_diagnostics(&format!("In '{:?}' identifier {} is not a reference", inner_expr, arr_name), &sym_memory),
                    None => panic_with_diagnostics(&format!("In '{:?}' identifier {} is not declared", inner_expr, arr_name), &sym_memory),
                };
                SymExpression::Forall(Forall::new(r, index, value, *inner_expr, sym_memory.clone()))
            },
            Expression::Exists(arr_name, index, value, expr) => todo!(),
            Expression::Identifier(id) => match sym_memory.stack_get(&id) {
                Some(sym_expr) => sym_expr,
                _ => panic_with_diagnostics(&format!("{} was not declared", id), &sym_memory),
            },
            Expression::SizeOf(arr_name) => {
                let r = match sym_memory.stack_get(&arr_name) {
                    Some(SymExpression::Reference(r)) => r,
                    _ => panic_with_diagnostics(
                        &format!(
                            "identifier {} in expression #{:?} does not refer to an array",
                            arr_name,
                            Expression::SizeOf(arr_name.clone())
                        ),
                        &sym_memory,
                    ),
                };
                SymExpression::SizeOf(
                    r,
                    Box::new(sym_memory.heap_get_arr_length(&arr_name)),
                    None,
                )
            }
            Expression::Implies(l, r) => SymExpression::Implies(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::And(l, r) => SymExpression::And(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Or(l, r) => SymExpression::Or(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::EQ(l, r) => SymExpression::EQ(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::NE(l, r) => SymExpression::NE(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::LT(l, r) => SymExpression::LT(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::GT(l, r) => SymExpression::GT(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::GEQ(l, r) => SymExpression::GEQ(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::LEQ(l, r) => SymExpression::LEQ(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Plus(l, r) => SymExpression::Plus(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Minus(l, r) => SymExpression::Minus(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Multiply(l, r) => SymExpression::Multiply(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Divide(l, r) => SymExpression::Divide(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Mod(l, r) => SymExpression::Mod(
                Box::new(SymExpression::new(sym_memory, *l)),
                Box::new(SymExpression::new(sym_memory, *r)),
            ),
            Expression::Negative(expr) => {
                SymExpression::Negative(Box::new(SymExpression::new(sym_memory, *expr)))
            }
            Expression::Not(expr) => {
                SymExpression::Not(Box::new(SymExpression::new(sym_memory, *expr)))
            }
            Expression::Literal(lit) => SymExpression::Literal(lit),
        }
    }

    /// front end simplifier, only pass sizes if we want to use them in simplification
    pub fn simplify(self, sizes: Option<&ArrSizes>) -> Self {
        match &self {
            SymExpression::And(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (SymExpression::Literal(Literal::Boolean(false)), _) => {
                        SymExpression::Literal(Literal::Boolean(false))
                    }
                    (_, SymExpression::Literal(Literal::Boolean(false))) => {
                        SymExpression::Literal(Literal::Boolean(false))
                    }
                    (
                        SymExpression::Literal(Literal::Boolean(true)),
                        SymExpression::Literal(Literal::Boolean(true)),
                    ) => SymExpression::Literal(Literal::Boolean(true)),
                    (l_simple, r_simple) => {
                        SymExpression::And(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::Or(l, r) => match (l.clone().simplify(sizes), r.clone().simplify(sizes))
            {
                (SymExpression::Literal(Literal::Boolean(true)), _) => {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                (_, SymExpression::Literal(Literal::Boolean(true))) => {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                (l_simple, r_simple) => SymExpression::Or(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::Implies(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (SymExpression::Literal(Literal::Boolean(false)), _) => {
                        SymExpression::Literal(Literal::Boolean(true))
                    }
                    (_, SymExpression::Literal(Literal::Boolean(true))) => {
                        SymExpression::Literal(Literal::Boolean(true))
                    }
                    (
                        SymExpression::Literal(Literal::Boolean(_)),
                        SymExpression::Literal(Literal::Boolean(_)),
                    ) => SymExpression::Literal(Literal::Boolean(false)),
                    (l_simple, r_simple) => {
                        SymExpression::Implies(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::EQ(l, r) => match (l.clone().simplify(sizes), r.clone().simplify(sizes))
            {
                // if lit or fv are equal => true
                (SymExpression::Literal(l_lit), SymExpression::Literal(r_lit)) => {
                    SymExpression::Literal(Literal::Boolean(l_lit == r_lit))
                }
                (SymExpression::FreeVariable(_, l_fv), SymExpression::FreeVariable(__, r_fv))
                    if l_fv == r_fv =>
                {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                //if sizeOfs or range's inner-expressions hash equals hash of other => true
                (SymExpression::SizeOf( _, size, _), r_expr)
                    if size.clone().simplify(sizes) == r_expr.clone() =>
                {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                (l_expr, SymExpression::SizeOf( _, size, _))
                    if l_expr.clone() == size.clone().simplify(sizes) =>
                {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                //if ArrSize is point and point == other side
                (
                    SymExpression::SizeOf( _, _, Some(ArrSize::Point(n))),
                    SymExpression::Literal(Literal::Integer(m)),
                ) if n == m => SymExpression::Literal(Literal::Boolean(true)),
                (
                    SymExpression::Literal(Literal::Integer(m)),
                    SymExpression::SizeOf( _, _, Some(ArrSize::Point(n))),
                ) if n == m => SymExpression::Literal(Literal::Boolean(true)),
                (l_simple, r_simple) => SymExpression::EQ(Box::new(l_simple), Box::new(r_simple)),
            },
            // if both sides are literal simplify
            SymExpression::NE(l, r) => match (l.clone().simplify(sizes), r.clone().simplify(sizes))
            {
                (SymExpression::Literal(l_lit), SymExpression::Literal(r_lit)) => {
                    SymExpression::Literal(Literal::Boolean(l_lit != r_lit))
                }
                (l_simple, r_simple) => SymExpression::NE(Box::new(l_simple), Box::new(r_simple)),
            },

            SymExpression::LT(l, r) => match (l.clone().simplify(sizes), r.clone().simplify(sizes))
            {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Boolean(l_lit < r_lit)),
                (
                    SymExpression::SizeOf( _, _, Some(size)),
                    SymExpression::Literal(Literal::Integer(n)),
                ) if size.lt(&ArrSize::Point(n)).is_some() => {
                    let b = size.lt(&ArrSize::Point(n)).unwrap();
                    SymExpression::Literal(Literal::Boolean(b))
                }
                (
                    SymExpression::Literal(Literal::Integer(n)),
                    SymExpression::SizeOf( _, _, Some(size)),
                ) if ArrSize::Point(n).lt(&size).is_some() => {
                    let b = ArrSize::Point(n).lt(&size).unwrap();
                    SymExpression::Literal(Literal::Boolean(b))
                }
                (
                    SymExpression::SizeOf( _, _, Some(l_size)),
                    SymExpression::SizeOf( _, _, Some(r_size)),
                ) if l_size.lt(&r_size).is_some() => {
                    let b = l_size.lt(&r_size).unwrap();
                    SymExpression::Literal(Literal::Boolean(b))
                }
                (l_simple, r_simple) => SymExpression::LT(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::GT(l, r) => match (l.clone().simplify(sizes), r.clone().simplify(sizes))
            {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Boolean(l_lit > r_lit)),
                (
                    SymExpression::SizeOf( _, _, Some(size)),
                    SymExpression::Literal(Literal::Integer(n)),
                ) if size.gt(&ArrSize::Point(n)).is_some() => {
                    let b = size.gt(&ArrSize::Point(n)).unwrap();
                    SymExpression::Literal(Literal::Boolean(b))
                }
                (
                    SymExpression::Literal(Literal::Integer(n)),
                    SymExpression::SizeOf( _, _, Some(size)),
                ) if ArrSize::Point(n).gt(&size).is_some() => {
                    let b = ArrSize::Point(n).gt(&size).unwrap();
                    SymExpression::Literal(Literal::Boolean(b))
                }
                (
                    SymExpression::SizeOf( _, _, Some(l_size)),
                    SymExpression::SizeOf( _, _, Some(r_size)),
                ) if l_size.gt(&r_size).is_some() => {
                    let b = l_size.gt(&r_size).unwrap();
                    SymExpression::Literal(Literal::Boolean(b))
                }
                (l_simple, r_simple) => SymExpression::GT(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::GEQ(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Boolean(l_lit >= r_lit)),
                    (
                        SymExpression::SizeOf( _, _, Some(size)),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) if size.ge(&ArrSize::Point(n)).is_some() => {
                        let b = size.ge(&ArrSize::Point(n)).unwrap();
                        SymExpression::Literal(Literal::Boolean(b))
                    }
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf( _, _, Some(size)),
                    ) if ArrSize::Point(n).ge(&size).is_some() => {
                        let b = ArrSize::Point(n).ge(&size).unwrap();
                        SymExpression::Literal(Literal::Boolean(b))
                    }
                    (
                        SymExpression::SizeOf( _, _, Some(l_size)),
                        SymExpression::SizeOf( _, _, Some(r_size)),
                    ) if l_size.ge(&r_size).is_some() => {
                        let b = l_size.ge(&r_size).unwrap();
                        SymExpression::Literal(Literal::Boolean(b))
                    }
                    (l_simple, r_simple) => {
                        SymExpression::GEQ(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }

            SymExpression::LEQ(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Boolean(l_lit <= r_lit)),
                    (
                        SymExpression::SizeOf( _, _, Some(size)),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) if size.le(&ArrSize::Point(n)).is_some() => {
                        let b = size.le(&ArrSize::Point(n)).unwrap();
                        SymExpression::Literal(Literal::Boolean(b))
                    }
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf( _, _, Some(size)),
                    ) if ArrSize::Point(n).le(&size).is_some() => {
                        let b = ArrSize::Point(n).le(&size).unwrap();
                        SymExpression::Literal(Literal::Boolean(b))
                    }
                    (
                        SymExpression::SizeOf( _, _, Some(l_size)),
                        SymExpression::SizeOf( _, _, Some(r_size)),
                    ) if l_size.le(&r_size).is_some() => {
                        let b = l_size.le(&r_size).unwrap();
                        SymExpression::Literal(Literal::Boolean(b))
                    }
                    (l_simple, r_simple) => {
                        SymExpression::LEQ(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }

            SymExpression::Plus(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Integer(l_lit + r_lit)),
                    (l_simple, r_simple) => {
                        SymExpression::Plus(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::Minus(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Integer(l_lit - r_lit)),
                    (l_simple, r_simple) => {
                        SymExpression::Minus(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::Multiply(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Integer(l_lit * r_lit)),
                    (l_simple, r_simple) => {
                        SymExpression::Multiply(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::Divide(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Integer(l_lit / r_lit)),
                    (l_simple, r_simple) => {
                        SymExpression::Divide(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::Mod(l, r) => {
                match (l.clone().simplify(sizes), r.clone().simplify(sizes)) {
                    (
                        SymExpression::Literal(Literal::Integer(l_lit)),
                        SymExpression::Literal(Literal::Integer(r_lit)),
                    ) => SymExpression::Literal(Literal::Integer(l_lit % r_lit)),
                    (l_simple, r_simple) => {
                        SymExpression::Mod(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            SymExpression::Not(expr) => match expr.clone().simplify(sizes) {
                SymExpression::Not(inner_expr) => inner_expr.clone().simplify(sizes),
                SymExpression::Literal(Literal::Boolean(b)) => {
                    SymExpression::Literal(Literal::Boolean(!b))
                }
                simple_expr => SymExpression::Not(Box::new(simple_expr)),
            },
            SymExpression::SizeOf( r, expr, _) => match (expr.clone().simplify(sizes), sizes) {
                (SymExpression::Literal(lit), _) => SymExpression::Literal(lit),
                (_, Some(sizes)) => {
                    SymExpression::SizeOf( r.clone(), expr.clone(), sizes.get(r))
                }
                _ => self,
            },
            SymExpression::Negative(expr) => match expr.clone().simplify(sizes){
                SymExpression::Literal(Literal::Integer(n)) => SymExpression::Literal(Literal::Integer(-n)),
                expr => SymExpression::Negative(Box::new(expr))
            },
            SymExpression::Literal(_) => self,
            SymExpression::FreeVariable(_, _) => self,
            SymExpression::Reference(_) => self,
            SymExpression::LazyReference(_) => self,
            
                // annotate forall with curr infered size if available
            SymExpression::Forall(f) => {
                let mut ann_f = f.clone();
                ann_f.sizes = sizes.cloned();
                SymExpression::Forall(ann_f.clone())
            },
            SymExpression::Exists(_, _, _, _) => self,
            SymExpression::Uninitialized => panic_with_diagnostics(
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
    inner_expr:Expression,
    captured_memory: SymMemory,
    pub sizes: Option<ArrSizes>
}

impl Forall {
    fn new(    r: Reference,
        index: Identifier,
        value: Identifier,
        inner_expr:Expression,
        captured_memory: SymMemory) -> Self {
        Self { r, index, value, inner_expr, captured_memory, sizes: None }
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
    pub fn construct(&self, current_memory: &SymMemory) -> SymExpression {
        let (r, index, value, inner_expr, captured_memory) = (self.r, &self.index,  &self.value, &self.inner_expr, &self.captured_memory);
        let index_id = SymExpression::FreeVariable(SymType::Int, index.clone());


        let (sym_ty, arr, size_expr, _) = match current_memory.heap_get(r){
            ReferenceValue::Array(arr) => arr,
            _ => panic_with_diagnostics(&format!("Can't quantify over {:?} since it does not refer to an array", r), &current_memory),

        };

        // foreach (i, v) pair in arr:
        // - C = for each[i |-> index, v |-> value]expr && C
        // - O = index != i && O
        let mut c = SymExpression::Literal(Literal::Boolean(true));
        let mut o = SymExpression::Literal(Literal::Boolean(true));
        for (i, v) in arr.into_iter() {
            // we insert index and value substitutions into stack
            // and build a new inner_expression with said substitutions
            let mut extended_memory = captured_memory.clone();
            extended_memory.stack_insert(index.clone(), i.clone());
            extended_memory.stack_insert(value.clone(), v.clone());
    
            c = SymExpression::And(
                Box::new(c),
                Box::new(SymExpression::new(&extended_memory, inner_expr.clone())),
            );
    
            let ne = SymExpression::NE(Box::new(index_id.clone()), Box::new(i.clone()));
            o = SymExpression::And(Box::new(ne), Box::new(o));
        }
    
        // E = index >= 0 && O && index < #arr ==> expr
        let i_geq_0 = SymExpression::GEQ(
            Box::new(index_id.clone()),
            Box::new(SymExpression::Literal(Literal::Integer(0))),
        );
    
        let size = self.sizes.as_ref().map(|s| s.get(&r)).flatten();
        let i_lt_size = SymExpression::LT(
            Box::new(index_id.clone()),
            Box::new(SymExpression::SizeOf(
                r,
                Box::new(size_expr.clone()),
                size,
            )),
        );
    
        // build inner expression with index and value as freevars
        let mut extended_memory = captured_memory.clone();
        extended_memory.stack_insert(
            index.clone(),
            SymExpression::FreeVariable(SymType::Int, index.clone()),
        );
        extended_memory.stack_insert(
            value.clone(),
            SymExpression::FreeVariable(sym_ty.clone(), value.clone()),
        );
        let inner_expr = SymExpression::new(&extended_memory, inner_expr.clone());
    
        let e = SymExpression::Implies(
            Box::new(SymExpression::And(
                Box::new(i_geq_0),
                Box::new(SymExpression::And(Box::new(o), Box::new(i_lt_size))),
            )),
            Box::new(inner_expr),
        );
    
        SymExpression::And(Box::new(c), Box::new(e))
      
    }
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
    FreeVariable(SymType, Identifier),
    SizeOf(Reference),
    Reference(Reference),
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

impl Hash for SymExpression {
    fn hash<H: Hasher>(&self, state: &mut H) {
        fn collect_sum(expr: SymExpression) -> Vec<SymExpression> {
            match expr {
                SymExpression::Plus(l_expr, r_expr) => {
                    let mut sum = collect_sum(*l_expr);
                    sum.append(&mut collect_sum(*r_expr));
                    sum
                }
                SymExpression::Minus(l_expr, r_expr) => collect_sum(SymExpression::Plus(
                    l_expr,
                    Box::new(SymExpression::Negative(r_expr)),
                )),
                _ => vec![expr],
            }
        }

        fn collect_mult(expr: SymExpression) -> Vec<SymExpression> {
            match expr {
                SymExpression::Multiply(l_expr, r_expr) => {
                    let mut mult = collect_mult(*l_expr);
                    mult.append(&mut collect_mult(*r_expr));
                    mult
                }
                _ => vec![expr],
            }
        }

        match self {
            SymExpression::Plus(_, _) => {
                let sum = collect_sum(self.clone());
                let mut hashed_sum = map_hash(&sum);
                hashed_sum.sort();
                HashExpression::Plus(hashed_sum).hash(state)
            }
            SymExpression::Multiply(_, _) => {
                let mult = collect_mult(self.clone());
                let mut hashed_mult = map_hash(&mult);
                hashed_mult.sort();
                HashExpression::Multiply(hashed_mult).hash(state)
            }
            SymExpression::Minus(l_expr, r_expr) => SymExpression::Plus(
                l_expr.clone(),
                Box::new(SymExpression::Negative(r_expr.clone())),
            )
            .hash(state),
            SymExpression::Divide(l_expr, r_expr) => {
                HashExpression::Divide(calculate_hash(&*l_expr), calculate_hash(&*r_expr))
                    .hash(state)
            }
            SymExpression::Mod(l_expr, r_expr) => {
                HashExpression::Mod(calculate_hash(&*l_expr), calculate_hash(&*r_expr)).hash(state)
            }
            SymExpression::Negative(expr) => {
                HashExpression::Negative(calculate_hash(&*expr)).hash(state)
            }
            SymExpression::SizeOf( r, _, _) => HashExpression::SizeOf(r.clone()).hash(state),
            SymExpression::FreeVariable(ty, id) => {
                HashExpression::FreeVariable(ty.clone(), id.clone()).hash(state)
            }
            SymExpression::Reference(r) => HashExpression::Reference(r.clone()).hash(state),
            SymExpression::Literal(lit) => lit.hash(state),
            _ => panic_with_diagnostics(&format!("Cannot hash expression {:?}", self), &()),
        }
    }
}

impl PartialEq for SymExpression {
    fn eq(&self, other: &Self) -> bool {
        calculate_hash(&self) == calculate_hash(other)
    }
}
impl Eq for SymExpression {}

impl fmt::Debug for PathConstraints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.combine_over_true())
    }
}
impl fmt::Debug for Forall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "forall {:?}, {}, {} : {:?}", self.r, self.index, self.value, self.inner_expr)
    }
}

impl fmt::Debug for SymExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymExpression::Implies(l_expr, r_expr) => write!(f, "({:?} ==> {:?})", l_expr, r_expr),
            SymExpression::Forall(forall) => {
                write!(f, "{:?}", forall)
            }
            SymExpression::Exists(arr, i, v, body) => {
                write!(f, "exists {}, {}, {} : {:?}", arr, i, v, body)
            }
            SymExpression::And(l_expr, r_expr) => write!(f, "({:?} && {:?})", l_expr, r_expr),
            SymExpression::Or(l_expr, r_expr) => write!(f, "({:?} || {:?})", l_expr, r_expr),
            SymExpression::EQ(l_expr, r_expr) => write!(f, "({:?} == {:?})", l_expr, r_expr),
            SymExpression::NE(l_expr, r_expr) => write!(f, "({:?} != {:?})", l_expr, r_expr),
            SymExpression::LT(l_expr, r_expr) => write!(f, "({:?} < {:?})", l_expr, r_expr),
            SymExpression::GT(l_expr, r_expr) => write!(f, "({:?} > {:?})", l_expr, r_expr),
            SymExpression::GEQ(l_expr, r_expr) => write!(f, "({:?} >= {:?})", l_expr, r_expr),
            SymExpression::LEQ(l_expr, r_expr) => write!(f, "({:?} <= {:?})", l_expr, r_expr),
            SymExpression::Plus(l_expr, r_expr) => write!(f, "({:?} + {:?})", l_expr, r_expr),
            SymExpression::Minus(l_expr, r_expr) => write!(f, "({:?} - {:?})", l_expr, r_expr),
            SymExpression::Multiply(l_expr, r_expr) => write!(f, "({:?} * {:?})", l_expr, r_expr),
            SymExpression::Divide(l_expr, r_expr) => write!(f, "({:?} / {:?})", l_expr, r_expr),
            SymExpression::Mod(l_expr, r_expr) => write!(f, "({:?} % {:?})", l_expr, r_expr),
            SymExpression::Negative(expr) => write!(f, "-{:?}", expr),
            SymExpression::Not(expr) => write!(f, "!{:?}", expr),
            SymExpression::Literal(Literal::Boolean(val)) => write!(f, "{:?}", val),
            SymExpression::Literal(Literal::Integer(val)) => write!(f, "{:?}", val),
            SymExpression::FreeVariable(_, fv) => write!(f, "{}", fv),
            SymExpression::SizeOf( r, _, s) => {
                if let Some(size) = s {
                    write!(f, "(#{:?} -> {:?})", r, size)
                } else {
                    write!(f, "#{:?}", r)
                }
            }
            SymExpression::Reference(r) => write!(f, "{:?}", r),
            SymExpression::LazyReference(lr) => write!(f, "{:?}", lr),
            SymExpression::Uninitialized => write!(f, "Uninitialized"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    lalrpop_mod!(pub parser);

 fn parse(i: &str) -> SymExpression {
     let expr = parser::VerificationExpressionParser::new()
         .parse(i)
         .unwrap();
     SymExpression::new(&SymMemory::new(Program(vec![])), expr)
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
}
