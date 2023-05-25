//! Symbolic model representing the values on the heap while symbolically executing a program
//!
use super::{
    expression::{PathConstraints, SymExpression, SymType},
    memory::SymMemory,
};
use crate::{
    ast::*,
    shared::{panic_with_diagnostics, Error},
    smt_solver::SolverEnv,
};
use core::fmt;
use infinitable::Infinitable;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    cmp::Ordering,
    collections::hash_map::Iter,
    ops::{Add, Mul, Sub},
};

/// tracks if reference is already initialized
pub type EvaluatedRefs = FxHashSet<i32>;

global_counter!(REF_COUNTER, i32, 1);

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Reference {
    Evaluated(i32),
    Lazy { r: i32, class: Identifier },
}

impl Reference {
    /// generates unique reference using a global counter
    pub fn new_evaluated() -> Reference {
        let i = REF_COUNTER.get_cloned();
        REF_COUNTER.inc();
        Reference::Evaluated(i)
    }

    pub fn new_lazy(class: Identifier) -> Self {
        let r = REF_COUNTER.get_cloned();
        REF_COUNTER.inc();
        Reference::Lazy { r, class }
    }
    /// returns the null reference
    pub fn null() -> Reference {
        Reference::Evaluated(0)
    }

    fn is_never_null(
        &self,
        solver: &mut SolverEnv,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &EvaluatedRefs,
        sym_memory: &SymMemory,
    ) -> Result<bool, Error> {
        let simplify = solver.config.expression_evaluation;

        // check if path is feasible
        let mut pc = pc.conjunct();
        if simplify {
            pc = pc.eval(i, Some(eval_refs));
            match pc {
                SymExpression::Literal(Literal::Boolean(false)) => return Ok(false),
                _ => (),
            }
        }
        if solver.verify_expr(&pc, sym_memory, i).is_none() {
            return Ok(false);
        }

        // if it's feasible we check if ref is never null
        let ref_is_null = SymExpression::EQ(
            Box::new(SymExpression::Reference(self.clone())),
            Box::new(SymExpression::Reference(Reference::null())),
        );
        let mut pc_null_check = SymExpression::And(Box::new(pc), Box::new(ref_is_null));
        if simplify {
            pc_null_check = pc_null_check.eval(i, Some(eval_refs));
            match pc_null_check {
                SymExpression::Literal(Literal::Boolean(true)) => return Ok(true),
                _ => (),
            }
        }

        match solver.verify_expr(&pc_null_check, sym_memory, i) {
            None => Ok(true),
            Some(model) => Err(Error::Verification(format!(
                "Reference {:?} could possibly be null:\n{:?}",
                self.get_unsafe(),
                model
            ))),
        }
    }

    /// returns the value of the reference without checking the reference
    pub fn get_unsafe(&self) -> i32 {
        match self {
            Reference::Evaluated(r) => *r,
            Reference::Lazy { r, class } => *r,
        }
    }

    // returns inner-value of reference, while accounting for the reference being (possibly) null but (possibly) on an infeasible path
    pub fn get(
        &self,
        solver: &mut SolverEnv,
        sym_memory: &mut SymMemory,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &mut EvaluatedRefs,
    ) -> Result<Option<i32>, Error> {

        match self {
            // if null reference make sure path is infeasible
            Reference::Evaluated(0) => match solver.verify_expr(&pc.conjunct(), sym_memory, i) {
                Some(model) => Err(Error::Verification(format!("Reference is null:\n{:?}", model))),
                None => Ok(None),
            },
            // if evaluated save and return
            Reference::Evaluated(r) => {
                eval_refs.insert(*r);
                Ok(Some(*r))
            }
            // if lazy, make sure it's feasible and not null and return
            Reference::Lazy { r, class } => {
                // try to add ref to hashset, and if it was already present return
                if eval_refs.contains(&r) {
                    return Ok(Some(*r));
                };
                let feasible = self.is_never_null(solver, pc, i, eval_refs, sym_memory)?;
                if feasible {
                    // insert fresh lazy object into heap
                    let obj = sym_memory.init_lazy_object(*r, class.clone());
                    sym_memory.heap_insert(Some(self.clone()), obj);

                    //update evaluated refs & return
                    eval_refs.insert(*r);
                    Ok(Some(*r))
                } else {
                    Ok(None)
                }
            }
        }
    }
}

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (Identifier, FxHashMap<Identifier, SymExpression>);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SymRefType {
    Array(Box<SymType>),
    Object(Identifier),
}

#[derive(Clone)]
pub enum ReferenceValue {
    Object(Object),
    Array(Array),
}

pub type IsLazy = bool;

/// Consists of type, a mapping from expression to symbolic expression, expression representing size and flag to indicate that we should lazily initialize objects from this array
pub type Array = (
    SymType,
    FxHashMap<SymExpression, SymExpression>,
    SymExpression,
    IsLazy,
);

#[derive(Clone, Copy, PartialEq)]
pub struct Interval(pub Infinitable<i64>, pub Infinitable<i64>);

impl Default for Interval {
    fn default() -> Self {
        Interval(Infinitable::NegativeInfinity, Infinitable::Infinity)
    }
}

impl Add for Interval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let ((a, b), (c, d)) = (self.get(), rhs.get());
        let lower = match (a, c) {
            (Infinitable::NegativeInfinity, _) => Infinitable::NegativeInfinity,
            (_, Infinitable::NegativeInfinity) => Infinitable::NegativeInfinity,
            _ => a + c,
        };
        let upper = match (b, d) {
            (Infinitable::Infinity, _) => Infinitable::Infinity,
            (_, Infinitable::Infinity) => Infinitable::Infinity,
            _ => b + d,
        };
        Interval::new(lower, upper)
    }
}
impl Sub for Interval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let ((a, b), (c, d)) = (self.get(), rhs.get());

        let lower = match (a, c) {
            (Infinitable::NegativeInfinity, _) => Infinitable::NegativeInfinity,
            (_, Infinitable::NegativeInfinity) => Infinitable::NegativeInfinity,
            _ => a - c,
        };
        let upper = match (b, d) {
            (Infinitable::Infinity, _) => Infinitable::Infinity,
            (_, Infinitable::Infinity) => Infinitable::Infinity,
            _ => b - d,
        };
        Interval::new(lower, upper)
    }
}

impl Mul for Interval {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let ((a, b), (c, d)) = (self.get(), rhs.get());

        // if one of the 2 sides is infinite, just return
        match (a.is_finite() && b.is_finite(), c.is_finite() && d.is_finite()) {
            (false, _) => self,
            (_, false) => rhs,
            _ => {
                let products = [a * c, a * d, b * c, b * d];
                Interval::new(
                    *products.iter().min().unwrap_or(&a.min(c)),
                    *products.iter().max().unwrap_or(&b.max(d)),
                )
            },
        }

    }
}

impl Interval {
    pub fn new(b: Infinitable<i64>, u: Infinitable<i64>) -> Interval {
        Interval(b, u)
    }
    pub fn get(self) -> (Infinitable<i64>, Infinitable<i64>) {
        (self.0, self.1)
    }

    // return most pessimistic interval, return
    pub fn broaden(self, other: Interval) -> Self {
        let min = self.0.min(other.0);
        let max = self.1.max(other.1);
        Interval(min, max.max(min))
    }

    pub fn narrow(self, other: Interval) -> Self {
        let min = self.0.max(other.0);
        let max = self.1.min(other.1);
        Interval(min, max.max(min))
    }

    pub fn infer(e: &SymExpression, i: &IntervalMap) -> Interval {
        match e {
            SymExpression::Literal(Literal::Integer(z)) => {
                Interval::new(Infinitable::Finite(*z), Infinitable::Finite(*z))
            }
            SymExpression::FreeVariable(SymType::Int, x) => i.get(x),
            SymExpression::Plus(l_expr, r_expr) => {
                Interval::infer(l_expr, i) + Interval::infer(r_expr, i)
            }
            SymExpression::Minus(l_expr, r_expr) => {
                Interval::infer(l_expr, i) - Interval::infer(r_expr, i)
            }
            SymExpression::Multiply(l_expr, r_expr) => {
                Interval::infer(l_expr, i) * Interval::infer(r_expr, i)
            }
            SymExpression::Negative(expr) => {
                Interval::new(Infinitable::Finite(-1), Infinitable::Finite(-1))
                    * Interval::infer(expr, i)
            }
            _ => Interval::default(),
        }
    }
}

#[derive(Clone)]
pub struct IntervalMap(FxHashMap<Identifier, Interval>);

impl Default for IntervalMap {
    fn default() -> Self {
        Self(FxHashMap::default())
    }
}

impl IntervalMap {
    fn broaden(&mut self, other: &IntervalMap) {
        let mut keys: FxHashSet<Identifier> = self.0.clone().into_keys().collect();
        keys.extend(
            other
                .0
                .clone()
                .into_keys()
                .collect::<FxHashSet<Identifier>>(),
        );
        for k in keys {
            self.0
                .insert(k.clone(), self.get(&k).broaden(other.get(&k)));
        }
    }

    fn narrow(&mut self, other: &IntervalMap) {
        let mut keys: FxHashSet<Identifier> = self.0.clone().into_keys().collect();
        keys.extend(
            other
                .0
                .clone()
                .into_keys()
                .collect::<FxHashSet<Identifier>>(),
        );
        for k in keys {
            self.0.insert(k.clone(), self.get(&k).narrow(other.get(&k)));
        }
    }

    pub fn get(&self, id: &Identifier) -> Interval {
        match self.0.get(id) {
            Some(i) => *i,
            None => Interval::default(),
        }
    }

    // updates IntervalMap with information from passed expression
    fn infer(&mut self, e: &SymExpression) {
        match e {
            SymExpression::And(l_expr, r_expr) => {
                let mut i1 = self.clone();
                i1.infer(r_expr);
                self.infer(l_expr);
                self.narrow(&i1);
            }
            SymExpression::Or(l_expr, r_expr) => {
                let mut i1 = self.clone();
                i1.infer(r_expr);
                self.infer(l_expr);
                self.broaden(&i1);
            }
            SymExpression::EQ(l_expr, r_expr) => match (&**l_expr, &**r_expr) {
                (
                    SymExpression::FreeVariable(SymType::Int, x1),
                    SymExpression::FreeVariable(SymType::Int, x2),
                ) => {
                    let i = self.get(x1).narrow(self.get(x2));
                    self.0.insert(x1.clone(), i);
                    self.0.insert(x2.clone(), i);
                }
                (SymExpression::FreeVariable(SymType::Int, x1), r_expr) => {
                    let i = self.get(x1).narrow(Interval::infer(r_expr, &self));
                    self.0.insert(x1.clone(), i);
                }
                (l_expr, (SymExpression::FreeVariable(SymType::Int, x2))) => {
                    let i = self.get(x2).narrow(Interval::infer(l_expr, &self));
                    self.0.insert(x2.clone(), i);
                }
                _ => (),
            },
            SymExpression::Not(expr) => match *expr.clone() {
                SymExpression::LT(l_expr, r_expr) => {
                    self.infer(&SymExpression::GEQ(l_expr, r_expr))
                }
                SymExpression::GT(l_expr, r_expr) => {
                    self.infer(&SymExpression::LEQ(l_expr, r_expr))
                }
                SymExpression::GEQ(l_expr, r_expr) => {
                    self.infer(&SymExpression::LT(l_expr, r_expr))
                }
                SymExpression::LEQ(l_expr, r_expr) => {
                    self.infer(&SymExpression::GT(l_expr, r_expr))
                }
                _ => (),
            },
            SymExpression::LT(l_expr, r_expr) => match (&**l_expr, &**r_expr) {
                (SymExpression::FreeVariable(SymType::Int, x), r_expr) => {
                    let (a, _) = Interval::infer(r_expr, self).get(); // abort inference if compared value is not finite

                    if !a.is_finite() {
                        return;
                    }

                    let i = self.get(x).narrow(Interval::new(
                        Infinitable::NegativeInfinity,
                        a - infinitable::Finite(1),
                    ));
                    self.0.insert(x.clone(), i);
                }
                (l_expr, (SymExpression::FreeVariable(SymType::Int, x))) => {
                    let (_, b) = Interval::infer(l_expr, self).get();
                    if !b.is_finite() {
                        return;
                    }
                    let i = self.get(x).narrow(Interval::new(
                        b + infinitable::Finite(1),
                        Infinitable::Infinity,
                    ));
                    self.0.insert(x.clone(), i);
                }
                _ => (),
            },
            SymExpression::LEQ(l_expr, r_expr) => match (&**l_expr, &**r_expr) {
                (SymExpression::FreeVariable(SymType::Int, x), r_expr) => {
                    let (a, _) = Interval::infer(r_expr, self).get();

                    if !a.is_finite() {
                        return;
                    }

                    let i = self
                        .get(x)
                        .narrow(Interval::new(Infinitable::NegativeInfinity, a));
                    self.0.insert(x.clone(), i);
                }
                (l_expr, (SymExpression::FreeVariable(SymType::Int, x))) => {
                    let (_, b) = Interval::infer(l_expr, self).get();
                    if !b.is_finite() {
                        return;
                    }
                    let i = self.get(x).narrow(Interval::new(b, Infinitable::Infinity));
                    self.0.insert(x.clone(), i);
                }
                _ => (),
            },
            SymExpression::GT(l_expr, r_expr) => match (&**l_expr, &**r_expr) {
                ((SymExpression::FreeVariable(SymType::Int, x)), r_expr) => {
                    let (_, b) = Interval::infer(r_expr, self).get();
                    if !b.is_finite() {
                        return;
                    }
                    let i = self.get(x).narrow(Interval::new(
                        b + infinitable::Finite(1),
                        Infinitable::Infinity,
                    ));
                    self.0.insert(x.clone(), i);
                }
                (l_expr, SymExpression::FreeVariable(SymType::Int, x)) => {
                    let (a, _) = Interval::infer(l_expr, self).get();
                    if !a.is_finite() {
                        return;
                    }
                    let i = self.get(x).narrow(Interval::new(
                        Infinitable::NegativeInfinity,
                        a - infinitable::Finite(1),
                    ));
                    self.0.insert(x.clone(), i);
                }

                _ => (),
            },
            SymExpression::GEQ(l_expr, r_expr) => match (&**l_expr, &**r_expr) {
                ((SymExpression::FreeVariable(SymType::Int, x)), r_expr) => {
                    let (_, b) = Interval::infer(r_expr, self).get();
                    if !b.is_finite() {
                        return;
                    }
                    let i = self.get(x).narrow(Interval::new(b, Infinitable::Infinity));
                    self.0.insert(x.clone(), i);
                }
                (l_expr, SymExpression::FreeVariable(SymType::Int, x)) => {
                    let (a, _) = Interval::infer(l_expr, self).get();
                    if !a.is_finite() {
                        return;
                    }
                    let i = self
                        .get(x)
                        .narrow(Interval::new(Infinitable::NegativeInfinity, a));
                    self.0.insert(x.clone(), i);
                }

                _ => (),
            },
            _ => (),
        }
    }

    // An iterative inference algorithm to update the IntervalMap with given expression
    pub fn iterative_inference<'a>(&'a mut self, e: &SymExpression, mut d: i8) {
        while d > 0 {
            d -= 1;
            let i = self.clone();
            self.infer(e);
            if i.0 == self.0 {
                break;
            }
        }
    }
}

impl fmt::Debug for Reference {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reference::Evaluated(_) => {
                if self.get_unsafe() == 0 {
                    write!(f, "null")
                } else {
                    write!(f, "r({})", self.get_unsafe())
                }
            }
            Reference::Lazy { r, class } => write!(f, "r({} || null)", self.get_unsafe()),
        }
    }
}

impl fmt::Debug for IntervalMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = "IntervalMap:\n".to_string();
        for (var, interval) in self.0.iter() {
            res.push_str(&format!("    {} -> {:?}\n", var, interval));
        }
        write!(f, "{}", res)
    }
}

impl fmt::Debug for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "⟨{}, {}⟩", self.0, self.1)
    }
}
