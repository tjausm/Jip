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
use std::cmp::Ordering;

/// tracks if lazy reference is already evaluated
pub type EvaluatedRefs = FxHashSet<Reference>;

global_counter!(REF_COUNTER, i32, 1);

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Reference(i32);

impl Reference {
    /// generates unique reference using a global counter
    pub fn new() -> Reference {
        let i = REF_COUNTER.get_cloned();
        REF_COUNTER.inc();
        Reference(i)
    }
    /// returns the null reference
    pub fn null() -> Reference {
        Reference(0)
    }

    /// return the i32 representing reference
    pub fn get(&self) -> i32 {
        self.0
    }
}

#[derive(Clone, Hash)]
pub struct LazyReference {
    r: Reference,
    class: Identifier,
}

impl LazyReference {
    pub fn new(class: Identifier) -> Self {
        LazyReference {
            r: Reference::new(),
            class,
        }
    }

    /// DO NOT USE function to generate reference from lazy reference. Use `initialize()` & `release()` instead to do this.
    pub fn get(&self) -> (Reference, &Identifier) {
        return (self.r, &self.class);
    }

    /// returns reference if it was already initialized
    pub fn evaluate(&self, eval_refs: &EvaluatedRefs) -> Option<Reference> {
        if eval_refs.contains(&self.r) {
            Some(self.r.clone())
        } else {
            None
        }
    }

    fn is_never_null(
        &self,
        solver: &mut SolverEnv,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &EvaluatedRefs,
        sym_memory: &SymMemory,
    ) -> Result<bool, Error> {
        let simplify = solver.config.simplify;

        // check if path is feasible
        let mut pc = pc.conjunct();
        if simplify {
            pc = pc.simplify(i, Some(eval_refs));
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
            Box::new(SymExpression::LazyReference(self.clone())),
            Box::new(SymExpression::Reference(Reference::null())),
        );
        let mut pc_null_check = SymExpression::And(Box::new(pc), Box::new(ref_is_null));
        if simplify {
            pc_null_check = pc_null_check.simplify(i, Some(eval_refs));
            match pc_null_check {
                SymExpression::Literal(Literal::Boolean(true)) => return Ok(true),
                _ => (),
            }
        }

        match solver.verify_expr(&pc_null_check, sym_memory, i) {
            None => Ok(true),
            Some(model) => Err(Error::Verification(format!(
                "Reference {:?} could possibly be null:\n{:?}",
                self.get().0,
                model
            ))),
        }
    }

    pub fn initialize(
        &self,
        solver: &mut SolverEnv,
        sym_memory: &mut SymMemory,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &mut EvaluatedRefs,
    ) -> Result<Option<Reference>, Error> {
        // try to add ref to hashset, and if it was already present return
        if eval_refs.contains(&self.r) {
            return Ok(Some(self.r));
        };

        let feasible = self.is_never_null(solver, pc, i, eval_refs, sym_memory)?;

        if feasible {
            // insert fresh lazy object into heap
            let r = self.r;
            let obj = sym_memory.init_lazy_object(r, self.class.clone());
            sym_memory.heap_insert(Some(r), obj);

            //update evaluated refs & return
            eval_refs.insert(r);
            Ok(Some(r))
        } else {
            Ok(None)
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

#[derive(Clone, Copy)]
pub struct Interval(Infinitable<i32>, Infinitable<i32>);

impl Interval {
    pub fn broaden(self, other:Interval) -> Self{
        Interval(self.0.max(other.0), self.1.min(other.1))
    }
    
    pub fn narrow(self, other:Interval) -> Self{
        Interval(self.0.min(other.0), self.1.max(other.1))
    }

    pub fn max() -> Interval{
        Interval(Infinitable::NegativeInfinity, Infinitable::Infinity)
    }

    pub fn infer(e: &SymExpression, i: &IntervalMap) -> Interval {
        todo!()
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
        let mut keys : FxHashSet<Identifier> = self.0.clone().into_keys().collect();
        keys.extend(other.0.clone().into_keys().collect::<FxHashSet<Identifier>>());
        for k in keys {
            self.0.insert(k.clone(), self.get(&k).broaden(other.get(&k)));
        }
    }

    fn narrow(&mut self, other: &IntervalMap){
        let mut keys : FxHashSet<Identifier> = self.0.clone().into_keys().collect();
        keys.extend(other.0.clone().into_keys().collect::<FxHashSet<Identifier>>());
        for k in keys {
            self.0.insert(k.clone(), self.get(&k).narrow(other.get(&k)));
        }
    }

    pub fn get(&self, id: &Identifier) -> Interval{
        match self.0.get(id){
            Some(i) => *i,
            None => Interval::max(),
        }
    }

    fn infer(self, e: &SymExpression) -> Self{
        match e {
            SymExpression::And(l_expr, r_expr) => {
                let mut i = self.infer(l_expr);
                i.narrow(&self.infer(r_expr));
                i
            },
            SymExpression::Or(l_expr, r_expr) => {
                let mut i = self.infer(l_expr);
                i.broaden(&self.infer(r_expr));
                i
            },
            SymExpression::EQ(l_expr, r_expr) => match (&**l_expr, &**r_expr){
                (SymExpression::FreeVariable(SymType::Int, x1), SymExpression::FreeVariable(SymType::Int, x2)) => {
                    let i = self.get(x1).narrow(self.get(x2));
                    self.0.insert(x1.clone(), i);
                    self.0.insert(x2.clone(), i);
                    self
                },
                (SymExpression::FreeVariable(SymType::Int, x1), r_expr) => {
                    let mut i = self.get(x1);
                    i.narrow(Interval::infer(r_expr, &self));
                    self.0.insert(x1.clone(), i);
                    self
                },
                (l_expr, (SymExpression::FreeVariable(SymType::Int, x2))) => {
                    let mut i = self.get(x2);
                    i.narrow(Interval::infer(l_expr, &self));
                    self.0.insert(x2.clone(), i);
                    self
                },

            },
            SymExpression::LT(_, _) => todo!(),
            SymExpression::GT(_, _) => todo!(),
            SymExpression::GEQ(_, _) => todo!(),
            SymExpression::LEQ(_, _) => todo!(),
            SymExpression::SizeOf(_, _) => todo!(),
            _ => self
        }
    }

    // An iterative inference algorithm to update the IntervalMap with given expression
    pub fn iterative_inference<'a>(&'a mut self, e: &SymExpression, d: i8) {
        todo!();
    }
}



impl fmt::Debug for Reference {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.get() == 0 {
            write!(f, "null")
        } else {
            write!(f, "r({})", self.get())
        }
    }
}

impl fmt::Debug for LazyReference {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r({} || null)", self.r.get())
    }
}

impl fmt::Debug for IntervalMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = "IntervalMap:\n".to_string();
        for (var, interval) in self.0.iter() {
            res.push_str(&format!("    {:?} -> {:?}\n", var, interval));
        }
        write!(f, "{}", res)
    }
}

impl fmt::Debug for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "⟨{}, {}⟩", self.0, self.1)
        }
    }


