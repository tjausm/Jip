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
                _ => ()
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
                _ => ()
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


pub struct Interval;

#[derive(Debug, Clone)]
pub struct IntervalMap;

impl Default for IntervalMap {
    fn default() -> Self {
        todo!()
    }
}

impl IntervalMap {
 /// make an empty set intervalmap
pub fn get(id: &Identifier) -> Interval {
    todo!()
}

    // An iterative inference algorithm to update the IntervalMap with given expression
    pub fn iterative_inference<'a>(&'a mut self, e: &SymExpression, d: i8){
        todo!();
    }
}


#[derive(Clone, Copy)]
pub enum Boundary {
    Known(i64),
    Unknown,
    None,
}

#[derive(Clone, Copy)]
pub enum ArrSize {
    Range(Boundary, Boundary),
    Point(i64),
}

#[derive(Clone)]
pub struct ArrSizes(FxHashMap<Reference, ArrSize>);

impl Default for ArrSizes {
    fn default() -> Self {
        ArrSizes(FxHashMap::default())
    }
}

impl ArrSizes {
    /// make a set of ranges with 1 mapping inserted
    pub fn new(arr: Reference, r: ArrSize) -> ArrSizes {
        let mut ranges = ArrSizes::default();
        ranges.0.insert(arr, r);
        ranges
    }

    pub fn get(&self, arr: &Reference) -> Option<ArrSize> {
        self.0.get(arr).map(|v| v.clone())
    }

    /// given 2 sets of symSizes, take the intersection of their boundaries
    /// and narrow all boundaries in their union to the most pesimistic (known) boundary
    /// e.g. if one boundary is unknown set boundary to unknown,
    /// if both are known set boundary to smallest min and largest max,
    /// otherwise set boundary to None
    fn broaden(&mut self, new_ranges: &ArrSizes) {
        for (arr, r_range) in new_ranges.0.iter() {
            if let Some(l_range) = new_ranges.0.get(arr) {
                self.0.insert(arr.clone(), broaden_one(l_range, &r_range));
            } else {
                self.0.insert(arr.clone(), r_range.clone());
            }
        }

        fn broaden_one(l: &ArrSize, r: &ArrSize) -> ArrSize {
            match (l, r) {
                (ArrSize::Range(l_min, l_max), ArrSize::Range(r_min, r_max)) => {
                    let min = match (l_min, r_min) {
                        (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(*l.min(r)),
                        (_, Boundary::Unknown) => Boundary::Unknown,
                        (Boundary::Unknown, _) => Boundary::Unknown,
                        _ => Boundary::None,
                    };
                    let max = match (l_max, r_max) {
                        (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(*l.max(r)),
                        (_, Boundary::Unknown) => Boundary::Unknown,
                        (Boundary::Unknown, _) => Boundary::Unknown,
                        _ => Boundary::None,
                    };
                    ArrSize::Range(min, max)
                }
                (ArrSize::Range(_, _), _) => *l,
                (_, ArrSize::Range(_, _)) => *r,
                (ArrSize::Point(n), ArrSize::Point(m)) if m == n => *l,
                _ => panic_with_diagnostics(
                    "Something has gone very wrong here during inference",
                    &vec![l, r],
                ),
            }
        }
    }
    /// given 2 sets of symSizes, take the intersection of their boundaries
    /// and narrow all boundaries in their union to the most optimistic (known) boundary
    /// if both are known set the largest min and smallest max,
    /// if one of the two boundaries is known set that boundary
    /// if one is unknown set boundary to unknown
    /// otherwise set boundary to None
    fn narrow(&mut self, r_ranges: &ArrSizes) {
        for (arr, r_range) in r_ranges.0.iter() {
            if let Some(l_range) = self.0.get(arr) {
                self.0.insert(arr.clone(), narrow_one(l_range, &r_range));
            } else {
                self.0.insert(arr.clone(), r_range.clone());
            }
        }
        fn narrow_one(l: &ArrSize, r: &ArrSize) -> ArrSize {
            match (l, r) {
                (ArrSize::Point(n), ArrSize::Point(m)) if n != m => panic_with_diagnostics(
                    "Something has gone very wrong here during inference",
                    &vec![l, r],
                ),
                (ArrSize::Point(_), _) => *l,
                (_, ArrSize::Point(_)) => *r,
                (ArrSize::Range(Boundary::Known(l_min), Boundary::Known(l_max)), _)
                    if l_min == l_max =>
                {
                    ArrSize::Point(*l_min)
                }
                (_, ArrSize::Range(Boundary::Known(r_min), Boundary::Known(r_max)))
                    if r_min == r_max =>
                {
                    ArrSize::Point(*r_min)
                }
                (ArrSize::Range(l_min, l_max), ArrSize::Range(r_min, r_max)) => {
                    let min = match (l_min, r_min) {
                        (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(*l.max(r)),
                        (_, Boundary::Unknown) => Boundary::Unknown,
                        (Boundary::Unknown, _) => Boundary::Unknown,
                        (Boundary::Known(_), _) => *l_min,
                        (_, Boundary::Known(_)) => *r_min,
                        _ => Boundary::None,
                    };
                    let max = match (l_max, r_max) {
                        (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(*l.min(r)),
                        (_, Boundary::Unknown) => Boundary::Unknown,
                        (Boundary::Unknown, _) => Boundary::Unknown,
                        (Boundary::Known(_), _) => *l_max,
                        (_, Boundary::Known(_)) => *r_max,
                        _ => Boundary::None,
                    };
                    ArrSize::Range(min, max)
                }
            }
        }
    }

    pub fn update_inference(&mut self, expr: SymExpression) {
        //self.narrow(&infer_new_ranges(&expr.simplify(None, None)));

        fn infer_new_ranges(expr: &SymExpression) -> ArrSizes {
            match expr {
                // rewrite negations and recurse
                SymExpression::Not(expr) => {
                    let new_expr = match &**expr {
                        SymExpression::NE(l, r) => {
                            SymExpression::EQ(Box::new(*l.clone()), Box::new(*r.clone()))
                        }
                        SymExpression::LT(l, r) => {
                            SymExpression::GEQ(Box::new(*l.clone()), Box::new(*r.clone()))
                        }
                        SymExpression::GT(l, r) => {
                            SymExpression::LEQ(Box::new(*l.clone()), Box::new(*r.clone()))
                        }
                        SymExpression::GEQ(l, r) => {
                            SymExpression::LT(Box::new(*l.clone()), Box::new(*r.clone()))
                        }
                        SymExpression::LEQ(l, r) => {
                            SymExpression::GT(Box::new(*l.clone()), Box::new(*r.clone()))
                        }
                        _ => *expr.clone(),
                    };
                    infer_new_ranges(&new_expr)
                }

                // if not falsifiable we assume it to be true and pick most pessimistic range?
                SymExpression::Implies(l, r) => match (&**l, &**r) {
                    (SymExpression::Literal(Literal::Boolean(false)), _) => ArrSizes::default(),
                    (_, SymExpression::Literal(Literal::Boolean(false))) => ArrSizes::default(),
                    _ => {
                        let mut range = infer_new_ranges(l);
                        range.broaden(&infer_new_ranges(r));
                        range
                    }
                },

                // pick the most optimistics range
                SymExpression::And(l, r) => {
                    let mut range = infer_new_ranges(l);
                    range.narrow(&infer_new_ranges(r));
                    range
                }

                // pick the most pesimistic range
                SymExpression::Or(l, r) => {
                    let mut range = infer_new_ranges(l);
                    range.broaden(&infer_new_ranges(r));
                    range
                }

                // if sizeof equals some literal we set all boundarys and size to that literal
                // else if sizeof equals some other expression we set all boundaries to unknown
                SymExpression::EQ(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(r1, _), SymExpression::SizeOf(r2, _)) => {
                        let mut ar_s = FxHashMap::default();
                        ar_s.insert(
                            r1.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ar_s.insert(
                            r2.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ArrSizes(ar_s)
                    }
                    (SymExpression::SizeOf(r, _), SymExpression::Literal(Literal::Integer(n))) => {
                        ArrSizes::new(r.clone(), ArrSize::Point(*n))
                    }
                    (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Point(*n))
                    }
                    (SymExpression::SizeOf(r, size_expr), _) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                    ),

                    (_, SymExpression::SizeOf(r, size_expr)) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                    ),

                    _ => ArrSizes::default(),
                },

                // if sizeof is LT or GT some literal we set min or max to that literal - 1
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::LT(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(r1, _), SymExpression::SizeOf(r2, _)) => {
                        let mut ar_s = FxHashMap::default();
                        ar_s.insert(
                            r1.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ar_s.insert(
                            r2.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ArrSizes(ar_s)
                    }
                    (SymExpression::SizeOf(r, _), SymExpression::Literal(Literal::Integer(n))) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::None, Boundary::Known(*n - 1)),
                        )
                    }
                    (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::Known(*n + 1), Boundary::None),
                        )
                    }
                    (_, SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }

                    (SymExpression::SizeOf(r, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }

                    _ => ArrSizes::default(),
                },
                SymExpression::GT(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(r1, _), SymExpression::SizeOf(r2, _)) => {
                        let mut ar_s = FxHashMap::default();
                        ar_s.insert(
                            r1.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ar_s.insert(
                            r2.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ArrSizes(ar_s)
                    }
                    (SymExpression::SizeOf(r, _), SymExpression::Literal(Literal::Integer(n))) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::Known(*n + 1), Boundary::None),
                        )
                    }
                    (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::None, Boundary::Known(*n - 1)),
                        )
                    }
                    (_, SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }
                    (SymExpression::SizeOf(r, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }
                    _ => ArrSizes::default(),
                },

                // if sizeof is LEQ or GEQ some literal we set min or max to that literal
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::GEQ(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(r1, _), SymExpression::SizeOf(r2, _)) => {
                        let mut ar_s = FxHashMap::default();
                        ar_s.insert(
                            r1.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ar_s.insert(
                            r2.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ArrSizes(ar_s)
                    }
                    (SymExpression::SizeOf(r, _), SymExpression::Literal(Literal::Integer(n))) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::Known(*n), Boundary::None),
                        )
                    }
                    (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::None, Boundary::Known(*n)),
                        )
                    }
                    (_, SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }
                    (SymExpression::SizeOf(r, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }
                    _ => ArrSizes::default(),
                },
                SymExpression::LEQ(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(r1, _), SymExpression::SizeOf(r2, _)) => {
                        let mut ar_s = FxHashMap::default();
                        ar_s.insert(
                            r1.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ar_s.insert(
                            r2.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        );
                        ArrSizes(ar_s)
                    }
                    (SymExpression::SizeOf(r, _), SymExpression::Literal(Literal::Integer(n))) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::None, Boundary::Known(*n)),
                        )
                    }
                    (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::Known(*n), Boundary::None),
                        )
                    }
                    (_, SymExpression::SizeOf(r, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }

                    (SymExpression::SizeOf(r, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }

                    _ => ArrSizes::default(),
                },
                _ => ArrSizes::default(),
            }
        }
    }
}

impl ArrSize {
    pub fn lt(&self, &other: &Self) -> Option<bool> {
        match self.partial_cmp(&other) {
            Some(ord) => match ord {
                Ordering::Less => Some(true),
                Ordering::Equal => Some(false),
                Ordering::Greater => Some(false),
            },
            // trivially returns true if there are no constraints on 1 boundary
            None => match (self, other) {
                (ArrSize::Range(Boundary::None, Boundary::None), _) => Some(true),
                (_, ArrSize::Range(Boundary::None, Boundary::None)) => Some(true),
                _ => None,
            },
        }
    }
    pub fn le(&self, &other: &Self) -> Option<bool> {
        match self.partial_cmp(&other) {
            Some(ord) => match ord {
                Ordering::Less => Some(true),
                Ordering::Equal => Some(true),
                Ordering::Greater => Some(false),
            },
            // trivially returns true if there are no constraints on 1 boundary
            None => match (self, other) {
                (ArrSize::Range(Boundary::None, Boundary::None), _) => Some(true),
                (_, ArrSize::Range(Boundary::None, Boundary::None)) => Some(true),
                _ => None,
            },
        }
    }
    pub fn gt(&self, &other: &Self) -> Option<bool> {
        match self.partial_cmp(&other) {
            Some(ord) => match ord {
                Ordering::Less => Some(false),
                Ordering::Equal => Some(false),
                Ordering::Greater => Some(true),
            },
            // trivially returns true if there are no constraints on 1 boundary
            None => match (self, other) {
                (ArrSize::Range(Boundary::None, Boundary::None), _) => Some(true),
                (_, ArrSize::Range(Boundary::None, Boundary::None)) => Some(true),
                _ => None,
            },
        }
    }
    pub fn ge(&self, &other: &Self) -> Option<bool> {
        match self.partial_cmp(&other) {
            Some(ord) => match ord {
                Ordering::Less => Some(false),
                Ordering::Equal => Some(true),
                Ordering::Greater => Some(true),
            },
            // trivially returns true if there are no constraints on 1 boundary
            None => match (self, other) {
                (ArrSize::Range(Boundary::None, Boundary::None), _) => Some(true),
                (_, ArrSize::Range(Boundary::None, Boundary::None)) => Some(true),
                _ => None,
            },
        }
    }
}

impl PartialOrd for ArrSize {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (ArrSize::Range(Boundary::Known(min), Boundary::Known(max)), _) if min == max => {
                ArrSize::Point(*min).partial_cmp(other)
            }
            (_, ArrSize::Range(Boundary::Known(min), Boundary::Known(max))) if min == max => {
                self.partial_cmp(&ArrSize::Point(*min))
            }

            (
                ArrSize::Range(_, Boundary::Known(l_max)),
                ArrSize::Range(Boundary::Known(r_min), _),
            ) if l_max < r_min => Some(Ordering::Less),
            (
                ArrSize::Range(_, Boundary::Known(l_max)),
                ArrSize::Range(Boundary::None, Boundary::Known(r_min)),
            ) if l_max < r_min => Some(Ordering::Less),
            (
                ArrSize::Range(Boundary::Known(l_min), _),
                ArrSize::Range(_, Boundary::Known(r_max)),
            ) if l_min > r_max => Some(Ordering::Greater),

            (ArrSize::Range(Boundary::Known(l_min), _), ArrSize::Point(p2)) if p2 < l_min => {
                Some(Ordering::Greater)
            }
            (ArrSize::Range(_, Boundary::Known(l_max)), ArrSize::Point(p2)) if p2 > l_max => {
                Some(Ordering::Less)
            }

            (ArrSize::Point(p1), ArrSize::Range(Boundary::Known(n), _)) if p1 < n => {
                Some(Ordering::Less)
            }
            (ArrSize::Point(p1), ArrSize::Range(_, Boundary::Known(n))) if p1 > n => {
                Some(Ordering::Greater)
            }
            (ArrSize::Point(p1), ArrSize::Point(p2)) => Some(p1.cmp(p2)),
            _ => None,
        }
    }
}

impl PartialEq for ArrSize {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ArrSize::Range(Boundary::Known(min), Boundary::Known(max)), _) if min == max => {
                ArrSize::Point(*min).eq(other)
            }
            (_, ArrSize::Range(Boundary::Known(min), Boundary::Known(max))) if min == max => {
                self.eq(&ArrSize::Point(*min))
            }
            (ArrSize::Point(p1), ArrSize::Point(p2)) => p1 == p2,
            _ => false,
        }
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

impl fmt::Debug for ArrSizes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = "Ranges:\n".to_string();
        for (arr, range) in self.0.iter() {
            res.push_str(&format!("    #{:?} -> {:?}\n", arr, range));
        }
        write!(f, "{}", res)
    }
}

impl fmt::Debug for ArrSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArrSize::Range(min, max) => write!(f, "({:?} - {:?})", min, max),
            ArrSize::Point(n) => write!(f, "({})", n),
        }
    }
}

impl fmt::Debug for Boundary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Boundary::Known(n) => write!(f, "{}", n),
            Boundary::Unknown => write!(f, "Unknown"),
            Boundary::None => write!(f, "None"),
        }
    }
}
