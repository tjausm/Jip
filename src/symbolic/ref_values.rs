//! Symbolic model representing the values on the heap while symbolically executing a program
//!
use super::{expression::{SymExpression, SymType, PathConstraints}, memory::SymMemory};
use crate::{ast::*, shared::{panic_with_diagnostics, Error}, smt_solver::Solver};
use core::fmt;
use rustc_hash::FxHashMap;
use std::cmp::Ordering;
use uuid::Uuid;

pub type Reference = Uuid;

#[derive(Clone)]
pub struct LazyReference(Reference, Identifier);

impl LazyReference {
    pub fn new(r: Reference, id: Identifier) -> Self{
        LazyReference(r, id)
    }

    pub fn initialize(&self, sym_memory: &mut SymMemory, pc: &PathConstraints, solver: &Solver) -> Result<Reference, Error> {
        todo!("");
    }
    pub fn release(&self, sym_memory: &mut SymMemory, pc: &PathConstraints, solver: &Solver) -> Result<Reference, Error> {
        todo!("");
    }
}

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (Identifier, FxHashMap<Identifier, SymExpression>);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SymRefType {
    Array(Box<SymType>),
    Object(Identifier),
    LazyObject(Identifier),
}

#[derive(Clone)]
pub enum ReferenceValue {
    Object(Object),
    Array(Array),
    LazyObject(Identifier),
}

/// Consists of type, a mapping from expression to symbolic expression, expression representing size and flag to indicate that we should lazily initialize objects from this array
pub type Array = (
    SymType,
    FxHashMap<SymExpression, SymExpression>,
    SymExpression,
);

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
        self.narrow(&infer_new_ranges(&expr.simplify(None)));

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
                    (SymExpression::SizeOf(_, r1, _, _), SymExpression::SizeOf(_, r2, _, _)) => {
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
                    (
                        SymExpression::SizeOf(_, r, _, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(r.clone(), ArrSize::Point(*n)),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, _, _),
                    ) => ArrSizes::new(r.clone(), ArrSize::Point(*n)),
                    (SymExpression::SizeOf(_, r, size_expr, _), _) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                    ),

                    (_, SymExpression::SizeOf(_, r, size_expr, _)) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                    ),

                    _ => ArrSizes::default(),
                },

                // if sizeof is LT or GT some literal we set min or max to that literal - 1
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::LT(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(_, r1, _, _), SymExpression::SizeOf(_, r2, _, _)) => {
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
                    (
                        SymExpression::SizeOf(_, r, _, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::None, Boundary::Known(*n - 1)),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, _, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Known(*n + 1), Boundary::None),
                    ),
                    (_, SymExpression::SizeOf(_, r, _, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }

                    (SymExpression::SizeOf(_, r, _, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }

                    _ => ArrSizes::default(),
                },
                SymExpression::GT(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(_, r1, _, _), SymExpression::SizeOf(_, r2, _, _)) => {
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
                    (
                        SymExpression::SizeOf(_, r, _, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Known(*n + 1), Boundary::None),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, _, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::None, Boundary::Known(*n - 1)),
                    ),
                    (_, SymExpression::SizeOf(_, r, _, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }
                    (SymExpression::SizeOf(_, r, _, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }
                    _ => ArrSizes::default(),
                },

                // if sizeof is LEQ or GEQ some literal we set min or max to that literal
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::GEQ(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(_, r1, _, _), SymExpression::SizeOf(_, r2, _, _)) => {
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
                    (
                        SymExpression::SizeOf(_, r, _, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Known(*n), Boundary::None),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, _, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::None, Boundary::Known(*n)),
                    ),
                    (_, SymExpression::SizeOf(_, r, _, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::None, Boundary::Unknown))
                    }
                    (SymExpression::SizeOf(_, r, _, _), _) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }
                    _ => ArrSizes::default(),
                },
                SymExpression::LEQ(l, r) => match (&**l, &**r) {
                    (SymExpression::SizeOf(_, r1, _, _), SymExpression::SizeOf(_, r2, _, _)) => {
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
                    (
                        SymExpression::SizeOf(_, r, _, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::None, Boundary::Known(*n)),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, _, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::Known(*n), Boundary::None),
                    ),
                    (_, SymExpression::SizeOf(_, r, _, _)) => {
                        ArrSizes::new(r.clone(), ArrSize::Range(Boundary::Unknown, Boundary::None))
                    }

                    (SymExpression::SizeOf(_, r, _, _), _) => {
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

impl fmt::Debug for LazyReference {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut formated = "".to_string();
        formated.push_str(&self.0.clone().to_string()[0..4]);
        write!(f, "LazyRef({} | null)", formated)
    }
}
impl fmt::Debug for ArrSizes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = "Ranges:\n".to_string();
        for (arr, range) in self.0.iter() {
            res.push_str(&format!("    #{} -> {:?}\n", &arr.to_string()[0..4], range));
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
