//! Symbolic model representing the values on the heap while symbolically executing a program
//!
use super::expression::{SymExpression};
use crate::{ast::*, shared::panic_with_diagnostics};
use core::fmt;
use rustc_hash::FxHashMap;
use uuid::Uuid;

pub type Reference = Uuid;

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (Identifier, FxHashMap<Identifier, SymExpression>);

#[derive(Clone)]
pub enum ReferenceValue {
    Object(Object),
    Array(Array),
    /// Takes classname as input
    UninitializedObj(Class),
}

/// Consists of type, a mapping from expression to symbolic expression and Substituted expression representing size
pub type Array = (Type, FxHashMap<SymExpression, SymExpression>, SymExpression);

#[derive(Clone, Copy)]
pub enum Boundary {
    Known(i64),
    Unknown,
    None,
}

#[derive(Clone)]
pub enum ArrSize{
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

    pub fn get<'a>(&'a self, arr: &Reference) -> Option<&'a ArrSize> {
        self.0.get(arr)
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
                (ArrSize::Point(n), _) => *l,
                (_, ArrSize::Point(n)) => *r,
                (ArrSize::Range(Boundary::Known(l_min), Boundary::Known(l_max)), _) if l_min == l_max => ArrSize::Point(*l_min),
                (_, ArrSize::Range(Boundary::Known(r_min), Boundary::Known(r_max))) if r_min == r_max => ArrSize::Point(*r_min),
                (ArrSize::Range(l_min, l_max), ArrSize::Range(r_min, r_max)) => {
                    let min = match (l_min, r_min) {
                        (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(*l.max(r)),
                        (Boundary::Known(_), _) => *l_min,
                        (_, Boundary::Known(_)) => *r_min,
                        (_, Boundary::Unknown) => Boundary::Unknown,
                        (Boundary::Unknown, _) => Boundary::Unknown,
                        _ => Boundary::None,
                    };
                    let max = match (l_max, r_max) {
                        (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(*l.min(r)),
                        (Boundary::Known(_), _) => *l_max,
                        (_, Boundary::Known(_)) => *r_max,
                        (_, Boundary::Unknown) => Boundary::Unknown,
                        (Boundary::Unknown, _) => Boundary::Unknown,
                        _ => Boundary::None,
                    };
                    ArrSize::Range(min, max)
                }
            }
        }
    }

    
    pub fn infer_arrsizes(&mut self, expr: SymExpression) {
        self.narrow(&infer_new_ranges(&expr.simplify()));

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
                // else if sizeof equals some freevar we set all boundaries to unknown and size to that fv
                SymExpression::EQ(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(_, r, size_expr, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Point(*n),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, size_expr, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Point(*n),
                    ),
                    (SymExpression::SizeOf(_, r, size_expr, _), SymExpression::FreeVariable(_, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        )
                    }

                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(_, r, size_expr, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(Boundary::Unknown, Boundary::Unknown),
                        )
                    }

                    _ => ArrSizes::default(),
                },

                // if sizeof is LT or GT some literal we set min or max to that literal - 1
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::LT(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(_, r, size_expr, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(Boundary::None,Boundary::Known(*n - 1)),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, size_expr, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range( Boundary::Known(*n + 1), Boundary::None),
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(_, r, size_expr, _),) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(
                                Boundary::Unknown,
                                
                                Boundary::None,
                            ),
                        )
                    }

                    (SymExpression::SizeOf(_, r, size_expr, _), SymExpression::FreeVariable(_, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(
                                Boundary::None,
                                
                                Boundary::Unknown,
                            ),
                        )
                    }

                    _ => ArrSizes::default(),
                },
                SymExpression::GT(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(_, r, size_expr, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(
                            Boundary::Known(*n + 1),
                            
                            Boundary::None,
                        ),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, size_expr, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(
                            Boundary::None,
                            
                            Boundary::Known(*n - 1),
                        ),
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(_, r, size_expr, _),) => {
                        ArrSizes::new(r.clone(), 
                            ArrSize::Range(
                                Boundary::None,
                                
                                Boundary::Unknown,
                            
                        ))
                    }
                    (SymExpression::SizeOf(_, r, size_expr, _), SymExpression::FreeVariable(_, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(
                                Boundary::Unknown,
                                
                                Boundary::None,
                            ),
                        )
                    }
                    _ => ArrSizes::default(),
                },

                // if sizeof is LEQ or GEQ some literal we set min or max to that literal
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::GEQ(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(_, r, size_expr, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(
                            Boundary::Known(*n),
                            
                            Boundary::None,
                        ),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, size_expr, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(
                            Boundary::None,
                            
                            Boundary::Known(*n),
                        ),
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(_, r, size_expr, _),) => {
                        ArrSizes::new(r.clone(), 
                            ArrSize::Range(
                                Boundary::None,
                                
                                Boundary::Unknown,
                            )
                        )
                    }
                    (SymExpression::SizeOf(_, r, size_expr, _), SymExpression::FreeVariable(_, _)) => {
                        ArrSizes::new(r.clone(), 
                            ArrSize::Range(
                                Boundary::Unknown,
                                
                                Boundary::None,
                            )
                        )
                    }
                    _ => ArrSizes::default(),
                },
                SymExpression::LEQ(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(_, r, size_expr, _),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(
                            Boundary::None,
                            
                            Boundary::Known(*n),
                        ),
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(_, r, size_expr, _),
                    ) => ArrSizes::new(
                        r.clone(),
                        ArrSize::Range(
                            Boundary::Known(*n),
                            
                            Boundary::None,
                        ),
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(_, r, size_expr, _),) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(
                                Boundary::Unknown,
                                
                                Boundary::None,
                            ),
                        )
                    }

                    (SymExpression::SizeOf(_, r, size_expr, _), SymExpression::FreeVariable(_, _)) => {
                        ArrSizes::new(
                            r.clone(),
                            ArrSize::Range(
                                Boundary::None,
                                
                                Boundary::Unknown,
                            ),
                        )
                    }

                    _ => ArrSizes::default(),
                },
                _ => ArrSizes::default(),
            }
        }
    }
}

impl ArrSize {
    pub fn new(size_expr: SymExpression, arr: Identifier) -> Self {
        match size_expr.simplify() {
            SymExpression::Literal(Literal::Integer(n)) => ArrSize::Range(
                Boundary::Known(n),
                Boundary::Known(n),
            ),
            expr => ArrSize::Range(
                Boundary::None,
                Boundary::None,
            ),
        }
    }

    pub fn min(&self) -> Option<i64> {
        match self {
            ArrSize::Point(n)=> Some(*n),
            ArrSize::Range(Boundary::Known(n), _) => Some(*n),
            _ => None,
        }
    }


    pub fn max(&self) -> Option<i64> {
        match self {
            ArrSize::Point(n)=> Some(*n),
            ArrSize::Range(_, Boundary::Known(n)) => Some(*n),
            _ => None,
        }
    }
}

impl fmt::Debug for ArrSizes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = "Ranges:\n".to_string();
        for (arr, range) in self.0.iter() {
            res.push_str(&format!("    #{} -> {:?}\n", arr, range));
        }
        write!(f, "{}", res)
    }
}

impl fmt::Debug for ArrSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArrSize::Range(min, max) =>         write!(
                f,
                "({:?} - {:?})",
                min, max
            ),
            ArrSize::Point(n) => write!(
                f,
                "({})",
                n
            ),
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
