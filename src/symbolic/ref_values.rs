//! Symbolic model representing the values on the heap while symbolically executing a program
//!
use super::expression::{PathConstraint, PathConstraints, SymExpression};
use crate::ast::*;
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

#[derive(Clone, Copy, Debug)]
pub enum Boundary {
    Known(i64),
    Unknown,
    None,
}

#[derive(Clone, Debug)]
pub struct Range {
    min: Boundary,
    size: SymExpression,
    max: Boundary,
}

#[derive(Clone)]
pub struct Ranges {
    mapping: FxHashMap<Identifier, Range>
}


impl Default for Ranges {
    fn default() -> Self {
        Ranges {
            mapping: FxHashMap::default(),
        }
    }

    
}

impl Ranges {
    
    /// make a set of ranges with 1 mapping inserted
    pub fn new(arr: Identifier, r: Range) -> Ranges {
        let mut ranges = Ranges::default();
        ranges.mapping.insert(arr, r);
        ranges
    }

    pub fn get<'a>(&'a self, arr: &Identifier) -> Option<&'a Range> {
        self.mapping.get(arr)
    }

    /// given 2 sets of symSizes, take the intersection of their boundaries
    /// and narrow all boundaries in their union to the most pesimistic (known) boundary
    /// e.g. if one boundary is unknown set boundary to unknown,
    /// if both are known set boundary to smallest min and largest max,
    /// otherwise set boundary to None
    pub fn broaden<'a>(l_ranges: &'a mut Ranges, r_ranges: &Ranges) -> &'a mut Ranges {
        for (arr, r_range) in r_ranges.mapping {
            if let Some(l_range) = l_ranges.mapping.get(&arr) {
                l_ranges.mapping.insert(arr.clone(), broaden_one(l_range, &r_range));
            } else {
                l_ranges.mapping.insert(arr.clone(), r_range.clone());
            }
        }
        return l_ranges;

        fn broaden_one(l: &Range, r: &Range) -> Range {
            let min = match (l.min, r.min) {
                (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(l.min(r)),
                (_, Boundary::Unknown) => Boundary::Unknown,
                (Boundary::Unknown, _) => Boundary::Unknown,
                _ => Boundary::None,
            };
            let max = match (l.max, r.max) {
                (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(l.max(r)),
                (_, Boundary::Unknown) => Boundary::Unknown,
                (Boundary::Unknown, _) => Boundary::Unknown,
                _ => Boundary::None,
            };
            Range {
                min: min,
                size: r.size.clone(),
                max: max,
            }
        }
    }
    /// given 2 sets of symSizes, take the intersection of their boundaries
    /// and narrow all boundaries in their union to the most optimistic (known) boundary
    /// if both are known set the largest min and smallest max,
    /// if one of the two boundaries is known set that boundary
    /// if one is unknown set boundary to unknown
    /// otherwise set boundary to None
    fn narrow<'a>(l_ranges: &'a mut Ranges, r_ranges: &Ranges) -> &'a mut Ranges {
        for (arr, r_range) in r_ranges.mapping {
            if let Some(l_range) = l_ranges.mapping.get(&arr) {
                l_ranges.mapping.insert(arr.clone(), narrow_one(l_range, &r_range));
            } else {
                l_ranges.mapping.insert(arr.clone(), r_range.clone());
            }
        }
        return l_ranges;

        fn narrow_one(l: &Range, r: &Range) -> Range {
            let min = match (l.min, r.min) {
                (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(l.max(r)),
                (Boundary::Known(_), _) => l.min,
                (_, Boundary::Known(_)) => r.min,
                (_, Boundary::Unknown) => Boundary::Unknown,
                (Boundary::Unknown, _) => Boundary::Unknown,
                _ => Boundary::None,
            };
            let max = match (l.max, r.max) {
                (Boundary::Known(l), Boundary::Known(r)) => Boundary::Known(l.min(r)),
                (Boundary::Known(_), _) => l.max,
                (_, Boundary::Known(_)) => r.max,
                (_, Boundary::Unknown) => Boundary::Unknown,
                (Boundary::Unknown, _) => Boundary::Unknown,
                _ => Boundary::None,
            };

            let size_expr = match (min, max) {
                (Boundary::Known(l), Boundary::Known(r)) if l == r => {
                    SymExpression::Literal(Literal::Integer(l))
                }
                _ => r.size.clone(),
            };

            Range {
                min: min,
                size: size_expr,
                max: max,
            }
        }
    }


    /// substitute all instances of sizeOf with the ranges we have saved in path constraints
    fn substitute_sizeof(&self, expr: SymExpression) -> SymExpression {
        match expr {
            SymExpression::Implies(l_expr, r_expr) => SymExpression::Implies(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::And(l_expr, r_expr) => SymExpression::And(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Or(l_expr, r_expr) => SymExpression::Or(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::EQ(l_expr, r_expr) => SymExpression::EQ(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::NE(l_expr, r_expr) => SymExpression::NE(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::LT(l_expr, r_expr) => SymExpression::LT(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::GT(l_expr, r_expr) => SymExpression::GT(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::GEQ(l_expr, r_expr) => SymExpression::GEQ(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::LEQ(l_expr, r_expr) => SymExpression::LEQ(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Plus(l_expr, r_expr) => SymExpression::Plus(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Minus(l_expr, r_expr) => SymExpression::Minus(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Multiply(l_expr, r_expr) => SymExpression::Multiply(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Divide(l_expr, r_expr) => SymExpression::Divide(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Mod(l_expr, r_expr) => SymExpression::Mod(
                Box::new(self.substitute_sizeof(*l_expr)),
                Box::new(self.substitute_sizeof(*r_expr)),
            ),
            SymExpression::Negative(expr) => {
                SymExpression::Negative(Box::new(self.substitute_sizeof(*expr)))
            }

            SymExpression::Not(expr) => {
                SymExpression::Not(Box::new(self.substitute_sizeof(*expr)))
            }
            SymExpression::SizeOf(arr, size) => {
                if let Some(range) = self.mapping.get(&arr) {
                    SymExpression::Range(Box::new(range.clone()))
                } else {
                    expr
                }
            }
            _ => expr,
        }
    }

}

impl Range {
    pub fn new(size_expr: SymExpression, arr: Identifier) -> Self {
        match size_expr.simplify() {
            SymExpression::Literal(Literal::Integer(n)) => Range {
                min: Boundary::Known(n),
                size: SymExpression::Literal(Literal::Integer(n)),
                max: Boundary::Known(n),
            },
            expr => Range {
                min: Boundary::None,
                size: expr,
                max: Boundary::None,
            },
        }
    }

    pub fn min(&self) -> Option<i64> {
        match self.min {
            Boundary::Known(n) => Some(n),
            _ => None,
        }
    }
    pub fn get(&self) -> SymExpression {
        self.size.clone()
    }

    pub fn max(&self) -> Option<i64> {
        match self.max {
            Boundary::Known(n) => Some(n),
            _ => None,
        }
    }


    pub fn infer_ranges<'a>(ranges: &'a mut Ranges, expr: &SymExpression) -> &'a mut Ranges {
        return Ranges::narrow(ranges, &infer_new_ranges(expr));



        fn infer_new_ranges(expr: &SymExpression) -> Ranges {
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
                    (SymExpression::Literal(Literal::Boolean(false)), _) => Ranges::default(),
                    (_, SymExpression::Literal(Literal::Boolean(false))) => Ranges::default(),
                    _ => Ranges::broaden(&mut infer_new_ranges(l), &infer_new_ranges(r)).clone(),
                },

                // pick the most optimistics range
                SymExpression::And(l, r) => {
                    Ranges::narrow(&mut infer_new_ranges(l), &infer_new_ranges(r)).clone()
                }

                // pick the most pesimistic range
                SymExpression::Or(l, r) => {
                    Ranges::broaden(&mut infer_new_ranges(l), &infer_new_ranges(r)).clone()
                }

                // if sizeof equals some literal we set all boundarys and size to that literal
                // else if sizeof equals some freevar we set all boundaries to unknown and size to that fv
                SymExpression::EQ(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(id, size_expr),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::Known(*n),
                            size: *r.clone(),
                            max: Boundary::Known(*n),
                        },
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(id, size_expr),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::Known(*n),
                            size: *r.clone(),
                            max: Boundary::Known(*n),
                        },
                    ),
                    (SymExpression::SizeOf(id, size_expr), SymExpression::FreeVariable(_, _)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::Unknown,
                                size: *r.clone(),
                                max: Boundary::Unknown,
                            },
                        )
                    }

                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, size_expr)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::Unknown,
                                size: *l.clone(),
                                max: Boundary::Unknown,
                            },
                        )
                    }

                    _ => Ranges::default(),
                },

                // if sizeof is LT or GT some literal we set min or max to that literal - 1
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::LT(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(id, size_expr),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::None,
                            size: *size_expr.clone(),
                            max: Boundary::Known(*n - 1),
                        },
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(id, size_expr),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::Known(*n + 1),
                            size: *size_expr.clone(),
                            max: Boundary::None,
                        },
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, size_expr)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::Unknown,
                                size: *size_expr.clone(),
                                max: Boundary::None,
                            },
                        )
                    }

                    (SymExpression::SizeOf(id, size_expr), SymExpression::FreeVariable(_, _)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::None,
                                size: *size_expr.clone(),
                                max: Boundary::Unknown,
                            },
                        )
                    }

                    _ => Ranges::default(),
                },
                SymExpression::GT(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(id, size_expr),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::Known(*n + 1),
                            size: *size_expr.clone(),
                            max: Boundary::None,
                        },
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(id, size_expr),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::None,
                            size: *size_expr.clone(),
                            max: Boundary::Known(*n - 1),
                        },
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, size_expr)) => {
                        Ranges::new(id.clone(), {
                            Range {
                                min: Boundary::None,
                                size: *size_expr.clone(),
                                max: Boundary::Unknown,
                            }
                        })
                    }
                    (SymExpression::SizeOf(id, size_expr), SymExpression::FreeVariable(_, _)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::Unknown,
                                size: *size_expr.clone(),
                                max: Boundary::None,
                            },
                        )
                    }
                    _ => Ranges::default()
                },

                // if sizeof is LEQ or GEQ some literal we set min or max to that literal
                // else if sizOf is LT or GT some freevar we set min or max to unknown
                SymExpression::GEQ(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(id, size_expr),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::Known(*n),
                            size: *size_expr.clone(),
                            max: Boundary::None,
                        },
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(id, size_expr),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::None,
                            size: *size_expr.clone(),
                            max: Boundary::Known(*n),
                        },
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, size_expr)) => {
                        Ranges::new(id.clone(), {
                            Range {
                                min: Boundary::None,
                                size: *size_expr.clone(),
                                max: Boundary::Unknown,
                            }
                        })
                    }
                    (SymExpression::SizeOf(id, size_expr), SymExpression::FreeVariable(_, _)) => {
                        Ranges::new(id.clone(), {
                            Range {
                                min: Boundary::Unknown,
                                size: *size_expr.clone(),
                                max: Boundary::None,
                            }
                        })
                    }
                    _ => Ranges::default(),
                },
                SymExpression::LEQ(l, r) => match (&**l, &**r) {
                    (
                        SymExpression::SizeOf(id, size_expr),
                        SymExpression::Literal(Literal::Integer(n)),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::None,
                            size: *size_expr.clone(),
                            max: Boundary::Known(*n),
                        },
                    ),
                    (
                        SymExpression::Literal(Literal::Integer(n)),
                        SymExpression::SizeOf(id, size_expr),
                    ) => Ranges::new(
                        id.clone(),
                        Range {
                            min: Boundary::Known(*n),
                            size: *size_expr.clone(),
                            max: Boundary::None,
                        },
                    ),
                    (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, size_expr)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::Unknown,
                                size: *size_expr.clone(),
                                max: Boundary::None,
                            },
                        )
                    }

                    (SymExpression::SizeOf(id, size_expr), SymExpression::FreeVariable(_, _)) => {
                        Ranges::new(
                            id.clone(),
                            Range {
                                min: Boundary::None,
                                size: *size_expr.clone(),
                                max: Boundary::Unknown,
                            },
                        )
                    }

                    _ => Ranges::default()
                },
                _ => Ranges::default()
            }
        }
    }
}

// impl fmt::Debug for SymSize {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match (self.min, self.max) {
//             (Boundary::None, Boundary::Known(max)) => write!(f, "{:?} <= {}", self.size, max),
//             (Boundary::Known(min), Boundary::None) => write!(f, "{} <= {:?}", min, self.size),
//             (Boundary::Known(min), Boundary::Known(max)) => {
//                 write!(f, "{} <= {:?} <= {}", min, self.size, max)
//             }
//             _ => write!(f, "{:?}", self.size),
//         }
//     }
// }
