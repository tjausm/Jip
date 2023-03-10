//! Symbolic model representing the values on the heap while symbolically executing a program
//!
use core::fmt;
use rustc_hash::FxHashMap;
use uuid::Uuid;
use super::expression::{SymExpression, PathConstraints, PathConstraint};
use crate::ast::*;

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

/// Consists of type, a mapping from expression to symbolic expression and Substituted expression representing length
pub type Array = (Type, FxHashMap<SymExpression, SymExpression>, SymSize);

#[derive(Clone, Copy, Debug)]
pub enum Boundary {
    Known(i64),
    Unknown,
    None,
}

#[derive(Clone , Debug)]
pub struct SymSize {
    min: Boundary,
    size: SymExpression,
    max: Boundary,
}

impl SymSize {
    pub fn new(size_expr: SymExpression) -> Self {
        SymSize {
            min: Boundary::None,
            size: size_expr,
            max: Boundary::None,
        }
    }

    pub fn min(&self) -> Boundary {
        self.min
    }
    pub fn get(&self) -> SymExpression {
        self.size.clone()
    }
    pub fn max(&self) -> Boundary {
        self.max
    }

    /// given 2 symSizes, returns the most pesimistic boundary
    /// e.g. if one boundary is unknown set boundary to unknown,
    /// if both are known set boundary to smallest min and largest max,
    /// otherwise set boundary to None
    fn broaden(l: &SymSize, r: &SymSize) -> SymSize {
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
        SymSize {
            min: min,
            size: r.size.clone(),
            max: max,
        }
    }
    /// given 2 symSizes, returns the most optimistic boundary
    /// e.g. if one boundary is unknown set boundary to unknown,
    /// if both are known set the largest min and smallest max,
    /// if one of the two boundaries is known set that boundary
    /// otherwise set boundary to None
    fn narrow(l: &SymSize, r: &SymSize) -> SymSize {
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

        let size_expr = match (min, max){
            (Boundary::Known(l), Boundary::Known(r)) if l == r => SymExpression::Literal(Literal::Integer(l)),
            _ => r.size.clone()
        };

        SymSize {
            min: min,
            size: size_expr,
            max: max,
        }
    }

    /// infers current symbolic array size of `a` from the pathconstraints
    /// by inspecting all constraints we try to narrow the range of
    pub fn infer(&self, pc: &PathConstraints, a: &Identifier) -> Self {
        //make length concrete if possible
        match self.size {
            SymExpression::Literal(Literal::Integer(n)) => {
                return SymSize {
                    min: Boundary::Known(n),
                    size: SymExpression::Literal(Literal::Integer(n)),
                    max: Boundary::Known(n),
                }
            }
            _ => (),
        };

        
        // otherwise iterate over all constraints and narrow down current range
        let mut sym_size = self.clone();
        for constraint in pc.clone().into_iter() {
            let expr = match constraint {
                PathConstraint::Assert(e) => e,
                PathConstraint::Assume(e) => e,
            };

            sym_size = SymSize::narrow(&sym_size, &SymSize::infer_from_expr(&self.size, &expr, a));

        }
        sym_size
    }

    fn infer_from_expr(size_expr: &SymExpression, expr: &SymExpression, a: &Identifier) -> SymSize {
        match expr {

            // rewrite negations and recurse
            SymExpression::Not(expr) => {
                let new_expr = 
                    match &**expr {
                    SymExpression::NE(l, r) => SymExpression::EQ(Box::new(*l.clone()), Box::new(*r.clone())),
                    SymExpression::LT(l, r) => SymExpression::GEQ(Box::new(*l.clone()), Box::new(*r.clone())),
                    SymExpression::GT(l, r) => SymExpression::LEQ(Box::new(*l.clone()), Box::new(*r.clone())),
                    SymExpression::GEQ(l, r) => SymExpression::LT(Box::new(*l.clone()), Box::new(*r.clone())),
                    SymExpression::LEQ(l, r) => SymExpression::GT(Box::new(*l.clone()), Box::new(*r.clone())),
                    _ => *expr.clone(),
                };         
                    SymSize::infer_from_expr(size_expr, &new_expr, a)      
            },

            // if not falsifiable we assume it to be true and pick most pessimistic range?
            SymExpression::Implies(l, r) => match (&**l, &**r) {
                (SymExpression::Literal(Literal::Boolean(false)), _) => {
                    SymSize::new(size_expr.clone())
                }
                (_, SymExpression::Literal(Literal::Boolean(false))) => {
                    SymSize::new(size_expr.clone())
                }
                _ => SymSize::broaden(
                    &SymSize::infer_from_expr(size_expr, l, a),
                    &SymSize::infer_from_expr(size_expr, r, a),
                ),
            },

            // pick the most optimistics range
            SymExpression::And(l, r) => SymSize::narrow(
                &SymSize::infer_from_expr(size_expr, l, a),
                &SymSize::infer_from_expr(size_expr, r, a),
            ),

            // pick the most pesimistic range
            SymExpression::Or(l, r) => SymSize::broaden(
                &SymSize::infer_from_expr(size_expr, l, a),
                &SymSize::infer_from_expr(size_expr, r, a),
            ),



            // if sizeof equals some literal we set all boundarys and size to that literal
            // else if sizeof equals some freevar we set all boundaries to unknown and size to that fv
            SymExpression::EQ(l, r) => match (&**l, &**r) {
                (SymExpression::SizeOf(id, _), SymExpression::Literal(Literal::Integer(n)))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::Known(*n),
                        size: *r.clone(),
                        max: Boundary::Known(*n),
                    }
                }
                (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(id, _))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::Known(*n),
                        size: *r.clone(),
                        max: Boundary::Known(*n),
                    }
                }
                (SymExpression::SizeOf(id, _), SymExpression::FreeVariable(_, _)) if id == a => {
                    SymSize {
                        min: Boundary::Unknown,
                        size: *r.clone(),
                        max: Boundary::Unknown,
                    }
                }
                (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, _)) if id == a => {
                    SymSize {
                        min: Boundary::Unknown,
                        size: *l.clone(),
                        max: Boundary::Unknown,
                    }
                }

                _ => SymSize::new(size_expr.clone()),
            },

            // if sizeof is LT or GT some literal we set min or max to that literal - 1
            // else if sizOf is LT or GT some freevar we set min or max to unknown
            SymExpression::LT(l, r) => match (&**l, &**r) {
                (SymExpression::SizeOf(id, _), SymExpression::Literal(Literal::Integer(n)))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Known(*n - 1),
                    }
                }
                (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(id, _))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::Known(*n + 1),
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, _)) if id == a => {
                    SymSize {
                        min: Boundary::Unknown,
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                (SymExpression::SizeOf(id, _), SymExpression::FreeVariable(_, _)) if id == a => {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Unknown,
                    }
                }
                _ => SymSize::new(size_expr.clone()),
            },
            SymExpression::GT(l, r) => match (&**l, &**r) {
                (SymExpression::SizeOf(id, _), SymExpression::Literal(Literal::Integer(n)))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::Known(*n + 1),
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(id, _))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Known(*n - 1),
                    }
                }
                (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, _)) if id == a => {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Unknown,
                    }
                }
                (SymExpression::SizeOf(id, _), SymExpression::FreeVariable(_, _)) if id == a => {
                    SymSize {
                        min: Boundary::Unknown,
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                _ => SymSize::new(size_expr.clone()),
            },

            // if sizeof is LEQ or GEQ some literal we set min or max to that literal
            // else if sizOf is LT or GT some freevar we set min or max to unknown
            SymExpression::GEQ(l, r) => match (&**l, &**r) {
                (SymExpression::SizeOf(id, _), SymExpression::Literal(Literal::Integer(n)))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::Known(*n),
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(id, _))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Known(*n),
                    }
                }
                (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, _)) if id == a => {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Unknown,
                    }
                }
                (SymExpression::SizeOf(id, _), SymExpression::FreeVariable(_, _)) if id == a => {
                    SymSize {
                        min: Boundary::Unknown,
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                _ => SymSize::new(size_expr.clone()),
            },
            SymExpression::LEQ(l, r) => match (&**l, &**r) {
                (SymExpression::SizeOf(id, _), SymExpression::Literal(Literal::Integer(n)))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Known(*n),
                    }
                }
                (SymExpression::Literal(Literal::Integer(n)), SymExpression::SizeOf(id, _))
                    if id == a =>
                {
                    SymSize {
                        min: Boundary::Known(*n),
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                (SymExpression::FreeVariable(_, _), SymExpression::SizeOf(id, _)) if id == a => {
                    SymSize {
                        min: Boundary::Unknown,
                        size: size_expr.clone(),
                        max: Boundary::None,
                    }
                }
                (SymExpression::SizeOf(id, _), SymExpression::FreeVariable(_, _)) if id == a => {
                    SymSize {
                        min: Boundary::None,
                        size: size_expr.clone(),
                        max: Boundary::Unknown,
                    }
                }
                _ => SymSize::new(size_expr.clone()),
            },
            _ => SymSize::new(size_expr.clone()),
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