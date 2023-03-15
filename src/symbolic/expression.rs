//! Symbolic types representing the values on the stack while symbolically executing a program
//!

use core::fmt;
use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
    vec::IntoIter,
};

use crate::{ast::*, shared::panic_with_diagnostics, symbolic::memory::SymMemory};
use super::ref_values::{Array, SymSize, Reference};

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
    pub fn into_iter(self) -> IntoIter<PathConstraint> {
        self.constraints.into_iter()
    }

    /// combine constraints over true as follows: `assume(a), assert(b) -> a ==> b && true`
    pub fn combine_over_true<'a>(&'a self) -> SymExpression {
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
    pub fn conjuct<'a>(&'a self) -> SymExpression {
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
    pub fn push_assertion(&mut self, s: SymExpression) {
        self.constraints.push(PathConstraint::Assert(s));
    }
    /// adds a new constraint
    pub fn push_assumption(&mut self, s: SymExpression) {
        self.constraints.push(PathConstraint::Assume(s));
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SymType {
    Int,
    Bool,
    Ref(Type),
}

#[derive(Clone)]
pub enum SymExpression {
    Implies(Box<SymExpression>, Box<SymExpression>),
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
    SizeOf(Identifier, Box<SymExpression>),
    Reference(Type, Reference),
    Uninitialized,
}

impl SymExpression {
    /// destructs forall and exists quantifiers and then
    /// generates a substituted expression from it
    pub fn new(sym_memory: &SymMemory, expr: Expression) -> Self {
        match expr {
            Expression::Forall(arr_name, index, value, expr) => destruct_forall(
                sym_memory.heap_get_array(&arr_name),
                &index,
                &value,
                &expr,
                sym_memory,
            ),
            Expression::Exists(arr_name, index, value, expr) => todo!(),
            Expression::Identifier(id) => match sym_memory.stack_get(&id) {
                Some(sym_expr) => sym_expr,
                _ => panic_with_diagnostics(&format!("{} was not declared", id), &sym_memory),
            },
            Expression::SizeOf(arr_name) => SymExpression::SizeOf(
                arr_name.clone(),
                Box::new(sym_memory.heap_get_arr_length(&arr_name)),
            ),
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

    /// front end simplifier
    pub fn simplify(self) -> Self {
        match &self {
            SymExpression::And(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
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
                (l_simple, r_simple) => SymExpression::And(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::Or(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (SymExpression::Literal(Literal::Boolean(true)), _) => {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                (_, SymExpression::Literal(Literal::Boolean(true))) => {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                (l_simple, r_simple) => SymExpression::Or(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::Implies(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
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
            },
            SymExpression::EQ(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (SymExpression::Literal(l_lit), SymExpression::Literal(r_lit)) => {
                    SymExpression::Literal(Literal::Boolean(l_lit == r_lit))
                }
                (SymExpression::FreeVariable(_, l_fv), SymExpression::FreeVariable(__, r_fv)) if l_fv == r_fv => {
                    SymExpression::Literal(Literal::Boolean(true))
                }
                (l_simple, r_simple) => SymExpression::EQ(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::NE(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (SymExpression::Literal(l_lit), SymExpression::Literal(r_lit)) => {
                    SymExpression::Literal(Literal::Boolean(l_lit != r_lit))
                }
                (l_simple, r_simple) => SymExpression::NE(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::LT(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Boolean(l_lit < r_lit)),
                (l_simple, r_simple) => SymExpression::LT(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::GT(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Boolean(l_lit > r_lit)),
                (l_simple, r_simple) => SymExpression::GT(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::GEQ(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Boolean(l_lit >= r_lit)),
                (l_simple, r_simple) => SymExpression::GEQ(Box::new(l_simple), Box::new(r_simple)),
            },

            SymExpression::LEQ(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Boolean(l_lit <= r_lit)),
                (l_simple, r_simple) => SymExpression::LEQ(Box::new(l_simple), Box::new(r_simple)),
            },

            SymExpression::Plus(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Integer(l_lit + r_lit)),
                (l_simple, r_simple) => SymExpression::Plus(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::Minus(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Integer(l_lit - r_lit)),
                (l_simple, r_simple) => {
                    SymExpression::Minus(Box::new(l_simple), Box::new(r_simple))
                }
            },
            SymExpression::Multiply(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Integer(l_lit * r_lit)),
                (l_simple, r_simple) => {
                    SymExpression::Multiply(Box::new(l_simple), Box::new(r_simple))
                }
            },
            SymExpression::Divide(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Integer(l_lit / r_lit)),
                (l_simple, r_simple) => {
                    SymExpression::Divide(Box::new(l_simple), Box::new(r_simple))
                }
            },
            SymExpression::Mod(l, r) => match (l.clone().simplify(), r.clone().simplify()) {
                (
                    SymExpression::Literal(Literal::Integer(l_lit)),
                    SymExpression::Literal(Literal::Integer(r_lit)),
                ) => SymExpression::Literal(Literal::Integer(l_lit % r_lit)),
                (l_simple, r_simple) => SymExpression::Mod(Box::new(l_simple), Box::new(r_simple)),
            },
            SymExpression::Not(expr) => match expr.clone().simplify() {
                SymExpression::Not(inner_expr) => inner_expr.clone().simplify(),
                SymExpression::Literal(Literal::Boolean(b)) => {
                    SymExpression::Literal(Literal::Boolean(!b))
                }
                simple_expr => SymExpression::Not(Box::new(simple_expr)),
            },
            SymExpression::SizeOf(_, _) => self,
            SymExpression::Literal(_) => self,
            SymExpression::FreeVariable(_, _) => self,
            SymExpression::Reference(_, _) => self,
            otherwise => {
                panic_with_diagnostics(&format!("{:?} is not yet implemented", otherwise), &self)
            }
        }
    }
}



/// destructs a `Expression::forall(arr, index, value)` statement using the following algorithm:
/// ``` ignore
/// // asserts expression holds for all values in array
/// c = true
/// foreach (i, v) in arr { [i |->index, v |-> value] in expr}     /// // substitute (i,v) into expression
///
/// // asserts expression holds for all values > 0 and < #arr that are not in symbolic array
/// o = true
/// foreach (i,v) in arr {o = index != i && o}
/// e = (0 < index && o && index < #arr && value == 0 ==> expr
///
/// return c && e
/// ```
fn destruct_forall<'a>(
    (ty, arr, size): &Array,
    index: &Identifier,
    value: &Identifier,
    inner_expr: &Expression,
    sym_memory: &SymMemory,
) -> SymExpression {
    let index_id = SymExpression::FreeVariable(SymType::Int, index.clone());
    let sym_ty = match ty {
        Type::Int => SymType::Int,
        Type::Bool => SymType::Bool,
        _ => SymType::Ref(ty.clone()),
    };
    // foreach (i, v) pair in arr:
    // - C = for each[i |-> index, v |-> value]expr && C
    // - O = index != i && O
    let mut c = SymExpression::Literal(Literal::Boolean(true));
    let mut o = SymExpression::Literal(Literal::Boolean(true));
    for (i, v) in arr.into_iter() {
        // we insert index and value substitutions into stack
        // and build a new inner_expression with said substitutions
        let mut extended_memory = sym_memory.clone();
        extended_memory.stack_insert(&index, i.clone());
        extended_memory.stack_insert(&value, v.clone());

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

    let i_lt_size = SymExpression::LT(Box::new(index_id.clone()), Box::new(size.clone()));

    // build inner expression with index and value as freevars
    let mut extended_memory = sym_memory.clone();
    extended_memory.stack_insert(
        &index,
        SymExpression::FreeVariable(SymType::Int, index.clone()),
    );
    extended_memory.stack_insert(&value, SymExpression::FreeVariable(sym_ty, value.clone()));
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
    SizeOf(String),
    Reference(Type, Reference),
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
            SymExpression::SizeOf(s, _) => HashExpression::SizeOf(s.clone()).hash(state),
            SymExpression::FreeVariable(ty, id) => {
                HashExpression::FreeVariable(ty.clone(), id.clone()).hash(state)
            }
            SymExpression::Reference(ty, r) => {
                HashExpression::Reference(ty.clone(), r.clone()).hash(state)
            }
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

impl fmt::Debug for SymExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymExpression::Implies(l_expr, r_expr) => write!(f, "({:?} ==> {:?})", l_expr, r_expr),
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
            SymExpression::SizeOf(id, _) => write!(f, "#{}", id),
            SymExpression::Reference(_, r) => {
                let mut formated = "".to_string();
                formated.push_str(&r.clone().to_string()[0..4]);
                write!(f, "Ref({})", formated)
            }
            SymExpression::Uninitialized => write!(f, "Unitialized)"),
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
        SymExpression::new(&SymMemory::new(), expr)
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
    #[test]
    fn arrlength_not_equivalent() {
        let e1 = parse("#a");
        let e2 = parse("a");
        assert!(calculate_hash(&e1) != calculate_hash(&e2));
    }
    #[test]
    fn literal_not_equivalent() {
        let e1 = parse("false");
        let e2 = parse("true");
        assert!(calculate_hash(&e1) != calculate_hash(&e2));
    }

    #[test]
    fn deterministic_sort() {
        let one = parse("1");
        let id = parse("id");
        let negative = parse("-1");
        let three = parse("0+1+2*3/3");

        // construct some random arrays with these expressions
        let vec1 = vec![negative.clone(), three.clone(), id.clone(), one.clone()];
        let vec2 = vec![negative.clone(), one.clone(), id.clone(), three.clone()];
        let vec3 = vec![three.clone(), id.clone(), negative.clone(), one.clone()];
        let vec4 = vec![id, negative, one, three];

        let mut vec1 = map_hash(&vec1);
        vec1.sort();
        let mut vec2 = map_hash(&vec2);
        vec2.sort();
        let mut vec3 = map_hash(&vec3);
        vec3.sort();
        let mut vec4 = map_hash(&vec4);
        vec4.sort();

        // check if arrays are equal after sorting
        assert!(vec1 == vec2);
        assert!(vec1 == vec3);
        assert!(vec1 == vec4);
    }
}
