//! Intermediate types & utilities to encode & manipulate ast before we call z3
//!
use rustc_hash::FxHashMap;
use std::fmt;
use std::path::Path;
use uuid::Uuid;

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, Scope};

//----------------------//
// Symbolic expressions //
//----------------------//

#[derive(Clone)]
pub struct PathConstraints {
    constraints: Vec<PathConstraint>,
}

#[derive(Clone)]
enum PathConstraint {
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
    pub fn get_constraints<'a>(&'a self) -> Expression {
        let mut constraints = Expression::Literal(Literal::Boolean(true));

        for constraint in self.constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(assertion) => {
                    constraints =
                        Expression::And(Box::new(assertion.clone()), Box::new(constraints));
                }
                PathConstraint::Assume(assumption) => {
                    constraints =
                        Expression::Implies(Box::new(assumption.clone()), Box::new(constraints));
                }
            }
        }
        return constraints;
    }
}

pub type Reference = Uuid;

#[derive(Debug, Clone)]
pub enum SymValue {
    Uninitialized,
    Expr(Expression),
}

#[derive(Debug, Clone)]
pub enum SymExpression {
    Int(SymValue),
    Bool(SymValue),
    Ref((Type, Reference)),
}

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (Identifier, FxHashMap<Identifier, (Type, SymExpression)>);

pub type _Array = (Type, Vec<SymExpression>);

#[derive(Debug, Clone)]
pub enum ReferenceValue {
    Object(Object),
    //Array(Array),
    /// Takes classname as input
    UninitializedObj(Identifier),
}

//-----------------//
// Symbolic memory //
//-----------------//

#[derive(Debug, Clone)]
struct Frame<'a> {
    pub scope: Scope,
    pub env: FxHashMap<&'a Identifier, SymExpression>,
}

type SymStack<'a> = Vec<Frame<'a>>;

type SymHeap = FxHashMap<Reference, ReferenceValue>;

#[derive(Clone)]
pub struct SymMemory<'ctx> {
    program: Program,
    stack: SymStack<'ctx>,
    heap: SymHeap,
}

impl<'ctx> SymMemory<'ctx> {
    pub fn new(program: Program) -> Self {
        SymMemory {
            program,
            stack: vec![Frame {
                scope: Scope { id: None },
                env: FxHashMap::default(),
            }],
            heap: FxHashMap::default(),
        }
    }
}

impl<'a> SymMemory<'a> {
    /// inserts a free variable (meaning we don't substitute's)
    pub fn stack_insert_free_var(&mut self, ty: Type, id: &'a Identifier) -> () {
        if let Some(s) = self.stack.last_mut() {
            match ty {
                Type::Int => s.env.insert(
                    &id,
                    SymExpression::Int(SymValue::Expr(Expression::Identifier(id.clone()))),
                ),
                Type::Bool => s.env.insert(
                    &id,
                    SymExpression::Bool(SymValue::Expr(Expression::Identifier(id.clone()))),
                ),
                _ => None,
            };
        };
    }

    /// generates a new PathConstraint from the subtituted assumption and the current constraints
    pub fn add_assert(&self, assertion: Expression, pc: &mut PathConstraints) {
        let subt_assertion = self.substitute_expr(assertion);

        pc.constraints.push(PathConstraint::Assert(subt_assertion));
    }

    /// generates a new PathConstraint from the subtituted assumption and the current constraints
    pub fn add_assume(&self, assumption: Expression, pc: &mut PathConstraints) {
        let subt_assertion = self.substitute_expr(assumption);
        pc.constraints.push(PathConstraint::Assume(subt_assertion));
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in top most frame of stack
    pub fn stack_insert(&mut self, id: &'a Identifier, sym_expr: SymExpression) -> () {
        let subst_expr = self.substitute_sym_expr(sym_expr);
        if let Some(s) = self.stack.last_mut() {
            s.env.insert(id, subst_expr);
        }
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in frame below top most frame of stack
    pub fn stack_insert_below(&mut self, id: &'a Identifier, sym_expr: SymExpression) -> () {
        let subst_expr = self.substitute_sym_expr(sym_expr);
        let below_index = self.stack.len() - 2;
        match self.stack.get_mut(below_index) {
            Some(frame) => {
                frame.env.insert(id, subst_expr);
            }
            _ => (),
        }
    }

    /// Iterate over frames from stack returning the first variable with given `id`
    pub fn stack_get(&self, id: &'a Identifier) -> Option<SymExpression> {
        if id == "null" {
            return Some(SymExpression::Ref((Type::Void, Uuid::nil())));
        };

        for s in self.stack.iter().rev() {
            match s.env.get(&id) {
                Some(var) => return Some(var.clone()),
                None => (),
            }
        }
        return None;
    }

    // Push new frame with given scope
    pub fn stack_push(&mut self, scope: Scope) -> () {
        self.stack.push(Frame {
            scope: scope.clone(),
            env: FxHashMap::default(),
        })
    }
    pub fn stack_pop(&mut self) -> () {
        self.stack.pop();
    }

    /// Returns scope indexed from the top of the stack `get_scope(0) == top_scope`
    pub fn get_scope(&self, index: usize) -> &Scope {
        let position = self.stack.len() - (1 + index);
        match self.stack.get(position) {
            Some(frame) => &frame.scope,
            None => {
                panic_with_diagnostics(&format!("No scope exists at position {}", position), &self)
            }
        }
    }

    /// Insert mapping `Reference |-> ReferenceValue` into heap
    pub fn heap_insert(&mut self, r: Reference, v: ReferenceValue) -> () {
        self.heap.insert(r, v);
    }

    /// Get symbolic value of the object's field, panics if something goes wrong
    pub fn heap_get_field(&mut self, obj_name: &String, field_name: &String) -> SymExpression {
        match self.stack_get(obj_name) {
            Some(SymExpression::Ref((_, r))) => {
                let ref_val = self.heap.get(&r).map(|s| s.clone());
                match ref_val {
                    Some(ReferenceValue::Object((_, fields))) => match fields.get(field_name) {
                        Some((_, expr)) => expr.clone(),
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            &self,
                        ),
                    },

                    Some(ReferenceValue::UninitializedObj(class_name)) => {
                        let mut new_fields = FxHashMap::default();

                        // initialize newObj lazily
                        let members = self.program.get_class(&class_name).1.clone();
                        for member in members {
                            if let Member::Field((ty, field_name)) = member {
                                match ty {
                                    Type::Int => {
                                        new_fields.insert(
                                            field_name.clone(),
                                            (
                                                Type::Int,
                                                SymExpression::Int(SymValue::Expr(
                                                    Expression::Identifier(format!(
                                                        "{}.{}",
                                                        r.as_u64_pair().0,
                                                        field_name
                                                    )),
                                                )),
                                            ),
                                        );
                                    }
                                    Type::Bool => {
                                        new_fields.insert(
                                            field_name.clone(),
                                            (
                                                Type::Bool,
                                                SymExpression::Bool(SymValue::Expr(
                                                    Expression::Identifier(format!(
                                                        "{}.{}",
                                                        r.as_u64_pair().0,
                                                        field_name
                                                    )),
                                                )),
                                            ),
                                        );
                                    }
                                    Type::Classtype(n) => {
                                        // add new unitializedObject to the heap
                                        let next_r = Uuid::new_v4();
                                        self.heap_insert(
                                            next_r,
                                            ReferenceValue::UninitializedObj(n.clone()),
                                        );

                                        // insert unitialized object in the object's fields
                                        new_fields.insert(
                                            field_name.clone(),
                                            (
                                                Type::Classtype(n.clone()),
                                                SymExpression::Ref((
                                                    Type::Classtype(n.clone()),
                                                    next_r,
                                                )),
                                            ),
                                        );
                                    }
                                    Type::Void => {
                                        panic_with_diagnostics("Panic should never trigger", &self)
                                    }
                                }
                            }
                        }

                        // push new object under original reference to heap and recurse
                        let new_obj = ReferenceValue::Object((class_name.clone(), new_fields));
                        self.heap_insert(r, new_obj);
                        self.heap_get_field(obj_name, field_name)
                    }

                    _ => panic_with_diagnostics(
                        &format!("Reference of {} not found on heap", obj_name),
                        &self,
                    ),
                }
            }
            _ => panic_with_diagnostics(&format!("{} is not a reference", obj_name), &self),
        }
    }
    /// Update symbolic value of the object's field, panics if something goes wrong
    pub fn heap_update_field(
        &mut self,
        obj_name: &String,
        field_name: &'a String,
        sym_expr: SymExpression,
    ) -> () {
        let subt_expr = self.substitute_sym_expr(sym_expr);

        match self.stack_get(obj_name) {
            Some(SymExpression::Ref((_, r))) => match self.heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let ty = match fields.get(field_name) {
                        Some(field) => field,
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            &self,
                        ),
                    }
                    .0
                    .clone();
                    fields.insert(field_name.clone(), (ty, subt_expr));
                }
                _ => panic_with_diagnostics(
                    &format!(
                        "Reference of {} not found on heap while doing assignment '{}.{} := {:?}'",
                        obj_name, obj_name, field_name, subt_expr
                    ),
                    &self,
                ),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", obj_name), &self),
        }
    }

    /// substitutes all variables in the underlying `Expression`
    fn substitute_sym_expr(&self, sym_expr: SymExpression) -> SymExpression {
        match sym_expr {
            SymExpression::Int(SymValue::Expr(expr)) => {
                SymExpression::Int(SymValue::Expr(self.substitute_expr(expr).clone()))
            }
            SymExpression::Bool(SymValue::Expr(expr)) => {
                SymExpression::Bool(SymValue::Expr(self.substitute_expr(expr).clone()))
            }
            _ => sym_expr,
        }
    }
    /// substitutes all variables in the underlying `Expression`
    fn substitute_expr(&self, expr: Expression) -> Expression {
        match expr {
            Expression::Forall(id, r) => {
                Expression::Forall(id.clone(), Box::new(self.substitute_expr(*r)))
            }
            Expression::And(l, r) => Expression::And(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Or(l, r) => Expression::Or(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::EQ(l, r) => Expression::EQ(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::NE(l, r) => Expression::NE(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::LT(l, r) => Expression::LT(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::GT(l, r) => Expression::GT(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::GEQ(l, r) => Expression::GEQ(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::LEQ(l, r) => Expression::LEQ(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Plus(l, r) => Expression::Plus(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Minus(l, r) => Expression::Minus(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Multiply(l, r) => Expression::Multiply(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Divide(l, r) => Expression::Divide(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Mod(l, r) => Expression::Mod(
                Box::new(self.substitute_expr(*l)),
                Box::new(self.substitute_expr(*r)),
            ),
            Expression::Negative(expr) => {
                Expression::Negative(Box::new(self.substitute_expr(*expr)))
            }
            Expression::Not(expr) => Expression::Not(Box::new(self.substitute_expr(*expr))),
            Expression::Literal(_) => expr,
            Expression::Identifier(id) => match self.stack_get(&id) {
                Some(SymExpression::Bool(SymValue::Expr(expr))) => expr,
                Some(SymExpression::Int(SymValue::Expr(expr))) => expr,
                Some(sym_expr) => panic_with_diagnostics(
                    &format!(
                        "identifier {} with value {:?} can't be substituted",
                        id, sym_expr
                    ),
                    self,
                ),
                None => panic_with_diagnostics(&format!("{} was not declared", id), self),
            },
            otherwise => {
                panic_with_diagnostics(&format!("{:?} is not yet implemented", otherwise), &self)
            }
        }
    }

    

    /// front end simplifier
    pub fn simplify_expr(&self, expr: Expression) -> Expression {
        match expr {
            Expression::And(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
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
                    (l_simple, r_simple) => Expression::And(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::Or(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (Expression::Literal(Literal::Boolean(true)), _) => {
                        Expression::Literal(Literal::Boolean(true))
                    }
                    (_, Expression::Literal(Literal::Boolean(true))) => {
                        Expression::Literal(Literal::Boolean(true))
                    }
                    (l_simple, r_simple) => Expression::Or(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::Implies(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
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
            Expression::EQ(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (Expression::Literal(l_lit), Expression::Literal(r_lit)) => {
                        Expression::Literal(Literal::Boolean(l_lit == r_lit))
                    }
                    (l_simple, r_simple) => Expression::EQ(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::NE(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (Expression::Literal(l_lit), Expression::Literal(r_lit)) => {
                        Expression::Literal(Literal::Boolean(l_lit != r_lit))
                    }
                    (l_simple, r_simple) => Expression::NE(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::LT(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Boolean(l_lit < r_lit)),
                    (l_simple, r_simple) => Expression::LT(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::GT(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Boolean(l_lit > r_lit)),
                    (l_simple, r_simple) => Expression::GT(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::GEQ(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Boolean(l_lit >= r_lit)),
                    (l_simple, r_simple) => Expression::GEQ(Box::new(l_simple), Box::new(r_simple)),
                }
            }

            Expression::LEQ(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Boolean(l_lit <= r_lit)),
                    (l_simple, r_simple) => Expression::LEQ(Box::new(l_simple), Box::new(r_simple)),
                }
            }

            Expression::Plus(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit + r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Plus(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Minus(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit - r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Minus(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Multiply(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit * r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Multiply(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Divide(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit / r_lit)),
                    (l_simple, r_simple) => {
                        Expression::Divide(Box::new(l_simple), Box::new(r_simple))
                    }
                }
            }
            Expression::Mod(l_expr, r_expr) => {
                match (self.simplify_expr(*l_expr), self.simplify_expr(*r_expr)) {
                    (
                        Expression::Literal(Literal::Integer(l_lit)),
                        Expression::Literal(Literal::Integer(r_lit)),
                    ) => Expression::Literal(Literal::Integer(l_lit % r_lit)),
                    (l_simple, r_simple) => Expression::Mod(Box::new(l_simple), Box::new(r_simple)),
                }
            }
            Expression::Not(expr) => match self.simplify_expr(*expr) {
                Expression::Literal(Literal::Boolean(b)) => {
                    Expression::Literal(Literal::Boolean(!b))
                }
                simple_expr => simple_expr,
            },
            Expression::Literal(_) => expr,
            Expression::Identifier(id) => match self.stack_get(&id) {
                Some(SymExpression::Bool(SymValue::Expr(expr))) => expr,
                Some(SymExpression::Int(SymValue::Expr(expr))) => expr,
                Some(sym_expr) => panic_with_diagnostics(
                    &format!(
                        "identifier {} with value {:?} can't be substituted",
                        id, sym_expr
                    ),
                    self,
                ),
                None => panic_with_diagnostics(&format!("{} was not declared", id), self),
            },
            otherwise => {
                panic_with_diagnostics(&format!("{:?} is not yet implemented", otherwise), &self)
            }
        }
    }
}

impl fmt::Debug for SymMemory<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "
State of Sym-Stack:
{:?}

State of Sym-Heap:
{:?}",
            self.stack, self.heap
        )
    }
}
