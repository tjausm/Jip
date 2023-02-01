//! Intermediate types & utilities to encode & manipulate ast before we call z3
//!
use rustc_hash::FxHashMap;
use std::fmt;
use std::rc::Rc;
use uuid::Uuid;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Context, SatResult, Solver};

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, Scope};

//----------------------//
// Symbolic expressions //
//----------------------//
#[derive(Clone)]
pub enum PathConstraint {
    Assume(Expression),
    Assert(Expression),
}

impl fmt::Debug for PathConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathConstraint::Assume(pc) => write!(f, "{:?}", pc),
            PathConstraint::Assert(pc) => write!(f, "{:?}", pc),
        }
    }
}

pub type Reference = Uuid;

#[derive(Debug, Clone)]
pub enum SymValue {
    Uninitialized,
    Expr(Expression)
}

#[derive(Debug, Clone)]
pub enum SymExpression {
    Int(SymValue),
    Bool(SymValue),
    Ref((Type, Reference)),
}

/// Consists of `identifier` (= classname) and a hashmap describing it's fields
pub type Object = (
    Identifier,
    FxHashMap<Identifier, (Type, SymExpression)>,
);

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
    pub fn new(p: Program) -> Self {
        SymMemory {
            program: p,
            stack: vec![Frame {
                scope: Scope { id: None },
                env: FxHashMap::default(),
            }],
            heap: FxHashMap::default(),
        }
    }
}

impl<'a> SymMemory<'a> {

    /// Insert mapping `Identifier |-> SymbolicExpression` in top most frame of stack
    pub fn stack_insert(&mut self, id: &'a Identifier, var: SymExpression) -> () {
        if let Some(s) = self.stack.last_mut() {
            s.env.insert(id, var);
        }
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in frame below top most frame of stack
    pub fn stack_insert_below(&mut self, id: &'a Identifier, var: SymExpression) -> () {
        let below_index = self.stack.len() - 2;
        match self.stack.get_mut(below_index) {
            Some(frame) => {
                frame.env.insert(id, var);
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
                                            (Type::Int, SymExpression::Int(SymValue::Expr(Expression::Identifier(format!("{}.{}", r.as_u64_pair().0, field_name))))),
                                        );
                                    }
                                    Type::Bool => {
                                        new_fields.insert(
                                            field_name.clone(),
                                            (Type::Bool, SymExpression::Bool(SymValue::Expr(Expression::Identifier(format!("{}.{}", r.as_u64_pair().0, field_name))))),
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
        var: SymExpression,
    ) -> () {
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
                    fields.insert(field_name.clone(), (ty, var));
                }
                _ => panic_with_diagnostics(
                    &format!(
                        "Reference of {} not found on heap while doing assignment '{}.{} := {:?}'",
                        obj_name, obj_name, field_name, var
                    ),
                    &self,
                ),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", obj_name), &self),
        }
    }

    pub fn expr_to_assertion(&self, expr: Expression) -> PathConstraint{
        let sub_expr = self.substitute_expr(expr.clone());
        PathConstraint::Assume(sub_expr)
    }

    pub fn expr_to_assumption(&self, expr: Expression) -> PathConstraint{
        let sub_expr = self.substitute_expr(expr.clone());
        PathConstraint::Assume(sub_expr)
    }

    /// substitutes all variables in a `SymExpression` 
    pub fn substitute(&self, sym_expr: SymExpression) -> SymExpression{

        match sym_expr {
            SymExpression::Int(SymValue::Expr(expr)) => SymExpression::Int(SymValue::Expr(self.substitute_expr(expr).clone())),
            SymExpression::Bool(SymValue::Expr(expr)) => SymExpression::Bool(SymValue::Expr(self.substitute_expr(expr).clone())),
            SymExpression::Ref(_) => return sym_expr,
            _ => panic_with_diagnostics(&format!("Cannot evaluate {:?}", sym_expr), &self)
        }

    }
    /// helper function to substitute the underlying `Expression` in a SymExpression
    pub fn substitute_expr(&self, expr: Expression) -> Expression{
        match expr{
            Expression::Forall(id, r) => Expression::Forall(id.clone(), Box::new(self.substitute_expr(*r))),
            Expression::And(l, r) => Expression::And(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Or(l, r) => Expression::Or(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::EQ(l, r) => Expression::EQ(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::NE(l, r) => Expression::NE(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::LT(l, r) => Expression::LT(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::GT(l, r) => Expression::GT(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::GEQ(l, r) => Expression::GEQ(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::LEQ(l, r) => Expression::LEQ(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Plus(l, r) => Expression::Plus(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Minus(l, r) => Expression::Minus(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Multiply(l, r) => Expression::Multiply(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Divide(l, r) => Expression::Divide(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Mod(l, r) => Expression::Mod(Box::new(self.substitute_expr(*l)), Box::new(self.substitute_expr(*r))),
            Expression::Negative(expr) =>  Expression::Negative(Box::new(self.substitute_expr(*expr))),
            Expression::Not(expr) => Expression::Not(Box::new(self.substitute_expr(*expr))),
            Expression::Literal(_) => expr,
            Expression::Identifier(id) => match self.stack_get(&id){
                Some(SymExpression::Bool(SymValue::Expr(expr))) => expr,
                Some(SymExpression::Int(SymValue::Expr(expr))) => expr,
                Some(sym_expr) => panic_with_diagnostics(&format!("{:?} can't be substituted", sym_expr), self),
                None => panic_with_diagnostics(&format!("{} was not declared", id), self),
            },
            otherwise => panic_with_diagnostics(&format!("{:?} is not yet implemented", otherwise), &self)
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
