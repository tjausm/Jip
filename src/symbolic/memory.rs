//! Symbolic model representing the stack and heap while symbolically executing a program
//!
use rustc_hash::FxHashMap;
use ::z3::Context;
use std::fmt;
use uuid::Uuid;

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, Scope};
use crate::z3;

use super::model::{SymExpression, Reference, ReferenceValue, Substituted, SymValue};


//-----------------//
// Symbolic memory //
//-----------------//

#[derive(Debug, Clone)]
struct Frame {
    pub scope: Scope,
    pub env: FxHashMap<Identifier, SymExpression>,
}

type SymStack = Vec<Frame>;

type SymHeap = FxHashMap<Reference, ReferenceValue>;


#[derive(Clone)]
pub struct SymMemory {
    stack: SymStack,
    heap: SymHeap,
}

impl<'ctx> SymMemory {
    pub fn new() -> Self {
        SymMemory {
            stack: vec![Frame {
                scope: Scope { id: None },
                env: FxHashMap::default(),
            }],
            heap: FxHashMap::default(),
        }
    }
}

impl<'a> SymMemory {
    /// inserts a free variable (meaning we don't substitute's)
    pub fn stack_insert_free_var(&mut self, ty: Type, id: &'a Identifier) -> () {
        if let Some(s) = self.stack.last_mut() {
            match ty {
                Type::Int => s.env.insert(
                    id.clone(),
                    SymExpression::Int(SymValue::Expr(Substituted(Expression::Identifier(
                        id.clone(),
                    )))),
                ),
                Type::Bool => s.env.insert(
                    id.clone(),
                    SymExpression::Bool(SymValue::Expr(Substituted(Expression::Identifier(
                        id.clone(),
                    )))),
                ),
                _ => None,
            };
        };
    }
    /// inserts a free object field, meaning it is inserted at the top of the stack (meaning we don't substitute's)
fn stack_insert_free_field(&mut self, ty: Type, id: &'a Identifier) -> () {
        if let Some(s) = self.stack.first_mut() {
            match ty {
                Type::Int => s.env.insert(
                    id.clone(),
                    SymExpression::Int(SymValue::Expr(Substituted(Expression::Identifier(
                        id.clone(),
                    )))),
                ),
                Type::Bool => s.env.insert(
                    id.clone(),
                    SymExpression::Bool(SymValue::Expr(Substituted(Expression::Identifier(
                        id.clone(),
                    )))),
                ),
                _ => None,
            };
        };
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in top most frame of stack
    pub fn stack_insert(&mut self, id: &'a Identifier, sym_expr: SymExpression) -> () {
        if let Some(s) = self.stack.last_mut() {
            s.env.insert(id.clone(), sym_expr);
        }
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in frame below top most frame of stack
    pub fn stack_insert_below(&mut self, id: &'a Identifier, sym_expr: SymExpression) -> () {
        let below_index = self.stack.len() - 2;
        match self.stack.get_mut(below_index) {
            Some(frame) => {
                frame.env.insert(id.clone(), sym_expr);
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
            match s.env.get(id) {
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

    /// Inserts mapping `Reference |-> ReferenceValue` into heap returning it's reference
    /// generates new reference if none is given
    pub fn heap_insert(&mut self, r: Option<Reference>, v: ReferenceValue) -> Reference {
        let r = r.unwrap_or(Uuid::new_v4());
        self.heap.insert(r, v);
        r
    }

    /// Get symbolic value of the object's field, panics if something goes wrong
    /// Possibly update with passed `var` and return current symbolic value of the object's field
    pub fn heap_access_object(
        &mut self,
        obj_name: &String,
        field_name: &'a String,
        var: Option<SymExpression>,
    ) -> SymExpression {
        match self.stack_get(obj_name) {
            Some(SymExpression::Ref((_, r))) => match self.heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (ty, expr) = match fields.get(field_name) {
                        Some(field) => field,
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            &self,
                        ),
                    };
                    match var {
                        Some(var) => {
                            let ty = ty.clone();
                            fields.insert(field_name.clone(), (ty, var.clone()));
                            var
                        }
                        None => expr.clone(),
                    }
                }
                Some(ReferenceValue::UninitializedObj(class)) => {
                    let class = class.clone();
                    let new_obj = self.init_object(r, class);
                    self.heap_insert(Some(r), new_obj);
                    self.heap_access_object(obj_name, field_name, var)
                }
                otherwise => panic_with_diagnostics(
                    &format!(
                        "{:?} can't be assigned in assignment '{}.{} := {:?}'",
                        otherwise, obj_name, field_name, var
                    ),
                    &self,
                ),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", obj_name), &self),
        }
    }

    /// Possibly update with passed `var` and return current symbolic expression at arrays index
    pub fn heap_access_array(
        &mut self,
        ctx : &Context,
        simplify: bool,
        arr_name: &Identifier,
        index: Expression,
        var: Option<SymExpression>,
    ) -> Result<SymExpression, Error> {
        // substitute expr and simplify
        let mut subt_index = self.substitute_expr(index);


        //get array type, array and length
        let (_, _, length)= match self.stack_get(&arr_name){
            Some(SymExpression::Ref((_, r))) => match self.heap.get(&r){
                Some(ReferenceValue::Array((ty, arr, length))) => (ty, arr, length),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, subt_index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // make length owned and simplifyif toggled
        let mut length = length.clone();
        if simplify {
            subt_index = self.simplify_expr(subt_index);
            length =  self.simplify_expr(length);
        };

        // check if index is always < length
        match (&subt_index.0, &length.0) {
            (Expression::Literal(Literal::Integer(lit_index)), Expression::Literal(Literal::Integer(lit_lenght))) if lit_index < lit_lenght  => (),
            _ => z3::check_length(
                ctx,
                &length,
                &subt_index,
            &self)?,
        };



        todo!("acces expression mapping here")
    }

    pub fn heap_get_length(&self, arr_name: &Identifier) -> SymExpression {
        match self.stack_get(&arr_name){
        Some(SymExpression::Ref((_, r))) => match self.heap.get(&r){
            Some(ReferenceValue::Array((_, _, length))) => SymExpression::Int(SymValue::Expr(length.clone())),
            otherwise => panic_with_diagnostics(&format!("Can't return length of {} since the value it references to ({:?}) is not an array", arr_name, otherwise), &self),
        },
        _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
    }
    }

    /// given a reference and the class, initializes all fields lazily and returns a ReferenceValue
    pub fn init_object(&mut self, r: Reference, (class, members): Class) -> ReferenceValue {
        let mut fields = FxHashMap::default();

        // map all fields to symbolic values
        for member in &members {
            match member {
                Member::Field((ty, field)) => match ty {
                    Type::Int => {
                        let field_name = format!(
                            "{}.{}",
                            r,
                            field
                        );
                        self.stack_insert_free_field(Type::Int, &field_name);
                        fields.insert(
                            field.clone(),
                            (
                                Type::Int,
                                SymExpression::Int(SymValue::Expr(Substituted(
                                    Expression::Identifier(field_name),
                                ))),
                            ),
                        );
                    }
                    Type::Bool => {
                        let field_name = format!(
                            "{}.{}",
                            r,
                            field
                        );
                        self.stack_insert_free_field(Type::Bool, &field_name);
                        (
                            Type::Bool,
                            fields.insert(
                                field.clone(),
                                (
                                    Type::Bool,
                                    SymExpression::Int(SymValue::Expr(Substituted(
                                        Expression::Identifier(format!(
                                            "{}.{}",
                                            r.as_u64_pair().0,
                                            field
                                        )),
                                    ))),
                                ),
                            ),
                        );
                    }
                    Type::ClassType(class) => {
                        // insert uninitialized object to heap
                        let ty = Type::ClassType(class.clone());
                        let r = self.heap_insert(
                            None,
                            ReferenceValue::UninitializedObj((class.clone(), members.clone())),
                        );
                        fields.insert(
                            field.clone(),
                            (
                                Type::ClassType(class.to_string()),
                                SymExpression::Ref((ty, r)),
                            ),
                        );
                    }
                    Type::Void => panic_with_diagnostics(
                        &format!("Type of {}.{} can't be void", class, field),
                        &self,
                    ),
                    Type::ArrayType(_) => todo!(),
                },
                _ => (),
            }
        }
        ReferenceValue::Object(("todo".to_owned(), fields))
    }

    //todo: how to initialize correctly
    pub fn init_array(&mut self, ty: Type, length: Expression) -> ReferenceValue {
        // generate substituted length
        let subt_len = self.substitute_expr(length);
        ReferenceValue::Array((ty, FxHashMap::default(), subt_len))
    }

    /// substitutes all variables in the underlying `Expression`
    pub fn substitute_expr(&self, expr: Expression) -> Substituted {
        return Substituted(substitute(self, expr));

        /// substitutes expression
        fn substitute(sym_memory: &SymMemory, expr: Expression) -> Expression {
            match expr {
                Expression::Forall(id, r) => {
                    Expression::Forall(id.clone(), Box::new(substitute(sym_memory, *r)))
                }
                Expression::And(l, r) => Expression::And(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Or(l, r) => Expression::Or(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::EQ(l, r) => Expression::EQ(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::NE(l, r) => Expression::NE(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::LT(l, r) => Expression::LT(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::GT(l, r) => Expression::GT(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::GEQ(l, r) => Expression::GEQ(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::LEQ(l, r) => Expression::LEQ(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Plus(l, r) => Expression::Plus(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Minus(l, r) => Expression::Minus(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Multiply(l, r) => Expression::Multiply(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Divide(l, r) => Expression::Divide(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Mod(l, r) => Expression::Mod(
                    Box::new(substitute(sym_memory, *l)),
                    Box::new(substitute(sym_memory, *r)),
                ),
                Expression::Negative(expr) => {
                    Expression::Negative(Box::new(substitute(sym_memory, *expr)))
                }
                Expression::Not(expr) => Expression::Not(Box::new(substitute(sym_memory, *expr))),
                Expression::Literal(_) => expr,
                Expression::Identifier(id) => match sym_memory.stack_get(&id) {
                    Some(SymExpression::Bool(SymValue::Expr(Substituted(expr)))) => expr,
                    Some(SymExpression::Int(SymValue::Expr(Substituted(expr)))) => expr,
                    Some(SymExpression::Ref(r)) => Expression::Literal(Literal::Ref(r)),
                    Some(sym_expr) => panic_with_diagnostics(
                        &format!(
                            "identifier {} with value {:?} can't be substituted",
                            id, sym_expr
                        ),
                        sym_memory,
                    ),
                    None => panic_with_diagnostics(&format!("{} was not declared", id), sym_memory),
                },
                otherwise => panic_with_diagnostics(
                    &format!("{:?} is not yet implemented", otherwise),
                    &sym_memory,
                ),
            }
        }
    }

    /// front end simplifier
    pub fn simplify_expr(&self, expr: Substituted) -> Substituted {
        return Substituted(simplify(self, expr.0));

        fn simplify(sym_memory: &SymMemory, expr: Expression) -> Expression {
            match expr {
                Expression::And(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
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
                        (l_simple, r_simple) => {
                            Expression::And(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::Or(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (Expression::Literal(Literal::Boolean(true)), _) => {
                            Expression::Literal(Literal::Boolean(true))
                        }
                        (_, Expression::Literal(Literal::Boolean(true))) => {
                            Expression::Literal(Literal::Boolean(true))
                        }
                        (l_simple, r_simple) => {
                            Expression::Or(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::Implies(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
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
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (Expression::Literal(l_lit), Expression::Literal(r_lit)) => {
                            Expression::Literal(Literal::Boolean(l_lit == r_lit))
                        },
                        (l_simple, r_simple) => {
                            Expression::EQ(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::NE(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (Expression::Literal(l_lit), Expression::Literal(r_lit)) => {
                            Expression::Literal(Literal::Boolean(l_lit != r_lit))
                        }
                        (l_simple, r_simple) => {
                            Expression::NE(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::LT(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (
                            Expression::Literal(Literal::Integer(l_lit)),
                            Expression::Literal(Literal::Integer(r_lit)),
                        ) => Expression::Literal(Literal::Boolean(l_lit < r_lit)),
                        (l_simple, r_simple) => {
                            Expression::LT(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::GT(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (
                            Expression::Literal(Literal::Integer(l_lit)),
                            Expression::Literal(Literal::Integer(r_lit)),
                        ) => Expression::Literal(Literal::Boolean(l_lit > r_lit)),
                        (l_simple, r_simple) => {
                            Expression::GT(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::GEQ(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (
                            Expression::Literal(Literal::Integer(l_lit)),
                            Expression::Literal(Literal::Integer(r_lit)),
                        ) => Expression::Literal(Literal::Boolean(l_lit >= r_lit)),
                        (l_simple, r_simple) => {
                            Expression::GEQ(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }

                Expression::LEQ(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (
                            Expression::Literal(Literal::Integer(l_lit)),
                            Expression::Literal(Literal::Integer(r_lit)),
                        ) => Expression::Literal(Literal::Boolean(l_lit <= r_lit)),
                        (l_simple, r_simple) => {
                            Expression::LEQ(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }

                Expression::Plus(l_expr, r_expr) => {
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
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
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
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
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
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
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
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
                    match (simplify(sym_memory, *l_expr), simplify(sym_memory, *r_expr)) {
                        (
                            Expression::Literal(Literal::Integer(l_lit)),
                            Expression::Literal(Literal::Integer(r_lit)),
                        ) => Expression::Literal(Literal::Integer(l_lit % r_lit)),
                        (l_simple, r_simple) => {
                            Expression::Mod(Box::new(l_simple), Box::new(r_simple))
                        }
                    }
                }
                Expression::Not(expr) => match simplify(sym_memory, *expr) {
                    Expression::Literal(Literal::Boolean(b)) => {
                        Expression::Literal(Literal::Boolean(!b))
                    }
                    simple_expr => Expression::Not(Box::new(simple_expr)),
                },
                Expression::Literal(_) => expr,
                Expression::Identifier(_) => expr,
                otherwise => panic_with_diagnostics(
                    &format!("{:?} is not yet implemented", otherwise),
                    &sym_memory,
                ),
            }
        }
    }
}

impl fmt::Debug for SymMemory {
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
