//! Share types and functions between modules
//!
//!

use core::fmt;
use rustc_hash::FxHashMap;
use std::default::Default;
use std::panic;
use std::process::exit;
use uuid::Uuid;
use z3::ast::{self, Bool, Int};

use crate::ast::*;

/// Indicates if program is valid, counterexample was found or other error occured
pub enum ExitCode {
    Valid = 0,
    CounterExample = 1,
    Error = 2,
}

#[derive(Debug, Clone)]
pub enum Error {
    Verification(String),
    Other(String),
}

/// Either has a scope id or None if we are at the entry scope of the program
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: Option<Uuid>,
}

/// Panics with passed message and print diagnostic info
#[track_caller]
pub fn panic_with_diagnostics<'a>(msg: &str, sym_memory: Option<&SymMemory<'a>>) -> ! {
    //get location of panic call
    let panic_loc = panic::Location::caller();

    //print diagnostics
    print!(
        "Program panicked at {} {}:{}

With error:
{}

{:?}",
        panic_loc.file(),
        panic_loc.line(),
        panic_loc.column(),
        msg,
        sym_memory
    );

    exit(ExitCode::Error as i32);
}

//----------------------//
// Symbolic expressions //
//----------------------//
pub type Reference = Uuid;

#[derive(Debug, Clone)]
pub enum SymbolicExpression<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
    Ref((Type, Reference)),
}

pub type Object<'a> = (
    Type,
    FxHashMap<&'a Identifier, (Type, SymbolicExpression<'a>)>,
);

pub type Array<'a> = (Type, Vec<SymbolicExpression<'a>>);

#[derive(Debug, Clone)]
pub enum ReferenceValue<'a> {
    Object(Object<'a>),
    Array(Array<'a>),
    Uninitialized(Type),
}

//-----------------//
// Symbolic memory //
//-----------------//
#[derive(Debug, Clone)]
struct Frame<'a> {
    pub scope: Scope,
    pub env: FxHashMap<&'a Identifier, SymbolicExpression<'a>>,
}

type SymStack<'a> = Vec<Frame<'a>>;

type SymHeap<'a> = FxHashMap<Reference, ReferenceValue<'a>>;

#[derive(Clone)]
pub struct SymMemory<'a> {
    stack: SymStack<'a>,
    heap: SymHeap<'a>,
}

impl Default for SymMemory<'_> {
    fn default() -> Self {
        SymMemory {
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
    pub fn stack_insert(&mut self, id: &'a Identifier, var: SymbolicExpression<'a>) -> () {
        match self.stack.last_mut() {
            Some(s) => {
                s.env.insert(id, var);
            }
            None => (),
        };
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in frame below top most frame of stack
    pub fn stack_insert_below(&mut self, id: &'a Identifier, var: SymbolicExpression<'a>) -> () {
        let below_index = self.stack.len() - 2;
        match self.stack.get_mut(below_index) {
            Some(frame) => {
                frame.env.insert(id, var);
            }
            _ => (),
        }
    }

    /// Iterate over frames from stack returning the first variable with given `id`
    pub fn stack_get(&self, id: &'a Identifier) -> Option<SymbolicExpression<'a>> {
        if id == "null" {
            return Some(SymbolicExpression::Ref((Type::Void, Uuid::nil())));
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

    /// Returns scope of top most frame in the stack
    pub fn current_scope(&self) -> &Scope {
        match self.stack.last() {
            Some(frame) => &frame.scope,
            None => panic_with_diagnostics("No scope exists currently", Some(&self)),
        }
    }

    /// Insert mapping `Reference |-> ReferenceValue` into heap
    pub fn heap_insert(&mut self, r: Reference, v: ReferenceValue<'a>) -> () {
        self.heap.insert(r, v);
    }

    /// Get symbolic value of the object's field, panics if something goes wrong
    pub fn heap_get_field(&self, obj_name: &String, field_name: &String) -> SymbolicExpression<'a> {
        match self.stack_get(obj_name) {
            Some(SymbolicExpression::Ref((_, r))) => match self.heap.get(&r) {
                Some(ReferenceValue::Object((_, fields))) => match fields.get(field_name) {
                    Some((ty, expr)) => expr.clone(),
                    None => panic_with_diagnostics(
                        &format!("Field {} does not exist on {}", field_name, obj_name),
                        Some(&self),
                    ),
                },

                Some(ReferenceValue::Uninitialized(ty)) => {
                    todo!("");
                }
                _ => panic_with_diagnostics(
                    &format!("Reference of {} not found on heap", obj_name),
                    Some(&self),
                ),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", obj_name), Some(&self)),
        }
    }
    /// Update symbolic value of the object's field, panics if something goes wrong
    pub fn heap_update_field(
        &mut self,
        obj_name: &String,
        field_name: &'a String,
        var: SymbolicExpression<'a>,
    ) -> () {
        match self.stack_get(obj_name) {
            Some(SymbolicExpression::Ref((_, r))) => match self.heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (ty, _) = match fields.get(field_name) {
                        Some(field) => field,
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            Some(&self),
                        ),
                    };
                    fields.insert(field_name, (ty.clone(), var));
                }
                _ => panic_with_diagnostics(
                    &format!(
                        "Reference of {} not found on heap while doing assignment '{}.{} := {:?}'",
                        obj_name, obj_name, field_name, var
                    ),
                    Some(&self),
                ),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", obj_name), Some(&self)),
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
