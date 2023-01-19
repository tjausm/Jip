use rustc_hash::FxHashMap;
use uuid::Uuid;
use z3::ast::{Bool, Int};

use crate::{
    ast::{Identifier, Type},
    shared::Scope,
};

// EXPRESSION MODEL

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

pub fn t(){
    SymMemory::default();
}

// MEMORY MODEL
#[derive(Debug, Clone)]
struct Frame<'a> {
    pub scope: Scope,
    pub env: FxHashMap<&'a Identifier, SymbolicExpression<'a>>,
}

type SymStack<'a> =  Vec<Frame<'a>>;

type SymHeap<'a> = FxHashMap<Reference, ReferenceValue<'a>>;


pub struct SymMemory<'a> {
    stack: SymStack<'a>,
    heap: SymHeap<'a>,
}


impl Default for SymMemory<'_> {
    fn default() -> Self { SymMemory {
        stack:  vec![],
        heap: FxHashMap::default(),
        }}
}

impl<'a> SymMemory<'a> {

    pub fn insert_into_stack(
        &mut self,
        id: &'a Identifier,
        var: SymbolicExpression<'a>,
    ) -> () {
        match self.stack.last_mut() {
            Some(s) => {
                s.env.insert(id, var);
            }
            None => (),
        };
    }
    
    pub fn get_from_stack(
        &self,
        id: &'a Identifier,
    ) -> Option<SymbolicExpression<'a>> {
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
    
}

