//! Symbolic model representing the stack and heap while symbolically executing a program
//!
use rustc_hash::FxHashMap;
use std::fmt;
use uuid::Uuid;

use super::expression::{PathConstraints, SymExpression, SymType};
use super::ref_values::{ArrSize, ArrSizes, Array, Reference, ReferenceValue, SymRefType};
use super::state::{Fork, PathState};
use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Diagnostics, Error, Scope};
use crate::smt_solver::Solver;

#[derive(Debug, Clone)]
struct Frame {
    pub scope: Scope,
    pub env: FxHashMap<Identifier, SymExpression>,
}

type SymStack = Vec<Frame>;

type SymHeap = FxHashMap<Reference, ReferenceValue>;

#[derive(Clone)]
pub struct SymMemory {
    prog: Program,
    stack: SymStack,
    heap: SymHeap,
}

impl<'a> SymMemory {
    pub fn new(prog: Program) -> Self {
        SymMemory {
            prog,
            stack: vec![Frame {
                scope: Scope { id: None },
                env: FxHashMap::default(),
            }],
            heap: FxHashMap::default(),
        }
    }
    /// Insert mapping `Identifier |-> SymbolicExpression` in top most frame of stack
    pub fn stack_insert(&mut self, id: Identifier, sym_expr: SymExpression) -> () {
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
            return Some(SymExpression::Reference(Uuid::nil()));
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

    // assigns the `from` value to the `to` value on the top most frame of the stack
    pub fn stack_assign(&mut self, from: &Identifier, to: Identifier) -> (){
        let mut from_val;
        for s in self.stack.iter().rev() {
            match s.env.get(from) {
                Some(v) => {
                    v = v;
                    break
                },
                _ => ()
            }
        panic_with_diagnostics(&format!("Couldn't assign value of {} to {}", from, to), &self);
        }
        if let Some(s) = self.stack.last_mut() {
            s.env.insert(to, from_val);
        };
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

    /// Inserts mapping `Reference |-> ReferenceValue` into heap returning it's reference.
    /// Generates new reference if none is given
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
            Some(SymExpression::Reference(r)) => match self.heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let expr = match fields.get(field_name) {
                        Some(field) => field,
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            &self,
                        ),
                    };
                    match var {
                        Some(var) => {
                            fields.insert(field_name.clone(), var.clone());
                            var
                        }
                        None => expr.clone(),
                    }
                }
                Some(ReferenceValue::LazyObject(class)) => {
                    let class = class.clone();
                    let new_obj = self.init_lazy_object(r, class.clone());
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

    pub fn heap_get_array(&self, arr_name: &Identifier) -> &Array {
        match self.stack_get(arr_name) {
            Some(SymExpression::Reference(r)) => match self.heap.get(&r) {
                Some(ReferenceValue::Array(arr)) => arr,
                otherwise => panic_with_diagnostics(
                    &format!(
                        "{:?} is not an array, it has value {:?} on the heap",
                        otherwise, arr_name
                    ),
                    &self,
                ),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        }
    }

    /// Possibly update with passed `var` and return current symbolic expression at arrays index
    pub fn heap_access_array(
        &mut self,
        pc: &PathConstraints,
        arr_sizes: &ArrSizes,
        solver: &mut Solver,
        diagnostics: &mut Diagnostics,
        arr_name: &Identifier,
        index: Expression,
        var: Option<SymExpression>,
    ) -> Result<SymExpression, Error> {
        //get mutable HashMap representing array
        let (r, size_expr) = match self.stack_get(&arr_name){
            Some(SymExpression::Reference(r)) => match self.heap.get(&r){
                Some(ReferenceValue::Array((_, _, length))) => (r, length),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // substitute expr and simplify
        let sym_index = SymExpression::new(self, index);

        //get ArrSize if it's inferred
        let (size) = arr_sizes.get(&r);

        // always simplify index, otherwise unsimplified SE could return different results than simplified SE
        let simple_index = sym_index.clone().simplify(Some(arr_sizes));

        // check if index is always < length
        match (&simple_index, &size_expr, &size) {
            (
                SymExpression::Literal(Literal::Integer(lit_i)),
                SymExpression::Literal(Literal::Integer(lit_l)),
                _,
            ) if lit_i < lit_l => (),
            (SymExpression::Literal(Literal::Integer(lit_i)), _, Some(s))
                if ArrSize::Point(*lit_i).lt(s) == Some(true) =>
            {
                ()
            }
            _ => {
                diagnostics.z3_calls += 1;
                let size_of =
                    SymExpression::SizeOf(arr_name.clone(), r, Box::new(size_expr.clone()), size);
                solver.verify_array_access(pc, &size_of, &simple_index)?
            }
        };

        //get mutable HashMap representing array
        let (ty, arr) = match self.stack_get(&arr_name){
            Some(SymExpression::Reference(r)) => match self.heap.get_mut(&r){
                Some(ReferenceValue::Array((ty, arr, _))) => (ty, arr),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, sym_index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        if let Some(var) = var {
            arr.insert(simple_index, var.clone());
            return Ok(var);
        }
        if let Some(v) = arr.get(&simple_index) {
            return Ok(v.clone());
        }

        match ty {
            SymType::Ref(ref_type) => match ref_type {
                SymRefType::Object(class) => {
                    // generate and insert reference
                    let r = Uuid::new_v4();
                    let sym_r = SymExpression::Reference(r);
                    arr.insert(simple_index, sym_r.clone());

                    // instantiate object and insert under reference afterwards (to please borrowchecker)
                    let class = class.clone();
                    let obj = self.init_object(r, class);
                    self.heap_insert(Some(r), obj);

                    Ok(sym_r)
                }
                SymRefType::LazyObject(class) => {
                    // generate and insert reference
                    let r = Uuid::new_v4();
                    let sym_r = SymExpression::Reference(r);
                    arr.insert(simple_index, sym_r.clone());

                    // instantiate lazy object and insert under reference afterwards (to please borrowchecker)
                    let class = class.clone();
                    let obj = self.init_lazy_object(r, class.clone());
                    self.heap_insert(Some(r), obj);

                    Ok(sym_r)
                }
                SymRefType::Array(_) => todo!("2+ dimensional arrays are not supported"),
            },
            _ => {
                let fv_id = format!("|{}[{:?}]|", arr_name.clone(), simple_index);
                let fv = SymExpression::FreeVariable(ty.clone(), fv_id);
                arr.insert(simple_index, fv.clone());
                Ok(fv)
            }
        }
    }

    // return the symbolic length of an array
    pub fn heap_get_arr_length(&self, arr_name: &Identifier) -> SymExpression {
        match self.stack_get(&arr_name){
        Some(SymExpression::Reference(r)) => match self.heap.get(&r){
            Some(ReferenceValue::Array((_, _, length))) => length.clone(),
            otherwise => panic_with_diagnostics(&format!("Can't return length of {} since the value it references to ({:?}) is not an array", arr_name, otherwise), &self),
        },
        _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
    }
    }

    // inits an object with al it's fields uninitialised
    pub fn init_object(&mut self, r: Reference, class: Identifier) -> ReferenceValue {
        let mut fields = FxHashMap::default();

        let members = self.prog.get_class(&class).1.clone();
        // map all fields to symbolic values
        for member in members {
            match member {
                Member::Field((_, field)) => {
                    fields.insert(field.clone(), SymExpression::Uninitialized);
                }
                _ => (),
            }
        }
        ReferenceValue::Object((class, fields))
    }

    // inits 1 objects with its concrete fields as free variables and its reference fields as lazy objects
    fn init_lazy_object(&mut self, r: Reference, class: Identifier) -> ReferenceValue {
        let r = Uuid::new_v4();
        let mut fields = FxHashMap::default();

        let members = self.prog.get_class(&class).1.clone();
        // map all fields to symbolic values
        for member in members {
            match member {
                Member::Field((ty, field)) => match ty {
                    (Type::Int) => {
                        let field_name = format!("|{}.{}|", &r.to_string()[0..4], field);

                        fields.insert(
                            field.clone(),
                            SymExpression::FreeVariable(SymType::Int, field_name),
                        );
                    }
                    Type::Bool => {
                        let field_name = format!("{}.{}", &r.to_string()[0..6], field);

                        fields.insert(
                            field.clone(),
                            SymExpression::FreeVariable(SymType::Bool, field_name),
                        );
                    }
                    Type::Class(class) => {
                        // either make lazy object or uninitialized
                        let obj = SymExpression::Reference(
                            self.heap_insert(None, ReferenceValue::LazyObject(class.clone())),
                        );
                        fields.insert(field.clone(), obj);
                    }
                    Type::Void => panic_with_diagnostics(
                        &format!("Type of {}.{} can't be void", class, field),
                        &self,
                    ),
                    Type::Array(_) => todo!(),
                },
                _ => (),
            }
        }
        ReferenceValue::Object((class, fields))
    }

    //todo: how to initialize correctly
    pub fn init_array(&mut self, ty: SymType, size_expr: SymExpression) -> ReferenceValue {
        ReferenceValue::Array((ty, FxHashMap::default(), size_expr))
    }
}

impl fmt::Debug for ReferenceValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReferenceValue::Object((ty, fields)) => {
                let mut formated_obj = format!("{}", ty);
                for (field_name, expr) in fields {
                    formated_obj
                        .push_str(&format!("\n                .{} := {:?}", field_name, expr))
                }
                write!(f, "{}", formated_obj)
            }
            ReferenceValue::Array((ty, entries, len)) => {
                let mut formated_obj = format!("{:?}[] with length {:?}", ty, len);
                for (index, value) in entries {
                    formated_obj
                        .push_str(&format!("\n                [{:?}] := {:?}", index, value))
                }
                write!(f, "{}", formated_obj)
            }
            ReferenceValue::LazyObject(class_name) => write!(f, "Uninitialized {}", class_name),
        }
    }
}
impl fmt::Debug for SymMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Format stack and heap to indented lists
        let mut formated_sym_stack = "".to_string();
        for Frame { scope, env } in &self.stack {
            // add name of frame
            formated_sym_stack.push_str("   Frame ");
            match scope.id {
                None => formated_sym_stack.push_str("'main'\n"),
                Some(id) => {
                    formated_sym_stack.push_str(&id.to_string()[0..4]);
                    formated_sym_stack.push_str("\n")
                }
            }

            // add all values of sym_stack
            for (id, expr) in env {
                formated_sym_stack.push_str(&format!("      {} := {:?}\n", id, expr))
            }
        }
        let mut formated_sym_heap = "".to_string();
        for (id, ref_val) in &self.heap {
            formated_sym_heap.push_str(&format!("   {} := {:?}\n", &id.to_string()[0..4], ref_val))
        }

        write!(
            f,
            "
State of Sym-Stack:
{}
State of Sym-Heap:
{}",
            formated_sym_stack, formated_sym_heap
        )
    }
}
