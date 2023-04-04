//! Symbolic model representing the stack and heap while symbolically executing a program
//!
use rustc_hash::FxHashMap;
use std::fmt;

use super::expression::{PathConstraints, SymExpression, SymType};
use super::ref_values::{
    ArrSize, ArrSizes, Array, EvaluatedRefs, LazyReference, Reference, ReferenceValue, SymRefType,
};
use crate::ast::*;
use crate::shared::{panic_with_diagnostics,  Error, Scope};
use crate::smt_solver::SolverEnv;

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
            s.env.insert(id, sym_expr);
        }
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in frame below top most frame of stack
    pub fn stack_insert_below(&mut self, id: Identifier, sym_expr: SymExpression) -> () {
        let below_index = self.stack.len() - 2;
        match self.stack.get_mut(below_index) {
            Some(frame) => {
                frame.env.insert(id, sym_expr);
            }
            _ => panic_with_diagnostics(&format!("No frame below"), &self),
        }
    }

    /// Iterate over frames from stack returning the first variable with given `id`
    pub fn stack_get(&self, id: &'a Identifier) -> Option<SymExpression> {
        if id == "null" {
            return Some(SymExpression::Reference(Reference::null()));
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

    /// Inserts mapping `Reference |-> ReferenceValue` into heap returning it's reference.
    /// Generates new reference if none is given
    pub fn heap_insert(&mut self, r: Option<Reference>, v: ReferenceValue) -> Reference {
        let r = r.unwrap_or(Reference::new());
        self.heap.insert(r, v);
        r
    }

    /// Get symbolic value of the object's field, panics if something goes wrong
    /// Possibly update with passed `var` and return current symbolic value of the object's field
    pub fn heap_access_object(
        &mut self,
        pc: &PathConstraints,
        arr_sizes: &ArrSizes,
        eval_refs: &mut EvaluatedRefs,
        solver: &mut SolverEnv,
        obj_name: &String,
        field_name: &'a String,
        var: Option<SymExpression>,
    ) -> Result<Option<SymExpression>, Error> {
        let r = match self.stack_get(obj_name) {
            Some(SymExpression::LazyReference(lr)) =>
            // if path is infeasible return nothing otherwise initialize obj and return ref
            {
                match lr.initialize( solver, self, pc, arr_sizes, eval_refs)? {
                    Some(r) => r,
                    _ => return Ok(None),
                }
            }
            Some(SymExpression::Reference(r)) => r,
            Some(otherwise) => panic_with_diagnostics(
                &format!(
                    "Error while accessing {} because {:?} is not a reference",
                    obj_name, otherwise
                ),
                &self,
            ),
            _ => panic_with_diagnostics(&format!("Did you declare object {}?", obj_name), &self),
        };

        match self.heap.get_mut(&r) {
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
                        Ok(Some(var))
                    }
                    None => Ok(Some(expr.clone())),
                }
            }
            None => panic_with_diagnostics(
                &format!(
                    "Can't get value of '{}.{}' because {} with reference {:?} this does not seem to refer to an object'",
                    obj_name, field_name, obj_name, &r
                ),
                &self,
            ),
            otherwise => panic_with_diagnostics(
                &format!(
                    "Can't get value of '{}.{}' because {:?} is not an object'",
                    obj_name, field_name, otherwise
                ),
                &self,
            ),
        }
    }

    pub fn heap_get(&self, r: Reference) -> &ReferenceValue {
        match self.heap.get(&r) {
            Some(ref_val) => ref_val,
            _ => panic_with_diagnostics(
                &format!("{:?} does not reference anything on the heap", r),
                &self,
            ),
        }
    }

    /// Possibly update with passed `var` and return current symbolic expression at arrays index
    pub fn heap_access_array(
        &mut self,
        pc: &PathConstraints,
        sizes: &ArrSizes,
        solver: &mut SolverEnv,
        arr_name: &Identifier,
        index: Expression,
        var: Option<SymExpression>,
    ) -> Result<SymExpression, Error> {

        //get information about array
        let (r, size_expr, size, is_lazy) = match self.stack_get(&arr_name){
            Some(SymExpression::Reference(r)) => match self.heap.get(&r){
                Some(ReferenceValue::Array((_, _, size_expr, is_lazy))) => (r, size_expr, sizes.get(&r),  *is_lazy),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // substitute index and try to simplify it to a literal using simplifier and / or z3
        // to prevent from values being indexed twice in the array
        let sym_index = SymExpression::new(self, index);
        let simple_index = sym_index.clone().simplify(Some(sizes), None); // simplify to prevent simplified see from having different results
        


        let evaluated_index = match simple_index {
            SymExpression::Literal(_) => simple_index,
            _ => {
                let pc_expr = Box::new(pc.conjunct());

                // check if z3 can find a value for index
                let val1_id = "!val1".to_string();
                let val1 = SymExpression::FreeVariable(SymType::Int, val1_id.clone());

                // check if there is a literal value for `index: pc && val1 == index` 
                let index_is_val1 = SymExpression::And(pc_expr.clone(), Box::new(SymExpression::EQ(Box::new(simple_index.clone()), Box::new(val1))));
                match solver.verify_expr(&index_is_val1, &self, Some(sizes)) {
                    Some(model) => {

                        let val2_id = "!val2".to_string();
                        let val2 = Box::new(SymExpression::FreeVariable(SymType::Int, val2_id.clone()));

                        // check if there is another literal value for index: `pc && val2 != val1 && val2 == index`
                        let val1_lit = model.find(&val1_id);
                        let val1 = Box::new(SymExpression::Literal(val1_lit.clone()));
                        let index_is_val2 = SymExpression::And(pc_expr, Box::new(SymExpression::And(Box::new(SymExpression::NE(val1, val2.clone())), Box::new(SymExpression::EQ(val2, Box::new(simple_index.clone()))))));

                        match solver.verify_expr(&index_is_val2, &self, Some(sizes)){
                            Some(_) => simple_index,
                            None => SymExpression::Literal(val1_lit),
                        }


                    
                    },
                    None => simple_index,
                }
            }
        };



        // check if index is always < length
        match (&evaluated_index, &size_expr, &size) {
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
                let size_of = SymExpression::SizeOf(r, Box::new(size_expr.clone()));

                //append length > index to PathConstraints and try to falsify
                let length_gt_index =
                    SymExpression::GT(Box::new(size_of.clone()), Box::new(evaluated_index.clone()));
                let mut pc = pc.clone();
                pc.push_assertion(length_gt_index);
                let constraints = pc.combine_over_true();

                match solver.verify_expr(&SymExpression::Not(Box::new(constraints)), &self, Some(sizes)) {
                    None => (),
                    Some(model) => {
                        return Err(Error::Verification(format!(
                    "Following input could (potentially) accesses an array out of bounds:\n{:?}",
                    model
                )));
                    }
                }
            }
        };

        //get mutable HashMap representing array
        let (ty, arr) = match self.stack_get(&arr_name){
            Some(SymExpression::Reference(r)) => match self.heap.get_mut(&r){
                Some(ReferenceValue::Array((ty, arr, _, _))) => (ty, arr),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, sym_index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // if we insert var or var is already in arr then return
        if let Some(var) = var {
            arr.insert(evaluated_index, var.clone());
            return Ok(var);
        }
        if let Some(v) = arr.get(&evaluated_index) {
            return Ok(v.clone());
        }

        // otherwise generate new
        match (is_lazy, &ty) {
            (false, SymType::Ref(SymRefType::Object(class))) => {
                // generate and insert reference
                let r = Reference::new();
                let sym_r = SymExpression::Reference(r);
                arr.insert(evaluated_index, sym_r.clone());

                // instantiate object and insert under reference afterwards (to please borrowchecker)
                let class = class.clone();
                let obj = self.init_object(class);
                self.heap_insert(Some(r), obj);

                Ok(sym_r)
            }
            // generate and return lazy reference
            (true, SymType::Ref(SymRefType::Object(class))) => {
                // generate and insert reference
                let lr = LazyReference::new(class.clone());
                let sym_lr = SymExpression::LazyReference(lr);
                arr.insert(evaluated_index, sym_lr.clone());

                Ok(sym_lr)
            }
            (_, SymType::Ref(SymRefType::Array(_))) => {
                todo!("2+ dimensional arrays are not supported")
            }

            (false, SymType::Int) => {
                let lit = SymExpression::Literal(Literal::Integer(0));
                arr.insert(evaluated_index, lit.clone());
                Ok(lit)
            }
            (false, SymType::Bool) => {
                let lit = SymExpression::Literal(Literal::Boolean(false));
                arr.insert(evaluated_index, lit.clone());
                Ok(lit)
            }
            _ => {
                let fv_id = format!("{}[{:?}]", arr_name.clone(), evaluated_index);
                let fv = SymExpression::FreeVariable(ty.clone(), fv_id);
                arr.insert(evaluated_index, fv.clone());
                Ok(fv)
            }
        }
    }

    // return the symbolic length of an array
    pub fn heap_get_arr_length(&self, arr_name: &Identifier) -> SymExpression {
        match self.stack_get(&arr_name){
        Some(SymExpression::Reference(r)) => match self.heap.get(&r){
            Some(ReferenceValue::Array((_, _, length, _))) => length.clone(),
            otherwise => panic_with_diagnostics(&format!("Can't return length of {} since the value it references to ({:?}) is not an array", arr_name, otherwise), &self),
        },
        _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
    }
    }

    // inits an object with al it's fields uninitialised
    pub fn init_object(&mut self, class: Identifier) -> ReferenceValue {
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

    // inits 1 objects with its concrete fields as free variables and its reference fields as lazy references
    pub fn init_lazy_object(&mut self, r: Reference, class: Identifier) -> ReferenceValue {
        let mut fields = FxHashMap::default();

        let members = self.prog.get_class(&class).1.clone();
        // map all fields to symbolic values
        for member in members {
            match member {
                Member::Field((ty, field)) => match ty {
                    (Type::Int) => {
                        let field_name = format!("{:?}.{}", r, field);

                        fields.insert(
                            field.clone(),
                            SymExpression::FreeVariable(SymType::Int, field_name),
                        );
                    }
                    Type::Bool => {
                        let field_name = format!("{:?}.{}", r, field);

                        fields.insert(
                            field.clone(),
                            SymExpression::FreeVariable(SymType::Bool, field_name),
                        );
                    }
                    Type::Class(class) => {
                        // either make lazy object or uninitialized
                        let lr = LazyReference::new(class.clone());
                        let lazy_ref = SymExpression::LazyReference(lr);

                        fields.insert(field.clone(), lazy_ref);
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
    pub fn init_array(
        &mut self,
        ty: SymType,
        size_expr: SymExpression,
        is_lazy: bool,
    ) -> ReferenceValue {
        ReferenceValue::Array((ty, FxHashMap::default(), size_expr, is_lazy))
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
            ReferenceValue::Array((ty, entries, len, _)) => {
                let mut formated_obj = format!("{:?}[] with length {:?}", ty, len);
                for (index, value) in entries {
                    formated_obj
                        .push_str(&format!("\n                [{:?}] := {:?}", index, value))
                }
                write!(f, "{}", formated_obj)
            }
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
                Some(id) => formated_sym_stack.push_str(&format!("{}\n", id)),
            }

            // add all values of sym_stack
            for (id, expr) in env {
                formated_sym_stack.push_str(&format!("      {} := {:?}\n", id, expr))
            }
        }
        let mut formated_sym_heap = "".to_string();
        for (r, ref_val) in &self.heap {
            formated_sym_heap.push_str(&format!("   {:?} := {:?}\n", r, ref_val))
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
