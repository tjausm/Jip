//! Symbolic model representing the stack and heap while symbolically executing a program
//!
use rustc_hash::FxHashMap;
use std::fmt;

use super::expression::{PathConstraints, SymExpression, SymType};
use super::ref_values::{Array, EvaluatedRefs, IntervalMap, Reference, ReferenceValue, SymRefType};
use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, Scope};
use crate::smt_solver::SolverEnv;

#[derive(Debug, Clone)]
struct Frame {
    pub scope: Scope,
    pub env: FxHashMap<Identifier, SymExpression>,
}

type SymStack = Vec<Frame>;

type SymHeap = FxHashMap<i32, ReferenceValue>;

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
        let r = r.unwrap_or(Reference::new_evaluated());
        self.heap.insert(r.get_unsafe(), v);
        r
    }

    /// Returns object / array that reference points to, with 3 exceptions: (1) If reference could be null return Error;
    /// (2) if path is infeasible return Ok(None) or (3) if reference has a value but points to nothing panic
    pub fn heap_get(
        &mut self,
        r: &Reference,
        solver: &mut SolverEnv,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &mut EvaluatedRefs,
    ) -> Result<Option<ReferenceValue>, Error> {
        let i = match r.get(solver, self, pc, i, eval_refs)? {
            Some(i) => i,
            None => return Ok(None),
        };
        match self.heap.get(&i) {
            Some(ref_val) => Ok(Some(ref_val.clone())),
            None => panic_with_diagnostics(
                &format!("Reference r({}) does not point to anything", i),
                &self,
            ),
        }
    }

    /// Returns object / array that reference points to, with 3 exceptions: (1) If reference could be null return Error;
    /// (2) if path is infeasible return Ok(None) or (3) if reference has a value but points to nothing panic
    pub fn heap_get_mut(
        &mut self,
        r: &Reference,
        solver: &mut SolverEnv,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &mut EvaluatedRefs,
    ) -> Result<Option<&mut ReferenceValue>, Error> {
        let i = match r.get(solver, self, pc, i, eval_refs)? {
            Some(i) => i,
            None => return Ok(None),
        };
        match self.heap.get_mut(&i) {
            Some(ref_val) => Ok(Some(ref_val)),
            None => panic_with_diagnostics(
                &format!("Reference r({}) does not point to anything", i),
                &(),
            ),
        }
    }

    /// Get symbolic value of the object's field, panics if something goes wrong
    /// Possibly update with passed `var` and return current symbolic value of the object's field
    pub fn heap_access_object(
        &mut self,
        pc: &PathConstraints,
        i: &IntervalMap,
        eval_refs: &mut EvaluatedRefs,
        solver: &mut SolverEnv,
        obj_name: &String,
        field_name: &'a String,
        var: Option<SymExpression>,
    ) -> Result<Option<SymExpression>, Error> {
        let r = match self.stack_get(obj_name) {
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

        match self.heap_get_mut(&r, solver, pc, i, eval_refs)? {
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
            None => return Ok(None),
            otherwise => panic_with_diagnostics(
                &format!(
                    "Can't get value of '{}.{}' because {:?} is not an object'",
                    obj_name, field_name, otherwise
                ),
                &self,
            ),
        }
    }

    /// gets referencevalue reference points to without checking if the reference is valid
    pub fn heap_get_unsafe(&self, r: &Reference) -> &ReferenceValue {
        match self.heap.get(&r.get_unsafe()) {
            Some(val) => val,
            _ => panic_with_diagnostics(
                &format!("{:?} does not reference an array on the heap", r),
                &self,
            ),
        }
    }

    /// Possibly update with passed `var` and return current symbolic expression at arrays index
    pub fn heap_access_array(
        &mut self,
        pc: &mut PathConstraints,
        i: &IntervalMap,
        eval_refs: &mut EvaluatedRefs,
        solver: &mut SolverEnv,
        arr_name: &Identifier,
        index: Expression,
        var: Option<SymExpression>,
    ) -> Result<Option<SymExpression>, Error> {
        //get information about array
        let (r, size, is_lazy) = match self.stack_get(&arr_name){
            Some(SymExpression::Reference(r)) => match self.heap_get(&r, solver, pc, i, eval_refs)?{
                Some(ReferenceValue::Array((_, _, size_expr, is_lazy))) => (r, size_expr,  is_lazy),
                None => return Ok(None),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // substitute index and try to simplify it to a literal using simplifier and / or z3
        // to prevent from values being indexed twice in the array
        let mut index = SymExpression::new(self, index);
        if (solver.config.expression_evaluation) {
            index = index.clone().eval(i, None);
        }

        let evaluated_index = match index {
            SymExpression::Literal(Literal::Integer(_)) => index.clone(),
            _ => {
                // conjunct pathconstraints and  `val1 == index` and let SMT-solver find value of 'val1'
                let conjuncted_pc = Box::new(pc.conjunct());
                let val1_id = "!val1".to_string();
                let val1 = SymExpression::FreeVariable(SymType::Int, val1_id.clone());
                let index_is_val1 = SymExpression::And(
                    conjuncted_pc.clone(),
                    Box::new(SymExpression::EQ(Box::new(index.clone()), Box::new(val1))),
                );

                match solver.verify_expr(&index_is_val1, &self, i) {
                    Some(model) => {
                        // combine pathconstraints and check wheter val1 is the only value index can be`pc && val2 != val1 && val2 == index`
                        let val2 = Box::new(SymExpression::FreeVariable(
                            SymType::Int,
                            "!val2".to_string(),
                        ));
                        let val1_lit = model.find(&val1_id);
                        let val1 = Box::new(SymExpression::Literal(val1_lit.clone()));
                        let index_is_val2 = SymExpression::And(
                            conjuncted_pc,
                            Box::new(SymExpression::And(
                                Box::new(SymExpression::NE(val1, val2.clone())),
                                Box::new(SymExpression::EQ(val2, Box::new(index.clone()))),
                            )),
                        );

                        // if index can be any other value than val1 return sym_index, otherwise return val1
                        match solver.verify_expr(&index_is_val2, &self, i) {
                            Some(_) => index.clone(),
                            None => SymExpression::Literal(val1_lit),
                        }
                    }
                    None => index.clone(),
                }
            }
        };

        // build expression index < length
        let mut index_lt_size = SymExpression::LT(Box::new(index.clone()), Box::new(size.clone()));
        if solver.config.expression_evaluation {
            index_lt_size = index_lt_size.eval(i, None);
        };

        match (index_lt_size) {
            SymExpression::Literal(Literal::Boolean(true)) => (),
            _ => {
                // add 'index < size' as inner most constraint of pc  '!(pc1 => (pc2 && index < size))'
                pc.push_assertion(index_lt_size);
                let not_pc_implies_index_lt_size =
                    &SymExpression::Not(Box::new(pc.combine_over_true()));

                // remove assertion to save memory e.g. if its
                pc.pop();

                // try to find counter-example
                match solver.verify_expr(not_pc_implies_index_lt_size, &self, i) {
                    None => (),
                    Some(model) => {
                        return Err(Error::Verification(format!(
                            "Following input could access an array out of bounds:\n{:?}",
                            model
                        )));
                    }
                }
            }
        };

        //get mutable HashMap representing array
        let (ty, arr) = match self.stack_get(&arr_name){
            Some(SymExpression::Reference(r)) => match self.heap_get_mut(&r, solver, pc, i, eval_refs)?{
                Some(ReferenceValue::Array((ty, arr, _, _))) => (ty, arr),
                None => return Ok(None),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // if we insert var or var is already in arr then return
        if let Some(var) = var {
            arr.insert(evaluated_index, var.clone());
            return Ok(Some(var));
        }
        if let Some(v) = arr.get(&evaluated_index) {
            return Ok(Some(v.clone()));
        }

        // otherwise generate new
        match (is_lazy, &ty) {
            (false, SymType::Ref(SymRefType::Object(class))) => {
                // generate and insert reference
                let r = Reference::new_evaluated();
                let sym_r = SymExpression::Reference(r.clone());
                arr.insert(evaluated_index, sym_r.clone());

                // instantiate object and insert under reference afterwards (to please borrowchecker)
                let class = class.clone();
                let obj = self.init_object(class);
                self.heap_insert(Some(r), obj);

                Ok(Some(sym_r))
            }
            // generate and return lazy reference
            (true, SymType::Ref(SymRefType::Object(class))) => {
                // generate and insert reference
                let lr = Reference::new_lazy(class.clone());
                let sym_lr = SymExpression::Reference(lr);
                arr.insert(evaluated_index, sym_lr.clone());

                Ok(Some(sym_lr))
            }
            (_, SymType::Ref(SymRefType::Array(_))) => {
                todo!("2+ dimensional arrays are not supported")
            }

            (false, SymType::Int) => {
                let lit = SymExpression::Literal(Literal::Integer(0));
                arr.insert(evaluated_index, lit.clone());
                Ok(Some(lit))
            }
            (false, SymType::Bool) => {
                let lit = SymExpression::Literal(Literal::Boolean(false));
                arr.insert(evaluated_index, lit.clone());
                Ok(Some(lit))
            }
            _ => {
                let fv_id = format!("{}[{:?}]", arr_name.clone(), evaluated_index);
                let fv = SymExpression::FreeVariable(ty.clone(), fv_id);
                arr.insert(evaluated_index, fv.clone());
                Ok(Some(fv))
            }
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
    pub fn init_lazy_object(&mut self, r: i32, class: Identifier) -> ReferenceValue {
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
                        let lr = Reference::new_lazy(class.clone());
                        let lazy_ref = SymExpression::Reference(lr);

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
