//! Transforms a program path to a logical formula and test satisfiability using theorem prover Z3
//!

extern crate z3;

use rustc_hash::FxHashMap;
use uuid::Uuid;

use std::fmt;
use std::rc::Rc;

use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{ast, Context, SatResult, Solver};

use crate::ast::*;
use crate::shared::{panic_with_diagnostics, Error, Scope};

use self::bindings::{fresh_bool, fresh_int};
use self::symModel::{Reference, ReferenceValue, SymExpression};

/// Contains the models for symbolic expressions, objects and arrays and accompanying helper functions.
pub mod symModel {

    use super::*;

    pub type Reference = Uuid;

    #[derive(Debug, Clone)]
    pub enum SymExpression<'a> {
        Int(Int<'a>),
        Bool(Bool<'a>),
        Ref((Type, Reference)),
    }

    /// Consists of `identifier` (= classname) and a hashmap describing it's fields
    pub type Object<'a> = (Identifier, FxHashMap<Identifier, (Type, SymExpression<'a>)>);

    pub type Array<'a> = (Type, Vec<SymExpression<'a>>);

    #[derive(Debug, Clone)]
    pub enum ReferenceValue<'a> {
        Object(Object<'a>),
        Array(Array<'a>),
        /// Takes classname as input
        UninitializedObj(Class),
    }
}

#[derive(Debug, Clone)]
struct Frame<'a> {
    pub scope: Scope,
    pub env: FxHashMap<&'a Identifier, SymExpression<'a>>,
}

type SymStack<'a> = Vec<Frame<'a>>;

type SymHeap<'a> = FxHashMap<Reference, ReferenceValue<'a>>;

/// Type representing the symbolic memory
#[derive(Clone)]
pub struct SymMemory<'ctx> {
    program: Program,
    ctx: &'ctx Context,
    stack: SymStack<'ctx>,
    heap: SymHeap<'ctx>,
}

impl<'ctx> SymMemory<'ctx> {
    pub fn new(p: Program, ctx: &'ctx Context) -> Self {
        SymMemory {
            program: p,
            ctx,
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
    pub fn stack_insert(&mut self, id: &'a Identifier, var: SymExpression<'a>) -> () {
        match self.stack.last_mut() {
            Some(s) => {
                s.env.insert(id, var);
            }
            None => (),
        };
    }

    /// Insert mapping `Identifier |-> SymbolicExpression` in frame below top most frame of stack
    pub fn stack_insert_below(&mut self, id: &'a Identifier, var: SymExpression<'a>) -> () {
        let below_index = self.stack.len() - 2;
        match self.stack.get_mut(below_index) {
            Some(frame) => {
                frame.env.insert(id, var);
            }
            _ => (),
        }
    }

    /// Iterate over frames from stack returning the first variable with given `id`
    pub fn stack_get(&self, id: &'a Identifier) -> Option<SymExpression<'a>> {
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

    /// Returns scope of top most frame in the stack
    pub fn current_scope(&self) -> &Scope {
        match self.stack.last() {
            Some(frame) => &frame.scope,
            None => panic_with_diagnostics("No scope exists currently", &self),
        }
    }

    /// Insert mapping `Reference |-> ReferenceValue` into heap
    pub fn heap_insert(&mut self, r: Reference, v: ReferenceValue<'a>) -> () {
        self.heap.insert(r, v);
    }

    /// Get symbolic value of the object's field, panics if something goes wrong
    pub fn heap_get_field(&mut self, obj_name: &String, field_name: &String) -> SymExpression<'a> {
        match self.stack_get(obj_name) {
            Some(SymExpression::Ref((_, r))) => {
                let ref_val = self.heap.get(&r).map(|s| s.clone());
                match ref_val {
                    Some(ReferenceValue::Object((_, fields))) => match fields.get(field_name) {
                        Some((ty, expr)) => expr.clone(),
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            &self,
                        ),
                    },

                    Some(ReferenceValue::UninitializedObj(class)) => {
                        let new_obj = self.init_object(&class);
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
        var: SymExpression<'a>,
    ) -> () {
        match self.stack_get(obj_name) {
            Some(SymExpression::Ref((_, r))) => match self.heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (ty, _) = match fields.get(field_name) {
                        Some(field) => field,
                        None => panic_with_diagnostics(
                            &format!("Field {} does not exist on {}", field_name, obj_name),
                            &self,
                        ),
                    };
                    fields.insert(field_name.clone(), (ty.clone(), var));
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

    pub fn heap_get_index(&self, arr_name: Identifier, index: SymExpression) -> SymExpression<'a> {
        todo!();
    }

    pub fn heap_update_index(
        &mut self,
        arr_name: Identifier,
        index: SymExpression,
        var: SymExpression,
    ) -> SymExpression<'a> {
        match self.stack_get(&arr_name){
            Some(SymExpression::Ref((_, r))) => match self.heap.get(&r){
                Some(ReferenceValue::Array((ty, arr))) => {
                    for _ in arr.len()..index{
                        match ty {
                            Type::Int => todo!(),
                            Type::Bool => todo!(),
                            Type::ClassType(_) => todo!(),
                            otherwise => panic_with_diagnostics(&format("Array of type {} is not possible", otherwise), &self)
                        }
                    }
                },
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        }
    }

    /// given a class initializes all fields lazily and returns a ReferenceValue
    pub fn init_object(&mut self, (class, members): &Class) -> ReferenceValue<'a> {
        let mut fields = FxHashMap::default();

        // map all fields to symbolic values
        for member in members {
            match member {
                Member::Field((ty, field)) => match ty {
                    Type::Int => {
                        fields.insert(
                            field.clone(),
                            (Type::Int, fresh_int(&self.ctx, field.to_string())),
                        );
                    }
                    Type::Bool => {
                        (
                            Type::Bool,
                            fields.insert(
                                field.clone(),
                                (Type::Bool, fresh_bool(&self.ctx, field.to_string())),
                            ),
                        );
                    }
                    Type::ClassType(class) => {
                        // insert uninitialized object to heap
                        let (ty, r) = (Type::ClassType(class.to_string()), Uuid::new_v4());
                        self.heap_insert(
                            r,
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
    pub fn init_array(&mut self, ty: Type, expr: &Expression) -> ReferenceValue<'a> {
        ReferenceValue::Array((ty, vec![]))
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

/// Contains all functions needed to interact with z3
pub mod bindings {

    use super::*;

    #[derive(Clone)]
    pub enum PathConstraint<'a> {
        Assume(Bool<'a>),
        Assert(Bool<'a>),
    }

    impl fmt::Debug for PathConstraint<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                PathConstraint::Assume(pc) => write!(f, "{}", pc),
                PathConstraint::Assert(pc) => write!(f, "{}", pc),
            }
        }
    }

    /// casts `SymbolicExpression` to dynamic z3 ast value from stack
    pub fn sym_expr_to_dyn<'a>(ctx: &'a Context, expr: SymExpression<'a>) -> Dynamic<'a> {
        match expr {
            SymExpression::Int(i) => Dynamic::from(i),
            SymExpression::Bool(b) => Dynamic::from(b),
            SymExpression::Ref((_, r)) => Dynamic::from(Int::from_u64(ctx, r.as_u64_pair().0)),
        }
    }

    pub fn fresh_int<'ctx>(ctx: &'ctx Context, id: String) -> SymExpression<'ctx> {
        return SymExpression::Int(Int::new_const(&ctx, id));
    }

    pub fn fresh_bool<'ctx>(ctx: &'ctx Context, id: String) -> SymExpression<'ctx> {
        return SymExpression::Bool(Bool::new_const(&ctx, id));
    }

    /// Combine the constraints in reversed order and check correctness
    /// `solve_constraints(ctx, vec![assume x, assert y, assume z] = x -> (y && z)`
    pub fn check_path<'ctx>(
        ctx: &'ctx Context,
        path_constraints: &Vec<PathConstraint<'ctx>>,
    ) -> Result<(), Error> {
        let mut constraints = Bool::from_bool(ctx, true);

        //reverse loop and combine constraints
        for constraint in path_constraints.iter().rev() {
            match constraint {
                PathConstraint::Assert(c) => constraints = Bool::and(&ctx, &[&c, &constraints]),
                PathConstraint::Assume(c) => constraints = Bool::implies(&c, &constraints),
            }
        }

        //println!("{}", constraints.not());

        let solver = Solver::new(&ctx);
        solver.assert(&constraints.not());
        let result = solver.check();
        let model = solver.get_model();

        //println!("{:?}", model);

        match (result, model) {
            (SatResult::Unsat, _) => return Ok(()),
            (SatResult::Sat, Some(model)) => {
                return Err(Error::Verification(format!(
                    "Following counter-example was found:\n{:?}",
                    model
                )));
            }
            _ => {
                return Err(Error::Verification(
                    "Huh, verification gave an unkown result".to_string(),
                ))
            }
        };
    }

    pub fn expr_to_int<'ctx>(
        ctx: &'ctx Context,
        env: &SymMemory<'ctx>,
        expr: &'ctx Expression,
    ) -> Int<'ctx> {
        return unwrap_as_int(expr_to_dynamic(&ctx, Rc::new(env), expr));
    }

    pub fn expr_to_bool<'ctx>(
        ctx: &'ctx Context,
        env: &SymMemory<'ctx>,
        expr: &'ctx Expression,
    ) -> Bool<'ctx> {
        return unwrap_as_bool(expr_to_dynamic(&ctx, Rc::new(env), expr));
    }

    fn expr_to_dynamic<'ctx, 'b>(
        ctx: &'ctx Context,
        sym_memory: Rc<&SymMemory<'ctx>>,
        expr: &'ctx Expression,
    ) -> Dynamic<'ctx> {
        match expr {
            Expression::Exists(id, expr) => {
                let l = Int::fresh_const(ctx, id);
                let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, expr));

                return Dynamic::from(ast::exists_const(&ctx, &[&l], &[], &r));
            }
            Expression::And(l_expr, r_expr) => {
                let l = unwrap_as_bool(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(Bool::and(ctx, &[&l, &r]));
            }
            Expression::Or(l_expr, r_expr) => {
                let l = unwrap_as_bool(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(Bool::or(ctx, &[&l, &r]));
            }
            Expression::EQ(l_expr, r_expr) => {
                let l = expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr);
                let r = expr_to_dynamic(ctx, sym_memory, r_expr);

                return Dynamic::from(l._eq(&r));
            }
            Expression::NE(l_expr, r_expr) => {
                let l = expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr);
                let r = expr_to_dynamic(ctx, sym_memory, r_expr);

                return Dynamic::from(l._eq(&r).not());
            }
            Expression::LT(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(l.lt(&r));
            }
            Expression::GT(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(l.gt(&r));
            }
            Expression::GEQ(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(l.ge(&r));
            }
            Expression::LEQ(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(l.le(&r));
            }
            Expression::Plus(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(ast::Int::add(&ctx, &[&l, &r]));
            }
            Expression::Minus(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(ast::Int::sub(&ctx, &[&l, &r]));
            }
            Expression::Multiply(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(ast::Int::mul(&ctx, &[&l, &r]));
            }
            Expression::Divide(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(l.div(&r));
            }
            Expression::Mod(l_expr, r_expr) => {
                let l = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), l_expr));
                let r = unwrap_as_int(expr_to_dynamic(ctx, sym_memory, r_expr));

                return Dynamic::from(l.modulo(&r));
            }
            Expression::Negative(expr) => {
                let e = unwrap_as_int(expr_to_dynamic(ctx, Rc::clone(&sym_memory), expr));

                return Dynamic::from(e.unary_minus());
            }
            Expression::Not(expr) => {
                let expr = unwrap_as_bool(expr_to_dynamic(ctx, sym_memory, expr));

                return Dynamic::from(expr.not());
            }
            Expression::Identifier(id) => match sym_memory.stack_get(id) {
                Some(sym_expr) => sym_expr_to_dyn(ctx, sym_expr),
                None => {
                    panic_with_diagnostics(&format!("Variable {} is undeclared", id), &sym_memory)
                }
            },
            Expression::Literal(Literal::Integer(n)) => Dynamic::from(ast::Int::from_i64(ctx, *n)),
            Expression::Literal(Literal::Boolean(b)) => {
                Dynamic::from(ast::Bool::from_bool(ctx, *b))
            }
            otherwise => {
                panic_with_diagnostics(
                    &format!(
                        "Expressions of the form {:?} are not parseable to a z3 ast",
                        otherwise
                    ),
                    &sym_memory,
                );
            }
        }
    }

    fn unwrap_as_bool<'ctx>(d: Dynamic<'ctx>) -> Bool<'ctx> {
        match d.as_bool() {
            Some(b) => b,
            None => panic_with_diagnostics(&format!("{} is not of type Bool", d), &()),
        }
    }

    fn unwrap_as_int<'ctx>(d: Dynamic<'ctx>) -> Int<'ctx> {
        match d.as_int() {
            Some(b) => b,
            None => panic_with_diagnostics(&format!("{} is not of type Int", d), &()),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use z3::{Config, FuncDecl};

    #[test]
    fn test_solving() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let x = Int::new_const(&ctx, "x");
        let y = Int::new_const(&ctx, "y");
        let solver = Solver::new(&ctx);
        solver.assert(&x.gt(&y));
        assert_eq!(solver.check(), SatResult::Sat);
    }

    #[test]
    fn manual_max() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let x = ast::Real::new_const(&ctx, "x");
        let y = ast::Real::new_const(&ctx, "y");
        let z = ast::Real::new_const(&ctx, "z");
        let x_plus_y = ast::Real::add(&ctx, &[&x, &y]);
        let x_plus_z = ast::Real::add(&ctx, &[&x, &z]);
        let substitutions = &[(&y, &z)];
        assert!(x_plus_y.substitute(substitutions) == x_plus_z);
    }
    #[test]
    fn exist_example() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);

        let x = ast::Int::new_const(&ctx, "x");
        let one = ast::Int::from_i64(&ctx, 1);

        let exists: ast::Bool = ast::exists_const(
            &ctx,
            &[&x],
            &[],
            &x._eq(&one), // hier gaat expression in
        )
        .try_into()
        .unwrap();

        println!("{:?}", exists);

        solver.assert(&exists.not());
    }
}
