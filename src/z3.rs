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

use self::bindings::{check_length, expr_to_int, fresh_bool, fresh_int};
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

    /// (type, concrete values, symbolic length)
    pub type Array<'a> = (Type, Vec<SymExpression<'a>>, SymExpression<'a>);

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
        if let Some(s) = self.stack.last_mut() {
            s.env.insert(id, var);
        }
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
    pub fn heap_insert(&mut self, r: Option<Reference>, v: ReferenceValue<'a>) -> Reference {
        let r = r.unwrap_or(Uuid::new_v4());
        self.heap.insert(r, v);
        r
    }

    /// Possibly update with passed `var` and return current symbolic value of the object's field
    pub fn heap_access_object(
        &mut self,
        obj_name: &String,
        field_name: &'a String,
        var: Option<SymExpression<'a>>,
    ) -> SymExpression<'a> {
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
                    let new_obj = self.init_object(&class);
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
        arr_name: &Identifier,
        index: &Expression,
        var: Option<SymExpression>,
    ) -> Result<SymExpression<'a>, Error> {
        let index = expr_to_int(self.ctx, self, index);

        let (ty, arr, length)= match self.stack_get(&arr_name){
            Some(SymExpression::Ref((_, r))) => match self.heap.get_mut(&r){
                Some(ReferenceValue::Array((ty, arr, length))) => (ty, arr, length),
                otherwise => panic_with_diagnostics(&format!("{:?} is not an array and can't be assigned to in assignment '{}[{:?}] := {:?}'", otherwise, arr_name, index, var), &self),
            },
            _ => panic_with_diagnostics(&format!("{} is not a reference", arr_name), &self),
        };

        // check if index is always < length
        check_length(self.ctx, length.clone(), SymExpression::Int(index.clone()))?;

        // instantiate null and fresh value before loop
        let (null, fresh) = match ty {
            Type::Int => (
                SymExpression::Int(Int::from_i64(self.ctx, 0)),
                bindings::fresh_int(self.ctx, format!("{}[{:?}]", arr_name, index)),
            ),
            Type::Bool => (
                SymExpression::Bool(Bool::from_bool(self.ctx, false)),
                bindings::fresh_bool(self.ctx, format!("{}[{:?}]", arr_name, index)),
            ),
            other => (
                SymExpression::Ref((other.clone(), Uuid::nil())),
                SymExpression::Ref((other.clone(), Uuid::nil())),
            ),
        };

        // if index is a literal
        match index.as_i64() {
            // then fill array up to index with value null and return last element
            Some(index) => {
                for _ in arr.len()..(index as usize) {
                    arr.push(null.clone());
                }
                Ok(arr.get(index as usize).unwrap().clone())
            }

            // otherwise return fresh
            None => Ok(fresh),
        }
    }

    pub fn heap_get_length(&self, arr_name: &Identifier) -> &SymExpression<'a> {
        match self.stack_get(&arr_name){
            Some(SymExpression::Ref((_, r))) => match self.heap.get(&r){
                Some(ReferenceValue::Array((_, _, length))) => length,
                otherwise => panic_with_diagnostics(&format!("Can't return length of {} since the value it references to ({:?}) is not an array", arr_name, otherwise), &self),
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
                        let ty = Type::ClassType(class.to_string());
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
    pub fn init_array(&mut self, ty: Type) -> ReferenceValue<'a> {
        // generate symbolic length
        let length = fresh_int(self.ctx, "array_length".to_string());

        ReferenceValue::Array((ty, vec![], length))
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

    /// Checks if `always length > index` for usage in array accessing
    pub fn check_length<'ctx>(
        ctx: &'ctx Context,
        length: SymExpression,
        index: SymExpression,
    ) -> Result<(), Error> {
        let length = unwrap_as_int(sym_expr_to_dyn(ctx, length));
        let index = unwrap_as_int(sym_expr_to_dyn(ctx, index));
        let length_gt_index = length.gt(&index);

        check_ast(ctx, &length_gt_index)
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

        check_ast(ctx, &constraints)
    }

    // returns error if there exists a counterexample for given formula
    fn check_ast<'ctx>(ctx: &'ctx Context, ast: &Bool) -> Result<(), Error> {
        let solver = Solver::new(&ctx);
        solver.assert(&ast.not());
        let result = solver.check();
        let model = solver.get_model();

        //println!("{:?}", model);

        match (result, model) {
            (SatResult::Unsat, _) => return Ok(()),
            (SatResult::Sat, Some(model)) => {
                return Err(Error::Verification(format!(
                    "For formula: {}\nFollowing counter-example was found:\n{:?}",
                    ast.to_string(),
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
            Expression::ArrLength(id) => {
                sym_expr_to_dyn(ctx, sym_memory.heap_get_length(id).clone())
            }
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

    fn unwrap_as_bool(d: Dynamic) -> Bool {
        match d.as_bool() {
            Some(b) => b,
            None => panic_with_diagnostics(&format!("{} is not of type Bool", d), &()),
        }
    }

    fn unwrap_as_int(d: Dynamic) -> Int {
        match d.as_int() {
            Some(b) => b,
            None => panic_with_diagnostics(&format!("{} is not of type Int", d), &()),
        }
    }

    #[cfg(test)]
    mod tests {

        use super::*;
        use z3::Config;

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
}
