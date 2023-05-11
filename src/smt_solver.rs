//! Encode expressions into the smt-lib format to test satisfiability using the chosen backend

use crate::ast::{Identifier, Literal};
use crate::shared::{panic_with_diagnostics, Config, Diagnostics, Rsmt2Arg, SolverType};
use crate::symbolic::expression::{SymExpression, SymType};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::{Interval, IntervalMap, Reference, SymRefType};
use core::fmt;
use std::hash::Hash;
use std::time::{Instant, Duration};
use infinitable::Infinitable;
use rsmt2;
use rsmt2::print::ModelParser;
use rustc_hash::FxHashSet;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::mpsc;
use std::thread;
use z3;
type Formula = String;

// set of all free variables and their types
type FreeVariables = FxHashSet<(SymType, String)>;
type Assertions = FxHashSet<String>;

#[derive(Clone)]
pub struct Model(Vec<(Identifier, Literal)>);

impl Model {
    /// given the identifier of one of the free variables, return it's value or panic
    pub fn find(&self, fv_id: &Identifier) -> Literal {
        self.0
            .as_slice()
            .into_iter()
            .find(|(e, _)| e == fv_id)
            .unwrap()
            .1
            .clone()
    }
}

#[derive(Clone, Copy)]
pub struct Parser;

impl<'a> rsmt2::print::IdentParser<String, SymType, &'a str> for Parser {
    fn parse_ident(self, input: &'a str) -> rsmt2::SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, ty: &'a str) -> rsmt2::SmtRes<SymType> {
        match ty {
            ty if ty == "Int" => rsmt2::SmtRes::Ok(SymType::Int),
            ty if ty == "Bool" => rsmt2::SmtRes::Ok(SymType::Bool),
            _ => panic_with_diagnostics(&format!("Error shouldn't happen"), &()),
        }
    }
}

impl<'a> ModelParser<String, SymType, (Identifier, Literal), &'a str> for Parser {
    fn parse_value(
        self,
        input: &'a str,
        id: &String,
        _: &[(String, SymType)],
        ty: &SymType,
    ) -> rsmt2::SmtRes<(Identifier, Literal)> {
        // remove spaces & braces from input
        let clean_input = input.replace(&['(', ')', ' '][..], "");
        let clean_id = id.replace("|", "");

        let lit = match ty {
            SymType::Bool => Literal::Boolean(bool::from_str(&clean_input).unwrap()),
            _ => match i64::from_str(&clean_input) {
                Ok(i) => Literal::Integer(i),
                Err(err) => {
                    panic_with_diagnostics(&format!("Error: {:?} - Value: {}", err, input), &())
                }
            },
        };

        Ok((clean_id, lit))
    }
}

type FormulaCache = HashMap<SymExpression, Option<Model>>;

enum Solver<'a> {
    Rsmt2(Vec<Rsmt2Arg>),
    Z3Api(z3::Solver<'a>),
}

pub struct SolverEnv<'a> {
    solver: Solver<'a>,
    formula_cache: FormulaCache,
    pub config: Config,
    pub diagnostics: Diagnostics,
}

impl SolverEnv<'_> {
    pub fn build_ctx() -> z3::Context {
        // generate config with model generation and parallel solving activated and return
        let mut z3_cfg = z3::Config::new();
        z3_cfg.set_model_generation(true);
        let ctx = z3::Context::new(&z3_cfg);
        ctx
    }

    /// Creates a new solver using the configured backend.
    /// For both Yices and Cvc we pas a set of flags to make them work with the rust interface
    pub fn new<'ctx>(config: &'ctx Config, ctx: &'ctx z3::Context) -> SolverEnv<'ctx> {
        let mut solver = match &config.solver_type {
            SolverType::Rsmt2(args) => Solver::Rsmt2(args.clone()),
            SolverType::Z3Api => Solver::Z3Api(z3::Solver::new(&ctx)),
        };

        SolverEnv {
            solver,
            formula_cache: HashMap::default(),
            config: config.clone(),
            diagnostics: Diagnostics::default(),
        }
    }

    /// returns a satisfying model of an expression if one was found
    pub fn verify_expr(
        &mut self,
        expr: &SymExpression,
        sym_memory: &SymMemory,
        i: &IntervalMap,
    ) -> Option<Model> {
        // check formula cache
        if self.config.formula_caching {
            match self.formula_cache.get(expr) {
                Some(res) => return res.clone(),
                None => (),
            };
        };
        self.diagnostics.solver_calls += 1;
        let verbose = self.config.verbose;

        let solution = match &mut self.solver {
            Solver::Rsmt2(args) => verify_with_rsmt2(verbose, args, expr, sym_memory, i),
            Solver::Z3Api(solver) => verify_with_z3api(verbose, solver, expr, sym_memory, i),
        };
        if self.config.formula_caching {
            self.formula_cache.insert(expr.clone(), solution.clone());
        };
        solution
    }
}

impl Rsmt2Arg {
    pub fn into_solver(&self) -> rsmt2::Solver<Parser> {
        let mut solver = match &self {
            Rsmt2Arg::Z3(arg) => {
                let mut conf = rsmt2::SmtConf::z3(arg);
                conf.models();
                let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
                solver
            }
            Rsmt2Arg::Yices2(arg) => {
                let mut conf = rsmt2::SmtConf::yices_2(arg);
                let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
                solver.set_option(":print-success", "false").unwrap(); //turn off automatic succes printing in yices2
                solver.produce_models().unwrap();
                solver
            }
            Rsmt2Arg::CVC4(arg) => {
                let mut conf = rsmt2::SmtConf::cvc4(arg);
                conf.models();
                conf.option("--rewrite-divk"); //add support for `div` and `mod` operators (not working)
                rsmt2::Solver::new(conf, Parser).unwrap()
            }
        };
        solver.set_logic(rsmt2::Logic::QF_NIA).unwrap(); //set logic to quantifier free non-linear arithmetics
        solver
    }
}

fn verify_with_rsmt2(
    verbose: bool,
    solver_args: &Vec<Rsmt2Arg>,
    expr: &SymExpression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> Option<Model> {
    
    let mut sub_time = Instant::now();
    let tot_time = Instant::now();

    // Print readable timing and reset duration
    let bench_id : u8 = rand::random();
    let print = move |label, inst: &Instant| {
        let dur = inst.elapsed();
        println!("{:<5}{:<30}= {:?},{:0>6}", bench_id, label,  dur.as_secs(), dur.as_millis());
    };

    

    let (expr_str, fvs, assertions) = expr_to_smtlib(expr, &sym_memory, i);

    print("Expr to smtlib".to_string(), &sub_time);

    if verbose {
        println!("\nInvoking SMT-solver(s) ({:?})", solver_args);
        println!("SymExpression: {:?}", &expr);
        println!("  Declarations: {:?}", fvs);
        println!("  Assertions:");

        for assertion in &assertions {
            println!("      {:?}", assertion);
        }

        println!("    Formula: {:?}\n", expr_str);
    }

    // define sender and receiver
    let (tx, rx) = mpsc::channel();

    // initialize and parallelize each of the passed solvers
    for arg in solver_args {
        let solver_name = match arg{
            Rsmt2Arg::Z3(_) => "z3",
            Rsmt2Arg::Yices2(_) => "yices",
            Rsmt2Arg::CVC4(_) => "cvc4",
        };

        let now = Instant::now();

        // clone info needed in new thread
        let expr_str = expr_str.clone();
        let tx = tx.clone();
        let assertions = assertions.clone();
        let fvs = fvs.clone();
        let arg = arg.clone();

        print(format!("{} clone thread info", solver_name), &now);
        let now = Instant::now();

        // spawn thread and start solving
        thread::spawn(move || {

            // initialize solver from the argument
            let mut solver = arg.into_solver();
    
            print(format!("{} build solver", solver_name), &now);

            let now = Instant::now();
            // declare free variables in solver
            for fv in fvs {
                match fv {
                    (SymType::Bool, id) => solver.declare_const(id, "Bool").unwrap(),
                    (SymType::Int, id) => solver.declare_const(id, "Int").unwrap(),
                    (SymType::Ref(_), id) => solver.declare_const(id, "Int").unwrap(),
                }
            }

            // declare assertions in solver
            for assertion in assertions {
                solver.assert(assertion).unwrap();
            }

            print(format!("{} declare and assertions", solver_name), &now);
            let now = Instant::now();

            solver.assert(expr_str.clone()).unwrap();

            print(format!("{} assert expr", solver_name), &now);
            let now = Instant::now();

            let satisfiable = match solver.check_sat() {
                Ok(b) => b,
                Err(err) => panic_with_diagnostics(
                    &format!(
                        "Received backend error: {}\nWith backtrace: {:?}\nWhile evaluating formula '{:?}'",
                        err, err.backtrace(), expr_str
                    ),
                    &(),
                ),
            };
            let model = solver.get_model();
            print(format!("{} solved expr", solver_name), &now);
            tx.send((arg, satisfiable, model));
        });
    }

    // loop until we receive a solution
    loop {
        match rx.recv() {
            Ok((arg, satisfiable, rsmt2_model)) => {
                //println!("solved with {:?}", arg);
                //get variable vvalue mapping from model either return Sat(model) or Unsat
                if satisfiable {
                    let mut parsed_model: Vec<(Identifier, Literal)> = vec![];
                    match rsmt2_model {
                        Ok(rsmt2_model) => {
                            for var in rsmt2_model {
                                parsed_model.push(var.3);
                            }
                        }
                        Err(err) => panic_with_diagnostics(
                            &format!("Error during model parsing: {:?}", err),
                            &(),
                        ),
                    };
                    print("Total time".to_string(), &tot_time);
                    return Some(Model(parsed_model));
                } else {
                    print("Total time".to_string(), &tot_time);
                    return None;
                }
            }
            Err(_) => (),
        }
    }
}

fn verify_with_z3api(
    verbose: bool,
    solver: &mut z3::Solver,
    expr: &SymExpression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> Option<Model> {
    solver.push();
    let (vars, ast) = expr_to_bool(solver.get_context(), expr, sym_memory, i);

    if verbose {
        println!("\nInvoking z3-Api");
        println!("SymExpression: {:?}", &expr);

        println!("    Formula: {:?}\n", ast);
    }

    // assert inferred intervals 
    for (ty, id) in vars.iter() {
        if let SymType::Int = ty{
            let Interval(min, max) = i.get(id);
            if let Infinitable::Finite(min) = min {
                let var_ast = z3::ast::Int::new_const(solver.get_context(), id.clone());
                let min_ast = z3::ast::Int::from_i64(solver.get_context(), min);
                solver.assert(&min_ast.le(&var_ast));
            }
            if let Infinitable::Finite(max) = max {
                let var_ast = z3::ast::Int::new_const(solver.get_context(), id.clone());
                let max_ast = z3::ast::Int::from_i64(solver.get_context(), max);
                solver.assert(&var_ast.le(&max_ast));
            }
        }

    }

    solver.assert(&ast);

    let res = match solver.check() {
        z3::SatResult::Unsat => None,
        z3::SatResult::Unknown => panic_with_diagnostics(
            &format!(
                "Ooh noo, solving expression {:?} gave an unknown result",
                expr
            ),
            &(),
        ),

        
        // If satisfiable, retreive values from z3 model
        z3::SatResult::Sat => { 
            let z3_model = solver.get_model().unwrap();
            let mut model = vec![];
            for (ty, id) in vars {
                match ty {
                    SymType::Int => {
                        let ast = z3::ast::Int::new_const(&solver.get_context(), id.clone());
                        let value = z3_model.eval(&ast, true).unwrap().as_i64().unwrap();
                        model.push((id.clone(), Literal::Integer(value)));
                    }
                    SymType::Bool => {
                        let ast = z3::ast::Bool::new_const(&solver.get_context(), id.clone());
                        let value = z3_model.eval(&ast, true).unwrap().as_bool().unwrap();
                        model.push((id.clone(), Literal::Boolean(value)));
                    },
                    SymType::Ref(_) => {
                        let ast = z3::ast::Int::new_const(&solver.get_context(), id.clone());
                        let value = z3_model.eval(&ast, true).unwrap().as_i64().unwrap();
                        model.push((id.clone(), Literal::Integer(value)));
                    }
                };
            }
            Some(Model(model))
        }
    };
    solver.pop(1);
    res
}

impl fmt::Debug for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut model_str = "".to_string();
        for var in &self.0 {
            let fv = format!("{}", var.0);
            model_str = format!("{}{:<12}-> {:?}\n", model_str, fv, var.1);
        }
        write!(f, "{}", model_str)
    }
}

/// returns an expression as RSMT parseable string
/// with a set of declarations declaring free variables
/// and a set of assertions that we do berfore checking formula
fn expr_to_smtlib<'a>(
    expr: &SymExpression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (Formula, FreeVariables, Assertions) {
    match expr {
        SymExpression::Forall(forall) => {
            let forall_expr = forall.construct(sym_memory);
            expr_to_smtlib(&forall_expr, sym_memory, i)
        }
        SymExpression::And(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(and {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Or(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(or {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(=> {} {})", l, r), fv_l, a_l);
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::NE(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(distinct {} {})", l, r), fv_l, a_l);
        }
        SymExpression::LT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(< {} {})", l, r), fv_l, a_l);
        }
        SymExpression::GT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(> {} {})", l, r), fv_l, a_l);
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(>= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(<= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(+ {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(- {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(* {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(div {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(mod {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Negative(expr) => {
            let (expr, fv, a) = expr_to_smtlib(expr, &sym_memory, i);

            return (format!("(- {})", expr), fv, a);
        }
        SymExpression::Not(expr) => {
            let (expr, fv, a) = expr_to_smtlib(expr, &sym_memory, i);

            return (format!("(not {})", expr), fv, a);
        }
        SymExpression::FreeVariable(ty, id) => {
            let closed_id = format!("|{}|", id);
            let mut fv = FxHashSet::default();
            fv.insert((ty.clone(), closed_id.clone()));

            //encode intervals in assertions
            let mut a = FxHashSet::default();
            let Interval(min, max) = i.get(&id);
            if let Infinitable::Finite(min) = min {
                a.insert(format!("(<= {} {})", min, closed_id));
            }
            if let Infinitable::Finite(max) = max {
                a.insert(format!("(<= {} {})", closed_id, max));
            }

            (format!("{}", closed_id), fv, a)
        }
        SymExpression::Literal(Literal::Integer(n)) => {
            (format!("{}", n), FxHashSet::default(), FxHashSet::default())
        }
        SymExpression::Literal(Literal::Boolean(b)) => {
            (format!("{}", b), FxHashSet::default(), FxHashSet::default())
        }
        SymExpression::LazyReference(lr) => {
            let mut a = FxHashSet::default();
            let mut fv = FxHashSet::default();

            let (r, class) = lr.get();
            let r_value = format!("{}", r.get());
            let null = format!("{}", Reference::null().get());
            let r_name = format!("|lazyRef({})|", r_value);

            fv.insert((
                SymType::Ref(SymRefType::Object(class.clone())),
                r_name.clone(),
            ));
            a.insert(format!(
                "(xor (= {} {}) (= {} {}))",
                r_name, r_value, r_name, null
            ));

            (r_name, fv, a)
        }
        SymExpression::Reference(r) => (
            format!("{}", r.get()),
            FxHashSet::default(),
            FxHashSet::default(),
        ),

        otherwise => {
            panic_with_diagnostics(
                &format!(
                    "Expressions of the form {:?} are not parseable to a z3 ast",
                    otherwise
                ),
                &(),
            );
        }
    }
}

/// returns an expression as a Int ast in z3's c++ api
fn expr_to_int<'ctx, 'a>(
    ctx: &'ctx z3::Context,
    expr: &'a SymExpression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (FreeVariables, z3::ast::Int<'ctx>) {
    let (fv, ast) = expr_to_dynamic(&ctx, expr, sym_memory, i);
    return (fv, unwrap_as_int(ast));
}

/// returns an expression as a Bool ast in z3's c++ api
fn expr_to_bool<'ctx, 'a>(
    ctx: &'ctx z3::Context,
    expr: &'a SymExpression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (FreeVariables, z3::ast::Bool<'ctx>) {
    let (fv, ast) = expr_to_dynamic(&ctx, expr, sym_memory, i);
    return (fv, unwrap_as_bool(ast));
}

fn expr_to_dynamic<'ctx, 'a>(
    ctx: &'ctx z3::Context,
    expr: &'a SymExpression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (FreeVariables, z3::ast::Dynamic<'ctx>) {
    match expr {
        SymExpression::Forall(forall) => {
            let forall_expr = forall.construct(sym_memory);
            let (fv, expr) = expr_to_bool(ctx, &forall_expr, sym_memory, i);
            return (fv, z3::ast::Dynamic::from(expr))
        },
        SymExpression::And(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_bool(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_bool(ctx, r_expr, sym_memory, i);
            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Bool::and(ctx, &[&l, &r])),
            );
        }
        SymExpression::Or(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_bool(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_bool(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Bool::or(ctx, &[&l, &r])),
            );
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_bool(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_bool(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.implies(&r)));
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_dynamic(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_dynamic(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(z3::ast::Ast::_eq(&l, &r)));
        }
        SymExpression::NE(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_dynamic(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_dynamic(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Ast::_eq(&l, &r).not()),
            );
        }
        SymExpression::LT(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.lt(&r)));
        }
        SymExpression::GT(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.gt(&r)));
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.ge(&r)));
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.le(&r)));
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Int::add(&ctx, &[&l, &r])),
            );
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Int::sub(&ctx, &[&l, &r])),
            );
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Int::mul(&ctx, &[&l, &r])),
            );
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.div(&r)));
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.modulo(&r)));
        }
        SymExpression::Negative(expr) => {
            let (fv, expr) = expr_to_int(ctx, expr, sym_memory, i);

            return (fv, z3::ast::Dynamic::from(expr.unary_minus()));
        }
        SymExpression::Not(expr) => {
            let (fv, expr) = expr_to_bool(ctx, expr, sym_memory, i);
            return (fv, z3::ast::Dynamic::from(expr.not()));
        }
        SymExpression::FreeVariable(ty, id) => {
            let mut fv = FxHashSet::default();
            fv.insert((ty.clone(), id.clone()));
            match ty {
                SymType::Bool => (
                    fv,
                    z3::ast::Dynamic::from(z3::ast::Bool::new_const(ctx, id.clone())),
                ),
                SymType::Int => (
                    fv,
                    z3::ast::Dynamic::from(z3::ast::Int::new_const(ctx, id.clone())),
                ),
                SymType::Ref(_) => (
                    fv,
                    z3::ast::Dynamic::from(z3::ast::Int::new_const(ctx, id.clone())),
                ),
            }
        }
        SymExpression::Literal(Literal::Integer(n)) => (
            FxHashSet::default(),
            z3::ast::Dynamic::from(z3::ast::Int::from_i64(ctx, *n)),
        ),
        SymExpression::Literal(Literal::Boolean(b)) => (
            FxHashSet::default(),
            z3::ast::Dynamic::from(z3::ast::Bool::from_bool(ctx, *b)),
        ),
        SymExpression::Reference(r) => (
            FxHashSet::default(),
            z3::ast::Dynamic::from(z3::ast::Int::from_i64(ctx, r.get().into())),
        ),
        otherwise => {
            panic_with_diagnostics(
                &format!(
                    "Expressions of the form {:?} are not parseable to a z3 ast",
                    otherwise
                ),
                &(),
            );
        }
    }
}

fn unwrap_as_bool(d: z3::ast::Dynamic) -> z3::ast::Bool {
    match d.as_bool() {
        Some(b) => b,
        None => panic_with_diagnostics(&format!("{} is not of type Bool", d), &()),
    }
}

fn unwrap_as_int(d: z3::ast::Dynamic) -> z3::ast::Int {
    match d.as_int() {
        Some(b) => b,
        None => panic_with_diagnostics(&format!("{} is not of type Int", d), &()),
    }
}
