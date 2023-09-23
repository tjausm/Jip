//! Encode expressions into the smt-lib format to test satisfiability using the chosen backend

use crate::ast::{Identifier, Literal};
use crate::shared::{panic_with_diagnostics, Config, Diagnostics, SolverType};
use crate::symbolic::expression::{Expression, SymType, NormalizedExpression};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::{Interval, IntervalMap, Reference, SymRefType};
use core::fmt;
use infinitable::Infinitable;
use rsmt2;
use rsmt2::print::ModelParser;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashMap;
use std::str::FromStr;
use z3;
type Formula = String;
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
struct Parser;

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

type EquivalentFormulaCache = HashMap<NormalizedExpression, Option<Model>>;
type FormulaCache = HashMap<Expression, Option<Model>>;

enum Solver<'a> {
    Rsmt2(rsmt2::Solver<Parser>),
    Z3Api(z3::Solver<'a>),
}

pub struct SolverEnv<'a> {
    solver: Solver<'a>,
    expression_cache: FormulaCache,
    normalized_expression_caching: EquivalentFormulaCache,
    pub config: Config,
    pub diagnostics: Diagnostics
}

impl SolverEnv<'_> {
    pub fn build_ctx() -> z3::Context {
        let z3_cfg = z3::Config::new();
        let ctx = z3::Context::new(&z3_cfg);
        ctx
    }

    /// Creates a new solver using the configured backend.
    /// For both Yices and Cvc we pas a set of flags to make them work with the rust interface
    pub fn new<'ctx>(
        cfg_size: usize,
        config: &'ctx Config,
        ctx: &'ctx z3::Context,
    ) -> SolverEnv<'ctx> {
        let mut solver = match &config.solver_type {
            SolverType::Z3(arg) => {
                let mut conf = rsmt2::SmtConf::z3(arg);
                conf.models();
                let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
                solver.set_logic(rsmt2::Logic::QF_NIA).unwrap(); //set logic to quantifier free non-linear arithmetics
                Solver::Rsmt2(solver)
            }
            SolverType::Yices2(arg) => {
                let mut conf = rsmt2::SmtConf::yices_2(arg);
                conf.models();
                conf.option("--incremental"); // turn on scope popping and pushing
                let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
                solver.set_option(":print-success", "false").unwrap(); //turn off automatic succes printing in yices2
                solver.produce_models().unwrap();
                solver.set_logic(rsmt2::Logic::QF_NIA).unwrap(); //set logic to quantifier free non-linear arithmetics
                Solver::Rsmt2(solver)
            }
            SolverType::CVC4(arg) => {
                let mut conf = rsmt2::SmtConf::cvc4(arg);
                conf.models();
                conf.option("--rewrite-divk"); //add support for `div` and `mod` operators (not working)
                conf.option("--incremental"); //add support for `div` and `mod` operators (not working)
                let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
                solver.set_logic(rsmt2::Logic::QF_NIA).unwrap(); //set logic to quantifier free non-linear arithmetics
                Solver::Rsmt2(solver)
            }
            SolverType::Z3Api => Solver::Z3Api(z3::Solver::new(&ctx)),
        };

        SolverEnv {
            solver,
            normalized_expression_caching: HashMap::default(),
            expression_cache: HashMap::default(),
            config: config.clone(),
            diagnostics: Diagnostics::new(cfg_size),
        }
    }

    /// returns a satisfying model of an expression if one was found
    pub fn satisfiable(
        &mut self,
        expr: &Expression,
        sym_memory: &SymMemory,
        i: &IntervalMap,
    ) -> Option<Model> {

        // memoize normalization 
        let mut norm_expr = None;

        // check formula cache
        if self.config.expression_caching {
            match self.expression_cache.get(expr) {
                Some(res)  => {
                    self.diagnostics.cache_hits += 1;
                    return res.clone()
                },
                None => (),
            };
        } else if self.config.equivalent_formula_caching {
            let norm_expr2 = expr.clone().normalize();
            match self.normalized_expression_caching.get(&norm_expr2) {
                Some(res)  => {
                    self.diagnostics.eq_cache_hits += 1;
                    return res.clone()
                },
                None => (),
            };
            norm_expr = Some(norm_expr2)
        };

        // solve using chosen backend
        self.diagnostics.smt_calls += 1;
        let res = match &mut self.solver {
            Solver::Rsmt2(solver) => {
                SolverEnv::rsmt2_satisfiable(&self.config, solver, expr, sym_memory, i)
            }
            Solver::Z3Api(solver) => {
                SolverEnv::z3api_satisfiable(&self.config, solver, expr, sym_memory, i)
            }
        };

        // update formula cache
        if self.config.expression_caching {
            self.expression_cache.insert(expr.clone(), res.clone());
        } else if self.config.equivalent_formula_caching {
            let norm_expr = norm_expr.unwrap_or(expr.clone().normalize());
            self.normalized_expression_caching
                .insert(norm_expr, res.clone());
        };
        res
    }

    fn rsmt2_satisfiable(
        config: &Config,
        solver: &mut rsmt2::Solver<Parser>,
        expr: &Expression,
        sym_memory: &SymMemory,
        i: &IntervalMap,
    ) -> Option<Model> {
        solver.push(1).unwrap();
        let (expr_str, fvs, assertions) = expr_to_smtlib(expr, &sym_memory, i);

        if config.verbose {
            println!("\nInvoking z3");
            println!("SymExpression: {:?}", &expr);
            println!("  Declarations: {:?}", fvs);
            println!("  Assertions:");

            for assertion in &assertions {
                println!("      {:?}", assertion);
            }

            println!("    Formula: {:?}\n", expr_str);
        }

        // declare free variables
        for fv in fvs {
            match fv {
                (SymType::Bool, id) => solver.declare_const(id, "Bool").unwrap(),
                (SymType::Int, id) => solver.declare_const(id, "Int").unwrap(),
                (SymType::Ref(_), id) => solver.declare_const(id, "Int").unwrap(),
            }
        }

        // perform set of collected assertions
        for assertion in assertions {
            solver.assert(assertion).unwrap();
        }

        solver.assert(expr_str.clone()).unwrap();
        let satisfiable = match solver.check_sat() {
            Ok(b) => b,
            Err(err) => panic_with_diagnostics(
                &format!(
                    "Received backend error: {}\nWhile evaluating formula '{:?}'",
                    err, expr_str
                ),
                &(),
            ),
        };

        let rsmt2_model = solver.get_model();
        solver.pop(1).unwrap();

        //either return Sat(model) or Unsat
        if satisfiable {
            let mut model: Vec<(Identifier, Literal)> = vec![];
            match rsmt2_model {
                Ok(rsmt2_model) => {
                    for var in rsmt2_model {
                        model.push(var.3);
                    }
                }
                Err(err) => {
                    panic_with_diagnostics(&format!("Error during model parsing: {:?}", err), &())
                }
            };
            Some(Model(model))
        } else {
            None
        }
    }

    fn z3api_satisfiable(
        config: &Config,
        solver: &mut z3::Solver,
        expr: &Expression,
        sym_memory: &SymMemory,
        i: &IntervalMap,
    ) -> Option<Model> {
        solver.push();
        let (vars, ast) = expr_to_bool(solver.get_context(), expr, sym_memory, i);

        if config.verbose {
            println!("\nInvoking z3");
            println!("SymExpression: {:?}", &expr);

            println!("    Formula: {:?}\n", ast);
        }

        // encode intervals in z3
        for (id, Interval(a, b)) in &i.0 {
            if let Infinitable::Finite(a) = a {
                let a_leq_id = Expression::LEQ(
                    Box::new((Expression::Literal(Literal::Integer(*a)))),
                    Box::new(Expression::FreeVariable(SymType::Int, id.clone())),
                );
                let (_, a_leq_id_ast) =
                    expr_to_bool(solver.get_context(), &a_leq_id, sym_memory, i);
                solver.assert(&a_leq_id_ast);
            }
            if let Infinitable::Finite(b) = b {
                let id_leq_b = Expression::LEQ(
                    Box::new(Expression::FreeVariable(SymType::Int, id.clone())),
                    Box::new((Expression::Literal(Literal::Integer(*b)))),
                );
                let (_, id_leq_b_ast) =
                    expr_to_bool(solver.get_context(), &id_leq_b, sym_memory, i);
                solver.assert(&id_leq_b_ast);
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
                        }
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
    expr: &Expression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (Formula, FreeVariables, Assertions) {
    match expr {
        Expression::Forall(forall) => {
            let forall_expr = forall.construct(sym_memory);
            expr_to_smtlib(&forall_expr, sym_memory, i)
        }
        Expression::And(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(and {} {})", l, r), fv_l, a_l);
        }
        Expression::Or(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(or {} {})", l, r), fv_l, a_l);
        }
        Expression::Implies(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(=> {} {})", l, r), fv_l, a_l);
        }
        Expression::EQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(= {} {})", l, r), fv_l, a_l);
        }
        Expression::NE(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(distinct {} {})", l, r), fv_l, a_l);
        }
        Expression::LT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(< {} {})", l, r), fv_l, a_l);
        }
        Expression::GT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(> {} {})", l, r), fv_l, a_l);
        }
        Expression::GEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(>= {} {})", l, r), fv_l, a_l);
        }
        Expression::LEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(<= {} {})", l, r), fv_l, a_l);
        }
        Expression::Plus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(+ {} {})", l, r), fv_l, a_l);
        }
        Expression::Minus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(- {} {})", l, r), fv_l, a_l);
        }
        Expression::Multiply(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(* {} {})", l, r), fv_l, a_l);
        }
        Expression::Divide(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(div {} {})", l, r), fv_l, a_l);
        }
        Expression::Mod(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, i);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, i);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(mod {} {})", l, r), fv_l, a_l);
        }
        Expression::Negative(expr) => {
            let (expr, fv, a) = expr_to_smtlib(expr, &sym_memory, i);

            return (format!("(- {})", expr), fv, a);
        }
        Expression::Not(expr) => {
            let (expr, fv, a) = expr_to_smtlib(expr, &sym_memory, i);

            return (format!("(not {})", expr), fv, a);
        }
        Expression::FreeVariable(ty, id) => {
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
        Expression::Literal(Literal::Integer(n)) => {
            (format!("{}", n), FxHashSet::default(), FxHashSet::default())
        }
        Expression::Literal(Literal::Boolean(b)) => {
            (format!("{}", b), FxHashSet::default(), FxHashSet::default())
        }
        Expression::Reference(r) => match r {
            Reference::Evaluated(r) => {
                (format!("{}", r), FxHashSet::default(), FxHashSet::default())
            }
            Reference::Lazy { r, class } => {
                let mut a = FxHashSet::default();
                let mut fv = FxHashSet::default();

                let r_value = format!("{}", r);
                let null = format!("{}", Reference::null().get_unsafe());
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
        },

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
    expr: &'a Expression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (FreeVariables, z3::ast::Int<'ctx>) {
    let (fv, ast) = expr_to_dynamic(&ctx, expr, sym_memory, i);
    return (fv, unwrap_as_int(ast));
}

/// returns an expression as a Bool ast in z3's c++ api
fn expr_to_bool<'ctx, 'a>(
    ctx: &'ctx z3::Context,
    expr: &'a Expression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (FreeVariables, z3::ast::Bool<'ctx>) {
    let (fv, ast) = expr_to_dynamic(&ctx, expr, sym_memory, i);
    return (fv, unwrap_as_bool(ast));
}

fn expr_to_dynamic<'ctx, 'a>(
    ctx: &'ctx z3::Context,
    expr: &'a Expression,
    sym_memory: &SymMemory,
    i: &IntervalMap,
) -> (FreeVariables, z3::ast::Dynamic<'ctx>) {
    match expr {
        Expression::Forall(forall) => {
            let forall_expr = forall.construct(sym_memory);
            let (fv, ast) = expr_to_bool(ctx, &forall_expr, sym_memory, i);
            return (fv, z3::ast::Dynamic::from(ast));
        }
        Expression::And(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_bool(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_bool(ctx, r_expr, sym_memory, i);
            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Bool::and(ctx, &[&l, &r])),
            );
        }
        Expression::Or(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_bool(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_bool(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Bool::or(ctx, &[&l, &r])),
            );
        }
        Expression::Implies(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_bool(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_bool(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.implies(&r)));
        }
        Expression::EQ(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_dynamic(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_dynamic(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(z3::ast::Ast::_eq(&l, &r)));
        }
        Expression::NE(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_dynamic(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_dynamic(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Ast::_eq(&l, &r).not()),
            );
        }
        Expression::LT(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.lt(&r)));
        }
        Expression::GT(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.gt(&r)));
        }
        Expression::GEQ(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.ge(&r)));
        }
        Expression::LEQ(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.le(&r)));
        }
        Expression::Plus(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Int::add(&ctx, &[&l, &r])),
            );
        }
        Expression::Minus(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Int::sub(&ctx, &[&l, &r])),
            );
        }
        Expression::Multiply(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (
                fv_l,
                z3::ast::Dynamic::from(z3::ast::Int::mul(&ctx, &[&l, &r])),
            );
        }
        Expression::Divide(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.div(&r)));
        }
        Expression::Mod(l_expr, r_expr) => {
            let (mut fv_l, l) = expr_to_int(ctx, l_expr, sym_memory, i);
            let (fv_r, r) = expr_to_int(ctx, r_expr, sym_memory, i);

            fv_l.extend(fv_r);
            return (fv_l, z3::ast::Dynamic::from(l.modulo(&r)));
        }
        Expression::Negative(expr) => {
            let (fv, expr) = expr_to_int(ctx, expr, sym_memory, i);

            return (fv, z3::ast::Dynamic::from(expr.unary_minus()));
        }
        Expression::Not(expr) => {
            let (fv, expr) = expr_to_bool(ctx, expr, sym_memory, i);
            return (fv, z3::ast::Dynamic::from(expr.not()));
        }
        Expression::FreeVariable(ty, id) => {
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
        Expression::Literal(Literal::Integer(n)) => (
            FxHashSet::default(),
            z3::ast::Dynamic::from(z3::ast::Int::from_i64(ctx, *n)),
        ),
        Expression::Literal(Literal::Boolean(b)) => (
            FxHashSet::default(),
            z3::ast::Dynamic::from(z3::ast::Bool::from_bool(ctx, *b)),
        ),
        Expression::Reference(r) => (
            FxHashSet::default(),
            z3::ast::Dynamic::from(z3::ast::Int::from_i64(ctx, r.get_unsafe().into())),
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
