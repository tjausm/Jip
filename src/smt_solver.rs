//! Encode expressions into the smt-lib format to test satisfiability using the chosen backend

use crate::ast::{Literal, Identifier};
use crate::shared::{panic_with_diagnostics, Config,  SolverType};
use crate::symbolic::expression::{ SymExpression, SymType};
use crate::symbolic::memory::SymMemory;
use crate::symbolic::ref_values::{ArrSize, Boundary,  Reference, SymRefType, ArrSizes};
use core::fmt;
use rsmt2::print::ModelParser;
use rsmt2::{self, SmtConf, SmtRes};
use rustc_hash::FxHashSet;
use std::str::FromStr;

type Formula = String;
type Declarations = FxHashSet<(SymType, String)>;
type Assertions = FxHashSet<String>;
pub struct Model(Vec<(Identifier, Literal)>);

impl Model {

    /// given the identifier of one of the free variables, return it's value or panic
    pub fn find(&self, fv_id: &Identifier) -> Literal{
        self.0.into_iter().find(|(e, _)| e == fv_id).unwrap().1
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
            ty if ty == "Int" => SmtRes::Ok(SymType::Int),
            ty if ty == "Bool" => SmtRes::Ok(SymType::Bool),
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
    ) -> SmtRes<(Identifier, Literal)> {
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

pub struct Solver {
    s: rsmt2::Solver<Parser>,
    pub config: Config,
}

impl Solver {
    /// Creates a new solver using the configured backend.
    /// For both Yices and Cvc we pas a set of flags to make them work with the rust interface
    pub fn new(config: &Config) -> Solver {
        let conf = match &config.solver_type {
            SolverType::Z3(arg) => SmtConf::z3(arg),
            SolverType::Yices2(arg) => {
                let mut conf = SmtConf::yices_2(arg);
                conf.option("--incremental"); //add support for scope popping and pushing from solver
                conf.option("--interactive"); //add support for scope popping and pushing from solvercargo
                conf
            }
            SolverType::CVC4(arg) => {
                let mut conf = SmtConf::cvc4(arg);
                conf.option("--incremental"); //add support for scope popping and pushing from solver
                conf.option("--rewrite-divk"); //add support for `div` and `mod` operators (not working)
                conf
            }
            SolverType::Default => SmtConf::default_z3(),
        };

        let mut solver = rsmt2::Solver::new(conf, Parser).unwrap();
        solver.set_option(":print-success", "false").unwrap(); //turn off automatic succes printing in yices2
        solver.produce_models().unwrap();
        solver.set_logic(rsmt2::Logic::QF_NIA).unwrap(); //set logic to quantifier free non-linear arithmetics
        Solver {
            s: solver,
            config: config.clone(),
        }
    }

    /// returns a satisfying model of an expression if one was found
    pub fn verify_expr(&mut self, expr: &SymExpression, sym_memory: &SymMemory, sizes: Option<&ArrSizes>) -> Option<Model> {
        self.s.push(1).unwrap();

        let (expr_str, fvs, assertions) = expr_to_smtlib(expr, &sym_memory, sizes);

        if self.config.verbose {
            println!("\nInvoking z3");
            println!("SymExpression: {:?}", &expr);
            println!("  Declarations: {:?}", fvs);
            println!("  Assertions:");

            for assertion in &assertions {
                println!("      {:?}", assertion);
            }

            println!("    Formula: {:?}\n", expr_str);
        }

        for fv in fvs {
            match fv {
                (SymType::Bool, id) => self.s.declare_const(id, "Bool").unwrap(),
                (SymType::Int, id) => self.s.declare_const(id, "Int").unwrap(),
                (SymType::Ref(_), id) => self.s.declare_const(id, "Int").unwrap(),
            }
        }
        for assertion in assertions {
            self.s.assert(assertion).unwrap();
        }

        self.s.assert(expr_str.clone()).unwrap();
        let satisfiable = match self.s.check_sat() {
            Ok(b) => b,
            Err(err) => panic_with_diagnostics(
                &format!(
                    "Received backend error: {}\nWhile evaluating formula '{:?}'",
                    err, expr_str
                ),
                &(),
            ),
        };

        let rsmt2_model = self.s.get_model();
        self.s.pop(1).unwrap();
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
}

impl fmt::Debug for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut model_str = "".to_string();
        for var in &self.0 {
            let fv = format!("{:?}", var.0);
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
    sizes: Option<&ArrSizes>
) -> (Formula, Declarations, Assertions) {
    match expr {
        SymExpression::Forall(forall) => {
            let forall_expr = forall.construct(sym_memory);
            expr_to_smtlib(&forall_expr, sym_memory, sizes)
        }
        SymExpression::And(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(and {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Or(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(or {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Implies(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(=> {} {})", l, r), fv_l, a_l);
        }
        SymExpression::EQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::NE(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(distinct {} {})", l, r), fv_l, a_l);
        }
        SymExpression::LT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(< {} {})", l, r), fv_l, a_l);
        }
        SymExpression::GT(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(> {} {})", l, r), fv_l, a_l);
        }
        SymExpression::GEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(>= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::LEQ(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(<= {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Plus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(+ {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Minus(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(- {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Multiply(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(* {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Divide(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(div {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Mod(l_expr, r_expr) => {
            let (l, mut fv_l, mut a_l) = expr_to_smtlib(l_expr, &sym_memory, sizes);
            let (r, fv_r, a_r) = expr_to_smtlib(r_expr, &sym_memory, sizes);
            fv_l.extend(fv_r);
            a_l.extend(a_r);
            return (format!("(mod {} {})", l, r), fv_l, a_l);
        }
        SymExpression::Negative(expr) => {
            let (expr, fv, a) = expr_to_smtlib(expr, &sym_memory, sizes);

            return (format!("(- {})", expr), fv, a);
        }
        SymExpression::Not(expr) => {
            let (expr, fv, a) = expr_to_smtlib(expr, &sym_memory, sizes);

            return (format!("(not {})", expr), fv, a);
        }
        SymExpression::FreeVariable(ty, id) => {
            let closed_id = format!("|{}|", id);
            let mut fv = FxHashSet::default();
            fv.insert((ty.clone(), closed_id.clone()));
            (format!("{}", closed_id), fv, FxHashSet::default())
        }
        SymExpression::SizeOf(r, size_expr) => match sizes.map(|s|s.get(r)).flatten() {
            Some(ArrSize::Point(n)) => {
                expr_to_smtlib(&SymExpression::Literal(Literal::Integer(n)), &sym_memory, sizes)
            }
            Some(ArrSize::Range(Boundary::Known(min), Boundary::Known(max))) => {
                let (expr, fv, mut a) = expr_to_smtlib(size_expr, &sym_memory, sizes);
                a.insert(format!("(<= {} {})", min, expr));
                a.insert(format!("(<= {} {})", expr, max));
                return (expr, fv, a);
            }
            Some(ArrSize::Range(Boundary::Known(min), _)) => {
                let (expr, fv, mut a) = expr_to_smtlib(size_expr, &sym_memory, sizes);
                a.insert(format!("(<= {} {})", min, expr));
                return (expr, fv, a);
            }
            Some(ArrSize::Range(_, Boundary::Known(max))) => {
                let (expr, fv, mut a) = expr_to_smtlib(size_expr, &sym_memory, sizes);
                a.insert(format!("(<= {} {})", expr, max));
                return (expr, fv, a);
            }
            _ => expr_to_smtlib(size_expr, &sym_memory, sizes),
        },
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
