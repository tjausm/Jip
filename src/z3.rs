extern crate z3;

use z3::ast::{Ast, Bool, Int};
use z3::{ast, Config, Context, SatResult, Solver};

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::paths::ExecutionPath;

/*

TODO: make constants of error messages

*/

#[derive(Debug, Clone)]
enum Variable<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
}

pub fn verify_path<'a>(path: ExecutionPath) -> Result<(), String> {
    //init the 'accounting' z3 needs
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    //calculate variable hashmap and formula representing our path
    let env: HashMap<&String, Variable> = build_env(&ctx, &path);
    let formula = match path_to_formula(&ctx, &path, &env) {
        Ok(formula) => formula,
        Err(why) => return Err(why),
    };

    //negate formula to 'disprove' validity of path
    let solver = Solver::new(&ctx);
    solver.assert(&formula.not());
    let result = solver.check();
    let model = solver.get_model();

    //let debug_formula = format!("{:?}", &formula.not());
    //println!("{}", debug_formula);

    match (result, model) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            return Err(format!(
                "Following configuration violates program:\n{:?}",
                model
            ))
        }
        _ => return Err("Huh, verification gave an unkown result".to_string()),
    };
}

//optimise idea: pass program and build env once
fn build_env<'ctx, 'p>(
    ctx: &'ctx Context,
    path: &'p ExecutionPath,
) -> HashMap<&'p String, Variable<'ctx>> {
    let mut env: HashMap<&'p String, Variable<'ctx>> = HashMap::new();
    for stmt in path {
        match stmt {
            Statement::Declaration((ty, id)) => match ty {
                Nonvoidtype::Primitivetype(Primitivetype::Int) => {
                    env.insert(id, Variable::Int(Int::new_const(&ctx, id.clone())));
                }
                Nonvoidtype::Primitivetype(Primitivetype::Bool) => {
                    env.insert(id, Variable::Bool(Bool::new_const(&ctx, id.clone())));
                }
            },
            _ => (),
        }
    }
    return env;
}

fn path_to_formula<'ctx>(
    ctx: &'ctx Context,
    path: &'ctx ExecutionPath,
    env: &'ctx HashMap<&String, Variable>,
) -> Result<Bool<'ctx>, String> {
    let mut formula = ast::Bool::from_bool(&ctx, true);
    for stmt in path.iter().rev() {
        match stmt {
            Statement::Declaration(_) => (),
            Statement::Assignment((lhs, Rhs::Expr(rhs))) => {
                match lhs {
                    Lhs::Identifier(id) => {
                        let rc_env = Rc::new(env);
                        match env.get(id) {
                            // TODO: refactor this to avoid duplicate code on adding a type
                            // (tried this once but can't get the types right here without boxing and unboxing alot)
                            Some(Variable::Int(l_ast)) => {
                                let r_ast = match expression_to_int(&ctx, Rc::clone(&rc_env), rhs) {
                                    Ok(r_ast) => r_ast,
                                    Err(why) => return Err(why),
                                };
                                let substitutions = &[(l_ast, r_ast)];
                                formula = formula.substitute(substitutions);
                            }
                            Some(Variable::Bool(l_ast)) => {
                                let r_ast = match expression_to_bool(&ctx, Rc::clone(&rc_env), rhs)
                                {
                                    Ok(r_ast) => r_ast,
                                    Err(why) => return Err(why),
                                };
                                let substitutions = &[(l_ast, &r_ast)];
                                formula = formula.substitute(substitutions);
                            }
                            None => return Err(format!("Variable {} is undeclared", id)),
                        }
                    }
                }
            }
            Statement::Assert(expr) => {
                let rc_env = Rc::new(env);
                let ast = match expression_to_bool(&ctx, Rc::clone(&rc_env), expr) {
                    Ok(ast) => ast,
                    Err(why) => return Err(why),
                };

                formula = Bool::and(&ctx, &[&ast, &formula])
            }
            Statement::Assume(expr) => {
                let rc_env = Rc::new(env);
                let ast = match expression_to_bool(&ctx, Rc::clone(&rc_env), expr) {
                    Ok(ast) => ast,
                    Err(why) => return Err(why),
                };
                formula = Bool::implies(&ast, &formula)
            }
            otherwise => {
                return Err(format!(
                    "Statements of the form {:?} should not be in an executionpath",
                    otherwise
                ));
            }
        }
    }
    return Ok(formula);
}

fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: Rc<&'ctx HashMap<&String, Variable<'ctx>>>,
    expr: &Expression,
) -> Result<Bool<'ctx>, String> {
    match expr {
        Expression::GEQ(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(l.ge(r)),
                Err(why) => Err(why.to_string()),
            }
        }
        Expression::And(l_expr, r_expr) => {
            let l = expression_to_bool(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_bool(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Bool::and(ctx, &[&l, &r])),
                Err(why) => return Err(why),
            }
        }
        Expression::Not(expr) => match expression_to_bool(ctx, env, expr) {
            Ok(expr) => return Ok(expr.not()),
            otherwise => return otherwise,
        },
        otherwise => {
            return Err(format!(
                "Expressions of the form {:?} should not be in a boolean expression",
                otherwise
            ));
        }
    }
}

//flatten result to ok, or the first error encountered
fn flatten_tupple<'ctx, A>(
    (l, r): (Result<A, String>, Result<A, String>),
) -> Result<(A, A), String> {
    match (l, r) {
        (Ok(l), Ok(r)) => return Ok((l, r)),
        (Ok(l), Err(r_err)) => return Err(r_err),
        (Err(l_err), _) => return Err(l_err),
    }
}

fn expression_to_int<'ctx>(
    ctx: &'ctx Context,
    env: Rc<&'ctx HashMap<&String, Variable<'ctx>>>,
    expr: &Expression,
) -> Result<&'ctx Int<'ctx>, String> {
    match expr {
        Expression::Identifier(id) => match env.get(id) {
            Some(var) => match var {
                Variable::Int(i) => {
                    return Ok(i);
                }
                _ => {
                    return Err(format!("can't convert {:?} to an int", var));
                }
            },
            None => {
                return Err(format!("Variable {} is undeclared", id));
            }
        },

        otherwise => {
            return Err(format!(
                "Expressions of the form {:?} should not be in a integer expression",
                otherwise
            ));
        }
    };
}

#[cfg(test)]
mod tests {

    use super::*;

    lalrpop_mod!(pub parser);
    use crate::cfg::generate_cfg;
    use crate::paths::{generate_execution_paths, tests};

    fn build_test(program: &str, correct: bool) {
        let stmts = parser::StatementsParser::new().parse(program).unwrap();
        let (start_node, cfg) = generate_cfg(stmts);
        let depth = 100;
        let paths = generate_execution_paths(start_node, cfg, depth);

        for path in paths {
            assert_eq!(verify_path(path).is_ok(), correct);
        }
    }

    #[test]
    fn max_program() {
        build_test(tests::MAX, true);
    }

    #[test]
    fn faulty_max_program() {
        build_test(tests::FAULTY_MAX, false);
    }

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
}
