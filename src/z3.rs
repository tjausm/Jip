extern crate z3;

use z3::ast::{Ast, Bool, Int};
use z3::{ast, AstKind, Config, Context, SatResult, Solver};

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::paths::ExecutionPath;

pub enum Error {
    Syntax(String),
    Semantics(String),
    Verification(String),
    Other(String)
}

#[derive(Debug, Clone)]
enum Variable<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
}

pub fn print_formula<'a>(path: ExecutionPath) -> Result<String, Error> {
    //init the 'accounting' z3 needs
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    //calculate variable hashmap and formula representing our path
    let env: HashMap<&String, Variable> = build_env(&ctx, &path);
    let formula = match path_to_formula(&ctx, &path, &env) {
        Ok(formula) => return Ok(format!("{}", &formula.not())),
        Err(why) => return Err(why),
    };
}

pub fn verify_path<'a>(path: ExecutionPath) -> Result<(), Error> {
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
    solver.assert(&formula);
    let result = solver.check();
    let model = solver.get_model();

    match (result, model) {
        (SatResult::Unsat, _) => return Ok(()),
        (SatResult::Sat, Some(model)) => {
            return Err(Error::Verification(format!(
                "Following configuration violates program:\n{:?}",
                model
            )))
        }
        _ => return Err(Error::Verification("Huh, verification gave an unkown result".to_string())),
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
) -> Result<Bool<'ctx>, Error> {
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
                                let substitutions = &[(l_ast, &r_ast)];
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
                            None => return Err(Error::Semantics(format!("Variable {} is undeclared", id))),
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
                return Err(Error::Semantics(format!(
                    "Statements of the form {:?} should not be in an executionpath",
                    otherwise
                )));
            }
        }
    }
    return Ok(formula.not());
}

fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: Rc<&'ctx HashMap<&String, Variable<'ctx>>>,
    expr: &Expression,
) -> Result<Bool<'ctx>, Error> {
    match expr {

        Expression::And(l_expr, r_expr) => {
            let l = expression_to_bool(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_bool(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Bool::and(ctx, &[&l, &r])),
                Err(why) => return Err(why),
            }
        }
        Expression::Or(l_expr, r_expr) => {
            let l = expression_to_bool(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_bool(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(Bool::or(ctx, &[&l, &r])),
                Err(why) => return Err(why),
            }
        }
        // Because type of expression is unknown, and it must be known for _eq() we try all conversion functions
        Expression::EQ(l_expr, r_expr) => {
            match (expression_to_int(ctx, Rc::clone(&env), l_expr), expression_to_int(ctx, Rc::clone(&env), r_expr)) {
                (Ok(l), Ok(r)) => return Ok(l._eq(&r)),
                _ => {
                    let t = (expression_to_bool(ctx, Rc::clone(&env), l_expr), expression_to_bool(ctx, env, r_expr)); 
                    match flatten_tupple(t) {
                        Ok((l,r)) => return Ok(l._eq(&r)),
                        Err(why) => return Err(Error::Semantics(format!("Can't compare expressions {:?} and {:?} because they have different types", l_expr, r_expr)))
                    }}
            }
        }
        Expression::LT(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(l.lt(&r)),
                Err(why) => Err(why),
            }
        }
        Expression::GT(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(l.gt(&r)),
                Err(why) => Err(why),
            }
        }
        Expression::GEQ(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(l.ge(&r)),
                Err(why) => Err(why),
            }
        }
        Expression::LEQ(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(l.le(&r)),
                Err(why) => Err(why),
            }
        }
        Expression::Not(expr) => match expression_to_bool(ctx, env, expr) {
            Ok(expr) => return Ok(expr.not()),
            otherwise => return otherwise,
        },
        otherwise => {
            return Err(Error::Semantics(format!(
                "Expressions of the form {:?} should not be in a boolean expression",
                otherwise
            )));
        }
    }
}

//flatten result to ok, or the first error encountered
fn flatten_tupple<'ctx, A>(
    (l, r): (Result<A, Error>, Result<A, Error>),
) -> Result<(A, A), Error> {
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
) -> Result<Int<'ctx>, Error> {
    match expr {
        Expression::Minus(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            match flatten_tupple((l, r)) {
                Ok((l, r)) => return Ok(ast::Int::sub(&ctx, &[&l, &r])),
                Err(why) => return Err(why),
            }       
        }
        Expression::Identifier(id) => match env.get(id) {
            Some(var) => match var {
                Variable::Int(i) => {
                    //klopt dit, moet ik niet de reference naar de variable in de env passen?
                    return Ok(i.clone());
                }
                _ => {
                    return Err(Error::Semantics(format!("can't convert {:?} to an int", var)));
                }
            },
            None => {
                return Err(Error::Semantics(format!("Variable {} is undeclared", id)));
            }
        },
        Expression::Literal(Literal::Integer(n)) => { 
            return Ok(ast::Int::from_i64(ctx, *n))},
        otherwise => {
            return Err(Error::Semantics(format!(
                "Expressions of the form {:?} should not be in an integer expression",
                otherwise
            )));
        }
    };
}

#[cfg(test)]
mod tests {

    use super::*;

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
