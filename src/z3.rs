extern crate z3;

use z3::ast::{Ast, Bool, Int};
use z3::*;

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::*;
use crate::see::ExecutionPath;

/*

declaration: either save in own environment or save it as z3 const
assignment: we check which type the lefthand side has and start parsing the rhs expression as z3 ast

do we let z3 crash or are we gonna keep track of types ourselves? (maybe we are forced by the type system)
if not do not keep track, since we will be implementing a static analyser anywar

TODO: make constants of error messages

*/

#[derive(Debug, Clone)]
enum Variable<'a> {
    Int(Int<'a>),
    Bool(Bool<'a>),
}


pub fn validate_path<'a>(path: ExecutionPath) -> Result<(), &'a str> {
    //init the 'accounting' z3 needs
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    //init formula representing our path & our variable hashmap
    let mut env: HashMap<&String, Variable> = build_env(&ctx, &path);
    let mut formula = ast::Bool::from_bool(&ctx, true);
    
    for stmt in path.iter().rev() {
        match stmt {
            Statement::Declaration((ty, id)) => (),
            Statement::Assignment((lhs, Rhs::Expr(rhs))) => {
                match lhs {
                    Lhs::Identifier(id) => {
                        let rc_env = Rc::new(&env);
                        match env.get(id) {
                            
                            // TODO: refactor this to avoid duplicate code on adding a type
                            // (tried this once but can't get the types right here without boxing and unboxing alot)
                            Some(Variable::Int(l_ast)) => {
                                let r_ast = expression_to_int(&ctx, Rc::clone(&rc_env), rhs);
                                let substitutions = &[(l_ast, &r_ast)];
                                formula.substitute(substitutions);
                            },
                            Some(Variable::Bool(l_ast)) => {
                                let r_ast = expression_to_bool(&ctx, Rc::clone(&rc_env), rhs);
                                let substitutions = &[(l_ast, &r_ast)];
                                formula.substitute(substitutions);
                            },
                            None => panic!("Variable {} is undeclared", id)
                        }
                    }
                }
                // todo: haal type uit environment
                // call the right expression parse function for the type
                // and substitute the ast with the resulting expression
            }
            Statement::Assert(expr) => {
                let rc_env = Rc::new(&env);
                let ast = expression_to_bool(&ctx, Rc::clone(&rc_env), expr);
                formula = Bool::and(&ctx, &[&ast, &formula])
            }
            Statement::Assume(expr) => {
                let rc_env = Rc::new(&env);
                let ast = expression_to_bool(&ctx, Rc::clone(&rc_env), expr);
                formula = Bool::implies(&ast, &formula)
            }
            otherwise => {
                panic!(
                    "Statements of the form {:?} should not be in an executionpath",
                    otherwise
                );
            }
        }
    }

    let solver = Solver::new(&ctx);
    solver.assert(&formula);
    match solver.check() {
        SatResult::Sat => return Ok(()),
        _ => return Err("Not satisfiable")
    }

}

//optimise idea: pass program and build env once
fn build_env<'ctx, 'p>(ctx: &'ctx Context, path : &'p ExecutionPath) -> HashMap<&'p String, Variable<'ctx>> {
    let mut env : HashMap<&'p String, Variable<'ctx>> = HashMap::new();
    for stmt in path {
        match stmt {
            Statement::Declaration((ty, id)) => {
                match ty {
                    Nonvoidtype::Primitivetype(Primitivetype::Int) => {
                        env.insert(id, Variable::Int(Int::new_const(&ctx, id.clone())));
                    } 
                    Nonvoidtype::Primitivetype(Primitivetype::Bool) => {
                        env.insert(id, Variable::Bool(Bool::new_const(&ctx, id.clone())));
                    } 
                }
            }
            _ => ()
        }
    }
    return env;
}

fn expression_to_bool<'ctx>(
    ctx: &'ctx Context,
    env: Rc<&HashMap<&String, Variable<'ctx>>>,
    expr: &Expression,
) -> Bool<'ctx> {
    match expr {
        Expression::GEQ(l_expr, r_expr) => {
            let l = expression_to_int(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_int(ctx, env, r_expr);
            return l.ge(&r);
        }
        Expression::And(l_expr, r_expr) => {
            let l = expression_to_bool(ctx, Rc::clone(&env), l_expr);
            let r = expression_to_bool(ctx, env, r_expr);
            return Bool::and(ctx, &[&l, &r]);
        }
        Expression::Not(expr) => {
            return expression_to_bool(ctx, env, expr).not();
        }
        otherwise => {
            panic!(
                "Expressions of the form {:?} should not be in a boolean expression",
                otherwise
            );
        }
    }
}

fn expression_to_int<'ctx>(
    ctx: &'ctx Context,
    env: Rc<&HashMap<&String, Variable<'ctx>>>,
    expr: &Expression,
) -> Int<'ctx> {
    match expr {
        Expression::Identifier(id) => match env.get(id) {
            Some(var) => match var {
                Variable::Int(i) => {
                    return i.clone();
                }
                _ => {
                    panic!("can't convert {:?} to an int", var);
                }
            },
            None => {
                panic!("Variable {} is undeclared", id);
            }
        },

        otherwise => {
            panic!(
                "Expressions of the form {:?} should not be in a integer expression",
                otherwise
            );
        }
    };
}


#[cfg(test)]
mod tests {

    use super::*;

    lalrpop_mod!(pub parser);
    use crate::cfg::stmts_to_cfg;
    use crate::see::{generate_execution_paths, tests};

    fn build_test(program: &str, correct: bool) {
        let stmts = parser::StatementsParser::new().parse(program).unwrap();
        let cfg = stmts_to_cfg(stmts, None);
        let paths = generate_execution_paths(cfg);

        for path in paths {
            assert_eq!(validate_path(path).is_ok(), correct);
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
    fn test_substitution() {
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
