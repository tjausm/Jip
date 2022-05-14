extern crate z3;

use z3::ast::*;
use z3::*;

use std::collections::HashMap;

use crate::see::{ExecutionPath}; 
use crate::ast::*;

/*

declaration: either save in own environment or save it as z3 const
assignment: we check which type the lefthand side has and start parsing the rhs expression as z3 ast

do we let z3 crash or are we gonna keep track of types ourselves? (maybe we are forced by the type system)
if not do not keep track, since we will be implementing a static analyser anywar

*/


pub fn validate_path(path: ExecutionPath) -> Result<(), &'static str> {
    
    //init the 'accounting' z3 needs
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    //init formula representing our path & our variable hashmap
    let mut variables : HashMap<&str, Box<dyn Ast>> = HashMap::new();
    let mut formula = ast::Bool::from_bool(&ctx, true);

    for stmt in path.iter().rev() {
        match stmt {
            Statement::Declaration ((ty, id)) => {
                match ty {
                    Nonvoidtype::Primitivetype(Primitivetype::Int) => {variables.insert(id, Box::new(Int::new_const(&ctx, id.clone())));} // add generated var to dictionary
                    Nonvoidtype::Primitivetype(Primitivetype::Bool) => {variables.insert(id, Box::new(Int::new_const(&ctx, id.clone())));} //and figure out how to convert id to Symbol
                }
            }
            Statement::Assignment ((lhs, rhs)) => {
                // todo: substitute ast here
            }
            Statement::Assert (expr) => {
                let ast = expression_to_bool(&ctx, expr);
                formula = Bool::and(&ctx, &[&ast, &formula])
            }
            Statement::Assume (expr) => {       
                let ast = expression_to_bool(&ctx, expr);
                formula = Bool::implies(&ast, &formula)
            }
            otherwise => {panic!("Statements of the form {:?} should not be in an executionpath", otherwise);}
        }
    }

    return Ok(())
}


fn expression_to_bool<'ctx>(ctx: &'ctx Context, expr: &Expression) -> Bool<'ctx> {

    match expr {
        Expression::GEQ(l_expr, r_expr) => {
            let l = expression_to_int(ctx, l_expr);
            let r = expression_to_int(ctx, r_expr);
            return l.ge(&r);
        }
        Expression::And(l_expr, r_expr) => {
            let l = expression_to_bool(ctx, l_expr);
            let r = expression_to_bool(ctx, r_expr);
            return Bool::and(ctx, &[&l, &r])
        }
        Expression::Not(expr) => {
            return expression_to_bool(ctx, expr).not();
        }
        otherwise => {panic!("Expressions of the form {:?} should not be in a boolean expression", otherwise);}
    }
}

fn expression_to_int<'ctx>(ctx: &'ctx Context, expr: &Expression) -> Int<'ctx> {
    return Int::from_i64(ctx, 0);
}

mod tests {

    use super::*;

    lalrpop_mod!(pub parser);
    use crate::cfg::{stmts_to_cfg};
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
    fn max_program(){
        build_test(tests::MAX, true);
    }

    #[test]
    fn faulty_max_program(){
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