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
            Statement::Assignment ((lhs, rhs)) => {panic!("");}
            Statement::Assert (expr) => {panic!("");}
            Statement::Assume (expr) => {panic!("");}
            otherwise => {panic!("Statements of the form {:?} should not be in an executionpath", otherwise);}
        }
    }

    return Ok(())
}

fn expression_to_ast(expr: Expression) -> () {
    return ();
}

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