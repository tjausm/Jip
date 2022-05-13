extern crate z3;
use std::convert::TryInto;
use std::ops::Add;
use std::time::Duration;
use z3::ast::*;
use z3::*;


use crate::see::{ExecutionPath}; 
use crate::ast::*;

fn validatePath(path: ExecutionPath) -> Result<(), &'static str> {
    /*
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    
    let mut formula = ast::Bool::from_bool(&ctx, true);

    
    for stmt in path.iter().rev() {
        match stmt {
            Declaration (ty, id) => panic!("");
            Assignment (lhs, rhs) => panic!("");
            Assert (expr) => panic!("");
            Assume (expr) => panic!("");
            otherwise => panic!("Statement of type {:?} should not be in an executionpath", otherwise);
        }
    }*/

    return Ok(())
}

mod tests {

    #[test]
    fn test_solving() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let x = ast::Int::new_const(&ctx, "x");
        let y = ast::Int::new_const(&ctx, "y");
    
        let solver = Solver::new(&ctx);
        solver.assert(&x.gt(&y));
        assert_eq!(solver.check(), SatResult::Sat);
    }
}