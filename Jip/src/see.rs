extern crate queues;
use queues::*;

use crate::ast::*;
use crate::cfg::{stmts_to_cfg, CFG};
use std::rc::Rc;

pub type ExecutionPath = Vec<Statement>;

pub fn generate_execution_paths(cfg: Rc<CFG>) -> Vec<ExecutionPath> {
    let mut e_paths: Vec<ExecutionPath> = vec![];

    let mut q: Queue<(ExecutionPath, Rc<CFG>)> = queue![(vec![], cfg)];
    
    loop {

        match q.remove() {
            Ok ((mut path, node)) => {
                match &*node {
                    // simply add straights to path and enqueue again
                    CFG::Straight {
                        statement: stmt,
                        next: nxt,
                    } => {
                        path.push(stmt.clone());
                        q.add((path, Rc::clone(&nxt))).unwrap();
                    }
        
                    // for branch we add 2 new paths, one pre-fixed with 'assume cond', the other
                    // with the negation of the condition as assume
                    CFG::Branch {
                        condition: cond,
                        if_condition: s1,
                        if_not_condition: s2,
                    } => {
                        let mut if_path = path.clone();
                        if_path.push(Statement::Assume(cond.clone()));
        
                        let mut if_not_path = path.clone();
                        if_not_path.push(Statement::Assume(Expression::Not(Box::new(cond.clone()))));
        
                        q.add((if_path, Rc::clone(&s1))).unwrap();
                        q.add((if_not_path, Rc::clone(&s2))).unwrap();
                    }
        
                    // if end node is reached path is pushed to result vec
                    CFG::End => e_paths.push(path),
                }
            }
            Err(_) => {break},
        }

    }

    return e_paths;
}

#[cfg(test)]
mod tests {
    use super::*;

    lalrpop_mod!(pub parser);

    fn parse_stmt(i: &str) -> Statement {
        return parser::StatementParser::new().parse(i).unwrap();
    }
    fn parse_expr(i: &str) -> Expression {
        return parser::Expression3Parser::new().parse(i).unwrap();
    }

    const max_program: &str = "if (x >= y) z := x; else z := y; assert z >= x && z >= y;";

    #[test]
    fn max_function() {
        // generate test data
        let stmts = parser::StatementsParser::new().parse(max_program).unwrap();
        let cfg = stmts_to_cfg(stmts, None);
        
        //generate correct data (in correct order, assume condition and then negation)
        fn gen_path(c: Statement, m: &str) -> ExecutionPath {
            return vec![c, parse_stmt(m), parse_stmt("assert z >= x && z >= y;")];
        }
        let correct_paths = vec![
            gen_path(parse_stmt("assume x >= y;"), "z := x;"),
            gen_path(
                //TODO: implement negation like in other path (when parentheses are implemented)
                Statement::Assume(Expression::Not(Box::new(parse_expr("x >= y")))),
                "z := y;",
            ),
        ];
        
        assert_eq!(
            format!("{:?}", generate_execution_paths(cfg)),
            format!("{:?}", correct_paths)
        );
    }
}
