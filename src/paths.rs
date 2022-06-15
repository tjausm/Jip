use crate::ast::*;
use crate::cfg::{generate_cfg, CFG, CfgNode};

use petgraph::graph::{NodeIndex};
use petgraph::visit::{EdgeRef};

use std::collections::VecDeque;

pub type ExecutionPath = Vec<Statement>;
pub type Depth = i64;

//bf-search collecting all possible paths to the END node in the cfg
pub fn generate_execution_paths(start_node: NodeIndex, cfg: CFG, d: Depth) -> Vec<ExecutionPath> {
    let mut resulting_paths: Vec<ExecutionPath> = vec![];
    
    let mut q: VecDeque<(ExecutionPath, Depth, NodeIndex)> = VecDeque::new(); //queue![(vec![], cfg)];
    q.push_back((vec![], d, start_node));
    
    //println!("{:?}", Dot::new(&cfg));

    loop {

        match q.pop_front() {
            Some((_, 0, _)) => continue,
            Some ((mut path, d, node_index)) => {
                match &cfg[node_index] {
                    // enqueue all starting statements of program
                    CfgNode::Start => {
                        for edge in cfg.edges(node_index){
                            let next = edge.target();
                            q.push_back((path.clone(), d, next));
                        }
                    }
                    
                    //add statement to path
                    CfgNode::Statement(stmt) => {
                        path.push(stmt.clone());

                        for edge in cfg.edges(node_index){
                            
                            //let dedge = format!("{:?}", cfg[edge.target()]);

                            let next = edge.target();
                            q.push_back((path.clone(), d-1, next));
                        }
                    }
        
                    // if end node is reached path is pushed to result vec
                    CfgNode::End => resulting_paths.push(path),
                }
            }
            None => {break},
        }

    }

    return resulting_paths;
}

#[cfg(test)]
pub mod tests {
    use super::*;

    lalrpop_mod!(pub parser);

    fn parse_stmt(i: &str) -> Statement {
        return parser::StatementParser::new().parse(i).unwrap();
    }
    fn parse_expr(i: &str) -> Expression {
        return parser::Expression3Parser::new().parse(i).unwrap();
    }

    pub const MAX: &str = "class Main { static void main () { int x; int y; int z; if (x >= y) z := x; else z := y; assert z >= x && z >= y;}}";

    #[test]
    fn max_function() {
        // generate test data
        let stmts = parser::ProgramParser::new().parse(MAX).unwrap();
        let (start_node, cfg) = generate_cfg(stmts).unwrap();
        
        //generate correct data (in correct order, assume condition and then negation)
        fn gen_path(c: Statement, m: &str) -> ExecutionPath {
            return vec![parse_stmt("int x;"), parse_stmt("int y;"), parse_stmt("int z;"), c, parse_stmt(m), parse_stmt("assert z >= x && z >= y;")];
        }
        let correct_paths = vec![
            gen_path(
                //TODO: implement negation like in other path (when parentheses are implemented)
                Statement::Assume(Expression::Not(Box::new(parse_expr("x >= y")))),
                "z := y;",
            ),
            gen_path(parse_stmt("assume x >= y;"), "z := x;")

        ];
        
        assert_eq!(
            format!("{:?}", generate_execution_paths(start_node, cfg, 40)),
            format!("{:?}", correct_paths)
        );
    }
}
