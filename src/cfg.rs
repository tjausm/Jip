lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use petgraph::graph::{Graph, NodeIndex};
use petgraph::dot::Dot; 

#[derive(Debug)]
pub enum CfgNode {
    Start,
    Statement(Statement),
    End,
}

pub type CFG = Graph<CfgNode, ()>;

// generates cfg in vizualizable Dot format(visualizable at http://viz-js.com/)
pub fn generate_dot_cfg(stmts: Statements) -> String{
    let (_,cfg) = generate_cfg(stmts);
    return format!("{:?}", Dot::new(&cfg));
}

// fuctions as the set-up for the recursive  stmts_to_cfg function
// returns cfg, and the start_node for search algorithms
pub fn generate_cfg(stmts: Statements) -> (NodeIndex, CFG) {
    let mut cfg = Graph::<CfgNode, ()>::new();
    let start_node = cfg.add_node(CfgNode::Start);
    let end_node = cfg.add_node(CfgNode::End);
    let (_, _, cfg) = stmts_to_cfgp(stmts, cfg, vec![start_node], Some(end_node));
    return (start_node, cfg);
}

// recursively unpacks Statement and returns start and end of cfg and cfg itself
fn stmt_to_cfgp(
    stmt: Statement,
    mut cfg: CFG,
    start_node: NodeIndex,
    end_node: Option<NodeIndex>,
) -> (Vec<NodeIndex>, NodeIndex, CFG) {
    match stmt {
        Statement::Block(stmts) => return stmts_to_cfgp(*stmts, cfg, vec![start_node], end_node),
        other => {
            let stmt_node = cfg.add_node(CfgNode::Statement(other));
            cfg.add_edge(start_node, stmt_node, ());
            match end_node {
                Some(end_node) => {
                    cfg.add_edge(stmt_node, end_node, ());
                    return (vec![start_node], end_node, cfg);
                }
                None => return (vec![start_node], stmt_node, cfg),
            }
        }
    }
}

// recursively unpacks Statements and returns start, end and cfg itself
// adds edges from all passed start nodes to first node it generates from stmts
// and adds edges from the last nodes it generates to the ending node if it is specified
fn stmts_to_cfgp(
    stmts: Statements,
    mut cfg: CFG,
    start_nodes: Vec<NodeIndex>,
    ending_node: Option<NodeIndex>,
) -> (Vec<NodeIndex>, NodeIndex, CFG) {
    match stmts {
        Statements::Cons(stmt, stmts) => match stmt {
            Statement::Ite((cond, s1, s2)) => {
                // add condition as assume and assume_not to the cfg
                let assume = CfgNode::Statement(Statement::Assume(cond.clone()));
                let assume_not =
                    CfgNode::Statement(Statement::Assume(Expression::Not(Box::new(cond))));
                let assume_node = cfg.add_node(assume);
                let assume_not_node = cfg.add_node(assume_not);
                //iterate over all starting nodes to lay edges
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, ());
                    cfg.add_edge(start_node, assume_not_node, ());
                }

                // add the if and else branch to the cfg
                let (_, if_ending, cfg) = stmt_to_cfgp(*s1, cfg, assume_node, None);
                let (_, else_ending, cfg) = stmt_to_cfgp(*s2, cfg, assume_not_node, None);
                return stmts_to_cfgp(*stmts, cfg, vec![if_ending, else_ending], ending_node);
            }
            Statement::While((cond, body)) => {
                // add condition as assume and assume_not to the cfg
                let assume_node = cfg.add_node(CfgNode::Statement(Statement::Assume(cond.clone())));
                let assume_not_node = cfg.add_node(CfgNode::Statement(Statement::Assume(
                    Expression::Not(Box::new(cond)),
                )));
                // add edges from start node to assume and assume_not
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, ());
                    cfg.add_edge(start_node, assume_not_node, ());
                }
                // calculate cfg for body of while and cfg for the remainder of the stmts
                let (_, body_ending, cfg) = stmt_to_cfgp(*body, cfg, assume_node, None);
                let (_, end_remainder, mut cfg) =
                    stmts_to_cfgp(*stmts, cfg, vec![assume_not_node], ending_node);
                // add edges from end of while body to begin and edge from while body to rest of stmts
                cfg.add_edge(body_ending, assume_node, ());
                cfg.add_edge(body_ending, assume_not_node, ());
                
                return (vec![assume_node, assume_not_node], end_remainder, cfg);
            }
            //add edge from start to stmt and recurse
            other => {
                let stmt_node = cfg.add_node(CfgNode::Statement(other));
                for start_node in start_nodes {
                    cfg.add_edge(start_node, stmt_node, ());
                }
                return stmts_to_cfgp(*stmts, cfg, vec![stmt_node], ending_node);
            }
        },
        Statements::Nil => match ending_node {
            Some(end_node) => {
                for start_node in &start_nodes {
                    cfg.add_edge(*start_node, end_node, ());
                }
                return (start_nodes, end_node, cfg);
            }
            None => return (start_nodes.clone(), start_nodes[0], cfg),
        },
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use petgraph::algo::is_isomorphic;

    lalrpop_mod!(pub parser);

    fn parse_stmt(i: &str) -> CfgNode {
        return CfgNode::Statement(parser::StatementParser::new().parse(i).unwrap());
    }

    fn build_test(input: &str, correct_cfg: CFG) {
        let stmts = parser::StatementsParser::new().parse(input).unwrap();
        let (_, generated_cfg) = generate_cfg(stmts);
        
        println!("Generated cfg: \n{:?}", Dot::new(&generated_cfg));
        println!("Correct cfg: \n{:?}", Dot::new(&correct_cfg));
        assert!(is_isomorphic(&generated_cfg, &correct_cfg));
    }

    #[test]
    fn empty() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Start);
        let e = cfg.add_node(CfgNode::End);
        cfg.add_edge(s, e, ());
        build_test("", cfg);
    }

    #[test]
    fn straight() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let a = cfg.add_node(CfgNode::Start);
        let b = cfg.add_node(parse_stmt("int x; "));
        let c = cfg.add_node(parse_stmt("arbitraryId := true;"));
        let d = cfg.add_node(CfgNode::End);

        cfg.add_edge(a, b, ());
        cfg.add_edge(b, c, ());
        cfg.add_edge(c, d, ());

        build_test("int x; arbitraryId := true;", cfg)
    }

    #[test]
    fn branch_and_block() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Start);
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(parse_stmt("int z;"));
        let f = cfg.add_node(CfgNode::End);

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, e, ());

        cfg.add_edge(s, b, ());
        cfg.add_edge(b, d, ());
        cfg.add_edge(d, e, ());

        cfg.add_edge(e, f, ());

        build_test("if (true) {int x;} else {int y; } int z;", cfg);
    }

    #[test]
    fn while_loop() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Start);
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(parse_stmt("int y;"));
        let e = cfg.add_node(CfgNode::End);

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, a, ());
        cfg.add_edge(c, b, ());

        cfg.add_edge(s, b, ());
        cfg.add_edge(b, d, ());
        cfg.add_edge(d, e, ());

        build_test("while (true) int x; int y;", cfg);
    }
}
