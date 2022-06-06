lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use petgraph::graph::{Graph, Node, NodeIndex};
use std::rc::Rc;

//TODO: do benchmark to check whether references work
// e.g. whether more edges don't increase graph size

#[derive(Debug)]
pub enum CFG {
    Branch {
        condition: Expression,
        if_condition: Rc<CFG>,
        if_not_condition: Rc<CFG>,
    },
    Straight {
        statement: Statement,
        next: Rc<CFG>,
    },
    End,
}
#[derive(Debug)]
pub enum CfgNode {
    Start,
    Statement(Statement),
    End,
}

type CFGp = Graph<CfgNode, ()>;

// fuctions as the set-up for the recursive stmt_to_cfg and stmts_to_cfg functions
pub fn generate_cfg(stmts: Statements) -> CFGp {
    let mut cfg = Graph::<CfgNode, ()>::new();
    let start_node = cfg.add_node(CfgNode::Start);
    let end_node = cfg.add_node(CfgNode::End);
    let (_, _, cfg) = stmts_to_cfgp(stmts, cfg, vec![start_node], Some(end_node));
    return cfg;
}

// recursively unpacks Statement and returns start and end of cfg and cfg itself
fn stmt_to_cfgp(
    stmt: Statement,
    mut cfg: CFGp,
    start_node: NodeIndex,
    end_node: Option<NodeIndex>,
) -> (Vec<NodeIndex>, NodeIndex, CFGp) {
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

// recursively unpacks Statements and returns start of cfg and the cfg itself
fn stmts_to_cfgp(
    stmts: Statements,
    mut cfg: CFGp,
    start_nodes: Vec<NodeIndex>,
    ending_node: Option<NodeIndex>,
) -> (Vec<NodeIndex>, NodeIndex, CFGp) {
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
                let assume = CfgNode::Statement(Statement::Assume(cond.clone()));
                let assume_not =
                    CfgNode::Statement(Statement::Assume(Expression::Not(Box::new(cond))));
                let assume_node = cfg.add_node(assume);
                let assume_not_node = cfg.add_node(assume_not);
                // add edges from start node to assume and assume_not
                for start_node in start_nodes {
                    cfg.add_edge(start_node, assume_node, ());
                    cfg.add_edge(start_node, assume_not_node, ());
                }
                // calculate cfg for body of while and cfg for the rest of the stmts
                let (_, body_ending, cfg) = stmt_to_cfgp(*body, cfg, assume_node, None);                
                let (start_remainder, end_remainder, mut cfg) =
                    stmts_to_cfgp(*stmts, cfg, vec![assume_not_node], ending_node);
                // add edges from end of while to begin and edge to rest of stmts
                cfg.add_edge(body_ending, assume_node, ());
                for start_node in start_remainder {
                    cfg.add_edge(body_ending, start_node, ());
                }
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

// both to_cfg functions create a graph, or a subgraph pointing to the supplied node
fn stmt_to_cfg(stmt: Statement, next: Option<Rc<CFG>>) -> Rc<CFG> {
    let endpoint = next.unwrap_or(Rc::new(CFG::End));
    match stmt {
        Statement::Block(stmts) => return stmts_to_cfg(*stmts, Some(endpoint)),
        other => {
            return Rc::new(CFG::Straight {
                statement: other,
                next: endpoint,
            })
        }
    }
}

pub fn stmts_to_cfg(stmts: Statements, next: Option<Rc<CFG>>) -> Rc<CFG> {
    // let endpoint(s) point to either the next arg or CFG::End
    let endpoint = next.unwrap_or(Rc::new(CFG::End));
    match stmts {
        Statements::Cons(stmt, stmts) => match stmt {
            Statement::Ite((cond, s1, s2)) => {
                // endpoint for cfg generated from branches is
                // cfg generated from stmts following ite,
                let next = Rc::new(stmts_to_cfg(*stmts, Some(endpoint)));
                return Rc::new(CFG::Branch {
                    condition: cond,
                    if_condition: stmt_to_cfg(*s1, Some(Rc::clone(&next))),
                    if_not_condition: stmt_to_cfg(*s2, Some(Rc::clone(&next))),
                });
            }
            other => {
                return Rc::new(CFG::Straight {
                    statement: other,
                    next: stmts_to_cfg(*stmts, Some(endpoint)),
                })
            }
        },
        Statements::Nil => return endpoint,
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

    fn build_test(input: &str, correct_cfg: CFGp) {
        let stmts = parser::StatementsParser::new().parse(input).unwrap();
        let generated_cfg = generate_cfg(stmts);
        //either pass unit test or print the 2 cfg's
        if (!is_isomorphic(&generated_cfg, &correct_cfg)) { assert_eq!(format!("{:?}", generated_cfg), format!("{:?}", correct_cfg))}
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
        let d = cfg.add_node(CfgNode::End);

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, a, ());
        cfg.add_edge(c, b, ());
        

        cfg.add_edge(s, b, ());

        cfg.add_edge(b, d, ());

        build_test("while (true) int x;", cfg);
    }
}
