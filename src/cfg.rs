lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use petgraph::graph::{Graph, Node};
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
enum CfgNode {
    Branch,
    Statement(Statement),
    End
} 

type CFGp = Graph<CfgNode, ()>;

// we update the cfg and return the begin and endpoint of this particular stmt in the graph
fn stmt_to_cfgp(
    stmt: Statement,
    curr_cfg: Option<CFGp>,
    starting_node: Option<Node<Statement>>,
    ennding_node: Option<Node<Statement>>,
) -> (Node<Statement>, Node<Statement>, CFGp) {
    return panic!("fuck!");
}

// we update the cfg and return the begin and endpoint of this particular set of statements in the graph
fn stmts_to_cfgp(
    stmts: Statements,
    curr_cfg: Option<CFGp>,
    starting_node: Option<Node<Statement>>,
    ennding_node: Option<Node<Statement>>,
) -> (Node<Statement>, Node<Statement>, CFGp) {
    let mut cfg = curr_cfg.unwrap_or(Graph::<CfgNode, ()>::new());

    match stmts {
        Statements::Cons(stmt, stmts) => match stmt {
            Statement::Ite((cond, s1, s2)) => {
                // endpoint for cfg generated from branches is
                // cfg generated from stmts following ite,
                //let (next_begin, _, cfg) = stmts_to_cfgp(stmts, Some(cfg));
                return panic!("");
            }
            Statement::While((cond, body)) => {
                return panic!("");
            }
            other => {
                return panic!("");
            }
        },
        Statements::Nil => return panic!(""),
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
    lalrpop_mod!(pub parser);

    fn parse_stmt(i: &str) -> CfgNode {
        return CfgNode::Statement(parser::StatementParser::new().parse(i).unwrap());
    }

    fn build_test(input: &str, correct_cfg: CFGp) {
        let statements = parser::StatementsParser::new().parse(input).unwrap();
        let (_, _, generated_cfg) = stmts_to_cfgp(statements, None, None, None);
        assert_eq!(format!("{:?}", generated_cfg), format!("{:?}", correct_cfg));
    }

    #[test]
    fn empty() {
        build_test("", Graph::<CfgNode, ()>::new());
    }

    #[test]
    fn straight() {
        let mut cfg = Graph::<CfgNode, ()>::new();
        let a = cfg.add_node(CfgNode::Branch);
        let b = cfg.add_node(parse_stmt("int x; "));
        let c = cfg.add_node(parse_stmt("arbitraryId := true;"));
        let d = cfg.add_node(CfgNode::End);

        cfg.add_edge(a, b, ());
        cfg.add_edge(b, c, ());
        cfg.add_edge(c,d, ());

        build_test(
            "int x; arbitraryId := true;",
            cfg)
    }


    #[test]
    fn branch_and_block() {
        
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Branch);
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

        build_test(
            "if (true) {int x;} else {int y; } int z;",
            cfg
        );
    }
    fn while_loop() {
        
        let mut cfg = Graph::<CfgNode, ()>::new();
        let s = cfg.add_node(CfgNode::Branch);
        let a = cfg.add_node(parse_stmt("assume true; "));
        let b = cfg.add_node(parse_stmt("assume !true;"));
        let c = cfg.add_node(parse_stmt("int x;"));
        let d = cfg.add_node(CfgNode::End);

        cfg.add_edge(s, a, ());
        cfg.add_edge(a, c, ());
        cfg.add_edge(c, s, ());

        cfg.add_edge(s, b, ());

        cfg.add_edge(b, d, ());

        build_test(
            "while (true) int x;",
            cfg
        );
    }
}
