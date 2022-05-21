lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use std::rc::Rc;

//TODO: do benchmark to check whether references work
// e.g. whether more edges don't increase graph size

#[derive(Debug)]
pub enum CFG {
    Branch { condition: Expression, if_condition: Rc<CFG>, if_not_condition: Rc<CFG> },
    Straight { statement: Statement, next: Rc<CFG> },
    End,
}

// both to_cfg functions create a graph, or a subgraph pointing to the supplied node 
fn stmt_to_cfg(stmt: Statement, next : Option<Rc<CFG>>) -> Rc<CFG> {
    
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

pub fn stmts_to_cfg(stmts: Statements, next : Option<Rc<CFG>>) -> Rc<CFG> {
    
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
                    next: stmts_to_cfg(*stmts, Some(endpoint))
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

    fn parse_stmt(i: &str,) -> Statement {return parser::StatementParser::new().parse(i).unwrap()}
    fn parse_expr(i: &str,) -> Expression {return parser::Expression3Parser::new().parse(i).unwrap()}

    fn build_test(input: &str, correct_cfg: Rc<CFG>) {
        let statements = parser::StatementsParser::new().parse(input).unwrap();
        assert_eq!(
            format!("{:?}", stmts_to_cfg(statements, None)),
            format!("{:?}", correct_cfg)
        );
    }


    // pre-build CFG's, 
    // combine by passing each element as argument to the next, with CFG::End as inner-most arg

    // "int x; ..."
    fn straight_declaration(next: Rc<CFG>) -> Rc<CFG> {
        return Rc::new(CFG::Straight {
            statement: parse_stmt("int x;"),
            next: next,
        });
    }

    // "arbitraryId = true; ..."
    fn straight_assignment(next: Rc<CFG>) -> Rc<CFG> {
        return Rc::new(CFG::Straight {
            statement: parse_stmt("arbitraryId := true;"),
            next: next,
        });
    }

    // {int x; int otherName;} ...
    fn block_declaration(next: Rc<CFG>) -> Rc<CFG> {
        return Rc::new(CFG::Straight {
            statement: parse_stmt("int x;"),
            next: Rc::new(CFG::Straight {
                statement: parse_stmt("int otherName;"),
                next: next
            })
        })
    }


    // if (true) then int x; else int x; ...
    fn branch_ite(l_and_r: fn(Rc<CFG>) -> Rc<CFG>, next: Option<Rc<CFG>>) -> Rc<CFG> {

        let endpoint = next.unwrap_or(Rc::new(CFG::End));

        return Rc::new(CFG::Branch { condition: parse_expr("true"), if_condition: l_and_r(Rc::clone(&endpoint)), if_not_condition: l_and_r(endpoint) });
    }

    #[test]
    fn empty() {
        build_test("", Rc::new(CFG::End));
    }

    #[test]
    fn straight() {
        build_test("int x; arbitraryId := true;", straight_declaration(straight_assignment(Rc::new(CFG::End))))
    }

    #[test]
    fn branch() {
        build_test(
            "if (true) int x; else int x;",
            branch_ite(straight_declaration, None)
        )
        
    }
    #[test]
    fn block() {
        let next = straight_declaration(Rc::new(CFG::End));

        build_test("if (true) {int x; int otherName;} else {int x; int otherName;} int x;", 
        branch_ite(block_declaration, Some(next)));
    }
}
