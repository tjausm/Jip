lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use std::rc::Rc;

// TODO: rebuild CFG as graph instead of a tree

#[derive(Debug)]
pub enum CFG {
    Branch { left: Rc<CFG>, right: Rc<CFG> },
    Straight { statement: Statement, next: Rc<CFG> },
    End,
}

type Branch = (CFG, CFG);

type Straight = (Statement, CFG);

fn to_cfg(stmts: Statements) -> CFG {
    match stmts {
        Statements::Cons(stmt, stmts) => match stmt {
            Statement::Ite((cond, s1, s2)) => {
                // generate the endpoint for both statements
                let next = Rc::new(to_cfg(*stmts));

                // 2 branches where both Straight's point to next
                return CFG::Branch {
                    left: Rc::new(CFG::Straight {
                        statement: *s1,
                        next: Rc::clone(&next),
                    }),
                    right: Rc::new(CFG::Straight {
                        statement: *s2,
                        next: Rc::clone(&next),
                    }),
                };
            }
            other => {
                return CFG::Straight {
                    statement: other,
                    next: Rc::new(to_cfg(*stmts)),
                }
            }
        },
        Statements::Nil => return CFG::End,
    }
}

mod tests {

    use super::*;

    fn build_test(input: &str, correct_cfg: Rc<CFG>) {
        let statements = parser::StatementsParser::new().parse(input).unwrap();
        assert_eq!(
            format!("{:?}", to_cfg(statements)),
            format!("{:?}", correct_cfg)
        );
    }

    //TODO (maybe): deze functies uitbreiden om makkelijker CFG's te maken

    // shorthands to build statements and CFG's
    fn declaration(t: Primitivetype, id: &str) -> Statement {
        return Statement::Declaration((
            Nonvoidtype::Primitivetype(Primitivetype::Int),
            String::from(id),
        ));
    }
    fn straight_declaration(next: Rc<CFG>) -> Rc<CFG> {
        return Rc::new(CFG::Straight {
            statement: declaration(Primitivetype::Int, "x"),
            next: next,
        });
    }
    fn expression() -> Expr9 {
        return Expr9::Literal(Literal::Boolean(true));
    }

    fn branch_ite(next: Rc<CFG>) -> Rc<CFG> {
        return Rc::new(CFG::Branch {
            left: straight_declaration(Rc::clone(&next)),
            right: straight_declaration(Rc::clone(&next)),
        });
    }

    #[test]
    fn empty() {
        build_test("", Rc::new(CFG::End));
    }

    #[test]
    fn straight() {
        build_test("int x;", straight_declaration(Rc::new(CFG::End)))
    }

    #[test]
    fn branch() {
        build_test(
            "if (true) int x; else int x;",
            branch_ite(Rc::new(CFG::End)),
        )
    }

    #[test]
    fn everything() {
        build_test(
            "int x;if (true) int x; else int x; int x;",
            straight_declaration(branch_ite(straight_declaration(Rc::new(CFG::End)))),
        )
    }
}
