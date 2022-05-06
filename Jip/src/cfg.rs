

lalrpop_mod!(pub parser); // synthesized by LALRPOP

use crate::ast::*;
use crate::parser::Token;

// TODO: rebuild CFG as graph instead of a tree

#[derive(Debug)]
pub enum CFG {
    Branch(Box<Branch>),
    Straight(Box<Straight>),
    Leaf
}

type Branch = (CFG, CFG);


type Straight = (Statement, CFG);


fn to_cfg(statements : Statements) -> CFG {
    
    
    return CFG::Leaf;
}

mod tests {

    use super::*;

    fn build_test(input : &str, correct_cfg : CFG) {
        let statements = parser::StatementsParser::new().parse(input).unwrap();
        assert_eq!(format!("{:?}", to_cfg(statements)), format!("{:?}", correct_cfg));
    }

    fn declaration() -> Statement { return Statement::Declaration((Nonvoidtype::Primitivetype(Primitivetype::Int), String::from("x")));} 
    fn straight_declaration() -> CFG {return CFG::Straight(Box::new((declaration(), CFG::Leaf)))}
    fn expression() -> Expr9 {return Expr9::Literal(Literal::Boolean(true))}
    fn ite() -> Statement { return Statement::Ite(Box::new((expression(), declaration(), declaration())))}
    fn branch_ite() -> CFG {return CFG::Branch(Box::new((straight_declaration(),straight_declaration())))}

    #[test]
    fn empty() {
        build_test("", CFG::Leaf);
    }

    #[test]
    fn straight() {
        build_test("int x;", straight_declaration())
    }

    #[test]
    fn branch() {
        build_test("if (true) int x; else int x;",branch_ite() )
    }

    #[test]
    fn everything() {
        build_test("int x;if (true) int x; else int x;", CFG::Straight(Box::new((declaration(), branch_ite()))) )
    }
}