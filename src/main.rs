#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub calculator); // synthesized by LALRPOP

#[test]
fn calculator1() {
    assert!(calculator::ExprParser::new().parse("22").is_ok());
    assert!(calculator::ExprParser::new().parse("((((22))))").is_ok());
    assert!(calculator::ExprParser::new().parse("(22)").is_ok());
    assert!(calculator::ExprParser::new().parse("2+(1+1)").is_ok());
    //Wassert!(calculator::ExprParser::new().parse("2+((4+3))").is_ok());
    assert!(calculator::ExprParser::new().parse("((22)").is_err());
    //assert!(calculator::ExprParser::new().parse("((  22)").is_err());
}

fn main() {
    println!("Hello, world!");
}