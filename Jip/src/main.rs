#[macro_use]
extern crate lalrpop_util;

mod ast;

lalrpop_mod!(pub parser); // synthesized by LALRPOP

#[test]
fn calculator1() {
    //test all data types, white spaces and nested tuples
    assert!(parser::Expr9Parser::new().parse("42").is_ok());
    assert!(parser::Expr9Parser::new().parse("ident").is_ok());
    assert!(parser::Expr9Parser::new().parse("true").is_ok());
    assert!(parser::Expr9Parser::new().parse("9 true").is_err());
}

fn main() {
    println!("Hello, world!");
}