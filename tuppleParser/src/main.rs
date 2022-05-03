#[macro_use]
extern crate lalrpop_util;

mod tupple;

lalrpop_mod!(pub calculator); // synthesized by LALRPOP

#[test]
fn calculator1() {
    //test all data types, white spaces and nested tuples
    assert!(calculator::ExprParser::new().parse(r#"(2 ,( false, "string") )"#).is_ok());
    assert!(calculator::ExprParser::new().parse("(2,(,(4,)))").is_err());

}

fn main() {
    println!("Hello, world!");
}