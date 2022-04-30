#[macro_use]
extern crate lalrpop_util;

mod tupple;

lalrpop_mod!(pub calculator); // synthesized by LALRPOP

#[test]
fn calculator1() {
    assert!(calculator::ExprParser::new().parse("(2,2)").is_ok());
}

fn main() {
    println!("Hello, world!");
}