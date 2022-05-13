#[macro_use]
extern crate lalrpop_util;


use std::io;

mod ast;
mod cfg;
mod see;
mod z3;

lalrpop_mod!(pub parser); // synthesized by LALRPOP

fn main() {

    println!("Welcome to Jip v0.1");
    
    loop{
        let mut input = String::new();

        println!("\nPlease input a string:");
        io::stdin().read_line(&mut input);
    
        match parser::StatementsParser::new().parse(&input){
            Ok(ast) => println!("Concrete syntax is correct, parse result: \n{:?}", ast),
            Err(e) => println!("Error: {})", e)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok()); 
    }
    #[test]
    fn expressions() {
        assert!(parser::StatementsParser::new().parse("x := 2 < 1;").is_ok()); 
        assert!(parser::StatementsParser::new().parse("x := !true && false;").is_ok()); 
        assert!(parser::StatementsParser::new().parse("x := -1;").is_ok()); 
    }
    #[test]
    fn declaration() {     
        assert!(parser::StatementsParser::new().parse("int x;").is_ok());
    
    }
    #[test]
    fn statements() {
        assert!(parser::StatementsParser::new().parse("int x; x := 2; if(true)x := 1; else x := 2;").is_ok());
    }
    #[test]
    fn block() {
        assert!(parser::StatementsParser::new().parse("if(true){x := 1; bool z;} else {y := 2; x := 2;}").is_ok());
        
    }
    #[test]
    fn assume(){
        assert!(parser::StatementsParser::new().parse("assume true;").is_ok());  
    }
    #[test]
    fn assert(){
        assert!(parser::StatementsParser::new().parse("assert true;").is_ok());  
    }

    #[test]
    fn faulty_input(){
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
        assert!(parser::StatementsParser::new().parse("if (x := 1) x := 1; else x := 2;").is_err());
    }

}

