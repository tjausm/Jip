#[macro_use]
extern crate lalrpop_util;

use std::io;

mod ast;

lalrpop_mod!(pub parser); // synthesized by LALRPOP

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
        
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
    fn faulty_input(){
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
        assert!(parser::StatementsParser::new().parse("if (x := 1) x := 1; else x := 2;").is_err());
    }

}

fn main() {

    println!("Welcome to Jip v0.1");
    loop{
        let mut input = String::new();

        println!("\nPlease input a string:");
        io::stdin().read_line(&mut input);
    
        match parser::StatementsParser::new().parse(&input){
            Ok(_) => println!("Concrete syntax is correct"),
            Err(e) => println!("Error: {})", e)
        }
    }
}



