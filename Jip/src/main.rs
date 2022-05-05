#[macro_use]
extern crate lalrpop_util;

mod ast;

lalrpop_mod!(pub parser); // synthesized by LALRPOP

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
    }
    #[test]
    fn declaration() {     
        assert!(parser::StatementsParser::new().parse("if(true)x := 1; else x := 2;").is_ok());

    }
    #[test]
    fn statements() {
        assert!(parser::StatementsParser::new().parse("int x;").is_ok());
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2").is_err());
    }

    

}

fn main() {
    println!("Hello, world!");
}



