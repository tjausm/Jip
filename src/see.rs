use crate::cfg::generate_cfg;
use crate::paths::{generate_execution_paths, Depth};
use crate::z3::{Error, verify_path};
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use std::fs;
use std::path::Path;

const PROG_CORRECT : &str = "Program is correct";

// 0 = validated program, 1 = validation error, 2 = all other errors
pub type ExitCode = i32;

fn print_result(r: Result<(), Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Syntax(why)) => (2, format!("Syntax error: {}", why)),
        Err(Error::Semantics(why)) => (2, format!("Semantics error: {}", why)),
        Err(Error::Other(why)) => (2, format!("{}", why)),
        Err(Error::Verification(why)) => (1, format!("{}", why)),
        Ok(_) => (0, PROG_CORRECT.to_string())
    }
}

pub fn verify_file_and_print(program: &Path, d: Depth) -> (ExitCode, String) {
    return print_result(verify_file(program, d)); 
}

pub fn verify_file(program: &Path, d : Depth) -> Result<(), Error> {
    match fs::read_to_string(program) {
        Err(why) => Err(Error::Other(format!("{}", why))),
        Ok(content) => verify_string(&content, d) 
    }
} 

pub fn verify_string_and_print(program: &str, d: Depth) -> (ExitCode, String) {
    return print_result(verify_string(program, d));
}

pub fn verify_string(program: &str, d: Depth) -> Result<(), Error> {
    match parser::StatementsParser::new().parse(program) {
        Err(pe) => return Err(Error::Syntax(format!("{}", pe))),
        Ok(stmts) => {
            let (start_node, cfg) = generate_cfg(stmts);
            for path in generate_execution_paths(start_node, cfg, d) {
                match verify_path(path) {
                    Ok(_) => continue,
                    Err(err) => return Err(err),
                }
            }
        }
    }
    return Ok(());
}

// put parser test here since parser mod is auto-generated
#[cfg(test)]
mod tests {

    lalrpop_mod!(pub parser);

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
    }

    #[test]
    fn expressions() {
        assert!(parser::VerificationExpressionParser::new().parse("2 < 1").is_ok());
        assert!(parser::VerificationExpressionParser::new().parse("!true && false").is_ok());
        assert!(parser::VerificationExpressionParser::new().parse("-1").is_ok());
        assert!(parser::VerificationExpressionParser::new().parse("y && z || a").is_ok());
        assert!(parser::VerificationExpressionParser::new().parse("1 == 2 != 3").is_ok());
        assert!(parser::VerificationExpressionParser::new().parse("1 + 2 - 3 / 4 % 5 * 6").is_ok());
    }
    #[test]
    fn declaration() {
        assert!(parser::StatementsParser::new().parse("int x;").is_ok());
    }
    #[test]
    fn statements() {
        assert!(parser::StatementsParser::new()
            .parse("int x; x := 2; if(true)x := 1; else x := 2;")
            .is_ok());
    }
    #[test]
    fn block() {
        assert!(parser::StatementsParser::new()
            .parse("if(true){x := 1; bool z;} else {y := 2; x := 2;}")
            .is_ok());
    }
    #[test]
    fn assume() {
        assert!(parser::StatementsParser::new()
            .parse("assume true;")
            .is_ok());
    }
    #[test]
    fn assert() {
        assert!(parser::StatementsParser::new()
            .parse("assert true;")
            .is_ok());
    }
    #[test]
    fn while_loop() {
        assert!(parser::StatementsParser::new()
            .parse("while (1 < 2) x := y;")
            .is_ok());
    }

    #[test]
    fn faulty_input() {
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
        assert!(parser::StatementsParser::new()
            .parse("if (x := 1) x := 1; else x := 2;")
            .is_err());
    }
}
