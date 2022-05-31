use crate::cfg::stmts_to_cfg;
use crate::paths::generate_execution_paths;
use crate::z3::verify_path;
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use std::fs;
use std::path::Path;

const PROG_CORRECT : &str = "Program is correct";

pub fn verify_file_and_print(program: &Path) -> String {
    match verify_file(program) {
        Err(why) => format!("{}", why),
        Ok(_) => PROG_CORRECT.to_string()
    }
}

pub fn verify_file(program: &Path) -> Result<(), String>{
    match fs::read_to_string(program) {
        Err(why) => Err(format!("{}", why)),
        Ok(content) => verify_string(&content) 
    }
} 

pub fn verify_string_and_print(program: &str) -> String {
    match verify_string(program) {
        Err(err) => err,
        Ok(_) => PROG_CORRECT.to_string(),
    }
}

pub fn verify_string(program: &str) -> Result<(), String> {
    match parser::StatementsParser::new().parse(program) {
        Err(pe) => return Err(format!("{}", pe)),
        Ok(stmts) => {
            let cfg = stmts_to_cfg(stmts, None);
            for path in generate_execution_paths(cfg) {
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
