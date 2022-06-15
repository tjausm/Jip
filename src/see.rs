use crate::ast::Program;
use crate::cfg::{generate_cfg, generate_dot_cfg};
use crate::errors::Error;
use crate::paths::{generate_execution_paths, Depth};
use crate::z3::{print_formula, verify_path};
lalrpop_mod!(pub parser); // synthesized by LALRPOP

use std::fs;

const PROG_CORRECT: &str = "Program is correct";

// 0 = validated program, 1 = validation error, 2 = all other errors
pub type ExitCode = i32;

fn print_result(r: Result<(), Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Syntax(why)) => (2, format!("Syntax error: {}", why)),
        Err(Error::Semantics(why)) => (2, format!("Semantics error: {}", why)),
        Err(Error::Other(why)) => (2, format!("{}", why)),
        Err(Error::Verification(why)) => (1, format!("{}", why)),
        Ok(_) => (0, PROG_CORRECT.to_string()),
    }
}

pub fn load_program(program: String) -> Result<String, (ExitCode, String)> {
    match fs::read_to_string(program) {
        Err(why) => Err(print_result(Err(Error::Other(format!("{}", why))))),
        Ok(content) => Ok(content),
    }
}

pub fn print_cfg(program: &str) -> (ExitCode, String) {
    match parse_program(program) {
        Err(parse_err) => print_result(Err(parse_err)),
        Ok(stmts) => match generate_dot_cfg(stmts) {
            Ok(cfg) => (0, cfg),
            Err(sem_err) => print_result(Err(sem_err)),
        },
    }
}

pub fn print_formulas(program: &str, d: Depth) -> (ExitCode, String) {
    match parse_program(program) {
        Err(parse_err) => return print_result(Err(parse_err)),
        Ok(stmts) => {
            match generate_cfg(stmts) {
                Ok((start_node, cfg)) => {
                    for path in generate_execution_paths(start_node, cfg, d) {
                        match print_formula(path) {
                            Ok(formula) => println!("{}", formula),
                            Err(err) =>  return print_result(Err(err)),
                        }
                    }
                },
                Err(sem_err) => return print_result(Err(sem_err))
            }

        }
    }
    //if all formulas are printed we end with success exitcode and empty msg
    return (0, "".to_string());
}

pub fn print_verification(program: &str, d: Depth) -> (ExitCode, String) {
    return print_result(verify(program, d));
}

fn verify(program: &str, d: Depth) -> Result<(), Error> {
    match parse_program(program) {
        Err(parse_error) => return Err(parse_error),
        Ok(prog) => match generate_cfg(prog) {
            Ok((start_node, cfg)) => {
                for path in generate_execution_paths(start_node, cfg, d) {
                    match verify_path(path) {
                        Ok(_) => continue,
                        Err(verification_error) => return Err(verification_error),
                    }
                }
            }
            Err(semantics_error) => return Err(semantics_error),
        },
    }
    return Ok(());
}

fn parse_program(program: &str) -> Result<Program, Error> {
    match parser::ProgramParser::new().parse(program) {
        Err(parse_err) => return Err(Error::Syntax(format!("{}", parse_err))),
        Ok(program) => return Ok(program),
    }
}

// put parser test here since parser mod is auto-generated
#[cfg(test)]
mod tests {

    lalrpop_mod!(pub parser);

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
        assert!(parser::StatementsParser::new()
            .parse("divisible := (i * k == x);")
            .is_ok());
        assert!(parser::StatementsParser::new().parse("int x := 2;").is_ok());
    }

    #[test]
    fn expressions() {
        assert!(parser::VerificationExpressionParser::new()
            .parse("2 < 1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("!true && false")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("-1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("y && z || a")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 == 2 != 3")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 + 2 - 3 / 4 % 5 * 6")
            .is_ok());
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
    fn Program() {
        assert!(parser::ProgramParser::new()
            .parse("class Main {static void main(){int x := 2;}}")
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
