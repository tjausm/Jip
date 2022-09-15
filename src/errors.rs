//! Contains types of errors that can propagate from our SEE
//! 

#[derive(Debug)]
pub enum Error {
    Syntax(String),
    Semantics(String),
    Verification(String),
    Other(String),
}