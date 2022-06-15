#[derive(Debug)]
pub enum Error {
    Syntax(String),
    Semantics(String),
    Verification(String),
    Other(String),
}