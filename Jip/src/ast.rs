//naming convention:
// - syntactical labels are taken as is from Stefan's thesis
// - each syntactical label's first symbol is transformed to uppercase (program -> Program)
// - labels with only 1 ´option´ are type aliases, , 1 < options are enums

#[derive(Debug)]
pub enum Statements {
    Cons(Statement, Box<Statements>),
    Nil,
}

#[derive(Debug)]
pub enum Statement {
    Declaration(Declaration),
    Assignment(Assignment),
    Ite(Ite),
    Block(Box<Statements>),
    Assert(Verificationexpression),
    Assume(Verificationexpression),
}

pub type Declaration = (Nonvoidtype, Identifier);

#[derive(Debug)]
pub enum Nonvoidtype {
    Primitivetype(Primitivetype),
}

#[derive(Debug)]
pub enum Primitivetype {
    Int,
    Bool,
}

pub type Assignment = (Lhs, Rhs);

#[derive(Debug)]
pub enum Lhs {
    Identifier(String),
}

#[derive(Debug)]
pub enum Rhs {
    Expr(Expr9),
}

pub type Ite = (Expr9, Box<Statement>, Box<Statement>);


//Todo: change to Expr1 when implemented
pub type Verificationexpression = Expr9;

#[derive(Debug)]
pub enum Expr9 {
    Identifier(Identifier),
    Literal(Literal),
}

#[derive(Debug)]
pub enum Literal {
    Boolean(bool),
    Integer(i32),
}

type Identifier = String;
