//naming convention: 
// - syntactical labels are taken as is from Stefan's thesis
// - each syntactical label's first symbol is transformed to uppercase (program -> Program)
// - labels with only 1 ´option´ are type aliases, , 1 < options are enums

pub enum Statements {
    Cons(Statement, Box<Statements>),
    Nil
}

pub enum Statement {
    Declaration(Declaration),
    Assignment(Assignment),
    Ite(Box<Ite>)
}

pub type Declaration = (Nonvoidtype, Identifier);

pub enum Nonvoidtype {
    Primitivetype
}

pub enum Primitivetype {
    Int,
    Bool
}


pub type Assignment = (Lhs, Rhs);

pub enum Lhs {
    Identifier(String),    
}

pub enum Rhs {
    Expr(Expr9)
}




pub type Ite = (Expr9, Statement, Statement);


pub enum Expr9 {
    Identifier(Identifier),
    Literal(Literal)
}

pub enum Literal{
    Boolean(bool),
    Integer(i32)
}

type Identifier = String;