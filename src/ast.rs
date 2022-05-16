//naming convention:
// - syntactical labels are taken as is from Stefan's thesis
// - each syntactical label's first symbol is transformed to uppercase (program -> Program)
// - labels with only 1 ´option´ are type aliases, , 1 < options are enums

//TODO: change identifier in &str (unfuck whole lifetime business)

#[derive(Debug, Clone)]
pub enum Statements {
    Cons(Statement, Box<Statements>),
    Nil,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Declaration(Declaration),
    Assignment(Assignment),
    Ite(Ite),
    Block(Box<Statements>),
    Assert(Expression),
    Assume(Expression),
}

pub type Declaration = (Nonvoidtype, Identifier);

#[derive(Debug, Clone)]
pub enum Nonvoidtype {
    Primitivetype(Primitivetype),
}

#[derive(Debug, Clone)]
pub enum Primitivetype {
    Int,
    Bool,
}

pub type Assignment = (Lhs, Rhs);

#[derive(Debug, Clone)]
pub enum Lhs {
    Identifier(String),
}

#[derive(Debug, Clone)]
pub enum Rhs {
    Expr(Expression),
}

pub type Ite = (Expression, Box<Statement>, Box<Statement>);

//Todo: change to Expr1 when implemented

#[derive(Debug, Clone)]
pub enum Expression {

    //expression3
    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),

    //Box<Expression>
    LT(Box<Expression>, Box<Expression>),
    GT(Box<Expression>, Box<Expression>),
    GEQ(Box<Expression>, Box<Expression>),
    LEQ(Box<Expression>, Box<Expression>),

    //Expression
    Minus(Box<Expression>),
    Not(Box<Expression>),
    Expr9(Box<Expression>),

    //expression9
    Identifier(Identifier),
    Literal(Literal),
}

#[derive(Debug, Clone)]
pub enum Literal {
    Boolean(bool),
    Integer(i32),
}

type Identifier = String;
