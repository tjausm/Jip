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
    While(While)

}

pub type Declaration = (Nonvoidtype, Identifier);

pub type While = (Expression, Box<Statement>);

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

    //expression1
    Forall(Box<Expression>, Box<Expression>),
    Exists(Box<Expression>, Box<Expression>),

    //expression3
    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),

    //expression4
    EQ(Box<Expression>, Box<Expression>),
    NE(Box<Expression>, Box<Expression>),
    

    //Expression5
    LT(Box<Expression>, Box<Expression>),
    GT(Box<Expression>, Box<Expression>),
    GEQ(Box<Expression>, Box<Expression>),
    LEQ(Box<Expression>, Box<Expression>),

    //Expression6
    Plus(Box<Expression>, Box<Expression>),
    Minus(Box<Expression>, Box<Expression>),
    
    //Expression7
    Times(Box<Expression>, Box<Expression>),
    Divide(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),

    //Expression8
    Negative(Box<Expression>),
    Not(Box<Expression>),

    //expression9
    Identifier(Identifier),
    Literal(Literal),
}

#[derive(Debug, Clone)]
pub enum Literal {
    Boolean(bool),
    Integer(i64),
}

type Identifier = String;
