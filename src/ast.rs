use std::fmt;

use crate::shared::panic_with_diagnostics;
/*
use non_empty_vec::NonEmpty;

//naming convention:
// - syntactical labels are taken as is from Stefan's thesis
// - each syntactical label's first symbol is transformed to uppercase (program -> Program)
// - labels with only 1 ´option´ are type aliases, , 1 < options are enums
*/

#[derive(Clone)]
pub struct Program(pub Vec<Class>);

impl Program {
    pub fn get_class<'a>(&'a self, class_name: &str) -> &'a Class {
        match self.0.iter().find(|(id, _)| id == class_name) {
            Some(class) => return class,
            None => panic_with_diagnostics(&format!("Class {} doesn't exist", class_name), &()),
        }
    }

    pub fn get_methodcontent<'a>(
        &'a self,
        class_name: &Identifier,
        method_name: &Identifier,
    ) -> &'a Methodcontent {
        let class = self.get_class(class_name);

        for member in class.1.iter() {
            match member {
                Member::Method(method) => match method {
                    Method::Static(content @ (_, id, _, _, _)) => {
                        if id == method_name {
                            return content;
                        }
                    }
                    Method::Nonstatic(content @ (_, id, _, _, _)) => {
                        if id == method_name {
                            return content;
                        }
                    }
                },
                _ => (),
            }
        }
        panic_with_diagnostics(
            &format!("Static method {}.{} doesn't exist", class.0, method_name),
            &(),
        );
    }

    pub fn get_constructor<'a>(&'a self, class_name: &str) -> &'a Constructor {
        let class = self.get_class(class_name);

        for m in class.1.iter() {
            match m {
                Member::Constructor(c) => return c,
                _ => continue,
            }
        }
        panic_with_diagnostics(
            &format!("Class {} does not have a constructor", class_name),
            &(),
        );
    }
}

pub type Class = (Identifier, Members);

pub type Members = Vec<Member>;

#[derive(Clone, Debug)]
pub enum Member {
    Constructor(Constructor),
    Method(Method),
    Field(Field),
}

pub type Constructor = (Identifier, Parameters, Specifications, Statements);

#[derive(Clone, Debug)]
pub enum Method {
    Static(Methodcontent),
    Nonstatic(Methodcontent),
}

//TODO: add args hier
pub type Methodcontent = (Type, Identifier, Parameters, Specifications, Statements);

pub type Parameters = Vec<Parameter>;

pub type Parameter = (Type, Identifier);

pub type Specifications = Vec<Specification>;

#[derive(Clone, Debug)]
pub enum Specification {
    Requires(Expression),
    Ensures(Expression),
}

pub type Field = (Type, Identifier);

pub type Statements = Vec<Statement>;

#[derive(Clone)]
pub enum Statement {
    DeclareAssign(DeclareAssign),
    Declaration(Declaration),
    Assignment(Assignment),
    Call(Invocation),
    Skip(Skip),
    Ite(Ite),
    Return(Expression),
    Block(Box<Statements>),
    Assert(Expression),
    Assume(Expression),
    While(While),
}

// Todo: add to syntax & semantics in thesis
pub type DeclareAssign = (Type, Identifier, Rhs);

pub type Declaration = (Type, Identifier);

pub type While = (Expression, Box<Statement>);

#[derive(Clone)]
pub enum Type {
    Void,
    Int,
    Bool,
    Classtype(Identifier),
}

pub type Assignment = (Lhs, Rhs);

#[derive(Clone)]
pub enum Lhs {
    Identifier(String),
    Accessfield(Identifier, Identifier),
}

#[derive(Clone)]
pub enum Rhs {
    Expression(Expression),
    Accessfield(Identifier, Identifier),
    Invocation(Invocation),
    Newobject(Identifier, Arguments),
    NewArray(Type, i64),
}

//TODO: add args hier
pub type Invocation = (Identifier, Identifier, Arguments);

pub type Arguments = Vec<Expression>;

#[derive(Clone)]
pub struct Skip;

pub type Ite = (Expression, Box<Statement>, Box<Statement>);

#[derive(Clone)]
pub enum Expression {
    //expression1
    Forall(Identifier, Box<Expression>),
    Exists(Identifier, Box<Expression>),

    //expression2
    Implies(Box<Expression>, Box<Expression>),

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
    Multiply(Box<Expression>, Box<Expression>),
    Divide(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),

    //Expression8
    Negative(Box<Expression>),
    Not(Box<Expression>),

    //expression9
    Identifier(Identifier),
    Literal(Literal),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Boolean(bool),
    Integer(i64),
}

pub type Identifier = String;

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::DeclareAssign((t, id, rhs)) => write!(
                f,
                "{:?} {:?}",
                t,
                Statement::Assignment((Lhs::Identifier(id.to_string()), rhs.clone()))
            ),
            Statement::Declaration((t, id)) => write!(f, "{:?} {};", t, id),
            Statement::Assignment((lhs, rhs)) => write!(f, "{:?} := {:?}", lhs, rhs),
            Statement::Call((l, r, args)) => write!(f, "{}.{}({:?});", l, r, args),
            Statement::Skip(Skip) => write!(f, " skip "),
            Statement::Ite((cond, if_expr, else_expr)) => {
                write!(f, "if ({:?}) then {:?} else {:?}", cond, if_expr, else_expr)
            }
            Statement::Return(expr) => write!(f, "return {:?};", expr),
            Statement::Block(stmts) => write!(f, "{{ {:?} }}", stmts),
            Statement::Assert(expr) => write!(f, "assert {:?};", expr),
            Statement::Assume(expr) => write!(f, "assume {:?};", expr),
            Statement::While((cond, body)) => write!(f, "while ({:?}) {:?}", cond, body),
        }
    }
}
impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Forall(id, body) => write!(f, "forall {} : {:?}", id, body),
            Expression::Exists(id, body) => write!(f, "exists {} : {:?}", id, body),
            Expression::Implies(l_expr, r_expr) => write!(f, "({:?} ==> {:?})", l_expr, r_expr),
            Expression::And(l_expr, r_expr) => write!(f, "({:?} && {:?})", l_expr, r_expr),
            Expression::Or(l_expr, r_expr) => write!(f, "({:?} || {:?})", l_expr, r_expr),
            Expression::EQ(l_expr, r_expr) => write!(f, "({:?} == {:?})", l_expr, r_expr),
            Expression::NE(l_expr, r_expr) => write!(f, "({:?} != {:?})", l_expr, r_expr),
            Expression::LT(l_expr, r_expr) => write!(f, "({:?} < {:?})", l_expr, r_expr),
            Expression::GT(l_expr, r_expr) => write!(f, "({:?} > {:?})", l_expr, r_expr),
            Expression::GEQ(l_expr, r_expr) => write!(f, "({:?} >= {:?})", l_expr, r_expr),
            Expression::LEQ(l_expr, r_expr) => write!(f, "({:?} <= {:?})", l_expr, r_expr),
            Expression::Plus(l_expr, r_expr) => write!(f, "({:?} + {:?})", l_expr, r_expr),
            Expression::Minus(l_expr, r_expr) => write!(f, "({:?} - {:?})", l_expr, r_expr),
            Expression::Multiply(l_expr, r_expr) => write!(f, "({:?} * {:?})", l_expr, r_expr),
            Expression::Divide(l_expr, r_expr) => write!(f, "({:?} / {:?})", l_expr, r_expr),
            Expression::Mod(l_expr, r_expr) => write!(f, "({:?} % {:?})", l_expr, r_expr),
            Expression::Negative(expr) => write!(f, "-{:?}", expr),
            Expression::Not(expr) => write!(f, "!{:?}", expr),
            Expression::Identifier(id) => write!(f, "{}", id),
            Expression::Literal(Literal::Boolean(val)) => write!(f, "{:?}", val),
            Expression::Literal(Literal::Integer(val)) => write!(f, "{:?}", val),
        }
    }
}
impl fmt::Debug for Lhs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::Accessfield(class, field) => write!(f, "{}.{}", class, field),
            Lhs::Identifier(id) => write!(f, "{}", id),
        }
    }
}
impl fmt::Debug for Rhs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rhs::Expression(expr) => write!(f, "{:?};", expr),
            Rhs::Accessfield(class, field) => write!(f, "{}.{};", class, field),
            Rhs::Invocation((class, fun, args)) => write!(f, " {}.{}({:?});", class, fun, args),
            Rhs::Newobject(class, args) => write!(f, "{}({:?});", class, args),
            Rhs::NewArray(ty, size) => write!(f, "{:?}[{}]", ty, size),
        }
    }
}
impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Bool => write!(f, "bool"),
            Type::Int => write!(f, "int"),
            Type::Classtype(name) => write!(f, "{}", name),
        }
    }
}
