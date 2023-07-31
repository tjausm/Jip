use crate::shared::panic_with_diagnostics;

use std::fmt;
use std::hash::Hash;
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
                            return &content;
                        }
                    }
                    Method::Nonstatic(content @ (_, id, _, _, _)) => {
                        if id == method_name {
                            return &content;
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
                Member::Constructor(c) => return &c,
                _ => continue,
            }
        }
        panic_with_diagnostics(
            &format!("Class {} does not have a constructor", class_name),
            &(),
        );
    }
}

/// `(class_name, members)`
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
    Requires(OOXExpression),
    Ensures(OOXExpression),
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
    Return(OOXExpression),
    ReturnVoid,
    Block(Box<Statements>),
    Assert(OOXExpression),
    Assume(OOXExpression),
    While(While),
}

// Todo: add to syntax & semantics in thesis
pub type DeclareAssign = (Type, Identifier, Rhs);

pub type Declaration = (Type, Identifier);

pub type While = (OOXExpression, Box<Statement>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Void,
    Int,
    Bool,
    Class(Identifier),
    Array(Box<Type>),
}

pub type Assignment = (Lhs, Rhs);

#[derive(Clone)]
pub enum Lhs {
    Identifier(String),
    AccessField(Identifier, Identifier),
    AccessArray(Identifier, OOXExpression),
}

#[derive(Clone)]
pub enum Rhs {
    OOXExpression(OOXExpression),
    AccessField(Identifier, Identifier),
    AccessArray(Identifier, OOXExpression),
    Invocation(Invocation),
    Newobject(Identifier, Arguments),
    NewArray(Type, OOXExpression),
}

//TODO: add args hier
pub type Invocation = (Identifier, Identifier, Arguments);

pub type Arguments = Vec<OOXExpression>;

#[derive(Clone)]
pub struct Skip;

pub type Ite = (OOXExpression, Box<Statement>, Box<Statement>);

#[derive(Clone, Hash)]
pub enum OOXExpression {
    //expression1
    ///(forall arr, index, value : expression) -> for all index value pairs in given array the expression holds
    Forall(Identifier, Identifier, Identifier, Box<OOXExpression>),
    ///(exists arr, index, value : expression) -> for all index value pairs in given array the expression holds
    Exists(Identifier, Identifier, Identifier, Box<OOXExpression>),

    //expression2
    Implies(Box<OOXExpression>, Box<OOXExpression>),

    //expression3
    And(Box<OOXExpression>, Box<OOXExpression>),
    Or(Box<OOXExpression>, Box<OOXExpression>),

    //expression4
    EQ(Box<OOXExpression>, Box<OOXExpression>),
    NE(Box<OOXExpression>, Box<OOXExpression>),

    //Expression5
    LT(Box<OOXExpression>, Box<OOXExpression>),
    GT(Box<OOXExpression>, Box<OOXExpression>),
    GEQ(Box<OOXExpression>, Box<OOXExpression>),
    LEQ(Box<OOXExpression>, Box<OOXExpression>),

    //Expression6
    Plus(Box<OOXExpression>, Box<OOXExpression>),
    Minus(Box<OOXExpression>, Box<OOXExpression>),

    //Expression7
    Multiply(Box<OOXExpression>, Box<OOXExpression>),
    Divide(Box<OOXExpression>, Box<OOXExpression>),
    Mod(Box<OOXExpression>, Box<OOXExpression>),

    //Expression8
    Negative(Box<OOXExpression>),
    Not(Box<OOXExpression>),

    //expression9
    Identifier(Identifier),
    Literal(Literal),
    SizeOf(Identifier),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
            Statement::Skip(Skip) => write!(f, "skip "),
            Statement::Ite((cond, if_expr, else_expr)) => {
                write!(f, "if ({:?}) then {:?} else {:?}", cond, if_expr, else_expr)
            }
            Statement::Return(expr) => write!(f, "return {:?};", expr),
            Statement::ReturnVoid => write!(f, "return;"),
            Statement::Block(stmts) => write!(f, "{{ {:?} }}", stmts),
            Statement::Assert(expr) => write!(f, "assert {:?};", expr),
            Statement::Assume(expr) => write!(f, "assume {:?};", expr),
            Statement::While((cond, body)) => write!(f, "while ({:?}) {:?}", cond, body),
        }
    }
}
impl fmt::Debug for OOXExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OOXExpression::Forall(arr, i, v, body) => {
                write!(f, "forall {}, {}, {} : {:?}", arr, i, v, body)
            }
            OOXExpression::Exists(arr, i, v, body) => {
                write!(f, "exists {}, {}, {} : {:?}", arr, i, v, body)
            }
            OOXExpression::Implies(l_expr, r_expr) => write!(f, "({:?} ==> {:?})", l_expr, r_expr),
            OOXExpression::And(l_expr, r_expr) => write!(f, "({:?} && {:?})", l_expr, r_expr),
            OOXExpression::Or(l_expr, r_expr) => write!(f, "({:?} || {:?})", l_expr, r_expr),
            OOXExpression::EQ(l_expr, r_expr) => write!(f, "({:?} == {:?})", l_expr, r_expr),
            OOXExpression::NE(l_expr, r_expr) => write!(f, "({:?} != {:?})", l_expr, r_expr),
            OOXExpression::LT(l_expr, r_expr) => write!(f, "({:?} < {:?})", l_expr, r_expr),
            OOXExpression::GT(l_expr, r_expr) => write!(f, "({:?} > {:?})", l_expr, r_expr),
            OOXExpression::GEQ(l_expr, r_expr) => write!(f, "({:?} >= {:?})", l_expr, r_expr),
            OOXExpression::LEQ(l_expr, r_expr) => write!(f, "({:?} <= {:?})", l_expr, r_expr),
            OOXExpression::Plus(l_expr, r_expr) => write!(f, "({:?} + {:?})", l_expr, r_expr),
            OOXExpression::Minus(l_expr, r_expr) => write!(f, "({:?} - {:?})", l_expr, r_expr),
            OOXExpression::Multiply(l_expr, r_expr) => write!(f, "({:?} * {:?})", l_expr, r_expr),
            OOXExpression::Divide(l_expr, r_expr) => write!(f, "({:?} / {:?})", l_expr, r_expr),
            OOXExpression::Mod(l_expr, r_expr) => write!(f, "({:?} % {:?})", l_expr, r_expr),
            OOXExpression::Negative(expr) => write!(f, "-{:?}", expr),
            OOXExpression::Not(expr) => write!(f, "!{:?}", expr),
            OOXExpression::Identifier(id) => write!(f, "{}", id),
            OOXExpression::Literal(lit) => write!(f, "{:?}", lit),
            OOXExpression::SizeOf(id) => write!(f, "#{}", id),
        }
    }
}
impl fmt::Debug for Lhs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::AccessField(class, field) => write!(f, "{}.{}", class, field),
            Lhs::AccessArray(id, index) => write!(f, "{}[{:?}]", id, index),
            Lhs::Identifier(id) => write!(f, "{}", id),
        }
    }
}
impl fmt::Debug for Rhs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rhs::OOXExpression(expr) => write!(f, "{:?};", expr),
            Rhs::AccessField(class, field) => write!(f, "{}.{};", class, field),
            Rhs::AccessArray(class, index) => write!(f, "{}[{:?}];", class, index),
            Rhs::Invocation((class, fun, args)) => write!(f, " {}.{}({:?});", class, fun, args),
            Rhs::Newobject(class, args) => write!(f, "new {}({:?});", class, args),
            Rhs::NewArray(ty, size) => write!(f, "new {:?}[{:?}]", ty, size),
        }
    }
}
impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Bool => write!(f, "bool"),
            Type::Int => write!(f, "int"),
            Type::Class(name) => write!(f, "{}", name),
            Type::Array(ty) => write!(f, "{:?}[]", ty),
        }
    }
}
impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Boolean(b) => write!(f, "{}", b),
            Literal::Integer(i) => write!(f, "{}", i),
        }
    }
}
