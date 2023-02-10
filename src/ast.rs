use crate::shared::panic_with_diagnostics;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::hash::{Hash, Hasher};
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
    ClassType(Identifier),
    ArrayType(Box<Type>),
}

pub type Assignment = (Lhs, Rhs);

#[derive(Clone)]
pub enum Lhs {
    Identifier(String),
    AccessField(Identifier, Identifier),
    AccessArray(Identifier, Expression),
}

#[derive(Clone)]
pub enum Rhs {
    Expression(Expression),
    AccessField(Identifier, Identifier),
    AccessArray(Identifier, Expression),
    Invocation(Invocation),
    Newobject(Identifier, Arguments),
    NewArray(Type, Expression),
}

//TODO: add args hier
pub type Invocation = (Identifier, Identifier, Arguments);

pub type Arguments = Vec<Expression>;

#[derive(Clone)]
pub struct Skip;

pub type Ite = (Expression, Box<Statement>, Box<Statement>);

#[derive(Clone, PartialEq, Eq)]
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
    ArrLength(Identifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Boolean(bool),
    Integer(i64),
}

pub type Identifier = String;

pub enum NormExpression {
    And(Vec<NormExpression>),
    Plus(Vec<NormExpression>),
    EQ(Box<NormExpression>, Box<NormExpression>),
    LT(Box<NormExpression>, Box<NormExpression>),
    Multiply(Box<NormExpression>, Box<NormExpression>),
    Divide(Box<NormExpression>, Box<NormExpression>),
    Mod(Box<NormExpression>, Box<NormExpression>),
    Negative(Box<NormExpression>),
    Not(Box<NormExpression>),
    Identifier(Identifier),
    Literal(Literal),
    ArrLength(Identifier),
}

/// Given 3 expressions `e1 = 1+2+3`, `e2 = 3+2+1` and `e1 = 2+3+1`
/// then `normalize(e1) == normalize(e2)`, `normalize(e2) == normalize(e3)` and so on
fn normalize(expr: Expression) -> NormExpression {

    // todo simplify expression somewhere

    fn collect_conjunction(expr: Expression) -> Vec<NormExpression> {
        match expr {
            Expression::And(l_expr, r_expr) => {
                let mut members = collect_conjunction(*l_expr);
                members.append(&mut collect_conjunction(*r_expr));
                members
            }
            _ => vec![normalize(expr)],
        }
    }
    fn collect_summation(expr: Expression) -> Vec<NormExpression> {
        match expr {
            Expression::Plus(l_expr, r_expr) => {
                let mut members = collect_conjunction(*l_expr);
                members.append(&mut collect_conjunction(*r_expr));
                members
            }
            _ => vec![normalize(expr)],
        }
    }

    match expr {
        // for both the summation and conjunction we collect all parts
        Expression::And(_, _) => NormExpression::And(collect_conjunction(expr)),
        Expression::Plus(_, _) => NormExpression::And(collect_summation(expr)),

        Expression::EQ(l_expr, r_expr) => {
            let mut nl_expr = normalize(*l_expr);
            let mut nr_expr = normalize(*r_expr);

            todo!()
        }

        // change a - b to a + (- b) and normalize again
        Expression::Minus(l_expr, r_expr) => normalize(Expression::Plus(
            Box::new(*l_expr),
            Box::new(Expression::Negative(Box::new(*r_expr))),
        )),

        // change to ! (!l_expr && !r_expr) and !(l_expr == r_expr),
        // meaning we map || and != to == and &&
        Expression::Or(l_expr, r_expr) => normalize(Expression::Not(Box::new(Expression::And(
            Box::new(Expression::Not(Box::new(*l_expr))),
            Box::new(Expression::Not(Box::new(*r_expr))),
        )))),
        Expression::NE(l_expr, r_expr) => normalize(Expression::Not(Box::new(Expression::EQ(
            Box::new(*l_expr),
            Box::new((*r_expr)),
        )))),

        // Stefan's normalization
        Expression::LT(l_expr, r_expr) => {
            NormExpression::LT(Box::new(normalize(*l_expr)), Box::new(normalize(*r_expr)))
        }
        Expression::GT(l_expr, r_expr) => {
            NormExpression::LT(Box::new(normalize(*r_expr)), Box::new(normalize(*l_expr)))
        }
        Expression::GEQ(l_expr, r_expr) => NormExpression::Not(Box::new(NormExpression::LT(
            Box::new(normalize(*l_expr)),
            Box::new(normalize(*r_expr)),
        ))),
        Expression::LEQ(l_expr, r_expr) => NormExpression::Not(Box::new(NormExpression::LT(
            Box::new(normalize(*r_expr)),
            Box::new(normalize(*l_expr)),
        ))),

        // normalize l and r
        Expression::Multiply(l_expr, r_expr) => {
            NormExpression::Multiply(Box::new(normalize(*l_expr)), Box::new(normalize(*r_expr)))
        }
        Expression::Divide(l_expr, r_expr) => {
            NormExpression::Multiply(Box::new(normalize(*l_expr)), Box::new(normalize(*r_expr)))
        }
        Expression::Mod(l_expr, r_expr) => {
            NormExpression::Multiply(Box::new(normalize(*l_expr)), Box::new(normalize(*r_expr)))
        }

        // normalize inner
        Expression::Negative(expr) => NormExpression::Negative(Box::new(normalize(*expr))),
        Expression::Not(expr) => NormExpression::Not(Box::new(normalize(*expr))),

        // identity function
        Expression::Identifier(id) => NormExpression::Identifier(id),
        Expression::Literal(lit) => NormExpression::Literal(lit),
        Expression::ArrLength(id) => NormExpression::ArrLength(id),

        _ => todo!(),
    };
    todo!()
}

// give an arbitrary number to expressions to sort them in a predictable manner
fn order_expr(expr: &NormExpression) -> u128 {
    let mut hasher = DefaultHasher::new();
    match expr {
        NormExpression::And(_) => todo!(),
        NormExpression::Plus(_) => todo!(),
        NormExpression::EQ(_, _) => todo!(),
        NormExpression::LT(_, _) => todo!(),
        NormExpression::Multiply(_, _) => todo!(),
        NormExpression::Divide(_, _) => todo!(),
        NormExpression::Mod(_, _) => todo!(),
        NormExpression::Negative(_) => todo!(),
        NormExpression::Not(_) => todo!(),
        NormExpression::Literal(Literal::Boolean(true)) => 0,
        NormExpression::Literal(Literal::Boolean(false)) => 1,
        NormExpression::Literal(Literal::Integer(n)) => u64::MAX as u128 + *n as u128,
        NormExpression::Identifier(id) => {
            id.hash(&mut hasher);
            hasher.finish() as u128
        }
        NormExpression::ArrLength(id) => {
            // write some data into this hasher to make result different than Identifier
            hasher.write_u8(100);
            id.hash(&mut hasher);
            hasher.finish() as u128
        }
    }
}

fn get_inner_exprs(expr: &Expression) -> (&Expression, Option<&Expression>) {
    match expr {
        Expression::Implies(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::And(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Or(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::EQ(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::NE(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::LT(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::GT(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::GEQ(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::LEQ(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Plus(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Minus(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Multiply(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Divide(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Mod(l_expr, r_expr) => (l_expr, Some(r_expr)),
        Expression::Forall(_, r_expr) => (r_expr, None),
        Expression::Exists(_, r_expr) => (r_expr, None),
        _ => (expr, None),
    }
}


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
            Expression::ArrLength(id) => write!(f, "#{:?}", id),
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
            Rhs::Expression(expr) => write!(f, "{:?};", expr),
            Rhs::AccessField(class, field) => write!(f, "{}.{};", class, field),
            Rhs::AccessArray(class, index) => write!(f, "{}.[{:?}];", class, index),
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
            Type::ClassType(name) => write!(f, "{}", name),
            Type::ArrayType(ty) => write!(f, "{:?}[]", ty),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    lalrpop_mod!(pub parser);

    fn parse(i: &str) -> Expression {
        return parser::VerificationExpressionParser::new()
            .parse(i)
            .unwrap();
    }

    #[test]
    fn sort_expressions() {
        let one = parse("1");
        let id = parse("id");
        let conjunction = parse("test && true");
        let negative = parse("-1");
        let three = parse("0+1+2*3/3");
        let onwaar = parse("!true && false || false");

        // construct some random arrays with these expressions
        let mut arr1 = [
            onwaar.clone(),
            onwaar.clone(),
            onwaar.clone(),
            conjunction.clone(),
            id.clone(),
            one.clone(),
        ];
        let mut arr2 = [
            one.clone(),
            id.clone(),
            conjunction.clone(),
            onwaar.clone(),
            onwaar.clone(),
            onwaar.clone(),
        ];
        let mut arr3 = [
            onwaar.clone(),
            one.clone(),
            onwaar.clone(),
            conjunction.clone(),
            onwaar.clone(),
            id.clone(),
        ];
        let mut arr4 = [id, onwaar, conjunction, negative, one, three];

        // arr1.sort();
        // arr2.sort();
        // arr3.sort();
        // arr4.sort();

        // check if arrays are equal after sorting
        assert!(arr1 == arr2);
        assert!(arr1 == arr3);
        assert!(arr1 == arr4);
    }

    #[test]
    fn expr_in_fxhashmap() {
        let e1 = parse("1+2+3");
        let e2 = parse("3+2+1");
        //assert!(normalize(e1) == normalize(e2));
    }
}
