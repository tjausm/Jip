//TODO: kan concrete syntax 

pub enum Expr9 {
    Identifier(String),
    Literal(Literal)
}

pub enum Literal{
    Boolean(bool),
    Integer(i32)
}
