
pub struct Tupple(pub Data, pub Data);

pub enum Data {
    Num(i32),
    Text(String),
    Bool(bool),
    Tupple(Box<Tupple>),
}


