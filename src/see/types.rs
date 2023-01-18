/// Defines search depth for SEE
pub type Depth = i32;

#[derive(Clone)]
pub struct Diagnostics {
    pub paths: i32,
    pub z3_invocations: i32,
}