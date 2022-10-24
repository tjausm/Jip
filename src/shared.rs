//! Share functions between modules
//!
//!

use crate::ast::*;

use rustc_hash::FxHashMap;
use std::fmt::Display;
use std::hash::Hash;
use uuid::Uuid;

#[derive(Debug, Clone)]
pub enum Error {
    Syntax(String),
    Semantics(String),
    Verification(String),
    Other(String),
}

/// since main is unique we only have a scope.id outside of main
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: Option<Uuid>,
    pub class: Identifier,
    pub method: Identifier
}

/// print the first 4 symbols of a scope id
pub fn print_short_id(scope: &Scope) -> String {
    let id = scope.id.map(|id| format!("{:?}", id));
    match id{
        None => "".to_owned(),
        Some(id) => {
            let (short_id, _) = id.split_at(4);
            short_id.to_owned()
        } 
    }

}


pub fn insert_into_env<K: Eq + Hash, V>(env: &mut Vec<FxHashMap<K, V>>, key: K, value: V) -> () {
    match env.last_mut() {
        Some(env) => {
            env.insert(key, value);
        }
        None => (),
    };
}

pub fn get_from_env<K: Eq + Hash + Display, V: Clone>(
    env_stack: &Vec<FxHashMap<K, V>>,
    id: &K,
) -> Option<V> {
    for env in env_stack.iter().rev() {
        match env.get(id) {
            Some(class) => return Some(class.clone()),
            None => (),
        }
    }
    return None;
}

pub fn get_class<'a>(prog: &'a Program, class_name: &str) -> Result<&'a Class, Error> {
    prog.iter()
        .find(|(id, _)| id == class_name)
        .ok_or(Error::Semantics(format!(
            "Class {} doesn't exist",
            class_name
        )))
}

pub fn get_method<'a>(
    prog: &'a Program,
    class_name: &str,
    method_name: &str,
) -> Result<&'a Method, Error> {
    let class = get_class(prog, class_name)?;
    for member in class.1.iter() {
        match member {
            Member::Method(method) => match method {
                Method::Nonstatic((_, id, _, _)) => {
                    if id == method_name {
                        return Ok(method);
                    }
                }
                Method::Static((_, id, _, _)) => {
                    if id == method_name {
                        return Ok(method);
                    }
                }
            },
            _ => (),
        }
    }
    return Err(Error::Semantics(format!(
        "Method {}.{} doesn't exist",
        class.0, method_name
    )));
}

pub fn get_methodcontent<'a>(
    prog: &'a Program,
    class_name: &str,
    method_name: &str,
) -> Result<&'a Methodcontent, Error> {
    let method = get_method(prog, &class_name, &method_name)?;

    match method {
        Method::Nonstatic(mc) => return Ok(&mc),
        Method::Static(mc) => return Ok(&mc),
    }
}