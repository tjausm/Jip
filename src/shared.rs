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
    Verification(String),
    Other(String),
}

/// since main is unique we only have a scope.id outside of main
#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: Option<Uuid>
}


/// Map identifier to clas, to know where to find invoked functions e.g. c.increment() can only be performed if we know where to find the increment function
pub type TypeStack = Vec<FxHashMap<Identifier, Class>>;

/// Abstraction type over methods & constructors
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Routine {
    Method {
        class: Identifier,
        method: Identifier,
    },
    Constructor {
        class: Identifier,
    },
}

/// print the first 4 symbols of a scope id
pub fn print_short_id(scope: &Scope) -> String {
    let id = scope.id.map(|id| format!("{:?}", id));
    match id {
        None => "".to_owned(),
        Some(id) => {
            let (short_id, _) = id.split_at(4);
            short_id.to_owned()
        }
    }
}

pub fn insert_into_ty_stack<K: Eq + Hash, V>(env: &mut Vec<FxHashMap<K, V>>, key: K, value: V) -> () {
    match env.last_mut() {
        Some(env) => {
            env.insert(key, value);
        }
        None => (),
    };
}

pub fn get_from_ty_stack<K: Eq + Hash + Display, V: Clone>(
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

/// given an object or class name, return class name
/// e.g. if we call o.f(), where object o is of class O then get_class(o) = O 
pub fn get_classname<'a>(object_or_class: &'a String, ty_env: &TypeStack) -> String {
    get_from_ty_stack(ty_env, &object_or_class)
        .map(|t| t.0)
        .unwrap_or(object_or_class.clone())
}

pub fn get_class<'a>(prog: &'a Program, class_name: &str) -> Result<&'a Class, Error> {
    prog.iter()
        .find(|(id, _)| id == class_name)
        .ok_or(Error::Semantics(format!(
            "Class {} doesn't exist",
            class_name
        )))
}

pub fn get_methodcontent<'a>(
    prog: &'a Program,
    class_name: &Identifier,
    method_name: &Identifier,
) -> Result<&'a Methodcontent, Error> {
    let class = get_class(prog, class_name)?;

    for member in class.1.iter() {
        match member {
            Member::Method(method) => match method {
                Method::Static(content @ (_, id, _, _)) => {
                    if id == method_name {
                        return Ok(content);
                    }
                }
                Method::Nonstatic(content @ (_, id, _, _)) => {
                    if id == method_name {
                        return Ok(content);
                    }
                }
            },
            _ => (),
        }
    }
    return Err(Error::Semantics(format!(
        "Static method {}.{} doesn't exist",
        class.0, method_name
    )));
}
    
fn get_constructor<'a>(prog: &'a Program, class_name: &str) -> Result<&'a Constructor, Error> {
    let class = get_class(prog, class_name)?;

    for m in class.1.iter() {
        match m {
            Member::Constructor(c) => return Ok(c),
            _ => continue,
        }
    }
    return Err(Error::Semantics(format!(
        "Class {} does not have a constructor",
        class_name
    )));
}

pub fn get_routine_content<'a>(
    prog: &'a Program,
    routine: &Routine
) -> Result<(&'a Parameters, &'a Statements), Error> {
    match routine {
        Routine::Constructor { class } => {
            let (_, params, stmts) = get_constructor(prog, class)?;
            Ok((params, stmts))
        },
        Routine::Method { class, method } => {
            let (_, _, params, stmts) = get_methodcontent(prog, class, method)?;
            Ok((params, stmts))
        },
    }
}
