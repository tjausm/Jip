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
    pub id: Option<Uuid>
}


/// Map identifier to clas, to know where to find invoked functions e.g. c.increment() can only be performed if we know where to find the increment function
pub type TypeEnv = Vec<FxHashMap<Identifier, Class>>;

/// Collection type to identify and retreive content of methods & constructors
#[derive(Clone, Hash, PartialEq, Eq)]
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

/// given a object- or classname returns the class_name
/// e.g. if we call o.f(), where the object o is of class O, calling get_class() will give us the objects class
pub fn get_class_name(object_or_class: &String, ty_env: &TypeEnv) -> &String {
    get_from_env(ty_env, &object_or_class)
        .map(|t| &t.0)
        .unwrap_or(object_or_class)
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
    class_name: &Identifier,
    method_name: &Identifier
) -> Result<&'a Methodcontent, Error> {
    let class = get_class(prog, &class_name)?;

    for member in class.1.iter() {
        match member {
            Member::Method(method) => match method {
                Method::Nonstatic(content @ (_, id, _, _)) => {
                    if id == method_name {
                        return Ok(content);
                    }
                }
                _ => (),
            },
            _ => (),
        }
    }
    return Err(Error::Semantics(format!(
        "Non-static method {}.{} doesn't exist",
        class.0, class_name
    )));
}

pub fn get_static_method<'a>(
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
                _ => (),
            },
            _ => (),
        }
    }
    return Err(Error::Semantics(format!(
        "Static method {}.{} doesn't exist",
        class.0, method_name
    )));
}

pub fn is_static(
    prog: &Program,
    class_name: &Identifier,
    method_name: &Identifier) -> bool {
        get_static_method(prog, class_name, method_name).is_ok()
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
        Routine::Static { class, method } => {
            let (_, _, params, stmts) = get_static_method(prog, class, method)?;
            Ok((params, stmts))
        },
        Routine::NonStatic { object, method } => {
            let (_, _, params, stmts) = get_method(prog, object, method)?;
            Ok((params, stmts))
        },
    }
}
