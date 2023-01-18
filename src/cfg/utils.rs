use crate::shared::{Scope, custom_panic};
use crate::ast::*;
use crate::cfg::types::*;

use rustc_hash::FxHashMap;
use std::fmt::{Display, self};
use std::hash::Hash;


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

pub fn insert_into_ty_stack<K: Eq + Hash, V>(
    env: &mut Vec<FxHashMap<K, V>>,
    key: K,
    value: V,
) -> () {
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

pub fn get_class<'a>(prog: &'a Program, class_name: &str) -> &'a Class {
    match prog.iter()
        .find(|(id, _)| id == class_name) {
            Some(class) => return class,
            None => custom_panic(&format!(
                "Class {} doesn't exist",
                class_name
            ), None, None)
        }

}

pub fn get_methodcontent<'a>(
    prog: &'a Program,
    class_name: &Identifier,
    method_name: &Identifier,
) -> &'a Methodcontent {
    let class = get_class(prog, class_name);

    for member in class.1.iter() {
        match member {
            Member::Method(method) => match method {
                Method::Static(content @ (_, id, _, _)) => {
                    if id == method_name {
                        return content;
                    }
                }
                Method::Nonstatic(content @ (_, id, _, _)) => {
                    if id == method_name {
                        return content;
                    }
                }
            },
            _ => (),
        }
    }
    custom_panic(&format!(
        "Static method {}.{} doesn't exist",
        class.0, method_name
    ), None, None);
    
}

fn get_constructor<'a>(prog: &'a Program, class_name: &str) -> &'a Constructor {
    let class = get_class(prog, class_name);

    for m in class.1.iter() {
        match m {
            Member::Constructor(c) => return c,
            _ => continue,
        }
    }
    custom_panic(&format!(
        "Class {} does not have a constructor",
        class_name
    ), None, None);
}

pub fn get_routine_content<'a>(
    prog: &'a Program,
    routine: &Routine,
) -> (&'a Parameters, &'a Statements) {
    match routine {
        Routine::Constructor { class } => {
            let (_, params, stmts) = get_constructor(prog, class);
            (params, stmts)
        }
        Routine::Method { class, method } => {
            let (_, _, params, stmts) = get_methodcontent(prog, class, method);
            (params, stmts)
        }
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::EnteringMain(_) => write!(f, "Entering Main.main"),
            Node::Statement(stmt) => write!(f, "{:?}", stmt),
            Node::EnterRoutine(r) => {
                write!(f, "Entering {:?}", r)
            }
            Node::LeaveRoutine(r) => {
                write!(f, "Leaving {:?}", r)
            }
            Node::End => {
                write!(f, "End")
            }
        }
    }
}

impl fmt::Debug for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Action::EnterScope { to: scope } => {
                write!(f, "Entering scope {}", print_short_id(scope))
            }
            Action::AssignArgs { params, args } => {
                let ap_str = params
                    .iter()
                    .zip(args.iter())
                    .map(|((_, arg), param)| format!("{} := {:?}", arg, param))
                    .collect::<Vec<String>>()
                    .join(", ");
                write!(f, "{}", ap_str)
            }
            Action::LeaveScope { from } => {
                write!(f, "Leaving scope {}", print_short_id(from))
            }
            Action::DeclareThis { class, obj } => write!(f, "{} this := {:?}", class, obj),
            Action::InitObj { from, to } => {
                write!(f, "Init {} {:?} on heap", from.0, to)
            }
            Action::LiftRetval => write!(f, "Lifting retval"),
            Action::DeclareRetval { ty } => write!(f, "Declaring '{:?} retval'", ty),
        }
    }
}
