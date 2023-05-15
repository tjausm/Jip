use std::fmt;

use crate::ast::*;
use crate::cfg::types::*;
use crate::shared::Scope;

/// prints either main or scope id if we have one
pub fn print_short_id(scope: &Scope) -> String {
    match scope.id {
        None => "main".to_owned(),
        Some(id) => id.to_string(),
    }
}

/// given an object or class name, return class name
/// e.g. if we call `o.f()`, where object `o` is of class `C` then `get_class(o) = C`
pub fn get_classname<'a>(object_or_class: &'a String, ty_stack: &TypeStack) -> String {
    ty_stack
        .get(&object_or_class)
        .map(|t| t.0)
        .unwrap_or(object_or_class.clone())
}

pub fn get_routine_content<'a>(
    prog: &'a Program,
    routine: &Routine,
) -> (&'a Parameters, &'a Specifications, &'a Statements) {
    match routine {
        Routine::Constructor { class } => {
            let (_, params, specs, stmts) = prog.get_constructor(class);
            (params, specs, stmts)
        }
        Routine::Method { class, method } => {
            let (_, _, params, specs, stmts) = prog.get_methodcontent(class, method);
            (params, specs, stmts)
        }
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::EnteringMain(_) => write!(f, "Entering Main.main"),
            Node::Statement(stmt) => write!(f, "{:?}", stmt),
            Node::EnterProcedure(r) => {
                write!(f, "Entering {:?}", r)
            }
            Node::LeaveProcedure(r) => {
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
            Action::InitObj { from_class, to } => {
                write!(f, "Init {} {:?} on heap", from_class, to)
            }
            Action::LiftRetval => write!(f, "Lifting retval"),
            Action::CheckSpecifications { specifications } => {
                write!(f, "Checking specifications: {:?}", specifications)
            }
        }
    }
}
