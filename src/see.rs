//! Symbolic Execution Engine (SEE) combines parser, CFG creation, program path generation, transformation from path to formula and verification of said formula by Z3
//!

use crate::ast::*;
use crate::cfg::{generate_cfg, generate_dot_cfg, Action, Node};
use crate::shared::{Error, Scope};
use crate::z3::{
    check_path, expression_to_bool, expression_to_int, fresh_bool, fresh_int, get_from_stack,
    insert_into_stack, Frame, PathConstraint, ReferenceValue, SymHeap, SymStack,
    SymbolicExpression,
};

lalrpop_mod!(pub parser);
// synthesized by LALRPOP
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use uuid::Uuid;
use z3::{Config, Context};

use rustc_hash::FxHashMap;
use std::collections::VecDeque;
use std::fs;

const PROG_CORRECT: &'static str = "Program is correct";

/// Indicates if program is valid, counterexample was found or other error occured
pub enum ExitCode {
    Valid = 0,
    CounterExample = 1,
    Error = 2,
}

/// Defines search depth for SEE
pub type Depth = i32;

#[derive(Clone)]
struct Diagnostics {
    paths: i32,
    z3_invocations: i32,
}

fn print_result(r: Result<Diagnostics, Error>) -> (ExitCode, String) {
    match r {
        Err(Error::Syntax(why)) => (ExitCode::Error, format!("Syntax error: {}", why)),
        Err(Error::Semantics(why)) => (ExitCode::Error, format!("Semantics error: {}", why)),
        Err(Error::Other(why)) => (ExitCode::Error, format!("{}", why)),
        Err(Error::Verification(why)) => (ExitCode::CounterExample, format!("{}", why)),
        Ok(_) => (ExitCode::Valid, PROG_CORRECT.to_string()),
    }
}

pub fn load_program(program: String) -> Result<String, (ExitCode, String)> {
    match fs::read_to_string(program) {
        Err(why) => Err(print_result(Err(Error::Other(format!("{}", why))))),
        Ok(content) => Ok(content),
    }
}

fn parse_program(program: &str) -> Result<Program, Error> {
    match parser::ProgramParser::new().parse(program) {
        Err(parse_err) => return Err(Error::Syntax(format!("{}", parse_err))),
        Ok(program) => return Ok(program),
    }
}

pub fn print_cfg(program: &str) -> (ExitCode, String) {
    match parse_program(program) {
        Err(parse_err) => print_result(Err(parse_err)),
        Ok(stmts) => match generate_dot_cfg(stmts) {
            Ok(cfg) => (ExitCode::Valid, cfg),
            Err(sem_err) => print_result(Err(sem_err)),
        },
    }
}

pub fn print_verification(program: &str, d: Depth, verbose: bool) -> (ExitCode, String) {
    let print_diagnostics = |d: Result<Diagnostics, _>| match d {
        Ok(Diagnostics {
            paths,
            z3_invocations,
        }) => format!(
            "\nPaths checked    {}\nZ3 invocations   {}",
            paths, z3_invocations
        ),
        _ => "".to_string(),
    };
    let result = verify_program(program, d);
    let (ec, r) = print_result(result.clone());

    if verbose {
        return (ec, format!("{}{}", r, print_diagnostics(result)));
    }
    return (ec, r);
}

fn verify_program(prog_string: &str, d: Depth) -> Result<Diagnostics, Error> {
    //init diagnostic info
    let mut diagnostics = Diagnostics {
        paths: 0,
        z3_invocations: 0,
    };

    // init retval and this such that it outlives env
    let retval_id = &"retval".to_string();
    let this_id = &"this".to_string();

    let prog = parse_program(prog_string)?;
    let (start_node, cfg) = generate_cfg(prog.clone())?;

    let z3_cfg = Config::new();
    let ctx = Context::new(&z3_cfg);

    //init our bfs through the cfg
    let mut q: VecDeque<(SymStack, SymHeap, Vec<PathConstraint>, Depth, NodeIndex)> =
        VecDeque::new();
    let main = Frame {
        scope: Scope { id: None },
        env: FxHashMap::default(),
    };
    q.push_back((
        vec![main.clone()],
        FxHashMap::default(),
        vec![],
        d,
        start_node,
    ));

    // Assert -> build & verify z3 formula, return error if disproven
    // Assume -> build & verify z3 formula, stop evaluating pad if disproven
    // assignment -> evaluate rhs and update env
    // then we enque all connected nodes, till d=0 or we reach end of cfg
    while let Some((mut sym_stack, mut sym_heap, mut pc, d, curr_node)) = q.pop_front() {
        if d == 0 {
            continue;
        }

        match &cfg[curr_node] {
            // add all parameters of main as free variables to env
            Node::EnteringMain(parameters) => {
                for p in parameters {
                    match p {
                        (Type::Int, id) => {
                            insert_into_stack(&mut sym_stack, &id, fresh_int(&ctx, id.clone()))
                        }
                        (Type::Bool, id) => {
                            insert_into_stack(&mut sym_stack, &id, fresh_bool(&ctx, id.clone()))
                        }
                        (ty, id) => {
                            return Err(Error::Semantics(format!(
                                "Can't call main with parameter {} of type {:?}",
                                id, ty
                            )))
                        }
                    }
                }
            }

            Node::Statement(stmt) => {
                match stmt {
                    Statement::Declaration((ty, id)) => match ty {
                        Type::Int => {
                            insert_into_stack(&mut sym_stack, &id, fresh_int(&ctx, id.clone()));
                        }
                        Type::Bool => {
                            insert_into_stack(&mut sym_stack, &id, fresh_bool(&ctx, id.clone()));
                        },
                        Type::Classtype(ty) => {
                            let r = Uuid::new_v4();
                            insert_into_stack(&mut sym_stack, id, SymbolicExpression::Ref((Type::Classtype(ty.clone()), r)))
                        },
                        Type::Void => panic!("Panic should never trigger, parser doesn't accept void type in declaration"),
                    },
                    Statement::Assume(expr) => {
                        let ast = expression_to_bool(&ctx, &sym_stack, &expr)?;
                        pc.push(PathConstraint::Assume(ast));
                    }

                    // return err if is invalid else continue
                    Statement::Assert(expr) => match expression_to_bool(&ctx, &sym_stack, &expr) {
                        Err(why) => return Err(why),
                        Ok(ast) => {
                            diagnostics.z3_invocations = diagnostics.z3_invocations + 1;

                            pc.push(PathConstraint::Assert(ast));
                            match check_path(&ctx, &pc) {
                                Err(why) => return Err(why),
                                Ok(_) => (),
                            }
                        }
                    },
                    Statement::Assignment((lhs, rhs)) => {
                        // get lhs type
                        // parse expression variable
                        // assign to id in stack
                        lhs_from_rhs(&ctx, &mut sym_stack, &mut sym_heap, lhs, rhs)?;
                    }
                    Statement::Return(expr) => {
                        
                        // stop path if it returns from main function 
                        match sym_stack.last() {
                            Some(an_scope) if an_scope.scope.id == main.scope.id => continue,
                            _ => (),
                        }

                        // evaluate return expression with type of retval and add to stack
                        match get_from_stack(&sym_stack, retval_id) {
                            Some(SymbolicExpression::Int(_)) => {
                                let ast = expression_to_int(&ctx, &sym_stack, &expr)?;
                                insert_into_stack(
                                    &mut sym_stack,
                                    retval_id,
                                    SymbolicExpression::Int(ast),
                                );
                            }

                            Some(SymbolicExpression::Bool(_)) => {
                                let ast = expression_to_bool(&ctx, &sym_stack, &expr)?;
                                insert_into_stack(
                                    &mut sym_stack,
                                    retval_id,
                                    SymbolicExpression::Bool(ast),
                                );
                            }
                            Some(SymbolicExpression::Ref(_)) => {
                                match expr {
                                    Expression::Identifier(id) => match get_from_stack(&sym_stack, id) {
                                        Some(SymbolicExpression::Ref(r)) => insert_into_stack(&mut sym_stack, retval_id, SymbolicExpression::Ref(r)),
                                        Some(expr) => return Err(Error::Semantics(format!("Can't return '{:?}' as a referencevalue", expr))),
                                        None => return Err(Error::Semantics(format!("{} is undeclared", id))),
                                    },
                                    _ => return Err(Error::Semantics(format!("Can't return expression '{:?}'", expr))),
                                }
                            },
                            None => {
                                print!("return {:?}", expr);
                                return Err(Error::Semantics(format!("retval is undeclared")));
                            }
                        }
                    }
                    _ => (),
                }
            }
            Node::End => diagnostics.paths = diagnostics.paths + 1,
            _ => (),
        }

        'q_nodes: for edge in cfg.edges(curr_node) {
            // clone new stack and heap for each edge we travel to
            let mut sym_stack = sym_stack.clone();
            let mut sym_heap = sym_heap.clone();

            // perform all actions in an edge and enque the result
            for action in edge.weight() {
                match action {
                    Action::EnterScope { to: scope } => sym_stack.push(Frame {
                        scope: scope.clone(),
                        env: FxHashMap::default(),
                    }),
                    Action::DeclareRetval { ty } => {
                        // declare retval with correct type in new scope
                        match ty {
                            Type::Int => insert_into_stack(
                                &mut sym_stack,
                                retval_id,
                                fresh_int(&ctx, "retval".to_string()),
                            ),
                            Type::Bool => insert_into_stack(
                                &mut sym_stack,
                                retval_id,
                                fresh_bool(&ctx, "retval".to_string()),
                            ),
                            Type::Classtype(ty) => insert_into_stack(
                                &mut sym_stack,
                                retval_id,
                                SymbolicExpression::Ref((Type::Classtype(ty.clone()), Uuid::nil()))),
                            Type::Void => panic!("Cannot declare retval of type void"),
                        }
                    }
                    Action::AssignArgs { params, args } => {
                        let variables = params_to_vars(&ctx, &mut sym_stack, params, &args)?;

                        for (id, var) in variables {
                            insert_into_stack(&mut sym_stack, id, var);
                        }
                    }
                    Action::DeclareThis { class, obj } => match obj {
                        Lhs::Identifier(id) => match get_from_stack(&sym_stack, id) {
                            Some(SymbolicExpression::Ref(r)) => insert_into_stack(
                                &mut sym_stack,
                                this_id,
                                SymbolicExpression::Ref(r),
                            ),
                            Some(_) => {
                                return Err(Error::Semantics(format!(
                                    "{} is not of type {}",
                                    id, class
                                )))
                            }
                            None => {
                                return Err(Error::Semantics(format!(
                                    "Variable {} is undeclared",
                                    id
                                )))
                            }
                        },
                        Lhs::Accessfield(_, _) => {
                            todo!("assigning objects to accesfields not implemented")
                        }
                    },
                    Action::InitObj {
                        from: (class, members),
                        to: lhs,
                    } => {
                        // make an empty object
                        let mut fields = FxHashMap::default();

                        // map all fields to symbolic values
                        for member in members {
                            match member {
                                Member::Field((ty, field)) => match ty {
                                    Type::Int => {
                                        fields.insert(
                                            field,
                                            (
                                                Type::Int,
                                                crate::z3::fresh_int(&ctx, field.to_string()),
                                            ),
                                        );
                                    }
                                    Type::Bool => {
                                        (
                                            Type::Bool,
                                            fields.insert(
                                                field,
                                                (Type::Bool, fresh_bool(&ctx, field.to_string())),
                                            ),
                                        );
                                    }
                                    Type::Classtype(class) => {
                                        // insert uninitialized object to heap
                                        let (ty, r) = (Type::Classtype(class.to_string()), Uuid::new_v4());
                                        sym_heap.insert(
                                            r,
                                            ReferenceValue::Uninitialized(Type::Classtype(
                                                class.to_string(),
                                            )),
                                        );
                                        fields.insert(
                                            field,
                                            (
                                                Type::Classtype(class.to_string()),
                                                SymbolicExpression::Ref((ty, r)),
                                            ),
                                        );
                                    }
                                    Type::Void => {
                                        return Err(Error::Semantics(format!(
                                            "Type of {}.{} can't be void",
                                            class, field
                                        )))
                                    }
                                },
                                _ => (),
                            }
                        }

                        // get reference r and map r to initialized object on heap
                        match lhs {
                            Lhs::Identifier(id) =>{
                                match get_from_stack(&sym_stack, id) {
                                    Some(SymbolicExpression::Ref((_, r))) => sym_heap.insert(r, ReferenceValue::Object((Type::Classtype(class.to_string()), fields))),
                                    _ => return Err(Error::Semantics(format!("Can't initialize '{} {}' because no reference is declared on the stack", class, id))),
                                }
                            },
                            Lhs::Accessfield(_, _) => todo!(),
                        };
                    }
                    // lift retval 1 scope up
                    Action::LiftRetval => {
                        match get_from_stack(&sym_stack, retval_id) {
                            Some(retval) => {
                                let higher_frame = sym_stack.len() - 2;
                                match sym_stack.get_mut(higher_frame) {
                                    Some(frame) => {
                                        frame.env.insert(retval_id, retval);
                                    }
                                    None => {
                                        return Err(Error::Semantics(
                                            "Can't return from main scope".to_owned(),
                                        ));
                                    }
                                }
                            }
                            None => {
                                return Err(Error::Semantics(
                                    "Can't lift retval to a higher scope".to_owned(),
                                ));
                            }
                        };
                    }
                    // if we can leave over this edge pop scope otherwise dismiss path pe
                    Action::LeaveScope { from: to_scope } => match sym_stack.last() {
                        Some(env) if env.scope == *to_scope => {
                            sym_stack.pop();
                        }
                        _ => continue 'q_nodes,
                    },
                }
            }
            let next = edge.target();
            q.push_back((sym_stack, sym_heap, pc.clone(), d - 1, next));
        }
    }
    return Ok(diagnostics);
}

fn type_lhs<'ctx>(
    sym_stack: &SymStack<'ctx>,
    sym_heap: &SymHeap<'ctx>,
    lhs: &'ctx Lhs,
) -> Result<Type, Error> {
    match lhs {
        Lhs::Accessfield(obj, field) => match get_from_stack(&sym_stack, obj) {
            Some(SymbolicExpression::Ref((ty, r))) => match sym_heap.get(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (ty, _) = fields.get(field).ok_or(Error::Semantics(format!(
                        "Can't type field '{}.{}' because it does not exist",
                        obj, field
                    )))?;
                    return Ok(ty.clone());
                }
                Some(ReferenceValue::Uninitialized(ty)) => {
                    todo!("searching through program to get type of uninitialized fields")
                }
                Some(ReferenceValue::Array(_)) => {
                    return Err(Error::Semantics(format!(
                        "Can't type '{}.{}' because the reference of '{}' points to an array",
                        obj, field, obj
                    )))
                }
                None => {
                    return Err(Error::Semantics(format!(
                    "Can't type '{}.{}' because reference of '{}' points to nothing on the heap",
                    obj, field, obj
                )))
                }
            },
            _ => {
                return Err(Error::Semantics(format!(
                    "Can't type '{}.{}' because {} is not a reference",
                    obj, field, obj
                )))
            }
        },
        Lhs::Identifier(id) => match get_from_stack(sym_stack, id) {
            Some(SymbolicExpression::Bool(_)) => Ok(Type::Bool),
            Some(SymbolicExpression::Int(_)) => Ok(Type::Int),
            Some(SymbolicExpression::Ref((ty, _))) => Ok(ty),
            None => {
                return Err(Error::Semantics(format!(
                    "Can't type '{}' because it is undeclared on the stack",
                    id
                )))
            }
        },
    }
}

/// returns the symbolic expression rhs refers to
fn parse_rhs<'ctx>(
    ctx: &'ctx Context,
    sym_stack: &SymStack<'ctx>,
    sym_heap: &SymHeap<'ctx>,
    ty: &Type,
    rhs: &'ctx Rhs,
) -> Result<SymbolicExpression<'ctx>, Error> {
    match rhs {
        Rhs::Accessfield(obj_name, field_name) => match get_from_stack(sym_stack, obj_name) {
            Some(SymbolicExpression::Ref((_, r))) => match sym_heap.get(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let (_, value) = fields.get(field_name).ok_or(Error::Semantics(format!(
                        "Field {} does not exist on {}",
                        field_name, obj_name
                    )))?;
                    return Ok(value.clone());
                }

                _ => Err(Error::Semantics(format!(
                    "Reference of {} does not exist on the heap",
                    obj_name
                ))),
            },
            _ => Err(Error::Semantics(format!("{} is not a reference", obj_name))),
        },
        Rhs::Expression(expr) => match ty {
            Type::Int => {
                let ast = expression_to_int(&ctx, &sym_stack, &expr)?;
                Ok(SymbolicExpression::Int(ast))
            }

            Type::Bool => {
                let ast = expression_to_bool(&ctx, &sym_stack, &expr)?;
                Ok(SymbolicExpression::Bool(ast))
            }
            Type::Classtype(class) => {
                match expr {
                    Expression::Identifier(id) => 
                        match get_from_stack(sym_stack, id) {
                            Some(SymbolicExpression::Ref((ty,r))) => Ok(SymbolicExpression::Ref((ty, r))),
                            Some(_) => Err(Error::Semantics(format!("TODO: think of error"))),
                            None => Err(Error::Semantics(format!("TODO: think of error"))),
                        }
                    _ => return Err(Error::Semantics(format!("Can't evaluate {:?} to type {}", rhs, class)))
                }
            },
            Type::Void => Err(Error::Other(format!(
                "Can't evaluate rhs expression of the form {:?} to type void",
                rhs
            ))),
        },
        _ => Err(Error::Other(format!(
            "Rhs of the form {:?} should not be in the cfg",
            rhs
        ))),
    }
}

/// assigns value from rhs to lhs
fn lhs_from_rhs<'ctx>(
    ctx: &'ctx Context,
    sym_stack: &mut SymStack<'ctx>,
    sym_heap: &mut SymHeap<'ctx>,
    lhs: &'ctx Lhs,
    rhs: &'ctx Rhs,
) -> Result<(), Error> {
    let ty = type_lhs(&sym_stack, &sym_heap, lhs)?;
    let var = parse_rhs(&ctx, sym_stack, sym_heap, &ty, rhs)?;
    match lhs {
        Lhs::Accessfield(obj_name, field_name) => match get_from_stack(sym_stack, obj_name) {
            Some(SymbolicExpression::Ref((ty, r))) => match sym_heap.get_mut(&r) {
                Some(ReferenceValue::Object((_, fields))) => {
                    let ty = fields
                        .get(field_name)
                        .ok_or(Error::Semantics(format!(
                            "Field {} does not exist on {}",
                            field_name, obj_name
                        )))?
                        .0
                        .clone();
                    fields.insert(field_name, (ty.clone(), var));
                    Ok(())
                }
                _ => Err(Error::Semantics(format!(
                    "Reference of {} does not exist on the heap",
                    obj_name
                ))),
            },
            _ => Err(Error::Semantics(format!("{} is not a reference", obj_name))),
        },
        Lhs::Identifier(id) => Ok(insert_into_stack(sym_stack, id, var)),
    }
}

/// evaluates the parameters & arguments to a mapping id -> variable that can be added to a function scope
fn params_to_vars<'ctx>(
    ctx: &'ctx Context,
    sym_stack: &mut SymStack<'ctx>,
    params: &'ctx Parameters,
    args: &'ctx Arguments,
) -> Result<Vec<(&'ctx String, SymbolicExpression<'ctx>)>, Error> {
    let mut params_iter = params.iter();
    let mut args_iter = args.iter();
    let mut variables = vec![];

    loop {
        match (params_iter.next(), args_iter.next()) {
            (Some((Type::Int, arg_id)), Some(expr)) => {
                let expr = expression_to_int(ctx, sym_stack, expr)?;
                variables.push((arg_id, SymbolicExpression::Int(expr)));
            }
            (Some((Type::Bool, arg_id)), Some(expr)) => {
                let expr = expression_to_bool(ctx, sym_stack, expr)?;
                variables.push((arg_id, SymbolicExpression::Bool(expr)));
            }
            (Some((Type::Classtype(class), arg_id)), Some(expr)) => {
                let err = |class, arg_id, expr| Err(Error::Semantics(format!("Can't assign argument '{} {}' value '{:?}'", class, arg_id, expr)));
                match expr {
                    Expression::Identifier(param_id) => {
                        match get_from_stack(sym_stack, param_id) {
                            Some(SymbolicExpression::Ref(r)) => variables.push((arg_id, SymbolicExpression::Ref(r))),
                            _ => return err(class,arg_id, expr),
                        }
                    },
                    _ => return err(class,arg_id, expr)
                }
            }
            (Some((ty, _)), Some(_)) => {
                return Err(Error::Semantics(format!(
                    "Argument of type {:?} are not implemented",
                    ty
                )))
            }
            (Some((_, param)), None) => {
                return Err(Error::Semantics(format!(
                    "Missing an argument for parameter {:?} in a method call",
                    param
                )))
            }
            (None, Some(expr)) => {
                return Err(Error::Semantics(format!(
                    "Expression {:?} has no parameter it can be assigned to in a method call",
                    expr
                )))
            }
            (None, None) => break,
        }
    }
    return Ok(variables);
}

/// Contains parser tests since parser mod is auto-generated
#[cfg(test)]
mod tests {

    lalrpop_mod!(pub parser);

    #[test]
    fn assignment() {
        assert!(parser::StatementsParser::new().parse("x := 2;").is_ok());
        assert!(parser::StatementsParser::new()
            .parse("divisible := (i * k == x);")
            .is_ok());
        assert!(parser::StatementsParser::new().parse("int x := 2;").is_ok());
    }

    #[test]
    fn expressions() {
        assert!(parser::VerificationExpressionParser::new()
            .parse("2 < 1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("!true && false")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("-1")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("y && z || a")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 == 2 != 3")
            .is_ok());
        assert!(parser::VerificationExpressionParser::new()
            .parse("1 + 2 - 3 / 4 % 5 * 6")
            .is_ok());
    }
    #[test]
    fn declaration() {
        assert!(parser::StatementsParser::new().parse("int x;").is_ok());
    }
    #[test]
    fn statements() {
        assert!(parser::StatementsParser::new()
            .parse("int x; x := 2; if(true)x := 1; else x := 2;")
            .is_ok());
    }
    #[test]
    fn block() {
        assert!(parser::StatementsParser::new()
            .parse("if(true){x := 1; bool z;} else {y := 2; x := 2;}")
            .is_ok());
    }
    #[test]
    fn assume() {
        assert!(parser::StatementsParser::new()
            .parse("assume true;")
            .is_ok());
    }
    #[test]
    fn assert() {
        assert!(parser::StatementsParser::new()
            .parse("assert true;")
            .is_ok());
    }
    #[test]
    fn while_loop() {
        assert!(parser::StatementsParser::new()
            .parse("while (1 < 2) x := y;")
            .is_ok());
    }
    #[test]
    fn Program() {
        assert!(parser::ProgramParser::new()
            .parse("class Main {static void main(){int x := 2;}}")
            .is_ok());
    }

    #[test]
    fn faulty_input() {
        assert!(parser::StatementsParser::new().parse("bool;").is_err());
        assert!(parser::StatementsParser::new().parse("2 := x;").is_err());
        assert!(parser::StatementsParser::new()
            .parse("if (x := 1) x := 1; else x := 2;")
            .is_err());
    }
}
