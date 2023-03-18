// use std::fs::File;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::marker::PhantomData;
use std::ops;
use z3::ast::Ast;
use z3::ast::Int;
use z3::SatResult;
use z3::Solver;
use z3::{Config, Context};

// First we define the language we'll be interpreting and proving properties about.
// - Expressions: computation that can read memory
// - Statements: Operations that interact with the world (print, network ops, write to memory or PC)
// - Programs: mapping of locations to basic blocks
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Operator {
    Add,
    Sub,
    Div,
    Mul,
    Equal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr<E> {
    Const {
        arg: u64,
        phantom: PhantomData<E>,
    },
    Negate {
        arg: Box<Expr<E>>,
    },
    BinOp {
        oper: Operator,
        arg1: Box<Expr<E>>,
        arg2: Box<Expr<E>>,
    },
    Var {
        arg: String,
    },
    If {
        discr: Box<Expr<E>>,
        then: Box<Expr<E>>,
        otherwise: Box<Expr<E>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Stmt<E> {
    NetSend { arg: Box<Expr<E>> },
    Assign { arg: String, val: Box<Expr<E>> },
    JumpZ { arg: Box<Expr<E>>, location: usize },
    Halt { arg: Box<Expr<E>> },
}

type Program<E> = Vec<Stmt<E>>;

// Not necessary, but these helpers are useful for syntactic cleanliness
impl<E> ops::Neg for Expr<E> {
    type Output = Self;

    fn neg(self) -> Self {
        Expr::Negate {
            arg: Box::new(self),
        }
    }
}

impl<E> ops::Add for Expr<E> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Expr::BinOp {
            oper: Operator::Add,
            arg1: Box::new(self),
            arg2: Box::new(other),
        }
    }
}

impl<E> ops::Sub for Expr<E> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Expr::BinOp {
            oper: Operator::Sub,
            arg1: Box::new(self),
            arg2: Box::new(other),
        }
    }
}

impl<E> ops::Mul for Expr<E> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Expr::BinOp {
            oper: Operator::Mul,
            arg1: Box::new(self),
            arg2: Box::new(other),
        }
    }
}

impl<E> ops::Div for Expr<E> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Expr::BinOp {
            oper: Operator::Div,
            arg1: Box::new(self),
            arg2: Box::new(other),
        }
    }
}

fn equals<E>(a: Expr<E>, b: Expr<E>) -> Expr<E> {
    Expr::BinOp {
        oper: Operator::Equal,
        arg1: Box::new(a),
        arg2: Box::new(b),
    }
}

// Concrete intepretation of expressions
fn interp_expr(e: Expr<u64>, env: &HashMap<String, u64>) -> u64 {
    match e {
        Expr::Const { arg, phantom } => arg,
        Expr::Negate { arg } => u64::MAX - interp_expr(*arg, &env),
        Expr::BinOp { oper, arg1, arg2 } => {
            let v1 = interp_expr(*arg1, &env);
            let v2 = interp_expr(*arg2, &env);
            match oper {
                Operator::Add => v1 + v2,
                Operator::Sub => v1 - v2,
                Operator::Mul => v1 * v2,
                Operator::Div => v1 / v2,
                Operator::Equal => {
                    if v1 == v2 {
                        1
                    } else {
                        0
                    }
                }
            }
        }
        Expr::Var { arg } => match env.get(&arg) {
            Some(val) => *val,
            None => 0, // A semantics choice
        },
        Expr::If {
            discr,
            then,
            otherwise,
        } => {
            if interp_expr(*discr, &env) != 0 {
                interp_expr(*then, &env)
            } else {
                interp_expr(*otherwise, env)
            }
        }
    }
}

// Finally we get to the real solution using symbolic execution. Our symbolic execution system has
// a few layers:
// 1. Machine state which includes
//      - a Program to execute and program counter
//      - an environment (memory)
//      - a solver context, and
//      - variables for any non-memory properties we wish to check
// 2. A work queue of machine states so we can check more than a single trace through the program
#[derive(Clone, Debug)]
struct MachineState<'a> {
    program: Program<u64>,
    pc: usize,
    env: HashMap<String, z3::ast::Int<'a>>,
    // ctx: Context,
    solver: Solver,
    // Properties of interest:
    netsend_vals: VecDeque<z3::ast::Int<'a>>,
    has_paniced: z3::ast::Int<'a>,
    halted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct WorkQueue<'a> {
    queue: VecDeque<MachineState<'a>>,
}

fn symexec_expr<'a>(
    e: Expr<u64>,
    env: &HashMap<String, z3::ast::Int<'a>>,
    ctx: &'a Context,
) -> z3::ast::Int<'a> {
    match e {
        Expr::Const { arg, .. } => Int::from_u64(&ctx, arg),
        Expr::Negate { arg } => symexec_expr(*arg, &env, ctx).unary_minus(),
        Expr::BinOp { oper, arg1, arg2 } => {
            let v1 = symexec_expr(*arg1, &env, ctx);
            let v2 = symexec_expr(*arg2, &env, ctx);
            match oper {
                Operator::Add => v1 + v2,
                Operator::Sub => v1 - v2,
                Operator::Mul => v1 * v2,
                Operator::Div => v1 / v2,
                Operator::Equal => v1
                    ._eq(&v2)
                    .ite(&Int::from_u64(&ctx, 1), &Int::from_u64(&ctx, 0)),
            }
        }
        Expr::Var { arg } => match env.get(&arg) {
            Some(val) => val.clone(),
            None => Int::from_u64(&ctx, 0), // A semantics choice that undefined means 0
        },
        Expr::If {
            discr,
            then,
            otherwise,
        } => symexec_expr(*discr, &env, ctx)
            ._eq(&Int::from_u64(&ctx, 0))
            .not()
            .ite(
                &symexec_expr(*then, &env, ctx),
                &symexec_expr(*otherwise, &env, ctx),
            ), // if symexec_expr(*discr, &env, ctx) != 0 {
               //     symexec_expr(*then, &env, ctx)
               // } else {
               //     symexec_expr(*otherwise, env, ctx)
               // }
    }
}

// Symbolically interpreting the statements requires us to write the symbolic expressions requires:
//  - Writing the symbolic value to the environment on assignment
//  - Asserting the zero and non-zero-ness of the value for jump-on-zero
//  - Update any flags tracking interesting facts we are proving such as halt, or sent values
fn symexec_stmt<'a>(s: Stmt<u64>, st: MachineState<'a>, q: &mut WorkQueue<'a>) {
    if st.halted {
        match s {
            Stmt::NetSend { arg } => {}
            Stmt::Assign { arg, val } => {
                let mut new_machine_state = st.clone();
                new_machine_state.env.insert(arg, val);
                q.push_front(new_machine_state);
            }
            Stmt::JumpZ { arg, location } => {
                if let Some(exprVal) = st.env.lookup(arg) {
                    let mut jumping_machine_state = st.clone();
                    jumping_machine_state
                        .solver
                        .assert(symexec_expr(exprVal, &st.env, st.solver.get_context()) == 0);
                    if let SatResult::Sat = jumping_machine_state.solver.check() {
                        jumping_machine_state.pc = location;
                        q.push_front(new_machine_state);
                    }
                }
                let non_jumping_machine_state = st.clone();
                non_jumping_machine_state.pc = st.location + 1;
                if let Some(exprVal) = non_jumping_machine_state.env.lookup(arg) {
                    non_jumping_machine_state
                        .assert(symexec_expr(exprVal, &st.env, st.solver.get_context()) != 0);
                }
                if let SatResult::Sat = non_jumping_machine_state.solver.check() {
                    q.push_front(new_machine_state)
                }
            }
            Stmt::Halt => {
                let new_machine_state = st.clone().halted = true;
                q.push_front(new_machine_state);
            }
        }
    }
}

fn main_symexec(e: Expr<u64>) {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let res = symexec_expr(e, &HashMap::new(), &ctx);
    let solver = Solver::new(&ctx);
    solver.check();
    println!("{:?}", solver.get_model());
}

fn con(v: u64) -> Box<Expr<u64>> {
    Box::new(Expr::Const {
        arg: v,
        phantom: PhantomData,
    })
}

fn binop<E>(oper: Operator, arg1: Box<Expr<E>>, arg2: Box<Expr<E>>) -> Box<Expr<E>> {
    Box::new(Expr::BinOp { oper, arg1, arg2 })
}

fn negate<E>(arg: Box<Expr<E>>) -> Box<Expr<E>> {
    Box::new(Expr::Negate { arg })
}

fn main() {
    let e = Box::new(Expr::If {
        discr: con(0),
        then: { con(0) },
        otherwise: binop(Operator::Add, con(42), con(32)),
    });
    let e2 = e.clone();
    println!("{:?}", interp_expr(*e, &HashMap::new()));
    main_symexec(*e2)
}
