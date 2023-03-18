// use std::fs::File;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt;
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
enum Expr {
    Const {
        arg: u64,
    },
    Negate {
        arg: Box<Expr>,
    },
    BinOp {
        oper: Operator,
        arg1: Box<Expr>,
        arg2: Box<Expr>,
    },
    Var {
        arg: String,
    },
    If {
        discr: Box<Expr>,
        then: Box<Expr>,
        otherwise: Box<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Stmt {
    NetSend { arg: Box<Expr> },
    NetRecv { arg: String },
    Assign { arg: String, val: Box<Expr> },
    JumpZ { arg: Box<Expr>, location: usize },
    Halt { arg: Box<Expr> },
}

type Program = Vec<Stmt>;

// Not necessary, but these helpers are useful for syntactic cleanliness
fn netsend(e: Box<Expr>) -> Stmt {
    Stmt::NetSend { arg: e }
}

fn netrecv(x: &str) -> Stmt {
    Stmt::NetRecv { arg: x.to_string() }
}

fn assign(x: &str, v: Box<Expr>) -> Stmt {
    Stmt::Assign {
        arg: x.to_string(),
        val: v,
    }
}

// Hacky re-use of recv as a random (universally quantified) value
fn rand(x: &str) -> Stmt {
    Stmt::NetRecv { arg: x.to_string() }
}

fn jumpz(e: Box<Expr>, l: usize) -> Stmt {
    Stmt::JumpZ {
        arg: e,
        location: l,
    }
}

fn jump(l: usize) -> Stmt {
    Stmt::JumpZ {
        arg: con(0),
        location: l,
    }
}

fn halt(e: Box<Expr>) -> Stmt {
    Stmt::Halt { arg: e }
}

impl ops::Neg for Expr {
    type Output = Self;

    fn neg(self) -> Self {
        Expr::Negate {
            arg: Box::new(self),
        }
    }
}

impl ops::Add for Box<Expr> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Box::new(Expr::BinOp {
            oper: Operator::Add,
            arg1: self,
            arg2: other,
        })
    }
}

impl ops::Sub for Box<Expr> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Box::new(Expr::BinOp {
            oper: Operator::Sub,
            arg1: self,
            arg2: other,
        })
    }
}

impl ops::Mul for Box<Expr> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Box::new(Expr::BinOp {
            oper: Operator::Mul,
            arg1: self,
            arg2: other,
        })
    }
}

impl ops::Div for Box<Expr> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Box::new(Expr::BinOp {
            oper: Operator::Div,
            arg1: self,
            arg2: other,
        })
    }
}

fn equals(a: Box<Expr>, b: Box<Expr>) -> Box<Expr> {
    Box::new(Expr::BinOp {
        oper: Operator::Equal,
        arg1: a,
        arg2: b,
    })
}

fn con(v: u64) -> Box<Expr> {
    Box::new(Expr::Const { arg: v })
}

fn var(s: &str) -> Box<Expr> {
    Box::new(Expr::Var { arg: s.to_string() })
}

fn ite(discr: Box<Expr>, then: Box<Expr>, otherwise: Box<Expr>) -> Box<Expr> {
    Box::new(Expr::If {
        discr,
        then,
        otherwise,
    })
}

fn binop(oper: Operator, arg1: Box<Expr>, arg2: Box<Expr>) -> Box<Expr> {
    Box::new(Expr::BinOp { oper, arg1, arg2 })
}

fn negate(arg: Box<Expr>) -> Box<Expr> {
    Box::new(Expr::Negate { arg })
}

// A typical interpreter would use concrete intepretation of expressions.
// The interpreter below is for exemplificiation only and not the main interest.
fn interp_expr(e: Expr, env: &HashMap<String, u64>) -> u64 {
    match e {
        Expr::Const { arg } => arg,
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

// Finally we get to the real solution using symbolic execution. Our analysis system has
// a few layers:
// 1. Machine state which includes
//      - a Program to execute and program counter
//      - an environment (memory)
//      - a solver context
//      - variables for any non-memory properties we wish to check
// 2. A work queue of machine states so we can check more than a single trace through the program
#[derive(Clone, Debug)]
struct MachineState<'a> {
    program: Program,
    pc: usize,
    env: HashMap<String, z3::ast::Int<'a>>,
    // ctx: Context,
    solver: Solver<'a>,
    // Properties of interest:
    netsend_vals: VecDeque<z3::ast::Int<'a>>,
    halted: Option<z3::ast::Int<'a>>,
    path: VecDeque<bool>,
}

#[derive(Debug)]
struct WorkQueue<'a> {
    queue: VecDeque<MachineState<'a>>,
}

// Interpreting an expression can't have any side effects. There are no writes to memory, network
// sends, etc. The only thing an expression needs is the ability to evaluate - thus, ctx and env (memory)
fn symexec_expr<'a>(
    e: Expr,
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
            None => panic!("Undefined behavior found"), // or Int::from_u64(&ctx, 0), // A semantics choice that undefined means 0
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

// Symbolically interpreting the statements requires:
//  - Writing the symbolic value to the environment on assignment
//  - Asserting the zero and non-zero-ness of the value for jump-on-zero
//  - Update any flags tracking interesting facts we are proving such as halt, or sent values
fn symexec_stmt<'a>(s: Stmt, st: &MachineState<'a>, q: &mut WorkQueue<'a>) {
    // println!("PC: {}, Stmt: {:?}", st.pc, s);
    // st.solver.check();
    // let mdl = st.solver.get_model();
    // println!("Model: {:?}", mdl);
    if st.halted.is_none() {
        match s {
            Stmt::NetSend { arg } => {
                let mut new_machine_state = st.clone();
                let evaluated = symexec_expr(*arg, &st.env, st.solver.get_context());
                new_machine_state.netsend_vals.push_back(evaluated);
                new_machine_state.pc += 1;
                q.queue.push_back(new_machine_state);
            }
            Stmt::NetRecv { arg } => {
                let mut new_machine_state = st.clone();
                let recved_value = Int::fresh_const(
                    &new_machine_state.solver.get_context(),
                    &format!("Recv@{}", new_machine_state.pc),
                );
                new_machine_state.env.insert(arg, recved_value.clone());
                new_machine_state.pc += 1;
                q.queue.push_back(new_machine_state);
            }
            Stmt::Assign { arg, val } => {
                let mut new_machine_state = st.clone();
                let evaluated = symexec_expr(
                    *val,
                    &new_machine_state.env,
                    new_machine_state.solver.get_context(),
                );
                new_machine_state.env.insert(arg, evaluated);
                new_machine_state.pc += 1;
                q.queue.push_back(new_machine_state);
            }
            Stmt::JumpZ { arg, location } => {
                let result = symexec_expr(*arg, &st.env, st.solver.get_context());
                let mut jumping_machine_state = st.clone();
                jumping_machine_state
                    .solver
                    .assert(&result._eq(&Int::from_u64(
                        jumping_machine_state.solver.get_context(),
                        0,
                    )));
                if let SatResult::Sat = jumping_machine_state.solver.check() {
                    // let mdl_j = jumping_machine_state.solver.get_model();
                    // println!("Jumping Model: {:?}", mdl_j);
                    jumping_machine_state.pc = location;
                    jumping_machine_state.path.push_back(true);
                    q.queue.push_back(jumping_machine_state);
                }
                let mut non_jumping_machine_state = st.clone();
                non_jumping_machine_state.pc = non_jumping_machine_state.pc + 1;
                non_jumping_machine_state.solver.assert(
                    &result
                        ._eq(&Int::from_u64(
                            non_jumping_machine_state.solver.get_context(),
                            0,
                        ))
                        .not(),
                );
                if let SatResult::Sat = non_jumping_machine_state.solver.check() {
                    non_jumping_machine_state.path.push_back(false);
                    q.queue.push_back(non_jumping_machine_state)
                }
            }
            Stmt::Halt { arg } => {
                let mut new_machine_state = st.clone();
                new_machine_state.halted = Some(symexec_expr(
                    *arg,
                    &new_machine_state.env,
                    new_machine_state.solver.get_context(),
                ));
                q.queue.push_back(new_machine_state);
            }
        }
    }
}

fn symexec_program(prog: Program) {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let st0 = MachineState {
        program: prog,
        pc: 0,
        env: HashMap::new(),
        solver: Solver::new(&ctx),
        netsend_vals: VecDeque::new(),
        halted: None,
        path: VecDeque::new(),
    };
    let mut q = WorkQueue {
        queue: VecDeque::new(),
    };
    q.queue.push_front(st0);
    while let Some(curr_state) = q.queue.pop_front() {
        if let Some { .. } = curr_state.halted {
            // The only real output of this "analysis"
            match curr_state.solver.check() {
                SatResult::Sat => {
                    println!("Solution's Model:\n{:?}", curr_state.solver.get_model())
                }
                x => println!("{:?}", x),
            }
            break;
        }
        match curr_state.program.get(curr_state.pc) {
            None => {
                println!("Oh bother. We found a bad Jump or Stmts that end without Halt");
                return;
            }
            Some(stmt) => {
                symexec_stmt(stmt.clone(), &curr_state, &mut q);
            }
        }
    }
}

fn main() {
    let program = vec![
        netrecv("must_be_non_zero"), // 0
        assign(
            "tested_non_zero",
            ite(var("must_be_non_zero"), con(0), con(1)),
        ),
        jumpz(var("tested_non_zero"), 4), // 2
        jump(0),                          // 3
        rand("random"),                   // 4
        netsend(var("random")),           // 5
        netrecv("must_match_random_plus13_minute_non_zero"), // 6
        jumpz(
            var("random") + con(13)
                - var("must_be_non_zero")
                - var("must_match_random_plus13_minute_non_zero"),
            9,
        ),
        jump(0), // 8
        netrecv("computation of first two"), // 9
        jumpz(
            con(1)
                - equals(
                    var("computation of first two"),
                    var("random") * var("must_be_non_zero"),
                ),
            12,
        ),
        jump(0), // 11
        halt(con(0)),
    ];
    symexec_program(program);
}
