use crate::syntax::Result;
use crate::syntax::{Error, Expr};
use crate::tokenizer::Literal::{self, *};
use crate::tokenizer::Operator::{self};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::ops::*;

impl Add<Literal> for Literal {
    type Output = Option<Literal>;

    fn add(self, rhs: Literal) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => Some(Num(a + b)),
            _ => None,
        }
    }
}

impl Sub<Literal> for Literal {
    type Output = Option<Literal>;

    fn sub(self, rhs: Literal) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => Some(Num(a - b)),
            _ => None,
        }
    }
}

impl Mul<Literal> for Literal {
    type Output = Option<Literal>;

    fn mul(self, rhs: Literal) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => Some(Num(a * b)),
            _ => None,
        }
    }
}

impl Div<Literal> for Literal {
    type Output = Option<Literal>;

    fn div(self, rhs: Literal) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => {
                if b == 0.0 {
                    return None;
                }
                Some(Num(a / b))
            }
            _ => None,
        }
    }
}

pub trait And<Rhs = Self> {
    type Output;

    fn and(self, rhs: Rhs) -> Self::Output;
}

pub trait Or<Rhs = Self> {
    type Output;

    fn or(self, rhs: Rhs) -> Self::Output;
}

impl And<Literal> for Literal {
    type Output = Option<Literal>;

    fn and(self, rhs: Literal) -> Self::Output {
        match (self, rhs) {
            (Bool(a), Bool(b)) => Some(Bool(a && b)),
            _ => None,
        }
    }
}

impl Or<Literal> for Literal {
    type Output = Option<Literal>;

    fn or(self, rhs: Literal) -> Self::Output {
        match (self, rhs) {
            (Bool(a), Bool(b)) => Some(Bool(a || b)),
            _ => None,
        }
    }
}

impl Not for Literal {
    type Output = Option<Literal>;

    fn not(self) -> Self::Output {
        match self {
            Bool(v) => Some(Bool(!v)),
            _ => None,
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Bool(a), Bool(b)) => a.partial_cmp(b),
            (Num(a), Num(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

#[derive(Default)]
pub struct Interpreter {
    pub vars: HashMap<String, Literal>,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter::default()
    }

    pub fn eval(&mut self, expr: Expr) -> Result<Literal> {
        match expr {
            Expr::Literal { lit } => Ok(lit),
            Expr::Binary { left, op, right } => {
                let l = self.eval(*left)?;
                let r = self.eval(*right)?;
                match op {
                    Operator::Add => l + r,
                    Operator::Sub => l - r,
                    Operator::Div => l / r,
                    Operator::Mul => l * r,
                    Operator::Assign => None,
                    Operator::BangEq => Some(Bool(l != r)),
                    Operator::EqEq => Some(Bool(l == r)),
                    Operator::Gt => Some(Bool(l > r)),
                    Operator::Lt => Some(Bool(l < r)),
                    Operator::GtEq => Some(Bool(l >= r)),
                    Operator::LtEq => Some(Bool(l <= r)),
                    Operator::And => l.and(r),
                    Operator::Or => l.or(r),
                    Operator::Not => panic!("Unexpected operator `!` in binary operator"),
                }
                .ok_or(Error::UnsopportedOperation)
            }
            Expr::Grouping { expr } => self.eval(*expr),
            Expr::Unary { op, right } => {
                let r = self.eval(*right)?;
                match op {
                    Operator::Sub => Literal::Num(-1.0) * r,
                    Operator::Not => !r,
                    _ => None,
                }
                .ok_or(Error::UnsopportedOperation)
            }
        }
    }
}

#[test]
pub fn test_interpret() {
    use crate::parse;

    let mut interpreter = Interpreter::new();

    //    let mut expr = "true == !false";
    //    let mut exprs = parse(&mut expr).pop().unwrap();
    //    let res = interpreter.eval(exprs).unwrap();
    //    assert_eq!(res, Literal::Bool(true));

    let mut expr = "1 - 2 * 3";
    let exprs = parse(&mut expr).pop().unwrap();
    let res = interpreter.eval(exprs).unwrap();
    assert_eq!(res, Literal::Num(-5.0));

    let mut expr = "(((1) - (2) * (3)))))";
    let exprs = parse(&mut expr).pop().unwrap();
    let res = interpreter.eval(exprs).unwrap();
    assert_eq!(res, Literal::Num(-5.0));

    let mut expr = "1 - (2 * 3)";
    let exprs = parse(&mut expr).pop().unwrap();
    let res = interpreter.eval(exprs).unwrap();
    assert_eq!(res, Literal::Num(-5.0));

    let mut expr = "(1 - 2) * 3";
    let exprs = parse(&mut expr).pop().unwrap();
    let res = interpreter.eval(exprs).unwrap();
    assert_eq!(res, Literal::Num(-3.0));

    let mut expr = "1 - (2 * 3) < 4";
    let exprs = parse(&mut expr).pop().unwrap();
    let res = interpreter.eval(exprs).unwrap();
    assert_eq!(res, Literal::Bool(true));

    //    let mut expr = "!(1 - (2 * 3) < 4)";
    //    let mut exprs = parse(&mut expr).pop().unwrap();
    //    let res = interpreter.eval(exprs).unwrap();
    //    assert_eq!(res, Literal::Bool(false));

    let mut expr = "1 - (2 * 3) < 4 != false";
    let exprs = parse(&mut expr).pop().unwrap();
    let res = interpreter.eval(exprs).unwrap();
    assert_eq!(res, Literal::Bool(true));
}
