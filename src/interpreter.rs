use self::Value::*;
use crate::syntax::Expr;
use crate::syntax::Stmt;
use crate::tokenizer::Literal;
use crate::tokenizer::Operator::*;
use std::cmp::Ordering::{self, *};
use std::collections::HashMap;
use std::fmt::{self, Display};
use std::ops::*;
use std::result;
use self::Number::*;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error(display = "Runtime error.")]
pub enum Error {
    #[error(display = "unsupported operation `{}`", _0)]
    UnsupportedOperation(String),
    #[error(display = "undefined variable `{}`", _0)]
    UndefinedVar(String),
    #[error(display = "variable `{}` is null", _0)]
    NullVar(String),
    #[error(display = "expected type `bool`")]
    ExpectedBool,
}

pub type Result<R> = result::Result<R, Error>;

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Number {
    Int(i64),
    Float(f64),
}

impl Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Number::Int(n) => n.fmt(f),
            Number::Float(n) => n.fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null,
    Num(Number),
    Str(String),
    Bool(bool),
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Num(n) => n.fmt(f),
            Value::Str(s) => s.fmt(f),
            Value::Bool(b) => b.fmt(f),
            Value::Null => f.write_str("null"),
        }
    }
}

impl Add<Number> for Number {
    type Output = Option<Number>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Int(a), Int(b)) => Some(Int(a + b)),
            (Float(a), Float(b)) => Some(Float(a + b)),
            (Float(a), Int(b)) => Some(Float(a + b as f64)),
            (Int(a), Float(b)) => Some(Float(a as f64 + b)),
        }
    }
}

impl Add<Value> for Value {
    type Output = Option<Value>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => (a + b).map(Num),
            (Num(a), Str(b)) => Some(Str(format!("{}{}", a, b))),
            (Str(a), Str(b)) => Some(Str(format!("{}{}", a, b))),
            (Str(a), Num(b)) => Some(Str(format!("{}{}", a, b))),
            _ => None,
        }
    }
}

impl Sub<Number> for Number {
    type Output = Option<Number>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Int(a), Int(b)) => Some(Int(a - b)),
            (Float(a), Float(b)) => Some(Float(a - b)),
            (Float(a), Int(b)) => Some(Float(a - b as f64)),
            (Int(a), Float(b)) => Some(Float(a as f64 - b)),
        }
    }
}

impl Sub<Value> for Value {
    type Output = Option<Value>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => (a - b).map(Num),
            _ => None,
        }
    }
}

impl Mul<Number> for Number {
    type Output = Option<Number>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Int(a), Int(b)) => Some(Int(a * b)),
            (Float(a), Float(b)) => Some(Float(a * b)),
            (Float(a), Int(b)) => Some(Float(a * b as f64)),
            (Int(a), Float(b)) => Some(Float(a as f64 * b)),
        }
    }
}

impl Mul<Value> for Value {
    type Output = Option<Value>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => (a * b).map(Num),
            _ => None,
        }
    }
}

impl Div<Number> for Number {
    type Output = Option<Number>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Int(a), Int(b)) => {
                if b == 0 {
                    return None;
                }

                Some(Int(a / b))
            },
            (Float(a), Float(b)) => {
                if b == 0.0 {
                    return None;
                }

                Some(Float(a / b))
            },
            (Float(a), Int(b)) => {
                if b == 0 {
                    return None;
                }

                Some(Float(a / b as f64))
            },
            (Int(a), Float(b)) => {
                if b == 0.0 {
                    return None;
                }

                Some(Float(a as f64 / b))
            },
        }
    }
}

impl Div<Value> for Value {
    type Output = Option<Value>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Num(a), Num(b)) => {
                (a / b).map(Num)
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

impl And<Value> for Value {
    type Output = Option<Value>;

    fn and(self, rhs: Value) -> Self::Output {
        match (self, rhs) {
            (Bool(a), Bool(b)) => Some(Bool(a && b)),
            _ => None,
        }
    }
}

impl Or<Value> for Value {
    type Output = Option<Value>;

    fn or(self, rhs: Value) -> Self::Output {
        if let Bool(a) = self {
            if a {
                return Some(Bool(true));
            }
        }

        match (self, rhs) {
            (Bool(a), Bool(b)) => Some(Bool(a || b)),
            _ => None,
        }
    }
}

impl Not for Value {
    type Output = Option<Value>;

    fn not(self) -> Self::Output {
        match self {
            Bool(v) => Some(Bool(!v)),
            _ => None,
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Bool(a), Bool(b)) => a.partial_cmp(b),
            (Num(a), Num(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl From<Literal> for Value {
    fn from(l: Literal) -> Self {
        match l {
            Literal::Num(v) => Num(v),
            Literal::Str(v) => Str(v),
            Literal::Bool(v) => Bool(v),
        }
    }
}

#[derive(Debug, Default)]
pub struct Env {
    vars: HashMap<String, Value>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn define(&mut self, name: String, val: Value) {
        self.vars.insert(name, val);
    }

    pub fn assign(&mut self, name: &str, val: Value) -> Result<()> {
        if !self.vars.contains_key(name) {
            return Err(Error::UndefinedVar(name.to_owned()));
        }
        self.vars.insert(name.to_owned(), val);
        Ok(())
    }

    pub fn get(&self, name: &str) -> Option<&Value> {
        self.vars.get(name)
    }
}

#[derive(Default)]
pub struct Interpreter {
    pub env: Env,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter::default()
    }

    pub fn eval(&self, expr: &Expr) -> Result<Value> {
        match expr {
            Expr::Literal { lit } => Ok(lit.clone().into()),
            Expr::Binary { left, op, right } => {
                if op == &And || op == &Or {
                    // use short-circuit evaluation for boolean operators
                    match op {
                        And => {
                            let l = self.eval(left)?;
                            if let Bool(a) = l {
                                if !a {
                                    Some(Bool(false))
                                } else {
                                    let r = self.eval(right)?;
                                    if let Bool(b) = r {
                                        Some(Bool(b))
                                    } else {
                                        None
                                    }
                                }
                            } else {
                                None
                            }
                        }
                        Or => {
                            let l = self.eval(left)?;
                            if let Bool(a) = l {
                                if a {
                                    Some(Bool(true))
                                } else {
                                    let r = self.eval(right)?;
                                    if let Bool(b) = r {
                                        Some(Bool(b))
                                    } else {
                                        None
                                    }
                                }
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    let l = self.eval(left)?;
                    let r = self.eval(right)?;
                    match op {
                        Plus => l + r,
                        Minus => l - r,
                        Slash => l / r,
                        Star => l * r,
                        Eq => None,
                        BangEq => Some(Bool(l != r)),
                        EqEq => Some(Bool(l == r)),
                        Gt => l.partial_cmp(&r).map(|o| Bool(o == Greater)),
                        Lt => l.partial_cmp(&r).map(|o| Bool(o == Less)),
                        GtEq => l.partial_cmp(&r).map(|o| Bool(o == Greater || o == Equal)),
                        LtEq => l.partial_cmp(&r).map(|o| Bool(o == Less || o == Equal)),
                        ExMark => panic!("Unexpected unary operator `!` in binary operation"),
                        And | Or => unreachable!(),
                    }
                }
                .ok_or_else(|| Error::UnsupportedOperation(format!("{}", op)))
            }
            Expr::Grouping { expr } => self.eval(expr),
            Expr::Unary { op, right } => {
                let r = self.eval(right)?;
                match op {
                    Minus => Value::from(Literal::Num(Int(-1))) * r,
                    ExMark => !r,
                    _ => None,
                }
                .ok_or_else(|| Error::UnsupportedOperation(format!("{}", op)))
            }
            Expr::Var(var) => self
                .env
                .get(&var.lexeme)
                .cloned()
                .ok_or_else(|| Error::UndefinedVar(var.lexeme.clone())),
        }
    }

    pub fn execute(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Expr(e) => {
                self.eval(e)?;
            }
            Stmt::Print(e) => {
                let val = self.eval(e)?;
                println!("{}", val);
            }
            Stmt::Read(meta) => {
                let var_name = &meta.lexeme;
                let old_val = self
                    .env
                    .get(var_name)
                    .ok_or_else(|| Error::UndefinedVar(var_name.clone()))?;
                let mut s = String::new();
                std::io::stdin()
                    .read_line(&mut s)
                    .expect("can't read from stdin");
                let s = s.trim().to_owned();
                let val = match old_val {
                    Null => Value::Str(s),
                    Num(Float(_)) => s.parse::<f64>().map(|x| Value::Num(Float(x))).unwrap_or(Value::Str(s)),
                    Num(Int(_)) => s.parse::<i64>().map(|x| Value::Num(Int(x))).unwrap_or(Value::Str(s)),
                    Str(_) => Value::Str(s),
                    Bool(_) => s.parse::<bool>().map(Value::Bool).unwrap_or(Value::Str(s)),
                };
                self.env.assign(var_name, val)?;
            }
            Stmt::VarDecl { name, initializer } => {
                let val = if let Some(init) = initializer {
                    self.eval(init)?
                } else {
                    Null
                };
                self.env.define(name.lexeme.clone(), val);
            }
            Stmt::VarAssign { name, value } => {
                self.env.assign(&name.lexeme, self.eval(value)?)?;
            }
            Stmt::If {
                cond,
                then,
                otherwise,
            } => {
                let val = self.eval(cond)?;
                match val {
                    Bool(b) => {
                        if b {
                            for stmt in then {
                                self.execute(stmt)?;
                            }
                        } else if let Some(other) = otherwise {
                            for stmt in other {
                                self.execute(stmt)?;
                            }
                        }
                    }
                    _ => return Err(Error::ExpectedBool),
                }
            }
            Stmt::While { cond, actions } => loop {
                let val = self.eval(&cond)?;
                match val {
                    Bool(b) => {
                        if b {
                            for stmt in actions {
                                self.execute(stmt)?;
                            }
                        } else {
                            break;
                        }
                    }
                    _ => return Err(Error::ExpectedBool),
                }
            },
        };
        Ok(())
    }

    pub fn interpret(&mut self, stmts: &[Stmt]) -> Result<()> {
        for stmt in stmts {
            self.execute(stmt)?;
        }
        Ok(())
    }
}

mod tests {
    use super::Value::*;
    use super::Number::*;
    use super::{Error, Interpreter};

    #[test]
    pub fn test_vars() -> Result<(), crate::Error> {
        use crate::parse;
        let mut interpreter = Interpreter::new();

        let program = "var a = 1;";
        let stmts = parse(&program).unwrap();
        interpreter.interpret(&stmts)?;
        assert_eq!(interpreter.env.vars.get("a").unwrap(), &Num(Int(1)));

        let program = "a = 2;";
        let stmts = parse(&program).unwrap();
        interpreter.interpret(&stmts)?;
        assert_eq!(interpreter.env.vars.get("a").unwrap(), &Num(Int(2)));

        let program = "var a = 0;";
        let stmts = parse(&program).unwrap();
        interpreter.interpret(&stmts)?;
        assert_eq!(interpreter.env.vars.get("a").unwrap(), &Num(Int(0)));

        let program = "b = 0;";
        let stmts = parse(&program).unwrap();
        let error = interpreter.interpret(&stmts).err().unwrap();
        assert_eq!(error, Error::UndefinedVar("b".into()));

        let program = "var b = a;";
        let stmts = parse(&program).unwrap();
        interpreter.interpret(&stmts)?;
        assert_eq!(
            interpreter.env.vars.get("b").unwrap(),
            interpreter.env.vars.get("a").unwrap()
        );

        let program = "var b = a = 3;";
        let error = parse(&program).err().unwrap();
        assert_eq!(
            error,
            crate::syntax::Error::ExpectedSemicol("variable declaration".into())
        );

        Ok(())
    }

    #[test]
    pub fn test_interpreter() -> Result<(), crate::Error> {
        use crate::parse;

        let mut interpreter = Interpreter::new();

        // TODO: expressions, starting operator
        // let mut expr = "true == !false";
        // let mut expr = parse(&mut expr)?.pop().unwrap().into_expr();
        // let res = interpreter.eval(&expr)?;
        // assert_eq!(res, Bool(true));

        let mut expr = "1 - 2 * 3;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Int(-5)));

        let mut expr = "1 - 2 * 3.0;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Float(-5.0)));

        let mut expr = "-2;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Int(-2)));

        let mut expr = "-2 * 3;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Int(-6)));

        let mut expr = "(( (1) - (2) * (3) ));";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Int(-5)));

        let mut expr = "1 - (2 * 3);";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Int(-5)));

        let mut expr = "(1 - 2) * 3;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Num(Int(-3)));

        let mut expr = "1 - (2 * 3) < 4;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "true && true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "false && true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        let mut expr = "false && false;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        let mut expr = "true && false;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        let mut expr = "true || true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "false || true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "true || false;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "false || false;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        let mut expr = "false || false || true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "false || true && true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "1 < 2 && 2 < 3;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "1 < 2 && 2 > 3;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        let mut expr = "1 + 1 < 2 + 1 && 2 - 1 > 3 - 1;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        let mut expr = "1 == 1 && true;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "1 == 1 == 1;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(false));

        // TODO: expressions, starting with operator

        //    let mut expr = "!(1 - (2 * 3) < 4)";
        //    let mut exprs = parse(&mut expr)?.pop().unwrap().into_expr();
        //    let res = interpreter.eval(exprs)?;
        //    assert_eq!(res, Bool(false));

        let mut expr = "1 - (2 * 3) < 4 != false;";
        let expr = parse(&mut expr)?.pop().unwrap().into_expr();
        let res = interpreter.eval(&expr)?;
        assert_eq!(res, Bool(true));

        let mut expr = "print 1 - (2 * 3) < 4 != false;";
        let stmt = parse(&mut expr)?;
        interpreter.interpret(&stmt)?;

        Ok(())
    }
}
