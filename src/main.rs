use log::LevelFilter;
use log::{debug, error, trace};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Error, Formatter};
use std::io;
use std::str::FromStr;

pub mod tree;

static mut VARS: Option<HashMap<String, Literal>> = None;

#[derive(Clone, Copy, PartialEq, Eq, Ord)]
enum Operator {
    Add,
    Sub,
    Mul,
    Div,
}

impl Debug for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Operator::Add => f.write_str("+"),
            Operator::Sub => f.write_str("-"),
            Operator::Mul => f.write_str("*"),
            Operator::Div => f.write_str("/"),
        }
    }
}

#[derive(Clone, Copy)]
enum Function {
    Sin,
    Cos,
}

impl Function {
    pub fn call(&self, x: f64) -> f64 {
        match self {
            Function::Sin => x.sin(),
            Function::Cos => x.cos(),
        }
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Function::Sin => f.write_str("sin"),
            Function::Cos => f.write_str("cos"),
        }
    }
}

impl FromStr for Function {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sin" => Ok(Function::Sin),
            "cos" => Ok(Function::Cos),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy)]
enum Constant {
    Pi,
    E,
}

impl Constant {
    pub fn eval(&self) -> f64 {
        match self {
            Constant::Pi => std::f64::consts::PI,
            Constant::E => std::f64::consts::E,
        }
    }
}

impl From<Constant> for Literal {
    fn from(c: Constant) -> Self {
        Literal::Num(c.eval())
    }
}

impl Debug for Constant {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Constant::Pi => f.write_str("π"),
            Constant::E => f.write_str("E"),
        }
    }
}

impl FromStr for Constant {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "pi" => Ok(Constant::Pi),
            "e" => Ok(Constant::E),
            _ => Err(()),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CharType {
    Digit,
    Alphabetic,
    Operator,
    Bracket,
}

#[derive(Clone)]
enum Literal {
    Num(f64),
    Str(String),
}

impl Literal {
    pub fn into_num(self) -> f64 {
        self.try_into().expect("Expected number")
    }
}

impl TryInto<f64> for Literal {
    type Error = ();

    fn try_into(self) -> Result<f64, ()> {
        match self {
            Literal::Num(n) => Ok(n),
            _ => Err(()),
        }
    }
}

impl Debug for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Literal::Num(n) => n.fmt(f),
            Literal::Str(s) => s.fmt(f),
        }
    }
}

#[derive(Clone)]
enum Token {
    Lit(Literal),
    Fn(Function),
    Const(Constant),
    Operator(Operator),
    Ident(String),
    OpenBracket,
    ClosedBracket,
}

impl Debug for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Token::Operator(o) => o.fmt(f),
            Token::Lit(l) => l.fmt(f),
            Token::Fn(fun) => fun.fmt(f),
            Token::Const(c) => c.fmt(f),
            Token::OpenBracket => f.write_str("("),
            Token::ClosedBracket => f.write_str(")"),
            Token::Ident(i) => f.write_str(&i),
        }
    }
}

impl TryFrom<Token> for Literal {
    type Error = ();

    fn try_from(t: Token) -> Result<Self, ()> {
        match t {
            Token::Const(c) => Ok(Literal::Num(c.eval())),
            Token::Lit(l) => Ok(l),
            Token::Ident(i) => Ok(unsafe {
                VARS.as_ref()
                    .unwrap()
                    .get(&i)
                    .map(|x| x.to_owned())
                    .expect("Unknown variable name")
            }),
            _ => Err(()),
        }
    }
}

impl Token {
    pub fn parse_num(num: &str) -> Result<Token, ()> {
        num.parse::<f64>()
            .map(|n| Token::Lit(Literal::Num(n)))
            .map_err(|e| trace!("try parse float error {}", e))
    }

    pub fn parse_alpha(s: &str) -> Result<Token, ()> {
        s.parse::<Function>()
            .map(|f| Token::Fn(f))
            .or(s.parse::<Constant>().map(|c| Token::Const(c)))
    }

    pub fn parse_operator(op: &str) -> Result<Token, ()> {
        op.parse::<Operator>().map(|o| Token::Operator(o))
    }

    pub fn parse_bracket(bracket: &str) -> Result<Token, ()> {
        if bracket == "(" {
            Ok(Token::OpenBracket)
        } else if bracket == ")" {
            Ok(Token::ClosedBracket)
        } else {
            Err(())
        }
    }

    pub fn char_type(c: char) -> CharType {
        if c.is_digit(10) || c == '.' {
            CharType::Digit
        } else if c.is_alphabetic() {
            CharType::Alphabetic
        } else if c == '+' || c == '-' || c == '*' || c == '/' {
            CharType::Operator
        } else if c == '(' || c == ')' {
            CharType::Bracket
        } else {
            panic!("Unknown char")
        }
    }

    pub fn consume(s: &str) -> Result<(Token, &str), ()> {
        if s.is_empty() {
            return Err(());
        }

        let mut len = 1usize;

        let mut curr_char_type = Self::char_type(s.chars().nth(0).unwrap());
        if curr_char_type != CharType::Bracket {
            loop {
                if !(len < s.len()) {
                    break;
                }
                let ct = Self::char_type(s.chars().nth(len).unwrap());
                if curr_char_type != ct {
                    break;
                } else {
                    len += 1;
                }
            }
        }

        s[..len].parse::<Token>().map(move |t| (t, &s[len..]))
    }

    pub fn parse_ident(s: &str) -> Result<Token, ()> {
        Ok(Token::Ident(s.to_owned()))
    }

    pub fn into_lit(self) -> Literal {
        match self {
            Token::Lit(lit) => lit,
            _ => panic!("Expected literal"),
        }
    }
}

impl FromStr for Token {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse_operator(s)
            .or(Self::parse_alpha(s))
            .or(Self::parse_num(s))
            .or(Self::parse_bracket(s))
            .or(Self::parse_ident(s))
    }
}

impl Operator {
    pub fn priority(&self) -> u32 {
        match self {
            Operator::Add | Operator::Sub => 1,
            Operator::Mul | Operator::Div => 2,
        }
    }

    pub fn apply(&self, a: f64, b: f64) -> f64 {
        match self {
            Operator::Add => a + b,
            Operator::Sub => a - b,
            Operator::Mul => a * b,
            Operator::Div => a / b,
        }
    }
}

impl PartialOrd for Operator {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.priority().partial_cmp(&other.priority())
    }
}

impl FromStr for Operator {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 1 {
            Err(())
        } else {
            match s {
                "+" => Ok(Operator::Add),
                "-" => Ok(Operator::Sub),
                "*" => Ok(Operator::Mul),
                "/" => Ok(Operator::Div),
                _ => Err(()),
            }
        }
    }
}

fn parse(mut program: &str) -> (Vec<Token>, Vec<String>) {
    let mut out: Vec<Token> = Vec::new();
    let mut stack: Vec<Token> = Vec::new();
    let mut vars: Vec<String> = vec![];

    while let Ok((token, s)) = Token::consume(program) {
        program = s;
        debug!("Parsed token {:?}. Rem: {}", token, program);

        match &token {
            Token::Lit(_) => out.push(token),
            Token::Fn(_) => stack.push(token),
            Token::Operator(operator) => {
                loop {
                    if let Some(t) = stack.last() {
                        let flag = match &t {
                            Token::Fn(_) => true,
                            Token::Operator(last_op) => last_op >= operator,
                            _ => false,
                        };
                        if flag {
                            out.push(stack.pop().unwrap())
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                stack.push(token);
            }
            Token::OpenBracket => stack.push(token),
            Token::ClosedBracket => {
                while let Some(t) = stack.pop() {
                    match t {
                        Token::OpenBracket => break,
                        _ => out.push(t),
                    }
                }
            }
            Token::Const(_) => out.push(token),
            Token::Ident(ident) => {
                vars.push(ident.clone());
                out.push(token);
            }
        };

        debug!("Out: {:?}", out);
        debug!("Stack: {:?}\n", stack);
    }

    debug!("Parsing ended");

    while let Some(token) = stack.pop() {
        out.push(token);
    }

    (out, vars)
}

fn main() {
    env_logger::Builder::new()
        .filter_level(LevelFilter::Debug)
        .init();

    unsafe {
        VARS = Some(HashMap::new());
    }

    let mut expr = "sin(pi*2)*sin(2*pi)+cos(2*pi)*cos(pi*2)+a";
    let (mut out, vars) = parse(&mut expr);
    debug!("Tokens: {:?}\n", out);

    for v in vars {
        let global_vars = unsafe { VARS.as_mut().unwrap() };
        if !global_vars.contains_key(&v) {
            println!("Enter value for var '{}': ", v);
            let mut input = String::new();
            io::stdin().read_line(&mut input).unwrap();
            let n: f64 = input.trim().parse().expect("Expected float number");
            global_vars.insert(v, Literal::Num(n));
        }
    }

    let mut stack: Vec<Token> = Vec::new();

    while let Some(token) = out.pop() {
        debug!("Processing {:?}", token);
        match token {
            Token::Operator(op) => {
                let b = out.last().expect("Expected b");
                let a = out.get(out.len() - 2).expect("Expected a");
                let op_a: Result<f64, _> = a.clone().try_into().and_then(|l: Literal| l.try_into());
                let op_b: Result<f64, _> = b.clone().try_into().and_then(|l: Literal| l.try_into());

                match (op_a, op_b) {
                    (Ok(a), Ok(b)) => {
                        out.pop();
                        out.pop();

                        let result = op.apply(a, b);
                        out.push(Token::Lit(Literal::Num(result)));

                        // move tokens from stack to output until new operator or fn is not found
                        while let Some(t) = stack.pop() {
                            match t {
                                Token::Operator(_) | Token::Fn(_) => {
                                    out.push(t);
                                    break;
                                }
                                _ => out.push(t),
                            }
                        }
                    }
                    _ => {
                        stack.push(token);
                    }
                }
            }
            Token::Fn(f) => {
                let t = out.pop().expect("Expected token");
                let n = match t {
                    Token::Lit(Literal::Num(n)) => n,
                    Token::Const(c) => c.eval(),
                    _ => {
                        out.push(t); // TODO: optimize?
                        stack.push(token);
                        debug!("Out: {:?}", out);
                        debug!("Stack: {:?}\n", stack);
                        continue;
                    }
                };
                let result = f.call(n);
                out.push(Token::Lit(Literal::Num(result)));
                // move tokens from stack to output until new operator or fn is not found
                while let Some(t) = stack.pop() {
                    match t {
                        Token::Operator(_) | Token::Fn(_) => {
                            out.push(t);
                            break;
                        }
                        _ => out.push(t),
                    }
                }
            }
            _ => {
                // not an operator, move to stack
                stack.push(token);
            }
        }
        debug!("Out: {:?}", out);
        debug!("Stack: {:?}\n", stack);
    }

    if let Some(v) = stack.pop() {
        println!("Asnwer {:?}", v);
    }
}
