use std::cmp::Ordering;
use std::str::FromStr;
use log::LevelFilter;
use log::{debug, error, trace};
use std::fmt::{Debug, Formatter, Error};

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
        match self {
            Literal::Num(n) => n,
            _ => panic!("Expected number")
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
        }
    }
}

impl Token {
    pub fn parse_num(num: &str) -> Result<Token, ()> {
        num.parse::<f64>().map(|n| Token::Lit(Literal::Num(n))).map_err(|e| trace!("try parse float error {}", e))
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
        if s.is_empty()  {
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

    pub fn into_lit(self) -> Literal {
        match self {
            Token::Lit(lit) => lit,
            _ => panic!("Expected literal")
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
            _ => unreachable!(),
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

fn main() {
    env_logger::Builder::new().filter_level(LevelFilter::Debug).init();

    let mut expr = "pi*2";
    let mut out: Vec<Token> = Vec::new();
    let mut stack: Vec<Token> = Vec::new();

    while let Ok((token, s)) = Token::consume(&expr) {
        expr = s;
        debug!("Parsed token {:?}. Rem: {}", token, expr);

        match &token {
            Token::Lit(_) => out.push(token),
            Token::Fn(_) => stack.push(token),
            Token::Operator(operator) => {
                loop {
                    if let Some(t) = stack.last() {
                        let flag = match &t {
                            Token::Fn(_) => true,
                            Token::Operator(last_op) => {
                                last_op >= operator
                            },
                            _ => false
                        };
                        if flag {
                            out.push(stack.pop().unwrap())
                        } else {
                            break
                        }
                    } else {
                        break;
                    }
                }
                stack.push(token);
            },
            Token::OpenBracket => stack.push(token),
            Token::ClosedBracket => {
                while let Some(t) = stack.pop() {
                    match t {
                        Token::OpenBracket => break,
                        _ => out.push(t),
                    }
                }
            },
            Token::Const(_) => out.push(token),
        };

        debug!("Out: {:?}", out);
        debug!("Stack: {:?}\n", stack);
    }

    debug!("Parsing ended");

    while let Some(token) = stack.pop() {
        out.push(token);
    }

    while let Some(token) = out.pop() {
        match token {
            Token::Operator(op) => {
                let b = out.last().expect("Expected b");
                let a = out.get(out.len() - 2).expect("Expected a");
                let operands = match (a, b) {
                    (Token::Lit(Literal::Num(a)), Token::Lit(Literal::Num(b))) => {
                        Some((*a, *b))
                    }
                    (Token::Const(a), Token::Lit(Literal::Num(b))) => {
                        Some((a.eval(), *b))
                    }
                    (Token::Lit(Literal::Num(a)), Token::Const(b)) => {
                        Some((*a, b.eval()))
                    }
                    (Token::Const(a), Token::Const(b)) => {
                        Some((a.eval(), b.eval()))
                    }
                    _ => None
                };
                match operands {
                    Some((a, b)) => {
                        out.pop();
                        out.pop();

                        let result = op.apply(a, b);
                        out.push(Token::Lit(Literal::Num(result)));

                        // move tokens from stack to output until new operator is not found
                        while let Some(t) = stack.pop() {
                            match t {
                                Token::Operator(_) => {
                                    out.push(t);
                                    break;
                                },
                                _ => out.push(t)
                            }
                        }
                    },
                    None => {
                        stack.push(token);
                    }
                }
            }
            _ => { // not an operator, move to stack
                stack.push(token);
            }
        }
        debug!("Out: {:?}", out);
        debug!("Stack: {:?}\n", stack);
    }
}
