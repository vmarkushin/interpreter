use crate::cursor::Cursor;
use log::{debug, error, trace};
use std::cmp::Ordering;
use std::collections::{HashMap, BTreeMap};
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Error, Formatter};
use std::io;
use std::str::FromStr;
use crate::VARS;
use self::Token::*;
use crate::tokenizer::Function::{Sin, Cos};

#[derive(Clone, Copy, PartialEq, Eq, Ord)]
pub enum Operator {
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
pub enum Function {
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
pub enum Constant {
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

#[derive(Clone)]
pub enum Literal {
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
pub enum Token {
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
    pub fn into_lit(self) -> Literal {
        match self {
            Token::Lit(lit) => lit,
            _ => panic!("Expected literal"),
        }
    }
}

//impl FromStr for Token {
//    type Err = ();
//
//    fn from_str(s: &str) -> Result<Self, Self::Err> {
//        Self::parse_operator(s)
//            .or(Self::parse_alpha(s))
//            .or(Self::parse_num(s))
//            .or(Self::parse_bracket(s))
//            .or(Self::parse_ident(s))
//    }
//}

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

pub fn parse(mut program: &str) -> (Vec<Token>, Vec<String>) {
    let mut out: Vec<Token> = Vec::new();
    let mut stack: Vec<Token> = Vec::new();
    let mut vars: Vec<String> = vec![];

    for token in tokenize(program) {

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


pub enum Keyword {

}


pub fn tokenize(mut input: &str) -> impl Iterator<Item = Token> + '_ {
    std::iter::from_fn(move || {
        if input.is_empty() {
            return None;
        }

        let (mut token, len) = Cursor::new(input).advance_token();
        input = &input[len..];
        debug!("Parsed token {:?}. Rem: {}", token, input);

        let mut funcs: BTreeMap<String, Function> = BTreeMap::new();
        funcs.insert("sin".to_owned(), Sin);
        funcs.insert("cos".to_owned(), Cos);

        let mut kws: HashMap<String, Keyword> = HashMap::new();
//        funcs.insert("sin".to_owned(), Sin);
//        funcs.insert("cos".to_owned(), Cos);

        if let Ident(id) = &token {
            if let Some(f) = funcs.get(id).cloned() {
                token = Fn(f);
            }
        }

        Some(token)
    })
}

pub fn is_id_start(c: char) -> bool {
    c.is_ascii_alphabetic()
}

pub fn is_id_continue(c: char) -> bool {
    c.is_ascii_alphabetic()
        || c.is_digit(10)
}

impl<'a> Cursor<'a> {
    fn advance_token(&mut self) -> (Token, usize) {
        self.reset();
        let first_char = self.bump().unwrap();
        let token = match first_char {
            // Identifier
            c if is_id_start(c) => self.ident(),

            // Numeric literal
            c @ '0'..='9' => {
                let literal_kind = self.number();
                Lit(literal_kind)
            }

            '(' => OpenBracket,
            ')' => ClosedBracket,
            '-' => Operator(Operator::Sub),
            '+' => Operator(Operator::Add),
            '/' => Operator(Operator::Div),
            '*' => Operator(Operator::Mul),

            // String literal
//            '"' => {
//                let terminated = self.double_quoted_string();
//                let suffix_start = self.len_consumed();
//                if terminated {
//                    self.eat_literal_suffix();
//                }
//                let kind = Literal::Str(terminated);
//                Lit(kind)
//            }
            _ => panic!("Unknown token {}", first_char),
        };
        (token, self.len_consumed())
    }

    fn eat_while<F>(&mut self, mut predicate: F) -> usize
        where
            F: FnMut(char) -> bool,
    {
        let mut eaten: usize = 0;
        while predicate(self.first()) && !self.is_eof() {
            eaten += 1;
            self.bump();
        }

        eaten
    }

    fn ident(&mut self) -> Token {
        // start is already eaten, eat the rest of identifier
        let s = self.eat_while(is_id_continue);
        let string = self.take_collected();
        Ident(string)
    }

    fn number(&mut self) -> Literal {
        let s = self.eat_while(|x| x.is_digit(10));
        let string = self.take_collected();
        Literal::Num(string.parse().expect("Expected float"))
    }
}