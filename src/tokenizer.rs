use self::Token::*;
use crate::cursor::Cursor;
use crate::tokenizer::Function::{Cos, Sin};
use crate::VARS;
use lazy_static::lazy_static;
use log::{debug, error, trace};
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Error, Formatter, Pointer, Write};
use std::io;
use std::pin::Pin;
use std::process::exit;
use std::ptr::NonNull;
use std::str::FromStr;
use crate::syntax::{parenthesize, Expr};

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

#[derive(Clone, Copy, PartialEq, Eq)]
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

#[derive(Clone, Copy, PartialEq, Eq)]
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
            Constant::E => f.write_str("e"),
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
    Bool(bool),
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
            Literal::Bool(b) => b.fmt(f),
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
    Kw(Keyword),
    OpenParen,
    ClosedParen,
    OpenBracket,
    ClosedBracket,
    OpenBrace,
    ClosedBrace,
    Assign,
    BangEq,
    Not,
    Gt,
    Lt,
    GtEq,
    LtEq,
    EqEq,
    And,
    Or,
    Semicol,
}


impl Debug for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Token::Operator(o) => o.fmt(f),
            Token::Lit(l) => l.fmt(f),
            Token::Fn(fun) => fun.fmt(f),
            Token::Const(c) => c.fmt(f),
            Token::OpenParen => f.write_str("("),
            Token::ClosedParen => f.write_str(")"),
            Token::OpenBracket => f.write_str("{"),
            Token::ClosedBracket => f.write_str("}"),
            Token::OpenBrace => f.write_str("["),
            Token::ClosedBrace => f.write_str("]"),
            Token::Ident(i) => f.write_str(&i),
            Kw(kw) => kw.fmt(f),
            Assign => f.write_str("="),
            Semicol => f.write_str(";"),
            BangEq => f.write_str("≠"),
            Gt => f.write_str(">"),
            Lt => f.write_str("<"),
            GtEq => f.write_str("≥"),
            LtEq => f.write_str("≤"),
            EqEq => f.write_str("≡"),
            And => f.write_str("∧"),
            Or => f.write_str("∨"),
            Not => f.write_str("!"),
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

    pub fn kind_like(&self, other: &Token) -> bool {
        match (self, other) {
            (Fn(v0), Fn(v1)) => v0 == v1,
            (Const(v0), Const(v1)) => v0 == v1,
            (Operator(v0), Operator(v1)) => v0 == v1,
            (Kw(v0), Kw(v1)) => v0 == v1,
            (Lit(v0), Lit(v1)) => {
                match (v0, v1) {
                    (Literal::Bool(v0), Literal::Bool(v1)) => v0 == v1,
                    _ => true,
                }
            }
            (Ident(_), Ident(_))
            | (OpenParen, OpenParen)
            | (ClosedParen, ClosedParen)
            | (OpenBracket, OpenBracket)
            | (ClosedBracket, ClosedBracket)
            | (OpenBrace, OpenBrace)
            | (ClosedBrace, ClosedBrace)
            | (Assign, Assign)
            | (BangEq, BangEq)
            | (Not, Not)
            | (Gt, Gt)
            | (Lt, Lt)
            | (GtEq, GtEq)
            | (LtEq, LtEq)
            | (EqEq, EqEq)
            | (And, And)
            | (Or, Or)
            | (Semicol, Semicol) => true,
            _ => false,
        }
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

lazy_static! {
    static ref KEYWORDS: HashMap<&'static str, Keyword> = {
        let mut m = HashMap::new();
        m.insert("if", Keyword::If);
        m.insert("loop", Keyword::Loop);
        m.insert("var", Keyword::Var);
        m.insert("fn", Keyword::Fn);
        m.insert("ret", Keyword::Ret);
        m.insert("print", Keyword::Print);
        m.insert("true", Keyword::True);
        m.insert("false", Keyword::False);
        m
    };
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Keyword {
    If,
    Loop,
    Var,
    Fn,
    Ret,
    Print,
    True,
    False,
}

pub fn tokenize(mut input: &str) -> impl Iterator<Item = Token> + '_ {
    std::iter::from_fn(move || {
        if input.is_empty() {
            return None;
        }

        let (mut token, len) = Cursor::new(input).advance_token();
        input = &input[len..];
        debug!("Parsed token '{:?}'. Rem: {}", token, input);

        let mut funcs: BTreeMap<String, Function> = BTreeMap::new();
        funcs.insert("sin".to_owned(), Sin);
        funcs.insert("cos".to_owned(), Cos);

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
    c.is_ascii_alphabetic() || c.is_digit(10)
}

impl<'a> Cursor<'a> {
    fn advance_token(&mut self) -> (Token, usize) {
        self.reset();

        let mut first_char = self.bump().unwrap();
        while first_char.is_whitespace() {
            first_char = self.bump().unwrap();
        }

        let token = match first_char {
            // Identifier
            c if is_id_start(c) => self.ident(),

            // Numeric literal
            c @ '0'..='9' => {
                let literal_kind = self.number();
                Lit(literal_kind)
            }

            '(' => OpenParen,
            ')' => ClosedParen,
            '-' => Operator(Operator::Sub),
            '+' => Operator(Operator::Add),
            '/' => Operator(Operator::Div),
            '*' => Operator(Operator::Mul),
            '=' => self.assign_or_eq(),
            ';' => Semicol,
            '!' => Not,
            '<' => self.lt(),
            '>' => self.gt(),

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

    fn assign_or_eq(&mut self) -> Token {
        // TODO
        match self.bump().expect("expected") {
            '=' => EqEq,
            _ => Assign,
        }
    }

    fn lt(&mut self) -> Token {
        // TODO
        match self.bump().expect("expected") {
            '=' => LtEq,
            _ => Lt,
        }
    }

    fn gt(&mut self) -> Token {
        // TODO
        match self.bump().expect("expected") {
            '=' => GtEq,
            _ => Gt,
        }
    }

    fn ident(&mut self) -> Token {
        // start is already eaten, eat the rest of identifier
        let s = self.eat_while(is_id_continue);
        let string = self.take_collected();

        if let Some(kw) = KEYWORDS.get(string.as_str()) {
            Kw(*kw)
        } else {
            Ident(string)
        }
    }

    fn number(&mut self) -> Literal {
        let s = self.eat_while(|x| x.is_digit(10));
        let string = self.take_collected();
        dbg!(&string);
        Literal::Num(string.parse().expect("Expected float"))
    }
}

#[test]
fn expr_formatting_test() -> Result<(), Error> {
    let exprs = vec![];
    let s = parenthesize("", &exprs)?;
    assert_eq!(&s, "()");

    let x = box Expr::Binary {
        left: box Expr::Unary {
            op: Token::Operator(Operator::Sub),
            right: box Expr::Literal {
                lit: Literal::Num(1.0),
            },
        },
        op: Token::Operator(Operator::Mul),
        right: box Expr::Grouping {
            expr: box Expr::Literal {
                lit: Literal::Num(2.3),
            },
        },
    };

    let exprs = vec![&x];
    let s = parenthesize("", &exprs)?;
    assert_eq!(&s, "( (* (- 1.0) (group 2.3)))");
    Ok(())
}
