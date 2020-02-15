use self::Token::*;
use crate::cursor::Cursor;
use crate::tokenizer::Function::{Cos, Sin};
use crate::VARS;
use lazy_static::lazy_static;
use log::debug;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap};
use std::convert::{TryFrom, TryInto};
use std::fmt::{Display, Error, Formatter, Pointer, Write};
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Div,
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
}

impl Display for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Operator::Add => f.write_str("+"),
            Operator::Sub => f.write_str("-"),
            Operator::Mul => f.write_str("*"),
            Operator::Div => f.write_str("/"),
            Operator::Assign => f.write_str("="),
            Operator::BangEq => f.write_str("≠"),
            Operator::Gt => f.write_str(">"),
            Operator::Lt => f.write_str("<"),
            Operator::GtEq => f.write_str("≥"),
            Operator::LtEq => f.write_str("≤"),
            Operator::EqEq => f.write_str("≡"),
            Operator::And => f.write_str("∧"),
            Operator::Or => f.write_str("∨"),
            Operator::Not => f.write_str("!"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Function {
    Sin,
    Cos,
}

impl Function {
    pub fn call(self, x: f64) -> f64 {
        match self {
            Function::Sin => x.sin(),
            Function::Cos => x.cos(),
        }
    }
}

impl Display for Function {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Constant {
    Pi,
    E,
}

impl Constant {
    pub fn eval(self) -> f64 {
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

impl Display for Constant {
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

#[derive(PartialEq, Clone, Debug)]
pub enum Literal {
    Num(f64),
    Str(String),
    Bool(bool),
}

impl Eq for Literal {}

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

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Literal::Num(n) => n.fmt(f),
            Literal::Str(s) => s.fmt(f),
            Literal::Bool(b) => b.fmt(f),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
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
    Semicol,
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        match self {
            Token::Operator(o) => o.fmt(f),
            Token::Lit(l) => l.fmt(f),
            Token::Fn(fun) => fun.fmt(f),
            Token::Const(c) => c.fmt(f),
            Token::Ident(i) => {
                f.write_char('`')?;
                f.write_str(&i)?;
                f.write_char('`')
            }
            Token::Kw(kw) => kw.fmt(f),
            Token::OpenParen => f.write_str("("),
            Token::ClosedParen => f.write_str(")"),
            Token::OpenBracket => f.write_str("{"),
            Token::ClosedBracket => f.write_str("}"),
            Token::OpenBrace => f.write_str("["),
            Token::ClosedBrace => f.write_str("]"),
            Token::Semicol => f.write_str(";"),
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
            (Lit(v0), Lit(v1)) => match (v0, v1) {
                (Literal::Bool(v0), Literal::Bool(v1)) => v0 == v1,
                _ => true,
            },
            (Ident(_), Ident(_))
            | (OpenParen, OpenParen)
            | (ClosedParen, ClosedParen)
            | (OpenBracket, OpenBracket)
            | (ClosedBracket, ClosedBracket)
            | (OpenBrace, OpenBrace)
            | (ClosedBrace, ClosedBrace)
            | (Semicol, Semicol) => true,
            _ => false,
        }
    }

    pub fn is_operator(&self) -> bool {
        matches!(self, Self::Operator(_))
    }

    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Lit(_))
    }

    pub fn is_ident(&self) -> bool {
        matches!(self, Self::Ident(_))
    }

    pub fn as_operator(&self) -> Option<Operator> {
        if let Self::Operator(op) = self {
            Some(*op)
        } else {
            None
        }
    }
}

impl Operator {
    pub fn priority(self) -> u32 {
        match self {
            Operator::Add | Operator::Sub => 1,
            Operator::Mul | Operator::Div => 2,
            _ => 0,
        }
    }
}

impl PartialOrd for Operator {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.priority().partial_cmp(&other.priority())
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
        debug!("Parsed token '{}'. Rem: {}", token, input);

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

            // TODO: parse floats
            // Numeric literal
            _c @ '0'..='9' => {
                let literal_kind = self.number();
                Lit(literal_kind)
            }

            '(' => OpenParen,
            ')' => ClosedParen,
            '{' => OpenBrace,
            '}' => ClosedBrace,
            '[' => OpenBracket,
            ']' => ClosedBracket,
            '-' => Operator(Operator::Sub),
            '+' => Operator(Operator::Add),
            '/' => Operator(Operator::Div),
            '*' => Operator(Operator::Mul),
            '=' => self.assign_or_eq(),
            ';' => Semicol,
            '!' => self.not_or_neq(),
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
        match self.bump() {
            Some('=') => Operator(Operator::EqEq),
            _ => Operator(Operator::Assign),
        }
    }

    fn not_or_neq(&mut self) -> Token {
        match self.bump() {
            Some('=') => Operator(Operator::BangEq),
            _ => Operator(Operator::Not),
        }
    }

    fn lt(&mut self) -> Token {
        match self.bump() {
            Some('=') => Operator(Operator::LtEq),
            _ => Operator(Operator::Lt),
        }
    }

    fn gt(&mut self) -> Token {
        match self.bump() {
            Some('=') => Operator(Operator::GtEq),
            _ => Operator(Operator::Gt),
        }
    }

    fn ident(&mut self) -> Token {
        // start is already eaten, eat the rest of identifier
        let _s = self.eat_while(is_id_continue);
        let string = self.take_collected();

        if let Some(kw) = KEYWORDS.get(string.as_str()) {
            Kw(*kw)
        } else {
            Ident(string)
        }
    }

    fn number(&mut self) -> Literal {
        let _s = self.eat_while(|x| x.is_digit(10));
        let string = self.take_collected();
        Literal::Num(string.parse().expect("Expected float"))
    }
}

#[test]
fn expr_formatting_test() -> Result<(), Error> {
    use crate::syntax::*;

    let exprs = vec![];
    let s = parenthesize("", &exprs)?;
    assert_eq!(&s, "()");

    let x = box Expr::Binary {
        left: box Expr::Unary {
            op: Operator::Sub,
            right: box Expr::Literal {
                lit: Literal::Num(1.0),
            },
        },
        op: Operator::EqEq,
        right: box Expr::Grouping {
            expr: box Expr::Literal {
                lit: Literal::Num(2.3),
            },
        },
    };

    let exprs = &[&*x][..];
    let s = parenthesize("", exprs)?;
    assert_eq!(&s, "( (≡ (- 1) (group 2.3)))");
    Ok(())
}

#[test]
fn test_tokenizer() -> Result<(), Error> {
    let ts: Vec<_> = tokenize("=").collect();
    assert_eq!(ts.as_slice(), &[Token::Operator(Operator::Assign)][..]);

    let ts: Vec<_> = tokenize("==").collect();
    assert_eq!(ts.as_slice(), &[Token::Operator(Operator::EqEq)][..]);

    let ts: Vec<_> = tokenize("!=").collect();
    assert_eq!(ts.as_slice(), &[Token::Operator(Operator::BangEq)][..]);

    let ts: Vec<_> = tokenize("1").collect();
    assert_eq!(ts.as_slice(), &[Token::Lit(Literal::Num(1.0))][..]);

    let ts: Vec<_> = tokenize("true false").collect();
    assert_eq!(
        ts.as_slice(),
        &[Token::Kw(Keyword::True), Token::Kw(Keyword::False)][..]
    );

    let ts: Vec<_> = tokenize("ident").collect();
    assert_eq!(ts.as_slice(), &[Token::Ident("ident".to_string())][..]);

    let ts: Vec<_> = tokenize("truee").collect();
    assert_eq!(ts.as_slice(), &[Token::Ident("truee".to_string())][..]);

    let ts: Vec<_> = tokenize("if a == true { b = 3 * -2; }").collect();
    let _x = ts.first().unwrap();
    assert_eq!(
        ts.as_slice(),
        &[
            Token::Kw(Keyword::If),
            Token::Ident("a".to_string()),
            Token::Operator(Operator::EqEq),
            Token::Kw(Keyword::True),
            Token::OpenBrace,
            Token::Ident("b".to_string()),
            Token::Operator(Operator::Assign),
            Token::Lit(Literal::Num(3.0)),
            Token::Operator(Operator::Mul),
            Token::Operator(Operator::Sub),
            Token::Lit(Literal::Num(2.0)),
            Token::Semicol,
            Token::ClosedBrace,
        ][..]
    );

    Ok(())
}
