use crate::tokenizer::{Token, Literal, Token::*, Operator, Keyword, tokenize};
use std::fmt::{self, Debug, Write, Formatter};
use log::debug;
use std::iter::Peekable;
use std::result;

#[derive(Debug, Clone, Copy)]
pub enum Error {
    ExpectedExpression
}

pub type Result<R> = result::Result<R, Error>;

pub enum Expr {
    Binary {
        left: Box<Expr>,
        op: Token,
        right: Box<Expr>,
    },
    Grouping {
        expr: Box<Expr>,
    },
    Literal {
        lit: Literal,
    },
    Unary {
        op: Token,
        right: Box<Expr>,
    },
}

static mut DBG_OBJ_PAD: usize = 0;

struct DbgObj {
    text: String,
}

impl DbgObj {
    pub fn new(d: impl Debug) -> Self {
        let pad = unsafe { DBG_OBJ_PAD += 2; DBG_OBJ_PAD };
        let padding: String = std::iter::repeat(' ').take(pad).collect();
        let s = format!("{}{:?}", padding, d);
        debug!("-> {}", s);
        DbgObj { text: s }
    }
}

impl Drop for DbgObj {
    fn drop(&mut self) {
        unsafe { DBG_OBJ_PAD -= 2; }
        debug!("<- {}", self.text);
    }
}

/**
Grammar:
Σ = { _number_, _bool_, -, +, *, (, ) }
N = { E, P, Q, V }
S = E
P:
    1. E ::= E O E
    1. O -> + | - | * | /

Name	       Operators	Associates
Unary	          ! -	      Right
Multiplication	  / *	      Left
Addition	      - +	      Left
Comparison	   > >= < <=	  Left
Equality	     == !=	      Left
*/
pub struct Parser<'a> {
    it: Peekable<Box<dyn Iterator<Item = Token> + 'a>>,
    prev: Option<Token>,
    curr: Option<Token>,
    ind: usize,
}

impl<'a> Parser<'a> {
    pub fn new(mut it: Box<dyn Iterator<Item = Token> + 'a>) -> Self {
        let first = it.next();
        Parser {
            it: it.peekable(),
            prev: None,
            curr: first,
            ind: 0,
        }
    }

    pub fn advance(&mut self) {
        self.prev = self.curr.take();
        self.curr = self.it.next();
    }

    pub fn consume(&mut self, t0: Token, err: &str) {
        match &self.curr {
            Some(t) if t.kind_like(&t0) => {
                self.advance();
            }
            _ => panic!("{}", err),
        }
    }

    pub fn matches_any(&mut self, ts: &[Token]) -> bool {
        match &self.curr {
            Some(t) => {
                for ti in ts {
                    if t.kind_like(ti) {
                        self.advance();
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    pub fn matches_1(&mut self, t0: Token) -> bool {
        self.matches_any(&[t0])
    }

    pub fn matches_2(&mut self, t0: Token, t1: Token) -> bool {
        self.matches_any(&[t0, t1])
    }

    pub fn primary(&mut self) -> Result<Box<Expr>> {
        let dobj = DbgObj::new("PRIMARY");

        if self.matches_1(Kw(Keyword::True)) {
            return Ok(box Expr::Literal {
                lit: Literal::Bool(true),
            });
        }

        if self.matches_1(Kw(Keyword::False)) {
            return Ok(box Expr::Literal {
                lit: Literal::Bool(false),
            });
        }

        match self.curr.clone() {
            Some(Lit(lit)) => {
                self.advance();
                return Ok(box Expr::Literal { lit: lit.clone() });
            }
            _ => {}
        }

        if self.matches_1(OpenParen) {
            let expr = self.expr();
            self.consume(ClosedParen, "Expected ')'");
            Ok(box Expr::Grouping { expr })
        } else {
            Err(Error::ExpectedExpression)
        }
    }

    pub fn unary(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("UNARY");

        if let Some(t) = &self.curr {
            match t {
                &Token::Operator(op) => {
                    match op {
                        Operator::Sub => (),
                        _ => panic!("Expected expression, found operator: {:?}", op)
                    }
                }
                _ => ()
            }
        }

        if self.matches_2(Not, Operator(Operator::Sub)) {
            let op = self.prev.clone().unwrap();
            let right = self.unary();
            box Expr::Unary { op, right }
        } else {
            self.primary().unwrap()
        }
    }

    pub fn mul_div(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("MUL");

        let mut expr = self.unary();
        while self.matches_2(Operator(Operator::Mul), Operator(Operator::Div)) {
            let op = self.prev.clone().expect("expected token").clone();
            let right = self.unary();
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        expr
    }

    pub fn add_sub(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("ADD");

        let mut expr = self.mul_div();
        while self.matches_2(Operator(Operator::Sub), Operator(Operator::Add)) {
            let op = self.prev.clone().expect("expected token").clone();
            let right = self.mul_div();
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        expr
    }

    pub fn comp(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("COMP");

        let mut expr = self.add_sub();
        while self.matches_any(&[Lt, Gt, LtEq, GtEq]) {
            let op = self.prev.clone().expect("expected token").clone();
            let right = self.add_sub();
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        expr
    }

    pub fn eq(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("EQ");

        let mut expr = self.comp();

        while self.matches_2(BangEq, EqEq) {
            let op = self.prev.clone().expect("expected token").clone();
            let right = self.comp();
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        expr
    }

    pub fn block_expr(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("BLOCK EXPR");
        self.consume(OpenBracket, "Expected '{'");
        let expr = self.expr();
        self.consume(ClosedBracket, "Expected '}'");
        expr
    }

    pub fn expr_without_block(&mut self) -> Box<Expr> {
        self.eq()
    }

    pub fn expr(&mut self) -> Box<Expr> {
//        let dobj = DbgObj::new("EXPR");
//        if self.matches_1(Keyword::If) {
//            let e = self.eq();
//            self.consume(OpenBracket)
//        }
        self.eq()
    }

    pub fn stmt(&mut self) -> Box<Expr> {
        let dobj = DbgObj::new("STMT");
        self.expr()
    }

    pub fn program(&mut self) -> Vec<Box<Expr>> {
//        self.it.peekable()
        let mut v = vec![];
        while self.curr.is_some() {
            v.push(self.stmt());
        }
        v
    }

    pub fn synchronize(&mut self) {
        self.advance();

        while self.it.peek().is_some() {
            if let Some(t) = &self.prev  {
                if t.kind_like(&Semicol) {
                    return;
                }
            }

            if let Some(t) = self.it.peek() {
                match t {
                    Kw(Keyword::Var) |
                        Kw(Keyword::If) |
                        Kw(Keyword::Fn) |
                        Kw(Keyword::Loop) |
                        Kw(Keyword::Ret) |
                        Kw(Keyword::Print) => return,
                    _ => ()
                }
            }

            self.advance();
        }
    }
}

pub fn parenthesize(name: &str, exprs: &Vec<&Box<Expr>>) -> result::Result<String, fmt::Error> {
    let mut f = String::new();
    f.write_char('(')?;
    f.write_str(name)?;
    for e in exprs {
        f.write_char(' ')?;
        write!(f, "{:?}", e)?;
    }
    f.write_char(')')?;
    Ok(f)
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            Expr::Binary { op, left, right } => {
                parenthesize(&format!("{:?}", op), &vec![left, right])?
            }
            Expr::Grouping { expr } => parenthesize("group", &vec![expr])?,
            Expr::Literal { lit } => format!("{:?}", lit),
            Expr::Unary { op, right } => parenthesize(&format!("{:?}", op), &vec![right])?,
        };
        f.write_str(&s)
    }
}

pub fn parse(mut program: &str) -> (Vec<Token>, Vec<String>) {
    let mut out: Vec<Token> = Vec::new();
    let mut stack: Vec<Token> = Vec::new();
    let mut vars: Vec<String> = vec![];

    let it = box tokenize(program);
    let mut parser = Parser::new(it);
    let e = parser.stmt();
    dbg!(e);

    (out, vars)
}