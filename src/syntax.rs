use crate::tokenizer::{
    tokenize, Keyword, Literal,
    Operator::{self, *},
    Token,
    Token::*,
};
use log::debug;
use std::fmt::{self, Display, Formatter, Write, Pointer};
use std::iter::Peekable;
use std::result;

#[derive(Debug, Clone, Copy)]
pub enum Error {
    ExpectedExpression,
    UnsopportedOperation,
}

pub type Result<R> = result::Result<R, Error>;

#[derive(Debug)]
pub enum Stmt {
    Expr(Expr),
    Print(Expr),
}

impl Stmt {
    pub fn into_expr(self) -> Expr {
        if let Stmt::Expr(e) = self {
            e
        } else {
            panic!("Expected expression")
        }
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Expr(e) | Stmt::Print(e) => e.fmt(f),
        }
    }
}

pub fn display_arr<T: Display>(arr: &[T]) {
    for s in arr {
        println!("{}", s);
    }
}

#[derive(Debug)]
pub enum Expr {
    Binary {
        left: Box<Expr>,
        op: Operator,
        right: Box<Expr>,
    },
    Grouping {
        expr: Box<Expr>,
    },
    Literal {
        lit: Literal,
    },
    Unary {
        op: Operator,
        right: Box<Expr>,
    },
}

static mut DBG_OBJ_PAD: usize = 0;

struct DbgObj {
    text: String,
}

impl DbgObj {
    pub fn new(d: impl Display) -> Self {
        let pad = unsafe {
            DBG_OBJ_PAD += 2;
            DBG_OBJ_PAD
        };
        let padding: String = std::iter::repeat(' ').take(pad).collect();
        let s = format!("{}{}", padding, d);
        debug!("-> {}", s);
        DbgObj { text: s }
    }
}

impl Drop for DbgObj {
    fn drop(&mut self) {
        unsafe {
            DBG_OBJ_PAD -= 2;
        }
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

Name            Operators    Associates
Unary             ! -         Right
Multiplication    / *         Left
Addition          - +         Left
Comparison     > >= < <=      Left
Equality         == !=        Left
*/
pub struct Parser<'a> {
    it: Peekable<Box<dyn Iterator<Item = Token> + 'a>>,
    prev: Option<Token>,
    curr: Option<Token>,
}

impl<'a> Parser<'a> {
    pub fn new(mut it: Box<dyn Iterator<Item = Token> + 'a>) -> Self {
        let first = it.next();
        Parser {
            it: it.peekable(),
            prev: None,
            curr: first,
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
        let _dobj = DbgObj::new("PRIMARY");

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

        #[allow(clippy::single_match)]
        match self.curr.clone() {
            Some(Lit(lit)) => {
                self.advance();
                return Ok(box Expr::Literal { lit });
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
        let _dobj = DbgObj::new("UNARY");

        if let Some(t) = &self.curr {
            #[allow(clippy::single_match)]
            match *t {
                Token::Operator(op) => match op {
                    Sub => (),
                    _ => panic!("Expected expression, found operator: {:?}", op),
                },
                _ => (),
            }
        }

        if self.matches_2(Operator(Not), Operator(Sub)) {
            let op = self
                .prev
                .clone()
                .unwrap()
                .as_operator()
                .expect("expected operator");
            let right = self.unary();
            box Expr::Unary { op, right }
        } else {
            self.primary().unwrap()
        }
    }

    pub fn mul_div(&mut self) -> Box<Expr> {
        let _dobj = DbgObj::new("MUL");

        let mut expr = self.unary();
        while self.matches_2(Operator(Mul), Operator(Div)) {
            let op = self
                .prev
                .clone()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
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
        let _dobj = DbgObj::new("ADD");

        let mut expr = self.mul_div();
        while self.matches_2(Operator(Sub), Operator(Add)) {
            let op = self
                .prev
                .clone()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
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
        let _dobj = DbgObj::new("COMP");

        let mut expr = self.add_sub();
        while self.matches_any(&[Operator(Lt), Operator(Gt), Operator(LtEq), Operator(GtEq)]) {
            let op = self
                .prev
                .clone()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
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
        let _dobj = DbgObj::new("EQ");

        let mut expr = self.comp();

        while self.matches_2(Operator(BangEq), Operator(EqEq)) {
            let op = self
                .prev
                .clone()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
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
        let _dobj = DbgObj::new("BLOCK EXPR");
        self.consume(OpenBracket, "Expected '{'");
        let expr = self.expr();
        self.consume(ClosedBracket, "Expected '}'");
        expr
    }

    pub fn expr_without_block(&mut self) -> Box<Expr> {
        self.eq()
    }

    pub fn expr_statement(&mut self) -> Stmt {
        let expr = *self.expr();
        self.consume(Semicol, "expected ';' after expression");
        Stmt::Expr(expr)
    }

    pub fn expr(&mut self) -> Box<Expr> {
        self.eq()
    }

    pub fn print(&mut self) -> Stmt {
        let expr = self.expr();
        self.consume(Semicol, "expected ';' after expression");
        Stmt::Print(*expr)
    }

    pub fn stmt(&mut self) -> Stmt {
        let _dobj = DbgObj::new("STMT");
        if self.matches_1(Kw(Keyword::Print)) {
            self.print()
        } else {
            self.expr_statement()
        }
    }

    pub fn program(&mut self) -> Vec<Stmt> {
        let mut v = vec![];
        while self.curr.is_some() {
            v.push(self.stmt());
        }
        v
    }

    pub fn synchronize(&mut self) {
        self.advance();

        while self.it.peek().is_some() {
            if let Some(t) = &self.prev {
                if t.kind_like(&Semicol) {
                    return;
                }
            }

            if let Some(t) = self.it.peek() {
                match t {
                    Kw(Keyword::Var) | Kw(Keyword::If) | Kw(Keyword::Fn) | Kw(Keyword::Loop)
                    | Kw(Keyword::Ret) | Kw(Keyword::Print) => return,
                    _ => (),
                }
            }

            self.advance();
        }
    }
}

pub fn parenthesize(name: &str, exprs: &[&Expr]) -> result::Result<String, fmt::Error> {
    let mut f = String::new();
    f.write_char('(')?;
    f.write_str(name)?;
    for e in exprs {
        f.write_char(' ')?;
        write!(f, "{}", e)?;
    }
    f.write_char(')')?;
    Ok(f)
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            Expr::Binary { op, left, right } => parenthesize(&format!("{}", op), &[left, right])?,
            Expr::Grouping { expr } => parenthesize("group", &[expr])?,
            Expr::Literal { lit } => format!("{}", lit),
            Expr::Unary { op, right } => parenthesize(&format!("{}", op), &[right])?,
        };
        f.write_str(&s)
    }
}

pub fn parse(program: &str) -> Vec<Stmt> {
    let it = box tokenize(program);
    let mut parser = Parser::new(it);
    parser.program()
}
