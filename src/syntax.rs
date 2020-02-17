use crate::tokenizer::{
    Keyword, Literal,
    Operator::{self, *},
    Token, TokenKind,
    TokenKind::*,
    Tokenizer,
};
use log::trace;
use std::fmt::{self, Display, Formatter, Write};
use std::iter::Peekable;
use std::result;
use log::debug;

#[derive(Debug, Clone, Error)]
#[error(display = "Interpreter error.")]
pub enum Error {
    #[error(display = "expected expression, found `{}`", _0)]
    ExpectedExpression(String),
    #[error(display = "unexpected operation `{}`", _0)]
    UnsopportedOperation(String),
    #[error(display = "expected `)`")]
    ExpectedClosedParen,
    #[error(display = "expected `{{`")]
    ExpectedOpenBrace,
    #[error(display = "expected `}}`")]
    ExpectedClosedBrace,
    #[error(display = "expected `;` after expression")]
    ExpectedSemicol,
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
            Stmt::Expr(e) => e.fmt(f),
            Stmt::Print(e) => {
                f.write_str("(print ")?;
                e.fmt(f)?;
                f.write_str(")")
            }
        }
    }
}

pub fn display_arr<T: Display>(arr: &[T]) {
    for s in arr {
        debug!("{}", s);
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
        trace!("-> {}", s);
        DbgObj { text: s }
    }
}

impl Drop for DbgObj {
    fn drop(&mut self) {
        unsafe {
            DBG_OBJ_PAD -= 2;
        }
        trace!("<- {}", self.text);
    }
}

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

    pub fn curr_kind(&self) -> Option<TokenKind> {
        self.curr.as_ref().map(|x| x.kind.clone())
    }

    pub fn prev_kind(&self) -> Option<TokenKind> {
        self.prev.as_ref().map(|x| x.kind.clone())
    }

    pub fn peek_kind(&mut self) -> Option<&TokenKind> {
        self.it.peek().map(|x| &x.kind)
    }

    pub fn consume(&mut self, t0: TokenKind, err: Error) -> Result<()> {
        match &self.curr_kind() {
            Some(t) if t.has_type_like(&t0) => {
                self.advance();
                Ok(())
            }
            _ => Err(err),
        }
    }

    pub fn matches_any(&mut self, ts: &[TokenKind]) -> bool {
        match &self.curr_kind() {
            Some(t) => {
                for ti in ts {
                    if t.has_type_like(ti) {
                        self.advance();
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    pub fn matches_1(&mut self, t0: TokenKind) -> bool {
        self.matches_any(&[t0])
    }

    pub fn matches_2(&mut self, t0: TokenKind, t1: TokenKind) -> bool {
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
        match self.curr_kind() {
            Some(Lit(lit)) => {
                self.advance();
                return Ok(box Expr::Literal { lit });
            }
            _ => {}
        }

        if self.matches_1(OpenParen) {
            let expr = self.expr()?;
            self.consume(ClosedParen, Error::ExpectedClosedParen)?;
            Ok(box Expr::Grouping { expr })
        } else {
            Err(Error::ExpectedExpression(format!("{:?}", self.peek_kind())))
        }
    }

    pub fn unary(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("UNARY");

        if let Some(t) = &self.curr_kind() {
            #[allow(clippy::single_match)]
            match *t {
                TokenKind::Operator(op) => match op {
                    Sub => (),
                    _ => return Err(Error::ExpectedExpression(format!("{}", op))),
                },
                _ => (),
            }
        }

        if self.matches_2(Operator(Not), Operator(Sub)) {
            let op = self
                .prev_kind()
                .unwrap()
                .as_operator()
                .expect("expected operator");
            let right = self.unary()?;
            Ok(box Expr::Unary { op, right })
        } else {
            self.primary()
        }
    }

    pub fn mul_div(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("MUL");

        let mut expr = self.unary()?;
        while self.matches_2(Operator(Mul), Operator(Div)) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = self.unary()?;
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    pub fn add_sub(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("ADD");

        let mut expr = self.mul_div()?;
        while self.matches_2(Operator(Sub), Operator(Add)) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = self.mul_div()?;
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    pub fn comp(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("COMP");

        let mut expr = self.add_sub()?;
        while self.matches_any(&[Operator(Lt), Operator(Gt), Operator(LtEq), Operator(GtEq)]) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = self.add_sub()?;
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    pub fn eq(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("EQ");

        let mut expr = self.comp()?;

        while self.matches_2(Operator(BangEq), Operator(EqEq)) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = self.comp()?;
            expr = box Expr::Binary {
                left: expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    pub fn block_expr(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("BLOCK EXPR");
        self.consume(OpenBracket, Error::ExpectedOpenBrace)?;
        let expr = self.expr()?;
        self.consume(ClosedBracket, Error::ExpectedClosedBrace)?;
        Ok(expr)
    }

    pub fn expr_without_block(&mut self) -> Result<Box<Expr>> {
        self.eq()
    }

    pub fn expr_statement(&mut self) -> Result<Stmt> {
        let expr = *self.expr()?;
        self.consume(Semicol, Error::ExpectedSemicol)?;
        Ok(Stmt::Expr(expr))
    }

    pub fn expr(&mut self) -> Result<Box<Expr>> {
        self.eq()
    }

    pub fn print(&mut self) -> Result<Stmt> {
        let expr = self.expr()?;
        self.consume(Semicol, Error::ExpectedSemicol)?;
        Ok(Stmt::Print(*expr))
    }

    pub fn stmt(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("STMT");
        if self.matches_1(Kw(Keyword::Print)) {
            self.print()
        } else {
            self.expr_statement()
        }
    }

    pub fn program(&mut self) -> Result<Vec<Stmt>> {
        let mut v = vec![];
        while self.curr.is_some() {
            v.push(self.stmt()?);
        }
        Ok(v)
    }

    pub fn synchronize(&mut self) {
        self.advance();

        while self.it.peek().is_some() {
            if let Some(t) = &self.prev_kind() {
                if t.has_type_like(&Semicol) {
                    return;
                }
            }

            if let Some(t) = self.peek_kind() {
                match t {
                    Kw(Keyword::Var) | Kw(Keyword::If) | Kw(Keyword::Loop) | Kw(Keyword::Ret)
                    | Kw(Keyword::Print) => return,
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

pub fn parse(program: &str) -> Result<Vec<Stmt>> {
    let tokenizer = Tokenizer::new(program);
    let it = box tokenizer;
    let mut parser = Parser::new(it);
    parser.program()
}
