use crate::tokenizer::{Keyword, Literal, Operator::{self, *}, Token, TokenKind, TokenKind::*, Tokenizer, TokenMeta};
use log::trace;
use std::fmt::{self, Display, Formatter, Write};
use std::iter::Peekable;
use std::result;
use log::{error, debug};
use std::option::NoneError;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error(display = "Syntax error.")]
pub enum Error {
    #[error(display = "expected expression, found `{}`", _0)]
    ExpectedExpression(String),
    #[error(display = "expected `)`")]
    ExpectedClosedParen,
    #[error(display = "expected `{{`")]
    ExpectedOpenBrace,
    #[error(display = "expected `}}`")]
    ExpectedClosedBrace,
    #[error(display = "expected `;` after {}", _0)]
    ExpectedSemicol(String),
    #[error(display = "expected identifier")]
    ExpectedIdent,
    #[error(display = "invalid assignment")]
    InvalidAssignment,
    #[error(display = "parse error")]
    ParseError,
}

impl From<NoneError> for Error {
    fn from(_: NoneError) -> Self {
        Error::ParseError
    }
}

pub type Result<R> = result::Result<R, Error>;

#[derive(Debug)]
pub enum Stmt {
    Expr(Expr),
    Print(Expr),
    VarDecl {
        name: TokenMeta,
        initializer: Option<Expr>,
    },
    VarAssign {
        name: TokenMeta,
        value: Expr,
    },
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
            Stmt::VarDecl {
                name,
                initializer
            } => {
                f.write_str("(var ")?;
                f.write_str(&name.lexeme)?;
                if let Some(init) = initializer {
                    f.write_char(' ')?;
                    init.fmt(f)?;
                }
                f.write_str(")")
            }
            Stmt::VarAssign { name, value } => {
                f.write_str("(= ")?;
                f.write_str(&name.lexeme)?;
                f.write_char(' ')?;
                value.fmt(f)?;
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
    Var(TokenMeta),
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
    had_error: bool,
    errors: Vec<Error>,
}

impl<'a> Parser<'a> {
    pub fn new(mut it: Box<dyn Iterator<Item = Token> + 'a>) -> Self {
        let first = it.next();
        Parser {
            it: it.peekable(),
            prev: None,
            curr: first,
            had_error: false,
            errors: Vec::new(),
        }
    }

    pub fn advance(&mut self) {
        self.prev = self.curr.take();
        self.curr = self.it.next();
    }

    pub fn curr_kind(&self) -> Option<TokenKind> {
        self.curr.as_ref().map(|x| x.kind.clone())
    }

    pub fn curr_meta(&self) -> Option<TokenMeta> {
        self.curr.as_ref().map(|x| x.meta.clone())
    }

    pub fn prev_kind(&self) -> Option<TokenKind> {
        self.prev.as_ref().map(|x| x.kind.clone())
    }

    pub fn peek_kind(&mut self) -> Option<&TokenKind> {
        self.it.peek().map(|x| &x.kind)
    }

    pub fn consume(&mut self, t0: TokenKind, err: Error) -> Result<Token> {
        match self.curr.take() {
            Some(t) if t.kind.has_type_like(&t0) => {
                self.advance();
                Ok(t)
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

        if let Some(Ident(_)) = self.curr_kind() {
            let var_expr = box Expr::Var(self.curr_meta().unwrap());
            self.advance();
            return Ok(var_expr);
        }

        if self.matches_1(OpenParen) {
            let expr = self.expr()?;
            self.consume(ClosedParen, Error::ExpectedClosedParen)?;
            Ok(box Expr::Grouping { expr })
        } else {
            match self.peek_kind() {
                Some(kind) => Err(Error::ExpectedExpression(format!("{}", kind))),
                None => Err(Error::ExpectedExpression("'nothing'".into())),
            }
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

    pub fn expr_statement(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("EXPR STMT");
        let expr = *self.expr()?;
        Ok(Stmt::Expr(expr))
    }

    /// Handles assignments statements.
    ///
    /// # Examples
    /// - `a = 1;`
    pub fn assign_statement(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("ASSIGN STMT");

        let expr_stmt = self.expr_statement()?;

        if self.matches_1(Operator(Operator::Eq)) {
            let value = *self.expr()?;
            if let Stmt::Expr(expr) = expr_stmt {
                if let Expr::Var(name) = expr {
                    return Ok(Stmt::VarAssign {
                        name,
                        value
                    })
                }
            }

            return Err(Error::InvalidAssignment);
        }

        Ok(expr_stmt)
    }

    pub fn expr(&mut self) -> Result<Box<Expr>> {
        let _dobj = DbgObj::new("EXPR");
        self.eq()
    }

    pub fn print(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("PRINT");
        let expr = self.expr()?;
        Ok(Stmt::Print(*expr))
    }

    // Handles variable declarations.
    ///
    /// # Examples
    /// - `var a = 1;`
    pub fn var_decl(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("VAR DECL");

        let ident_token = self.consume(TokenKind::Ident("".to_string()), Error::ExpectedIdent)?;
        let initializer = self.matches_1(Operator(Operator::Eq)).then(|| self.expr()).transpose()?.map(|x| *x);
        let stmt = Stmt::VarDecl {
            name: ident_token.meta,
            initializer,
        };
        self.consume(Semicol, Error::ExpectedSemicol("variable declaration".into()))?;
        Ok(stmt)
    }

    /// Handles statements.
    ///
    /// # Examples
    /// - `var a = 1;`
    /// - `print a;`
    pub fn stmt(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("STMT");

        let stmt = if self.matches_1(Kw(Keyword::Print)) {
            self.print()
        } else {
            self.assign_statement()
        }?;
        self.consume(Semicol, Error::ExpectedSemicol("expression".into()))?;
        Ok(stmt)
    }

    /// Handles declarations (variable declarations and statements).
    pub fn decl(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("DECL");
        if self.matches_1(Kw(Keyword::Var)) {
            self.var_decl()
        } else {
            self.stmt()
        }
    }

    /// Handles the whole program.
    pub fn program(&mut self) -> Vec<Stmt> {
        let _dobj = DbgObj::new("PROG");
        let mut v = vec![];
        while self.curr.is_some() {
            match self.decl() {
                Ok(decl) => v.push(decl),
                Err(e) => {
                    self.had_error = true;
                    error!("{}", e);
                    self.errors.push(e);
                    self.synchronize();
                },
            }
        }
        v
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
            Expr::Var(var) => format!("{}", var.lexeme),
        };
        f.write_str(&s)
    }
}

pub fn parse(program: &str) -> Result<Vec<Stmt>> {
    let tokenizer = Tokenizer::new(program);
    let it = box tokenizer;
    let mut parser = Parser::new(it);
    let vec = parser.program();
    if parser.had_error {
        Err(parser.errors.first().cloned().unwrap())
    } else {
        Ok(vec)
    }
}

mod tests {
    use crate::tokenizer::tokenize;
    use super::{Parser, Error};

    #[test]
    fn test_parser() {
        let mut parser = Parser::new(box tokenize("1;"));
        let _ = parser.program();
        assert!(!parser.had_error);

        let mut parser = Parser::new(box tokenize("1"));
        let _ = parser.program();
        assert_eq!(parser.errors.first().unwrap(), &Error::ExpectedSemicol("expression".into()));

        let mut parser = Parser::new(box tokenize("1 + 2;"));
        let _ = parser.program();
        assert!(!parser.had_error);

        let mut parser = Parser::new(box tokenize("1 + true;"));
        let _ = parser.program();
        assert!(!parser.had_error);

        let mut parser = Parser::new(box tokenize("1 + var;"));
        let _ = parser.program();
        assert_eq!(parser.errors.first().unwrap(), &Error::ExpectedExpression(";".into()));

        let mut parser = Parser::new(box tokenize("var a = 1 + 2;"));
        let _ = parser.program();
        assert!(!parser.had_error);

        let mut parser = Parser::new(box tokenize("var a = 1 < 2;"));
        let _ = parser.program();
        assert!(!parser.had_error);

        let mut parser = Parser::new(box tokenize("var a = null;"));
        let _ = parser.program();
        assert!(!parser.had_error);

        let mut parser = Parser::new(box tokenize("var if = a;"));
        let _ = parser.program();
        assert_eq!(parser.errors.first().unwrap(), &Error::ExpectedIdent);
    }
}