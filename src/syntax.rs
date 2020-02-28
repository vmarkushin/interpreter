//! Syntax analyzer.
//!
//! Provides functionality for building AST (abstract syntax tree).
//!
//! Syntax grammar:
//! ```
//! <prog>: <decl>*
//!
//! <decl>: 'var' IDENT '=' <expr> ';'
//!       | <stmt>
//!
//! <stmt>: 'print' <expr> ';'
//!       | 'read' <expr> ';'
//!       | 'if' <expr> <block> ('else' <block>)?
//!       | 'while' <expr> <block>
//!       | <assign>
//!
//! <block>: '{' <stmt>* '}'
//!
//! <assign>: IDENT '=' <expr> ';'
//!         | <expr> ';'
//!
//! <expr>: <or>
//!
//! <or>: <and> ('||' <and>)*
//!
//! <and>: <eq> ('&&' <eq>)*
//!
//! <eq>: <comp> (('=='|'!=') <comp>)*
//!
//! <comp>: <sum> (('<'|'>'|'>='|'<=') <sum>)*
//!
//! <sum>: <prod> (('-'|'+') <prod>)*
//!
//! <prod>: <unary> (('/'|'*') <unary>)*
//!
//! <unary>: ('!'|'-') <unary>
//!        | <primary>
//!
//! <primary>: LITER
//!          | IDENT
//!          | '(' <expr> ')'
//! ```

use crate::tokenizer::{
    Error as TokError,
    Keyword::*,
    Literal,
    Operator::{self, *},
    Result as TokResult, Token, TokenKind,
    TokenKind::*,
    TokenMeta, Tokenizer,
};
use log::trace;
use log::{debug, error};
use std::fmt::{self, Display, Formatter, Write};
use std::iter::Peekable;
use std::option::NoneError;
use std::result;

/// Kind of syntax parse error.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error(display = "Syntax error.")]
pub enum Error {
    /// Occurs when parser expected an expression, but found _something else_ (this information
    /// is imprinted in the `String`).
    #[error(display = "expected expression, found `{}`", _0)]
    ExpectedExpression(String),
    /// Occurs when parser expected an closed parenthesis (`)`).
    #[error(display = "expected `)`")]
    ExpectedClosedParen,
    /// Occurs when parser expected an open brace (`{`).
    #[error(display = "expected `{{`")]
    ExpectedOpenBrace,
    /// Occurs when parser expected an closed brace (`}`).
    #[error(display = "expected `}}`")]
    ExpectedClosedBrace,
    /// Occurs when parser expected an semicolon (`;`).
    #[error(display = "expected `;` after {}", _0)]
    ExpectedSemicol(String),
    /// Occurs when parser expected an identifier (e.g. `foo`).
    #[error(display = "expected identifier")]
    ExpectedIdent,
    /// Occurs when parser expected an variable name, but found _something else_ (this information
    /// is imprinted in the `String`).
    #[error(display = "expected expression, found `{}`", _0)]
    ExpectedVar(String),
    /// Occurs on tokenizer error.
    #[error(display = "{}", _0)]
    TokenError(TokError),
    /// General parser error.
    #[error(display = "parse error")]
    ParseError,
}

impl From<NoneError> for Error {
    fn from(_: NoneError) -> Self {
        Error::ParseError
    }
}

pub type Result<R> = result::Result<R, Error>;

/// Statement. The most general component of the program.
#[derive(Debug)]
pub enum Stmt {
    /// Expression statement.
    Expr(Expr),
    /// Print statement.
    Print(Expr),
    /// Read statement.
    Read(TokenMeta),
    /// Variable declaration statement.
    VarDecl {
        name: TokenMeta,
        initializer: Option<Expr>,
    },
    /// Variable assignment statement.
    VarAssign { name: TokenMeta, value: Expr },
    /// If condition statement.
    If {
        cond: Expr,
        then: Vec<Stmt>,
        otherwise: Option<Vec<Stmt>>,
    },
    /// While loop statement.
    While { cond: Expr, actions: Vec<Stmt> },
}

impl Stmt {
    /// Forces statement into an expression.
    ///
    /// # Panics
    /// Panics when `self` is not an expression.
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
            Stmt::Read(meta) => {
                f.write_str("(read ")?;
                f.write_str(&meta.lexeme)?;
                f.write_str(")")
            }
            Stmt::VarDecl { name, initializer } => {
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
            Stmt::If {
                cond,
                then,
                otherwise,
            } => {
                f.write_str("(if ")?;
                cond.fmt(f)?;
                f.write_char(' ')?;

                f.write_char('[')?;
                for s in then {
                    s.fmt(f)?;
                    f.write_char(',')?;
                }
                f.write_char(']')?;

                if let Some(other) = otherwise {
                    f.write_char(' ')?;

                    f.write_char('[')?;
                    for s in other {
                        s.fmt(f)?;
                        f.write_char(',')?;
                    }
                    f.write_char(']')?;
                }

                f.write_str(")")
            }
            Stmt::While { cond, actions } => {
                f.write_str("(while ")?;
                cond.fmt(f)?;
                f.write_char(' ')?;

                f.write_char('[')?;
                for s in actions {
                    s.fmt(f)?;
                    f.write_char(',')?;
                }
                f.write_char(']')?;

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

/// Expression. Always evaluates to [`Value`](value) and may have side effects during evaluation.
#[derive(Debug, Clone)]
pub enum Expr {
    /// Binary expression.
    ///
    /// # Example
    /// `a + b`
    Binary {
        left: Box<Expr>,
        op: Operator,
        right: Box<Expr>,
    },
    /// Grouping expression.
    ///
    /// # Example
    /// `(a + b) * c`
    Grouping { expr: Box<Expr> },
    /// Literal expression.
    ///
    /// # Examples
    /// - `321`
    /// - `"hi"`
    Literal { lit: Literal },
    /// Unary expression.
    ///
    /// # Example
    /// - `-1`
    /// - `!false`
    Unary { op: Operator, right: Box<Expr> },
    /// Variable expression. Evaluates to a value of the variable.
    ///
    /// # Example
    /// - `foo`
    Var(TokenMeta),
}

static mut DBG_OBJ_PAD: usize = 0;

struct DbgObj {
    text: String,
}

impl DbgObj {
    pub fn new(d: impl Display) -> Self {
        #[cfg(test)]
        let pad = 0;
        #[cfg(not(test))]
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
        #[cfg(not(test))]
        unsafe {
            DBG_OBJ_PAD -= 2;
        }
        trace!("<- {}", self.text);
    }
}

/// Syntax parser. Constructs AST from a stream of tokens.
pub struct Parser<'a> {
    it: Peekable<Box<dyn Iterator<Item = TokResult<Token>> + 'a>>,
    prev: Option<Token>,
    curr: Option<Token>,
    errors: Vec<Error>,
}

impl<'a> Parser<'a> {
    pub fn new(it: Box<dyn Iterator<Item = TokResult<Token>> + 'a>) -> Self {
        let mut parser = Parser {
            it: it.peekable(),
            prev: None,
            curr: None,
            errors: Vec::new(),
        };

        parser.advance();
        parser
    }

    pub fn had_error(&self) -> bool {
        !self.errors.is_empty()
    }

    fn advance(&mut self) {
        self.prev = self.curr.take();
        loop {
            let next = self.it.next().transpose();
            match next {
                Err(e) => self.errors.push(e.into()),
                Ok(opt) => {
                    self.curr = opt;
                    break;
                }
            }
        }
    }

    fn curr_kind(&self) -> Option<TokenKind> {
        self.curr.as_ref().map(|x| x.kind.clone())
    }

    fn curr_meta(&self) -> Option<TokenMeta> {
        self.curr.as_ref().map(|x| x.meta.clone())
    }

    fn prev_kind(&self) -> Option<TokenKind> {
        self.prev.as_ref().map(|x| x.kind.clone())
    }

    fn peek_kind(&mut self) -> Result<Option<&TokenKind>> {
        match self.it.peek() {
            Some(Ok(x)) => Ok(Some(&x.kind)),
            Some(Err(e)) => Err(e.clone().into()),
            None => Ok(None),
        }
    }

    fn consume(&mut self, t0: TokenKind, err: Error) -> Result<Token> {
        match self.curr.take() {
            Some(t) if t.kind.has_type_like(&t0) => {
                self.advance();
                Ok(t)
            }
            _ => Err(err),
        }
    }

    fn matches_any(&mut self, ts: &[TokenKind]) -> bool {
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

    fn matches(&mut self, t0: TokenKind) -> bool {
        self.matches_any(&[t0])
    }

    fn matches_2(&mut self, t0: TokenKind, t1: TokenKind) -> bool {
        self.matches_any(&[t0, t1])
    }

    /// Handles primary expression.
    ///
    /// # Examples
    /// - `4`
    /// - `"jam"`
    /// - `foo`
    /// - `(...)`
    fn primary(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("PRIMARY");

        if self.matches(Kw(True)) {
            return Ok(Expr::Literal {
                lit: Literal::Bool(true),
            });
        }

        if self.matches(Kw(False)) {
            return Ok(Expr::Literal {
                lit: Literal::Bool(false),
            });
        }

        if let Some(Lit(lit)) = self.curr_kind() {
            self.advance();
            return Ok(Expr::Literal { lit });
        }

        if let Some(Ident(_)) = self.curr_kind() {
            let var_expr = Expr::Var(self.curr_meta().unwrap());
            self.advance();
            return Ok(var_expr);
        }

        if self.matches(OpenParen) {
            let expr = box self.expr()?;
            self.consume(ClosedParen, Error::ExpectedClosedParen)?;
            Ok(Expr::Grouping { expr })
        } else {
            match self.peek_kind()? {
                Some(kind) => Err(Error::ExpectedExpression(format!("{}", kind))),
                None => Err(Error::ExpectedExpression("'nothing'".into())),
            }
        }
    }

    /// Handles unary operation expression.
    ///
    /// # Examples
    /// - `-a`
    /// - `!b`
    fn unary(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("UNARY");

        if let Some(TokenKind::Op(op)) = &self.curr_kind() {
            match op {
                Minus | ExMark => (),
                _ => return Err(Error::ExpectedExpression(format!("{}", op))),
            }
        }

        if self.matches_2(Op(ExMark), Op(Minus)) {
            let op = self
                .prev_kind()
                .unwrap()
                .as_operator()
                .expect("expected operator");
            let right = box self.unary()?;
            Ok(Expr::Unary { op, right })
        } else {
            self.primary()
        }
    }

    /// Handles multiplication/division expression.
    ///
    /// # Example
    /// `a * b`
    fn mul_div(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("MUL");

        let mut expr = self.unary()?;
        while self.matches_2(Op(Star), Op(Slash)) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = box self.unary()?;
            expr = Expr::Binary {
                left: box expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    /// Handles addition/subtraction expression.
    ///
    /// # Example
    /// `a - b`
    fn add_sub(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("ADD");

        let mut expr = self.mul_div()?;
        while self.matches_2(Op(Minus), Op(Plus)) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = box self.mul_div()?;
            expr = Expr::Binary {
                left: box expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    /// Handles comparison expression.
    ///
    /// # Example
    /// `a > b`
    fn comp(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("COMP");

        let mut expr = self.add_sub()?;
        while self.matches_any(&[Op(Lt), Op(Gt), Op(LtEq), Op(GtEq)]) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = box self.add_sub()?;
            expr = Expr::Binary {
                left: box expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    /// Handles equality expression.
    ///
    /// # Example
    /// `a == b`
    fn eq(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("EQ");

        let mut expr = self.comp()?;

        while self.matches_2(Op(BangEq), Op(EqEq)) {
            let op = self
                .prev_kind()
                .expect("expected token")
                .clone()
                .as_operator()
                .expect("expected operator");
            let right = box self.comp()?;
            expr = Expr::Binary {
                left: box expr,
                op,
                right,
            };
        }
        Ok(expr)
    }

    /// Handles `and` expression.
    ///
    /// # Example
    /// `a && b`
    fn and(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("AND");

        let mut expr = self.eq()?;

        while self.matches(Op(And)) {
            let right = box self.eq()?;
            expr = Expr::Binary {
                left: box expr,
                op: And,
                right,
            };
        }

        Ok(expr)
    }

    /// Handles `or` expression.
    ///
    /// # Example
    /// `a || b`
    fn or(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("OR");

        let mut expr = self.and()?;

        while self.matches(Op(Or)) {
            let right = box self.and()?;
            expr = Expr::Binary {
                left: box expr,
                op: Or,
                right,
            };
        }

        Ok(expr)
    }

    /// Handles expression.
    ///
    /// # Example
    /// `2 + 3`
    fn expr(&mut self) -> Result<Expr> {
        let _dobj = DbgObj::new("EXPR");
        self.or()
    }

    /// Handles expression statement.
    ///
    /// # Example
    /// `var a = 1;`
    fn expr_statement(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("EXPR STMT");
        let expr = self.expr()?;
        Ok(Stmt::Expr(expr))
    }

    /// Handles assignment statement.
    ///
    /// # Example
    /// `a = 1;`
    fn assign_stmt(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("ASSIGN STMT");

        let expr_stmt = self.expr_statement()?;

        if self.matches(Op(Eq)) {
            let value = self.expr()?;
            if let Stmt::Expr(expr) = expr_stmt {
                if let Expr::Var(name) = expr {
                    self.consume(Semicol, Error::ExpectedSemicol("expression".into()))?;
                    Ok(Stmt::VarAssign { name, value })
                } else {
                    Err(Error::ExpectedVar(format!("{}", expr)))
                }
            } else {
                Err(Error::ExpectedExpression(format!("{}", expr_stmt)))
            }
        } else {
            self.consume(Semicol, Error::ExpectedSemicol("expression".into()))?;

            Ok(expr_stmt)
        }
    }

    /// Handles block statement (block of statements).
    ///
    /// # Example
    /// ```{
    ///     var a = 2;
    ///     a = 3;
    /// }```
    fn block_stmt(&mut self) -> Result<Vec<Stmt>> {
        let _dobj = DbgObj::new("BLOCK STMT");
        let mut stmts = Vec::new();

        self.consume(OpenBrace, Error::ExpectedOpenBrace)?;

        while !self.matches(ClosedBrace) {
            let stmt = self.stmt()?;
            stmts.push(stmt);
        }

        match self.prev_kind() {
            Some(prev) => {
                if prev != ClosedBrace {
                    return Err(Error::ExpectedClosedBrace);
                }
            }
            None => return Err(Error::ExpectedClosedBrace),
        }

        Ok(stmts)
    }

    /// Handles `if` statement.
    ///
    /// # Examples=
    /// `if (b) { ... }`
    fn if_stmt(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("IF");

        let cond = self.expr()?;

        let then = self.block_stmt()?;

        let otherwise = if self.matches(Kw(Else)) {
            Some(self.block_stmt()?)
        } else {
            None
        };

        Ok(Stmt::If {
            cond,
            then,
            otherwise,
        })
    }

    /// Handles `while` loop statement.
    ///
    /// # Example
    /// `while (b) { ... }`
    fn while_stmt(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("WHILE");

        let cond = self.expr()?;
        let actions = self.block_stmt()?;

        Ok(Stmt::While { cond, actions })
    }

    /// Handles `print` statement for writing to stdout.
    ///
    /// # Example
    /// `write a;`
    fn print(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("PRINT");
        let expr = self.expr()?;
        self.consume(Semicol, Error::ExpectedSemicol("expression".into()))?;
        Ok(Stmt::Print(expr))
    }

    /// Handles `read` statement for reading from stdin.
    ///
    /// # Example
    /// `read a;`
    fn read(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("READ");

        if let Some(Ident(_)) = self.curr_kind() {
            let stmt = Stmt::Read(self.curr_meta().unwrap());
            self.advance();
            self.consume(Semicol, Error::ExpectedSemicol("variable".into()))?;
            Ok(stmt)
        } else {
            Err(Error::ExpectedIdent)
        }
    }

    /// Handles variable declarations.
    ///
    /// # Example
    /// `var a = 1;`
    fn var_decl(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("VAR DECL");

        let ident_token = self.consume(TokenKind::Ident("".to_string()), Error::ExpectedIdent)?;
        let initializer = self.matches(Op(Eq)).then(|| self.expr()).transpose()?;
        let stmt = Stmt::VarDecl {
            name: ident_token.meta,
            initializer,
        };
        self.consume(
            Semicol,
            Error::ExpectedSemicol("variable declaration".into()),
        )?;
        Ok(stmt)
    }

    /// Handles statements.
    ///
    /// # Examples
    /// - `var a = 1;`
    /// - `print a;`
    fn stmt(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("STMT");

        let stmt = if self.matches(Kw(Print)) {
            self.print()
        } else if self.matches(Kw(Read)) {
            self.read()
        } else if self.matches(Kw(If)) {
            self.if_stmt()
        } else if self.matches(Kw(While)) {
            self.while_stmt()
        } else {
            self.assign_stmt()
        }?;
        Ok(stmt)
    }

    /// Handles declarations (variable declarations and statements).
    fn decl(&mut self) -> Result<Stmt> {
        let _dobj = DbgObj::new("DECL");
        if self.matches(Kw(Var)) {
            self.var_decl()
        } else {
            self.stmt()
        }
    }

    /// Handles the whole program.
    fn program(&mut self) -> Vec<Stmt> {
        let _dobj = DbgObj::new("PROG");
        let mut v = vec![];
        while self.curr.is_some() {
            match self.decl() {
                Ok(decl) => v.push(decl),
                Err(e) => {
                    error!("{}", e);
                    self.errors.push(e);
                    self.synchronize();
                }
            }
        }
        v
    }

    /// Tries to synchronize parser to continue parsing a program in case of an error.
    fn synchronize(&mut self) {
        self.advance();

        while self.it.peek().is_some() {
            if let Some(t) = &self.prev_kind() {
                if t.has_type_like(&Semicol) {
                    return;
                }
            }

            match self.peek_kind() {
                Ok(opt) => {
                    if let Some(t) = opt {
                        match t {
                            Kw(Var) | Kw(If) | Kw(While) | Kw(Loop) | Kw(Ret) | Kw(Print)
                            | Kw(Read) => return,
                            _ => (),
                        }
                    }
                }
                Err(_) => continue,
            }

            self.advance();
        }
    }
}

pub(crate) fn parenthesize(name: &str, exprs: &[&Expr]) -> result::Result<String, fmt::Error> {
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
            Expr::Var(var) => var.lexeme.clone(),
        };
        f.write_str(&s)
    }
}

/// Parses the given program and returns its AST.
pub fn parse(program: &str) -> Result<Vec<Stmt>> {
    let tokenizer = Tokenizer::new(program);
    let it = box tokenizer;
    let mut parser = Parser::new(it);
    let vec = parser.program();
    if parser.had_error() {
        Err(parser.errors.first().cloned().unwrap())
    } else {
        Ok(vec)
    }
}

mod tests {
    use super::{Error, Parser};
    use crate::tokenizer::tokenize;

    #[test]
    fn test_parser() {
        let mut parser = Parser::new(box tokenize("1;"));
        let _ = parser.program();
        assert!(!parser.had_error());

        let mut parser = Parser::new(box tokenize("1"));
        let _ = parser.program();
        assert_eq!(
            parser.errors.first().unwrap(),
            &Error::ExpectedSemicol("expression".into())
        );

        let mut parser = Parser::new(box tokenize("1 + 2;"));
        let _ = parser.program();
        assert!(!parser.had_error());

        let mut parser = Parser::new(box tokenize("1 + true;"));
        let _ = parser.program();
        assert!(!parser.had_error());

        let mut parser = Parser::new(box tokenize("1 + var;"));
        let _ = parser.program();
        assert_eq!(
            parser.errors.first().unwrap(),
            &Error::ExpectedExpression(";".into())
        );

        let mut parser = Parser::new(box tokenize("var a = 1 + 2;"));
        let _ = parser.program();
        assert!(!parser.had_error());

        let mut parser = Parser::new(box tokenize("var a = 1 < 2;"));
        let _ = parser.program();
        assert!(!parser.had_error());

        let mut parser = Parser::new(box tokenize("var a = null;"));
        let _ = parser.program();
        assert!(!parser.had_error());

        let mut parser = Parser::new(box tokenize("var if = a;"));
        let _ = parser.program();
        assert_eq!(parser.errors.first().unwrap(), &Error::ExpectedIdent);
    }
}
