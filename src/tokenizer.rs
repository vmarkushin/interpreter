use self::TokenKind::*;
use lazy_static::lazy_static;
use log::debug;
use log::error;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter, Write};
use std::iter::Peekable;
use std::result;
use std::str::Chars;
use crate::interpreter::Number;
use crate::interpreter::Number::Float;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error(display = "Tokenizer error.")]
pub enum Error {
    #[error(display = "unexpected new line in string")]
    UnexpectedNewLineInStr,
    #[error(display = "unterminated string")]
    UnterminatedStr,
    #[error(display = "unexpected new line in string")]
    InvalidFloat,
}

pub type Result<R> = result::Result<R, Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Operator::Add => f.write_str("+"),
            Operator::Sub => f.write_str("-"),
            Operator::Mul => f.write_str("*"),
            Operator::Div => f.write_str("/"),
            Operator::Eq => f.write_str("="),
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

#[derive(PartialEq, Clone, Debug)]
pub enum Literal {
    Num(Number),
    Str(String),
    Bool(bool),
}

impl Eq for Literal {}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Num(n) => n.fmt(f),
            Literal::Str(s) => s.fmt(f),
            Literal::Bool(b) => b.fmt(f),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum TokenKind {
    Lit(Literal),
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
    Unknown,
}

#[derive(Debug, Clone)]
pub struct TokenMeta {
    pub lexeme: String,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub(crate) kind: TokenKind,
    pub(crate) meta: TokenMeta,
}

impl Token {
    pub fn into_kind(self) -> TokenKind {
        self.kind
    }

    pub fn into_meta(self) -> TokenMeta {
        self.meta
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Operator(o) => o.fmt(f),
            TokenKind::Lit(l) => l.fmt(f),
            TokenKind::Ident(i) => {
                f.write_char('`')?;
                f.write_str(&i)?;
                f.write_char('`')
            }
            TokenKind::Kw(kw) => kw.fmt(f),
            TokenKind::OpenParen => f.write_str("("),
            TokenKind::ClosedParen => f.write_str(")"),
            TokenKind::OpenBracket => f.write_str("{"),
            TokenKind::ClosedBracket => f.write_str("}"),
            TokenKind::OpenBrace => f.write_str("["),
            TokenKind::ClosedBrace => f.write_str("]"),
            TokenKind::Semicol => f.write_str(";"),
            TokenKind::Unknown => f.write_str("UNKNOWN"),
        }
    }
}

impl TokenKind {
    /// Compares token types (not actual values).
    pub fn has_type_like(&self, other: &TokenKind) -> bool {
        match (self, other) {
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
        m.insert("else", Keyword::Else);
        m.insert("for", Keyword::For);
        m.insert("while", Keyword::While);
        m.insert("loop", Keyword::Loop);
        m.insert("var", Keyword::Var);
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
    Else,
    For,
    While,
    Loop,
    Var,
    Ret,
    Print,
    True,
    False,
}

impl Display for Keyword {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::If => f.write_str("if"),
            Self::Else => f.write_str("else"),
            Self::For => f.write_str("for"),
            Self::While => f.write_str("while"),
            Self::Loop => f.write_str("loop"),
            Self::Var => f.write_str("var"),
            Self::Ret => f.write_str("ret"),
            Self::Print => f.write_str("print"),
            Self::True => f.write_str("true"),
            Self::False => f.write_str("false"),
        }
    }
}

pub struct Tokenizer<'a> {
    input: &'a str,
    start: usize,
    curr: usize,
    col: usize,
    line: usize,
    it: Peekable<Chars<'a>>,
}

impl<'a> Tokenizer<'a> {
    pub fn new(input: &'a str) -> Self {
        Tokenizer {
            input,
            line: 0,
            col: 0,
            start: 0,
            curr: 0,
            it: input.chars().peekable(),
        }
    }

    /// Tries to find next token.
    ///
    /// May return `None` even if it is not the end of input yet (e.g. on comment).
    fn next_token(&mut self) -> Option<Result<Token>> {
        let mut first_char = self.next_char()?;
        while first_char.is_whitespace() {
            first_char = self.next_char()?;
        }

        self.start = self.curr - 1;

        let token: Result<Token> = try {
            let token_kind = match first_char {
                // Identifier
                c if is_id_start(c) => self.ident(),

                // TODO: parse floats
                // Numeric literal
                _c @ '0'..='9' => {
                    let literal_kind = self.number()?;
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
                '/' => {
                    if self.eat_matches('/') {
                        while let Some(c) = self.it.peek() {
                            if *c == '\n' {
                                break;
                            }
                            let _ = self.next_char();
                        }
                        return None;
                    } else {
                        Operator(Operator::Div)
                    }
                }
                '*' => Operator(Operator::Mul),
                '=' => self.assign_or_eq(),
                ';' => Semicol,
                '!' => self.not_or_neq(),
                '<' => self.lt(),
                '>' => self.gt(),
                '\n' => {
                    self.col = 0;
                    self.line += 1;
                    return None;
                }
                // String literal
                '"' => self.string()?,
                _ => Unknown,
            };

            let lexeme = self.curr_lexeme();

            let token = Token {
                kind: token_kind,
                meta: TokenMeta {
                    lexeme,
                    line: self.line,
                    column: self.col,
                },
            };

            let remaining_input: String = self.input.chars().skip(self.curr).collect();
            debug!(
                "Parsed token '{:?}' ({}). Rem: {}",
                token.kind, token.meta.lexeme, remaining_input
            );

            token
        };
        Some(token)
    }

    pub fn next_char(&mut self) -> Option<char> {
        self.col += 1;
        self.curr += 1;
        self.it.next()
    }

    pub(crate) fn curr_lexeme(&mut self) -> String {
        self.input
            .chars()
            .skip(self.start)
            .take(self.curr - self.start)
            .collect()
    }

    fn eat_matches(&mut self, expect: char) -> bool {
        let b = self.it.peek().map_or(false, |c| *c == expect);
        if b {
            let _ = self.next_char();
        }
        b
    }

    fn eat_while<F>(&mut self, mut predicate: F)
    where
        F: FnMut(char) -> bool,
    {
        while !self.is_eof() && predicate(*self.it.peek().unwrap()) {
            let _ = self.next_char();
        }
    }

    fn is_eof(&mut self) -> bool {
        self.it.peek().is_none()
    }

    fn assign_or_eq(&mut self) -> TokenKind {
        if self.eat_matches('=') {
            Operator(Operator::EqEq)
        } else {
            Operator(Operator::Eq)
        }
    }

    fn not_or_neq(&mut self) -> TokenKind {
        if self.eat_matches('=') {
            Operator(Operator::BangEq)
        } else {
            Operator(Operator::Not)
        }
    }

    fn lt(&mut self) -> TokenKind {
        if self.eat_matches('=') {
            Operator(Operator::LtEq)
        } else {
            Operator(Operator::Lt)
        }
    }

    fn gt(&mut self) -> TokenKind {
        if self.eat_matches('=') {
            Operator(Operator::GtEq)
        } else {
            Operator(Operator::Gt)
        }
    }

    fn ident(&mut self) -> TokenKind {
        // start is already eaten, eat the rest of identifier
        self.eat_while(is_id_continue);
        let string = self.curr_lexeme();

        if let Some(kw) = KEYWORDS.get(string.as_str()) {
            Kw(*kw)
        } else {
            Ident(string.to_owned())
        }
    }

    fn number(&mut self) -> Result<Literal> {
        self.eat_while(|x| x.is_digit(10));
        let string = self.curr_lexeme();
        Ok(Literal::Num(
            Float(string.parse().map_err(|_| Error::InvalidFloat)?),
        ))
    }

    fn string(&mut self) -> Result<TokenKind> {
        // TODO: show more info in errors
        let _start_line = self.line;
        let mut terminated = false;

        let mut err = None;
        while let Some(c) = self.next_char() {
            if c == '\n' {
                err = Some(Error::UnexpectedNewLineInStr);
            } else if c == '"' {
                terminated = true;
                break;
            }
        }

        if let Some(e) = err {
            return Err(e);
        }

        if !terminated {
            return Err(Error::UnterminatedStr);
        }

        let string = self
            .input
            .chars()
            .skip(self.start + 1)
            .take(self.curr - self.start - 2)
            .collect();
        Ok(TokenKind::Lit(Literal::Str(string)))
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut token = self.next_token();
        while token.is_none() && !self.is_eof() {
            token = self.next_token();
        }
        token.and_then(|result| match result {
            Ok(token) => Some(Ok(token)),
            Err(e) => {
                error!("{}", e);
                Some(Err(e))
            }
        })
    }
}

pub fn tokenize(input: &str) -> impl Iterator<Item = Result<Token>> + '_ {
    Tokenizer::new(input)
}

pub fn is_id_start(c: char) -> bool {
    c.is_ascii_alphabetic()
}

pub fn is_id_continue(c: char) -> bool {
    c.is_ascii_alphabetic() || c.is_digit(10)
}

#[test]
fn expr_formatting_test() -> fmt::Result {
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
fn test_tokenizer_kinds() -> fmt::Result {
    let ts: Vec<_> = tokenize("print")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Kw(Keyword::Print)][..]);

    let ts: Vec<_> = tokenize("=")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Operator(Operator::Eq)][..]);

    let ts: Vec<_> = tokenize("$")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Unknown][..]);

    let ts: Vec<_> = tokenize("==")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Operator(Operator::EqEq)][..]);

    let ts: Vec<_> = tokenize("!=")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Operator(Operator::BangEq)][..]);

    let ts: Vec<_> = tokenize("1")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Lit(Literal::Num(1.0))][..]);

    let ts: Vec<_> = tokenize(r#""hello""#)
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(
        ts.as_slice(),
        &[TokenKind::Lit(Literal::Str("hello".into()))][..]
    );

    let mut ts: Vec<_> = tokenize("\"he\nllo\"").map(Result::unwrap_err).collect();
    assert_eq!(ts.as_slice(), &[Error::UnexpectedNewLineInStr][..]);

    let ts: Vec<_> = tokenize("true false")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(
        ts.as_slice(),
        &[TokenKind::Kw(Keyword::True), TokenKind::Kw(Keyword::False)][..]
    );

    let ts: Vec<_> = tokenize("ident")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Ident("ident".to_string())][..]);

    let ts: Vec<_> = tokenize("truee")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    assert_eq!(ts.as_slice(), &[TokenKind::Ident("truee".to_string())][..]);

    let ts: Vec<_> = tokenize("if a == true { b = 3 * -2; }")
        .map(Result::unwrap)
        .map(Token::into_kind)
        .collect();
    let _x = ts.first().unwrap();
    assert_eq!(
        ts.as_slice(),
        &[
            TokenKind::Kw(Keyword::If),
            TokenKind::Ident("a".to_string()),
            TokenKind::Operator(Operator::EqEq),
            TokenKind::Kw(Keyword::True),
            TokenKind::OpenBrace,
            TokenKind::Ident("b".to_string()),
            TokenKind::Operator(Operator::Eq),
            TokenKind::Lit(Literal::Num(3.0)),
            TokenKind::Operator(Operator::Mul),
            TokenKind::Operator(Operator::Sub),
            TokenKind::Lit(Literal::Num(2.0)),
            TokenKind::Semicol,
            TokenKind::ClosedBrace,
        ][..]
    );

    Ok(())
}
