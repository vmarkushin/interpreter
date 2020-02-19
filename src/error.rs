use crate::interpreter::Error as RuntimeError;
use crate::syntax::Error as SyntaxError;
use crate::tokenizer::Error as TokenizerError;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum Error {
    #[error(display = "Tokenizer error: {}", _0)]
    TokenizerError(TokenizerError),
    #[error(display = "Syntax error: {}", _0)]
    SyntaxError(SyntaxError),
    #[error(display = "Runtime error: {}", _0)]
    RuntimeError(RuntimeError),
}

impl From<TokenizerError> for Error {
    fn from(e: TokenizerError) -> Self {
        Self::TokenizerError(e)
    }
}

impl From<TokenizerError> for SyntaxError {
    fn from(e: TokenizerError) -> Self {
        Self::TokenError(e)
    }
}

impl From<SyntaxError> for Error {
    fn from(e: SyntaxError) -> Self {
        Self::SyntaxError(e)
    }
}

impl From<RuntimeError> for Error {
    fn from(e: RuntimeError) -> Self {
        Self::RuntimeError(e)
    }
}
