#![feature(box_syntax, try_trait, bool_to_option, try_blocks)]

#[macro_use]
extern crate err_derive;
#[macro_use]
extern crate log;

pub mod compiler;
pub mod error;
pub mod interpreter;
pub mod syntax;
pub mod tokenizer;
pub mod vm;
#[macro_use]
pub mod macros;

pub use crate::error::Error;
pub use crate::syntax::parse;
