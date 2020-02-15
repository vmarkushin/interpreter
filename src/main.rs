#![feature(box_syntax)]

pub mod cursor;
pub mod interpreter;
pub mod syntax;
pub mod tokenizer;

use crate::interpreter::Interpreter;
use crate::syntax::{parse, display_arr};
use log::debug;
use log::LevelFilter;
use std::collections::HashMap;
use tokenizer::Literal;

pub static mut VARS: Option<HashMap<String, Literal>> = None;

fn main() {
    env_logger::Builder::new()
        .filter_level(LevelFilter::Debug)
        .init();

    unsafe {
        VARS = Some(HashMap::new());
    }

    let expr = "print 1 - (2 * 3) < 4 != false;";
    let mut stmts = parse(&expr);
    let mut interpreter = Interpreter::new();
    display_arr(&stmts);
    interpreter.interpret(stmts).unwrap();
}
