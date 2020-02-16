#![feature(box_syntax)]

pub mod interpreter;
pub mod syntax;
pub mod tokenizer;

use crate::interpreter::Interpreter;
use crate::syntax::{display_arr, parse};
use log::error;
use log::LevelFilter;
use std::collections::HashMap;
use tokenizer::Literal;

pub static mut VARS: Option<HashMap<String, Literal>> = None;

fn main() {
    env_logger::Builder::new()
        .filter_level(LevelFilter::Debug)
        .init();

    let mut interpreter = Interpreter::new();

    let expr = r#"
        print "hello";
        print true;
        print 2 + 1;
    "#;
    let stmts = parse(&expr);
    display_arr(&stmts);
    if let Err(e) = interpreter.interpret(stmts) {
        error!("Error: {:?}", e);
    }

    // REPL mode
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        stdin.read_line(&mut line).unwrap();
        let stmts = parse(&line);
        display_arr(&stmts);
        if let Err(e) = interpreter.interpret(stmts) {
            error!("Error: {:?}", e);
        }
    }
}
