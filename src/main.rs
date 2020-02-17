#![feature(box_syntax)]

#[macro_use]
extern crate err_derive;

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

    let mut line = r#"
        print "hello";
        print true;
        print 2 + 1;
    "#.to_owned();

    // REPL mode
    let stdin = std::io::stdin();
    loop {
        if line.is_empty() {
            stdin.read_line(&mut line).unwrap();
        } else {
            if let Some(e) = parse(&line).and_then(|stmts| {
                display_arr(&stmts);
                interpreter.interpret(stmts)
            }).err() {
                error!("Error: {:?}", e);
            }
            line.clear();
        }
    }
}
