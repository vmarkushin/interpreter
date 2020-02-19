#![feature(box_syntax, try_trait, bool_to_option, try_blocks)]

#[macro_use]
extern crate err_derive;

pub mod error;
pub mod interpreter;
pub mod syntax;
pub mod tokenizer;

use crate::interpreter::Interpreter;
use crate::syntax::{display_arr, parse};
use log::error;
use log::LevelFilter;
use error::Error;

fn main() {
    env_logger::Builder::new()
        .filter_level(LevelFilter::Debug)
        .init();

    let mut interpreter = Interpreter::new();
    let mut line = r#"
        var a = 1336;
        var b = 3;
        print c;
    "#.to_owned();

    // REPL mode
    let stdin = std::io::stdin();
    loop {
        if line.is_empty() {
            stdin.read_line(&mut line).unwrap();
        } else {
            let result: Result<(), Error> = try {
                let stmts = parse(&line)?;
                display_arr(&stmts);
                interpreter.interpret(stmts)?;
            };
            if let Err(e) = result {
                error!("{}", e);
            }
            line.clear();
        }
    }
}
