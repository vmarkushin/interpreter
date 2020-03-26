#![feature(box_syntax, bool_to_option, try_blocks, stmt_expr_attributes)]

use interpreter::error::Error;
use interpreter::interpreter::Interpreter;
use interpreter::syntax::{display_arr, parse};
use log::error;
use log::LevelFilter;
use std::env::args;
use std::fs::read_to_string;
use std::path::Path;

fn main() {
    env_logger::Builder::new()
        .format_timestamp(None)
        .filter_level(LevelFilter::Debug)
        .init();

    let mut interpreter = Interpreter::new();

    let default_prog = r#"
        var a = 10;
        var b = 1;
        print b + a;

        if b == 1 && a == 11 - 1 {
            print "yes!";
        } else {
            print "no...";
        }

        b = 10;
        while b > 0 {
            print "Counting down... " + b;
            b = b - 1;
        }

        print "Off blast!";

        var a = 1;
        print a > 2;
        print "enter a: ";
        read a;
        print a > 2;
        print "enter a: ";
        read a;
        print a > 2;
    "#;
    let mut prog = args()
        .nth(2)
        .map(|file| read_to_string(Path::new(&file)).expect("invalid file"))
        .unwrap_or_else(|| default_prog.to_owned());

    // REPL mode
    let stdin = std::io::stdin();
    loop {
        if prog.is_empty() {
            stdin.read_line(&mut prog).unwrap();
        } else {
            let result: Result<(), Error> = try {
                let stmts = parse(&prog)?;
                display_arr(&stmts);
                interpreter.interpret(&stmts)?;
            };
            if let Err(e) = result {
                error!("{}", e);
            }
            prog.clear();
        }
    }
}
