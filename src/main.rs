pub mod tree;
pub mod cursor;
pub mod tokenizer;

use log::LevelFilter;
use log::{debug, error, trace};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt::{Debug, Error, Formatter};
use std::io;
use std::str::FromStr;
use tokenizer::Literal;
use crate::tokenizer::{parse, Token};

pub static mut VARS: Option<HashMap<String, Literal>> = None;

fn main() {
    env_logger::Builder::new()
        .filter_level(LevelFilter::Debug)
        .init();

    unsafe {
        VARS = Some(HashMap::new());
    }

    let mut expr = "sin(pi*2)*sin(2*pi)+cos(2*pi)*cos(pi*2)+a";
    let (mut out, vars) = parse(&mut expr);
    debug!("Tokens: {:?}\n", out);

    for v in vars {
        let global_vars = unsafe { VARS.as_mut().unwrap() };
        if !global_vars.contains_key(&v) {
            println!("Enter value for var '{}': ", v);
            let mut input = String::new();
            io::stdin().read_line(&mut input).unwrap();
            let n: f64 = input.trim().parse().expect("Expected float number");
            global_vars.insert(v, Literal::Num(n));
        }
    }

    let mut stack: Vec<Token> = Vec::new();

    while let Some(token) = out.pop() {
        debug!("Processing {:?}", token);
        match token {
            Token::Operator(op) => {
                let b = out.last().expect("Expected b");
                let a = out.get(out.len() - 2).expect("Expected a");
                let op_a: Result<f64, _> = a.clone().try_into().and_then(|l: Literal| l.try_into());
                let op_b: Result<f64, _> = b.clone().try_into().and_then(|l: Literal| l.try_into());

                match (op_a, op_b) {
                    (Ok(a), Ok(b)) => {
                        out.pop();
                        out.pop();

                        let result = op.apply(a, b);
                        out.push(Token::Lit(Literal::Num(result)));

                        // move tokens from stack to output until new operator or fn is not found
                        while let Some(t) = stack.pop() {
                            match t {
                                Token::Operator(_) | Token::Fn(_) => {
                                    out.push(t);
                                    break;
                                }
                                _ => out.push(t),
                            }
                        }
                    }
                    _ => {
                        stack.push(token);
                    }
                }
            }
            Token::Fn(f) => {
                let t = out.pop().expect("Expected token");
                let n = match t {
                    Token::Lit(Literal::Num(n)) => n,
                    Token::Const(c) => c.eval(),
                    _ => {
                        out.push(t); // TODO: optimize?
                        stack.push(token);
                        debug!("Out: {:?}", out);
                        debug!("Stack: {:?}\n", stack);
                        continue;
                    }
                };
                let result = f.call(n);
                out.push(Token::Lit(Literal::Num(result)));
                // move tokens from stack to output until new operator or fn is not found
                while let Some(t) = stack.pop() {
                    match t {
                        Token::Operator(_) | Token::Fn(_) => {
                            out.push(t);
                            break;
                        }
                        _ => out.push(t),
                    }
                }
            }
            _ => {
                // not an operator, move to stack
                stack.push(token);
            }
        }
        debug!("Out: {:?}", out);
        debug!("Stack: {:?}\n", stack);
    }

    if let Some(v) = stack.pop() {
        println!("Asnwer {:?}", v);
    }
}
