#![feature(box_syntax)]

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

    let mut expr = "1 - (2 * 3) < 4 == false";
    let (mut out, vars) = parse(&mut expr);
    debug!("Tokens: {:?}\n", out);
}
