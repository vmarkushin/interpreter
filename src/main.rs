use crate::Operator::OpenBracket;
use std::cmp::Ordering;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord)]
enum Operator {
    ClosedBracket,
    Add,
    Sub,
    Mul,
    Div,
    OpenBracket,
}

impl Operator {
    pub fn priority(&self) -> u32 {
        match self {
            Operator::ClosedBracket => 0,
            Operator::Add | Operator::Sub => 1,
            Operator::Mul | Operator::Div => 2,
            Operator::OpenBracket => 3,
        }
    }

    pub fn apply(&self, a: i64, b: i64) -> i64 {
        match self {
            Operator::Add => a + b,
            Operator::Sub => a - b,
            Operator::Mul => a * b,
            Operator::Div => a / b,
            _ => unreachable!(),
        }
    }
}

impl PartialOrd for Operator {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.priority().partial_cmp(&other.priority())
    }
}

impl FromStr for Operator {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 1 {
            Err(())
        } else {
            match s {
                "(" => Ok(Operator::OpenBracket),
                ")" => Ok(Operator::ClosedBracket),
                "+" => Ok(Operator::Add),
                "-" => Ok(Operator::Sub),
                "*" => Ok(Operator::Mul),
                "/" => Ok(Operator::Div),
                _ => Err(()),
            }
        }
    }
}

fn main() {
    let expr = "(12+(((8/2)+((2)))/2))/5+2";
    let mut operands: Vec<i64> = vec![];
    let mut operators: Vec<Operator> = vec![];
    let l = expr.len();
    let mut ind = 0;
    let mut tmp_num = "".to_string();

    while ind < l {
        let c = expr.chars().nth(ind).unwrap();
        if c.is_numeric() {
            tmp_num.push(c);
            if ind == l - 1 {
                operands.push(tmp_num.parse().expect("Invalid number"));
                break;
            }
        } else {
            if !tmp_num.is_empty() {
                operands.push(tmp_num.parse().expect("Invalid number"));
                tmp_num = "".to_string();
            }

            let next_op: Operator =
                Operator::from_str(&c.to_string()).expect("Invalid operator");

            if !operators.is_empty() {
                loop {
                    if let Some(last_op) = operators.last() {
                        if operands.len() < 2 || *last_op == Operator::OpenBracket {
                            break;
                        }
                        if *last_op as u32 >= next_op as u32 {
                            let last_op = operators.pop().unwrap();
                            let b = operands.pop().unwrap();
                            let a = operands.pop().unwrap();
                            let result = last_op.apply(a, b);
                            operands.push(result);
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }

                if next_op == Operator::ClosedBracket {
                    let should_be_bracket = operators.pop().expect("Expected bracket");
                    if should_be_bracket != Operator::OpenBracket {
                        panic!("Expected open bracket");
                    }
                    ind += 1;
                    continue;
                }
            }
            operators.push(next_op);
        }
        ind += 1;
    }
    println!("operators={:?}", operators);
    println!("operands={:?}", operands);

    while let Some(op) = operators.pop() {
        let b = operands.pop().expect("Expected a");
        let a = operands.pop().expect("Expected b");
        let result = op.apply(a, b);
        operands.push(result);
    }

    println!("result={}", operands.pop().unwrap());
}
