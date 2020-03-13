use crate::interpreter::Number;
use crate::syntax::Expr;
use crate::tokenizer::Literal;
use crate::tokenizer::{Operator, TokenMeta};
use std::ops::Deref;

type Word = i32;
type Reg = i32;

#[derive(Debug, Copy, Clone)]
pub enum Operand {
    Word(Word),
    Reg(Reg),
}

impl Operand {
    pub fn as_word(&self) -> Word {
        match self {
            Operand::Word(w) => *w,
            _ => panic!(),
        }
    }

    pub fn as_reg(&self) -> Reg {
        match self {
            Operand::Reg(r) => *r,
            _ => panic!(),
        }
    }
}

/// An assembly opcode.
///
/// All the commands is presented as motorolla-like (i.e. `OP A B` is literally equal `A = A OP B`)
#[derive(Debug)]
pub enum Instruction {
    LDR(Reg, Word),
    STR(Reg, Word),
    MOV(Reg, Operand),
    ADD(Reg, Operand),
    SUB(Reg, Operand),
    MUL(Reg, Operand),
    DIV(Reg, Operand),
}

#[derive(Debug)]
pub struct Tree {
    left: Box<Node>,
    right: Box<Node>,
    value: Node,
}

#[derive(Debug)]
pub struct Data {
    registers_need: usize,
    register_number: Reg,
}

/// Expression. Always evaluates to [`Value`](value) and may have side effects during evaluation.
#[derive(Debug)]
pub enum Node {
    /// Binary expression.
    ///
    /// # Example
    /// `a + b`
    Binary {
        op: Operator,
        data: Data,
        left: Box<Node>,
        right: Box<Node>,
    },
    /// Grouping expression.
    ///
    /// # Example
    /// `(a + b) * c`
    Grouping { data: Data, node: Box<Node> },
    /// Literal expression.
    ///
    /// # Examples
    /// - `321`
    /// - `"hi"`
    Literal { data: Data, lit: Literal },
    /// Unary expression.
    ///
    /// # Example
    /// - `-1`
    /// - `!false`
    Unary {
        op: Operator,
        data: Data,
        right: Box<Node>,
    },
    /// Variable expression. Evaluates to a value of the variable.
    ///
    /// # Example
    /// - `foo`
    Var { data: Data, meta: TokenMeta },
}

impl Data {
    pub fn new(registers_need: usize) -> Self {
        Data {
            registers_need,
            register_number: 0,
        }
    }
}

impl Node {
    pub fn data(&self) -> &Data {
        match self {
            Node::Binary { data, .. } => data,
            Node::Grouping { data, .. } => data,
            Node::Literal { data, .. } => data,
            Node::Unary { data, .. } => data,
            Node::Var { data, .. } => data,
        }
    }

    pub fn data_mut(&mut self) -> &mut Data {
        match self {
            Node::Binary { data, .. } => data,
            Node::Grouping { data, .. } => data,
            Node::Literal { data, .. } => data,
            Node::Unary { data, .. } => data,
            Node::Var { data, .. } => data,
        }
    }
}

/// Markups the given tree by how many registers each node would need.
#[allow(clippy::boxed_local)]
fn markup_registers_count(expr: Box<Expr>, is_left: bool) -> Node {
    match *expr {
        Expr::Binary { left, op, right } => {
            let left_subtree = markup_registers_count(left, true);
            let right_subtree = markup_registers_count(right, false);
            let n0 = left_subtree.data().registers_need;
            let n1 = right_subtree.data().registers_need;
            let n = if n0 == n1 { n0 + 1 } else { n0.max(n1) };
            Node::Binary {
                data: Data::new(n),
                left: box left_subtree,
                op,
                right: box right_subtree,
            }
        }
        Expr::Grouping { expr } => {
            let node = box markup_registers_count(expr, true);
            Node::Grouping {
                data: Data::new(node.data().registers_need),
                node,
            }
        }
        Expr::Literal { lit } => {
            let n = if is_left { 0 } else { 1 };
            Node::Literal {
                data: Data::new(n),
                lit,
            }
        }
        Expr::Unary { op, right } => {
            let right = box markup_registers_count(right, false);
            Node::Unary {
                data: Data::new(right.data().registers_need),
                op,
                right,
            }
        }
        Expr::Var(meta) => {
            let n = if is_left { 0 } else { 1 };
            Node::Var {
                data: Data::new(n),
                meta,
            }
        }
    }
}

/// Markups registers by number.
fn markup_registers(node: &mut Node) {
    match node {
        Node::Binary {
            left,
            op,
            right,
            data,
        } => {
            let nl = left.data().registers_need;
            let nr = right.data().registers_need;
            let rp = data.register_number;
            let (rl, rr) = if nl <= nr { (rp + 1, rp) } else { (rp, rp + 1) };
            left.data_mut().register_number = rl;
            right.data_mut().register_number = rr;
            markup_registers(left);
            markup_registers(right);
        }
        Node::Grouping { node, data } => {
            node.data_mut().register_number = data.register_number;
            markup_registers(node);
        }
        Node::Literal { lit, data } => {}
        Node::Unary { op, right, data } => {
            right.data_mut().register_number = data.register_number;
            markup_registers(right);
        }
        _ => {}
    };
}

fn binary_instruction(op: &Operator, reg: Reg, op1: Operand) -> Option<Instruction> {
    match op {
        Operator::Plus => Some(Instruction::ADD(reg, op1)),
        Operator::Minus => Some(Instruction::SUB(reg, op1)),
        Operator::Star => Some(Instruction::MUL(reg, op1)),
        Operator::Slash => Some(Instruction::DIV(reg, op1)),
        _ => None,
    }
}

struct Compiler {
    gen_instructions: Vec<Instruction>,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            gen_instructions: Vec::new(),
        }
    }

    fn add_inst(&mut self, inst: Instruction) {
        self.gen_instructions.push(inst);
    }

    pub fn generate_instructions(&mut self, node: &Node) {
        match node {
            Node::Binary {
                left,
                op,
                right,
                data,
            } => {
                self.generate_instructions(right);
                self.generate_instructions(left);
                match dbg!((left.deref(), right.deref())) {
                    (Node::Literal { data, lit }, _) => {
                        if left.data().registers_need == 0 {
                            let num = match lit {
                                Literal::Num(Number::Int(n)) => *n as Word,
                                _ => panic!("expected int"),
                            };
                            self.add_inst(
                                binary_instruction(op, data.register_number, Operand::Word(num))
                                    .expect("unsupported op"),
                            );
                        } else {
                            panic!()
                        }
                    }
                    (Node::Var { data, meta }, _) => {
                        if left.data().registers_need == 0 {
                            self.add_inst(
                                binary_instruction(op, data.register_number, Operand::Word(0))
                                    .expect("unsupported op"),
                            );
                        } else {
                            panic!()
                        }
                    }
                    (Node::Binary { data: ldata, .. }, Node::Binary { data: rdata, .. }) => {
                        let lrn = ldata.registers_need;
                        let rrn = rdata.registers_need;
                        if rrn >= lrn {
                            self.add_inst(
                                binary_instruction(
                                    op,
                                    ldata.register_number,
                                    Operand::Reg(data.register_number),
                                )
                                .unwrap(),
                            );
                        } else {
                            self.add_inst(
                                binary_instruction(
                                    op,
                                    data.register_number,
                                    Operand::Reg(rdata.register_number),
                                )
                                .unwrap(),
                            );
                            self.add_inst(Instruction::MOV(
                                rdata.register_number,
                                Operand::Reg(data.register_number),
                            ));
                        }
                    }
                    _ => unimplemented!("unimplemented op"),
                }
            }
            Node::Grouping { node, data } => {
                self.generate_instructions(node);
            }
            Node::Literal { lit, data } => {
                if data.registers_need == 1 {
                    match lit {
                        Literal::Num(num) => match num {
                            Number::Int(int) => {
                                if *int > std::i32::MAX as i64 {
                                    unimplemented!("double words are unsupported now")
                                }
                                self.add_inst(Instruction::LDR(data.register_number, *int as Word));
                            }
                            Number::Float(_float) => unimplemented!("floats are unsupported now"),
                        },
                        Literal::Str(_) => unimplemented!("strings are unsupported now"),
                        Literal::Bool(bool) => {
                            self.add_inst(Instruction::LDR(
                                data.register_number,
                                if *bool { 1 } else { 0 },
                            ));
                        }
                    }
                }
            }
            Node::Unary { op, right, data } => {
                self.generate_instructions(right);
                match op {
                    Operator::Minus => {}
                    Operator::ExMark => {}
                    _ => panic!("unexpected unary operator: {}", op),
                }
            }
            Node::Var { data, meta } => {
                if data.registers_need == 1 {
                    self.add_inst(Instruction::LDR(data.register_number, 0));
                }
            }
        };
    }

    pub fn generated(&self) -> &Vec<Instruction> {
        &self.gen_instructions
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::Number;

    #[test]
    fn registers_distribution() {
        fn var(name: &str) -> TokenMeta {
            TokenMeta {
                line: 0,
                column: 0,
                lexeme: name.into(),
            }
        }
        let expr = box Expr::Binary {
            left: box Expr::Binary {
                left: box Expr::Binary {
                    left: box Expr::Var(var("b")),
                    op: Operator::Plus,
                    right: box Expr::Var(var("c")),
                },
                op: Operator::Plus,
                right: box Expr::Binary {
                    left: box Expr::Var(var("f")),
                    op: Operator::Star,
                    right: box Expr::Var(var("g")),
                },
            },
            op: Operator::Star,
            right: box Expr::Binary {
                left: box Expr::Var(var("d")),
                op: Operator::Plus,
                right: box Expr::Literal {
                    lit: Literal::Num(Number::Int(3)),
                },
            },
        };
        let mut tree = markup_registers_count(expr, false);
        markup_registers(&mut tree);
        let mut comp = Compiler::new();
        comp.generate_instructions(&tree);
        let insts = comp.generated();
        println!("{:#?}", insts);
        panic!()
    }
}
