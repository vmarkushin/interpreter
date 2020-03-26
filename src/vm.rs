use num_traits::{NumCast, ToPrimitive};
use registers::*;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter, Write};
use std::mem::size_of;
use std::num::Wrapping;
use std::ops::{BitOrAssign, ShrAssign};

pub const SPECIAL_REGISTERS_COUNT: Reg = 8;
pub const COMMON_REGISTERS_COUNT: Reg = 8;
pub const REGISTERS_COUNT: Reg = COMMON_REGISTERS_COUNT + SPECIAL_REGISTERS_COUNT;
pub const DEFAULT_MEM_SIZE: Size = 1024;

pub type Word = u16;
pub type Size = Word;
pub type Reg = u8;
pub type Opcode = u32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    Data(String),
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

pub const FAMILY_OFFSET: Opcode = 30;

pub const DATA_PROCESS_INST_FAMILY: u8 = 0b00;
pub const DATA_PROCESS_IMMEDIATE_OPERAND_OFFSET: u8 = 29;
pub const DATA_PROCESS_REG_DEST_OFFSET: u8 = 16;
pub const DATA_PROCESS_VAL_OFFSET: u8 = 0;
pub const DATA_PROCESS_VAL_SIZE: u8 = 16;
pub const DATA_PROCESS_REG_VAL_OFFSET: u8 = 0;
pub const DATA_PROCESS_OPCODE_OFFSET: u8 = 20;
pub const DATA_PROCESS_OPCODE_SIZE: u8 = 4;

pub const DATA_TRANSFER_INST_FAMILY: u8 = 0b01;
pub const DATA_TRANSFER_IMMEDIATE_OFFSET_OFFSET: u8 = 29;
pub const DATA_TRANSFER_PRE_POST_INDEXING_OFFSET: u8 = 28;
pub const DATA_TRANSFER_BYTE_WORD_OFFSET: u8 = 27;
pub const DATA_TRANSFER_LOAD_STORE_OFFSET: u8 = 26;
pub const DATA_TRANSFER_REG_DEST_OFFSET: u8 = 16;
pub const DATA_TRANSFER_VAL_OFFSET: u8 = 0;
pub const DATA_TRANSFER_VAL_SIZE: u8 = 16;
pub const DATA_TRANSFER_REG_VAL_OFFSET: u8 = 0;

pub const BRANCH_INST_FAMILY: u8 = 0b10;
pub const BRANCH_LINK_BIT_OFFSET: u8 = 29;
pub const BRANCH_OFFSET_OFFSET: u8 = 0;
pub const BRANCH_OFFSET_SIZE: u8 = 20;

pub const STACK_INST_FAMILY: u8 = 0b11;
pub const STACK_PUSH_POP_BIT_OFFSET: u8 = 29;
pub const STACK_VAL_OFFSET: u8 = 0;
pub const STACK_VAL_SIZE: u8 = 16;

pub const REG_SIZE: u8 = 4;

pub const OPCODE_MOV: u8 = 0b0000;
pub const OPCODE_ADD: u8 = 0b0001;
pub const OPCODE_SUB: u8 = 0b0010;
pub const OPCODE_MUL: u8 = 0b0011;
pub const OPCODE_DIV: u8 = 0b0100;
pub const OPCODE_CMP: u8 = 0b0101;
pub const OPCODE_TST: u8 = 0b0110;

pub const READ_SUB_PROG_PTR: Size = 0;
pub const WRITE_SUB_PROG_PTR: Size = 1;
pub const ALLOC_SUB_PROG_PTR: Size = 2;

/// An assembly opcode.
///
/// All the commands is presented as motorolla-like (i.e. `OP A B` is literally equal `A := A OP B`)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instruction {
    /// Data processing
    ///
    /// +---+-+---------+-------+-------+------------------------------+
    /// |0 0|I|reserved |opcode |  Reg  |           operand            |
    /// 31--2928--------23------19------15----------------------------00
    ///
    /// Operand representation:
    ///  I == 0:
    ///   +-----------------------+------+
    ///   |       reserved        | Reg  |
    ///   15----------------------03----00
    ///  I == 1:
    ///   +------------------------------+
    ///   |             value            |
    ///   15----------------------------00
    ///
    /// I - immediate operand bit (0 = operand is a register, 1 = operand is an immediate value)
    ///
    /// Opcodes:
    /// MOV - 0000
    /// ADD - 0001
    /// SUB - 0010
    /// MUL - 0011
    /// DIV - 0100
    /// CMP - 0101
    /// TST - 0110
    MOV(Reg, Operand),
    ADD(Reg, Operand),
    SUB(Reg, Operand),
    MUL(Reg, Operand),
    DIV(Reg, Operand),
    CMP(Reg, Operand),
    TST(Reg, Operand),
    /// Data transfer
    ///
    /// +---+-+-+-+-+-----------+-------+------------------------------+
    /// |0 1|I|P|B|L| reserved  | Reg   |            offset            |
    /// +---+-+-+-+-+-----------+-------+------------------------------+
    ///
    /// Offset representation:
    ///  I == 0:
    ///   +------------------------------+
    ///   |            value             |
    ///   15-----------------------------+
    ///  I == 1:
    ///   +-----------------------+------+
    ///   |       reserved        | reg  |
    ///   15----------------------03----00
    ///
    /// I - immediate offset bit (0 = offset is an immediate value, 1 = offset is a register)
    /// P - pre/post indexing bit (0 = post; add operand after transfer, 1 = pre; add operand before transfer)
    /// B - byte/word bit (0 = transfer word quantity, 1 = transfer byte quantity)
    /// L - Load/Store bit (0 = store to memory, 1 = load from memory)
    LDR(Reg, Operand),
    STR(Reg, Operand),
    /// Branch and branch with link
    /// +---+-+-+---------------+--------------------------------------+
    /// |1 0|L|    reserved     |            offset (20 B)             |
    /// +---+-+-+---------------19-------------------------------------+
    ///
    /// L - Link bit (0 = branch, 1 = branch with link)
    B(Operand),
    BL(Operand),
    /// Stack manipulation
    ///
    /// +---+-+---------+-------+-------+------------------------------+
    /// |1 1|P|        reserved         |        operand (16 B)        |
    /// 31--2928------------------------15----------------------------00
    ///
    /// P - pus/pop (0 = push, 1 = pop)
    PUSH(Operand),
    POP(Operand),
}

impl Instruction {
    pub fn into_opcode(self) -> Opcode {
        self.into()
    }

    pub fn dest_reg(&self) -> Reg {
        match self {
            Instruction::MOV(r, _)
            | Instruction::ADD(r, _)
            | Instruction::SUB(r, _)
            | Instruction::MUL(r, _)
            | Instruction::DIV(r, _)
            | Instruction::LDR(r, _)
            | Instruction::STR(r, _)
            | Instruction::CMP(r, _)
            | Instruction::TST(r, _) => *r,
            Instruction::PUSH(_) | Instruction::POP(_) | Instruction::B(_) | Instruction::BL(_) => {
                0
            }
        }
    }

    pub fn dest_reg_and_op(&self) -> (Reg, &Operand) {
        match self {
            Instruction::MOV(r, op)
            | Instruction::ADD(r, op)
            | Instruction::SUB(r, op)
            | Instruction::MUL(r, op)
            | Instruction::DIV(r, op)
            | Instruction::LDR(r, op)
            | Instruction::CMP(r, op)
            | Instruction::TST(r, op)
            | Instruction::STR(r, op) => (*r, op),
            Instruction::PUSH(op)
            | Instruction::POP(op)
            | Instruction::B(op)
            | Instruction::BL(op) => (0, op),
        }
    }
    pub fn op_mut(&mut self) -> &mut Operand {
        match self {
            Instruction::MOV(_, op)
            | Instruction::ADD(_, op)
            | Instruction::SUB(_, op)
            | Instruction::MUL(_, op)
            | Instruction::DIV(_, op)
            | Instruction::LDR(_, op)
            | Instruction::TST(_, op)
            | Instruction::CMP(_, op)
            | Instruction::STR(_, op) => op,
            Instruction::PUSH(op)
            | Instruction::POP(op)
            | Instruction::B(op)
            | Instruction::BL(op) => op,
        }
    }
}

impl Into<Opcode> for Instruction {
    fn into(self) -> Opcode {
        let mut opcode = Opcode::default();

        let apply_trans = |mut opcode: Opcode, rd: Reg, op: Operand| {
            opcode |= 1 << FAMILY_OFFSET;
            opcode |= (rd as Opcode) << (DATA_TRANSFER_REG_DEST_OFFSET as Opcode);
            match op {
                Operand::Data(_data) => unimplemented!(),
                Operand::Word(word) => {
                    opcode |= word as Opcode;
                }
                Operand::Reg(rn) => {
                    opcode |= rn as Opcode;
                    opcode |= 1 << (DATA_TRANSFER_IMMEDIATE_OFFSET_OFFSET as Opcode);
                }
            };
            opcode
        };

        let apply_proc = |mut opcode: Opcode, rd: Reg, op: Operand| {
            opcode |= (rd as Opcode) << (DATA_PROCESS_REG_DEST_OFFSET as Opcode);
            match op {
                Operand::Data(_data) => unimplemented!(),
                Operand::Word(word) => {
                    opcode |= word as Opcode;
                    opcode |= 1 << (DATA_PROCESS_IMMEDIATE_OPERAND_OFFSET as Opcode);
                }
                Operand::Reg(rn) => {
                    opcode |= rn as Opcode;
                }
            };
            opcode
        };

        let apply_branch = |mut opcode: Opcode, op: Operand| {
            opcode |= (BRANCH_INST_FAMILY as Opcode) << FAMILY_OFFSET;
            match op {
                Operand::Data(_data) => unimplemented!(),
                Operand::Word(word) => {
                    opcode |= word as Opcode;
                }
                Operand::Reg(_rn) => unimplemented!(),
            };
            opcode
        };

        let apply_stack = |mut opcode: Opcode, op: Operand| {
            opcode |= (STACK_INST_FAMILY as Opcode) << FAMILY_OFFSET;
            match op {
                Operand::Data(_data) => unimplemented!(),
                Operand::Word(_word) => unimplemented!(),
                Operand::Reg(rn) => {
                    opcode |= rn as Opcode;
                }
            };
            opcode
        };

        match self {
            Instruction::LDR(rd, op) => {
                opcode |= 1 << (DATA_TRANSFER_LOAD_STORE_OFFSET as Opcode);
                opcode = apply_trans(opcode, rd, op);
            }
            Instruction::STR(rd, op) => {
                opcode = apply_trans(opcode, rd, op);
            }
            Instruction::MOV(rd, op) => {
                opcode |= (OPCODE_MOV as Opcode) << (DATA_PROCESS_OPCODE_OFFSET as Opcode);
                opcode = apply_proc(opcode, rd, op);
            }
            Instruction::ADD(rd, op) => {
                opcode |= (OPCODE_ADD as Opcode) << (DATA_PROCESS_OPCODE_OFFSET as Opcode);
                opcode = apply_proc(opcode, rd, op);
            }
            Instruction::SUB(rd, op) => {
                opcode |= (OPCODE_SUB as Opcode) << (DATA_PROCESS_OPCODE_OFFSET as Opcode);
                opcode = apply_proc(opcode, rd, op);
            }
            Instruction::MUL(rd, op) => {
                opcode |= (OPCODE_MUL as Opcode) << (DATA_PROCESS_OPCODE_OFFSET as Opcode);
                opcode = apply_proc(opcode, rd, op);
            }
            Instruction::DIV(rd, op) => {
                opcode |= (OPCODE_DIV as Opcode) << (DATA_PROCESS_OPCODE_OFFSET as Opcode);
                opcode = apply_proc(opcode, rd, op);
            }
            Instruction::B(op) => {
                opcode = apply_branch(opcode, op);
            }
            Instruction::BL(op) => {
                opcode |= 1 << (BRANCH_LINK_BIT_OFFSET as Opcode);
                opcode = apply_branch(opcode, op);
            }
            Instruction::PUSH(op) => {
                opcode = apply_stack(opcode, op);
            }
            Instruction::POP(op) => {
                opcode |= 1 << (STACK_PUSH_POP_BIT_OFFSET as Opcode);
                opcode = apply_stack(opcode, op);
            }
            _ => panic!(),
        };
        opcode
    }
}

pub fn bit_flag(opcode: Opcode, pos: u8) -> bool {
    opcode & (1 << pos as Opcode) != 0
}

pub fn bit_field(opcode: Opcode, pos: u8, size: u8) -> Opcode {
    let pos = pos as Opcode;
    let mut mask = (Wrapping(Opcode::default()) - Wrapping(1)).0;
    let i = (size_of::<Opcode>() * 8) as Opcode - size as Opcode;
    mask >>= i;
    mask <<= pos;
    (opcode & mask) >> pos
}

impl From<Opcode> for Instruction {
    fn from(opcode: Opcode) -> Self {
        let family = (opcode >> 30) as u8;
        match family {
            DATA_PROCESS_INST_FAMILY => {
                let is_immediate = bit_flag(opcode, DATA_PROCESS_IMMEDIATE_OPERAND_OFFSET);
                let op = if is_immediate {
                    Operand::Word(
                        bit_field(opcode, DATA_PROCESS_VAL_OFFSET, DATA_PROCESS_VAL_SIZE) as Word,
                    )
                } else {
                    Operand::Reg(bit_field(opcode, DATA_PROCESS_REG_VAL_OFFSET, REG_SIZE) as Reg)
                };
                let reg = bit_field(opcode, DATA_PROCESS_REG_DEST_OFFSET, REG_SIZE) as Reg;
                let opid =
                    bit_field(opcode, DATA_PROCESS_OPCODE_OFFSET, DATA_PROCESS_OPCODE_SIZE) as u8;

                match opid {
                    OPCODE_MOV => Instruction::MOV(reg, op),
                    OPCODE_ADD => Instruction::ADD(reg, op),
                    OPCODE_SUB => Instruction::SUB(reg, op),
                    OPCODE_MUL => Instruction::MUL(reg, op),
                    OPCODE_DIV => Instruction::DIV(reg, op),
                    _ => panic!("invalid opid"),
                }
            }
            DATA_TRANSFER_INST_FAMILY => {
                let is_load = bit_flag(opcode, DATA_TRANSFER_LOAD_STORE_OFFSET);
                let is_immediate = bit_flag(opcode, DATA_TRANSFER_IMMEDIATE_OFFSET_OFFSET);
                let op = if !is_immediate {
                    Operand::Word(bit_field(
                        opcode,
                        DATA_TRANSFER_VAL_OFFSET,
                        DATA_TRANSFER_VAL_SIZE,
                    ) as Word)
                } else {
                    Operand::Reg(bit_field(opcode, DATA_TRANSFER_REG_VAL_OFFSET, REG_SIZE) as Reg)
                };
                let reg = bit_field(opcode, DATA_TRANSFER_REG_DEST_OFFSET, REG_SIZE) as Reg;
                if is_load {
                    Instruction::LDR(reg, op)
                } else {
                    Instruction::STR(reg, op)
                }
            }
            BRANCH_INST_FAMILY => {
                let op = Operand::Word(
                    bit_field(opcode, BRANCH_OFFSET_OFFSET, BRANCH_OFFSET_SIZE) as Word
                );
                let is_link = bit_flag(opcode, BRANCH_LINK_BIT_OFFSET);
                if is_link {
                    Instruction::BL(op)
                } else {
                    Instruction::B(op)
                }
            }
            STACK_INST_FAMILY => {
                let op = Operand::Reg(bit_field(opcode, STACK_VAL_OFFSET, STACK_VAL_SIZE) as Reg);
                let is_pop = bit_flag(opcode, STACK_PUSH_POP_BIT_OFFSET);
                if is_pop {
                    Instruction::POP(op)
                } else {
                    Instruction::PUSH(op)
                }
            }
            _ => panic!("Unknown instruction {:032b}", opcode),
        }
    }
}

pub mod registers {
    use super::Reg;
    use crate::vm::COMMON_REGISTERS_COUNT;

    pub const R0: Reg = 0;
    pub const R1: Reg = R0 + 1;
    pub const R2: Reg = R1 + 1;
    pub const R3: Reg = R2 + 1;
    pub const R4: Reg = R3 + 1;
    pub const R5: Reg = R4 + 1;
    pub const R6: Reg = R5 + 1;
    pub const R7: Reg = R6 + 1;

    /// Program counter register.
    pub const PC: Reg = COMMON_REGISTERS_COUNT;
    /// Stack pointer register.
    pub const SP: Reg = COMMON_REGISTERS_COUNT + 1;
    /// Current program status register.
    pub const CPSR: Reg = COMMON_REGISTERS_COUNT + 2;
    /// Link register.
    pub const LR: Reg = COMMON_REGISTERS_COUNT + 3;
}

pub struct Vm {
    registers: [Word; REGISTERS_COUNT as usize],
    memory: [u8; DEFAULT_MEM_SIZE as usize],
    builtin_fns: [fn(&mut Self) -> (); 3],
}

impl Display for Vm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut reg_num = 0;
        while reg_num < REGISTERS_COUNT {
            if reg_num == PC {
                f.write_str("PC: ")?;
            } else if reg_num == SP {
                f.write_str("SP: ")?;
            } else {
                f.write_str("R")?;
                reg_num.fmt(f)?;
                f.write_str(": ")?;
            }
            self.read_reg(reg_num).fmt(f)?;
            f.write_char('\n')?;
            reg_num += 1;
        }

        let word_size = size_of::<Word>();
        let chunks = self.memory.chunks(word_size);
        let mut offset = 0;
        let bytes_per_line = 32;
        for (i, x) in chunks.enumerate() {
            if i % (bytes_per_line / word_size) == 0 {
                f.write_char('\n')?;
                f.write_str(&format!("<{:08X}> ", offset))?;
                offset += bytes_per_line;
            }

            for b in x {
                f.write_str(&format!("{:02X}", b))?;
            }
            f.write_char(' ')?;
        }
        f.write_char('\n')?;

        Ok(())
    }
}

impl Vm {
    pub fn new() -> Self {
        Vm {
            registers: [Word::default(); REGISTERS_COUNT as usize],
            memory: [0u8; DEFAULT_MEM_SIZE as usize],
            builtin_fns: [Vm::builtin_read, Vm::builtin_write, Vm::builtin_alloc],
        }
    }

    pub fn reset(&mut self) {
        self.registers = [Word::default(); REGISTERS_COUNT as usize];
        self.memory = [0; DEFAULT_MEM_SIZE as usize];
    }

    pub fn load_program(
        &mut self,
        consts: HashMap<String, Word>,
        parts: Vec<(String, Vec<Instruction>)>,
    ) {
        let mut pointer = 0;
        let mut consts_addrs = HashMap::<&str, Size>::new();
        for (cn, cv) in &consts {
            self.write_mem(pointer, *cv);
            consts_addrs.insert(&*cn, pointer);
            pointer += size_of::<Word>() as Size;
        }
        let mut labels_addrs = HashMap::<String, Size>::new();
        labels_addrs.insert("read".into(), DEFAULT_MEM_SIZE + READ_SUB_PROG_PTR);
        labels_addrs.insert("write".into(), DEFAULT_MEM_SIZE + WRITE_SUB_PROG_PTR);
        labels_addrs.insert("alloc".into(), DEFAULT_MEM_SIZE + ALLOC_SUB_PROG_PTR);

        let consts_offset = consts_addrs.len() as Size;
        let mut label_pointer = consts_offset;
        for (label, instructions) in &parts {
            let instructions_size = (instructions.len() * size_of::<Opcode>()) as Size;
            labels_addrs.insert(label.clone(), label_pointer);
            label_pointer += instructions_size;
        }

        self.write_reg(PC, pointer);

        for (_, instructions) in parts {
            for mut inst in instructions {
                let is_branch = matches!(&inst, Instruction::BL(_));
                let dest_reg = inst.dest_reg();
                let op = inst.op_mut();
                if let Operand::Data(name) = op {
                    let addr = if is_branch {
                        labels_addrs.get(name.as_str())
                    } else {
                        consts_addrs.get(name.as_str())
                    };
                    let addr = addr.unwrap_or_else(|| panic!("unknown address of '{}'", name));
                    println!("sub {} -> {}", name, addr);
                    *op = Operand::Word(*addr);
                }

                if dest_reg >= REGISTERS_COUNT {
                    panic!("Unknown register {}", dest_reg);
                }
                let i = inst.clone().into_opcode();
                self.write_mem(pointer, i);
                pointer += size_of::<Opcode>() as Size;
            }
        }

        self.write_reg(SP, pointer);
    }

    pub fn write_mem<T>(&mut self, address: Size, mut data: T)
    where
        T: Copy + NumCast + ShrAssign,
    {
        let data_size = size_of::<T>();
        for i in 0..data_size {
            self.memory[address as usize + i] = (data.to_u64().unwrap() & 0xFFu64).to_u8().unwrap();
            data >>= T::from(8).unwrap();
        }
    }

    pub fn read_mem<T>(&self, address: Size) -> T
    where
        T: Default + BitOrAssign + NumCast,
    {
        let mut data = T::default();
        for i in 0..size_of::<T>() {
            data |= T::from((self.memory[address as usize + i] as usize) << (i * 8)).unwrap();
        }
        data
    }

    pub fn write_reg<T>(&mut self, register: Reg, data: T)
    where
        T: Into<Word>,
    {
        self.registers[register as usize] = data.into();
    }

    pub fn read_reg(&self, register: Reg) -> Word {
        self.registers[register as usize]
    }

    pub fn push(&mut self, val: Word) {
        let addr = self.read_reg(SP);
        let naddr = addr + size_of::<Word>() as Size;
        self.write_mem(naddr, val);
        self.write_reg(SP, naddr);
    }

    pub fn pop(&mut self) -> Word {
        let addr = self.read_reg(SP);
        let val: Word = self.read_mem(addr);
        self.write_reg(SP, addr - size_of::<Word>() as Size);
        val
    }

    pub fn run(&mut self) {
        loop {
            let mut pc = self.read_reg(PC);
            let opcode: Opcode = self.read_mem(pc as Size);

            if opcode == 0 {
                debug!("Execution ended");
                break;
            }
            let inst = Instruction::from(opcode);
            let dr = inst.dest_reg();
            let dr_val = self.registers[dr as usize];
            match inst {
                Instruction::LDR(_, op) => match op {
                    Operand::Word(w) => {
                        let word = self.read_mem::<Word>(w);
                        self.write_reg(dr, word)
                    }
                    Operand::Reg(r) => {
                        let word = self.read_mem::<Word>(self.read_reg(r));
                        self.write_reg(dr, word)
                    }
                    Operand::Data(_) => panic!(),
                },
                Instruction::STR(_, op) => match op {
                    Operand::Word(w) => self.write_mem(w, dr_val),
                    Operand::Reg(r) => self.write_mem(self.read_reg(r), dr_val),
                    Operand::Data(_) => panic!(),
                },
                Instruction::MOV(_, op) => match op {
                    Operand::Word(w) => self.write_reg(dr, w),
                    Operand::Reg(r) => self.write_reg(dr, self.read_reg(r)),
                    Operand::Data(_) => panic!(),
                },
                Instruction::ADD(_, op) => match op {
                    Operand::Word(w) => {
                        let word = self.read_mem::<Word>(w);
                        self.write_reg(dr, dr_val.overflowing_add(word).0)
                    }
                    Operand::Reg(r) => {
                        self.write_reg(dr, dr_val.overflowing_add(self.read_reg(r)).0)
                    }
                    Operand::Data(_) => panic!(),
                },
                Instruction::MUL(_, op) => match op {
                    Operand::Word(w) => {
                        let word = self.read_mem::<Word>(w);
                        self.write_reg(dr, dr_val.overflowing_mul(word).0)
                    }
                    Operand::Reg(r) => {
                        self.write_reg(dr, dr_val.overflowing_mul(self.read_reg(r)).0)
                    }
                    Operand::Data(_) => panic!(),
                },
                Instruction::B(op) => match op {
                    Operand::Word(addr) => {
                        self.write_reg(PC, addr);
                    }
                    Operand::Reg(r) => {
                        let addr = self.read_reg(r);
                        self.write_reg(PC, addr);
                    }
                    Operand::Data(_) => panic!(),
                },
                Instruction::BL(op) => match op {
                    Operand::Word(addr) => {
                        self.write_reg(PC, addr);
                        if addr < DEFAULT_MEM_SIZE {
                            self.write_reg(LR, self.read_reg(PC));
                        } else {
                            self.builtin_fns[(addr - DEFAULT_MEM_SIZE) as usize](self);
                            // call builtin function
                        }
                    }
                    Operand::Reg(r) => {
                        let addr = self.read_reg(r);
                        self.write_reg(LR, self.read_reg(PC));
                        if addr < DEFAULT_MEM_SIZE {
                            self.write_reg(PC, addr);
                        } else {
                            self.builtin_fns[(addr - DEFAULT_MEM_SIZE) as usize](self);
                            // call builtin function
                        }
                    }
                    Operand::Data(_) => panic!(),
                },
                Instruction::PUSH(op) => match op {
                    Operand::Word(_addr) => panic!(),
                    Operand::Reg(r) => {
                        let val = self.read_reg(r);
                        self.push(val);
                    }
                    Operand::Data(_) => panic!(),
                },
                Instruction::POP(op) => match op {
                    Operand::Word(_addr) => panic!(),
                    Operand::Reg(r) => {
                        let val = self.pop();
                        self.write_reg(r, val);
                    }
                    Operand::Data(_) => panic!(),
                },
                _ => panic!("unimplemented instruction {:?}", inst),
            }
            pc += size_of::<Opcode>() as Word;
            self.write_reg(PC, pc);
        }
    }
}

impl Vm {
    fn builtin_read(&mut self) {
        #[cfg(not(test))]
        fn read_line() -> String {
            let mut line = String::new();
            std::io::stdin().read_line(&mut line).unwrap();
            line
        }

        #[cfg(test)]
        fn read_line() -> String {
            "123".into()
        }

        let count = self.pop();

        for _ in 0..count {
            let t = self.pop();
            let addr = self.pop() as Size;

            let mut line = read_line();
            match t {
                0 => {
                    let word = line.trim().parse::<Word>().expect("failed to parse word");
                    self.write_mem(addr, word);
                }
                1 => {
                    let bytes = line.into_bytes();
                    let l = bytes.len();
                    for (i, b) in bytes.into_iter().enumerate() {
                        self.write_mem(addr + i as Size, b);
                    }
                    self.write_mem(addr + l as Size, 0u8);
                }
                _ => panic!("unknown data type {}", t),
            }
        }
    }

    fn builtin_write(&mut self) {
        let count = self.pop();
        for _ in 0..dbg!(count) {
            let t = self.pop();
            let addr = self.pop() as Size;

            match t {
                0 => {
                    let word: Word = self.read_mem(addr);
                    println!("{}", word);
                }
                1 => {
                    let mut bytes = vec![];
                    let mut i = 0;
                    loop {
                        let b = self.read_mem(addr + i);
                        if b == 0 {
                            break;
                        }
                        bytes.push(b);
                        i += 1;
                    }
                    println!("{}", String::from_utf8(bytes).expect("invalid string"));
                }
                _ => panic!("unknown data type {}", t),
            }
        }
    }

    fn builtin_alloc(&mut self) {
        todo!("alloc")
    }
}

impl Default for Vm {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm_asm;

    #[test]
    fn test_vm() {
        let mut vm = Vm::new();
        vm.load_program(
            [("var".into(), 16u16), ("var2".into(), 32u16)]
                .iter()
                .cloned()
                .collect(),
            [
                (
                    "_start".into(),
                    vm_asm! {
                        MOV R0, 1;
                        ADD R0, [R0];
                        ADD R0, 10;
                        MUL R0, 4;
                        LDR R1, var;
                        ADD R1, var2;
                        STR R1, var;
                        LDR R2, var
                    }
                    .to_vec(),
                ),
                ("l1".into(), vec![]),
            ]
            .iter()
            .cloned()
            .collect(),
        );
        vm.run();
        assert_eq!(vm.read_reg(R0), 18);
        assert_eq!(vm.read_reg(R1), 48);
        assert_eq!(vm.read_reg(R2), 48);
        assert_eq!(vm.read_reg(PC), 36);
        println!("{}", vm);
    }

    #[test]
    fn test_io() {
        let mut vm = Vm::new();
        vm.load_program(
            [("a".into(), 10u16), ("b".into(), 10u16)]
                .iter()
                .cloned()
                .collect(),
            [(
                "_start".into(),
                // read two numbers, add together and write the result back
                vm_asm! {
                    MOV R0, 2;
                    MOV R1, 0;
                    MOV R2, a;
                    MOV R3, 0;
                    MOV R4, b;
                    PUSH R4;
                    PUSH R3;
                    PUSH R2;
                    PUSH R1;
                    PUSH R0;
                    BL read;
                    LDR R1, a;
                    LDR R2, b;
                    ADD R1, [R2];
                    STR R1, a;
                    MOV R1, a;
                    MOV R0, 1;
                    MOV R2, 0;
                    PUSH R1;
                    PUSH R2;
                    PUSH R0;
                    BL write
                }
                .to_vec(),
            )]
            .iter()
            .cloned()
            .collect(),
        );
        vm.run();

        vm.reset();
        // vm.load_program(
        //     [("a".into(), 10u16), ("b".into(), 10u16)]
        //         .iter()
        //         .cloned()
        //         .collect(),
        //     [(
        //         "_start".into(),
        //         // read string and write it back
        //         vm_asm! {
        //             PUSH 10;
        //             MOV R0, [PC];
        //             B alloc;
        //             MOV R1, 1;
        //             PUSH R1;
        //             PUSH R0;
        //             B read;
        //             PUSH R0;
        //             B write
        //         }
        //         .to_vec(),
        //     )]
        //     .iter()
        //     .cloned()
        //     .collect(),
        // );
    }

    #[test]
    fn test_stack() {
        let mut vm = Vm::new();
        vm.load_program(
            [("a".into(), 16u16), ("b".into(), 8u16)]
                .iter()
                .cloned()
                .collect(),
            [(
                "_start".into(),
                vm_asm! {
                    MOV R0, 20;
                    PUSH R0;
                    POP R0;
                    PUSH R0
                }
                .to_vec(),
            )]
            .iter()
            .cloned()
            .collect(),
        );
        vm.run();
        assert_eq!(vm.pop(), 20);
        vm.push(1);
        vm.push(2);
        vm.push(3);
        assert_eq!(vm.pop(), 3);
        assert_eq!(vm.pop(), 2);
        assert_eq!(vm.pop(), 1);
    }

    #[test]
    fn test_mem() {
        let mut vm = Vm::new();
        vm.load_program(
            [("a".into(), 16u16), ("b".into(), 8u16)]
                .iter()
                .cloned()
                .collect(),
            [(
                "_start".into(),
                vm_asm! {
                    LDR R0, a;
                    LDR R1, b;
                    ADD R0, [R1];
                    STR R0, a;
                    STR R0, b
                }
                .to_vec(),
            )]
            .iter()
            .cloned()
            .collect(),
        );
        vm.run();
        assert_eq!(vm.read_mem::<Word>(0), 24);
    }

    #[test]
    fn test_instructions() {
        let instruct = Instruction::LDR(0b1111, Operand::Word(0xFF));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b01_0001_000000_1111_0000000011111111u32);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::STR(0b11, Operand::Word(0xF));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b01_0000_000000_0011_0000000000001111u32);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::MOV(R1, Operand::Word(0b1010));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b00_1_00000_0000_0001_0000000000001010);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::ADD(R1, Operand::Word(0b1010));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b00_1_00000_0001_0001_0000000000001010);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::MUL(R0, Operand::Word(0xFFFF));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b00_1_00000_0011_0000_1111111111111111);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::B(Operand::Word(0xFFFF));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b10_0_00000_0000_0000_1111111111111111);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::BL(Operand::Word(0xFFFF));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b10_1_00000_0000_0000_1111111111111111);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::PUSH(Operand::Reg(3));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b11_0_00000_0000_0000_0000000000000011);
        assert_eq!(Instruction::from(opcode), instruct);

        let instruct = Instruction::POP(Operand::Reg(2));
        let opcode = instruct.clone().into_opcode();
        assert_eq!(opcode, 0b11_1_00000_0000_0000_0000000000000010);
        assert_eq!(Instruction::from(opcode), instruct);
        println!("{:032b}", opcode);
    }

    #[test]
    fn test_bit_field() {
        let opcode: u32 = 0b00001110_00000000_00000000_00000000;
        assert_eq!(bit_field(opcode, 25, 3), 0b111);
        assert_eq!(bit_field(opcode, 24, 3), 0b110);
        assert_eq!(bit_field(opcode, 26, 3), 0b011);
        assert_eq!(bit_field(opcode, 26, 4), 0b0011);
    }
}
