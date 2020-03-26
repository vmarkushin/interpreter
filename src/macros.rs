#[macro_export(local_inner_macros)]
macro_rules! vm_inst {
    (POP $dr:ident) => {
        crate::vm::Instruction::POP(crate::vm::Operand::Reg($dr))
    };
    (PUSH $dr:ident) => {
        crate::vm::Instruction::PUSH(crate::vm::Operand::Reg($dr))
    };
    ($cmd:ident $w:literal) => {
        crate::vm::Instruction::$cmd(crate::vm::Operand::Word($w))
    };
    ($cmd:ident $v:ident) => {
        crate::vm::Instruction::$cmd(crate::vm::Operand::Data(core::stringify!($v).into()))
    };
    ($cmd:ident [$sr:ident]) => {
        crate::vm::Instruction::$cmd(crate::vm::Operand::Reg($sr))
    };
    ($cmd:ident $dr:ident, [$sr:ident]) => {
        crate::vm::Instruction::$cmd($dr, crate::vm::Operand::Reg($sr))
    };
    ($cmd:ident $dr:ident, $w:literal) => {
        crate::vm::Instruction::$cmd($dr, crate::vm::Operand::Word($w))
    };
    ($cmd:ident $dr:ident, $v:ident) => {
        crate::vm::Instruction::$cmd($dr, crate::vm::Operand::Data(core::stringify!($v).into()))
    };
}

#[macro_export]
macro_rules! vm_asm {
    (
        $(
            $x:ident $( $y:tt ),*
        );*
    ) => {
        &[ $(crate::vm_inst!($x $( $y ),*)),* ]
    }
}

#[cfg(test)]
mod tests {
    use crate::vm::registers::*;
    use crate::vm::{Instruction, Operand};

    #[test]
    fn test_asm_gen() {
        let gen = vm_asm!(
            MOV R0, 1;
            ADD R0, [R0];
            ADD R0, 10;
            MUL R0, 4;
            LDR R1, var;
            ADD R1, var2;
            STR R1, var;
            LDR R2, var
        );
        assert_eq!(
            gen,
            &[
                Instruction::MOV(R0, Operand::Word(1)),
                Instruction::ADD(R0, Operand::Reg(R0)),
                Instruction::ADD(R0, Operand::Word(10)),
                Instruction::MUL(R0, Operand::Word(4)),
                Instruction::LDR(R1, Operand::Data("var".into())),
                Instruction::ADD(R1, Operand::Data("var2".into())),
                Instruction::STR(R1, Operand::Data("var".into())),
                Instruction::LDR(R2, Operand::Data("var".into())),
            ]
        );
        let gen = vm_asm!(
            MOV R0, 10;
            LDR R2, var;
            SUB R0, [R0];
            B 0x100;
            BL label;
            PUSH R4;
            POP R3
        );
        assert_eq!(
            gen,
            &[
                Instruction::MOV(R0, Operand::Word(10)),
                Instruction::LDR(R2, Operand::Data("var".into())),
                Instruction::SUB(R0, Operand::Reg(R0)),
                Instruction::B(Operand::Word(0x100)),
                Instruction::BL(Operand::Data("label".into())),
                Instruction::PUSH(Operand::Reg(R4)),
                Instruction::POP(Operand::Reg(R3)),
            ]
        );
    }
}
