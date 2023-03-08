use std::ops::{Index, IndexMut};

use crate::instruction_set::{Instruction, InstructionSet, Opcode, Register};

#[derive(Clone)]
pub struct Runtime {
    // Instruction
    instruction_set: InstructionSet,
    instruction_ptr: usize,
    registers: [i16; 4],
    ram: Vec<i16>,
    /// The result of the most recently executed instruction
    prev_result: i16,
}

impl std::fmt::Debug for Runtime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Runtime")
            // .field("instruction_set", &self.instruction_set)
            .field("instruction_ptr", &self.instruction_ptr)
            .field("registers", &self.registers)
            .field("ram", &self.ram)
            .finish()
    }
}

impl Runtime {
    pub fn new(instruction_set: InstructionSet) -> Self {
        Self::new_with_ram(instruction_set, vec![0; 2_usize.pow(6)])
    }
    pub const fn instructions(&self) -> &InstructionSet {
        &self.instruction_set
    }
    pub const fn instruction_ptr(&self) -> usize {
        self.instruction_ptr
    }
    pub const fn prev_result(&self) -> i16 {
        self.prev_result
    }
    pub fn set_instruction_ptr(&mut self, instruction_ptr: usize) {
        self.instruction_ptr = instruction_ptr;
    }
    /// Returns a reference to the array of registers in self
    ///
    /// If a reference is needed to a specific register,
    /// use the `Index<Register>` implementation provided
    pub const fn registers(&self) -> &[i16; 4] {
        &self.registers
    }
    pub fn instructions_len(&self) -> usize {
        self.instruction_set.instructions.len()
    }
    /// `ram` is expected to be at least 2^6 values long
    pub fn new_with_ram(instruction_set: InstructionSet, ram: Vec<i16>) -> Self {
        Self {
            instruction_set,
            instruction_ptr: 0,
            registers: [0; 4],
            ram,
            prev_result: 0,
        }
    }
    /// Returns the next instruction which will be executed
    pub fn peek_instruction(&self) -> Option<Instruction> {
        self.instruction_set
            .instructions
            .get(self.instruction_ptr)
            .cloned()
    }
    /// Sets `self[rd] = n` and `self.prev_result = n`
    #[inline]
    fn set_rd(&mut self, rd: Register, n: i16) {
        self[rd] = n;
        self.prev_result = n;
    }
    pub fn execute_instruction(&mut self, ins: Instruction) {
        match ins {
            Instruction::Add(rd, rs) => self.set_rd(rd, self[rd].wrapping_add(self[rs])),
            Instruction::Sub(rd, rs) => self.set_rd(rd, self[rd].wrapping_sub(self[rs])),
            Instruction::Ldi(rd, n) => self.set_rd(rd, n.into()),
            Instruction::Ld(rd, rs) => self.set_rd(rd, self.ram[self[rs] as usize]),
            Instruction::Mov(rd, rs) => self.set_rd(rd, self[rs]),
            Instruction::Store(rd, rs) => {
                let addr = self[rs] as usize;
                self.ram[addr] = self[rd]
            }
            Instruction::Noop => (),
            Instruction::Jump(addr) => self.instruction_ptr = addr as usize,
            Instruction::JumpNeg(addr) => {
                if self.prev_result.is_negative() {
                    self.instruction_ptr = addr as usize
                }
            }
        }
    }
    pub fn step(&mut self) -> Option<()> {
        let ins = *self
            .instruction_set
            .instructions
            .get(self.instruction_ptr)?;
        self.instruction_ptr += 1;

        self.execute_instruction(ins);

        Some(())
    }
}

impl Index<Register> for Runtime {
    type Output = i16;

    fn index(&self, index: Register) -> &Self::Output {
        &self.registers[Into::<u8>::into(index) as usize]
    }
}

impl IndexMut<Register> for Runtime {
    fn index_mut(&mut self, index: Register) -> &mut Self::Output {
        &mut self.registers[Into::<u8>::into(index) as usize]
    }
}
