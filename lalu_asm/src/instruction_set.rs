use std::{collections::HashMap, fmt::Display, ops::Add};

use bimap::BiMap;
use derive_more::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use once_cell::sync::Lazy;

#[derive(Debug, Clone)]
pub struct InstructionSet {
    pub instructions: Vec<Instruction>,
}

impl InstructionSet {
    pub fn from_string(s: impl AsRef<str>) -> Self {
        let s = s.as_ref();

        let mut lines = s.lines().filter(|l| !l.is_empty()).collect::<Vec<_>>();

        let mut v = Vec::new();

        let mut jump_labels = HashMap::new();

        // First, register all labels and get rid of comments
        for (i, line) in lines.clone().iter().enumerate().rev() {
            let line = line
                .trim()
                .split([' ', ':'])
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>();

            if line.is_empty() {
                continue;
            }

            // Comments
            match line[0].chars().next().unwrap() {
                '#' | '/' => {
                    // Update the previously created jump labels, all of which are after this line
                    // (move them all down by one)
                    jump_labels.iter_mut().for_each(|(_label, idx)| *idx -= 1);

                    lines.remove(i);
                }
                _ => (),
            }

            // Labels
            match line[..] {
                ["label", label, ..] => {
                    // Update the previously created jump labels, all of which are after this line
                    // (move them all down by one)
                    jump_labels.iter_mut().for_each(|(_label, idx)| *idx -= 1);

                    jump_labels.insert(label.into(), i as u8);
                    // Remove from `lines`
                    lines.remove(i);
                }
                _ => (),
            }
        }

        println!("Labels:");
        jump_labels
            .iter()
            .for_each(|(label, idx)| println!("  {label}: {idx}"));

        for (i, line) in lines.iter().enumerate() {
            if let Some(ins) = Instruction::try_from_string_asm(line, &jump_labels) {
                v.push(ins);
            } else {
                if !line.is_empty() {
                    println!("Invalid instruction on line {}: `{line}`", i + 1);
                }
            }
        }

        Self { instructions: v }
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        self.instructions.iter().map(|ins| ins.to_byte()).collect()
    }
}

/// A 2-bit unsigned integer
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
    Add,
    Sub,
    Mul,
    Div,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
)]
pub struct U2(u8);

impl U2 {
    pub fn zero() -> Self {
        Self(0)
    }
    pub fn try_from_u8(n: u8) -> Option<Self> {
        if (0..4).contains(&n) {
            Some(Self(n))
        } else {
            None
        }
    }
}

macro_rules! impl_from_u2 {
    ($t:ty) => {
        impl From<U2> for $t {
            fn from(value: U2) -> Self {
                value.0 as $t
                // value.0.into()
            }
        }
    };
    ($t:ty, $($y:ty),+) => {
        impl_from_u2!($t);
        impl_from_u2!($($y),+);
    };
}
impl_from_u2!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, usize, isize);

impl Display for U2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Instruction {
    Add(Register, Register),
    Sub(Register, Register),
    Ldi(Register, U2),
    Ld(Register, Register),

    Mov(Register, Register),
    Store(Register, Register),
    Noop,

    Jump(u8),
    JumpNeg(u8),
}

impl Instruction {
    pub fn to_string_asm(&self) -> String {
        match self {
            Instruction::Add(rd, rs) => format!("add {rd},{rs}"),
            Instruction::Sub(rd, rs) => format!("sub {rd},{rs}"),
            Instruction::Ldi(rd, val) => format!("ldi {rd},{val}"),
            Instruction::Ld(rd, rs) => format!("ld {rd},{rs}"),
            Instruction::Mov(rd, rs) => format!("mov {rd},{rs}"),
            Instruction::Store(rd, rs) => format!("st {rd},{rs}"),
            Instruction::Noop => format!("nop"),
            Instruction::Jump(addr) => format!("jmp {addr}"),
            Instruction::JumpNeg(addr) => format!("jmpn {addr}"),
        }
    }
    /// Return type:
    /// * `Some(t) => The line was an instruction`
    /// * `None => The line was not a valid instruction. This could also mean an unknown jump label`
    pub fn try_from_string_asm(raw: &str, jump_labels: &HashMap<String, u8>) -> Option<Self> {
        // Format is "{opcode} {rd},{rs}"
        let raw = raw.to_lowercase();
        let components = raw.trim().split([' ', ',']);

        let components: Vec<_> = components.filter(|s| !s.is_empty()).collect();

        use Instruction::*;

        // Pattern match for the instruction
        // Note that each pattern has `, ..` at the end to allow comments at the end

        Some(match components[0..] {
            ["add", rd, rs, ..] => Add(
                Register::try_from_string_asm(rd)?,
                Register::try_from_string_asm(rs)?,
            ),
            ["sub", rd, rs, ..] => Sub(
                Register::try_from_string_asm(rd)?,
                Register::try_from_string_asm(rs)?,
            ),
            ["ldi", rd, val, ..] => Ldi(Register::try_from_string_asm(rd)?, U2(val.parse().ok()?)),
            ["ld", rd, rs, ..] => Ld(
                Register::try_from_string_asm(rd)?,
                Register::try_from_string_asm(rs)?,
            ),

            ["mov", rd, rs, ..] => Mov(
                Register::try_from_string_asm(rd)?,
                Register::try_from_string_asm(rs)?,
            ),
            ["st", rd, rs, ..] => Store(
                Register::try_from_string_asm(rd)?,
                Register::try_from_string_asm(rs)?,
            ),

            ["nop", ..] => Noop,

            ["jmp", label, ..] => Jump(*jump_labels.get(label)?),
            ["jmpn", label, ..] => JumpNeg(*jump_labels.get(label)?),

            _ => {
                // println!("Instruction not matched: {}", components.join(":"));
                return None;
            }
        })
    }
    pub fn to_byte(&self) -> u8 {
        match self {
            Instruction::Add(rd, rs)
            | Instruction::Sub(rd, rs)
            | Instruction::Ld(rd, rs)
            | Instruction::Mov(rd, rs)
            | Instruction::Store(rd, rs) => {
                let mut ins = match self {
                    Instruction::Add(_, _) => 0b0010,
                    Instruction::Sub(_, _) => 0b0011,
                    Instruction::Ld(_, _) => 0b1111,
                    Instruction::Mov(_, _) => 0b0110,
                    Instruction::Store(_, _) => 0b1011,
                    _ => unreachable!(),
                };

                ins |= (*rd as u8) << 6;
                ins |= (*rs as u8) << 4;

                ins
            }
            Instruction::Ldi(rd, val) => {
                let mut ins = 0b1110;
                ins |= (*rd as u8) << 6;
                ins |= (val.0) << 4;

                ins
            }
            Instruction::Noop => 0b0000_0110,
            Instruction::Jump(n) => {
                let mut ins = 0b00;
                ins |= *n << 2;
                ins
            }
            Instruction::JumpNeg(n) => {
                let mut ins = 0b01;
                ins |= *n << 2;
                ins
            }
        }
    }
}

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub struct Instruction {
//     pub opcode: Opcode,
//     pub rd: Register,
//     pub rs: Register,
// }

// impl Instruction {
//     pub fn to_string_asm(&self) -> String {
//         format!(
//             "{} {},{}",
//             self.opcode.to_string_asm(),
//             self.rd.to_string_asm(),
//             self.rs.to_string_asm()
//         )
//     }
//     /// Returns the binary representation of this instruction
//     pub fn to_byte(&self) -> u8 {
//         // {rd}{rs}{opcode}
//         let mut s = 0;
//         s |= (self.rd as u8) << 6;
//         s |= (self.rd as u8) << 4;
//         s |= self.opcode as u8;

//         s
//     }
//     pub fn try_from_string_asm(raw: &str) -> Option<Self> {
//         // Format is "{opcode} {rd},{rs}"
//         let components = raw.trim().split([' ', ',']);

//         let components: Vec<_> = components.filter(|s| !s.is_empty()).collect();

//         let opcode = Opcode::try_from_string_asm(components.get(0)?)?;
//         let rd = Register::try_from_string_asm(components.get(1)?)?;
//         let rs = Register::try_from_string_asm(components.get(2)?)?;

//         Some(Self { opcode, rd, rs })
//     }
// }

static OPCODE_NAMES: Lazy<BiMap<Opcode, &str>> = Lazy::new(|| {
    use Opcode::*;

    [(Add, "add"), (Sub, "sub")].into_iter().collect()
});

static REGISTER_NAMES: Lazy<BiMap<Register, &str>> = Lazy::new(|| {
    use Register::*;
    [(R0, "r0"), (R1, "r1"), (R2, "r2"), (R3, "r3")]
        .into_iter()
        .collect()
});

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Opcode {
    Add = 0b0010,
    Sub = 0b0011,
}

impl Opcode {
    pub fn to_string_asm(&self) -> &'static str {
        OPCODE_NAMES.get_by_left(self).unwrap()
    }
    pub fn try_from_string_asm(s: &str) -> Option<Self> {
        OPCODE_NAMES
            .get_by_right(s.to_lowercase().as_str())
            .copied()
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Register {
    R0 = 0b00,
    R1 = 0b01,
    R2 = 0b10,
    R3 = 0b11,
}

impl Register {
    pub fn to_string_asm(&self) -> &'static str {
        REGISTER_NAMES.get_by_left(self).unwrap()
    }
    pub fn try_from_string_asm(s: &str) -> Option<Self> {
        REGISTER_NAMES
            .get_by_right(s.to_lowercase().as_str())
            .copied()
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_asm())
    }
}

impl TryFrom<u8> for Register {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        use Register::*;
        match value {
            0 => Ok(R0),
            1 => Ok(R1),
            2 => Ok(R2),
            3 => Ok(R3),
            _ => Err(()),
        }
    }
}

impl From<Register> for u8 {
    fn from(value: Register) -> Self {
        value as u8
    }
}

#[cfg(test)]
mod tests {
    use crate::instruction_set::{Instruction, Opcode};

    use super::Register;

    #[test]
    fn test_to_string() {
        // ASM
        {
            assert_eq!(Register::R0.to_string_asm(), "r0");
            assert_eq!(Register::R1.to_string_asm(), "r1");
            assert_eq!(Register::R2.to_string_asm(), "r2");
            assert_eq!(Register::R3.to_string_asm(), "r3");

            assert_eq!(Opcode::Add.to_string_asm(), "add");
            assert_eq!(Opcode::Sub.to_string_asm(), "sub");
        }
    }
    #[test]
    fn test_from_string() {
        // Registers
        {
            use Register::*;
            assert_eq!(Register::try_from_string_asm("r0"), Some(R0));
            assert_eq!(Register::try_from_string_asm("r1"), Some(R1));
            assert_eq!(Register::try_from_string_asm("r2"), Some(R2));
            assert_eq!(Register::try_from_string_asm("r3"), Some(R3));
        }

        // Opcodes
        {
            use Opcode::*;
            assert_eq!(Opcode::try_from_string_asm("add"), Some(Add));
            assert_eq!(Opcode::try_from_string_asm("Add"), None);
            assert_eq!(Opcode::try_from_string_asm("sub"), Some(Sub));
        }

        // Instructions
        {
            let jump_labels = Default::default();

            use Opcode::*;
            use Register::*;

            assert_eq!(
                Instruction::try_from_string_asm("add R0,r1", &jump_labels),
                Some(Instruction::Add(R0, R1))
            );

            assert_eq!(
                Instruction::try_from_string_asm("  add    R0,        R1   ", &jump_labels),
                Some(Instruction::Add(R0, R1))
            );

            assert_eq!(
                Instruction::try_from_string_asm("sub R0,R1", &jump_labels),
                Some(Instruction::Sub(R0, R1))
            );

            // assert_eq!(
            //     Instruction::try_from_string_asm("  add    R0,        R1   "),
            //     Some(Instruction {
            //         opcode: Add,
            //         rd: R0,
            //         rs: R1
            //     })
            // );

            // assert_eq!(
            //     Instruction::try_from_string_asm("sub R0,R1"),
            //     Some(Instruction {
            //         opcode: Sub,
            //         rd: R0,
            //         rs: R1
            //     })
            // );
        }
    }
}
