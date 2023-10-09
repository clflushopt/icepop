//! RISC-V instruction decoder and machine specification.

/// RISC-V 64-bit has 33 64-bit wide registers.
pub const MAX_CPU_REGISTERS: usize = 33;

/// 64-bit RISC-V registers.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(usize)]
pub enum Register {
    // Zero register always holds 0.
    Zero = 0,
    Ra,
    Sp,
    Gp,
    Tp,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
    Pc,
}

impl From<u32> for Register {
    /// Transforms a `u32` to `Register`, this cast is useful when parsing
    /// instructions that encode source and destination registers.
    ///
    /// # Safety
    ///
    /// Caller must ensure that value is within the specified range [0..32)
    /// otherwise the assertion will fail.
    /// Since we use `#[repr(usize)]` the pointer cast is safe.
    fn from(value: u32) -> Self {
        assert!(value < 32);
        unsafe {
            core::ptr::read_unaligned(
                &(value as usize) as *const usize as *const Register,
            )
        }
    }
}

/// U-type instruction.
#[derive(Debug, Clone, Copy)]
pub struct Utype {
    pub imm: i64,
    pub rd: Register,
}

impl From<u32> for Utype {
    /// Decode a `Utype` instruction.
    fn from(inst: u32) -> Self {
        Self {
            imm: (inst & !0xfff) as i32 as i64,
            rd: Register::from((inst >> 7) & 0b11111),
        }
    }
}

/// J-type instruction.
#[derive(Debug, Clone, Copy)]
pub struct Jtype {
    pub imm: i32,
    pub rd: Register,
}

impl From<u32> for Jtype {
    /// Decode a `Jtype` instruction.
    fn from(inst: u32) -> Self {
        let imm20 = (inst >> 31) & 1;
        let imm101 = (inst >> 21) & 0b1111111111;
        let imm11 = (inst >> 20) & 1;
        let imm1912 = (inst >> 12) & 0b11111111;
        let imm =
            (imm20 << 20) | (imm1912 << 12) | (imm11 << 11) | (imm101 << 1);
        let imm = ((imm as i32) << 11) >> 11;

        Self {
            imm: imm,
            rd: Register::from((inst >> 7) & 0b11111),
        }
    }
}

/// I-type instruction.
#[derive(Debug, Clone, Copy)]
pub struct Itype {
    pub imm: i32,
    pub rs1: Register,
    pub funct3: u32,
    pub rd: Register,
}

impl From<u32> for Itype {
    /// Decode a `Itype` instruction.
    fn from(inst: u32) -> Self {
        let imm = (inst as i32) >> 20;
        let rs1 = Register::from((inst >> 15) & 0b11111);
        let rd = Register::from((inst >> 7) & 0b11111);
        let funct3 = (inst >> 12) & 0b111;

        Self {
            imm,
            rs1,
            funct3,
            rd,
        }
    }
}

/// B-type instruction.
#[derive(Debug, Clone, Copy)]
pub struct Btype {
    pub imm: i32,
    pub rs2: Register,
    pub rs1: Register,
    pub funct3: u32,
}

impl From<u32> for Btype {
    /// Decode a `Btype` instruction.
    fn from(inst: u32) -> Self {
        let imm12 = (inst >> 31) & 1;
        let imm105 = (inst >> 25) & 0b111111;
        let imm41 = (inst >> 8) & 0b1111;
        let imm11 = (inst >> 7) & 1;
        let imm = (imm12 << 12) | (imm11 << 11) | (imm105 << 5) | (imm41 << 1);
        let imm = ((imm as i32) << 19) >> 19;

        Self {
            imm: imm,
            rs2: Register::from((inst >> 20) & 0b11111),
            rs1: Register::from((inst >> 15) & 0b11111),
            funct3: (inst >> 12) & 0b111,
        }
    }
}

/// R-type instruction.
#[derive(Debug, Clone, Copy)]
pub struct Rtype {
    pub rs2: Register,
    pub rs1: Register,
    pub rd: Register,
    pub funct3: u32,
    pub funct7: u32,
}

impl From<u32> for Rtype {
    /// Decode a `Rtype` instruction.
    fn from(inst: u32) -> Self {
        Self {
            rs2: Register::from((inst >> 20) & 0b11111),
            rs1: Register::from((inst >> 15) & 0b11111),
            rd: Register::from((inst >> 7) & 0b11111),
            funct3: (inst >> 12) & 0b111,
            funct7: (inst >> 25) & 0b1111111,
        }
    }
}

/// S-type instruction.
#[derive(Debug, Clone, Copy)]
pub struct Stype {
    pub imm: i32,
    pub rs2: Register,
    pub rs1: Register,
    pub funct3: u32,
}

impl From<u32> for Stype {
    /// Decode a `Stype` instruction.
    fn from(inst: u32) -> Self {
        let imm115 = (inst >> 25) & 0b1111111;
        let imm40 = (inst >> 7) & 0b11111;
        let imm = (imm115 << 5) | (imm40);
        let imm = ((imm as i32) << 20) >> 20;
        Self {
            imm: imm,
            rs2: Register::from((inst >> 20) & 0b11111),
            rs1: Register::from((inst >> 15) & 0b11111),
            funct3: (inst >> 12) & 0b111,
        }
    }
}
