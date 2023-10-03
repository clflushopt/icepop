//! RISC-V instruction decoder.

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

impl From<u8> for Register {
    fn from(value: u8) -> Self {
        assert!(value < 32);
        unsafe {
            core::ptr::read_unaligned(
                &(value as usize) as *const usize as *const Register,
            )
        }
    }
}

/// U-type instruction.
pub struct Utype {
    imm: i64,
    rd: Register,
}
