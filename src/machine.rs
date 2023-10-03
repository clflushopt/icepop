//! RISC-V instruction decoder.

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

impl From<u8> for Register {
    /// Transform a `u8` to `Register`, this cast is useful when parsing
    /// instructions that encoded source and destination registers.
    ///
    /// # Safety
    ///
    /// Caller must ensure that value is within the specified range [0..32]
    /// otherwise the assertion will fail.
    /// Since we use `#[repr(usize)]` the pointer cast is safe.
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
