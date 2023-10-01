//! 64-bit RISC-V RV64i emulator.
use crate::mmu::Mmu;

/// RISC-V 64-bit has 33 64-bit wide registers.
const MAX_REGISTERS: usize = 33;

/// Single threaded RISC-V RV64i emulator with an MMU.
pub struct Emulator {
    /// Memory manager for this emulator.
    pub memory: Mmu,

    /// RV64i register state.
    registers: [u64; MAX_REGISTERS],
}

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
