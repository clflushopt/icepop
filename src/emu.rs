//! 64-bit RISC-V RV64i emulator.
use crate::machine::Register;
use crate::mmu::{Mmu, Permission, VirtAddr, DEFAULT_EMU_MMU_SIZE, PERM_EXEC};
/// RISC-V 64-bit has 33 64-bit wide registers.
const MAX_CPU_REGISTERS: usize = 33;

/// Single threaded RISC-V RV64i emulator with an MMU.
pub struct Emulator {
    /// Memory manager for this emulator.
    pub memory: Mmu,

    /// RV64i register state.
    registers: [u64; MAX_CPU_REGISTERS],
}

impl Emulator {
    /// Create a new `Emulator` with an mmu of default size (32 MB).
    pub fn new() -> Self {
        Self {
            memory: Mmu::new(DEFAULT_EMU_MMU_SIZE),
            registers: [0u64; MAX_CPU_REGISTERS],
        }
    }

    /// Reset emulator to its original state.
    pub fn reset(&mut self, other: &Self) {
        self.memory.reset(&other.memory);
        self.registers = other.registers;
    }

    /// Read a register.
    pub fn reg(&self, register: Register) -> u64 {
        self.registers[register as usize]
    }

    /// Set a register to `value`.
    pub fn set_reg(&mut self, register: Register, value: u64) {
        self.registers[register as usize] = value
    }

    /// Run the emulator loop.
    pub fn run(&mut self) -> Option<()> {
        loop {
            // Get current Pc.
            let pc = self.reg(Register::Pc);
            // Fetch next instruction.
            let inst = self
                .memory
                .read_into::<u32>(VirtAddr(pc as usize), Permission(PERM_EXEC))
                .expect("Failed to fetch next instruction");

            // Decode instruction.
            let opcode = inst & 0b1111111;

            match opcode {
                0b0110111 => {
                    // LUI.
                }
                _ => todo!(),
            }
        }
    }
}
