//! 64-bit RISC-V RV64i emulator.
use crate::machine::{
    Btype, Itype, Jtype, Register, Rtype, Stype, Utype, MAX_CPU_REGISTERS,
};
use crate::mmu::{Mmu, Permission, VirtAddr, DEFAULT_EMU_MMU_SIZE, PERM_EXEC};

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
        if register != Register::Zero {
            self.registers[register as usize]
        } else {
            0
        }
    }

    /// Set a register to `value`.
    pub fn set_reg(&mut self, register: Register, value: u64) {
        if register != Register::Zero {
            self.registers[register as usize] = value
        }
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

            println!("Executing  {:08b} @ {:08x}\n", opcode, pc);

            match opcode {
                0b0110111 => {
                    // LUI.
                    let inst = Utype::from(inst);
                    self.set_reg(inst.rd, inst.imm as i64 as u64);
                    print!("{:?}\n", inst);
                }
                0b0010111 => {
                    // AUIPC.
                    let inst = Utype::from(inst);
                    self.set_reg(
                        inst.rd,
                        (inst.imm as i64 as u64).wrapping_add(pc),
                    );
                }
                0b1101111 => {
                    // JAL.
                    let inst = Jtype::from(inst);
                    self.set_reg(inst.rd, pc.wrapping_add(4));
                    self.set_reg(
                        Register::Pc,
                        pc.wrapping_add(inst.imm as i64 as u64),
                    )
                }
                0b1100111 => {
                    // Itype instruction.
                    let inst = Itype::from(inst);
                    match inst.funct3 {
                        0b000 => {
                            // JALR.
                            // Target address of JALR.
                            let target = self
                                .reg(inst.rs1)
                                .wrapping_add(inst.imm as i64 as u64);
                            // Set pc to target address.
                            self.set_reg(inst.rd, pc.wrapping_add(4));
                            self.set_reg(Register::Pc, target);
                        }

                        _ => todo!(),
                    }
                }
                0b11000111 => {
                    // Btype instruction.
                    let inst = Btype::from(inst);

                    let rs1 = self.reg(inst.rs1);
                    let rs2 = self.reg(inst.rs2);
                    match inst.funct3 {
                        0b000 => {
                            // BEQ
                            if rs1 == rs2 {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                            }
                        }
                        0b001 => {
                            // BNE
                            if rs1 != rs2 {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                            }
                        }
                        0b100 => {
                            // BLT
                            if (rs1 as i64) < (rs2 as i64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                            }
                        }
                        0b101 => {
                            // BGE
                            if (rs1 as i64) >= (rs2 as i64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                            }
                        }
                        0b110 => {
                            // BLTU
                            if (rs1 as u64) < (rs2 as u64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                            }
                        }
                        0b111 => {
                            // BGEU
                            if (rs1 as u64) >= (rs2 as u64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                0b0000011 => {
                    // Itype instruction.
                    let inst = Itype::from(inst);
                    // Address to load from.
                    let addr = VirtAddr(
                        self.reg(inst.rs1).wrapping_add(inst.imm as i64 as u64)
                            as usize,
                    );
                    match inst.funct3 {
                        0b000 => {
                            // LB.
                            let mut b = [0u8; 1];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i8::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b001 => {
                            // LH.
                            let mut b = [0u8; 2];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i16::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b010 => {
                            // LW.
                            let mut b = [0u8; 4];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i32::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b100 => {
                            // LBU.
                            let mut b = [0u8; 1];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(inst.rd, u8::from_le_bytes(b) as u64);
                        }
                        0b101 => {
                            // LHU.
                            let mut b = [0u8; 2];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(inst.rd, u16::from_le_bytes(b) as u64);
                        }
                        _ => unreachable!(),
                    }
                }
                0b0100011 => {
                    // S-type instruction.
                    let inst = Stype::from(inst);
                    // Compute target address.
                    let addr = VirtAddr(
                        self.reg(inst.rs1).wrapping_add(inst.imm as i64 as u64)
                            as usize,
                    );

                    match inst.funct3 {
                        0b000 => {
                            // SB.
                            let val = self.reg(inst.rs2) as u8;
                            self.memory.write_into(addr, val)?;
                        }
                        0b001 => {
                            // SH.
                            let val = self.reg(inst.rs2) as u16;
                            self.memory.write_into(addr, val)?;
                        }
                        0b010 => {
                            // SW.
                            let val = self.reg(inst.rs2) as u32;
                            self.memory.write_into(addr, val)?;
                        }
                        _ => todo!(),
                    }
                }
                0b0010011 => {
                    // I-type instruction.
                    let inst = Itype::from(inst);

                    let rs1 = self.reg(inst.rs1);
                    let imm = inst.imm as i64 as u64;

                    match inst.funct3 {
                        0b000 => {
                            // ADDI
                            self.set_reg(inst.rd, rs1.wrapping_add(imm));
                        }
                        0b010 => {
                            // SLTI
                            if (rs1 as i64) < (imm as i64) {
                                self.set_reg(inst.rd, 1);
                            } else {
                                self.set_reg(inst.rd, 0);
                            }
                        }
                        0b011 => {
                            // SLTIU
                            if (rs1 as u64) < (imm as u64) {
                                self.set_reg(inst.rd, 1);
                            } else {
                                self.set_reg(inst.rd, 0);
                            }
                        }
                        0b100 => {
                            // XORI
                            self.set_reg(inst.rd, rs1 ^ imm);
                        }
                        0b110 => {
                            // ORI
                            self.set_reg(inst.rd, rs1 | imm);
                        }
                        0b111 => {
                            // ANDI
                            self.set_reg(inst.rd, rs1 & imm);
                        }
                        0b001 => {
                            // SLLI
                            let shamt = inst.imm & 0b111111;
                            self.set_reg(inst.rd, rs1 << shamt);
                        }
                        0b101 => {
                            let mode = (inst.imm >> 6) & 0b111111;

                            match mode {
                                0b0000000 => {
                                    // SRLI
                                    let shamt = inst.imm & 0b111111;
                                    self.set_reg(inst.rd, rs1 >> shamt);
                                }
                                0b0100000 => {
                                    // SRAI
                                    let shamt = inst.imm & 0b111111;
                                    self.set_reg(
                                        inst.rd,
                                        ((rs1 as i64) >> shamt) as u64,
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                0b0110011 => {
                    let inst = Rtype::from(inst);

                    match inst.funct3 {
                        _ => todo!(),
                    }
                }
                _ => todo!(),
            }
            // Increment PC to the next instruction.
            self.set_reg(Register::Pc, pc.wrapping_add(4));
        }
    }
}
