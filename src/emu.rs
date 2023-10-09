//! 64-bit RISC-V RV64i emulator.
use crate::machine::{
    Btype, Itype, Jtype, Register, Rtype, Stype, Utype, MAX_CPU_REGISTERS,
};
use crate::mmu::{
    Mmu, Permission, VirtAddr, DEFAULT_EMU_MMU_SIZE, PERM_EXEC, PERM_READ,
};

/// Single threaded RISC-V RV64i emulator with an MMU.
pub struct Emulator {
    /// Memory manager for this emulator.
    pub memory: Mmu,

    /// RV64i register state.
    registers: [u64; MAX_CPU_REGISTERS],

    /// Execution mode, supports `ExecMode::Debug`.
    mode: ExecMode,
}

/// Execution mode for the Emulator, note that `Debug` mode writes to `stdout`
/// on each fetch and should only be used when debugging.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecMode {
    // Debug mode writes debug logs to `stdout`.
    Debug,
    // Reset mode will reset the VM on each `VmExit`.
    Reset,
    // Jit mode will turn on the Jit.
    Jit,
}

/// Exit reasons for the Emulator.
#[derive(Debug, Copy, Clone)]
pub enum VmExit {
    /// VM exit due to a call to `exit()`.
    Exit,
    /// VM exit due to an unhandled syscall.
    Syscall,
    /// VM exit due an integer overflow.
    SyscallIntegerOverflow,
    /// VM exit due to a read fault @ `VirtAddr` of `usize` length.
    ReadFault(VirtAddr, usize),
}

impl Emulator {
    /// Create a new `Emulator` with an mmu of default size (32 MB).
    pub fn new() -> Self {
        Self {
            memory: Mmu::new(DEFAULT_EMU_MMU_SIZE),
            registers: [0u64; MAX_CPU_REGISTERS],
            mode: ExecMode::Debug,
        }
    }

    /// Mode sets the `ExecMode` on the emulator.
    pub fn set_mode(&mut self, mode: ExecMode) {
        self.mode = mode;
    }

    /// Prepare the VM stack with respect to ABI.
    pub fn prepare(&mut self) {
        /// Macro for stack push.
        macro_rules! push {
            ($expr:expr) => {
                let sp = self.reg(Register::Sp)
                    - core::mem::size_of_val(&$expr) as u64;
                self.memory
                    .write_into(VirtAddr(sp as usize), $expr)
                    .expect("Failed to push into the stack");
                self.set_reg(Register::Sp, sp);
            };
        }

        // Allocate stack memory.
        let stack = self
            .memory
            .alloc(32 * 1024)
            .expect("Failed to allocate stack space");
        // Set the stack pointer.
        self.set_reg(Register::Sp, stack.0 as u64 + 32 * 1024);
        // Set argv, argc, envp, auxp.
        let argv = self.memory.alloc(8).expect("Failed to allocate argv");
        // Write program name to argv.
        self.memory
            .write(argv, b"test\0")
            .expect("Failed to write to argv");
        // Push arguments in order.
        push!(0u64);
        push!(0u64);
        push!(0u64);
        push!(argv.0);
        push!(1u64);
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

    /// Handle system calls.
    pub fn handle_syscall(&mut self, syscall: u64) -> Result<(), VmExit> {
        match syscall {
            29 => {
                // ioctl()
                self.set_reg(Register::A0, !0);
                Ok(())
            }
            66 => {
                // writev()
                let _fd = self.reg(Register::A0);
                let iov = self.reg(Register::A1);
                let iovcnt = self.reg(Register::A2);
                let mut bytes_written = 0;

                for idx in 0..iovcnt {
                    let ptr = 16u64
                        .checked_mul(idx)
                        .and_then(|x| x.checked_add(iov))
                        .and_then(|x| x.checked_add(15))
                        .ok_or(VmExit::SyscallIntegerOverflow)?
                        as usize
                        - 15;

                    // Read the iovec entry pointer and length.
                    let buf: usize = self
                        .memory
                        .read_into(VirtAddr(ptr + 0), Permission(PERM_READ))
                        .ok_or(VmExit::ReadFault(VirtAddr(ptr + 0), 8))?;
                    let len: usize = self
                        .memory
                        .read_into(VirtAddr(ptr + 8), Permission(PERM_READ))
                        .ok_or(VmExit::ReadFault(VirtAddr(ptr + 8), 8))?;

                    // Read the iovec buffer.
                    let _data = self
                        .memory
                        .peek_perms(VirtAddr(buf), len, Permission(PERM_READ))
                        .ok_or(VmExit::ReadFault(VirtAddr(buf), len))?;

                    bytes_written += len as u64;

                    if self.mode == ExecMode::Debug {
                        if let Ok(data) = core::str::from_utf8(_data) {
                            print!("{}", data);
                        }
                    }
                }

                self.set_reg(Register::A0, bytes_written);
                Ok(())
            }
            96 => {
                // set_tid_address()
                self.set_reg(Register::A0, 0x1337);
                Ok(())
            }
            94 => Err(VmExit::Exit),
            _ => panic!("Unhandled syscall {syscall}"),
        }
    }

    /// Run the emulator loop.
    pub fn run(&mut self) -> Option<VmExit> {
        'next_inst: loop {
            // Get current Pc.
            let pc = self.reg(Register::Pc);
            // Fetch next instruction.
            let inst = self
                .memory
                .read_into::<u32>(VirtAddr(pc as usize), Permission(PERM_EXEC))
                .expect("Failed to fetch next instruction");

            // Decode instruction.
            let opcode = inst & 0b1111111;

            if self.mode == ExecMode::Debug {
                println!("Executing  {:08b} @ {:08x}\n", opcode, pc);
            }

            match opcode {
                0b0110111 => {
                    // LUI: Load Upper Immediate places the 20 bit U-immediate
                    // into bits 31-12 of register `rd` and places zero in the
                    // lowest 12 bits.
                    let inst = Utype::from(inst);
                    self.set_reg(inst.rd, inst.imm as i64 as u64);
                }
                0b0010111 => {
                    // AUIPC: Add Upper Immediate to PC is used for building
                    // pc-relative addresses. AUPIC appends 12 zero bits to
                    // the 20-bit U-immediate, sign extends the result to 64
                    // bits and adds it to the address of AUIPC.
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
                    );
                    continue 'next_inst;
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
                            continue 'next_inst;
                        }
                        _ => todo!(),
                    }
                }
                0b1100011 => {
                    // Btype instruction.
                    let inst = Btype::from(inst);

                    let rs1 = self.reg(inst.rs1);
                    let rs2 = self.reg(inst.rs2);
                    match inst.funct3 {
                        0b000 => {
                            // BEQ: Branches if registers rs1 and rs2 are
                            // equal.
                            if rs1 == rs2 {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );

                                continue 'next_inst;
                            }
                        }
                        0b001 => {
                            // BNE: Branches if registers rs1 and rs2 are not
                            // equal.
                            if rs1 != rs2 {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                                continue 'next_inst;
                            }
                        }
                        0b100 => {
                            // BLT: Branches if the signed rs1 is less than the
                            // signed rs2.
                            if (rs1 as i64) < (rs2 as i64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                                continue 'next_inst;
                            }
                        }
                        0b101 => {
                            // BGE: Branches if the signed rs1 is greater or
                            // equal than the signed rs2.
                            if (rs1 as i64) >= (rs2 as i64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                                continue 'next_inst;
                            }
                        }
                        0b110 => {
                            // BLTU: Similar to BLT but uses the unsigned
                            // comparison.
                            if (rs1 as u64) < (rs2 as u64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                                continue 'next_inst;
                            }
                        }
                        0b111 => {
                            // BGEU: Similar to BGE but uses the unsigned
                            // comparison.
                            if (rs1 as u64) >= (rs2 as u64) {
                                self.set_reg(
                                    Register::Pc,
                                    pc.wrapping_add(inst.imm as i64 as u64),
                                );
                                continue 'next_inst;
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
                            // LB: Load a byte from memory into the target
                            // register.
                            let mut b = [0u8; 1];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i8::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b001 => {
                            // LH: Load a half word (2 bytes) from memory into
                            // the target register.
                            let mut b = [0u8; 2];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i16::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b010 => {
                            // LW: Load a word (4 bytes) from memory into the
                            // target register.
                            let mut b = [0u8; 4];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i32::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b011 => {
                            // LD: Load double word from memory into the target
                            // register.
                            let mut b = [0u8; 8];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(
                                inst.rd,
                                i64::from_le_bytes(b) as i64 as u64,
                            );
                        }
                        0b100 => {
                            // LBU: Load byte from memory into the target
                            // register.
                            let mut b = [0u8; 1];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(inst.rd, u8::from_le_bytes(b) as u64);
                        }
                        0b101 => {
                            // LHU: Load half word from memory into the target
                            // register.
                            let mut b = [0u8; 2];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(inst.rd, u16::from_le_bytes(b) as u64);
                        }
                        0b110 => {
                            // LWU: Load word from memory into the target
                            // register.
                            let mut b = [0u8; 4];
                            self.memory.read(addr, &mut b)?;
                            self.set_reg(inst.rd, u32::from_le_bytes(b) as u64);
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
                            // SB:  Store single byte in memory.
                            let val = self.reg(inst.rs2) as u8;
                            self.memory.write_into(addr, val)?;
                        }
                        0b001 => {
                            // SH: Store half word in memory.
                            let val = self.reg(inst.rs2) as u16;
                            self.memory.write_into(addr, val)?;
                        }
                        0b010 => {
                            // SW: Store word in memory.
                            let val = self.reg(inst.rs2) as u32;
                            self.memory.write_into(addr, val)?;
                        }
                        0b011 => {
                            // SD: Store double word in memory.
                            let val = self.reg(inst.rs2) as u64;
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
                            // ADDI: Add immediate to Rd.
                            self.set_reg(inst.rd, rs1.wrapping_add(imm));
                        }
                        0b010 => {
                            // SLTI: Set Less Than Immediate sets the target
                            // register to 1 or 0 depending on comparison.
                            if (rs1 as i64) < (imm as i64) {
                                self.set_reg(inst.rd, 1);
                            } else {
                                self.set_reg(inst.rd, 0);
                            }
                        }
                        0b011 => {
                            // SLTIU: Similar to SLTI but uses unsigned compare.
                            if (rs1 as u64) < (imm as u64) {
                                self.set_reg(inst.rd, 1);
                            } else {
                                self.set_reg(inst.rd, 0);
                            }
                        }
                        0b100 => {
                            // XORI: Xor rs1 with immediate and store in Rd.
                            self.set_reg(inst.rd, rs1 ^ imm);
                        }
                        0b110 => {
                            // ORI: Or rs1 with immediate and store in Rd.
                            self.set_reg(inst.rd, rs1 | imm);
                        }
                        0b111 => {
                            // ANDI: And rs1 with immediate and store in Rd.
                            self.set_reg(inst.rd, rs1 & imm);
                        }
                        0b001 => {
                            // SLLI: Shift rs1 left by shift amount in imm
                            // and store in Rd.
                            let shamt = inst.imm & 0b111111;
                            self.set_reg(inst.rd, rs1 << shamt);
                        }
                        0b101 => {
                            // Uses the mode bits (last 6 bits) in the imm
                            // to decide whether it's a shift right logical
                            // or arithmetic.
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
                    let rs1 = self.reg(inst.rs1);
                    let rs2 = self.reg(inst.rs2);

                    match (inst.funct7, inst.funct3) {
                        (0b0000000, 0b000) => {
                            // ADD
                            self.set_reg(inst.rd, rs1.wrapping_add(rs2));
                        }
                        (0b0100000, 0b000) => {
                            // SUB
                            self.set_reg(inst.rd, rs1.wrapping_sub(rs2));
                        }
                        (0b0000000, 0b001) => {
                            // SLL
                            let shamt = rs2 & 0b111111;
                            self.set_reg(inst.rd, rs1 << shamt);
                        }
                        (0b0000000, 0b010) => {
                            // SLT
                            if (rs1 as i64) < (rs2 as i64) {
                                self.set_reg(inst.rd, 1);
                            } else {
                                self.set_reg(inst.rd, 0);
                            }
                        }
                        (0b0000000, 0b011) => {
                            // SLTU
                            if (rs1 as u64) < (rs2 as u64) {
                                self.set_reg(inst.rd, 1);
                            } else {
                                self.set_reg(inst.rd, 0);
                            }
                        }
                        (0b0000000, 0b100) => {
                            // XOR
                            self.set_reg(inst.rd, rs1 ^ rs2);
                        }
                        (0b0000000, 0b101) => {
                            let shamt = rs2 & 0b111111;
                            // SRL
                            self.set_reg(inst.rd, rs1 >> shamt);
                        }
                        (0b0100000, 0b101) => {
                            let shamt = rs2 & 0b111111;
                            // SRA
                            self.set_reg(
                                inst.rd,
                                ((rs1 as i64) >> shamt) as u64,
                            );
                        }
                        (0b0000000, 0b110) => {
                            // OR
                            self.set_reg(inst.rd, rs1 | rs2);
                        }
                        (0b0000000, 0b111) => {
                            // AND
                            self.set_reg(inst.rd, rs1 & rs2);
                        }
                        _ => unreachable!(),
                    }
                }
                0b0001111 => {
                    // Fence
                    let inst = Itype::from(inst);
                    match inst.funct3 {
                        0b000 => {
                            // FENCE
                        }
                        _ => unreachable!(),
                    }
                }
                0b1110011 => {
                    let inst = Itype::from(inst);
                    match inst.funct3 {
                        0b000 => {
                            if inst.imm == 0b0 {
                                // ECALL
                                return Some(VmExit::Syscall);
                                //panic!("Executing Syscall");
                            } else if inst.imm == 0b1 {
                                // EBREAK
                                panic!("EBREAK");
                            }
                        }
                        0b001 => {
                            // CSRRW
                        }
                        0b010 => {
                            // CSRRS
                        }
                        0b011 => {
                            // CSRRC
                        }
                        0b101 => {
                            // CSRRWI
                        }
                        0b110 => {
                            // CSRRSI
                        }
                        0b111 => {
                            // CSRRCI
                        }
                        _ => todo!(),
                    }
                }
                0b0011011 => {
                    // I-type instruction.
                    let inst = Itype::from(inst);

                    let rs1 = self.reg(inst.rs1) as u32;
                    let imm = inst.imm as u32;

                    match inst.funct3 {
                        0b000 => {
                            // ADDIW: Add immediate to Rd.
                            self.set_reg(
                                inst.rd,
                                rs1.wrapping_add(imm) as i64 as u64,
                            );
                        }
                        0b001 => {
                            let mode = (inst.imm >> 5) & 0b1111111;
                            match mode {
                                0b0000000 => {
                                    // SLLIW: Shift rs1 left by shift amount in imm
                                    // and store in Rd.
                                    let shamt = inst.imm & 0b111111;
                                    self.set_reg(
                                        inst.rd,
                                        (rs1 << shamt) as i32 as i64 as u64,
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        0b101 => {
                            // Uses the mode bits (last 6 bits) in the imm
                            // to decide whether it's a shift right logical
                            // or arithmetic.
                            let mode = (inst.imm >> 5) & 0b1111111;

                            match mode {
                                0b0000000 => {
                                    // SRLIW
                                    let shamt = inst.imm & 0b11111;
                                    self.set_reg(
                                        inst.rd,
                                        (rs1 >> shamt) as i32 as i64 as u64,
                                    );
                                }
                                0b0100000 => {
                                    // SRAIW
                                    let shamt = inst.imm & 0b11111;
                                    self.set_reg(
                                        inst.rd,
                                        ((rs1 as i32) >> shamt) as i64 as u64,
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                0b0111011 => {
                    let inst = Rtype::from(inst);
                    let rs1 = self.reg(inst.rs1) as u32;
                    let rs2 = self.reg(inst.rs2) as u32;

                    match (inst.funct7, inst.funct3) {
                        (0b0000000, 0b000) => {
                            // ADDW
                            self.set_reg(
                                inst.rd,
                                rs1.wrapping_add(rs2) as i32 as i64 as u64,
                            );
                        }
                        (0b0100000, 0b000) => {
                            // SUBW
                            self.set_reg(
                                inst.rd,
                                rs1.wrapping_sub(rs2) as i32 as i64 as u64,
                            );
                        }
                        (0b0000000, 0b001) => {
                            // SLLW
                            let shamt = rs2 & 0b11111;
                            self.set_reg(
                                inst.rd,
                                (rs1 << shamt) as i32 as i64 as u64,
                            );
                        }
                        (0b0000000, 0b101) => {
                            let shamt = rs2 & 0b11111;
                            // SRLW
                            self.set_reg(
                                inst.rd,
                                (rs1 >> shamt) as i32 as i64 as u64,
                            );
                        }
                        (0b0100000, 0b101) => {
                            let shamt = rs2 & 0b11111;
                            // SRAW
                            self.set_reg(
                                inst.rd,
                                ((rs1 as i32) >> shamt) as i64 as u64,
                            );
                        }
                        _ => unreachable!(),
                    }
                }
                _ => unimplemented!("Unhandled opcode {:#08b}\n", opcode),
            }
            // Increment PC to the next instruction.
            self.set_reg(Register::Pc, pc.wrapping_add(4));
        }
    }
}

#[allow(unused_imports)]
mod tests {
    use super::*;
    use crate::elf;
    use crate::mmu;
    use crate::mmu::{
        Mmu, Permission, VirtAddr, DEFAULT_EMU_MMU_SIZE, PERM_EXEC, PERM_READ,
        PERM_WRITE,
    };
    use std::env;
    use std::path::Path;

    #[test]
    #[ignore = "this test is for compliance only and isn't properly handled"]
    fn can_run_add_compliance_test() {
        let mut emu = Emulator::new();

        let env_var = env::var("CARGO_MANIFEST_DIR").unwrap();
        let path = Path::new(&env_var).join("support/compliance/rv64ui-p-add");
        let test_app_entry_point = 0x80000000;

        emu.memory
            .load(
                path,
                &[
                    elf::Section {
                        file_offset: 0x0000000000001000,
                        virt_addr: mmu::VirtAddr(0x0000000080000000),
                        file_size: 0x00000000000006bc,
                        mem_size: 0x00000000000006bc,
                        permissions: mmu::Permission(PERM_READ | PERM_EXEC),
                    },
                    elf::Section {
                        file_offset: 0x0000000000002000,
                        virt_addr: mmu::VirtAddr(0x0000000080001000),
                        file_size: 0x0000000000000048,
                        mem_size: 0x0000000000000048,
                        permissions: mmu::Permission(PERM_READ | PERM_WRITE),
                    },
                ],
            )
            .expect("Failed to read test binary");

        // Set program counter to our test app entry point.
        emu.set_reg(Register::Pc, test_app_entry_point);
        emu.run().expect("Failed to run emulator loop");
    }
}
