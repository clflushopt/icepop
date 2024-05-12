//! 64-bit RISC-V emulator for the user mode base level ISA `RV64i` with
//! support for memory hooks and just-in-time dynamic recompilation.
use std::arch::asm;
use std::process::Command;
use std::sync::{Arc, Mutex};

#[cfg(target_os = "linux")]
use crate::jit::{alloc_rwx, JitCache};
use crate::machine::{
    Btype, Csr, Itype, Jtype, Register, Rtype, Stype, Utype, MAX_CPU_REGISTERS,
};
use crate::mmu::{
    Mmu, Permission, VirtAddr, DEFAULT_EMU_MMU_SIZE, DIRTY_BLOCK_SIZE,
    PERM_EXEC, PERM_READ, PERM_WRITE,
};

/// Single threaded RISC-V RV64i emulator with an MMU.
pub struct Emulator {
    /// Memory manager for this emulator.
    pub memory: Mmu,

    /// RV64i register state.
    registers: [u64; MAX_CPU_REGISTERS],

    /// Control and status Register.
    csrs: [u64; 4096],

    /// Execution mode, supports `ExecMode::Debug`.
    mode: ExecMode,

    /// List of hooks to run before performing an IO operation.
    pre: Vec<fn()>,

    /// List of hooks to run after performing an IO operation.
    post: Vec<fn()>,

    /// Cache of jitted blocks.
    #[cfg(target_os = "linux")]
    jit_cache: Option<Arc<JitCache>>,
}

/// Execution mode for the Emulator, note that `Debug` mode writes to `stdout`
/// on each fetch and should only be used when debugging.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ExecMode {
    // Debug mode writes debug logs to `stdout`.
    Debug,
    // Reset mode will reset the VM on each `VmExit`.
    Reset,
    // Emulator mode will run the emulator using the interpreter.
    Emu,
    // Jit mode will run the emulator using the JIT.
    Jit,
}

/// Exit reasons for the Emulator.
#[derive(Debug, Copy, Clone)]
pub enum VmExit {
    /// VM exit due to a call to `exit()`.
    Exit,
    /// VM exit due to an unhandled syscall.
    Syscall,
    /// VM exit due an integer overflow in a syscall argument.
    IntegerOverflow,
    /// VM exit due to an out of bounds read or write that overflowed
    /// the address.
    OutOfBounds,
    /// VM exit due to a read fault caused by missing permissions.
    ReadFault(VirtAddr),
    /// VM exit due to a write fault caused by missing permissions.
    WriteFault(VirtAddr),
    /// VM exit due to an out of bounds address.
    AddressFault(VirtAddr, usize),
}

impl Emulator {
    /// Create a new `Emulator` with an mmu of default size (32 MB).
    pub fn new() -> Self {
        Self {
            memory: Mmu::new(DEFAULT_EMU_MMU_SIZE),
            registers: [0u64; MAX_CPU_REGISTERS],
            csrs: [0u64; 4096],
            mode: ExecMode::Debug,
            pre: vec![],
            post: vec![],
            #[cfg(target_os = "linux")]
            jit_cache: None,
        }
    }

    /// Mode sets the `ExecMode` on the emulator.
    pub fn set_mode(&mut self, mode: ExecMode) {
        #[cfg(target_os = "linux")]
        if mode == ExecMode::Jit {
            let mut jit_cache = Arc::new(JitCache::new(VirtAddr(1024 * 1024)));
            self.jit_cache = Some(jit_cache);
        }
        self.mode = mode;
    }

    /// Prepare the VM stack with respect to ABI.
    ///
    /// # Panics
    ///
    /// `prepare` panics if it is not able to allocate stack space.
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

    /// Fork an existing emulator to a new one with the same state.
    pub fn fork(&self) -> Self {
        Self {
            memory: self.memory.fork(),
            registers: self.registers.clone(),
            csrs: self.csrs.clone(),
            mode: self.mode,
            pre: self.pre.clone(),
            post: self.post.clone(),
            #[cfg(target_os = "linux")]
            jit_cache: self.jit_cache.clone(),
        }
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

    /// Read a control and status register.
    pub fn csr(&self, register: Csr) -> u64 {
        if register != Csr::SIE {
            self.csrs[register as usize]
        } else {
            self.csrs[Csr::MIE as usize] & self.csrs[Csr::MIDeleg as usize]
        }
    }

    /// Set a control and status register.
    pub fn set_csr(&mut self, register: Csr, value: u64) {
        if register != Csr::SIE {
            self.csrs[register as usize] = value
        } else {
            self.csrs[Csr::MIE as usize] = (self.csrs[Csr::MIE as usize]
                & !self.csrs[Csr::MIDeleg as usize])
                | (value & self.csrs[Csr::MIDeleg as usize]);
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
                        .ok_or(VmExit::IntegerOverflow)?
                        as usize
                        - 15;

                    // Read the iovec entry pointer and length.
                    let buf: usize = self
                        .memory
                        .read_into(VirtAddr(ptr + 0), Permission(PERM_READ))?;
                    let len: usize = self
                        .memory
                        .read_into(VirtAddr(ptr + 8), Permission(PERM_READ))?;

                    // Read the iovec buffer.
                    let _data = self.memory.view(
                        VirtAddr(buf),
                        len,
                        Permission(PERM_READ),
                    )?;

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
            93 | 94 => Err(VmExit::Exit),
            _ => panic!("Unhandled syscall {syscall}"),
        }
    }

    /// Run the emulator loop.
    pub fn run(&mut self) -> Result<(), VmExit> {
        #[cfg(target_os = "linux")]
        if self.mode == ExecMode::Jit {
            self.run_jit()
        }
        self.run_emu()
    }

    /// Run the emulator in Jit mode.
    #[cfg(target_os = "linux")]
    pub fn run_jit(&mut self) -> Result<(), VmExit> {
        // Load the translation table.
        let tlb = self.jit_cache.as_ref().unwrap().translation_table();

        let (memory, perms, dirty, dirty_bitmap) = self.memory.jit_addrs();
        let mut override_jit_addr = None;

        loop {
            let jit_addr =
                if let Some(override_jit_addr) = override_jit_addr.take() {
                    override_jit_addr
                } else {
                    // Load the current PC
                    let pc = self.reg(Register::Pc);
                    let (jit_addr, num_blocks) = {
                        let jit_cache = self.jit_cache.as_ref().unwrap();
                        (
                            jit_cache.lookup(VirtAddr(pc as usize)),
                            jit_cache.num_blocks(),
                        )
                    };

                    if let Some(jit_addr) = jit_addr {
                        jit_addr
                    } else {
                        // Compile every instruction in the current block
                        // to be assembled.
                        let asm = self
                            .generate_jit(VirtAddr(pc as usize), num_blocks)?;

                        // Write the assembly to a temporary file.
                        let asmfn = std::env::temp_dir().join(format!(
                            "fwetmp_{:?}.asm",
                            std::thread::current().id()
                        ));
                        let binfn = std::env::temp_dir().join(format!(
                            "fwetmp_{:?}.bin",
                            std::thread::current().id()
                        ));
                        std::fs::write(&asmfn, &asm)
                            .expect("Failed to write out assembly");

                        // Invoke NASM to generate the binary.
                        let res = Command::new("nasm")
                            .args(&[
                                "-f",
                                "bin",
                                "-o",
                                binfn.to_str().unwrap(),
                                asmfn.to_str().unwrap(),
                            ])
                            .status()
                            .expect("Failed to run nasm, is it in the path");
                        assert!(res.success(), "nasm exited with an error");

                        // Load the assembled binary and update the JIT cache.
                        let tmp = std::fs::read(&binfn)
                            .expect("Failed to read nasm output");
                        self.jit_cache
                            .as_ref()
                            .unwrap()
                            .update(VirtAddr(pc as usize), &tmp)
                    }
                };
            unsafe {
                // Invoke the jit
                let exit_code: u64;
                let reentry_pc: u64;
                let exit_info: u64;

                let dirty_inuse = self.memory.dirty_len();
                let new_dirty_inuse: usize;

                asm!(r#"
                    call {entry}
                    "#,
                entry = in(reg) jit_addr,
                out("rax") exit_code,
                out("rsi") reentry_pc,
                out("rdx") _,
                in("r8") memory,
                in("r9") perms,
                in("r10") dirty,
                in("r11") dirty_bitmap,
                inout("r12") dirty_inuse => new_dirty_inuse,
                in("r13") self.registers.as_ptr(),
                in("r14") tlb,
                );

                // Update the program counter reentry point
                self.set_reg(Register::Pc, reentry_pc);
                // Update the dirty state
                self.memory.set_dirty_len(new_dirty_inuse);

                match exit_code {
                    1 => {
                        // Branch decode request, continue as PC has been updated
                        // to new target branch.
                    }
                    2 => {
                        // Syscall
                        return Err(VmExit::Syscall);
                    }
                    4 => {
                        // Read fault
                        return Err(VmExit::ReadFault(VirtAddr(
                            reentry_pc as usize,
                        )));
                    }
                    5 => {
                        // Write fault
                        return Err(VmExit::WriteFault(VirtAddr(
                            reentry_pc as usize,
                        )));
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Run the emulator in interpreter mode.
    pub fn run_emu(&mut self) -> Result<(), VmExit> {
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
                println!("Executing  {opcode:08b} @ {pc:08x}\n");
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
                            let mode = (inst.imm >> 6) & 0b111111;

                            match mode {
                                0b000000 => {
                                    let shamt = inst.imm & 0b111111;
                                    self.set_reg(inst.rd, rs1 << shamt);
                                }
                                _ => unreachable!(),
                            }
                        }
                        0b101 => {
                            // Uses the mode bits (last 6 bits) in the imm
                            // to decide whether it's a shift right logical
                            // or arithmetic.
                            let mode = (inst.imm >> 6) & 0b111111;

                            match mode {
                                0b000000 => {
                                    // SRLI
                                    let shamt = inst.imm & 0b111111;
                                    self.set_reg(inst.rd, rs1 >> shamt);
                                }
                                0b010000 => {
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
                    let imm = ((inst & 0xfff00000) >> 20) as usize;
                    let inst = Itype::from(inst);
                    let rs1 = inst.rs1;
                    let rd = inst.rd;

                    match inst.funct3 {
                        0b000 => {
                            if inst.imm == 0b0 {
                                // ECALL
                                return Err(VmExit::Syscall);
                                //panic!("Executing Syscall");
                            } else if inst.imm == 0b1 {
                                // EBREAK
                                panic!("EBREAK");
                            }
                        }
                        0b001 => {
                            // CSRRW reads old value of CSR, zero-extends then
                            // writes it to rd.
                            //
                            let old = self.csr(Csr::from(imm));
                            self.set_csr(Csr::from(imm), self.reg(rs1));
                            self.set_reg(rd, old);
                        }
                        0b010 => {
                            // CSRRS
                            let old = self.csr(Csr::from(imm));
                            self.set_csr(Csr::from(imm), old | self.reg(rs1));
                            self.set_reg(rd, old);
                        }
                        0b011 => {
                            // CSRRC
                            let old = self.csr(Csr::from(imm));
                            self.set_csr(
                                Csr::from(imm),
                                old & (!self.reg(rs1)),
                            );
                            self.set_reg(rd, old);
                        }
                        0b101 => {
                            // CSRRWI
                            let zimm = imm as u64;
                            self.set_csr(Csr::from(imm), zimm);
                            self.set_reg(rd, self.csr(Csr::from(imm)));
                        }
                        0b110 => {
                            // CSRRSI
                            let zimm = imm as u64;
                            let old = self.csr(Csr::from(imm));
                            self.set_csr(Csr::from(imm), old | zimm);
                            self.set_reg(rd, old);
                        }
                        0b111 => {
                            // CSRRCI
                            let zimm = imm as u64;
                            let old = self.csr(Csr::from(imm));
                            self.set_csr(Csr::from(imm), old & (!zimm));
                            self.set_reg(rd, old);
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
                                rs1.wrapping_add(imm) as i32 as i64 as u64,
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

    /// Generate the assembly for the basic block at the given `pc`.
    #[cfg(target_os = "linux")]
    pub fn generate_jit(
        &mut self,
        pc: VirtAddr,
        num_blocks: usize,
    ) -> Result<String, VmExit> {
        let mut asm = "[bits 64]\n".to_string();

        let mut pc = pc.0 as u64;
        let mut block_instrs = 0;

        'next_inst: loop {
            // Check that the program counter is aligned.
            if pc & 3 != 0 {
                return Err(VmExit::AddressFault(VirtAddr(pc as usize), 0));
            }
            // Read the next instruction in this block.
            let inst: u32 = self
                .memory
                .read_into::<u32>(VirtAddr(pc as usize), Permission(PERM_EXEC))
                .map_err(|x| VmExit::AddressFault(VirtAddr(pc as usize), 0))?;
            // Extract the opcode.
            let opcode = inst & 0b1111111;

            // Label this instruction.
            asm += &format!("inst_pc_{:#x}:\n", pc);

            // Generate an assembly statement equivalent to a load.
            macro_rules! load_reg {
                    ($x86reg:expr, $reg:expr) => {
                        // Reading from the zero register is equivalent to clearing the destination
                        // register.
                        if $reg == Register::Zero  {
                            format!("xor {x86reg}, {x86reg}\n", x86reg = $x86reg)
                        } else {
                            // Otherwise emit a `mov`, `self.registers` is passed in `r13` and each
                            // register is 8 bytes long so the offset uses the base, index with
                            // scale approach.
                            format!("mov {x86reg}, qword [r13 + {reg} * 8]\n",
                                x86reg = $x86reg, reg = $reg as usize)
                        }
                    }
                }

            // Emit a store.
            macro_rules! store_reg {
                ($reg: expr, $x86reg: expr) => {
                    // Nothing to do here.
                    if $reg == Register::Zero {
                        String::new()
                    } else {
                        format!(
                            "mov qword [r13 + {reg} * 8], {x86reg}\n",
                            reg = $reg as usize,
                            x86reg = $x86reg
                        )
                    }
                };
            }

            // Codegen the instructions in the block.
            match opcode {
                0b0110111 => {
                    // LUI
                    let inst = Utype::from(inst);
                    asm += &store_reg!(inst.rd, inst.imm);
                }
                0b0010111 => {
                    // AUIPC
                    let inst = Utype::from(inst);
                    let val = (inst.imm as i64 as u64).wrapping_add(pc);
                    asm += &format!(
                        r#"\
                            mov rax, {imm:#x}
                            {store_rd_from_rax}
                        "#,
                        imm = val,
                        store_rd_from_rax = store_reg!(inst.rd, "rax")
                    );
                }
                0b1101111 => {
                    // JAL
                    let inst = Jtype::from(inst);

                    // Compute the return address
                    let ret = pc.wrapping_add(4);

                    // Compute the branch target
                    let target = pc.wrapping_add(inst.imm as i64 as u64);

                    if (target / 4) >= num_blocks as u64 {
                        // Branch target is out of bounds.
                        panic!("Target branch is out of bounds");
                    }
                    asm += &format!(
                        r#"
                        mov rax, {ret}
                        {store_rd_from_rax}

                        mov rax, [r14 + {target}]
                        test rax, rax
                        jz .jit_resolve

                        jmp rax

                        .jit_resolve:
                        mov rax, 1
                        mov rsi, {target_pc}
                        ret
                        "#,
                        ret = ret,
                        target_pc = target,
                        store_rd_from_rax = store_reg!(inst.rd, "rax"),
                        target = (target / 4) * 8
                    );
                    // Exit the current block and go to target.
                    break 'next_inst;
                }
                0b1100111 => {
                    let inst = Itype::from(inst);

                    match inst.funct3 {
                        0b000 => {
                            // JALR

                            // Compute the return address.
                            let ret = pc.wrapping_add(4);

                            asm += &format!(
                                r#"
                                mov rax, {ret}
                                {store_rd_from_rax}

                                {load_rax_from_rs1}
                                add rax, {imm}

                                shr rax, 2
                                cmp rax, {num_blocks}
                                jae .jit_resolve

                                mov rax, [r14 + rax * 8]
                                test rax, rax
                                jz .jit_resolve

                                jmp rax

                                .jit_resolve:
                                {load_rsi_from_rs1}
                                add rsi, {imm}
                                mov rax, 1
                                ret
                            "#,
                                imm = inst.imm,
                                ret = ret,
                                store_rd_from_rax = store_reg!(inst.rd, "rax"),
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs1 = load_reg!("rsi", inst.rs1),
                                num_blocks = num_blocks
                            );
                            break 'next_inst;
                        }
                        _ => unimplemented!("Unexpected 0b1100111"),
                    }
                }
                0b1100011 => {
                    let inst = Btype::from(inst);

                    match inst.funct3 {
                        0b000 | 0b001 | 0b100 | 0b101 | 0b111 => {
                            let cond = match inst.funct3 {
                                // Map conditional juimp from RISC-V to x86
                                0b000 =>
                                /* BEQ */
                                {
                                    "jne"
                                }
                                0b001 =>
                                /* BNE */
                                {
                                    "je"
                                }
                                0b100 =>
                                /* BLT */
                                {
                                    "jnl"
                                }
                                0b101 =>
                                /* BGE */
                                {
                                    "jnge"
                                }
                                0b110 =>
                                /* BLTU */
                                {
                                    "jnb"
                                }
                                0b111 =>
                                /* BGEU */
                                {
                                    "jnae"
                                }
                                _ => unreachable!(),
                            };

                            let target =
                                pc.wrapping_add(inst.imm as i64 as u64);

                            if (target / 4) >= num_blocks as u64 {
                                // Branch target is out of bounds.
                                panic!("Target branch is out of bounds");
                            }

                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}

                                cmp rax, rsi
                                {cond} .fallthrough

                                mov rax, [r14 + {target}]
                                test rax, rax
                                jz .jit_resolve

                                jmp rax

                                .jit_resolve:
                                mov rax, 1
                                mov rsi, {target_pc}
                                ret

                                .fallthrough:
                            "#,
                                cond = cond,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                target_pc = target,
                                target = (target / 4) * 8
                            );
                        }
                        _ => unimplemented!("Unexpected 0b1100011"),
                    }
                }
                0b0000011 => {
                    let inst = Itype::from(inst);

                    let (loadtyp, loadsz, regtyp, access_size) =
                        match inst.funct3 {
                            0b000 =>
                            /* LB */
                            {
                                ("movsx", "byte", "rsi", 1)
                            }
                            0b001 =>
                            /* LH */
                            {
                                ("movsx", "word", "rsi", 2)
                            }
                            0b010 =>
                            /* LW */
                            {
                                ("movsx", "dword", "rsi", 4)
                            }
                            0b011 =>
                            /* LD */
                            {
                                ("mov", "qword", "rsi", 8)
                            }
                            0b100 =>
                            /* LBU */
                            {
                                ("movzx", "byte", "rsi", 1)
                            }
                            0b101 =>
                            /* LHU */
                            {
                                ("movzx", "word", "rsi", 2)
                            }
                            0b110 =>
                            /* LWU */
                            {
                                ("mov", "dword", "esi", 4)
                            }
                            _ => unreachable!(),
                        };
                    // Compute the read permission mask.
                    let mut perm_mask = 0u64;
                    for ii in 0..access_size {
                        perm_mask |= (PERM_READ as u64) << (ii * 8)
                    }

                    asm += &format!(
                        r#"
                    {load_rax_from_rs1}
                    add rax, {imm}

                    cmp rax, {memory_len} - {access_size}
                    ja .fault

                    {loadtyp} {regtyp}, {loadsz} [r9 + rax]
                    mov rcx, {perm_mask}
                    and rsi, rcx
                    cmp rsi, rcx
                    je .nofault

                    .fault:
                    mov rcx, rax
                    mov rsi, {pc}
                    mov rax, 4
                    ret

                    .nofault:
                    {loadtyp} {regtyp}, {loadsz} [r8 + rax]
                    {store_rsi_into_rd}
                    "#,
                        load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                        store_rsi_into_rd = store_reg!(inst.rd, "rsi"),
                        loadtyp = loadtyp,
                        loadsz = loadsz,
                        regtyp = regtyp,
                        pc = pc,
                        access_size = access_size,
                        perm_mask = perm_mask,
                        memory_len = self.memory.len(),
                        imm = inst.imm
                    );
                }
                0b0100011 => {
                    let inst = Stype::from(inst);
                    let (loadtyp, loadsz, regtype, loadrt, access_size) =
                        match inst.funct3 {
                            0b000 =>
                            /* SB */
                            {
                                ("movzx", "byte", "sil", "esi", 1)
                            }
                            0b001 =>
                            /* SH */
                            {
                                ("movzs", "word", "si", "esi", 2)
                            }
                            0b010 =>
                            /* SW */
                            {
                                ("mov", "dword", "esi", "esi", 4)
                            }
                            0b011 =>
                            /* SD */
                            {
                                ("mov", "qword", "rsi", "rsi", 8)
                            }
                            _ => unreachable!(),
                        };

                    assert!(
                        DIRTY_BLOCK_SIZE.count_ones() == 1
                            && DIRTY_BLOCK_SIZE >= 8,
                        "Dirty block size must be a power of two and >= 8"
                    );
                    // Shift amount to get the block from an address.
                    let dirty_block_shift = DIRTY_BLOCK_SIZE.trailing_zeros();

                    // Compute the write permission mask
                    let mut perm_mask = 0u64;
                    for ii in 0..access_size {
                        perm_mask |= (PERM_WRITE as u64) << (ii * 8)
                    }

                    asm += &format!(
                        r#"
                        {load_rax_from_rs1}
                        add rax, {imm}

                        cmp rax, {memory_len} - {access_size}
                        ja .fault

                        {loadtyp} {loadrt}, {loadsz} [r9 + rax]
                        mov rcx, {perm_mask}
                        mov rdx, rsi
                        and rsi, rcx
                        cmp rsi, rcx
                        je .nofault

                        .fault:
                        mov rcx, rax
                        mov rsi, {pc}
                        mov rax, 5
                        ret

                        .nofault:
                        shl rcx, 2
                        and rdx, rcx
                        shr rdx, 3
                        mov rsi, rdx
                        or {loadsz} [r9 + rax], {regtype}

                        mov rcx, rax
                        shr rcx, {dirty_block_shift}
                        bts qword [r11], rcx
                        jc .continue

                        mov qword [r10 + r12 * 8], rcx
                        add r12, 1

                        .continue:
                        {load_rsi_from_rs2}
                        mov {loadsz} [r8 + rax], {regtype}
                    "#,
                        load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                        load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                        loadtyp = loadtyp,
                        loadsz = loadsz,
                        regtype = regtype,
                        imm = inst.imm,
                        loadrt = loadrt,
                        access_size = access_size,
                        perm_mask = perm_mask,
                        memory_len = self.memory.len(),
                        pc = pc,
                        dirty_block_shift = dirty_block_shift,
                    );
                }
                0b0010011 => {
                    let inst = Itype::from(inst);

                    match inst.funct3 {
                        0b000 => {
                            // ADDI
                            asm += &format!(
                                r#"
                            {load_rax_from_rs1}
                            add rax, {imm}
                            {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rax_into_rd = store_reg!(inst.rd, "rax"),
                                imm = inst.imm
                            );
                        }
                        0b010 => {
                            // SLTI
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                xor esi, esi
                                cmp rax, {imm}
                                setl sil
                                {store_rsi_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rsi_into_rd = store_reg!(inst.rd, "rsi"),
                                imm = inst.imm,
                            );
                        }
                        0b011 => {
                            // SLTIU
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                xor esi, esi
                                cmp rax, {imm}
                                setb sil
                                {store_rsi_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rsi_into_rd = store_reg!(inst.rd, "rsi"),
                                imm = inst.imm
                            );
                        }
                        0b100 => {
                            // XORI
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                xor rax, {imm}
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rax_into_rd = store_reg!(inst.rd, "rax"),
                                imm = inst.imm
                            );
                        }
                        0b110 => {
                            // ORI
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                or rax, {imm}
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rax_into_rd = store_reg!(inst.rd, "rax"),
                                imm = inst.imm
                            );
                        }
                        0b111 => {
                            // ANDI
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                and rax, {imm}
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rax_into_rd = store_reg!(inst.rd, "rax"),
                                imm = inst.imm
                            );
                        }

                        0b001 => {
                            let mode = (inst.imm >> 6) & 0b111111;

                            match mode {
                                0b000000 => {
                                    // SLLI
                                    let shamt = inst.imm & 0b111111;
                                    asm += &format!(
                                        r#"
                                        {load_rax_from_rs1}
                                        shl rax, {imm}
                                        {store_rax_into_rd}
                                    "#,
                                        load_rax_from_rs1 =
                                            load_reg!("rax", inst.rs1),
                                        store_rax_into_rd =
                                            store_reg!(inst.rd, "rax"),
                                        imm = shamt
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        0b101 => {
                            let mode = (inst.imm >> 6) & 0b111111;

                            match mode {
                                0b000000 => {
                                    // SRLI
                                    let shamt = inst.imm & 0b111111;
                                    asm += &format!(
                                        r#"
                                        {load_rax_from_rs1}
                                        shr rax, {imm}
                                        {store_rax_into_rd}
                                    "#,
                                        load_rax_from_rs1 =
                                            load_reg!("rax", inst.rs1),
                                        store_rax_into_rd =
                                            store_reg!(inst.rd, "rax"),
                                        imm = shamt
                                    );
                                }
                                0b010000 => {
                                    // SRAI
                                    let shamt = inst.imm & 0b111111;
                                    asm += &format!(
                                        r#"
                                        {load_rax_from_rs1}
                                        sar rax, {imm}
                                        {store_rax_into_rd}
                                    "#,
                                        load_rax_from_rs1 =
                                            load_reg!("rax", inst.rs1),
                                        store_rax_into_rd =
                                            store_reg!(inst.rd, "rax"),
                                        imm = shamt
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => unreachable!(),
                    }
                }

                0b0110011 => {
                    // We know it's an Rtype
                    let inst = Rtype::from(inst);

                    match (inst.funct7, inst.funct3) {
                        (0b0000000, 0b000) => {
                            // ADD
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                add rax, rsi
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0100000, 0b000) => {
                            // SUB
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                sub rax, rsi
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b001) => {
                            // SLL
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rcx_from_rs2}
                                shl rax, cl
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rcx_from_rs2 = load_reg!("rcx", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b010) => {
                            // SLT
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                xor  ecx, ecx
                                cmp  rax, rsi
                                setl cl
                                {store_rcx_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rcx_into_rd = store_reg!(inst.rd, "rcx")
                            );
                        }
                        (0b0000000, 0b011) => {
                            // SLTU
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                xor  ecx, ecx
                                cmp  rax, rsi
                                setb cl
                                {store_rcx_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rcx_into_rd = store_reg!(inst.rd, "rcx")
                            );
                        }
                        (0b0000000, 0b100) => {
                            // XOR
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                xor rax, rsi
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b101) => {
                            // SRL
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rcx_from_rs2}
                                shr rax, cl
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rcx_from_rs2 = load_reg!("rcx", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0100000, 0b101) => {
                            // SRA
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rcx_from_rs2}
                                sar rax, cl
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rcx_from_rs2 = load_reg!("rcx", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b110) => {
                            // OR
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                or rax, rsi
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b111) => {
                            // AND
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                and rax, rsi
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        _ => unreachable!(),
                    }
                }
                0b0111011 => {
                    // We know it's an Rtype
                    let inst = Rtype::from(inst);

                    match (inst.funct7, inst.funct3) {
                        (0b0000000, 0b000) => {
                            // ADDW
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                add eax, esi
                                movsx rax, eax
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0100000, 0b000) => {
                            // SUBW
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rsi_from_rs2}
                                sub eax, esi
                                movsx rax, eax
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rsi_from_rs2 = load_reg!("rsi", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b001) => {
                            // SLLW
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rcx_from_rs2}
                                shl eax, cl
                                movsx rax, eax
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rcx_from_rs2 = load_reg!("rcx", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0000000, 0b101) => {
                            // SRLW
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rcx_from_rs2}
                                shr eax, cl
                                movsx rax, eax
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rcx_from_rs2 = load_reg!("rcx", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        (0b0100000, 0b101) => {
                            // SRAW
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                {load_rcx_from_rs2}
                                sar eax, cl
                                movsx rax, eax
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                load_rcx_from_rs2 = load_reg!("rcx", inst.rs2),
                                store_rax_into_rd = store_reg!(inst.rd, "rax")
                            );
                        }
                        _ => unreachable!(),
                    }
                }
                0b0001111 => {
                    let inst = Itype::from(inst);

                    match inst.funct3 {
                        0b000 => {
                            // FENCE
                        }
                        _ => unreachable!(),
                    }
                }
                0b1110011 => {
                    if inst == 0b00000000000000000000000001110011 {
                        // ECALL
                        asm += &format!(
                            r#"
                            mov rax, 2
                            mov rsi, {pc}

                            ret
                        "#,
                            pc = pc,
                        );
                    } else if inst == 0b00000000000100000000000001110011 {
                        // EBREAK
                        asm += &format!(
                            r#"
                            mov rax, 3
                            mov rsi, {pc}

                            ret
                        "#,
                            pc = pc,
                        );
                    } else {
                        unreachable!();
                    }
                }
                0b0011011 => {
                    // We know it's an Itype
                    let inst = Itype::from(inst);

                    match inst.funct3 {
                        0b000 => {
                            // ADDIW
                            asm += &format!(
                                r#"
                                {load_rax_from_rs1}
                                add eax, {imm}
                                movsx rax, eax
                                {store_rax_into_rd}
                            "#,
                                load_rax_from_rs1 = load_reg!("rax", inst.rs1),
                                store_rax_into_rd = store_reg!(inst.rd, "rax"),
                                imm = inst.imm
                            );
                        }
                        0b001 => {
                            let mode = (inst.imm >> 5) & 0b1111111;

                            match mode {
                                0b0000000 => {
                                    // SLLIW
                                    let shamt = inst.imm & 0b11111;
                                    asm += &format!(
                                        r#"
                                        {load_rax_from_rs1}
                                        shl eax, {imm}
                                        movsx rax, eax
                                        {store_rax_into_rd}
                                    "#,
                                        load_rax_from_rs1 =
                                            load_reg!("rax", inst.rs1),
                                        store_rax_into_rd =
                                            store_reg!(inst.rd, "rax"),
                                        imm = shamt
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        0b101 => {
                            let mode = (inst.imm >> 5) & 0b1111111;

                            match mode {
                                0b0000000 => {
                                    // SRLIW
                                    let shamt = inst.imm & 0b11111;
                                    asm += &format!(
                                        r#"
                                        {load_rax_from_rs1}
                                        shr eax, {imm}
                                        movsx rax, eax
                                        {store_rax_into_rd}
                                    "#,
                                        load_rax_from_rs1 =
                                            load_reg!("rax", inst.rs1),
                                        store_rax_into_rd =
                                            store_reg!(inst.rd, "rax"),
                                        imm = shamt
                                    );
                                }
                                0b0100000 => {
                                    // SRAIW
                                    let shamt = inst.imm & 0b11111;
                                    asm += &format!(
                                        r#"
                                        {load_rax_from_rs1}
                                        sar eax, {imm}
                                        movsx rax, eax
                                        {store_rax_into_rd}
                                    "#,
                                        load_rax_from_rs1 =
                                            load_reg!("rax", inst.rs1),
                                        store_rax_into_rd =
                                            store_reg!(inst.rd, "rax"),
                                        imm = shamt
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        _ => unreachable!(),
                    }
                }

                _ => {
                    asm += &format!(
                        r#"
                        mov rax, 8
                        mov rsi, {pc}
                        red
                    "#,
                        pc = pc
                    );
                }
            }
            pc += 4;
        }
        Ok(asm)
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

    /// Tupl of `FileSz` and `MemSz` stored in program headers.
    pub struct Sizes(usize, usize);

    /// This macro builds a test case for a specific RISCV-64 UI binary.
    /// All the test cases have the same structure after being linked and so
    /// they share the same entrypoint 0x80000000 and file offsets of sections
    /// we care about 0x1000 and 0x2000 respectively.
    macro_rules! run_compliance_case {
        ($name: ident, $file_name: expr, $sec1: expr, $sec2: expr) => {
            #[test]
            fn $name() {
                let mut emu = Emulator::new();
                let filename = $file_name;
                let env_var = env::var("CARGO_MANIFEST_DIR").unwrap();
                let path = Path::new(&env_var).join(filename);
                let test_app_entry_point = 0x80000000;
                emu.set_mode(ExecMode::Debug);

                emu.memory
                    .load(
                        path,
                        &[
                            elf::Section {
                                file_offset: 0x0000000000001000,
                                virt_addr: mmu::VirtAddr(0x0000000080000000),
                                file_size: $sec1.0,
                                mem_size: $sec1.1,
                                permissions: mmu::Permission(
                                    PERM_READ | PERM_EXEC,
                                ),
                            },
                            elf::Section {
                                file_offset: 0x0000000000002000,
                                virt_addr: mmu::VirtAddr(0x0000000080001000),
                                file_size: $sec2.0,
                                mem_size: $sec2.1,
                                permissions: mmu::Permission(
                                    PERM_READ | PERM_WRITE,
                                ),
                            },
                        ],
                    )
                    .expect("Failed to read test binary");

                // Set program counter to our test app entry point.
                emu.set_reg(Register::Pc, test_app_entry_point);
                let exit_reason =
                    emu.run().expect_err("Failed to run emulator loop.");
                match exit_reason {
                    // Handle , for the compliance tests exit
                    // Compliance tests use an `exit` syscall with a status number `0`
                    // for pass, the calling convention specifies that for syscalls
                    // arguments go in `Register::A0` so to check if we pass a given
                    // test we read the `Register::A0` and check if it's 0 otherwise
                    // well the test failed.
                    // ref: https://riscv.org/wp-content/uploads/2015/01/riscv-calling.pdf
                    VmExit::Syscall => {
                        let syscall_num = emu.reg(Register::A7);
                        let exit_code = emu.reg(Register::A0);
                        // Ensure that the syscall on exit is `exit` or `exit_group`
                        // this is a sanity check for when we check the `exit_code`.
                        assert!((syscall_num == 93) || (syscall_num == 94));
                        assert_eq!(exit_code, 0);
                    }
                    _ => panic!("Unexpected exit reason : {:?}", exit_reason),
                }
            }
        };
    }
    // ADD
    run_compliance_case!(
        can_pass_compliance_test_rv64i_add,
        "support/compliance/rv64ui-p-add",
        Sizes(0x6bc, 0x6bc),
        Sizes(0x48, 0x48)
    );
    // ADDW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_addw,
        "support/compliance/rv64ui-p-addw",
        Sizes(0x6bc, 0x6bc),
        Sizes(0x48, 0x48)
    );
    // ADDI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_addi,
        "support/compliance/rv64ui-p-addi",
        Sizes(0x47c, 0x47c),
        Sizes(0x48, 0x48)
    );
    // ADDIW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_addiw,
        "support/compliance/rv64ui-p-addiw",
        Sizes(0x47c, 0x47c),
        Sizes(0x48, 0x48)
    );
    // AND
    run_compliance_case!(
        can_pass_compliance_test_rv64i_and,
        "support/compliance/rv64ui-p-and",
        Sizes(0x73c, 0x73c),
        Sizes(0x48, 0x48)
    );
    // ANDI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_andi,
        "support/compliance/rv64ui-p-andi",
        Sizes(0x3bc, 0x3bc),
        Sizes(0x48, 0x48)
    );
    // AUIPC
    run_compliance_case!(
        can_pass_compliance_test_rv64i_auipc,
        "support/compliance/rv64ui-p-auipc",
        Sizes(0x238, 0x238),
        Sizes(0x48, 0x48)
    );
    // BEQ
    run_compliance_case!(
        can_pass_compliance_test_rv64i_beq,
        "support/compliance/rv64ui-p-beq",
        Sizes(0x4bc, 0x4bc),
        Sizes(0x48, 0x48)
    );
    // BGE
    run_compliance_case!(
        can_pass_compliance_test_rv64i_bge,
        "support/compliance/rv64ui-p-bge",
        Sizes(0x4fc, 0x4fc),
        Sizes(0x48, 0x48)
    );
    // BGEU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_bgeu,
        "support/compliance/rv64ui-p-bgeu",
        Sizes(0x5bc, 0x5bc),
        Sizes(0x48, 0x48)
    );
    // BLT
    run_compliance_case!(
        can_pass_compliance_test_rv64i_blt,
        "support/compliance/rv64ui-p-blt",
        Sizes(0x4bc, 0x4bc),
        Sizes(0x48, 0x48)
    );
    // BLTU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_bltu,
        "support/compliance/rv64ui-p-bltu",
        Sizes(0x57c, 0x57c),
        Sizes(0x48, 0x48)
    );
    // BNE
    run_compliance_case!(
        can_pass_compliance_test_rv64i_bne,
        "support/compliance/rv64ui-p-bne",
        Sizes(0x4bc, 0x4bc),
        Sizes(0x48, 0x48)
    );
    // JAL
    run_compliance_case!(
        can_pass_compliance_test_rv64i_jal,
        "support/compliance/rv64ui-p-jal",
        Sizes(0x23c, 0x23c),
        Sizes(0x48, 0x48)
    );
    // JALR
    run_compliance_case!(
        can_pass_compliance_test_rv64i_jalr,
        "support/compliance/rv64ui-p-jalr",
        Sizes(0x2bc, 0x2bc),
        Sizes(0x48, 0x48)
    );
    // LB
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lb,
        "support/compliance/rv64ui-p-lb",
        Sizes(0x43c, 0x43c),
        Sizes(0x1010, 0x1010)
    );
    // LBU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lbu,
        "support/compliance/rv64ui-p-lbu",
        Sizes(0x43c, 0x43c),
        Sizes(0x1010, 0x1010)
    );
    // LD
    run_compliance_case!(
        can_pass_compliance_test_rv64i_ld,
        "support/compliance/rv64ui-p-ld",
        Sizes(0x67c, 0x67c),
        Sizes(0x1020, 0x1020)
    );
    // LH
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lh,
        "support/compliance/rv64ui-p-lh",
        Sizes(0x47c, 0x47c),
        Sizes(0x1010, 0x1010)
    );
    // LHU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lhu,
        "support/compliance/rv64ui-p-lhu",
        Sizes(0x47c, 0x47c),
        Sizes(0x1010, 0x1010)
    );
    // LUI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lui,
        "support/compliance/rv64ui-p-lui",
        Sizes(0x23c, 0x23c),
        Sizes(0x48, 0x48)
    );
    // LW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lw,
        "support/compliance/rv64ui-p-lw",
        Sizes(0x4bc, 0x4bc),
        Sizes(0x1010, 0x1010)
    );
    // LWU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_lwu,
        "support/compliance/rv64ui-p-lwu",
        Sizes(0x4fc, 0x4fc),
        Sizes(0x1010, 0x1010)
    );
    // OR
    run_compliance_case!(
        can_pass_compliance_test_rv64i_or,
        "support/compliance/rv64ui-p-or",
        Sizes(0x7bc, 0x7bc),
        Sizes(0x48, 0x48)
    );
    // ORI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_ori,
        "support/compliance/rv64ui-p-ori",
        Sizes(0x3bc, 0x3bc),
        Sizes(0x48, 0x48)
    );
    // SB
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sb,
        "support/compliance/rv64ui-p-sb",
        Sizes(0x63c, 0x63c),
        Sizes(0x1010, 0x1010)
    );
    // SD
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sd,
        "support/compliance/rv64ui-p-sd",
        Sizes(0x8bc, 0x8bc),
        Sizes(0x1050, 0x1050)
    );
    // SH
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sh,
        "support/compliance/rv64ui-p-sh",
        Sizes(0x6bc, 0x6bc),
        Sizes(0x1020, 0x1020)
    );
    // SW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sw,
        "support/compliance/rv64ui-p-sw",
        Sizes(0x6fc, 0x6fc),
        Sizes(0x1030, 0x1030)
    );
    // SLL
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sll,
        "support/compliance/rv64ui-p-sll",
        Sizes(0x7fc, 0x7fc),
        Sizes(0x48, 0x48)
    );
    // SLLI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_slli,
        "support/compliance/rv64ui-p-slli",
        Sizes(0x4bc, 0x4bc),
        Sizes(0x48, 0x48)
    );
    // SLLIW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_slliw,
        "support/compliance/rv64ui-p-slliw",
        Sizes(0x4fc, 0x4fc),
        Sizes(0x48, 0x48)
    );
    // SLLW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sllw,
        "support/compliance/rv64ui-p-sllw",
        Sizes(0x7fc, 0x7fc),
        Sizes(0x48, 0x48)
    );
    // SLT
    run_compliance_case!(
        can_pass_compliance_test_rv64i_slt,
        "support/compliance/rv64ui-p-slt",
        Sizes(0x6bc, 0x6bc),
        Sizes(0x48, 0x48)
    );
    // SLTI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_slti,
        "support/compliance/rv64ui-p-slti",
        Sizes(0x43c, 0x43c),
        Sizes(0x48, 0x48)
    );
    // SLTIU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sltiu,
        "support/compliance/rv64ui-p-sltiu",
        Sizes(0x43c, 0x43c),
        Sizes(0x48, 0x48)
    );
    // SLTU
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sltu,
        "support/compliance/rv64ui-p-sltu",
        Sizes(0x6fc, 0x6fc),
        Sizes(0x48, 0x48)
    );
    // SRA
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sra,
        "support/compliance/rv64ui-p-sra",
        Sizes(0x77c, 0x77c),
        Sizes(0x48, 0x48)
    );
    // SRAI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_srai,
        "support/compliance/rv64ui-p-srai",
        Sizes(0x4bc, 0x4bc),
        Sizes(0x48, 0x48)
    );
    // SRAIW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sraiw,
        "support/compliance/rv64ui-p-sraiw",
        Sizes(0x53c, 0x53c),
        Sizes(0x48, 0x48)
    );
    // SRAW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sraw,
        "support/compliance/rv64ui-p-sraw",
        Sizes(0x83c, 0x83c),
        Sizes(0x48, 0x48)
    );
    // SRL
    run_compliance_case!(
        can_pass_compliance_test_rv64i_srl,
        "support/compliance/rv64ui-p-srl",
        Sizes(0x7fc, 0x7fc),
        Sizes(0x48, 0x48)
    );
    // SRLI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_srli,
        "support/compliance/rv64ui-p-srli",
        Sizes(0x4fc, 0x4fc),
        Sizes(0x48, 0x48)
    );
    // SRLIW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_srliw,
        "support/compliance/rv64ui-p-srliw",
        Sizes(0x4fc, 0x4fc),
        Sizes(0x48, 0x48)
    );
    // SRLW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_srlw,
        "support/compliance/rv64ui-p-srlw",
        Sizes(0x7fc, 0x7fc),
        Sizes(0x48, 0x48)
    );
    // SUB
    run_compliance_case!(
        can_pass_compliance_test_rv64i_sub,
        "support/compliance/rv64ui-p-sub",
        Sizes(0x6bc, 0x6bc),
        Sizes(0x48, 0x48)
    );
    // SUBW
    run_compliance_case!(
        can_pass_compliance_test_rv64i_subw,
        "support/compliance/rv64ui-p-subw",
        Sizes(0x6bc, 0x6bc),
        Sizes(0x48, 0x48)
    );
    // XOR
    run_compliance_case!(
        can_pass_compliance_test_rv64i_xor,
        "support/compliance/rv64ui-p-xor",
        Sizes(0x7bc, 0x7bc),
        Sizes(0x48, 0x48)
    );
    // XORI
    run_compliance_case!(
        can_pass_compliance_test_rv64i_xori,
        "support/compliance/rv64ui-p-xori",
        Sizes(0x3bc, 0x3bc),
        Sizes(0x48, 0x48)
    );
}
