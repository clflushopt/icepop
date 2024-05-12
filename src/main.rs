use std::sync::{Arc, Mutex};

use icepop::emu::{Emulator, ExecMode, VmExit};
#[cfg(target_os = "linux")]
use icepop::jit::JitCache;
use icepop::machine::Register;
use icepop::mmu;

fn main() {
    use icepop::elf;
    use std::env;
    use std::path::Path;

    let mut vm = Emulator::new();
    // Prepare the VM environment.
    vm.prepare();
    // Set execution mode to JIT.
    vm.set_mode(ExecMode::Jit);

    let env_var = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path = Path::new(&env_var).join("support/unit/test_app");
    let test_app_entry_point = 0x11190;
    // Load test_app target binary.
    vm.memory
        .load(
            path,
            &[
                elf::Section {
                    file_offset: 0x0000000000000000,
                    virt_addr: mmu::VirtAddr(0x0000000000010000),
                    file_size: 0x0000000000000190,
                    mem_size: 0x0000000000000190,
                    permissions: mmu::Permission(mmu::PERM_READ),
                },
                elf::Section {
                    file_offset: 0x0000000000000190,
                    virt_addr: mmu::VirtAddr(0x0000000000011190),
                    file_size: 0x000000000000255c,
                    mem_size: 0x000000000000255c,
                    permissions: mmu::Permission(
                        mmu::PERM_READ | mmu::PERM_EXEC,
                    ),
                },
                elf::Section {
                    file_offset: 0x00000000000026f0,
                    virt_addr: mmu::VirtAddr(0x00000000000146f0),
                    file_size: 0x00000000000000f8,
                    mem_size: 0x0000000000000750,
                    permissions: mmu::Permission(
                        mmu::PERM_READ | mmu::PERM_WRITE,
                    ),
                },
            ],
        )
        .expect("Failed to read test binary");
    // Set program counter to our test app entry point.
    vm.set_reg(Register::Pc, test_app_entry_point);

    // Fork a single worker.
    let mut runer = vm.memory.fork();
    use std::time::Instant;
    let start = Instant::now();

    // VM run loop.
    let exit_reason = loop {
        let exit_reason = vm.run().expect_err("Failed to run emulator loop.");
        match exit_reason {
            // Handle syscalls, by convention syscall number is stored in
            // `Register::A7`, and arguments in registers `Register::A0` to
            // `Register::A5` with the unused arguments set to `0`.
            //
            // The return value is stored in `Register::A0`.
            VmExit::Syscall => {
                let stop = Instant::now();
                let num = vm.reg(Register::A7);
                if let Err(exit_reason) = vm.handle_syscall(num) {
                    break exit_reason;
                }
                let pc = vm.reg(Register::Pc);
                vm.set_reg(Register::Pc, pc.wrapping_add(4));
                println!(
                    "VM Exited with code: {:?} took {} seconds",
                    exit_reason,
                    (stop - start).as_secs(),
                );
            }
            // Exit the Vm if `exit_reason` is anythign other than `VmExit::Syscall`.
            _ => {
                println!("VM Exited with code: {:?}", exit_reason);
                break exit_reason;
            }
        }
    };
}
