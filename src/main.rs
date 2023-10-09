use icepop::emu::{Emulator, ExecMode, VmExit};
use icepop::machine::Register;
use icepop::mmu;

fn main() {
    use icepop::elf;
    use std::env;
    use std::path::Path;

    let mut emu = Emulator::new();
    emu.prepare();

    let env_var = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path = Path::new(&env_var).join("support/unit/test_app");
    let test_app_entry_point = 0x11190;

    emu.memory
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
    emu.set_reg(Register::Pc, test_app_entry_point);

    // Disable debug logs.
    emu.set_mode(ExecMode::Reset);
    // VM run loop.
    let vmexit = loop {
        let vmexit = emu.run().expect("Failed to run emulator loop.");
        match vmexit {
            VmExit::Syscall => {
                let num = emu.reg(Register::A7);
                if let Err(vmexit) = emu.handle_syscall(num) {
                    break vmexit;
                }
                let pc = emu.reg(Register::Pc);
                emu.set_reg(Register::Pc, pc.wrapping_add(4));
            }
            _ => break vmexit,
        }
    };
    println!("VM exited with {:#x?}", vmexit);
}
