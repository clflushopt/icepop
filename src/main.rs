use icepop::mmu;

fn main() {
    let mut mmu = mmu::Mmu::new(1024 * 1024);
    let write_base_addr = mmu.alloc(16).unwrap();
    mmu.write(write_base_addr, b"AAAAAAAAA").unwrap();
    {
        let mut forked = mmu.fork();

        for ii in 0..10_000_000 {
            mmu.write(write_base_addr, b"BBBBBBBB").unwrap();
            forked.reset(&mmu);
        }
    }

    println!("Hello, world!");
}
