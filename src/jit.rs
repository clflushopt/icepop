/// Alloc RWX memory for jitted blocks, needs to be page aligned with proper
/// bits set.
#[cfg(all(target_family = "unix"))]
pub fn alloc_rwx(size: usize) -> &'static mut [u8] {
    extern "C" {
        fn mmap(
            addr: *mut u8,
            length: usize,
            prot: i32,
            flags: i32,
            fd: i32,
            offset: usize,
        ) -> *mut u8;
    }

    unsafe {
        let mem = mmap(0 as *mut u8, size, 7, 34, -1, 0);
        assert!(!mem.is_null());
        std::slice::from_raw_parts_mut(mem, size)
    }
}
