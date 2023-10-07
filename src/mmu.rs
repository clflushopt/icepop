//! Software based memory management for Icepop.
//!
//! This is a translation-less software MMU that works with our local toolchain
//! to change the code to support address translation you will need to change
//! all `read` and `write` implementations to translate addresses.
//!
/// Address translation in soft MMU :
///
/// To do address translation on larger address ranges for example 0x8000_0000
/// we can mark 0x8000_0000 as the base address and use relative addressing
/// to translate all memory addresses, for example a load @ 0x8000_abcd in an
/// MMU with a max addressable memory at 0x2000000 will be equivalent to :
///
/// new_address = base - addr
/// new_address = 0x8000_0000 - 0x8000_abcd = 0xabcd
///
/// Which fits within our MMU's range.
///
/// Since the Toolchain we have builds all binaries with a base address or
/// entry point of 0x10000 then we don't need to do the translation.
use crate::elf;
use std::path::Path;

/// Default MMU size when used in emulator.
pub const DEFAULT_EMU_MMU_SIZE: usize = 32 * 1024 * 1024;


/// Permission bytes are assigned to single bytes and define the permissions
/// on a that byte.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Permission(pub u8);

/// Permission bits that can be set on allocated memory, we have READ, WRITE
/// and EXEC permissions and READ-AFTER-WRITE which can be used to track
/// reading uninitialized memory.
pub const PERM_READ: u8 = 1 << 0;
pub const PERM_WRITE: u8 = 1 << 1;
pub const PERM_EXEC: u8 = 1 << 2;
pub const PERM_RAW: u8 = 1 << 3;

/// Unit number of bytes that are cleared and reset on each run.
const DIRTY_BLOCK_SIZE: usize = 4096;

/// Strongly typed reference to guest virtual addresses.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirtAddr(pub usize);

/// Mmu is used to represent a soft isolated memory space.
#[derive(Debug)]
pub struct Mmu {
    /// Block of memory associated with this address space where the zeroth
    /// address corresponds to the zeroth address in the guest address space.
    memory: Vec<u8>,

    /// Permission bytes associated with the entire memory block.
    permissions: Vec<Permission>,

    /// Used to keep track of blocks indices in `memory` which are considered
    /// dirty i.e have been written to.
    dirty: Vec<usize>,

    /// Tracks which regions in memory have been dirtied.
    dirty_bitmap: Vec<u64>,

    /// Base address of the next allocation.
    base_addr: VirtAddr,
}

impl Mmu {
    /// Creates a new memory space with `size` bytes.
    pub fn new(size: usize) -> Self {
        Self {
            memory: vec![0; size],
            permissions: vec![Permission(0); size],
            dirty: Vec::with_capacity(size / DIRTY_BLOCK_SIZE + 1),
            dirty_bitmap: vec![0u64; size / DIRTY_BLOCK_SIZE / 64 + 1],
            base_addr: VirtAddr(0x10000),
        }
    }

    /// Creates a copy of the MMU state.
    pub fn fork(&self) -> Self {
        let size = self.memory.len();

        Self {
            memory: self.memory.clone(),
            permissions: self.permissions.clone(),
            dirty: Vec::with_capacity(size / DIRTY_BLOCK_SIZE + 1),
            dirty_bitmap: vec![0u64; size / DIRTY_BLOCK_SIZE / 64 + 1],
            base_addr: self.base_addr,
        }
    }

    /// Restores MMU state to its original state.
    pub fn reset(&mut self, other: &Mmu) {
        for &block in &self.dirty {
            let start = block * DIRTY_BLOCK_SIZE;
            let end = (block + 1) * DIRTY_BLOCK_SIZE;
            // Zero out the bitmap.
            self.dirty_bitmap[block / 64] = 0;

            // Reset memory state.
            self.memory[start..end].copy_from_slice(&other.memory[start..end]);

            // Restore permissions.
            self.permissions[start..end]
                .copy_from_slice(&other.permissions[start..end]);
         :
        // Clear the dirty blocks list.
        self.dirty.clear()
    }

    /// Allocate a region in memory as read-writable.
    pub fn alloc(&mut self, size: usize) -> Option<VirtAddr> {
        // Align `size` to nearest 16 bytes.
        let aligned_size = (size + 0xf) & !0xf;
        // Get the current base address.
        let base = self.base_addr;

        // If we've reached the allocatable bound return None.
        if base.0 >= self.memory.len() {
            return None;
        }

        // Update base address
        self.base_addr = VirtAddr(self.base_addr.0.checked_add(aligned_size)?);

        // Bound check the allocation space.
        if self.base_addr.0 > self.memory.len() {
            return None;
        }

        self.set_permissions(base, size, Permission(PERM_RAW | PERM_WRITE));

        Some(base)
    }

    /// Set permissions to the memory region starting at `addr` and is `size`
    /// bytes long.
    pub fn set_permissions(
        &mut self,
        addr: VirtAddr,
        size: usize,
        perm: Permission,
    ) -> Option<()> {
        self.permissions
            .get_mut(addr.0..addr.0.checked_add(size)?)?
            .iter_mut()
            .for_each(|x| *x = perm);
        Some(())
    }

    /// Write the bytes from `buf` into `memory` at given `addr`.
    pub fn write(&mut self, addr: VirtAddr, buf: &[u8]) -> Option<()> {
        let perms = self
            .permissions
            .get_mut(addr.0..addr.0.checked_add(buf.len())?)?;
        // Check that the entire memory region [addr..addr+buf.len()]
        // is writable.
        let mut has_raw = false;
        if !perms.iter().all(|x| {
            has_raw |= (x.0 & PERM_RAW) != 0;
            (x.0 & PERM_WRITE) != 0
        }) {
            return None;
        }

        self.memory
            .get_mut(addr.0..addr.0.checked_add(buf.len())?)?
            .copy_from_slice(buf);

        // Compute dirty bit blocks.
        let block_start = addr.0 / DIRTY_BLOCK_SIZE;
        let block_end = (addr.0 + buf.len()) / DIRTY_BLOCK_SIZE;

        for block in block_start..=block_end {
            // Determine the bitmap position of the dirty block.
            let idx = block_start / 64;
            let bit = block_start % 64;

            if self.dirty_bitmap[idx] & (1 << bit) == 0 {
                // Block is not dirty, mark it as dirty.
                self.dirty.push(block);
                // Update the dirty bitmap.
                self.dirty_bitmap[idx] |= 1 << bit;
            }
        }

        // Update RAW bits.
        if has_raw {
            perms.iter_mut().for_each(|x| {
                if (x.0 & PERM_RAW) != 0 {
                    *x = Permission(x.0 | PERM_READ);
                }
            });
        }
        Some(())
    }

    /// Read `buf.len()` bytes from `memory` at `addr` into `buf`.
    pub fn read(&self, addr: VirtAddr, buf: &mut [u8]) -> Option<()> {
        self.read_into_perms(addr, buf, Permission(PERM_READ))
    }

    /// Read a type `T` at `addr` expecting the region `[addr..addr+sizeof(T)]`
    /// to have the expected permissions.
    ///
    /// # Safety
    ///
    /// The largest sized type fits within the 16 bytes we allocate in `buf`
    /// so the read will always be bounded.
    pub fn read_into<T: Sized>(
        &mut self,
        addr: VirtAddr,
        expected_permissions: Permission,
    ) -> Option<T> {
        // We will read at most an 8 byte chunk.
        let mut buf = [0u8; 16];
        self.read_into_perms(
            addr,
            &mut buf[..core::mem::size_of::<T>()],
            expected_permissions,
        )?;
        Some(unsafe { core::ptr::read_unaligned(buf.as_ptr() as *const T) })
    }

    /// Write a type `T` to `addr`.
    ///
    /// # Safety
    ///
    /// The `Sized` bound ensures that pointer has the size we are trying
    /// to read.
    pub fn write_into<T: Sized>(
        &mut self,
        addr: VirtAddr,
        value: T,
    ) -> Option<()> {
        let buf = unsafe {
            core::slice::from_raw_parts(
                &value as *const T as *const u8,
                core::mem::size_of::<T>(),
            )
        };

        self.write(addr, buf)
    }

    /// Read `buf.len()` bytes from `memory` at `addr` into `buf`.
    pub fn read_into_perms(
        &self,
        addr: VirtAddr,
        buf: &mut [u8],
        expected_permissions: Permission,
    ) -> Option<()> {
        // Fetch permission bits of the memory region we are trying
        // to read from.
        let perms = self
            .permissions
            .get(addr.0..addr.0.checked_add(buf.len()).unwrap())
            .unwrap();

        let mut has_raw = false;
        // Check memory region has READ bit set.
        if expected_permissions.0 != 0
            && !perms.iter().all(|x| {
                (x.0 & expected_permissions.0) == expected_permissions.0
            })
        {
            return None;
        }

        buf.copy_from_slice(
            self.memory
                .get(addr.0..addr.0.checked_add(buf.len()).unwrap())
                .unwrap(),
        );
        Some(())
    }

    /// Load an ELF binary from disk.
    pub fn load<P: AsRef<Path>>(
        &mut self,
        filename: P,
        sections: &[elf::Section],
    ) -> Option<()> {
        // Read the file into memory.
        let contents = std::fs::read(filename).ok()?;

        // Iterate over sections and load them from their offsets in the binary.
        for section in sections {
            // Set memory to writable.
            self.set_permissions(
                section.virt_addr,
                section.mem_size,
                Permission(PERM_WRITE),
            )?;

            // Write the binary to memory.
            self.write(
                section.virt_addr,
                contents.get(
                    section.file_offset
                        ..section.file_offset.checked_add(section.file_size)?,
                )?,
            )?;

            // Fill any padding with zeroes.
            if section.mem_size > section.file_size {
                let padding = vec![0u8; section.mem_size - section.file_size];
                self.write(
                    VirtAddr(
                        section.virt_addr.0.checked_add(section.file_size)?,
                    ),
                    &padding,
                )?;
            }

            self.set_permissions(
                section.virt_addr,
                section.mem_size,
                section.permissions,
            )?;

            self.base_addr = VirtAddr(std::cmp::max(
                self.base_addr.0,
                (section.virt_addr.0 + section.mem_size + 0xf) & !0xf,
            ));
        }

        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    #[test]
    fn can_allocate_when_in_range() {
        let mut mmu = Mmu::new(1024 * 1024);
        assert_eq!(mmu.alloc(250), Some(VirtAddr(0x10000)));
    }

    #[test]
    fn fails_when_oom() {
        let mut mmu = Mmu::new(1024);
        assert_eq!(mmu.alloc(4096), None);
    }

    #[test]
    fn can_read_write_within_bounds() {
        let mut mmu = Mmu::new(1024 * 1024);
        let write_base_addr = mmu.alloc(4096).unwrap();
        mmu.write(write_base_addr, b"Hello this is a write")
            .unwrap();
        let mut buf = [0u8; 21];
        mmu.read(write_base_addr, &mut buf).unwrap();
        // Check it contains 'H'
        assert!(buf.contains(&0x48));
    }

    #[test]
    fn fails_on_out_of_bounds_raw() {
        let mut mmu = Mmu::new(1024 * 1024);
        let write_base_addr = mmu.alloc(4096).unwrap();
        mmu.write(write_base_addr, b"Hello this is a write")
            .unwrap();
        // Only 21 bytes have been written, trying to read out of bounds
        // on the 11 bytes that aren't marked RAW will fail.
        let mut buf = [0u8; 32];
        assert!(mmu.read(write_base_addr, &mut buf).is_none());
    }

    #[test]
    fn can_track_dirty_bits() {
        let mut mmu = Mmu::new(1024 * 1024);
        let write_base_addr = mmu.alloc(4096).unwrap();
        mmu.write(write_base_addr, b"cafe").unwrap();
        mmu.write(write_base_addr, b"cafe").unwrap();
        let mut buf = [0u8; 4];
        assert!(mmu.read(write_base_addr, &mut buf).is_some());
        // 0x10000 / 0x1000 = 0x10
        assert_eq!(mmu.dirty[0], 0x10);
    }

    #[test]
    fn can_fork_and_reset_state() {
        let mut mmu = Mmu::new(1024 * 1024);
        let write_base_addr = mmu.alloc(4).unwrap();
        mmu.write(write_base_addr, b"BBBB").unwrap();

        {
            let mut forked = mmu.fork();

            forked.write(write_base_addr, b"AAAA").unwrap();
            let mut buf = [0u8; 4];
            forked.read(write_base_addr, &mut buf).unwrap();
            // After write.
            assert_eq!(&buf.as_slice(), b"AAAA");

            // Reset
            forked.reset(&mmu);

            let mut buf = [0u8; 4];
            forked.read(write_base_addr, &mut buf).unwrap();
            // After reset, back to its original state.
            assert_eq!(&buf.as_slice(), &b"BBBB");
        }
    }

    #[test]
    fn respects_permissions_when_forking() {
        let mut mmu = Mmu::new(1024 * 1024);
        let write_base_addr = mmu.alloc(4).unwrap();
        {
            let mut forked = mmu.fork();

            forked.write(write_base_addr, b"AAAA").unwrap();
            let mut buf = [0u8; 4];
            forked.read(write_base_addr, &mut buf).unwrap();
            // After write.
            assert_eq!(&buf.as_slice(), b"AAAA");

            // Reset
            forked.reset(&mmu);
            // Permissions are reset the read will fail.
            let mut buf = [0u8; 4];
            assert!(forked.read(write_base_addr, &mut buf).is_none());
        }
    }

    #[test]
    #[ignore = "this test is environment specific and depends on built binary"]
    fn can_load_elf_binaries() {
        use crate::elf;

        let env_var = env::var("CARGO_MANIFEST_DIR").unwrap();
        let path = Path::new(&env_var).join("support/unit/test_app");

        let mut mmu = Mmu::new(32 * 1024 * 1024);
        mmu.load(
            path,
            &[
                elf::Section {
                    file_offset: 0x0000000000000000,
                    virt_addr: VirtAddr(0x0000000000010000),
                    file_size: 0x0000000000000190,
                    mem_size: 0x0000000000000190,
                    permissions: Permission(PERM_READ),
                },
                elf::Section {
                    file_offset: 0x0000000000000190,
                    virt_addr: VirtAddr(0x0000000000011190),
                    file_size: 0x0000000000002598,
                    mem_size: 0x0000000000002598,
                    permissions: Permission(PERM_EXEC),
                },
                elf::Section {
                    file_offset: 0x0000000000002728,
                    virt_addr: VirtAddr(0x0000000000014728),
                    file_size: 0x00000000000000f8,
                    mem_size: 0x0000000000000750,
                    permissions: Permission(PERM_READ | PERM_WRITE),
                },
            ],
        );
        let mut buf = [0u8; 4];
        mmu.read_into_perms(VirtAddr(0x11190), &mut buf, Permission(0))
            .unwrap();
        assert_eq!(buf.as_slice(), vec![0x97, 0x41, 0x0, 0x0]);
    }
}
