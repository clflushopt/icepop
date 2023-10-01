//! Software based memory management for Icepop.

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

    /// Base address of the next allocation.
    base_addr: VirtAddr,
}

impl Mmu {
    /// Creates a new memory space with `size` bytes.
    pub fn new(size: usize) -> Self {
        Self {
            memory: vec![0; size],
            permissions: vec![Permission(0); size],
            base_addr: VirtAddr(0x10000),
        }
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
        // Fetch permission bits of the memory region we are trying
        // to read from.
        let perms = self
            .permissions
            .get(addr.0..addr.0.checked_add(buf.len())?)?;

        let mut has_raw = false;
        // Check memory region has READ bit set.
        if !perms.iter().all(|x| (x.0 & PERM_READ) != 0) {
            return None;
        }

        buf.copy_from_slice(
            self.memory.get(addr.0..addr.0.checked_add(buf.len())?)?,
        );
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let mut bytes = [0u8; 21];
        mmu.read(write_base_addr, &mut bytes).unwrap();
        // Check it contains 'H'
        assert!(bytes.contains(&0x48));
    }

    #[test]
    fn fails_on_out_of_bounds_raw() {
        let mut mmu = Mmu::new(1024 * 1024);
        let write_base_addr = mmu.alloc(4096).unwrap();
        mmu.write(write_base_addr, b"Hello this is a write")
            .unwrap();
        // Only 21 bytes have been written, trying to read out of bounds
        // on the 11 bytes that aren't marked RAW will fail.
        let mut bytes = [0u8; 32];
        assert!(mmu.read(write_base_addr, &mut bytes).is_none());
    }
}
