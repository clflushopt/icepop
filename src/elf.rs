//! Micro ELF reader.
use crate::mmu::{Permission, VirtAddr};

/// Section information for ELF file format.
pub struct Section {
    pub file_offset: usize,
    pub virt_addr: VirtAddr,
    pub file_size: usize,
    pub mem_size: usize,
    pub permissions: Permission,
}
