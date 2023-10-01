//! Software based memory management for Icepop.

/// Permission bytes are assigned to single bytes and define the permissions
/// on a that byte.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Permission(pub u8);

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
}
