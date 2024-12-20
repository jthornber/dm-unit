use log::*;
use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryInto;
use std::fmt;
use std::result;
use thiserror::Error;

use crate::primitive::Primitive;

//-------------------------------------

/// An address used within the guest.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Addr(pub u64);

impl fmt::Debug for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:x}", self.0)
    }
}

impl fmt::LowerHex for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.0;
        fmt::LowerHex::fmt(&val, f)
    }
}

impl Addr {
    /// Returns true if the address is null.
    pub fn is_null(&self) -> bool {
        self.0 == 0
    }
}

//-------------------------------------

/// Indicates memory errors such as referencing unallocated memory.  Or bad permissions.
#[derive(Error, Clone, Copy, Debug)]
pub enum MemErr {
    #[error("Memory is not mapped at {0:?}, looking for perms {1:?}")]
    UnmappedRegion(Addr, u8),

    #[error("Bad memory permissions at {0:?}, wanted {1}")]
    BadPerms(Addr, u8),

    #[error("Address out of bounds")]
    OutOfBounds,

    #[error("Unable to allocate enough space")]
    OutOfSpace,

    #[error("Bad free requested {0:?}")]
    BadFree(Addr),
}

pub type Result<T> = result::Result<T, MemErr>;

//-------------------------------------

// FIXME: use an enum, or bitset or something
pub const PERM_READ: u8 = 1 << 0;
pub const PERM_WRITE: u8 = 1 << 1;
pub const PERM_EXEC: u8 = 1 << 2;

/// Memory for a region of the address space.
#[derive(Clone, Debug)]
struct MMap {
    perms: u8,
    begin: u64,
    end: u64,
    bytes: Vec<u8>,
}

impl MMap {
    fn new(begin: u64, bytes: Vec<u8>, perms: u8) -> Self {
        let end = begin + bytes.len() as u64;
        MMap {
            perms,
            begin,
            end,
            bytes,
        }
    }

    /// Checks all 'perms' are present for this region.
    fn check_perms(&self, begin: u64, perms: u8) -> Result<()> {
        if (self.perms & perms) != perms {
            debug!("bad perms: mm.perms = {}, perms = {}", self.perms, perms);
            return Err(MemErr::BadPerms(Addr(begin), perms));
        }

        Ok(())
    }

    /// Changes the permissions of a mapped region.
    fn change_perms(&mut self, begin: u64, end: u64, mut perms: u8) -> Result<u8> {
        if (begin != self.begin) || (end - begin != self.bytes.len() as u64) {
            return Err(MemErr::OutOfBounds);
        }

        std::mem::swap(&mut perms, &mut self.perms);
        Ok(perms)
    }

    /// Reads data from the region.  Fails if all the data can't be read
    /// from this region, or if any of the perms are not present.
    fn read(&self, begin: u64, bytes: &mut [u8], perms: u8) -> Result<()> {
        let end = begin + (bytes.len() as u64);
        assert!(begin >= self.begin);
        assert!(end <= self.end);

        self.check_perms(begin, perms)?;

        let slice = &self.bytes[((begin - self.begin) as usize)..((end - self.begin) as usize)];
        bytes.copy_from_slice(slice);

        Ok(())
    }

    /// Writes data to the region.  Fails if all the data can't be
    /// written to this region, or if any of the perms are not pesent.
    fn write(&mut self, begin: u64, bytes: &[u8], perms: u8) -> Result<()> {
        let end = begin + (bytes.len() as u64);
        assert!(begin >= self.begin);
        assert!(end <= self.end);

        self.check_perms(begin, perms)?;

        let slice = &mut self.bytes[((begin - self.begin) as usize)..((end - self.begin) as usize)];
        slice.copy_from_slice(bytes);

        Ok(())
    }

    fn zero(&mut self, begin: u64, end: u64, perms: u8) -> Result<()> {
        assert!(begin >= self.begin);
        assert!(end <= self.end);

        self.check_perms(begin, perms)?;

        let slice = &mut self.bytes[((begin - self.begin) as usize)..((end - self.begin) as usize)];
        unsafe {
            std::ptr::write_bytes(slice.as_ptr() as *mut u8, 0, (end - begin) as usize);
        }
        Ok(())
    }

    /// Trashes any data in the region, and clear the written bits.
    fn forget(&mut self, begin: u64, end: u64) {
        let begin = begin - self.begin;
        let end = end - self.begin;
        for b in begin..end {
            if (b & 1) != 0 {
                self.bytes[b as usize] = 0xde;
            } else {
                self.bytes[b as usize] = 0xad;
            }
        }
    }

    // Checks if the MMap contains the given address.
    fn contains(&self, addr: u64) -> bool {
        addr >= self.begin && addr < self.end
    }
}

//-------------------------------------

// Uniform Layer struct
#[derive(Clone, Debug)]
struct Layer {
    // Range covered by this layer.
    begin: u64,
    end: u64,

    // Mappings that are either:
    // - Cross-boundary mappings stored at this level
    // - Mappings in leaf nodes
    mappings: Vec<MMap>,

    // Optional children layers for further subdivision.
    children: Option<Box<[Layer; 256]>>,
}

impl Layer {
    // Create a new layer covering the given range.
    fn new(begin: u64, end: u64) -> Self {
        Layer {
            begin,
            end,
            mappings: Vec::new(),
            children: None,
        }
    }

    // Calculate the size of the layer's range.
    fn size(&self) -> u64 {
        self.end - self.begin
    }

    // Inserts an MMap into the trie.
    fn insert(&mut self, mmap: MMap) {
        // If this layer cannot be subdivided further (e.g., minimum size), store the mapping here.
        if self.size() <= 256 {
            self.mappings.push(mmap);
            return;
        }

        // Determine if the MMap fits entirely within one child layer.
        let child_size = self.size() / 256;
        let first_child_index = ((mmap.begin - self.begin) / child_size) as usize;
        let last_child_index = ((mmap.end - 1 - self.begin) / child_size) as usize;

        if first_child_index == last_child_index {
            // The MMap fits entirely within one child layer.
            // Ensure children exist.
            if self.children.is_none() {
                self.create_children();
            }
            // Insert into the appropriate child.
            let child = &mut self.children.as_mut().unwrap()[first_child_index];
            child.insert(mmap);
        } else {
            // The MMap crosses child boundaries; store at this level.
            self.mappings.push(mmap);
        }
    }

    // Looks up an MMap containing the given address.
    fn lookup(&self, addr: u64) -> Option<&MMap> {
        // Check if the address is within any of the mappings at this layer.
        for mm in &self.mappings {
            if mm.contains(addr) {
                return Some(mm);
            }
        }

        // If not, and if children exist, descend into the appropriate child.
        if let Some(children) = &self.children {
            let child_index = self.child_index(addr);
            return children[child_index].lookup(addr);
        }

        // Not found.
        None
    }

    // Similar to lookup, but returns a mutable reference.
    fn lookup_mut(&mut self, addr: u64) -> Option<&mut MMap> {
        // Compute necessary values before mutable borrow begins
        let begin = self.begin;
        let size = self.size();

        for mm in &mut self.mappings {
            if mm.contains(addr) {
                return Some(mm);
            }
        }

        if let Some(children) = &mut self.children {
            // Use the previously computed values to calculate child_index
            let child_size = size / 256;
            let child_index = ((addr - begin) / child_size) as usize;
            return children[child_index].lookup_mut(addr);
        }

        None
    }

    // Removes an MMap starting at the given address.
    fn remove(&mut self, addr: u64) -> Option<MMap> {
        // First, try to remove from mappings at this layer.
        if let Some(pos) = self.mappings.iter().position(|mm| mm.begin == addr) {
            // Found it in this layer's mappings; remove and return it.
            return Some(self.mappings.swap_remove(pos));
        }

        // Precompute child_index if children exist.
        if self.children.is_some() {
            let child_index = self.child_index(addr);

            // Now, we can mutably borrow self.children safely.
            if let Some(children) = &mut self.children {
                // Attempt to remove from the appropriate child.
                return children[child_index].remove(addr);
            }
        }

        // If no mappings or children are found, return None.
        None
    }

    // Helper functions...

    // Creates child layers.
    fn create_children(&mut self) {
        let child_size = self.size() / 256;
        let mut children = Vec::with_capacity(256);

        for i in 0..256 {
            let child_begin = self.begin + child_size * i as u64;
            let child_end = child_begin + child_size;
            children.push(Layer::new(child_begin, child_end));
        }

        self.children = Some(children.into_boxed_slice().try_into().unwrap());
    }

    // Determines the index of the child that contains the given address.
    fn child_index(&self, addr: u64) -> usize {
        let child_size = self.size() / 256;
        ((addr - self.begin) / child_size) as usize
    }
}

#[derive(Clone)]
struct Trie {
    root: Layer,
}

impl Trie {
    fn new() -> Self {
        Trie {
            root: Layer::new(0, 1 << 32),
        }
    }

    fn out_of_bounds(addr: u64) -> bool {
        addr >= (1 << 32)
    }

    fn insert(&mut self, mmap: MMap) {
        if Trie::out_of_bounds(mmap.begin) {
            panic!("MMU only supports a 32bit address space");
        }
        self.root.insert(mmap);
    }

    fn lookup(&self, addr: u64) -> Option<&MMap> {
        if Trie::out_of_bounds(addr) {
            None
        } else {
            self.root.lookup(addr)
        }
    }

    fn lookup_mut(&mut self, addr: u64) -> Option<&mut MMap> {
        if Trie::out_of_bounds(addr) {
            None
        } else {
            self.root.lookup_mut(addr)
        }
    }

    fn remove(&mut self, addr: u64) -> Option<MMap> {
        if Trie::out_of_bounds(addr) {
            panic!("MMU only supports a 32bit address space");
        }
        self.root.remove(addr)
    }
}

//-------------------------------------

#[derive(Clone, Debug)]
pub struct MEntry {
    pub heap_ptr: u64,
    pub len: usize,

    // Riscv program counter that made the call.  Optional because
    // a lot of memory gets allocated by stubs.
    pub pc: Option<u64>,
}

impl MEntry {
    fn new(heap_ptr: u64, len: usize) -> Self {
        Self {
            heap_ptr,
            len,
            pc: None,
        }
    }

    fn new_with_pc(heap_ptr: u64, len: usize, pc: u64) -> Self {
        Self {
            heap_ptr,
            len,
            pc: Some(pc),
        }
    }
}

/// Manages memory for the vm.  Tracks permissions at the byte level.
/// Checks memory has been initialised before it's read.
pub struct Memory {
    mmaps: Trie,

    // We always want a heap, so I'm embedding it in the mmu.
    heap: Heap,

    // Maps the ptr returned by alloc_bytes() back to the heap ptr and len.
    allocations: BTreeMap<u64, MEntry>,
}

impl Memory {
    pub fn new(heap_begin: Addr, heap_end: Addr) -> Self {
        Memory {
            mmaps: Trie::new(),
            heap: Heap::new(heap_begin, heap_end),
            allocations: BTreeMap::new(),
        }
    }

    pub fn snapshot(&self) -> Self {
        Memory {
            mmaps: self.mmaps.clone(),
            heap: self.heap.clone(),
            allocations: self.allocations.clone(),
        }
    }

    pub fn new_allocations(&self, newer_memory: &Self) -> Vec<MEntry> {
        let mut result = Vec::new();
        for (addr, me) in &newer_memory.allocations {
            if !self.allocations.contains_key(addr) {
                result.push(me.clone());
            }
        }

        result
    }

    /*
    // Checks there are no mappings in a particular range
    fn no_mappings(&self, begin: u64, end: u64) -> bool {
        let mut cur = self.mmaps.upper_bound(Bound::Included(&begin));

        loop {
            if cur.is_null() {
                break;
            }

            let mm = cur.get().unwrap().mmap.borrow();
            if mm.begin >= end {
                break;
            }

            if mm.end > begin && (mm.begin >= begin || mm.end < end) {
                debug!(
                    "mapping clash: mm.begin = {:x}, mm.end = {:x}",
                    mm.begin, mm.end
                );
                return false;
            }

            cur.move_next();
        }

        true
    }
    */

    fn insert_mm(&mut self, mm: MMap) {
        self.mmaps.insert(mm);
    }

    /// Remove an mmapped area.
    pub fn unmap(&mut self, begin: Addr) -> Result<Vec<u8>> {
        let mm = self.mmaps.remove(begin.0);

        if let Some(mut mm) = mm {
            let mut bytes = Vec::new();

            std::mem::swap(&mut mm.bytes, &mut bytes);
            Ok(bytes)
        } else {
            Err(MemErr::BadFree(begin))
        }
    }

    /// Creates a new mapped region of memory with the specified perms.  The
    /// data will be uninitialised.
    pub fn mmap(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        // FIXME: not sure how to create an uninitialised vec
        self.mmap_zeroes(begin, end, perms)
    }

    /// Like mmap, but it intialises the data with zeroes and sets the written bits.
    pub fn mmap_zeroes(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        assert!(begin.0 <= end.0);
        let mm = MMap::new(begin.0, vec![0u8; (end.0 - begin.0) as usize], perms);
        self.insert_mm(mm);
        Ok(())
    }

    /// Creates a new mapping with the given permissions and takes ownership
    /// it with the given data.  This is an efficient way to pass data from
    /// the host to the guest.
    pub fn mmap_bytes(&mut self, begin: Addr, bytes: Vec<u8>, perms: u8) -> Result<()> {
        let mm = MMap::new(begin.0, bytes, perms);
        self.insert_mm(mm);
        Ok(())
    }

    /// Gets the mmap that contains the given range or returns an error.  Assumes
    /// a single mmap covers the whole range.
    fn get_mmap(&self, begin: u64, end: u64, perms: u8) -> Result<&MMap> {
        let mm = self.mmaps.lookup(begin);
        if let Some(mm) = mm {
            // begin and end must be within the region
            if (begin < mm.begin) || (begin >= mm.end) || (end < mm.begin) || (end > mm.end) {
                return Err(MemErr::UnmappedRegion(Addr(begin), perms));
            }

            mm.check_perms(begin, perms)?;

            Ok(mm)
        } else {
            Err(MemErr::UnmappedRegion(Addr(begin), perms))
        }
    }

    fn get_mut_mmap<F, V>(&mut self, begin: u64, end: u64, perms: u8, func: F) -> Result<V>
    where
        F: FnOnce(&mut MMap) -> Result<V>,
    {
        let mm = self.mmaps.lookup_mut(begin);
        if let Some(mm) = mm {
            // begin and end must be within the region
            // FIXME: repetition
            if (begin < mm.begin) || (begin >= mm.end) || (end < mm.begin) || (end > mm.end) {
                return Err(MemErr::UnmappedRegion(Addr(begin), perms));
            }

            mm.check_perms(begin, perms)?;
            func(mm)
        } else {
            Err(MemErr::UnmappedRegion(Addr(begin), perms))
        }
    }

    /// Checks that a memory region is mapped with the particular permissions.
    pub fn check_perms(&self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        let mm = self.get_mmap(begin.0, end.0, perms)?;
        mm.check_perms(begin.0, perms)?;
        Ok(())
    }

    /// Changes the permissions of a single mapped region.
    pub fn change_perms(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<u8> {
        let begin = begin.0;
        let end = end.0;
        self.get_mut_mmap(begin, end, 0, |mm| mm.change_perms(begin, end, perms))
    }

    // Dangerous, for use by the JIT only
    pub fn guest_to_host(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<u64> {
        let mm = self.get_mmap(begin.0, end.0, perms)?;
        let mm_begin = (begin.0 - mm.begin) as usize;
        let mm_end = (end.0 - mm.begin) as usize;
        let slice = &mm.bytes[mm_begin..mm_end];

        let ptr = slice.as_ptr();
        let addr = ptr as u64;

        Ok(addr)
    }

    /// Reads bytes from a memory range.  Fails if the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn read(&self, begin: Addr, bytes: &mut [u8], perms: u8) -> Result<()> {
        let begin = begin.0;
        let end = begin + (bytes.len() as u64);
        let mm = self.get_mmap(begin, end, perms)?;

        let len = end - begin;
        mm.read(begin, &mut bytes[0..(len as usize)], perms)?;

        Ok(())
    }

    /// When reading basic blocks we don't know how much to read, so this method
    /// just returns what is in the individual mmap.
    pub fn read_some<F, V>(&self, begin: Addr, perms: u8, func: F) -> Result<V>
    where
        F: FnOnce(&[u8]) -> V,
    {
        let begin = begin.0;
        let mm = self.get_mmap(begin, begin + 1, perms)?;

        let offset = (begin - mm.begin) as usize;
        Ok(func(&mm.bytes[offset..]))
    }

    /// Writes bytes to a memory range.  Fails in the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn write(&mut self, begin: Addr, bytes: &[u8], perms: u8) -> Result<()> {
        let begin = begin.0;
        let end = begin + (bytes.len() as u64);

        self.get_mut_mmap(begin, end, perms, |mm| {
            let len = end - begin;
            mm.write(begin, &bytes[0..(len as usize)], perms)?;
            Ok(())
        })
    }

    /// Zeroes a part of a single mmapped region.  Similar to write, but faster.
    pub fn zero(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        let begin = begin.0;
        let end = end.0;

        self.get_mut_mmap(begin, end, perms, |mm| {
            mm.zero(begin, end, perms)?;
            Ok(())
        })
    }

    /// Clears the 'written' bits for a region.  Used by the heap code when
    /// a block of memory is deallocated.
    pub fn forget(&mut self, begin: Addr, end: Addr) -> Result<()> {
        let begin = begin.0;
        let end = end.0;

        self.get_mut_mmap(begin, end, 0, |mm| {
            mm.forget(begin, end);
            Ok(())
        })
    }

    /// Accesses a primitive.  `perm` checked.
    pub fn read_into<T: Primitive>(&self, loc: Addr, perms: u8) -> Result<T> {
        let begin = loc.0;
        let mm = self.get_mmap(begin, begin + 1, perms)?;

        let offset = (begin - mm.begin) as usize;
        let bytes = &mm.bytes[offset..];

        if bytes.len() < ::core::mem::size_of::<T>() {
            return Err(MemErr::BadPerms(Addr(begin), perms));
        }

        Ok(unsafe { core::ptr::read_unaligned(bytes.as_ptr() as *const T) })
    }

    pub fn write_out<T: Primitive>(&mut self, v: T, begin: Addr, perms: u8) -> Result<()> {
        let begin = begin.0;
        self.get_mut_mmap(begin, begin + 1, perms, |mm| {
            let offset = (begin - mm.begin) as usize;
            let bytes = &mut mm.bytes[offset..];

            if bytes.len() < ::core::mem::size_of::<T>() {
                return Err(MemErr::BadPerms(Addr(begin), perms));
            }

            unsafe { core::ptr::write_unaligned(bytes.as_ptr() as *mut T, v) };
            Ok(())
        })?;
        Ok(())
    }

    /// Allocates a block of memory and moves the given bytes into it.
    ///
    /// The function allocates an extra double word before and after the block to detect overwrites.
    /// It returns the address of the allocated block.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A vector of bytes to move into the allocated block.
    /// * `perms` - The permissions to set for the allocated block.
    ///
    /// # Returns
    ///
    /// The address of the allocated block.
    ///
    /// # Errors
    ///
    /// The function returns an error if it fails to allocate memory or if the permissions are invalid.
    pub fn alloc_common(&mut self, bytes: Vec<u8>, perms: u8, pc: Option<u64>) -> Result<Addr> {
        // We allocate an extra double word before and after the block to
        // detect overwrites.
        let len = bytes.len();
        let heap_len = len + 8;
        let heap_ptr = self.heap.alloc(heap_len)?;

        // mmap just the central part that may be used.
        let ptr = Addr(heap_ptr.0 + 4);
        self.mmap_bytes(ptr, bytes, perms)?;
        match pc {
            Some(pc) => self
                .allocations
                .insert(ptr.0, MEntry::new_with_pc(heap_ptr.0, heap_len, pc)),
            None => self
                .allocations
                .insert(ptr.0, MEntry::new(heap_ptr.0, heap_len)),
        };
        Ok(ptr)
    }

    pub fn alloc_bytes(&mut self, bytes: Vec<u8>, perms: u8) -> Result<Addr> {
        self.alloc_common(bytes, perms, None)
    }

    pub fn alloc_with_pc(&mut self, bytes: Vec<u8>, perms: u8, pc: u64) -> Result<Addr> {
        self.alloc_common(bytes, perms, Some(pc))
    }

    pub fn alloc_with<F>(&mut self, count: usize, perms: u8, func: F) -> Result<Addr>
    where
        F: FnOnce(Addr, &mut [u8]) -> Result<()>,
    {
        // We allocate an extra double word before and after the block to
        // detect overwrites.
        let len = count;
        let heap_len = len + 8;
        let heap_ptr = self.heap.alloc(heap_len)?;

        // mmap just the central part that may be used.
        let ptr = Addr(heap_ptr.0 + 4);
        let mut bytes = vec![0u8; count];
        func(ptr, &mut bytes)?;
        self.mmap_bytes(ptr, bytes, perms)?;
        self.allocations
            .insert(ptr.0, MEntry::new(heap_ptr.0, heap_len));

        Ok(ptr)
    }

    /// Allocates a block of memory with a specified alignment and moves the given bytes into it.
    ///
    /// The function allocates an extra double word before and after the block to detect overwrites.
    /// It returns the address of the allocated block.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A vector of bytes to move into the allocated block.
    /// * `perms` - The permissions to set for the allocated block.
    /// * `align` - The alignment of the allocated block, in bytes.
    ///
    /// # Returns
    ///
    /// The address of the allocated block.
    ///
    /// # Errors
    ///
    /// The function returns an error if it fails to allocate memory or if the permissions are invalid.
    pub fn alloc_aligned(&mut self, bytes: Vec<u8>, perms: u8, align: usize) -> Result<Addr> {
        // We allocate an extra double word before and after the block to
        // detect overwrites.
        let len = bytes.len();
        let heap_len = len + align + 16;
        let heap_ptr = self.heap.alloc(heap_len)?;

        // mmap just the central part that may be used.
        let align = align as u64;
        let next = (heap_ptr.0 + 8).div_ceil(align) * align;
        let ptr = Addr(next);
        self.mmap_bytes(ptr, bytes, perms)?;
        self.allocations
            .insert(ptr.0, MEntry::new(heap_ptr.0, heap_len));
        Ok(ptr)
    }

    // Free returns the bytes that made up the allocation.  Useful for
    // bouncing block manager buffers between host and guest.
    pub fn free(&mut self, ptr: Addr) -> Result<Vec<u8>> {
        if let Some(MEntry { heap_ptr, .. }) = self.allocations.remove(&ptr.0) {
            self.heap.free(Addr(heap_ptr))?;
            self.unmap(ptr)
        } else {
            Err(MemErr::BadFree(ptr))
        }
    }

    /// This is a bit of a hack for use by printk and friends.
    pub fn read_string(&self, ptr: Addr) -> Result<String> {
        // We assume the string is short, and grab the indexes for that max range.
        // Then read bytes from it.
        let mut buffer = Vec::new();
        self.read_some(ptr, PERM_READ, |bytes| {
            for byte in bytes {
                if *byte == 0 {
                    break;
                }

                buffer.push(*byte);
            }
        })?;

        Ok(std::str::from_utf8(&buffer).unwrap().to_owned())
    }

    /// Returns the total amount of memory currently mapped.  This includes
    /// extra that we use for alignment or overrun detection unfortunately.  So
    /// this number is only really useful to spot memory leaks.
    pub fn total_allocated(&self) -> u64 {
        let mut total = 0;
        for MEntry { len, .. } in self.allocations.values() {
            total += len;
        }

        total as u64
    }
}

//-------------------------------------

#[derive(Clone)]
pub struct BuddyAllocator {
    // free_blocks[0] holds blocks of size 'block_size',
    // free_blocks[1]         "            2 * 'block_size' etc.
    //
    // If a block is not present in free_blocks, then it's been allocated
    free_blocks: Vec<BTreeSet<u64>>,

    // Allocated blocks are entered in here.  Maps block index to order.
    allocated: BTreeMap<u64, usize>,
}

fn get_buddy(index: u64, order: usize) -> u64 {
    index ^ (1 << order)
}

impl BuddyAllocator {
    pub fn new(order: usize) -> Self {
        assert!(order <= 32);
        let mut free_blocks = Vec::new();
        for _ in 0..(order + 1) {
            free_blocks.push(BTreeSet::new());
        }

        // we start with a single block of order size.
        free_blocks[order].insert(0);

        BuddyAllocator {
            free_blocks,
            allocated: BTreeMap::new(),
        }
    }

    fn alloc(&mut self, order: usize) -> Result<u64> {
        // We search up through the orders looking for one that
        // contains some free blocks.  We then split this block
        // back down through the orders, until we have one of the
        // desired size.
        let mut high_order = order;
        loop {
            if high_order >= self.free_blocks.len() {
                return Err(MemErr::OutOfSpace);
            }

            if !self.free_blocks[high_order].is_empty() {
                break;
            }

            high_order += 1;
        }

        let index = self.free_blocks[high_order].pop_first().unwrap();

        // split back down
        while high_order != order {
            high_order -= 1;
            self.free_blocks[high_order].insert(get_buddy(index, high_order));
        }

        assert!(!self.allocated.contains_key(&index));
        self.allocated.insert(index, order);
        Ok(index)
    }

    pub fn free(&mut self, mut index: u64) -> Result<()> {
        let order = self.allocated.remove(&index);
        if order.is_none() {
            // The heap class intercepts and turns the index into a
            // ptr.
            return Err(MemErr::BadFree(Addr(index)));
        }

        let mut order = order.unwrap();
        loop {
            let buddy = get_buddy(index, order);

            // Is the buddy free at this order?
            if !self.free_blocks[order].contains(&buddy) {
                break;
            }
            self.free_blocks[order].remove(&buddy);
            order += 1;

            if buddy < index {
                index = buddy;
            }

            if order == self.free_blocks.len() {
                break;
            }
        }

        self.free_blocks[order].insert(index);
        Ok(())
    }
}

#[test]
fn test_create_allocator() -> Result<()> {
    let _buddy = BuddyAllocator::new(10);
    Ok(())
}

#[test]
fn test_alloc_small() -> Result<()> {
    let mut buddy = BuddyAllocator::new(10);

    // order 0, is a single byte
    let index = buddy.alloc(0)?;
    assert!(index == 0);
    buddy.free(index)?;
    let index = buddy.alloc(0)?;
    assert!(index == 0);
    Ok(())
}

//-------------------------------------

const MIN_BLOCK_SIZE: usize = 8;
const MIN_BLOCK_SHIFT: usize = 3;
const MIN_BLOCK_MASK: u64 = 0b111;

/// A simple buddy allocator.  This is not attached to the memory directly
/// so the layer above this needs to allocate via this heap, and then mmap
/// the new chunk of memory.  Likewise the caller of free needs to unmap.
#[derive(Clone)]
pub struct Heap {
    base: u64,
    allocator: BuddyAllocator,
}

impl Heap {
    pub fn new(begin: Addr, end: Addr) -> Self {
        let len = end.0 - begin.0;
        assert!(len.is_power_of_two());
        let order = len.trailing_zeros() as usize;
        let order = order - MIN_BLOCK_SHIFT;
        let allocator = BuddyAllocator::new(order);

        Heap {
            base: begin.0,
            allocator,
        }
    }

    fn addr_to_index(&self, ptr: Addr) -> u64 {
        let ptr = ptr.0 - self.base;
        assert!((ptr & MIN_BLOCK_MASK) == 0);
        ptr >> MIN_BLOCK_SHIFT
    }

    fn index_to_addr(&self, index: u64) -> Addr {
        Addr(self.base + (index << MIN_BLOCK_SHIFT))
    }

    // Allocate a block of memory in the heap.
    pub fn alloc(&mut self, mut size: usize) -> Result<Addr> {
        if size < MIN_BLOCK_SIZE {
            size = MIN_BLOCK_SIZE;
        }
        let order = size.next_power_of_two().trailing_zeros() - (MIN_BLOCK_SHIFT as u32);
        let index = self.allocator.alloc(order as usize)?;
        let ptr = self.index_to_addr(index);

        Ok(ptr)
    }

    pub fn free(&mut self, ptr: Addr) -> Result<()> {
        let index = self.addr_to_index(ptr);
        match self.allocator.free(index) {
            Err(MemErr::BadFree(_)) => Err(MemErr::BadFree(ptr)),
            r => r,
        }
    }
}

#[test]
fn test_create_mem() -> Result<()> {
    let mem = Memory::new(Addr(0), Addr(1024));
    drop(mem);
    Ok(())
}

#[test]
fn test_single_mmap() -> Result<()> {
    let mut mem = Memory::new(Addr(0), Addr(1024));
    let begin = Addr(0xff);
    let end = Addr(begin.0 + 0xffff);
    mem.mmap(begin, end, PERM_READ)?;

    let mut buf = vec![0u8; 16];
    assert!(mem.read(Addr(0), &mut buf, 0).is_err());
    assert!(mem.read(Addr(begin.0 - 8), &mut buf, 0).is_err());
    mem.read(begin, &mut buf, 0)?;
    mem.read(Addr(end.0 - 16), &mut buf, 0)?;
    assert!(mem.read(Addr(end.0 - 8), &mut buf, 0).is_err());
    assert!(mem.read(Addr(0xffffff), &mut buf, 0).is_err());

    Ok(())
}

/*
// Currently we're not supporting memory accesses that span boundaries.
#[test]
fn test_adjacent_mmap() -> Result<()> {
    let mut mem = Memory::new(Addr(0), Addr(1024));
    let begin = Addr(64);
    let mid = Addr(128);
    let end = Addr(192);

    mem.mmap(begin, mid, PERM_READ)?;
    mem.mmap(mid, end, PERM_READ)?;

    let mut buf = vec![0u8; 16];
    mem.read(Addr(120), &mut buf, 0)?;

    Ok(())
}
*/

#[test]
fn test_heap_create() -> Result<()> {
    let h = Heap::new(Addr(0x1000), Addr(0x1000 + (1 << 12)));
    drop(h);

    Ok(())
}

#[test]
fn test_heap_alloc() -> Result<()> {
    let mut h = Heap::new(Addr(0x1000), Addr(0x1000 + (1 << 12)));
    let block = h.alloc(23)?;
    eprintln!("allocated block at {:?}", block);
    Ok(())
}

//-------------------------------------
