use log::*;
use std::collections::HashMap;
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

// Internally addresses are split into a 32bit generation, and
// 32bit ptr.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// FIXME: make private
pub struct IAddr {
    generation: u32,
    ptr: u32,
}

fn to_iaddr(addr: Addr) -> IAddr {
    let generation = (addr.0 >> 32) as u32;
    let ptr = (addr.0 & ((1 << 32) - 1)) as u32;

    /*
        if ptr == 0 {
            panic!("don't panic");
        }
    */

    IAddr { generation, ptr }
}

fn to_addr(iaddr: IAddr) -> Addr {
    let ptr = ((iaddr.generation as u64) << 32) | (iaddr.ptr as u64);
    Addr(ptr)
}

//-------------------------------------

// FIXME: use an enum, or bitset or something
pub const PERM_READ: u8 = 1 << 0;
pub const PERM_WRITE: u8 = 1 << 1;
pub const PERM_EXEC: u8 = 1 << 2;

/// Memory for a region of the address space.
#[derive(Clone, Debug)]
struct MMap {
    addr: IAddr,
    bytes: Vec<u8>,
    perms: u8,
}

impl MMap {
    fn new(addr: IAddr, bytes: Vec<u8>, perms: u8) -> Self {
        MMap { addr, bytes, perms }
    }

    fn end_ptr(&self) -> u32 {
        self.addr.ptr + self.bytes.len() as u32
    }

    /// Checks all 'perms' are present for this region.
    fn check_perms(&self, addr: IAddr, perms: u8) -> Result<()> {
        if (self.perms & perms) != perms {
            debug!(
                "bad perms: addr = {:?}, mm.perms = {}, perms = {}",
                addr, self.perms, perms
            );
            return Err(MemErr::BadPerms(to_addr(addr), perms));
        }

        Ok(())
    }

    /// Checks the generations match.  Trivial, but I want to compute
    /// the Err code in one place.
    fn check_generation(&self, addr: IAddr, perms: u8) -> Result<()> {
        if self.addr.generation != addr.generation {
            debug!("generation mismatch");
            Err(MemErr::UnmappedRegion(to_addr(addr), perms))
        } else {
            Ok(())
        }
    }

    /// Changes the permissions of a mapped region.
    fn change_perms(&mut self, begin: IAddr, end: IAddr, mut perms: u8) -> Result<u8> {
        if begin.generation != end.generation {
            // FIXME: This could happen if end is right at the start of the next generation
            debug!("generation mismatch");
            return Err(MemErr::OutOfBounds);
        }

        if (begin.ptr != self.addr.ptr) || (end.ptr - begin.ptr != self.bytes.len() as u32) {
            return Err(MemErr::OutOfBounds);
        }

        std::mem::swap(&mut perms, &mut self.perms);
        Ok(perms)
    }

    /// Reads data from the region.  Fails if all the data can't be read
    /// from this region, or if any of the perms are not present.
    fn read(&self, begin: IAddr, bytes: &mut [u8], perms: u8) -> Result<()> {
        let end = IAddr {
            ptr: begin.ptr + bytes.len() as u32,
            generation: begin.generation,
        };

        // FIXME: can we roll these check together?
        self.check_generation(begin, perms)?;
        assert!(begin.ptr >= self.addr.ptr);
        assert!(end.ptr <= self.addr.ptr + self.bytes.len() as u32);
        self.check_perms(begin, perms)?;

        let slice = &self.bytes
            [((begin.ptr - self.addr.ptr) as usize)..((end.ptr - self.addr.ptr) as usize)];
        bytes.copy_from_slice(slice);

        Ok(())
    }

    /// Writes data to the region.  Fails if all the data can't be
    /// written to this region, or if any of the perms are not pesent.
    fn write(&mut self, begin: IAddr, bytes: &[u8], perms: u8) -> Result<()> {
        let end = IAddr {
            ptr: begin.ptr + bytes.len() as u32,
            generation: begin.generation,
        };

        // FIXME: can we roll these check together?
        self.check_generation(begin, perms)?;
        assert!(begin.ptr >= self.addr.ptr);
        assert!(end.ptr <= self.addr.ptr + self.bytes.len() as u32);
        self.check_perms(begin, perms)?;

        let slice = &mut self.bytes
            [((begin.ptr - self.addr.ptr) as usize)..((end.ptr - self.addr.ptr) as usize)];
        slice.copy_from_slice(bytes);

        Ok(())
    }

    fn zero(&mut self, begin: IAddr, end: IAddr, perms: u8) -> Result<()> {
        // FIXME: can we roll these check together?
        self.check_generation(begin, perms)?;
        assert!(begin.ptr >= self.addr.ptr);
        assert!(end.ptr <= self.addr.ptr + self.bytes.len() as u32);
        self.check_perms(begin, perms)?;

        let slice = &mut self.bytes
            [((begin.ptr - self.addr.ptr) as usize)..((end.ptr - self.addr.ptr) as usize)];

        unsafe {
            std::ptr::write_bytes(slice.as_ptr() as *mut u8, 0, slice.len());
        }
        Ok(())
    }

    /*
    /// Trashes any data in the region, and clear the written bits.
    fn forget(&mut self, begin: IAddr, end: IAddr) {
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
    */

    // Checks if the MMap contains the given address.
    fn contains(&self, addr: IAddr) -> bool {
        (addr.generation == self.addr.generation)
            && addr.ptr >= self.addr.ptr
            && addr.ptr < (self.addr.ptr + self.bytes.len() as u32)
    }
}

//-------------------------------------

// Uniform Layer struct.
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
    children: Vec<Option<Box<Layer>>>,

    // Precomputed shift for child index calculation
    shift: u32,
}

impl Layer {
    // Create a new layer covering the given range.
    // FIXME: should we change this to begin, len, so we can cover the full 32bit address range?
    fn new(begin: u64, end: u64) -> Self {
        let size = end - begin;
        let shift = size.trailing_zeros() - 8;
        Layer {
            begin,
            end,
            mappings: Vec::new(),
            children: Vec::new(),
            shift,
        }
    }

    fn no_children(&self) -> bool {
        self.children.is_empty()
    }

    fn has_children(&self) -> bool {
        !self.no_children()
    }

    fn create_children(&mut self) {
        self.children.reserve(256);
        for _ in 0..256 {
            self.children.push(None);
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
        let first_child_index = ((mmap.addr.ptr as u64 - self.begin) / child_size) as usize;
        let last_child_index = ((mmap.end_ptr() as u64 - 1 - self.begin) / child_size) as usize;

        if first_child_index == last_child_index {
            // The MMap fits entirely within one child layer.
            if self.no_children() {
                self.create_children();
            }

            let child = &mut self.children[first_child_index];
            if child.is_none() {
                *child = Some(Box::new(Layer::new(
                    self.begin + child_size * first_child_index as u64,
                    self.begin + child_size * (first_child_index as u64 + 1),
                )));
            }
            child.as_mut().unwrap().insert(mmap);
        } else {
            // The MMap crosses child boundaries; store at this level.
            self.mappings.push(mmap);
        }
    }

    // Looks up an MMap containing the given address.
    fn lookup(&self, addr: IAddr) -> Option<&MMap> {
        // Check if the address is within any of the mappings at this layer.
        for mm in &self.mappings {
            if mm.contains(addr) {
                return Some(mm);
            }
        }

        // If not, and if children exist, descend into the appropriate child.
        if self.has_children() {
            let child_index = self.child_index(addr);
            if let Some(child) = &self.children[child_index] {
                return child.lookup(addr);
            }
        }

        // Not found.
        None
    }

    // Similar to lookup, but returns a mutable reference.
    fn lookup_mut(&mut self, addr: IAddr) -> Option<&mut MMap> {
        // Compute necessary values before mutable borrow begins
        let child_index = self.child_index(addr);
        let has_children = self.has_children();

        for mm in &mut self.mappings {
            if mm.contains(addr) {
                return Some(mm);
            }
        }

        if has_children {
            if let Some(child) = &mut self.children[child_index] {
                return child.lookup_mut(addr);
            }
        }

        None
    }

    // Removes an MMap starting at the given address.
    fn remove(&mut self, addr: IAddr) -> Option<MMap> {
        // First, try to remove from mappings at this layer.
        if let Some(pos) = self.mappings.iter().position(|mm| mm.addr == addr) {
            // Found it in this layer's mappings; remove and return it.
            return Some(self.mappings.swap_remove(pos));
        }

        // Precompute child_index if children exist.
        if self.has_children() {
            let child_index = self.child_index(addr);

            // Now, we can mutably borrow self.children safely.
            if let Some(child) = &mut self.children[child_index] {
                return child.remove(addr);
            }
        }

        // If no mappings or children are found, return None.
        None
    }

    // Determines the index of the child that contains the given address.
    fn child_index(&self, addr: IAddr) -> usize {
        ((addr.ptr as u64 - self.begin) >> self.shift) as usize
    }

    fn build_histogram(&self, depth: usize, hist: &mut HashMap<usize, HashMap<usize, usize>>) {
        let num_mappings = self.mappings.len();
        let depth_hist = hist.entry(depth).or_insert_with(HashMap::new);
        *depth_hist.entry(num_mappings).or_insert(0) += 1;

        if self.has_children() {
            for child in &self.children {
                if let Some(child) = child {
                    child.build_histogram(depth + 1, hist);
                }
            }
        }
    }
}

#[derive(Clone)]
/// Although the Trie takes 64 bit addresses, it only actually covers a 32bit address
/// range.  This is plenty for our tests, and allows us to use the other 32 bits of a ptr
/// for a 'generation'.
struct Trie {
    root: Layer,
}

impl Trie {
    fn new() -> Self {
        Trie {
            root: Layer::new(0, 1 << 32),
        }
    }

    fn insert(&mut self, mmap: MMap) {
        self.root.insert(mmap);
    }

    fn lookup(&self, addr: IAddr) -> Option<&MMap> {
        self.root.lookup(addr)
    }

    fn lookup_mut(&mut self, addr: IAddr) -> Option<&mut MMap> {
        self.root.lookup_mut(addr)
    }

    fn remove(&mut self, addr: IAddr) -> Option<MMap> {
        self.root.remove(addr)
    }

    fn print_histogram(&self) {
        let mut hist = HashMap::new();
        self.root.build_histogram(0, &mut hist);
        debug!("layer histogram: {:?}", hist);
    }
}

//-------------------------------------

#[derive(Clone, Debug)]
pub struct MEntry {
    pub heap_ptr: IAddr,
    pub len: usize,

    // Riscv program counter that made the call.  Optional because
    // a lot of memory gets allocated by stubs.
    pub pc: Option<u64>,
}

impl MEntry {
    fn new(heap_ptr: IAddr, len: usize) -> Self {
        Self {
            heap_ptr,
            len,
            pc: None,
        }
    }

    fn new_with_pc(heap_ptr: IAddr, len: usize, pc: u64) -> Self {
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

    // The generation is incremented for each heap allocation.  This will mean
    // a free followed by an allocation will not return the same pointer and so
    // make it more likely that we spot use after free issues.
    generation: u32,

    // Maps the ptr returned by alloc_bytes() back to the heap ptr and len.
    allocations: BTreeMap<Addr, MEntry>,
}

impl Memory {
    pub fn new(heap_begin: Addr, heap_end: Addr) -> Self {
        Memory {
            mmaps: Trie::new(),
            heap: Heap::new(heap_begin, heap_end),
            generation: 0,
            allocations: BTreeMap::new(),
        }
    }

    pub fn print_histogram(&self) {
        self.mmaps.print_histogram();
    }

    pub fn snapshot(&self) -> Self {
        Memory {
            mmaps: self.mmaps.clone(),
            heap: self.heap.clone(),
            generation: self.generation,
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

    fn insert_mm(&mut self, mm: MMap) {
        self.mmaps.insert(mm);
    }

    /// Remove an mmapped area.
    pub fn unmap(&mut self, begin: Addr) -> Result<Vec<u8>> {
        let begin = to_iaddr(begin);
        let mm = self.mmaps.remove(begin);

        if let Some(mut mm) = mm {
            let mut bytes = Vec::new();
            std::mem::swap(&mut mm.bytes, &mut bytes);
            Ok(bytes)
        } else {
            Err(MemErr::BadFree(to_addr(begin)))
        }
    }

    /// Creates a new mapped region of memory with the specified perms.  The
    /// data will be uninitialised.
    pub fn mmap(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        self.mmap_zeroes(begin, end, perms)
    }

    /// Like mmap, but it intialises the data with zeroes and sets the written bits.
    pub fn mmap_zeroes(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        let len = end.0 - begin.0;
        let begin = to_iaddr(begin);
        let end = to_iaddr(end);
        assert!(begin.generation == end.generation);
        assert!(begin.ptr <= end.ptr);

        let mm = MMap::new(begin, vec![0u8; len as usize], perms);
        self.insert_mm(mm);
        Ok(())
    }

    /// Creates a new mapping with the given permissions and takes ownership
    /// it with the given data.  This is an efficient way to pass data from
    /// the host to the guest.
    pub fn mmap_bytes(&mut self, begin: Addr, bytes: Vec<u8>, perms: u8) -> Result<()> {
        let begin = to_iaddr(begin);
        let mm = MMap::new(begin, bytes, perms);
        self.insert_mm(mm);
        Ok(())
    }

    /// Gets the mmap that contains the given range or returns an error.  Assumes
    /// a single mmap covers the whole range.
    fn get_mmap(&self, begin: IAddr, end: IAddr, perms: u8) -> Result<&MMap> {
        if begin.generation != end.generation {
            return Err(MemErr::UnmappedRegion(to_addr(begin), perms));
        }

        let mm = self.mmaps.lookup(begin);
        if let Some(mm) = mm {
            // begin and end must be within the region
            if end.ptr > mm.end_ptr() {
                return Err(MemErr::UnmappedRegion(to_addr(begin), perms));
            }

            mm.check_perms(begin, perms)?;

            Ok(mm)
        } else {
            Err(MemErr::UnmappedRegion(to_addr(begin), perms))
        }
    }

    fn get_mut_mmap<F, V>(&mut self, begin: IAddr, end: IAddr, perms: u8, func: F) -> Result<V>
    where
        F: FnOnce(&mut MMap) -> Result<V>,
    {
        if begin.generation != end.generation {
            return Err(MemErr::UnmappedRegion(to_addr(begin), perms));
        }

        let mm = self.mmaps.lookup_mut(begin);
        if let Some(mm) = mm {
            // begin and end must be within the region
            if end.ptr > mm.end_ptr() {
                return Err(MemErr::UnmappedRegion(to_addr(begin), perms));
            }

            mm.check_perms(begin, perms)?;
            func(mm)
        } else {
            Err(MemErr::UnmappedRegion(to_addr(begin), perms))
        }
    }

    /// Checks that a memory region is mapped with the particular permissions.
    pub fn check_perms(&self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        let begin = to_iaddr(begin);
        let end = to_iaddr(end);

        let mm = self.get_mmap(begin, end, perms)?;
        mm.check_perms(begin, perms)?;
        Ok(())
    }

    /// Changes the permissions of a single mapped region.
    pub fn change_perms(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<u8> {
        let begin = to_iaddr(begin);
        let end = to_iaddr(end);

        self.get_mut_mmap(begin, end, 0, |mm| mm.change_perms(begin, end, perms))
    }

    // Dangerous, for use by the JIT only
    pub fn guest_to_host(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<u64> {
        todo!();

        /*
                let generation = get_generation(begin.0);
                if generation != get_generation(end.0) {
                    warn!("mismatched generations");
                    return Err(MemErr::UnmappedRegion(begin, perms));
                }
                let begin = get_ptr(begin.0);
                let end = get_ptr(end.0);

                let mm = self.get_mmap(begin, end, perms)?;
                let mm_begin = (begin - mm.begin) as usize;
                let mm_end = (end - mm.begin) as usize;
                let slice = &mm.bytes[mm_begin..mm_end];

                let ptr = slice.as_ptr();
                let addr = ptr as u64;

                Ok(addr)
        */
    }

    /// Reads bytes from a memory range.  Fails if the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn read(&self, begin: Addr, bytes: &mut [u8], perms: u8) -> Result<()> {
        let mut end = to_iaddr(begin);
        end.ptr += bytes.len() as u32;
        let begin = to_iaddr(begin);

        let mm = self.get_mmap(begin, end, perms)?;

        let len = end.ptr - begin.ptr;
        mm.read(begin, &mut bytes[0..(len as usize)], perms)?;

        Ok(())
    }

    /// When reading basic blocks we don't know how much to read, so this method
    /// just returns what is in the individual mmap.
    pub fn read_some<F, V>(&self, begin: Addr, perms: u8, func: F) -> Result<V>
    where
        F: FnOnce(&[u8]) -> V,
    {
        let begin = to_iaddr(begin);
        let mut end = begin;
        end.ptr += 1;
        let mm = self.get_mmap(begin, end, perms)?;

        let offset = (begin.ptr - mm.addr.ptr) as usize;
        Ok(func(&mm.bytes[offset..]))
    }

    /// Writes bytes to a memory range.  Fails in the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn write(&mut self, begin: Addr, bytes: &[u8], perms: u8) -> Result<()> {
        let begin = to_iaddr(begin);
        let mut end = begin;
        end.ptr += bytes.len() as u32;

        self.get_mut_mmap(begin, end, perms, |mm| {
            mm.write(begin, &bytes[..], perms)?;
            Ok(())
        })
    }

    /// Zeroes a part of a single mmapped region.  Similar to write, but faster.
    pub fn zero(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        let begin = to_iaddr(begin);
        let end = to_iaddr(end);

        self.get_mut_mmap(begin, end, perms, |mm| {
            mm.zero(begin, end, perms)?;
            Ok(())
        })
    }

    /*
    /// Clears the 'written' bits for a region.  Used by the heap code when
    /// a block of memory is deallocated.
    pub fn forget(&mut self, begin: Addr, end: Addr) -> Result<()> {
        let begin = begin.0;
        let end = end.0;

        self.get_mut_mmap(begin, end, 0, |mm| {
            mm.forget(get_ptr(begin), get_ptr(end));
            Ok(())
        })
    }
    */

    /// Accesses a primitive.  `perm` checked.
    pub fn read_into<T: Primitive>(&self, begin: Addr, perms: u8) -> Result<T> {
        let begin = to_iaddr(begin);
        let mut end = begin;
        end.ptr += 1;

        let mm = self.get_mmap(begin, end, perms)?;

        let offset = (begin.ptr - mm.addr.ptr) as usize;
        let bytes = &mm.bytes[offset..];

        if bytes.len() < ::core::mem::size_of::<T>() {
            return Err(MemErr::BadPerms(to_addr(begin), perms));
        }

        Ok(unsafe { core::ptr::read_unaligned(bytes.as_ptr() as *const T) })
    }

    pub fn write_out<T: Primitive>(&mut self, v: T, begin: Addr, perms: u8) -> Result<()> {
        let begin = to_iaddr(begin);
        let mut end = begin;
        end.ptr += 1;

        self.get_mut_mmap(begin, end, perms, |mm| {
            let offset = (begin.ptr - mm.addr.ptr) as usize;
            let bytes = &mut mm.bytes[offset..];

            if bytes.len() < ::core::mem::size_of::<T>() {
                return Err(MemErr::BadPerms(to_addr(begin), perms));
            }

            unsafe { core::ptr::write_unaligned(bytes.as_ptr() as *mut T, v) };
            Ok(())
        })?;
        Ok(())
    }

    fn next_generation(&mut self) -> u32 {
        let g = self.generation;
        self.generation += 1;
        g
    }

    /// Allocates a block of memory and moves the given bytes into it.
    ///
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
        let len = bytes.len();
        let ptr = self.heap.alloc(len)?;
        let generation = self.next_generation();
        let ptr = IAddr {
            generation,
            ptr: ptr.0 as u32,
        };
        let addr = to_addr(ptr);

        self.mmap_bytes(addr, bytes, perms)?;
        match pc {
            Some(pc) => self
                .allocations
                .insert(addr, MEntry::new_with_pc(ptr, len, pc)),
            None => self.allocations.insert(addr, MEntry::new(ptr, len)),
        };

        Ok(addr)
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
        let len = count;
        let heap_ptr = self.heap.alloc(len)?;
        let generation = self.next_generation();
        let ptr = IAddr {
            generation,
            ptr: heap_ptr.0 as u32,
        };
        let addr = to_addr(ptr);

        let mut bytes = vec![0u8; count];
        func(addr, &mut bytes)?;
        self.mmap_bytes(addr, bytes, perms)?;
        self.allocations.insert(addr, MEntry::new(ptr, len));

        Ok(addr)
    }

    /// Allocates a block of memory with a specified alignment and moves the given bytes into it.
    ///
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
        let len = bytes.len();
        let heap_len = len + align;
        let heap_ptr = self.heap.alloc(heap_len)?;
        let generation = self.next_generation();
        let ptr = IAddr {
            generation,
            ptr: heap_ptr.0 as u32,
        };

        let align = align as u64;
        let mut next = ptr;
        next.ptr = next.ptr.div_ceil(align as u32) * align as u32;
        let addr = to_addr(next);
        self.mmap_bytes(addr, bytes, perms)?;
        self.allocations.insert(addr, MEntry::new(ptr, heap_len));
        Ok(to_addr(next))
    }

    // Free returns the bytes that made up the allocation.  Useful for
    // bouncing block manager buffers between host and guest.
    pub fn free(&mut self, ptr: Addr) -> Result<Vec<u8>> {
        if let Some(MEntry { heap_ptr, .. }) = self.allocations.remove(&ptr) {
            let mut no_gen = heap_ptr;
            no_gen.generation = 0;
            self.heap.free(to_addr(no_gen))?;
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
