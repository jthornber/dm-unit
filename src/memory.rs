use fixedbitset::FixedBitSet;
use intrusive_collections::intrusive_adapter;
use intrusive_collections::{Bound, KeyAdapter, RBTree, RBTreeLink};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;
use std::result;
use thiserror::Error;

use crate::primitive::Primitive;

//-------------------------------------

/// An address used within the guest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Addr(pub u64);

impl fmt::LowerHex for Addr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.0;
        fmt::LowerHex::fmt(&val, f)
    }
}

//-------------------------------------

/// Indicates memory errors such as referencing unallocated memory.  Or bad permissions.
#[derive(Error, Debug)]
pub enum MemErr {
    #[error("Memory is not mapped at {0:?}")]
    UnmappedRegion(Addr),

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
struct MMap {
    perms: u8,
    begin: u64,
    end: u64,
    bytes: Vec<u8>,
    written: FixedBitSet,
}

impl MMap {
    fn new(begin: u64, end: u64, perms: u8) -> Self {
        let len = (end - begin) as usize;
        MMap {
            perms,
            begin,
            end,
            bytes: vec![0u8; len],
            written: FixedBitSet::with_capacity(len),
        }
    }

    /// Checks all 'perms' are present for this region.
    fn check_perms(&self, begin: u64, perms: u8) -> Result<()> {
        if (self.perms & perms) != perms {
            return Err(MemErr::BadPerms(Addr(begin), perms));
        }

        Ok(())
    }

    /// Checks that the bytes have been written for the given range.
    fn check_written(&self, begin: u64, end: u64) -> Result<()> {
        let begin = begin - self.begin;
        let end = end - self.begin;
        for b in begin..end {
            if !self.written.contains(b as usize) {
                // return Err(MemErr::BadRead(Addr(b + self.begin)));
            }
        }

        Ok(())
    }

    /// Sets the written bits for a given range.
    fn set_written(&mut self, begin: u64, end: u64, enabled: bool) {
        let begin = begin - self.begin;
        let end = end - self.begin;
        for b in begin..end {
            self.written.set(b as usize, enabled);
        }
    }

    /// Reads data from the region.  Fails if all the data can't be read from this
    /// region, or if any of the perms are not present.
    fn read(&self, begin: u64, bytes: &mut [u8], perms: u8) -> Result<()> {
        let end = begin + (bytes.len() as u64);
        assert!(begin >= self.begin);
        assert!(end <= self.end);

        self.check_perms(begin, perms)?;
        self.check_written(begin, end)?;

        let slice = &self.bytes[((begin - self.begin) as usize)..((end - self.begin) as usize)];
        bytes.copy_from_slice(slice);

        Ok(())
    }

    /// Writes data to the region.  Fails if all the data can't be written to this
    /// region, or if any of the perms are not pesent.
    fn write(&mut self, begin: u64, bytes: &[u8], perms: u8) -> Result<()> {
        let end = begin + (bytes.len() as u64);
        assert!(begin >= self.begin);
        assert!(end <= self.end);

        self.check_perms(begin, perms)?;

        let slice = &mut self.bytes[((begin - self.begin) as usize)..((end - self.begin) as usize)];
        slice.copy_from_slice(bytes);
        self.set_written(begin, end, true);

        Ok(())
    }

    /// Zeroes a region, setting the written bits.  Fails if all the
    /// data can't be written to this region, or if any of the perms
    /// are not pesent.
    fn zero(&mut self, begin: u64, end: u64, perms: u8) -> Result<()> {
        assert!(begin >= self.begin);
        assert!(end <= self.end);

        let zeroes = vec![0u8; (end - begin) as usize];
        self.write(begin, &zeroes, perms)
    }

    /// Trashes any data in the region, and clear the written bits.
    fn forget(&mut self, begin: u64, end: u64) {
        self.set_written(begin, end, false);

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
}

struct MMapIndex {
    link: RBTreeLink,
    begin: u64,
    index: usize,
}

impl MMapIndex {
    fn new(begin: u64, index: usize) -> Self {
        MMapIndex {
            link: RBTreeLink::default(),
            begin,
            index,
        }
    }
}

intrusive_adapter!(MMapAdapter = Box<MMapIndex>: MMapIndex { link: RBTreeLink });
impl<'a> KeyAdapter<'a> for MMapAdapter {
    type Key = u64;
    fn get_key(&self, mmi: &'a MMapIndex) -> u64 {
        mmi.begin
    }
}

//-------------------------------------

/// Manages memory for the vm.  Tracks permissions at the byte level.
/// Checks memory has been initialised before it's read.
pub struct Memory {
    index: RBTree<MMapAdapter>,
    mmaps: Vec<MMap>,
}

// FIXME: implement snapshotting.

impl Memory {
    pub fn new() -> Self {
        Memory {
            index: RBTree::new(MMapAdapter::new()),
            mmaps: Vec::new(),
        }
    }

    /// Inserts a MMap into both the mmaps vec, and the index rbtree.
    fn insert_mm(&mut self, mm: MMap) {
        let index = self.mmaps.len();
        let begin = mm.begin;
        self.mmaps.push(mm);
        self.index.insert(Box::new(MMapIndex::new(begin, index)));
    }

    /// Creates a new mapped region of memory with the specified perms.  The
    /// data will be uninitialised.
    pub fn mmap(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        assert!(begin.0 <= end.0);
        let mm = MMap::new(begin.0, end.0, perms);
        self.insert_mm(mm);
        Ok(())
    }

    /// Like mmap, but it intialises the data with zeroes and sets the written bits.
    pub fn mmap_zeroes(&mut self, begin: Addr, end: Addr, perms: u8) -> Result<()> {
        assert!(begin.0 <= end.0);
        let mut mm = MMap::new(begin.0, end.0, perms);
        mm.zero(begin.0, end.0, 0)?;
        self.insert_mm(mm);
        Ok(())
    }

    /// Creates a new mapping with the given permissions and intialises
    /// it with the given data.  This method is needed because perm may
    /// not include PERM_WRITE, which would prevent self.write being
    /// used to initialise the data.
    pub fn mmap_bytes(&mut self, begin: Addr, bytes: &[u8], perms: u8) -> Result<()> {
        let mut mm = MMap::new(begin.0, begin.0 + (bytes.len() as u64), perms);
        mm.write(begin.0, bytes, 0)?;
        self.insert_mm(mm);
        Ok(())
    }

    /// Builds a vec of mmap indexes within a given address range.
    fn get_indexes(&self, mut begin: u64, end: u64) -> Result<VecDeque<usize>> {
        let mut cursor = self.index.upper_bound(Bound::Included(&begin));
        let mut indexes = VecDeque::new();

        while begin < end {
            eprintln!("get_indexes: begin = {}", begin);
            if cursor.is_null() {
                eprintln!("exit 1, begin = {}, end = {}", begin, end);
                return Err(MemErr::UnmappedRegion(Addr(begin)));
            }

            let mi = cursor.get().unwrap();
            let mm = &self.mmaps[mi.index];

            // begin must be within the region
            if (begin < mm.begin) || (begin >= mm.end) {
                eprintln!("exit 2");
                return Err(MemErr::UnmappedRegion(Addr(begin)));
            }

            indexes.push_back(mi.index);
            eprintln!("setting begin to {}", mm.end);
            begin = mm.end;
            cursor.move_next();
        }

        Ok(indexes)
    }

    /// Reads bytes from a memory range.  Fails if the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn read(&self, begin: Addr, mut bytes: &mut [u8], perms: u8) -> Result<()> {
        let mut begin = begin.0;
        let end = begin + (bytes.len() as u64);

        eprintln!(">>> read, begin = {}, end = {}", begin, end);

        let mut indexes = self.get_indexes(begin, end)?;
        eprintln!("indexes = {:?}", indexes);

        while begin < end {
            if indexes.len() == 0 {
                return Err(MemErr::BadPerms(Addr(begin), perms));
            }

            let index = indexes.pop_front().unwrap();
            let mm = &self.mmaps[index];

            // begin must be within mm, otherwise we have a gap.
            if begin >= mm.end {
                return Err(MemErr::BadPerms(Addr(begin), perms));
            }

            let len = std::cmp::min(end, mm.end) - begin;
            mm.read(begin, &mut bytes[0..(len as usize)], perms)?;

            bytes = &mut bytes[(len as usize)..];
            begin += len;
        }

        eprintln!("<<< read");
        Ok(())
    }

    /// Writes bytes to a memory range.  Fails in the bits in 'perms' are
    /// not set for any byte in the range.
    pub fn write(&mut self, begin: Addr, mut bytes: &[u8], perms: u8) -> Result<()> {
        let mut begin = begin.0;
        let end = begin + (bytes.len() as u64);

        let mut indexes = self.get_indexes(begin, end)?;

        let mut mmaps = Vec::new();
        std::mem::swap(&mut mmaps, &mut self.mmaps);

        while begin < end {
            if indexes.len() == 0 {
                return Err(MemErr::BadPerms(Addr(begin), perms));
            }

            let index = indexes.pop_front().unwrap();
            let mm = &mut mmaps[index];

            // begin must be within mm, otherwise we have a gap.
            if begin >= mm.end {
                return Err(MemErr::BadPerms(Addr(begin), perms));
            }

            let len = std::cmp::min(end, mm.end) - begin;
            mm.write(begin, &bytes[0..(len as usize)], perms)?;

            bytes = &bytes[(len as usize)..];
            begin += len;
        }

        std::mem::swap(&mut mmaps, &mut self.mmaps);
        Ok(())
    }

    /// Clears the 'written' bits for a region.  Used by the heap code when
    /// a block of memory is deallocated.
    pub fn forget(&mut self, begin: Addr, end: Addr) -> Result<()> {
        let mut begin = begin.0;
        let end = end.0;

        let mut indexes = self.get_indexes(begin, end)?;

        let mut mmaps = Vec::new();
        std::mem::swap(&mut mmaps, &mut self.mmaps);

        while begin < end {
            if indexes.len() == 0 {
                return Err(MemErr::BadPerms(Addr(begin), 0));
            }

            let index = indexes.pop_front().unwrap();
            let mm = &mut mmaps[index];

            // begin must be within mm, otherwise we have a gap.
            if begin >= mm.end {
                return Err(MemErr::BadPerms(Addr(begin), 0));
            }

            let len = std::cmp::min(end, mm.end) - begin;
            mm.forget(begin, end);
            begin += len;
        }

        std::mem::swap(&mut mmaps, &mut self.mmaps);
        Ok(())
    }

    /// Accesses a primitive, loc must be 4 byte aligned.  `perm` checked.
    pub fn read_into<T: Primitive>(&mut self, loc: Addr, perm: u8) -> Result<T> {
        let mut dest = [0u8; 16];
        self.read(loc, &mut dest[..::core::mem::size_of::<T>()], perm)?;

        Ok(unsafe { core::ptr::read_unaligned(dest.as_ptr() as *const T) })
    }

    pub fn create_heap(&mut self, begin: Addr, end: Addr) -> Result<Heap> {
        let size = end.0 - begin.0;
        assert!(size.count_ones() == 1);
        self.mmap_zeroes(begin, end, PERM_READ | PERM_WRITE)?;
        Ok(Heap::new(begin, size.trailing_zeros() as usize))
    }
}

//-------------------------------------

const MIN_BLOCK_SIZE: u64 = 8;
const MIN_BLOCK_SHIFT: u64 = 3;
const MAX_ORDER: u64 = 13; // 64k will be the largest allocation size

pub struct Heap {
    base: u64,

    // The minimum block size
    block_size: usize,

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

impl Heap {
    pub fn new(begin: Addr, order: usize) -> Self {
        let order = order - MIN_BLOCK_SHIFT as usize;
        eprintln!("order = {}", order);
        assert!(order <= MAX_ORDER as usize);

        let mut free_blocks = Vec::new();
        for _ in MIN_BLOCK_SHIFT..MAX_ORDER {
            free_blocks.push(BTreeSet::new());
        }

        eprintln!("inserting free block at order {}", order);
        free_blocks[order].insert(begin.0);

        Heap {
            base: begin.0,
            block_size: MIN_BLOCK_SIZE as usize,
            free_blocks,
            allocated: BTreeMap::new(),
        }
    }

    fn addr_to_index(&self, ptr: Addr) -> u64 {
        (ptr.0 - self.base) >> MIN_BLOCK_SHIFT
    }

    fn index_to_addr(&self, index: u64) -> Addr {
        Addr(self.base + (index << MIN_BLOCK_SHIFT))
    }

    fn alloc_order(&mut self, order: usize) -> Result<u64> {
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

        eprintln!(
            "self.free_blocks[{}].len() = {}",
            high_order,
            self.free_blocks[high_order].len()
        );
        let index = self.free_blocks[high_order].pop_first().unwrap();

        // split back down
        while high_order != order {
            high_order -= 1;
            self.free_blocks[high_order].insert(get_buddy(index, high_order));
        }

        Ok(index)
    }

    // Allocate a block of memory in the heap.
    pub fn alloc(&mut self, mut size: usize) -> Result<Addr> {
        if size < self.block_size {
            size = self.block_size;
        }
        let order = size.next_power_of_two().trailing_zeros() - (MIN_BLOCK_SHIFT as u32);
        let index = self.alloc_order(order as usize)?;
        let ptr = self.index_to_addr(index);

        // FIXME: adjust perms in heap here.

        Ok(ptr)
    }

    pub fn free(&mut self, ptr: Addr) -> Result<()> {
        let mut index = self.addr_to_index(ptr);
        let order = self.allocated.get(&index);
        if order.is_none() {
            return Err(MemErr::BadFree(ptr));
        }

        let mut order = *order.unwrap();
        self.allocated.remove(&index);

        loop {
            let buddy = get_buddy(index, order);
            if !self.allocated.contains_key(&buddy) {
                order += 1;
            } else {
                break;
            }

            if buddy < index {
                index = buddy;
            }
        }

        self.free_blocks[order].insert(index);
        Ok(())
    }

/*
    // It's important that we have no bugs in this allocator
    // because it would put all the test results into question.
    // These methods are just for use by the unit tests.
    fn is_allocated(&self, ptr: Addr, size: usize) -> bool {
        todo!();
    }

    fn is_free(&self, ptr: Addr, order: usize) -> bool {
        todo!();
    }
    */
}

#[test]
fn test_create_mem() -> Result<()> {
    let mem = Memory::new();
    drop(mem);
    Ok(())
}

#[test]
fn test_single_mmap() -> Result<()> {
    let mut mem = Memory::new();
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

#[test]
fn test_adjacent_mmap() -> Result<()> {
    let mut mem = Memory::new();
    let begin = Addr(64);
    let mid = Addr(128);
    let end = Addr(192);

    mem.mmap(begin, mid, PERM_READ)?;
    mem.mmap(mid, end, PERM_READ)?;

    let mut buf = vec![0u8; 16];
    mem.read(Addr(120), &mut buf, 0)?;

    Ok(())
}

#[test]
fn test_heap_create() -> Result<()> {
    let h = Heap::new(Addr(0x1000), 12);
    drop(h);

    Ok(())
}

#[test]
fn test_heap_alloc() -> Result<()> {
    let mut h = Heap::new(Addr(0x1000), 12);
    let block = h.alloc(23)?;
    eprintln!("allocated block at {:?}", block);
    Ok(())
}

//-------------------------------------
