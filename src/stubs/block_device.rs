use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};

use crate::guest::*;
use crate::emulator::memory::*;

//-------------------------------

#[allow(dead_code)]
pub struct INode {
    pub nr_sectors: u64,
    pub ro: bool,
}

impl Guest for INode {
    fn guest_len() -> usize {
        16
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.nr_sectors)?;
        w.write_u64::<LittleEndian>(if self.ro { 1 } else { 0 })?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let nr_sectors = r.read_u64::<LittleEndian>()?;
        let ro = !r.read_u64::<LittleEndian>()? == 0;
        Ok(INode { nr_sectors, ro })
    }
}

//-------------------------------

/*
 * Kernel v5.12-rc8
 
Assumes SYSFS is enabled.
struct block_device {
    dev_t                      bd_dev;               /*    28     4 */
    struct inode *             bd_inode;             /*    40     8 */
    /* size: 832, cachelines: 13, members: 25 */
};
*/

const BD_DEV_OFFSET: usize = 28;
const BD_INODE_OFFSET: usize = 40;
const BDEV_SIZE: usize = 832;

#[allow(dead_code)]
pub struct BlockDevice {
    pub inode: Addr,
    pub dev_node: u32,
}

impl Guest for BlockDevice {
    fn guest_len() -> usize {
        BDEV_SIZE
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_all(&[0u8; BD_DEV_OFFSET])?;
        w.write_u32::<LittleEndian>(self.dev_node)?;
        w.write_all(&[0u8; BD_INODE_OFFSET - 4 - BD_DEV_OFFSET])?;
        w.write_u64::<LittleEndian>(self.inode.0)?;
        w.write_all(&[0u8; BDEV_SIZE - BD_INODE_OFFSET - 8])?;

        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let mut buf = [0u8; BD_DEV_OFFSET];
        r.read_exact(&mut buf)?;
        let dev_node = r.read_u32::<LittleEndian>()?;
        let mut buf = [0u8; BD_INODE_OFFSET - 4 - BD_DEV_OFFSET];
        r.read_exact(&mut buf)?;
        let inode = Addr(r.read_u64::<LittleEndian>()?);

        Ok(BlockDevice { inode, dev_node })
    }
}

// FIXME: remove in favour of auto_bdev
pub fn mk_block_device(mem: &mut Memory, dev_node: u32, nr_sectors: u64) -> Result<Addr> {
    let inode = INode {
        nr_sectors,
        ro: false,
    };
    let inode_ptr = alloc_guest::<INode>(mem, &inode, PERM_READ | PERM_WRITE)?;
    let bdev = BlockDevice {
        inode: inode_ptr,
        dev_node,
    };
    let bdev_ptr = alloc_guest::<BlockDevice>(mem, &bdev, PERM_READ | PERM_WRITE)?;
    Ok(bdev_ptr)
}

/*
pub fn auto_bdev<'a>(fix: &'a mut Fixture, dev_node: u32, nr_sectors: u64) -> Result<(AutoGPtr<'a>, Addr)> {
    let inode = INode {
        nr_sectors,
        ro: false,
    };
    let (mut fix, inode_ptr) = auto_guest::<INode>(&mut *fix, &inode, PERM_READ | PERM_WRITE)?;
    let bdev = BlockDevice {
        inode: inode_ptr,
        dev_node,
    };
    let (mut fix, bdev_ptr) = auto_guest::<BlockDevice>(&mut *fix, &bdev, PERM_READ | PERM_WRITE)?;
    Ok((fix, bdev_ptr))
}
*/

//-------------------------------
