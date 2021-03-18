use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use std::io;
use std::io::{Read, Write};

use crate::guest::*;
use crate::memory::*;

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

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.nr_sectors)?;
        w.write_u64::<LittleEndian>(if self.ro { 1 } else { 0 })?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let nr_sectors = r.read_u64::<LittleEndian>()?;
        let ro = !r.read_u64::<LittleEndian>()? == 0;
        Ok(INode { nr_sectors, ro })
    }
}

//-------------------------------

/*
Assumes SYSFS is enabled.
struct block_device {
    dev_t                      bd_dev;               /*     0     4 */
    int                        bd_openers;           /*     4     4 */
    struct inode *             bd_inode;             /*     8     8 */
    struct super_block *       bd_super;             /*    16     8 */
    struct mutex               bd_mutex;             /*    24    64 */
    /* --- cacheline 1 boundary (64 bytes) was 24 bytes ago --- */
    void *                     bd_claiming;          /*    88     8 */
    void *                     bd_holder;            /*    96     8 */
    int                        bd_holders;           /*   104     4 */
    bool                       bd_write_holder;      /*   108     1 */

    /* XXX 3 bytes hole, try to pack */

    struct list_head           bd_holder_disks;      /*   112    16 */
    /* --- cacheline 2 boundary (128 bytes) --- */
    struct block_device *      bd_contains;          /*   128     8 */
    u8                         bd_partno;            /*   136     1 */

    /* XXX 7 bytes hole, try to pack */

    struct hd_struct *         bd_part;              /*   144     8 */
    unsigned int               bd_part_count;        /*   152     4 */

    /* XXX 4 bytes hole, try to pack */

    spinlock_t                 bd_size_lock;         /*   160    24 */
    struct gendisk *           bd_disk;              /*   184     8 */
    /* --- cacheline 3 boundary (192 bytes) --- */
    struct backing_dev_info *  bd_bdi;               /*   192     8 */
    int                        bd_fsfreeze_count;    /*   200     4 */

    /* XXX 4 bytes hole, try to pack */

    struct mutex               bd_fsfreeze_mutex;    /*   208    64 */

    /* size: 272, cachelines: 5, members: 19 */
    /* sum members: 254, holes: 4, sum holes: 18 */
    /* last cacheline: 16 bytes */
};
*/

#[allow(dead_code)]
pub struct BlockDevice {
    pub inode: Addr,
    pub dev_node: u32,
}

impl Guest for BlockDevice {
    fn guest_len() -> usize {
        272
    }

    fn pack<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_u32::<LittleEndian>(self.dev_node)?; // bd_dev
        w.write_i32::<LittleEndian>(0)?; // bd_openers
        w.write_u64::<LittleEndian>(self.inode.0)?; // bd_inode
        w.write_all(&vec![0u8; 272 - 16])?; // everything else

        Ok(())
    }

    fn unpack<R: Read>(r: &mut R) -> io::Result<Self> {
        let dev_node = r.read_u32::<LittleEndian>()?;
        let _bd_openers = r.read_i32::<LittleEndian>()?;
        let inode = Addr(r.read_u64::<LittleEndian>()?);

        Ok(BlockDevice { inode, dev_node })
    }
}

// FIXME: use auto alloc
pub fn mk_block_device(mem: &mut Memory, dev_node: u32, nr_sectors: u64) -> Result<Addr> {
    let inode = INode {
        nr_sectors,
        ro: false,
    };
    let inode_ptr = alloc_guest::<INode>(mem, &inode, PERM_READ | PERM_WRITE)?;
    debug!("allocated inode at {:?}", inode_ptr);
    let bdev = BlockDevice {
        inode: inode_ptr,
        dev_node,
    };
    let bdev_ptr = alloc_guest::<BlockDevice>(mem, &bdev, PERM_READ | PERM_WRITE)?;
    Ok(bdev_ptr)
}

//-------------------------------