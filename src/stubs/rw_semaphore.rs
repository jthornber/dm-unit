use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io;
use std::io::{Read, Write};

use crate::decode::*;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;

use Reg::*;

//-------------------------------

/*
struct rw_semaphore {
    atomic_long_t              count;                /*     0     8 */
    atomic_long_t              owner;                /*     8     8 */
    struct optimistic_spin_queue osq;                /*    16     4 */

    /* XXX 4 bytes hole, try to pack */

    raw_spinlock_t             wait_lock;            /*    24    24 */
    struct list_head           wait_list;            /*    48    16 */
    /* --- cacheline 1 boundary (64 bytes) --- */
    void *                     magic;                /*    64     8 */

    /* size: 72, cachelines: 2, members: 6 */
    /* sum members: 68, holes: 1, sum holes: 4 */
    /* last cacheline: 8 bytes */
};
*/

#[allow(dead_code)]
pub struct RWSem {
    count: u64,
}

impl Guest for RWSem {
    fn guest_len() -> usize {
        72
    }

    fn pack<W: Write>(&self, w: &mut W, _ptr: Addr) -> io::Result<()> {
        w.write_u64::<LittleEndian>(self.count)?;
        w.write_all(&[0u8; 72 - 8])?;
        Ok(())
    }

    fn unpack<R: Read>(r: &mut R, _ptr: Addr) -> io::Result<Self> {
        let count = r.read_u64::<LittleEndian>()?;
        Ok(RWSem { count })
    }
}

fn init_rwsem(fix: &mut Fixture) -> Result<()> {
    let sem = RWSem { count: 0 };
    let ptr = Addr(fix.vm.reg(A0));
    write_guest::<RWSem>(&mut fix.vm.mem, ptr, &sem)?;
    fix.vm.ret(0);
    Ok(())
}

fn mut_count<F>(mem: &mut Memory, ptr: Addr, func: F) -> Result<()>
where
    F: FnOnce(u64) -> Result<u64>,
{
    let count = mem.read_into::<u64>(ptr, PERM_READ)?;
    let count = func(count)?;
    mem.write_out::<u64>(count, ptr, PERM_WRITE)?;
    Ok(())
}

fn down_read(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(A0));
    mut_count(&mut fix.vm.mem, ptr, |mut count| {
        if count == 1 {
            return Err(anyhow!("down_read called when write locked"));
        } else {
            count >>= 8;
            count += 1;
            count <<= 8;
        }
        Ok(count)
    })?;

    fix.vm.ret(0);
    Ok(())
}

fn up_read(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(A0));
    mut_count(&mut fix.vm.mem, ptr, |mut count| {
        if count == 1 {
            return Err(anyhow!("up_read called when write locked"));
        } else {
            count >>= 8;
            if count == 0 {
                return Err(anyhow!("up_read called when not locked"));
            }

            count -= 1;
            count <<= 8;
        }
        Ok(count)
    })?;

    fix.vm.ret(0);
    Ok(())
}

fn down_write(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(A0));
    mut_count(&mut fix.vm.mem, ptr, |count| {
        if count != 0 {
            return Err(anyhow!("down_write called when already locked"));
        }

        Ok(1)
    })?;
    
    fix.vm.ret(0);
    Ok(())
}

fn up_write(fix: &mut Fixture) -> Result<()> {
    let ptr = Addr(fix.vm.reg(A0));
    mut_count(&mut fix.vm.mem, ptr, |count| {
        if count != 1 {
            return Err(anyhow!("up_write called when not locked"));
        }

        Ok(0)
    })?;

    fix.vm.ret(0);
    Ok(())
}

//-------------------------------

pub fn rw_sem_stubs(fix: &mut Fixture) -> Result<()> {
    let _ = fix.at_func("__init_rwsem", Box::new(init_rwsem));
    let _ = fix.at_func("down_read", Box::new(down_read));
    let _ = fix.at_func("up_read", Box::new(up_read));
    let _ = fix.at_func("down_write", Box::new(down_write));
    let _ = fix.at_func("up_write", Box::new(up_write));
    Ok(())
}

//-------------------------------
