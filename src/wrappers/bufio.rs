use crate::decode::*;
use crate::fixture::*;
use crate::guest::*;
use crate::memory::*;

use anyhow::{ensure, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use log::*;
use std::io;
use std::io::{Read, Write};

use Reg::*;

//-------------------------------

pub fn dm_bufio_client_create(
    fix: &mut Fixture,
    bdev: Addr,
    block_size: usize,
    reserved_buffers: usize,
    aux_size: usize,
    alloc_callback: Addr,
    write_callback: Addr,
) -> Result<Addr> {
    fix.vm.set_reg(A0, bdev.0);
    fix.vm.set_reg(A1, block_size as u64);
    fix.vm.set_reg(A2, aux_size as u64);
    fix.vm.set_reg(A3, alloc_callback.0);
    fix.vm.set_reg(A4, write_callback.0);

    fix.call_with_err_ptr("dm_bufio_client_create")
}

pub fn dm_bufio_client_destroy(fix: &mut Fixture, c: Addr) -> Result<()> {
    fix.vm.set_reg(A0, c.0);
    fix.call("dm_bufio_client_destroy")
}

pub fn dm_bufio_set_sector_offset(fix: &mut Fixture, c: Addr, start: u64) -> Result<()> {
    fix.vm.set_reg(A0, c.0);
    fix.vm.set_reg(A1, start);
    fix.call("dm_bufio_set_sector_offset")
}

pub fn dm_bufio_read(fix: &mut Fixture, c: Addr, block: u64) -> Result<(Addr, Addr)> {
    let (mut fix, result_ptr) = auto_alloc(&mut *fix, 8)?;
    fix.vm.set_reg(A0, c.0);
    fix.vm.set_reg(A1, block);
    fix.vm.set_reg(A2, result_ptr.0);

    let data = fix.call_with_err_ptr("dm_bufio_read")?;
    Ok((
        data,
        Addr(fix.vm.mem.read_into::<u64>(result_ptr, PERM_READ)?),
    ))
}

/*


/*
 * Like dm_bufio_read, but return buffer from cache, don't read
 * it. If the buffer is not in the cache, return NULL.
 */
void *dm_bufio_get(struct dm_bufio_client *c, sector_t block,
           struct dm_buffer **bp);

/*
 * Like dm_bufio_read, but don't read anything from the disk.  It is
 * expected that the caller initializes the buffer and marks it dirty.
 */
void *dm_bufio_new(struct dm_bufio_client *c, sector_t block,
           struct dm_buffer **bp);

/*
 * Prefetch the specified blocks to the cache.
 * The function starts to read the blocks and returns without waiting for
 * I/O to finish.
 */
void dm_bufio_prefetch(struct dm_bufio_client *c,
               sector_t block, unsigned n_blocks);

/*
 * Release a reference obtained with dm_bufio_{read,get,new}. The data
 * pointer and dm_buffer pointer is no longer valid after this call.
 */
void dm_bufio_release(struct dm_buffer *b);

/*
 * Mark a buffer dirty. It should be called after the buffer is modified.
 *
 * In case of memory pressure, the buffer may be written after
 * dm_bufio_mark_buffer_dirty, but before dm_bufio_write_dirty_buffers.  So
 * dm_bufio_write_dirty_buffers guarantees that the buffer is on-disk but
 * the actual writing may occur earlier.
 */
void dm_bufio_mark_buffer_dirty(struct dm_buffer *b);

/*
 * Mark a part of the buffer dirty.
 *
 * The specified part of the buffer is scheduled to be written. dm-bufio may
 * write the specified part of the buffer or it may write a larger superset.
 */
void dm_bufio_mark_partial_buffer_dirty(struct dm_buffer *b,
                    unsigned start, unsigned end);

/*
 * Initiate writing of dirty buffers, without waiting for completion.
 */
void dm_bufio_write_dirty_buffers_async(struct dm_bufio_client *c);

/*
 * Write all dirty buffers. Guarantees that all dirty buffers created prior
 * to this call are on disk when this call exits.
 */
int dm_bufio_write_dirty_buffers(struct dm_bufio_client *c);

/*
 * Send an empty write barrier to the device to flush hardware disk cache.
 */
int dm_bufio_issue_flush(struct dm_bufio_client *c);

/*
 * Send a discard request to the underlying device.
 */
int dm_bufio_issue_discard(struct dm_bufio_client *c, sector_t block, sector_t count);

/*
 * Like dm_bufio_release but also move the buffer to the new
 * block. dm_bufio_write_dirty_buffers is needed to commit the new block.
 */
void dm_bufio_release_move(struct dm_buffer *b, sector_t new_block);

/*
 * Free the given buffer.
 * This is just a hint, if the buffer is in use or dirty, this function
 * does nothing.
 */
void dm_bufio_forget(struct dm_bufio_client *c, sector_t block);

/*
 * Free the given range of buffers.
 * This is just a hint, if the buffer is in use or dirty, this function
 * does nothing.
 */
void dm_bufio_forget_buffers(struct dm_bufio_client *c, sector_t block, sector_t n_blocks);

/*
 * Set the minimum number of buffers before cleanup happens.
 */
void dm_bufio_set_minimum_buffers(struct dm_bufio_client *c, unsigned n);

unsigned dm_bufio_get_block_size(struct dm_bufio_client *c);
sector_t dm_bufio_get_device_size(struct dm_bufio_client *c);
sector_t dm_bufio_get_block_number(struct dm_buffer *b);
void *dm_bufio_get_block_data(struct dm_buffer *b);
void *dm_bufio_get_aux_data(struct dm_buffer *b);
struct dm_bufio_client *dm_bufio_get_client(struct dm_buffer *b);
*/
//-------------------------------
