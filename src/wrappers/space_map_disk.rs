use crate::emulator::decode::*;
use crate::fixture::*;
use crate::emulator::memory::*;

use anyhow::{anyhow, Result};

use Reg::*;

//-------------------------------

pub fn dm_sm_disk_create(fix: &mut Fixture, tm: Addr, nr_blocks: u64) -> Result<Addr> {
    fix.vm.set_reg(A0, tm.0);
    fix.vm.set_reg(A1, nr_blocks);
    fix.call("dm_sm_disk_create")?;
    let ret = fix.vm.reg(A0);
    if ret == 0 {
        return Err(anyhow!(""));
    }
    Ok(Addr(ret))
}

//-------------------------------
