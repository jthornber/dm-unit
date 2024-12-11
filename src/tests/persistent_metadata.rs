use crate::block_manager::*;
use crate::emulator::memory::*;
use crate::fixture::*;
use crate::stubs::block_manager::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::transaction_manager::*;

use anyhow::{anyhow, Context, Result};
use std::sync::Arc;

pub struct PersistentMetadata<'a> {
    pub fix: &'a mut Fixture,
    pub bm: Addr,
    pub tm: Addr,
    pub sm: Addr,
    pub sb: Option<Addr>,
}

impl<'a> PersistentMetadata<'a> {
    pub fn new(fix: &'a mut Fixture) -> Result<Self> {
        let bm = dm_bm_create(fix, 1024)?;
        let (tm, sm) = dm_tm_create(fix, bm, 0)?;

        // increment the superblock within the sm
        sm_inc_block(fix, sm, 0, 1)?;

        Ok(PersistentMetadata {
            fix,
            bm,
            tm,
            sm,
            sb: None,
        })
    }

    pub fn begin(&mut self) -> Result<()> {
        if self.sb.is_some() {
            return Err(anyhow!("transaction already begun"));
        }

        // lock the superblock to prevent further accesses
        self.sb = Some(dm_bm_write_lock_zero(self.fix, self.bm, 0, Addr(0))?);
        Ok(())
    }

    pub fn commit(&mut self) -> Result<()> {
        dm_tm_pre_commit(self.fix, self.tm)?;
        dm_tm_commit(self.fix, self.tm, self.sb.unwrap())?;
        self.sb = None; // dm_tm_commit had unlocked the superblock implicitly
        Ok(())
    }

    pub fn get_bm(&self) -> Arc<BlockManager> {
        get_bm(self.fix, self.bm)
    }

    pub fn complete(self) -> Result<()> {
        if let Some(sb) = self.sb {
            dm_bm_unlock(self.fix, sb).context("unlock superblock")?;
        }
        dm_tm_destroy(self.fix, self.tm).context("destroy tm")?;
        sm_destroy(self.fix, self.sm).context("destroy sm")?;
        dm_bm_destroy(self.fix, self.bm).context("destroy bm")?;
        Ok(())
    }
}
