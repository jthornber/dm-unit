use crate::block_manager::*;
use crate::fixture::*;
use crate::tests::persistent_metadata::PersistentMetadata;
use crate::wrappers::btree::*;

use anyhow::Result;
use std::sync::Arc;

//-------------------------------

pub struct BTreeMetadata<'a> {
    md: PersistentMetadata<'a>,
    info: BTreeInfoPtr<u64>,
    root: u64,
}

impl<'a> BTreeMetadata<'a> {
    pub fn new(fix: &'a mut Fixture) -> Result<Self> {
        let md = PersistentMetadata::new(fix)?;

        let vtype = BTreeValueType::<u64>::default();
        let info = alloc_btree_info(md.fix, md.tm, 1, vtype)?;
        let root = dm_btree_empty(md.fix, &info)?;

        Ok(BTreeMetadata { md, info, root })
    }

    pub fn begin(&mut self) -> Result<()> {
        self.md.begin()
    }

    pub fn commit(&mut self) -> Result<()> {
        self.md.commit()
    }

    pub fn get_bm(&self) -> Arc<BlockManager> {
        self.md.get_bm()
    }

    pub fn root(&self) -> u64 {
        self.root
    }

    pub fn fixture(&self) -> &Fixture {
        self.md.fix
    }

    pub fn fixture_mut(&mut self) -> &mut Fixture {
        self.md.fix
    }

    // This function takes ownership as the btree is no longer valid
    pub fn delete(mut self) -> Result<()> {
        dm_btree_del(self.md.fix, &self.info, self.root)?;
        self.commit()
    }

    pub fn insert(&mut self, key: u64, value: &u64) -> Result<()> {
        let ks = vec![key];
        self.root = dm_btree_insert(self.md.fix, &self.info, self.root, &ks, value)?;
        Ok(())
    }

    pub fn lookup(&mut self, key: u64) -> Result<u64> {
        let keys = vec![key];
        dm_btree_lookup(self.md.fix, &self.info, self.root, &keys)
    }

    pub fn remove(&mut self, key: u64) -> Result<()> {
        let keys = vec![key];
        self.root = dm_btree_remove(self.md.fix, &self.info, self.root, &keys)?;
        Ok(())
    }
}

impl Drop for BTreeMetadata<'_> {
    fn drop(&mut self) {
        free_btree_info(self.md.fix, &mut self.info).expect("release dm_btree_info");
    }
}

//-------------------------------
