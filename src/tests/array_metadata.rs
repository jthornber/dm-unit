use crate::block_manager::*;
use crate::fixture::*;
use crate::tests::persistent_metadata::PersistentMetadata;
use crate::wrappers::array::*;
use crate::wrappers::btree::BTreeValueType;

use anyhow::Result;
use std::sync::Arc;

pub struct ArrayMetadata<'a> {
    md: PersistentMetadata<'a>,
    info: ArrayInfo<u64>,
    root: u64,
    array_size: u32,
}

impl<'a> ArrayMetadata<'a> {
    pub fn new(fix: &'a mut Fixture) -> Result<Self> {
        let md = PersistentMetadata::new(fix)?;

        let vtype = BTreeValueType::<u64>::default(); // contained type for the array
        let info = init_array_info(md.fix, md.tm, &vtype)?;
        let root = dm_array_empty(md.fix, &info)?;

        Ok(ArrayMetadata {
            md,
            info,
            root,
            array_size: 0,
        })
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

    // This function takes ownership as the array is no longer valid
    pub fn delete(mut self) -> Result<()> {
        dm_array_del(self.md.fix, &self.info, self.root)?;
        self.commit()
    }

    pub fn set_value(&mut self, index: u32, value: &u64) -> Result<()> {
        self.root = dm_array_set_value(self.md.fix, &self.info, self.root, index, value)?;
        Ok(())
    }

    pub fn get_value(&mut self, index: u32) -> Result<u64> {
        dm_array_get_value(self.md.fix, &self.info, self.root, index)
    }

    pub fn resize(&mut self, new_size: u32, value: u64) -> Result<()> {
        self.root = dm_array_resize(
            self.md.fix,
            &self.info,
            self.root,
            self.array_size,
            new_size,
            &value,
        )?;
        self.array_size = new_size;
        Ok(())
    }
}

impl Drop for ArrayMetadata<'_> {
    fn drop(&mut self) {
        free_array_info(self.md.fix, &mut self.info).expect("free dm_array_info");
    }
}
