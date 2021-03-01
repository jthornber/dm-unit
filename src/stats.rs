use crate::fixture::*;
use crate::stubs::block_manager::*;

//-------------------------------

pub struct Stats {
    pub instrs: u64,
    pub read_locks: u64,
    pub write_locks: u64,
}

impl Stats {
    pub fn collect_stats(fix: &Fixture) -> Self {
        let bm = get_bm().unwrap();
        Stats {
            instrs: fix.vm.stats.instrs,
            read_locks: bm.nr_read_locks,
            write_locks: bm.nr_write_locks,
        }
    }

    pub fn delta(&self, fix: &Fixture) -> Self {
        let rhs = Stats::collect_stats(fix);
        Stats {
            instrs: rhs.instrs - self.instrs,
            read_locks: rhs.read_locks - self.read_locks,
            write_locks: rhs.write_locks - self.write_locks,
        }
    }
}

//-------------------------------
