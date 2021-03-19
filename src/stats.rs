use anyhow::Result;
use std::fs::File;
use std::io::prelude::*;
use log::*;

use crate::fixture::*;
use crate::stubs::block_manager::*;

//-------------------------------

pub struct Stats {
    pub instrs: u64,
    pub read_locks: u64,
    pub write_locks: u64,
}

impl Default for Stats {
    fn default() -> Self {
        Stats {
            instrs: 0,
            read_locks: 0,
            write_locks: 0,
        }
    }
}

impl Stats {
    pub fn collect_stats(fix: &Fixture) -> Self {
        let bm = get_bm().unwrap();
        Stats {
            instrs: fix.vm.stats.instrs,
            read_locks: bm.get_nr_read_locks(),
            write_locks: bm.get_nr_write_locks(),
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

pub struct CostTracker {
    csv_out: File,
    iteration: u32,
    baseline: Stats,
}

impl CostTracker {
    pub fn new(path: &str) -> Result<Self> {
        // FIXME: support overwrite
        let mut csv_out = File::create(path)?;
        csv_out.write_all(b"iteration, instructions, read locks, write locks\n")?;

        Ok(CostTracker {
            csv_out,
            iteration: 0,
            baseline: Stats::default(),
        })
    }

    pub fn begin(&mut self, fix: &mut Fixture) {
        self.baseline = Stats::collect_stats(fix);
        self.iteration += 1;
    }

    pub fn end(&mut self, fix: &mut Fixture) -> Result<()> {
        let delta = Stats::delta(&self.baseline, fix);
        if delta.write_locks > 200 {
            info!("iteration {} has gone crazy", self.iteration);
        }

        write!(self.csv_out, "{}, {}, {}, {}\n", self.iteration, delta.instrs, delta.read_locks, delta.write_locks)?;
        Ok(())
    }
}

//-------------------------------
