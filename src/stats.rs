use anyhow::Result;
use std::fs::File;
use std::io::prelude::*;

use crate::block_manager::*;
use crate::fixture::*;

//-------------------------------

#[derive(Default)]
pub struct Stats {
    pub instrs: u64,
    pub read_locks: u64,
    pub write_locks: u64,
    pub disk_reads: u64,
}

impl Stats {
    pub fn collect_stats(fix: &Fixture, bm: &BlockManager) -> Self {
        Stats {
            instrs: fix.vm.stats.instrs,
            read_locks: bm.get_nr_read_locks(),
            write_locks: bm.get_nr_write_locks(),
            disk_reads: bm.get_nr_disk_reads(),
        }
    }

    pub fn delta(&self, fix: &Fixture, bm: &BlockManager) -> Self {
        let rhs = Stats::collect_stats(fix, bm);
        Stats {
            instrs: rhs.instrs - self.instrs,
            read_locks: rhs.read_locks - self.read_locks,
            write_locks: rhs.write_locks - self.write_locks,
            disk_reads: rhs.disk_reads - self.disk_reads,
        }
    }
}

//-------------------------------

pub struct CostTracker {
    csv_out: File,
    iteration: u64,
    baseline: Stats,
}

impl CostTracker {
    pub fn new(path: &str) -> Result<Self> {
        // FIXME: support overwrite
        let mut csv_out = File::create(path)?;
        csv_out.write_all(b"iteration, instructions, read_locks, write_locks, disk_reads\n")?;

        Ok(CostTracker {
            csv_out,
            iteration: 0,
            baseline: Stats::default(),
        })
    }

    pub fn begin(&mut self, fix: &mut Fixture, bm: &BlockManager) {
        self.baseline = Stats::collect_stats(fix, bm);
    }

    pub fn end(&mut self, fix: &mut Fixture, bm: &BlockManager) -> Result<()> {
        self.end_in_iterations(fix, bm, 1)
    }

    pub fn end_in_iterations(
        &mut self,
        fix: &mut Fixture,
        bm: &BlockManager,
        iters: u64,
    ) -> Result<()> {
        self.iteration += iters;
        let delta = Stats::delta(&self.baseline, fix, bm);
        writeln!(
            self.csv_out,
            "{}, {}, {:.1}, {:.1}, {:.1}",
            self.iteration,
            delta.instrs / iters,
            delta.read_locks as f64 / iters as f64,
            delta.write_locks as f64 / iters as f64,
            delta.disk_reads as f64 / iters as f64
        )?;
        Ok(())
    }
}

//-------------------------------
