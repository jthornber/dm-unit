use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::block_manager::*;
use crate::wrappers::space_map::*;
use crate::wrappers::transaction_manager::*;

use anyhow::Result;
use log::*;

//-------------------------------

fn stats_report(fix: &Fixture, baseline: &Stats, desc: &str, count: u64) {
    let delta = baseline.delta(fix);
    info!(
        "{}: instrs = {}, read_locks = {:.1}, write_locks = {:.1}",
        desc,
        delta.instrs / count,
        delta.read_locks as f64 / count as f64,
        delta.write_locks as f64 / count as f64
    );
}

fn test_commit_cost(fix: &mut Fixture) -> Result<()> {
    fix.trace_func("sm_metadata_new_block")?;
    fix.trace_func("sm_metadata_new_block_")?;

    standard_globals(fix)?;

    let count = 100000;
    let bm = dm_bm_create(fix, count + 100)?;
    let (tm, sm) = dm_tm_create(fix, bm, 0)?;
    let mut sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;

    let commit_interval = 100;

    let mut baseline = Stats::collect_stats(fix);
    let mut commit_count = commit_interval;
    for _ in 0..count {
        let _b = sm_new_block(fix, sm)?;

        if commit_count == 0 {
            info!("committing");
            stats_report(fix, &baseline, "new_block", commit_interval);
            dm_tm_pre_commit(fix, tm)?;
            dm_tm_commit(fix, tm, sb)?;
            sb = dm_bm_write_lock_zero(fix, bm, 0, Addr(0))?;
            commit_count = commit_interval;
            baseline = Stats::collect_stats(fix);
        } else {
            commit_count -= 1;
        }
    }
    stats_report(fix, &baseline, "new_block", count);

    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let mut prefix: Vec<&'static str> = Vec::new();

    macro_rules! test_section {
        ($path:expr, $($s:stmt)*) => {{
            prefix.push($path);
            $($s)*
            prefix.pop().unwrap();
        }}
    }

    macro_rules! test {
        ($path:expr, $func:expr) => {{
            prefix.push($path);
            let p = prefix.concat();
            prefix.pop().unwrap();
            runner.register(&p, Box::new($func));
        }};
    }

    test_section! {
        "/pdata/space-map/",
        test!("commit-cost", test_commit_cost)
    };

    Ok(())
}

//-------------------------------
