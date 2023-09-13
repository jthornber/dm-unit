use crate::emulator::memory::*;
use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::wrappers::extent_allocator::*;

use anyhow::{ensure, Result};
use log::*;
use rand::Rng;
use roaring::RoaringBitmap;
use std::sync::{Arc, Mutex};

//-------------------------------

fn test_create(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let ea = extent_allocator_create(fix, 1024)?;
    extent_allocator_destroy(fix, ea)?;
    Ok(())
}

struct AllocationContext {
    context: Addr,
    blocks: Vec<u64>,
}

impl AllocationContext {
    fn new(context: Addr) -> Self {
        Self {
            context,
            blocks: Vec::new(),
        }
    }

    fn alloc(
        &mut self,
        fix: &mut Fixture,
        allocated: &Arc<Mutex<RoaringBitmap>>,
    ) -> Result<Option<u64>> {
        match alloc_context_alloc(fix, self.context, allocated) {
            Ok(Some(block)) => {
                self.blocks.push(block);
                Ok(Some(block))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(e),
        }
    }
}

fn build_runs(blocks: &[u64]) -> Vec<(u64, u64)> {
    let mut runs = Vec::new();

    if blocks.is_empty() {
        return runs;
    }

    let mut run_start = blocks[0];
    let mut run_end = blocks[0] + 1;
    for &b in blocks.iter().skip(1) {
        if b == run_end {
            run_end += 1;
        } else {
            runs.push((run_start, run_end));
            run_start = b;
            run_end = b + 1;
        }
    }
    runs.push((run_start, run_end));
    runs
}

fn do_allocation_test(
    fix: &mut Fixture,
    nr_contexts: usize,
    nr_blocks: usize,
    allocated: &Arc<Mutex<RoaringBitmap>>,
    nr_blocks_to_allocate: usize,
) -> Result<Vec<AllocationContext>> {
    let mut contexts = Vec::new();
    let ea = extent_allocator_create(fix, nr_blocks as u64)?;

    for _ in 0..nr_contexts {
        let context = alloc_context_get(fix, ea)?;
        contexts.push(AllocationContext::new(context));
    }

    for i in 0..nr_blocks_to_allocate {
        let context = &mut contexts[i % nr_contexts];
        context.alloc(fix, allocated)?;
    }

    for context in &contexts {
        alloc_context_put(fix, context.context)?;
    }

    extent_allocator_destroy(fix, ea)?;

    Ok(contexts)
}

fn test_single_leaf(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));
    let contexts = do_allocation_test(fix, 1, 1024, &allocated, 1024)?;
    for context in contexts {
        let runs = build_runs(&context.blocks);
        ensure!(runs.len() == 1);
        ensure!(runs[0] == (0, 1024));
    }
    Ok(())
}

fn prealloc_test(
    fix: &mut Fixture,
    allocated: &Arc<Mutex<RoaringBitmap>>,
    nr_blocks: usize,
    max_runs: usize,
) -> Result<()> {
    let nr_contexts = 16;
    let nr_blocks_to_allocate = nr_blocks / 2;

    standard_globals(fix)?;

    let nr_prealloc = allocated.lock().unwrap().len();
    let contexts = do_allocation_test(
        fix,
        nr_contexts,
        nr_blocks,
        allocated,
        nr_blocks_to_allocate,
    )?;
    let nr_allocated = allocated.lock().unwrap().len() - nr_prealloc;

    let mut total = 0;
    for (i, context) in contexts.iter().enumerate() {
        let runs = build_runs(&context.blocks);
        // debug!("runs {:?}, cnt = {}", runs, context.blocks.len());
        ensure!(runs.len() <= max_runs);

        let mut expected = nr_blocks_to_allocate / nr_contexts;
        if i < nr_blocks_to_allocate % nr_contexts {
            expected += 1;
        }
        ensure!(context.blocks.len() == expected);
        total += context.blocks.len();
    }

    ensure!(nr_allocated == nr_blocks_to_allocate as u64);
    ensure!(total == nr_blocks_to_allocate);

    Ok(())
}

fn test_no_preallocations(fix: &mut Fixture) -> Result<()> {
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));
    prealloc_test(fix, &allocated, 1024, 1)
}

fn test_prealloc_linear_start(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1024;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    {
        let mut allocated = allocated.lock().unwrap();
        for i in 0..(nr_blocks / 5) {
            allocated.insert(i as u32);
        }
    }

    prealloc_test(fix, &allocated, nr_blocks, 2)
}

fn test_prealloc_linear_middle(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1024;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    {
        let mut allocated = allocated.lock().unwrap();
        for i in (nr_blocks / 5)..(2 * nr_blocks / 5) {
            allocated.insert(i as u32);
        }
    }

    prealloc_test(fix, &allocated, nr_blocks, 2)
}

fn test_prealloc_linear_end(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1024;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    {
        let mut allocated = allocated.lock().unwrap();
        for i in (4 * nr_blocks / 5)..nr_blocks {
            allocated.insert(i as u32);
        }
    }

    prealloc_test(fix, &allocated, nr_blocks, 2)
}

fn test_prealloc_random(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1024;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    let mut rng = rand::thread_rng();
    {
        let mut allocated = allocated.lock().unwrap();
        for _ in 0..(nr_blocks / 5) {
            allocated.insert(rng.gen_range(0..nr_blocks) as u32);
        }
    }

    prealloc_test(fix, &allocated, nr_blocks, 16)
}

fn test_prealloc_many_contexts(fix: &mut Fixture) -> Result<()> {
    let nr_blocks = 1024 * 1024;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    prealloc_test(fix, &allocated, nr_blocks, 1024)
}

fn test_reset_no_holders(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_blocks = 1024;
    let nr_blocks_to_allocate = nr_blocks / 2;
    let nr_contexts = 16;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    let mut contexts = Vec::new();
    let ea = extent_allocator_create(fix, nr_blocks as u64)?;

    for _ in 0..16 {
        extent_allocator_reset(fix, ea)?;
    }

    for _ in 0..nr_contexts {
        let context = alloc_context_get(fix, ea)?;
        contexts.push(AllocationContext::new(context));
    }

    for i in 0..nr_blocks_to_allocate {
        let context = &mut contexts[(i % nr_contexts) as usize];
        context.alloc(fix, &allocated)?;
    }

    for context in &contexts {
        alloc_context_put(fix, context.context)?;
        ensure!(build_runs(&context.blocks).len() <= 2);
    }

    extent_allocator_destroy(fix, ea)?;

    Ok(())
}

fn allocate_all_blocks(
    fix: &mut Fixture,
    contexts: &mut [AllocationContext],
    allocated: &Arc<Mutex<RoaringBitmap>>,
) -> Result<()> {
    let mut i = 0;
    loop {
        let context = &mut contexts[i % contexts.len()];
        i += 1;

        match context.alloc(fix, allocated) {
            Ok(Some(_)) => {}
            Ok(None) => {
                debug!("all blocks allocated");
                break;
            }
            Err(e) => {
                debug!("error allocating block: {}", e);
                return Err(e);
            }
        }
    }
    Ok(())
}

fn test_reset_many_holders(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_blocks = 1024;
    let nr_contexts = 16;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    let mut rng = rand::thread_rng();
    {
        let mut allocated = allocated.lock().unwrap();
        for _ in 0..(nr_blocks / 5) {
            allocated.insert(rng.gen_range(0..nr_blocks) as u32);
        }
    }

    let mut contexts = Vec::new();
    let ea = extent_allocator_create(fix, nr_blocks as u64)?;

    for _ in 0..nr_contexts {
        let context = alloc_context_get(fix, ea)?;
        contexts.push(AllocationContext::new(context));
    }

    allocate_all_blocks(fix, &mut contexts, &allocated)?;

    {
        let allocated = allocated.lock().unwrap();
        for b in 0..nr_blocks {
            ensure!(allocated.contains(b as u32));
        }
    }

    // Reset allocator
    extent_allocator_reset(fix, ea)?;

    // Free off a bunch of blocks
    {
        let mut allocated = allocated.lock().unwrap();
        for _ in 0..(nr_blocks / 3) {
            allocated.remove(rng.gen_range(0..nr_blocks) as u32);
        }
    }

    allocate_all_blocks(fix, &mut contexts, &allocated)?;

    {
        let allocated = allocated.lock().unwrap();
        for b in 0..nr_blocks {
            ensure!(allocated.contains(b as u32));
        }
    }

    for context in &contexts {
        alloc_context_put(fix, context.context)?;

        // Note the runs will contain duplicate blocks due to freeing
        // off blocks in 'allocated' above.
        // let runs = build_runs(&context.blocks);
    }

    extent_allocator_destroy(fix, ea)?;
    Ok(())
}

fn test_shared_contexts(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let nr_blocks = 1024;
    let nr_contexts = 32;
    let allocated = Arc::new(Mutex::new(RoaringBitmap::new()));

    let mut rng = rand::thread_rng();
    {
        let mut allocated = allocated.lock().unwrap();
        for _ in 0..(nr_blocks / 5) {
            allocated.insert(rng.gen_range(0..nr_blocks) as u32);
        }
    }

    let mut contexts = Vec::new();
    let ea = extent_allocator_create(fix, nr_blocks as u64)?;

    for _ in 0..nr_contexts {
        let context = alloc_context_get(fix, ea)?;
        contexts.push(AllocationContext::new(context));
    }

    // Disable kmalloc so that we force sharing of contexts
    disable_kmalloc(fix)?;

    for _ in 0..nr_contexts {
        let context = alloc_context_get(fix, ea)?;
        contexts.push(AllocationContext::new(context));
    }

    allocate_all_blocks(fix, &mut contexts, &allocated)?;

    {
        let allocated = allocated.lock().unwrap();
        for b in 0..nr_blocks {
            ensure!(allocated.contains(b as u32));
        }
    }

    for context in &contexts {
        ensure!(context.blocks.len() > 0);
        alloc_context_put(fix, context.context)?;
    }

    extent_allocator_destroy(fix, ea)?;
    Ok(())
}

//-------------------------------

pub fn register_tests(tests: &mut TestSet) -> Result<()> {
    let kmodules = vec![PDATA_MOD];
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
            tests.register(&p, Test::new(kmodules.clone(), Box::new($func)));
        }};
    }

    test_section! {
        "/pdata/extent-allocator/",
        test!("create", test_create)
        test!("no-preallocations", test_no_preallocations)
        test!("single-leaf", test_single_leaf)
        test!("prealloc/linear-start", test_prealloc_linear_start)
        test!("prealloc/linear-middle", test_prealloc_linear_middle)
        test!("prealloc/linear-end", test_prealloc_linear_end)
        test!("prealloc/random", test_prealloc_random)
        test!("prealloc/many-contexts", test_prealloc_many_contexts)
        test!("reset/no-holders", test_reset_no_holders)
        test!("reset/many-holders", test_reset_many_holders)
        test!("shared-contexts", test_shared_contexts)
    };

    Ok(())
}
