Tests are kept in _src/tests_.  Each test module has a `register_tests()`
function; you can copy and paste this function into your test code,
changing the test paths and test functions approriately.

Reading the existing test suites is the best way to learn how to write
tests.  I'll give a couple of short examples here.

## test_redistribute_2

The redistribute2 function in dm-btree.c takes a pair of btree node and
redistributes the entries to make them have similar amounts in each.

The test goes through the following steps:

1. Setup standard stubs such as kmalloc, mutex_lock etc.
2. Create two nodes in the guest with the specified nr of entries.
3. call redistribute2 in the guest
4. retrieve the nodes from the guest
5. check they are well formed and have the expected nr of entries

``` Rust
fn test_redistribute_2(fix: &mut Fixture, nr_left: usize, nr_right: usize) -> Result<()> {
    standard_globals(fix)?;

    let total = nr_left + nr_right;
    let target_left = total / 2;
    let target_right = total - target_left;

    let (mut fix, left_ptr) = mk_node(fix, 0u64, nr_left)?;
    let (mut fix, right_ptr) = mk_node(&mut *fix, nr_left as u64, nr_right)?;
    redistribute2(&mut *fix, left_ptr, right_ptr)?;

    let left = get_node::<Value64>(&mut *fix, left_ptr, true)?;
    let right = get_node::<Value64>(&mut *fix, right_ptr, true)?;
    check_node(&left, 0u64, target_left)?;
    check_node(&right, target_left as u64, target_right)?;

    Ok(())
}

fn test_redistribute2_balanced(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 50, 50)
}

fn test_redistribute2_right_only(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 0, 100)
}

fn test_redistribute2_left_below_target(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 25, 75)
}

fn test_redistribute2_left_only(fix: &mut Fixture) -> Result<()> {
    test_redistribute_2(fix, 100, 0)
}
```


## btree insertion tests

A longer test.  This:
1. Sets up standard stubs.
2. Create a new btree within the guest
3. inserts many keys, committing regularly
4. when it commits it also reports some useful statistics such as
   instruction counts, buffer locks, average residency of btree.
5. Use the guest to look up all the keys to check they really were inserted.
6. Run a check of the whole btree.

Recording metrics is very easy with the approach, because any Rust code
you run has no effect on the vm (eg, instruction counts).  I typically
write csv files from my longer running tests and analyse in an app such
as Mathematica.  When first running this dm_btree_insert() test it became
apparent that occasionally insert would take hugely more instructions
and buffer locks.  This would not have been obvious if we'd just been
recording wall clock time, or average execution time.

``` Rust 
fn do_insert_test_(
    fix: &mut Fixture,
    keys: &[u64],
    pass_count: usize,
    target_residency: usize,
) -> Result<()> {
    standard_globals(fix)?;
    let mut bt = BTreeTest::new(fix)?;
    let commit_interval = 100;

    // First pass inserts, subsequent passes overwrite
    let mut commit_counter = commit_interval;
    for pass in 0..pass_count {
        bt.stats_start();
        bt.begin()?;
        for k in keys {
            bt.insert(*k)?;

            if commit_counter == 0 {
                bt.commit()?;
                bt.begin()?;
                commit_counter = commit_interval;
            }
            commit_counter -= 1;
        }
        bt.commit()?;

        let residency = bt.residency()?;
        if residency < target_residency {
            return Err(anyhow!("Residency is too low ({}%)", residency));
        }

        let desc = if pass == 0 { "insert" } else { "overwrite" };
        bt.stats_report(desc, keys.len() as u64)?;
    }

    // Lookup
    bt.begin()?;
    bt.stats_start();
    for k in keys {
        bt.lookup(*k)?;
    }
    bt.stats_report("lookup", keys.len() as u64)?;
    bt.commit()?;

    bt.check_keys_present(&keys)?;

    Ok(())
}

const KEY_COUNT: u64 = 10240;

fn test_insert_ascending(fix: &mut Fixture) -> Result<()> {
    let keys: Vec<u64> = (0..KEY_COUNT).collect();
    do_insert_test_(fix, &keys, 2, 75)
}

fn test_insert_descending(fix: &mut Fixture) -> Result<()> {
    let keys: Vec<u64> = (0..KEY_COUNT).rev().collect();
    do_insert_test_(fix, &keys, 2, 49)
}
```