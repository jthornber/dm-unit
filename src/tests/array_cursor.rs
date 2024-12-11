use crate::emulator::memory::Addr;
use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::array::MAX_U64_ENTRIES_PER_BLOCK;
use crate::tests::array_metadata::ArrayMetadata;
use crate::wrappers::array_cursor::*;

use anyhow::{anyhow, ensure, Result};
use rand::prelude::SliceRandom;
use rand::SeedableRng;
use thinp::pdata::btree_walker::btree_to_value_vec;

//-------------------------------

fn test_iterate_empty_array(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;
    let e = md.get_cursor().unwrap_err();

    // dm_array_cursor_begin() should fail on an empty array.
    // Avoid using the ensure!() macro to compare the error type, as it prevents
    // the original error from being returned directly.
    let errno = e.downcast_ref::<CallError>().and_then(|err| err.errno());
    if errno != Some(libc::ENODATA) {
        return Err(e);
    }

    md.complete()?;

    Ok(())
}

fn iterate_populated_array(fix: &mut Fixture, nr_entries: usize) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;
    md.resize(nr_entries as u32, 0)?;

    let mut values: Vec<u64> = (0..nr_entries as u64).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    values.shuffle(&mut rng);
    values
        .iter()
        .enumerate()
        .try_for_each(|(i, v)| md.set_value(i as u32, v))?;

    let mut c = md.get_cursor()?;
    let mut last_err = None;
    for (i, v) in values.iter().enumerate() {
        match dm_array_cursor_get_value(md.fixture_mut(), &c) {
            Ok(v2) => {
                if *v != v2 {
                    last_err = Some(anyhow!("unexpectd value {}, expected {}", v2, v));
                    break;
                }
            }
            Err(e) => {
                last_err = Some(e);
                break;
            }
        }

        if i < nr_entries - 1 {
            if let Err(e) = dm_array_cursor_next(md.fixture_mut(), &mut c) {
                last_err = Some(e);
                break;
            }
        }
    }

    dm_array_cursor_end(md.fixture_mut(), &mut c)?;
    free_array_cursor(md.fixture_mut(), c)?;

    if let Some(e) = last_err {
        return Err(e);
    }
    md.complete()?;

    Ok(())
}

fn test_iterate_populated_array(fix: &mut Fixture) -> Result<()> {
    iterate_populated_array(fix, 1024)
}

fn test_damaged_array_blocks(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;
    md.resize(1024, 0)?;
    md.commit()?;

    // trash the first array block and remove its validator
    let bm = md.get_bm();
    let ablocks = btree_to_value_vec(&mut vec![], bm.clone(), false, md.root())?;
    let lock = bm.write_lock_zero(md.fixture_mut(), ablocks[0], Addr(0))?;
    bm.unlock(md.fixture_mut(), lock)?;
    drop(bm);

    md.begin()?;

    // dm_array_cursor_begin() should fail due to unexpected block type
    let e = md.get_cursor().unwrap_err();

    // The BlockManager stub is expected to return EINVAL on validator mismatch,
    // like the dm_bm_validate_buffer() does.
    // Avoid using the ensure!() macro to compare the error type, as it prevents
    // the original error from being returned directly.
    let errno = e.downcast_ref::<CallError>().and_then(|err| err.errno());
    if errno != Some(libc::EINVAL) {
        return Err(e);
    }
    md.complete()?;

    Ok(())
}

fn test_cursor_skip(fix: &mut Fixture, counts: &[u32]) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;
    md.resize(1024, 0)?;
    (0..1024).try_for_each(|i| md.set_value(i, &(i as u64)))?;
    md.commit()?;
    md.begin()?;

    let mut c = md.get_cursor()?;
    let mut ret = Ok(());
    let mut expected = 0;
    for cnt in counts {
        dm_array_cursor_skip(md.fixture_mut(), &mut c, *cnt)?;
        let v = dm_array_cursor_get_value(md.fixture_mut(), &c)?;
        expected += *cnt;
        if v != expected as u64 {
            ret = Err(anyhow!(
                "value mismatch: expected {}, actual {}",
                expected,
                v
            ));
            break;
        }
    }
    dm_array_cursor_end(md.fixture_mut(), &mut c)?;
    free_array_cursor(md.fixture_mut(), c)?;
    md.complete()?;

    ret
}

fn test_cursor_skip_pass_the_end(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;
    md.resize(1024, 0)?;
    (0..1024).try_for_each(|i| md.set_value(i, &(i as u64)))?;
    md.commit()?;
    md.begin()?;

    let mut c = md.get_cursor()?;
    let r = dm_array_cursor_skip(md.fixture_mut(), &mut c, 1024);
    ensure!(r.is_err());
    let e = r.unwrap_err();

    // dm_array_cursor_skip() should fail if there's no more data
    let errno = e.downcast_ref::<CallError>().and_then(|err| err.errno());

    dm_array_cursor_end(md.fixture_mut(), &mut c)?;
    free_array_cursor(md.fixture_mut(), c)?;

    if errno != Some(libc::ENODATA) {
        return Err(e);
    }
    md.complete()?;

    Ok(())
}

fn test_skip_from_zero_to_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[MAX_U64_ENTRIES_PER_BLOCK - 1])
}

fn test_skip_from_zero_across_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[MAX_U64_ENTRIES_PER_BLOCK])
}

fn test_skip_from_zero_to_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[MAX_U64_ENTRIES_PER_BLOCK * 2 - 1])
}

fn test_skip_from_zero_across_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[MAX_U64_ENTRIES_PER_BLOCK * 2])
}

fn test_skip_from_non_zero_to_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[10, MAX_U64_ENTRIES_PER_BLOCK - 11])
}

fn test_skip_from_non_zero_across_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[10, MAX_U64_ENTRIES_PER_BLOCK - 10])
}

fn test_skip_from_non_zero_to_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[10, MAX_U64_ENTRIES_PER_BLOCK * 2 - 11])
}

fn test_skip_from_non_zero_across_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[10, MAX_U64_ENTRIES_PER_BLOCK * 2 - 10])
}

fn test_skip_from_aligned_across_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(fix, &[MAX_U64_ENTRIES_PER_BLOCK - 1, 1])
}

fn test_skip_from_aligned_to_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(
        fix,
        &[MAX_U64_ENTRIES_PER_BLOCK - 1, MAX_U64_ENTRIES_PER_BLOCK],
    )
}

fn test_skip_from_aligned_across_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_cursor_skip(
        fix,
        &[MAX_U64_ENTRIES_PER_BLOCK - 1, MAX_U64_ENTRIES_PER_BLOCK + 1],
    )
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
        "/pdata/array_cursor/",

        test_section! {
            "iterate/",
            test!("empty", test_iterate_empty_array)
            test!("populated", test_iterate_populated_array)
        }

        test!("skip/pass_the_end", test_cursor_skip_pass_the_end)

        test_section! {
            "skip/from_zero/",
            test!("to_boundary", test_skip_from_zero_to_boundary)
            test!("across_boundary", test_skip_from_zero_across_boundary)
            test!("to_next_boundary", test_skip_from_zero_to_next_boundary)
            test!("across_next_boundary", test_skip_from_zero_across_next_boundary)
        }

        test_section! {
            "skip/from_non_zero/",
            test!("to_boundary", test_skip_from_non_zero_to_boundary)
            test!("across_boundary", test_skip_from_non_zero_across_boundary)
            test!("to_next_boundary", test_skip_from_non_zero_to_next_boundary)
            test!("across_next_boundary", test_skip_from_non_zero_across_next_boundary)
        }

        test_section! {
            "skip/from_aligned/",
            test!("across_boundary", test_skip_from_aligned_across_boundary)
            test!("to_next_boundary", test_skip_from_aligned_to_next_boundary)
            test!("across_next_boundary", test_skip_from_aligned_across_next_boundary)
        }

        test_section! {
            "damaged/",
            test!("array_blocks", test_damaged_array_blocks)
        }
    };

    Ok(())
}

//-------------------------------
