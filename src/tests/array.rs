use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::array_metadata::ArrayMetadata;

use anyhow::{ensure, Result};
use rand::prelude::SliceRandom;
use rand::SeedableRng;

//-------------------------------

pub const MAX_U64_ENTRIES_PER_BLOCK: u32 = 509;

// Delete an empty array.
fn test_del_empty(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;
    md.delete()
}

//-------------------------------

// TODO: check array entries
// TODO: use random numbers for the value
fn test_resize_array(fix: &mut Fixture, old_size: u32, new_size: u32) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;

    if old_size > 0 {
        md.begin()?;
        md.resize(old_size, 0)?;
        md.commit()?;
    }

    md.begin()?;
    md.resize(new_size, 0)?;
    md.commit()?;

    Ok(())
}

fn test_expand_from_empty_within_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 0, 101)
}

fn test_expand_from_empty_to_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 0, MAX_U64_ENTRIES_PER_BLOCK)
}

fn test_expand_from_empty_across_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 0, MAX_U64_ENTRIES_PER_BLOCK + 101)
}

fn test_expand_from_empty_to_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 0, MAX_U64_ENTRIES_PER_BLOCK * 2)
}

fn test_expand_from_empty_across_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 0, MAX_U64_ENTRIES_PER_BLOCK * 2 + 101)
}

fn test_expand_from_non_empty_within_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 97, 101)
}

fn test_expand_from_non_empty_to_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 97, MAX_U64_ENTRIES_PER_BLOCK)
}

fn test_expand_from_non_empty_across_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 97, MAX_U64_ENTRIES_PER_BLOCK + 101)
}

fn test_expand_from_non_empty_to_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 97, MAX_U64_ENTRIES_PER_BLOCK * 2)
}

fn test_expand_from_non_empty_across_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(fix, 97, MAX_U64_ENTRIES_PER_BLOCK * 2 + 101)
}

fn test_expand_from_aligned_within_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(
        fix,
        MAX_U64_ENTRIES_PER_BLOCK,
        MAX_U64_ENTRIES_PER_BLOCK + 101,
    )
}

fn test_expand_from_aligned_to_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(
        fix,
        MAX_U64_ENTRIES_PER_BLOCK,
        MAX_U64_ENTRIES_PER_BLOCK * 2,
    )
}

fn test_expand_from_aligned_across_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(
        fix,
        MAX_U64_ENTRIES_PER_BLOCK,
        MAX_U64_ENTRIES_PER_BLOCK * 2 + 101,
    )
}

fn test_expand_from_aligned_to_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(
        fix,
        MAX_U64_ENTRIES_PER_BLOCK,
        MAX_U64_ENTRIES_PER_BLOCK * 3,
    )
}

fn test_expand_from_aligned_across_next_boundary(fix: &mut Fixture) -> Result<()> {
    test_resize_array(
        fix,
        MAX_U64_ENTRIES_PER_BLOCK,
        MAX_U64_ENTRIES_PER_BLOCK * 3 + 101,
    )
}

//-------------------------------

fn test_set_values(fix: &mut Fixture, values: &[(u32, u64)]) -> Result<()> {
    standard_globals(fix)?;

    let mut md = ArrayMetadata::new(fix)?;
    md.begin()?;

    let size = values.iter().map(|(i, _)| *i).max().map_or(0, |s| s + 1);
    md.resize(size, 0)?;

    values.iter().try_for_each(|(i, v)| md.set_value(*i, v))?;

    // TODO: check the rest of the entries are not affected
    values.iter().try_for_each(|(i, v)| {
        ensure!(md.get_value(*i)? == *v);
        Ok(())
    })?;

    Ok(())
}

fn test_set_values_forward(fix: &mut Fixture) -> Result<()> {
    let mut values: Vec<u64> = (0..1024u64).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    values.shuffle(&mut rng);
    let values: Vec<(u32, u64)> = values
        .into_iter()
        .enumerate()
        .map(|(i, v)| (i as u32, v))
        .collect();

    test_set_values(fix, &values)
}

fn test_set_values_backward(fix: &mut Fixture) -> Result<()> {
    let mut values: Vec<u64> = (0..1024u64).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    values.shuffle(&mut rng);
    let values: Vec<(u32, u64)> = values
        .into_iter()
        .enumerate()
        .rev()
        .map(|(i, v)| (i as u32, v))
        .collect();

    test_set_values(fix, &values)
}

fn test_set_values_random(fix: &mut Fixture) -> Result<()> {
    let mut values: Vec<u64> = (0..1024u64).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    values.shuffle(&mut rng);
    let mut values: Vec<(u32, u64)> = values
        .into_iter()
        .enumerate()
        .map(|(i, v)| (i as u32, v))
        .collect();
    values.shuffle(&mut rng);

    test_set_values(fix, &values)
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
        "/pdata/array/",
        test!("del/empty", test_del_empty)

        test_section! {
            "resize/grow/from_empty/",
            test!("within_block", test_expand_from_empty_within_boundary)
            test!("to_boundary", test_expand_from_empty_to_boundary)
            test!("across_boundary", test_expand_from_empty_across_boundary)
            test!("to_next_boundary", test_expand_from_empty_to_next_boundary)
            test!("across_next_boundary", test_expand_from_empty_across_next_boundary)
        }

        test_section! {
            "resize/grow/from_non_empty/",
            test!("within_block", test_expand_from_non_empty_within_boundary)
            test!("to_boundary", test_expand_from_non_empty_to_boundary)
            test!("across_boundary", test_expand_from_non_empty_across_boundary)
            test!("to_next_boundary", test_expand_from_non_empty_to_next_boundary)
            test!("across_next_boundary", test_expand_from_non_empty_across_next_boundary)
        }

        test_section! {
            "resize/grow/from_aligned/",
            test!("within_block", test_expand_from_aligned_within_boundary)
            test!("to_boundary", test_expand_from_aligned_to_boundary)
            test!("across_boundary", test_expand_from_aligned_across_boundary)
            test!("to_next_boundary", test_expand_from_aligned_to_next_boundary)
            test!("across_next_boundary", test_expand_from_aligned_across_next_boundary)
        }

        test_section! {
            "set_values/",
            test!("forward", test_set_values_forward)
            test!("backward", test_set_values_backward)
            test!("random", test_set_values_random)
        }
    };

    Ok(())
}

//-------------------------------
