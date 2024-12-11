use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::btree_metadata::BTreeMetadata;
use crate::wrappers::btree_cursor::*;

use anyhow::{anyhow, Result};
use rand::prelude::SliceRandom;
use rand::SeedableRng;

//-------------------------------

fn test_iterate_empty_btree(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;

    let mut md = BTreeMetadata::new(fix)?;
    let e = md.get_cursor().unwrap_err();

    if !matches!(e.downcast_ref::<CallError>(), Some(err) if err.is_errno(libc::ENODATA)) {
        return Err(e);
    }
    md.complete()
}

fn iterate_populated_btree(fix: &mut Fixture, nr_entries: usize) -> Result<()> {
    standard_globals(fix)?;

    let mut md = BTreeMetadata::new(fix)?;

    let mut values: Vec<u64> = (0..nr_entries as u64).collect();
    let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(1);
    values.shuffle(&mut rng);
    for (k, v) in values.iter().enumerate() {
        md.insert(k as u64, v)?;
    }

    let mut cursor = md.get_cursor()?;
    let mut last_err = None;
    for (k, v) in values.iter().enumerate() {
        match dm_btree_cursor_get_value(md.fixture_mut(), &cursor) {
            Ok((k2, v2)) => {
                if k as u64 != k2 || *v != v2 {
                    last_err = Some(anyhow!(
                        "unexpectd key-value pair ({} {}), expected ({} {})",
                        k2,
                        v2,
                        k,
                        v
                    ));
                    break;
                }
            }
            Err(e) => {
                last_err = Some(e);
                break;
            }
        }

        if k == nr_entries - 1 {
            break;
        }

        if let Err(e) = dm_btree_cursor_next(md.fixture_mut(), &mut cursor) {
            last_err = Some(e);
            break;
        }
    }

    dm_btree_cursor_end(md.fixture_mut(), &mut cursor)?;
    free_btree_cursor(md.fixture_mut(), cursor)?;

    if let Some(e) = last_err {
        return Err(e);
    }
    md.complete()
}

fn test_iterate_populated_btree(fix: &mut Fixture) -> Result<()> {
    iterate_populated_btree(fix, 1024)
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
        "/pdata/btree_cursor/",
        test!("iterate/empty", test_iterate_empty_btree)
        test!("iterate/populated", test_iterate_populated_btree)
    };

    Ok(())
}

//-------------------------------
