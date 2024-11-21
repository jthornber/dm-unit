use crate::fixture::*;
use crate::stubs::*;
use crate::test_runner::*;
use crate::tests::array_metadata::ArrayMetadata;
use crate::wrappers::array_cursor::*;

use anyhow::{anyhow, Result};
use rand::prelude::SliceRandom;
use rand::SeedableRng;

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

    Ok(())
}

fn test_iterate_populated_array(fix: &mut Fixture) -> Result<()> {
    iterate_populated_array(fix, 1024)
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
    };

    Ok(())
}

//-------------------------------
