use anyhow::Result;
use log::*;
use rand::prelude::*;
use rand::SeedableRng;

use crate::fixture::*;
use crate::memory::*;
use crate::stats::*;
use crate::stubs::block_device::*;
use crate::stubs::*;
use crate::test_runner::*;

//-------------------------------

fn test_nothing(fix: &mut Fixture) -> Result<()> {
    standard_globals(fix)?;
    Ok(())
}

//-------------------------------

pub fn register_tests(runner: &mut TestRunner) -> Result<()> {
    let kmodules = vec![THIN2_MOD];
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
            runner.register(&p, Test::new(kmodules.clone(), Box::new($func)));
        }};
    }

    test_section! {
        "/thinp2/",
        test!("nothing", test_nothing)
    }

    Ok(())
}

//-------------------------------
