use anyhow::Result;
use log::info;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use crate::tests::fixture::*;

//-------------------------------

pub type TestFn = Box<dyn FnMut(&mut Fixture) -> Result<()>>;

pub struct TestRunner {
    kernel_dir: PathBuf,
    tests: BTreeMap<String, TestFn>,
}

impl TestRunner {
    pub fn new<P: AsRef<Path>>(kernel_dir: P) -> Self {
        let mut path = PathBuf::new();
        path.push(kernel_dir);
        
        TestRunner {
            kernel_dir: path,
            tests: BTreeMap::new(),
        }
    }

    pub fn get_kernel_dir(&self) -> &Path {
        &self.kernel_dir
    }

    pub fn register_test(&mut self, path: &str, t: TestFn) {
        self.tests.insert(path.to_string(), t);
    }

    pub fn exec(&mut self)  -> Result<(usize, usize)> {
        let mut pass = 0;
        let mut fail = 0;

        for (p, t) in &mut self.tests{
            info!(">>> {}", p);
            let mut fix = Fixture::new(&self.kernel_dir)?;
            if let Err(e) = (*t)(&mut fix) {
                fail += 1;
                info!("<<< {}: FAIL, {}", p, e);
            } else {
                pass += 1;
                info!("<<< {}: PASS", p);
            }
        }
        
        Ok((pass, fail))
    }
}

//-------------------------------
