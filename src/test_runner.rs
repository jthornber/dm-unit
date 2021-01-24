use anyhow::Result;
use log::info;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//-------------------------------

pub trait Test {
    fn exec(&self, kdir: &PathBuf) -> Result<()>;
}

pub struct TestRunner {
    kernel_dir: PathBuf,
    tests: BTreeMap<String, Box<dyn Test>>,
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

    pub fn register_test(&mut self, path: &str, t: Box<dyn Test>) {
        self.tests.insert(path.to_string(), t);
    }

    pub fn exec(&self)  -> (usize, usize) {
        let mut pass = 0;
        let mut fail = 0;

        for (p, t) in &self.tests{
            info!(">>> {}", p);
            if let Err(e) = t.exec(&self.kernel_dir) {
                fail += 1;
                info!("<<< {}: FAIL, {}", p, e);
            } else {
                pass += 1;
                info!("<<< {}: PASS", p);
            }
        }
        
        (pass, fail)
    }
}

//-------------------------------
