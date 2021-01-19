use anyhow::Result;
use log::info;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//-------------------------------

/// A test suite gathers a group of tests together that all
/// use the same fixture.  The tests all have paths associated
/// with them which are used in the user interface.  Test suites
/// are not visible to the user.

pub type TestPath = String;

pub trait TestSuite {
    fn get_paths(&self) -> Vec<TestPath>;
    fn exec(&self, p: &TestPath) -> Result<()>;
}

pub struct TestRunner {
    kernel_dir: PathBuf,
    suites: Vec<Box<dyn TestSuite>>,

    // Maps paths to the index of the test suite that
    // contains it.
    paths: BTreeMap<TestPath, usize>,
}

impl TestRunner {
    pub fn new<P: AsRef<Path>>(kernel_dir: P) -> Self {
        let mut path = PathBuf::new();
        path.push(kernel_dir);
        
        TestRunner {
            kernel_dir: path,
            suites: Vec::new(),
            paths: BTreeMap::new(),
        }
    }

    pub fn get_kernel_dir(&self) -> &Path {
        &self.kernel_dir
    }

    pub fn register_suite(&mut self, s: Box<dyn TestSuite>) {
        let paths = s.get_paths();
        let index = self.suites.len();
        for p in paths {
            self.paths.insert(p, index);
        }
        self.suites.push(s);
    }

    pub fn exec(&self)  -> (usize, usize) {
        let mut pass = 0;
        let mut fail = 0;

        for (p, sindex) in &self.paths {
            info!(">>> {}", p);
            let suite = &self.suites[*sindex];
            if let Err(e) = suite.exec(p) {
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
