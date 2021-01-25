use crate::tests::fixture::*;
use anyhow::Result;
use log::info;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//-------------------------------

pub struct TestRunner {
    kernel_dir: PathBuf,
    tests: BTreeMap<String, TestFn>,
}

fn path_components(path: &String) -> Vec<String> {
    path.trim_start_matches('/')
        .split('/')
        .map(|s| s.to_string())
        .collect()
}

struct PathFormatter {
    last_path: Vec<String>,
}

impl PathFormatter {
    fn new() -> Self {
        PathFormatter {
            last_path: Vec::new(),
        }
    }

    fn indent(&self, count: usize) {
        let mut space = String::new();
        for _ in 0..count {
            space.push_str("  ");
        }
        print!("{}", space);
    }

    fn dots(&self, count: usize) {
        let mut space = String::new();
        for _ in 0..count {
            space.push_str(".");
        }
        print!("{}", space);
    }

    fn print(&mut self, components: &Vec<String>) {
        let mut last_path = Vec::new();
        let mut common = true;
        let mut width = 0;
        for (index, c) in components.iter().enumerate() {
            let last = self.last_path.get(index);
            if last.is_none() || last.unwrap() != c {
                common = false;
            }

            if !common {
                self.indent(index);
                if index == components.len() - 1 {
                    print!("{} ", c);
                } else {
                    println!("{} ", c);
                }
            }

            last_path.push(c.clone());
            width = (index * 2) + c.len();
        }
        self.dots(60 - width);

        // Inefficient, but I don't think it will be significant.
        self.last_path = last_path;
    }
}

//-------------------------------

pub type TestFn = Box<dyn FnMut(&mut Fixture) -> Result<()>>;

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

    pub fn register(&mut self, path: &str, t: TestFn) {
        self.tests.insert(path.to_string(), t);
    }

    pub fn exec(&mut self) -> Result<(usize, usize)> {
        let mut pass = 0;
        let mut fail = 0;
        let mut formatter = PathFormatter::new();

        for (p, t) in &mut self.tests {
            info!(">>> {}", p);
            let components = path_components(p);
            formatter.print(&components);

            let mut fix = Fixture::new(&self.kernel_dir)?;
            if let Err(e) = (*t)(&mut fix) {
                fail += 1;
                println!(" FAIL");
                info!("<<< {}: FAIL, {}", p, e);
            } else {
                pass += 1;
                println!(" PASS");
                info!("<<< {}: PASS", p);
            }
        }

        Ok((pass, fail))
    }
}

//-------------------------------
