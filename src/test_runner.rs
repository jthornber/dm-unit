use crate::fixture::*;
use anyhow::Result;
use log::{debug, info};
use regex::Regex;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

//-------------------------------

fn path_components(path: &str) -> Vec<String> {
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
            space.push('.');
        }
        print!("{}", space);
    }

    fn print(&mut self, components: &[String]) {
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

#[allow(dead_code)]
pub struct TestRunner<'a> {
    kernel_dir: PathBuf,
    filter_fn: Box<dyn Fn(&str) -> bool + 'a>,
    tests: BTreeMap<String, TestFn>,
    gdb: bool,
}

pub type TestFn = Box<dyn Fn(&mut Fixture) -> Result<()>>;

impl<'a> TestRunner<'a> {
    pub fn new<P: AsRef<Path>>(kernel_dir: P) -> Self {
        let mut path = PathBuf::new();
        path.push(kernel_dir);

        let filter_fn = Box::new(move |_: &str| true);

        TestRunner {
            kernel_dir: path,
            filter_fn,
            tests: BTreeMap::new(),
            gdb: false,
        }
    }

    pub fn enable_gdb(&mut self) {
        self.gdb = true;
    }

    pub fn set_filter(&mut self, filter: Regex) {
        self.filter_fn = Box::new(move |p| filter.is_match(p));
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
            if !(*self.filter_fn)(p) {
                continue;
            }

            let components = path_components(p);
            formatter.print(&components);

            let mut fix = Fixture::new(&self.kernel_dir)?;

            if let Err(e) = (*t)(&mut fix) {
                fail += 1;
                println!(" FAIL");
                info!("{}", e);
                debug!("{}", fix.vm);
                drop(fix);
            } else {
                fix.log_top_funcs(20);
                drop(fix);
                pass += 1;
                println!(" PASS");
            }
        }

        Ok((pass, fail))
    }
}

//-------------------------------
