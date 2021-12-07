use anyhow::{anyhow, Result};
use log::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::OpenOptions;
use std::io::{prelude::*, BufReader};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex};
use threadpool::ThreadPool;

use crate::emulator::loader::*;
use crate::emulator::memory::*;
use crate::fixture::*;

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

/// The tests are very closely tied to a particular version of the
/// kernel.  For instance we need to produce fake 'struct block_device'
/// values to pass into the guest code being tested, and the contents
/// of struct block_device can change from kernel to kernel.  This
/// function checks we're using a recent kernel.

#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct KernelVersion {
    version: u32,
    patchlevel: u32,
    sublevel: u32,
}

// Reads the kernel version from the Makefile
fn read_kernel_version<P: AsRef<Path>>(kernel_dir: P) -> Result<KernelVersion> {
    let mut path = PathBuf::new();
    path.push(kernel_dir);
    path.push("Makefile");
    let makefile = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(path)?;
    let reader = BufReader::new(makefile);

    let mut version: Option<u32> = None;
    let mut patch: Option<u32> = None;
    let mut sub: Option<u32> = None;

    let re = Regex::new(r"^(VERSION|PATCHLEVEL|SUBLEVEL)\s*=\s*(\d+)\s*$")?;

    for line in reader.lines() {
        let line = &line?;
        let caps = re.captures(line);
        if let Some(caps) = caps {
            match caps.get(1).unwrap().as_str() {
                "VERSION" => {
                    version = Some(caps.get(2).unwrap().as_str().parse().unwrap());
                }
                "PATCHLEVEL" => {
                    patch = Some(caps.get(2).unwrap().as_str().parse().unwrap());
                }
                "SUBLEVEL" => {
                    sub = Some(caps.get(2).unwrap().as_str().parse().unwrap());
                }
                _ => {
                    return Err(anyhow!("Broken kernel version regex"));
                }
            }
        }
    }

    if version.is_none() || patch.is_none() || sub.is_none() {
        Err(anyhow!(
            "Couldn't read kernel version from Makefile (is the kernel dir correct?)"
        ))
    } else {
        Ok(KernelVersion {
            version: version.unwrap(),
            patchlevel: patch.unwrap(),
            sublevel: sub.unwrap(),
        })
    }
}

fn check_kernel_version<P: AsRef<Path>>(kernel_dir: P) -> Result<()> {
    const MIN_KERNEL_VERSION: KernelVersion = KernelVersion {
        version: 5,
        patchlevel: 12,
        sublevel: 0,
    };
    let v = read_kernel_version(kernel_dir)?;
    if v < MIN_KERNEL_VERSION {
        info!(
            "kernel v{}.{}.{} is below v{}.{}.{}",
            v.version,
            v.patchlevel,
            v.sublevel,
            MIN_KERNEL_VERSION.version,
            MIN_KERNEL_VERSION.patchlevel,
            MIN_KERNEL_VERSION.sublevel
        );
        Err(anyhow!("Unsuitable kernel version"))
    } else {
        Ok(())
    }
}

//-------------------------------

trait TestFn_ = FnOnce(&mut Fixture) -> Result<()> + Send + 'static;
pub type TestFn = Box<dyn TestFn_>;

pub struct Test {
    kmodules: Vec<KernelModule>,
    func: TestFn,
}

impl Test {
    pub fn new(kmodules: Vec<KernelModule>, func: TestFn) -> Self {
        Test {
            kmodules,
            func: Box::new(func),
        }
    }
}

#[allow(dead_code)]
pub struct TestRunner<'a> {
    kernel_dir: PathBuf,
    filter_fn: Box<dyn Fn(&str) -> bool + 'a>,
    tests: BTreeMap<String, Test>,
    jobs: usize,
    jit: bool,
}

/// Wraps a test so we can run it in a thread.
fn run_test(mut fix: Fixture, t: Test) -> Result<()> {
    (t.func)(&mut fix)
}

impl<'a> TestRunner<'a> {
    pub fn new<P: AsRef<Path>>(kernel_dir: P) -> Result<Self> {
        check_kernel_version(&kernel_dir)?;

        let mut path = PathBuf::new();
        path.push(kernel_dir);

        let filter_fn = Box::new(move |_: &str| true);

        Ok(TestRunner {
            kernel_dir: path,
            filter_fn,
            tests: BTreeMap::new(),
            jobs: 1,
            jit: false,
        })
    }

    pub fn set_filter(&mut self, filter: Regex) {
        self.filter_fn = Box::new(move |p| filter.is_match(p));
    }

    pub fn set_jobs(&mut self, jobs: usize) {
        self.jobs = jobs;
    }

    pub fn set_jit(&mut self) {
        self.jit = true;
    }

    pub fn get_kernel_dir(&self) -> &Path {
        &self.kernel_dir
    }

    pub fn register(&mut self, path: &str, t: Test) {
        self.tests.insert(path.to_string(), t);
    }

    pub fn exec(self) -> Result<(usize, usize)> {
        let mut pass = 0;
        let mut fail = 0;
        let mut formatter = PathFormatter::new();

        let pool = ThreadPool::new(self.jobs);

        let results: Arc<Mutex<BTreeMap<String, Result<()>>>> =
            Arc::new(Mutex::new(BTreeMap::new()));

        let mut memories: BTreeMap<BTreeSet<String>, Result<(LoaderInfo, Memory)>> =
            BTreeMap::new();

        for (p, t) in self.tests {
            if !(*self.filter_fn)(&p) {
                continue;
            }

            let mut modules = BTreeSet::new();
            for m in &t.kmodules {
                modules.insert(m.name());
            }

            let rmem;
            {
                let kernel_dir = self.kernel_dir.clone();
                rmem = memories
                    .entry(modules)
                    .or_insert_with(|| Fixture::prep_memory(kernel_dir, &t.kmodules));
            }
            match rmem {
                Ok((loader_info, mem)) => {
                    let results = results.clone();
                    let loader_info = loader_info.clone();
                    let mem = mem.clone();
                    let jit = self.jit;

                    match Fixture::new(loader_info, mem, jit) {
                        Ok(fix) => {
                            pool.execute(move || {
                                let res = run_test(fix, t);

                                // FIXME: common code
                                let mut results = results.lock().unwrap();
                                results.insert(p.clone(), res);
                            });
                        }
                        Err(e) => {
                            // FIXME: common code
                            let mut results = results.lock().unwrap();
                            results.insert(p.clone(), Err(e));
                            drop(results);
                        }
                    }
                }
                Err(r) => {
                    // FIXME: common code
                    let mut results = results.lock().unwrap();
                    results.insert(p.clone(), Err(anyhow!(r.to_string()))); // anyhow!("unable to load kernel modules")));
                    drop(results);
                }
            }
        }

        pool.join();

        let results = Arc::try_unwrap(results).unwrap().into_inner()?;

        for (p, res) in results.into_iter() {
            let components = path_components(&p);
            formatter.print(&components);

            match res {
                Err(e) => {
                    fail += 1;
                    println!(" FAIL");
                    info!("{}", e);
                }
                Ok(()) => {
                    pass += 1;
                    println!(" PASS");
                }
            }
        }

        Ok((pass, fail))
    }
}

//-------------------------------
