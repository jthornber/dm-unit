use anyhow::{anyhow, Result};
use log::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::OpenOptions;
use std::io::{prelude::*, BufReader};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::capture_log::*;
use crate::db::TestResult;
use crate::emulator::loader::*;
use crate::emulator::memory::*;
use crate::fixture::*;

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
        .truncate(false)
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

#[derive(Default)]
pub struct TestSet {
    tests: BTreeMap<String, Test>,
}

impl TestSet {
    pub fn register(&mut self, path: &str, test: Test) {
        self.tests.insert(path.to_string(), test);
    }

    pub fn filter(&mut self, rx: &Regex) {
        let mut to_remove = Vec::new();
        for p in self.tests.keys() {
            if !rx.is_match(p) {
                to_remove.push(p.clone());
            }
        }
        for p in to_remove {
            self.tests.remove(&p);
        }
    }

    pub fn into_inner(self) -> BTreeMap<String, Test> {
        self.tests
    }
}

pub struct Test {
    kmodules: Vec<KernelModule>,
    func: TestFn,
    allow_leaks: bool,
}

impl Test {
    pub fn new(kmodules: Vec<KernelModule>, func: TestFn) -> Self {
        Test {
            kmodules,
            func: Box::new(func),
            allow_leaks: false,
        }
    }

    // A test that allows memory leaks.
    pub fn new_leaky(kmodules: Vec<KernelModule>, func: TestFn) -> Self {
        Test {
            kmodules,
            func: Box::new(func),
            allow_leaks: true,
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
    args: BTreeSet<String>,
}

fn get_log(log_lines: &Arc<Mutex<LogInner>>) -> String {
    let mut log = log_lines.lock().unwrap();
    log.get_lines().join("\n")
}

/// Wraps a test so we can run it in a thread.
fn run_test(mut fix: Fixture, t: Test, log_lines: Arc<Mutex<LogInner>>) -> TestResult {
    {
        let mut log = log_lines.lock().unwrap();
        let _ = log.get_lines();
    }

    let icount_begin = fix.vm.stats.instrs;
    let orig_memory = fix.vm.mem.snapshot();
    let mut result = (t.func)(&mut fix);

    // Check for memory leaks, but only if the test passed
    if result.is_ok() && !t.allow_leaks {
        let leaks = orig_memory.new_allocations(&fix.vm.mem);
        if !leaks.is_empty() {
            warn!("There were memory leaks:");
            for MEntry { heap_ptr, len, pc } in leaks {
                let loc = if let Some(pc) = pc {
                    fix.get_loc_from_addr(Addr(pc)).unwrap()
                } else {
                    String::new()
                };
                warn!("    0x{:x}+{:x} {}", heap_ptr, len, loc);
            }
            warn!("Source locations may be incorrect due to tail-call optimisation.");
            result = Err(anyhow!("Guest has memory leaks"));
        }
    }

    let icount_end = fix.vm.stats.instrs;

    match result {
        Ok(()) => TestResult {
            pass: true,
            log: get_log(&log_lines),
            icount: icount_end - icount_begin,
        },
        Err(e) => {
            warn!("Test failed: {:#}", e);

            TestResult {
                pass: false,
                log: get_log(&log_lines),
                icount: icount_end - icount_begin,
            }
        }
    }
}

impl TestRunner<'_> {
    pub fn new<P: AsRef<Path>>(kernel_dir: P, tests: TestSet) -> Result<Self> {
        check_kernel_version(&kernel_dir)?;

        let mut path = PathBuf::new();
        path.push(kernel_dir);

        let filter_fn = Box::new(move |_: &str| true);

        Ok(TestRunner {
            kernel_dir: path,
            filter_fn,
            tests: tests.into_inner(),
            jobs: 1,
            jit: false,
            args: BTreeSet::new(),
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

    pub fn append_arg(&mut self, arg: &str) {
        self.args.insert(arg.to_owned());
    }

    pub fn get_kernel_dir(&self) -> &Path {
        &self.kernel_dir
    }

    // FIXME: I've stripped out the jobs stuff for now.  We need to switch to using
    // processes for rather than threads so we can capture the log output.
    pub fn exec(self, log_lines: Arc<Mutex<LogInner>>) -> BTreeMap<String, TestResult> {
        let mut results: BTreeMap<String, TestResult> = BTreeMap::new();

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

            let rmem = {
                let kernel_dir = self.kernel_dir.clone();
                memories
                    .entry(modules)
                    .or_insert_with(|| Fixture::prep_memory(kernel_dir, &t.kmodules))
            };
            match rmem {
                Ok((loader_info, mem)) => {
                    let loader_info = loader_info.clone();
                    let mem = mem.snapshot();
                    let jit = self.jit;
                    let kernel_dir = self.kernel_dir.clone();
                    let args = self.args.clone();

                    match Fixture::new(&kernel_dir, loader_info, mem, jit, args) {
                        Ok(fix) => {
                            info!("Running test: {}", p);
                            let res = run_test(fix, t, log_lines.clone());
                            results.insert(p.clone(), res);
                        }
                        Err(e) => {
                            results.insert(
                                p.clone(),
                                TestResult {
                                    pass: false,
                                    log: format!("{:#}", e),
                                    icount: 0,
                                },
                            );
                        }
                    }
                }
                Err(_) => {
                    results.insert(
                        p.clone(),
                        TestResult {
                            pass: false,
                            log: "unable to load kernel modules".to_string(),
                            icount: 0,
                        },
                    );
                }
            }
        }

        results
    }
}

//-------------------------------
