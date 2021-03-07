use crate::fixture::*;
use anyhow::Result;
use gdbstub::arch::riscv::Riscv64;
use gdbstub::arch::Arch;
use gdbstub::target::ext::base::singlethread::{SingleThreadOps, StopReason};
use gdbstub::target::ext::base::{self, ResumeAction};
use gdbstub::target::{Target, TargetResult};
use log::{debug, info};
use regex::Regex;
use std::collections::BTreeMap;
use std::net::{TcpListener, TcpStream};
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
// GDB support

#[allow(dead_code)]
struct TestTarget<'a> {
    fix: Fixture,
    test_fn: &'a mut Box<dyn Fn(&mut Fixture) -> Result<()>>,
}

impl<'a> SingleThreadOps for TestTarget<'a> {
    fn resume(
        &mut self,
        _action: ResumeAction,
        _check_gdb_interrupt: &mut dyn FnMut() -> bool,
    ) -> Result<StopReason<<Self::Arch as Arch>::Usize>, Self::Error> {
        todo!();
    }

    fn read_registers(
        &mut self,
        _regs: &mut <Self::Arch as Arch>::Registers,
    ) -> TargetResult<(), Self> {
        todo!();
    }

    fn write_registers(
        &mut self,
        _regs: &<Self::Arch as Arch>::Registers,
    ) -> TargetResult<(), Self> {
        todo!();
    }

    fn read_addrs(
        &mut self,
        _start_addr: <Self::Arch as Arch>::Usize,
        _data: &mut [u8],
    ) -> TargetResult<(), Self> {
        todo!();
    }

    fn write_addrs(
        &mut self,
        _start_addr: <Self::Arch as Arch>::Usize,
        _data: &[u8],
    ) -> TargetResult<(), Self> {
        todo!();
    }
}

impl<'a> Target for TestTarget<'a> {
    type Arch = Riscv64;
    type Error = anyhow::Error;

    fn base_ops(&mut self) -> base::BaseOps<Self::Arch, Self::Error> {
        base::BaseOps::SingleThread(self)
    }
}

#[allow(dead_code)]
fn wait_for_gdb_connection(port: u16) -> std::io::Result<TcpStream> {
    let sockaddr = format!("localhost:{}", port);
    eprintln!("Waiting for a GDB connection on {:?}...", sockaddr);
    let sock = TcpListener::bind(sockaddr)?;

    // Blocks ...
    let (stream, addr) = sock.accept()?;

    eprintln!("Debugger connected from {}", addr);
    Ok(stream)
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
                debug!("skipping {} due to filter", p);
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
            } else {
                pass += 1;
                println!(" PASS");
            }
        }

        Ok((pass, fail))
    }
}

//-------------------------------
