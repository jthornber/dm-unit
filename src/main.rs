pub mod memory;

use elf;
use std::result;
use memory::Memory;

/// Emulator for riscv32i

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
enum Reg {
    Zero = 0,
    Ra,
    Sp,
    Gp,
    Tp,
    T0,
    T1,
    T2,
    S0,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
}

struct VM {
    registers: Vec<u32>,
    mem: Memory,
}

impl VM {
    pub fn new(mem: u32) -> Self {
        todo!();
    }
}

fn main() {
    let _mem = Memory::new(1 * 1024 * 1024);
    println!("Hello, world!");
}
