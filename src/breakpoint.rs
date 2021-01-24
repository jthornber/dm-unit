use crate::vm;
use crate::vm::*;

use log::debug;

//-------------------------------
/*
pub struct Stub {
    name: String,
    v: u64,
}

impl Stub {
    pub fn new(name: &str, v: u64) -> Self {
        Stub {
            name: name.to_string(),
            v,
        }
    }
}

impl Breakpoint for Stub {
    fn exec(&mut self, vm: &mut VM) -> vm::Result<()> {
        debug!("stubbed '{}' returning {}", self.name, self.v);
        vm.ret(self.v);
        Ok(())
    }
}
*/
//-------------------------------
