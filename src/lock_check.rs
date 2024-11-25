use crate::emulator::memory::Addr;

//-------------------------------

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum LockType {
    Spin,
    Mutex,
    RWLock,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Lock {
    pub lock_type: LockType,
    pub lock_addr: Addr,
    pub pc: Addr,
}

#[derive(Default)]
pub struct LockCheck {
    locks: Vec<Lock>,
    spin_count: usize,
}


impl LockCheck {
    pub fn lock(&mut self, lock_type: LockType, lock_addr: Addr, pc: Addr) {
        self.locks.push(Lock {
            lock_type,
            lock_addr,
            pc,
        });

        if lock_type == LockType::Spin {
            self.spin_count += 1;
        }
    }

    pub fn unlock(&mut self, lock_type: LockType, lock_addr: Addr) -> Result<(), Lock> {
        let lock = self.locks.pop().unwrap();

        if lock.lock_type != lock_type || lock.lock_addr != lock_addr {
            return Err(lock);
        }

        if lock_type == LockType::Spin {
            self.spin_count -= 1;
        }

        Ok(())
    }

    pub fn spin_held(&self) -> bool {
        self.spin_count > 0
    }

    pub fn most_recent_spin_pc(&self) -> Option<Addr> {
        for lock in self.locks.iter().rev() {
            if lock.lock_type == LockType::Spin {
                return Some(lock.pc);
            }
        }

        None
    }
}

//-------------------------------