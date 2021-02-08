use crate::memory::Addr;

use anyhow::{anyhow, Result};
use std::any::Any;
use std::collections::BTreeMap;

//-------------------------------

/// We need to be able to get from a guest address, to an arbitrarily
/// typed value in the host.  We use the Any trait for this.
pub struct UserData {
    map: BTreeMap<Addr, Box<dyn Any>>,
}

impl UserData {
    pub fn new() -> Self {
        UserData {
            map: BTreeMap::new(),
        }
    }

    fn bad_address(ptr: Addr) -> anyhow::Error {
        anyhow!("couldn't find user data at address {:?}", ptr)
    }

    fn bad_type(ptr: Addr) -> anyhow::Error {
        anyhow!("Incorrect user data type for {:?}", ptr)
    }

    pub fn insert(&mut self, ptr: Addr, v: Box<dyn Any>) {
        self.map.insert(ptr, v);
    }

    pub fn get_ref<T: Any>(&self, ptr: Addr) -> Result<&T> {
        let ud = self.map.get(&ptr);

        if ud.is_none() {
            return Err(UserData::bad_address(ptr));
        }

        match ud.unwrap().downcast_ref::<T>() {
            Some(v) => Ok(v),
            None => {
                Err(UserData::bad_type(ptr))
            }
        }
    }

    pub fn get_mut<T: Any>(&mut self, ptr: Addr) -> Result<&mut T> {
        let ud = self.map.get_mut(&ptr);

        if ud.is_none() {
            return Err(UserData::bad_address(ptr));
        }

        match ud.unwrap().downcast_mut::<T>() {
            Some(v) => Ok(v),
            None => Err(UserData::bad_type(ptr)),
        }
    }

    pub fn remove<T: Any>(&mut self, ptr: Addr) -> Result<T> {
        match self.map.remove(&ptr) {
            Some(boxed_value) => match boxed_value.downcast::<T>() {
                Ok(v) => Ok(*v),
                Err(boxed_value) => {
                    self.map.insert(ptr, boxed_value);
                    Err(UserData::bad_type(ptr))
                }
            },
            None => Err(UserData::bad_address(ptr)),
        }
    }
}

impl Default for UserData {
    fn default() -> Self {
        Self::new()
    }
}

//-------------------------------
