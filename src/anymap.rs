use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

//-------------------------------

// All borrowed from the egui library.

/// A cloneable Any
struct AnyEntry {
    value: Box<dyn Any + 'static>,
    clone_fn: fn(&Box<dyn Any + 'static>) -> Box<dyn Any + 'static>,
}

impl fmt::Debug for AnyEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AnyEntry")
            .field("value_type_id", &self.type_id())
            .finish()
    }
}

impl Clone for AnyEntry {
    fn clone(&self) -> Self {
        AnyEntry {
            value: (self.clone_fn)(&self.value),
            clone_fn: self.clone_fn,
        }
    }
}

pub trait AnyMapTrait: 'static + Any + Clone {}

impl<T: 'static + Any + Clone> AnyMapTrait for T {}

impl AnyEntry {
    pub fn new<T: AnyMapTrait>(t: T) -> Self {
        AnyEntry {
            value: Box::new(t),
            clone_fn: |x| {
                let x = x.downcast_ref::<T>().unwrap();
                Box::new(x.clone())
            },
        }
    }

    pub fn type_id(&self) -> TypeId {
        (*self.value).type_id()
    }

    pub fn get_mut<T: AnyMapTrait>(&mut self) -> Option<&mut T> {
        self.value.downcast_mut()
    }

    pub fn get<T: AnyMapTrait>(&self) -> Option<&T> {
        self.value.downcast_ref()
    }

    pub fn get_mut_or_set_with<T: AnyMapTrait>(&mut self, set_with: impl FnOnce() -> T) -> &mut T {
        if !self.value.is::<T>() {
            *self = Self::new(set_with());
        }
        self.value.downcast_mut().unwrap()
    }

    pub fn downcast<T: AnyMapTrait>(self) -> Box<T> {
        self.value.downcast::<T>().unwrap()
    }
}

//-------------------------------

#[derive(Clone, Debug)]
pub struct AnyMap<Key: Hash + Eq>(HashMap<Key, AnyEntry>);

impl<Key: Hash + Eq> Default for AnyMap<Key> {
    fn default() -> Self {
        AnyMap(HashMap::new())
    }
}

impl<Key: Hash + Eq> AnyMap<Key> {
    pub fn get<T: AnyMapTrait>(&self, key: &Key) -> Option<&T> {
        self.0.get(key)?.get()
    }

    pub fn get_mut<T: AnyMapTrait>(&mut self, key: &Key) -> Option<&mut T> {
        self.0.get_mut(key)?.get_mut()
    }
}

impl<Key: Hash + Eq> AnyMap<Key> {
    pub fn get_or_insert_with<T: AnyMapTrait>(
        &mut self,
        key: Key,
        or_insert_with: impl FnOnce() -> T,
    ) -> &T {
        &*self.get_mut_or_insert_with(key, or_insert_with)
    }

    pub fn get_or_default<T: AnyMapTrait + Default>(&mut self, key: Key) -> &T {
        self.get_or_insert_with(key, Default::default)
    }

    pub fn get_mut_or_insert_with<T: AnyMapTrait>(
        &mut self,
        key: Key,
        or_insert_with: impl FnOnce() -> T,
    ) -> &mut T {
        use std::collections::hash_map::Entry;
        match self.0.entry(key) {
            Entry::Vacant(vacant) => vacant
                .insert(AnyEntry::new(or_insert_with()))
                .get_mut()
                .unwrap(),
            Entry::Occupied(occupied) => occupied.into_mut().get_mut_or_set_with(or_insert_with),
        }
    }

    pub fn get_mut_or_default<T: AnyMapTrait + Default>(&mut self, key: Key) -> &mut T {
        self.get_mut_or_insert_with(key, Default::default)
    }
}

impl<Key: Hash + Eq> AnyMap<Key> {
    pub fn insert<T: AnyMapTrait>(&mut self, key: Key, element: T) {
        self.0.insert(key, AnyEntry::new(element));
    }

    pub fn remove<T: AnyMapTrait>(&mut self, key: &Key) -> Box<T> {
        let v = self.0.remove(key).unwrap();
        v.downcast::<T>()
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }
}

//-------------------------------
