use std::sync::{Arc, Mutex};
use std::ops::Deref;

//-------------------------------

// Snapshot is very similar to clone, except we
// always want a real copy.  eg, Arc::clone() doesn't
// do the right thing.
pub trait Snapshot {
    fn snapshot(&self) -> Self;
}

impl<S: Snapshot> Snapshot for Arc<S> {
    fn snapshot(&self) -> Self {
        Arc::new((*self).deref().snapshot())
    }
}

impl<S: Snapshot> Snapshot for Mutex<S> {
    fn snapshot(&self) -> Self {
        let v = self.lock().unwrap();
        Mutex::new(v.snapshot())
    }
}

impl<S: Snapshot> Snapshot for Vec<S> {
    fn snapshot(&self) -> Self {
        let mut new = Vec::with_capacity(self.len());

        for v in self {
            new.push(v.snapshot());
        }

        new
    }
}

//-------------------------------
