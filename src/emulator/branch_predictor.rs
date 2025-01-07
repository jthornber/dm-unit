use crate::emulator::memory::*;

//--------------------------------

// A saturating 2bit counter.
#[derive(Default)]
struct TwoBitCounter {
    count: u8,
}

impl TwoBitCounter {
    pub fn is_set(&self) -> bool {
        (self.count & 0b10) == 0b10
    }

    pub fn inc(&mut self) {
        if self.count < 3 {
            self.count += 1;
        }
    }

    pub fn dec(&mut self) {
        if self.count > 0 {
            self.count -= 1;
        }
    }
}

//--------------------------------

const HISTORY_BITS: usize = 12;
const HISTORY_MASK: u16 = (1 << HISTORY_BITS) - 1;

enum BranchPrediction {
    Hit,
    Miss,
}

/// A branch predictor using global history and a table of 2-bit saturating counters.
///
/// The `BranchPredictor` maintains a global history of branch outcomes and uses it,
/// along with the branch address, to index into a table of `TwoBitCounter`s.
/// This allows for dynamic prediction of branch behavior based on historical patterns.
struct BranchPredictor {
    history: u16,
    table: Vec<TwoBitCounter>,
}

impl BranchPredictor {
    pub fn new() -> Self {
        let table: Vec<TwoBitCounter> = (0..(1 << HISTORY_BITS))
            .map(|_| TwoBitCounter::default())
            .collect();
        Self { history: 0, table }
    }

    /// Processes a branch outcome and updates the predictor state.
    ///
    /// This method updates the global history and the corresponding counter
    /// based on whether the branch was taken. It returns whether the prediction
    /// was a hit (correct) or a miss (incorrect).
    ///
    /// # Arguments
    ///
    /// * `addr` - The address of the branch instruction.
    /// * `taken` - A boolean indicating if the branch was taken (`true`) or not taken (`false`).
    ///
    /// # Returns
    ///
    /// A `BranchPrediction` indicating if the prediction was a `Hit` or a `Miss`.
    pub fn branch(&mut self, addr: Addr, taken: bool) -> BranchPrediction {
        use BranchPrediction::*;

        let low_bits = (addr.0 as u16) & HISTORY_MASK;
        let key = low_bits ^ self.history;
        let count: &mut TwoBitCounter = &mut self.table[key as usize];
        let result = if count.is_set() == taken { Hit } else { Miss };

        self.history = ((self.history << 1) | if taken { 1 } else { 0 }) & HISTORY_MASK;

        if taken {
            count.inc();
        } else {
            count.dec();
        }

        result
    }
}

//--------------------------------
