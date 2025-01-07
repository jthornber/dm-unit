use crate::emulator::memory::*;

//--------------------------------

const HISTORY_BITS: usize = 12;
const HISTORY_MASK: u16 = (1 << HISTORY_BITS) - 1;
const COUNTS_PER_WORD: usize = 32;
const NR_U64: usize = ((1 << HISTORY_BITS) + (COUNTS_PER_WORD - 1)) / COUNTS_PER_WORD;

#[derive(Eq, PartialEq, Debug)]
pub enum BranchPrediction {
    Hit,
    Miss,
}

/// A branch predictor using global history and a table of 2-bit saturating counters.
///
/// The `BranchPredictor` maintains a global history of branch outcomes and uses it,
/// along with the branch address, to index into a table of `TwoBitCounter`s.
/// This allows for dynamic prediction of branch behavior based on historical patterns.
pub struct BranchPredictor {
    history: u16,

    // This is a table of 2-bit saturating counts stored in u64s.
    counts: Box<[u64]>,
}

impl Default for BranchPredictor {
    fn default() -> Self {
        let counts = vec![0u64; NR_U64].into_boxed_slice();
        Self { history: 0, counts }
    }
}

impl BranchPredictor {
    fn update_counter(&mut self, index: u16, taken: bool) -> bool {
        let word_index = index as usize / COUNTS_PER_WORD;
        let word = &mut self.counts[word_index];
        let shift = 2 * (index % COUNTS_PER_WORD as u16);
        let mut count = (*word >> shift) & 0b11;
        let was_set = count >= 2;

        if taken && count < 3 {
            count += 1;
        } else if !taken && count > 0 {
            count -= 1;
        }

        *word = (*word & !(0b11 << shift)) | (count << shift);
        was_set
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

        let was_set = self.update_counter(key, taken);

        self.history = ((self.history << 1) | (taken as u16)) & HISTORY_MASK;

        if was_set == taken {
            Hit
        } else {
            Miss
        }
    }
}

//--------------------------------

mod tests {
    use super::*;

    #[test]
    fn test_update_counter_increment() {
        let mut predictor = BranchPredictor::default();
        let index = 0u16;

        // Initial prediction should be Not Taken (count = 0)
        let prediction = predictor.update_counter(index, true);
        assert_eq!(prediction, false); // Since count = 0 (< 2)

        // Increment the counter a few times
        for _ in 0..3 {
            predictor.update_counter(index, true);
        }

        // Now the prediction should be Taken (count >= 2)
        let prediction = predictor.update_counter(index, true);
        assert_eq!(prediction, true); // Since count >= 2

        // Counter should be saturated at 3
        let word = predictor.counts[index as usize / COUNTS_PER_WORD];
        let shift = 2 * (index % COUNTS_PER_WORD as u16);
        let count = (word >> shift) & 0b11;
        assert_eq!(count, 3);
    }

    #[test]
    fn test_update_counter_decrement() {
        let mut predictor = BranchPredictor::default();
        let index = 0u16;

        // Set counter to maximum
        predictor.update_counter(index, true);
        predictor.update_counter(index, true);
        predictor.update_counter(index, true);

        // Decrement the counter a few times
        for _ in 0..3 {
            predictor.update_counter(index, false);
        }

        // Now the prediction should be Not Taken (count < 2)
        let prediction = predictor.update_counter(index, false);
        assert_eq!(prediction, false);

        // Counter should be at 0
        let word = predictor.counts[index as usize / COUNTS_PER_WORD];
        let shift = 2 * (index % COUNTS_PER_WORD as u16);
        let count = (word >> shift) & 0b11;
        assert_eq!(count, 0);
    }

    #[test]
    fn test_counter_saturation_hit_rate() {
        let mut predictor = BranchPredictor::default();
        let addr = Addr(0x1000);
        let mut hits = 0;
        let total = 20;

        // Simulate a branch taken repeatedly
        for _ in 0..total {
            if predictor.branch(addr, true) == BranchPrediction::Hit {
                hits += 1;
            }
        }

        let hit_rate = hits as f64 / total as f64;
        println!("Hit rate after training: {:.2}%", hit_rate * 100.0);

        // Expect a high hit rate after the predictor has trained
        assert!(hit_rate > 0.8);
    }
}

//--------------------------------
