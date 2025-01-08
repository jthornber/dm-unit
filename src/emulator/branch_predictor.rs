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
    pub fn update_counter(&mut self, index: u16, taken: bool) -> bool {
        let word_index = index as usize / COUNTS_PER_WORD;
        let shift = 2 * (index as usize % COUNTS_PER_WORD);
        let word = &mut self.counts[word_index];
        let mut count = ((*word >> shift) & 0b11) as u8;

        // Determine if the previous count was >= 2
        let was_set = ((count >> 1) & 1) != 0;

        // Compute masks
        let taken_mask = taken as u8;
        let not_taken_mask = (!taken_mask) & 1;

        // Compute increment and decrement without branches
        let inc = taken_mask & ((count < 3) as u8);
        let dec = not_taken_mask & ((count > 0) as u8);

        // Update count branchlessly and ensure it stays within 0..=3
        count = count.wrapping_add(inc).wrapping_sub(dec) & 0b11;

        // Update the counter in the word
        *word = (*word & !(0b11 << shift)) | ((count as u64) << shift);

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

        let predicted_taken = self.update_counter(key, taken);

        self.history = ((self.history << 1) | (taken as u16)) & HISTORY_MASK;

        if predicted_taken == taken {
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
}

//--------------------------------
