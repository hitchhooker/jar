//! f-fault-tolerant tip tracking for GRANDPA finality convergence.
//!
//! Ported from commonware-sdk's aggregation engine. Tracks the reported
//! finality tip for each validator and efficiently computes the "safe tip" —
//! the highest height that at least one honest validator has reached.
//!
//! With n validators and f = floor((n-1)/3) maximum faults:
//! - The `hi` set contains the f highest tips (potentially faulty)
//! - The `lo` set contains the n-f lowest tips (at least one honest)
//! - The safe tip is max(lo) — guaranteed reached by ≥1 honest validator
//!
//! All operations are O(log n) via BTreeMap.

use std::collections::{btree_map, BTreeMap, HashMap};

/// Block height (finality tip).
pub type Height = u64;

/// Tracks the f-th highest validator tip for safe finality advancement.
///
/// Used by the GRANDPA voting logic to determine when finality has
/// genuinely advanced (at least one honest validator reached that height).
pub struct SafeTip {
    /// Per-validator maximum reported tip.
    tips: HashMap<u32, Height>,

    /// The f highest tips (assumed potentially faulty).
    hi: BTreeMap<Height, usize>,

    /// The n-f lowest tips. max(lo) is the safe tip.
    lo: BTreeMap<Height, usize>,
}

impl Default for SafeTip {
    fn default() -> Self {
        Self {
            tips: HashMap::new(),
            hi: BTreeMap::new(),
            lo: BTreeMap::new(),
        }
    }
}

impl SafeTip {
    /// Initialize with a validator set. All tips start at 0.
    ///
    /// `n` is the total validator count. `f` = floor((n-1)/3) maximum faults.
    ///
    /// # Panics
    ///
    /// Panics if validator count is zero.
    pub fn init(&mut self, validator_count: usize) {
        assert!(validator_count > 0, "empty validator set");

        let n = validator_count;
        let f = (n - 1) / 3; // n3f1: floor((n-1)/3)

        let mut tips = HashMap::with_capacity(n);
        for i in 0..n {
            tips.insert(i as u32, 0);
        }

        let mut lo = BTreeMap::new();
        lo.insert(0u64, n - f);
        let mut hi = BTreeMap::new();
        if f > 0 {
            hi.insert(0u64, f);
        }

        self.tips = tips;
        self.hi = hi;
        self.lo = lo;
    }

    /// Update the tip for a validator. Returns the old tip if updated,
    /// None if the validator doesn't exist or the new tip isn't higher.
    pub fn update(&mut self, validator_index: u32, new: Height) -> Option<Height> {
        let &old = self.tips.get(&validator_index)?;

        if old >= new {
            return None;
        }

        self.tips.insert(validator_index, new);

        // Case 1: value was in hi, stays in hi
        if self.hi.contains_key(&old) {
            dec(self.hi.entry(old));
            inc(self.hi.entry(new));
            return Some(old);
        }

        // Value is in lo. Check if it can stay there.
        let stay_in_lo = self
            .hi
            .first_entry()
            .map(|e| *e.key())
            .is_none_or(|min_hi| min_hi >= new);

        // Case 2: stays in lo
        if stay_in_lo {
            dec(self.lo.entry(old));
            inc(self.lo.entry(new));
            return Some(old);
        }

        // Case 3: must move from lo to hi, rebalance
        dec(self.lo.entry(old));
        inc(self.hi.entry(new));

        // Move min(hi) back to lo
        let min_hi = *self.hi.first_entry().expect("empty hi").key();
        assert!(min_hi < new);
        dec(self.hi.entry(min_hi));
        inc(self.lo.entry(min_hi));

        Some(old)
    }

    /// Returns the safe tip: the highest height that at least one
    /// honest validator has reached (max of the lo set).
    ///
    /// # Panics
    ///
    /// Panics if the validator set is empty.
    pub fn get(&self) -> Height {
        self.lo
            .last_key_value()
            .map(|(k, _)| *k)
            .expect("empty validator set")
    }

    /// Returns the number of tracked validators.
    pub fn validator_count(&self) -> usize {
        self.tips.len()
    }

    /// Returns the tip for a specific validator, if tracked.
    pub fn tip_for(&self, validator_index: u32) -> Option<Height> {
        self.tips.get(&validator_index).copied()
    }
}

fn inc(entry: btree_map::Entry<'_, Height, usize>) {
    *entry.or_default() += 1;
}

fn dec(entry: btree_map::Entry<'_, Height, usize>) {
    let btree_map::Entry::Occupied(mut value) = entry else {
        panic!("cannot decrement non-existent entry");
    };
    *value.get_mut() -= 1;
    if *value.get() == 0 {
        value.remove();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init() {
        let mut st = SafeTip::default();
        st.init(4);
        assert_eq!(st.validator_count(), 4);
        assert_eq!(st.get(), 0);
    }

    #[test]
    fn test_update_and_safe_tip_advancement() {
        // 4 validators, f=1: hi has 1 slot, lo has 3 slots
        let mut st = SafeTip::default();
        st.init(4);

        // First update: only 1 of 4 advanced → safe tip stays 0
        assert_eq!(st.update(0, 10), Some(0));
        assert_eq!(st.get(), 0);

        // Second: 2 of 4 → safe tip = 10 (the f+1-th highest)
        assert_eq!(st.update(1, 20), Some(0));
        assert_eq!(st.get(), 10);

        // Third: 3 of 4 → safe tip = 20
        assert_eq!(st.update(2, 30), Some(0));
        assert_eq!(st.get(), 20);

        // Fourth: all → safe tip = 30
        assert_eq!(st.update(3, 40), Some(0));
        assert_eq!(st.get(), 30);
    }

    #[test]
    fn test_update_noop_for_lower_tip() {
        let mut st = SafeTip::default();
        st.init(4);
        st.update(0, 10);
        assert_eq!(st.update(0, 5), None);
        assert_eq!(st.update(0, 10), None);
    }

    #[test]
    fn test_update_unknown_validator() {
        let mut st = SafeTip::default();
        st.init(4);
        assert_eq!(st.update(99, 10), None);
    }

    #[test]
    fn test_1023_validators() {
        // JAM mainnet: 1023 validators, f=340
        let mut st = SafeTip::default();
        st.init(1023);
        assert_eq!(st.get(), 0);

        // Update 682 validators (n-f) → safe tip advances
        for i in 0..682 {
            st.update(i, 100);
        }
        assert_eq!(st.get(), 100);

        // Update remaining 341 → safe tip still 100
        // (they're in hi, which has f=340 slots)
        for i in 682..1023 {
            st.update(i, 200);
        }
        assert_eq!(st.get(), 200);
    }

    #[test]
    fn test_rebalancing_lo_to_hi() {
        let mut st = SafeTip::default();
        st.init(4); // f=1
        st.update(0, 5);
        st.update(1, 15);
        st.update(2, 25);
        // lo=[5,15,25], hi=[0] (validator 3 still at 0)

        // Update validator 0 from 5 to 40 — must move to hi
        st.update(0, 40);
        // 40 goes to hi, min_hi goes back to lo
        assert_eq!(st.get(), 25);
    }

    #[test]
    fn test_tip_for() {
        let mut st = SafeTip::default();
        st.init(4);
        st.update(2, 42);
        assert_eq!(st.tip_for(2), Some(42));
        assert_eq!(st.tip_for(0), Some(0));
        assert_eq!(st.tip_for(99), None);
    }

    #[test]
    #[should_panic]
    fn test_init_empty() {
        let mut st = SafeTip::default();
        st.init(0);
    }
}
