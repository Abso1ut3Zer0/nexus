//! Shared state and bookkeeping for the bandits.
//!
//! Every bandit keeps two per-arm `f64` arrays (pull counts and reward sums,
//! or the two parameters of a posterior), a pull counter and a priming
//! threshold, and does the same three things with them on every update:
//! check the arm index, decay both arrays toward a reference, add to one arm.
//! That lives here once; the selection rules stay with the types.

use alloc::boxed::Box;
use alloc::vec;

use nexus_stats_core::ConfigError;
use nexus_stats_core::math::MulAdd;

/// Panics unless `arm < num_arms`: an out-of-range arm is runtime misuse, not
/// a data error (the crate's three-way policy).
#[inline]
pub(crate) fn check_arm(arm: usize, num_arms: usize) {
    assert!(arm < num_arms, "arm {arm} >= num_arms {num_arms}");
}

/// A per-update decay factor must lie in `(0, 1]`; NaN and infinities are
/// rejected.
pub(crate) fn checked_decay(decay: f64) -> Result<f64, ConfigError> {
    if !(decay > 0.0 && decay <= 1.0) {
        return Err(ConfigError::Invalid("decay must be in (0, 1]"));
    }
    Ok(decay)
}

#[derive(Debug, Clone)]
pub(crate) struct ArmBank {
    /// First per-arm statistic: pull counts, or the first posterior parameter.
    pub a: Box<[f64]>,
    /// Second per-arm statistic: reward sums, or the second posterior parameter.
    pub b: Box<[f64]>,
    pub total_pulls: u64,
    pub min_samples: u64,
}

impl ArmBank {
    /// Two arms is the smallest bandit; fewer is a configuration error.
    pub fn new(
        arms: usize,
        fill_a: f64,
        fill_b: f64,
        min_samples: u64,
    ) -> Result<Self, ConfigError> {
        if arms < 2 {
            return Err(ConfigError::Invalid("arms must be >= 2"));
        }
        Ok(Self {
            a: vec![fill_a; arms].into_boxed_slice(),
            b: vec![fill_b; arms].into_boxed_slice(),
            total_pulls: 0,
            min_samples,
        })
    }

    #[inline]
    pub fn arms(&self) -> usize {
        self.a.len()
    }

    #[inline]
    pub fn check_arm(&self, arm: usize) {
        check_arm(arm, self.a.len());
    }

    /// Pulls every element of both arrays toward its reference:
    /// `v = (v - toward) * decay + toward`. Toward zero this is plain
    /// forgetting; toward a prior it forgets evidence without ever collapsing
    /// a posterior to a point mass.
    /// Multiplies both arrays by `decay` (the decay-toward-zero of the
    /// count-and-reward bandits). A plain multiply: `decay_toward(d, 0, 0)`
    /// would compute `v * d + 0.0`, which the compiler cannot fold to `v * d`
    /// (`-0.0 + 0.0` is `+0.0`), and that extra add costs the K=2 update
    /// 60 percent.
    #[inline]
    pub fn decay(&mut self, decay: f64) {
        for (a, b) in self.a.iter_mut().zip(self.b.iter_mut()) {
            *a *= decay;
            *b *= decay;
        }
    }

    #[inline]
    pub fn decay_toward(&mut self, decay: f64, toward_a: f64, toward_b: f64) {
        for (a, b) in self.a.iter_mut().zip(self.b.iter_mut()) {
            *a = (*a - toward_a).fma(decay, toward_a);
            *b = (*b - toward_b).fma(decay, toward_b);
        }
    }

    /// One pull of `arm`, adding `da` and `db` to its two statistics.
    #[inline]
    pub fn record(&mut self, arm: usize, da: f64, db: f64) {
        self.a[arm] += da;
        self.b[arm] += db;
        self.total_pulls += 1;
    }

    #[inline]
    pub fn is_primed(&self) -> bool {
        self.total_pulls >= self.min_samples
    }

    #[inline]
    pub fn reset(&mut self, fill_a: f64, fill_b: f64) {
        self.a.fill(fill_a);
        self.b.fill(fill_b);
        self.total_pulls = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "arm 3 >= num_arms 3")]
    fn out_of_range_arm_panics() {
        let bank = ArmBank::new(3, 0.0, 0.0, 1).unwrap();
        bank.check_arm(3);
    }

    #[test]
    fn decay_toward_moves_both_arrays_toward_the_reference() {
        let mut bank = ArmBank::new(2, 1.0, 1.0, 1).unwrap();
        bank.record(0, 9.0, 3.0); // a = [10, 1], b = [4, 1]
        bank.decay_toward(0.5, 1.0, 1.0);
        assert_eq!(bank.a[0], 5.5); // 1 + (10 - 1) * 0.5
        assert_eq!(bank.b[0], 2.5); // 1 + (4 - 1) * 0.5
        assert_eq!(bank.a[1], 1.0); // already at the reference
        assert_eq!(bank.b[1], 1.0);
        assert_eq!(bank.total_pulls, 1);
    }

    #[test]
    fn decay_validation() {
        assert!(checked_decay(1.0).is_ok());
        assert!(checked_decay(0.5).is_ok());
        for bad in [0.0, -0.1, 1.5, f64::NAN, f64::INFINITY] {
            assert!(checked_decay(bad).is_err(), "{bad} must be rejected");
        }
        assert!(ArmBank::new(1, 0.0, 0.0, 1).is_err());
    }
}
