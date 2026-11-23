/// Debounce filter — requires N consecutive active signals to trigger.
///
/// Prevents spurious single-sample activations from triggering.
/// Resets the consecutive counter on any inactive sample.
///
/// # Use Cases
/// - Confirming a condition persists before acting
/// - Filtering noisy boolean signals
/// - "Only alert if elevated for N consecutive checks"
#[derive(Debug, Clone)]
pub struct Debounce {
    threshold: u64,
    consecutive: u64,
    /// Updates since construction or `reset`.
    count: u64,
}

impl Debounce {
    /// Creates a new debounce filter.
    ///
    /// `threshold` is the number of consecutive active samples required
    /// to trigger (return `true`).
    #[inline]
    pub fn new(threshold: u64) -> Result<Self, nexus_stats_core::ConfigError> {
        if threshold == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "threshold must be positive",
            ));
        }
        Ok(Self {
            threshold,
            consecutive: 0,
            count: 0,
        })
    }

    /// Feeds a boolean signal. Returns `true` once the threshold of
    /// consecutive active samples is reached.
    #[inline]
    #[must_use]
    pub fn update(&mut self, active: bool) -> bool {
        self.count += 1;
        if active {
            self.consecutive += 1;
        } else {
            self.consecutive = 0;
        }
        self.consecutive >= self.threshold
    }

    /// Current consecutive count.
    #[inline]
    #[must_use]
    pub fn consecutive(&self) -> u64 {
        self.consecutive
    }

    /// Samples processed since construction or `reset`.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether at least one update has been seen.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count > 0
    }

    /// Resets the consecutive counter.
    #[inline]
    pub fn reset(&mut self) {
        self.consecutive = 0;
        self.count = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn triggers_after_threshold() {
        let mut d = Debounce::new(3).unwrap();
        assert!(!d.update(true));
        assert!(!d.update(true));
        assert!(d.update(true)); // 3rd consecutive
    }

    #[test]
    fn resets_on_false() {
        let mut d = Debounce::new(3).unwrap();
        assert!(!d.update(true));
        assert!(!d.update(true));
        assert!(!d.update(false)); // reset
        assert!(!d.update(true)); // restart count
        assert!(!d.update(true));
        assert!(d.update(true)); // 3rd consecutive again
    }

    #[test]
    fn no_false_trigger_at_threshold_minus_one() {
        let mut d = Debounce::new(5).unwrap();
        for _ in 0..4 {
            assert!(!d.update(true));
        }
        // 4 is not enough
        assert!(!d.update(false)); // break
    }

    #[test]
    fn stays_triggered() {
        let mut d = Debounce::new(2).unwrap();
        assert!(!d.update(true));
        assert!(d.update(true));
        assert!(d.update(true)); // stays triggered
    }

    #[test]
    fn reset() {
        let mut d = Debounce::new(2).unwrap();
        let _ = d.update(true);
        d.reset();
        assert_eq!(d.consecutive(), 0);
    }

    #[test]
    fn rejects_zero_threshold() {
        assert!(matches!(
            Debounce::new(0),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }
}
