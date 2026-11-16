/// Fixed-size sliding window of boolean outcomes.
///
/// Uses a heap-allocated array of `u64` words with incremental failure
/// tracking for O(1) rate queries.
///
/// The window size is specified at construction time. Internally allocates
/// `ceil(sample_count / 64)` words. Allocated once — no allocation after
/// construction.
///
/// # Use Cases
/// - "What fraction of the last 100 requests failed?"
/// - Sliding window success/failure rate
/// - Recent error ratio for circuit breaker input
///
/// Requires the `alloc` feature.
pub struct BoolWindow {
    bits: *mut u64,
    words: usize,
    capacity: usize,
    head: usize,
    count: u64,
    failures: u32,
}

// SAFETY: buffer is exclusively owned, u64 is Copy + Send
unsafe impl Send for BoolWindow {}

impl BoolWindow {
    #[inline]
    fn ring(&self) -> &[u64] {
        // SAFETY: buffer allocated with capacity `words`, all elements initialized
        unsafe { core::slice::from_raw_parts(self.bits, self.words) }
    }

    #[inline]
    fn ring_mut(&mut self) -> &mut [u64] {
        // SAFETY: buffer exclusively owned, all elements initialized
        unsafe { core::slice::from_raw_parts_mut(self.bits, self.words) }
    }

    /// Creates a new empty window with the given sample capacity.
    #[inline]
    pub fn new(sample_count: usize) -> Result<Self, nexus_stats_core::ConfigError> {
        if sample_count == 0 {
            return Err(nexus_stats_core::ConfigError::Invalid(
                "BoolWindow capacity must be > 0",
            ));
        }
        let words = sample_count.div_ceil(64);
        let mut vec = core::mem::ManuallyDrop::new(alloc::vec![0u64; words]);
        let bits = vec.as_mut_ptr();
        Ok(Self {
            bits,
            words,
            capacity: sample_count,
            head: 0,
            count: 0,
            failures: 0,
        })
    }

    /// Total capacity of the window in samples.
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Updates with an outcome. `true` = success, `false` = failure.
    #[inline]
    pub fn update(&mut self, success: bool) {
        let head = self.head;
        let capacity = self.capacity;
        let count = self.count;
        let word = head / 64;
        let bit = head % 64;
        let mask = 1u64 << bit;
        // SAFETY: buffer allocated with capacity `words`, all elements initialized, exclusively owned
        let bits = unsafe { core::slice::from_raw_parts_mut(self.bits, self.words) };
        let mut failures = self.failures;

        // Branchless eviction: decrement failures if evicting a failure bit
        let was_failure = ((bits[word] >> bit) & 1) as u32;
        if count >= capacity as u64 {
            failures -= was_failure;
        }

        // Branchless write: clear the bit, then conditionally set it
        let fail_bit = (!success) as u64;
        bits[word] = (bits[word] & !mask) | (fail_bit << bit);
        failures += fail_bit as u32;

        self.failures = failures;
        self.head = head + 1;
        if self.head == capacity {
            self.head = 0;
        }
        if count < capacity as u64 {
            self.count = count + 1;
        }
    }

    /// Failure rate over the window (0.0 to 1.0).
    #[inline]
    #[must_use]
    pub fn failure_rate(&self) -> f64 {
        if self.count == 0 {
            0.0
        } else {
            self.failures as f64 / self.count as f64
        }
    }

    /// Success rate over the window (0.0 to 1.0).
    #[inline]
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        1.0 - self.failure_rate()
    }

    /// Number of failures in the current window.
    #[inline]
    #[must_use]
    pub fn failures(&self) -> u32 {
        self.failures
    }

    /// Number of samples in the window.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the window is full.
    #[inline]
    #[must_use]
    pub fn is_full(&self) -> bool {
        self.count >= self.capacity as u64
    }

    /// Resets to empty state.
    #[inline]
    pub fn reset(&mut self) {
        self.ring_mut().fill(0);
        self.head = 0;
        self.count = 0;
        self.failures = 0;
    }
}

impl Drop for BoolWindow {
    fn drop(&mut self) {
        // SAFETY: buffer was allocated by Vec with capacity `words`.
        // u64 is Copy so no element drops needed. Reclaim the allocation.
        unsafe {
            let _ = alloc::vec::Vec::from_raw_parts(self.bits, 0, self.words);
        }
    }
}

impl Clone for BoolWindow {
    fn clone(&self) -> Self {
        let mut vec = alloc::vec![0u64; self.words];
        vec.copy_from_slice(self.ring());
        let mut cloned = core::mem::ManuallyDrop::new(vec);
        let bits = cloned.as_mut_ptr();
        Self {
            bits,
            words: self.words,
            capacity: self.capacity,
            head: self.head,
            count: self.count,
            failures: self.failures,
        }
    }
}

impl core::fmt::Debug for BoolWindow {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BoolWindow")
            .field("capacity", &self.capacity)
            .field("count", &self.count)
            .field("failures", &self.failures)
            .finish()
    }
}

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let bw = BoolWindow::new(64).unwrap();
        assert_eq!(bw.count(), 0);
        assert_eq!(bw.capacity(), 64);
        assert_eq!(bw.failure_rate(), 0.0);
        assert_eq!(bw.success_rate(), 1.0);
    }

    #[test]
    fn all_success() {
        let mut bw = BoolWindow::new(64).unwrap();
        for _ in 0..64 {
            bw.update(true);
        }
        assert_eq!(bw.failure_rate(), 0.0);
        assert_eq!(bw.failures(), 0);
    }

    #[test]
    fn all_failure() {
        let mut bw = BoolWindow::new(64).unwrap();
        for _ in 0..64 {
            bw.update(false);
        }
        assert_eq!(bw.failure_rate(), 1.0);
        assert_eq!(bw.failures(), 64);
    }

    #[test]
    fn half_and_half() {
        let mut bw = BoolWindow::new(64).unwrap();
        for i in 0..64 {
            bw.update(i % 2 == 0);
        }
        assert!((bw.failure_rate() - 0.5).abs() < 1e-10);
    }

    #[test]
    fn window_rolls() {
        let mut bw = BoolWindow::new(64).unwrap();
        for _ in 0..64 {
            bw.update(false);
        }
        assert_eq!(bw.failures(), 64);

        for _ in 0..64 {
            bw.update(true);
        }
        assert_eq!(bw.failures(), 0);
    }

    #[test]
    fn arbitrary_size() {
        let mut bw = BoolWindow::new(100).unwrap();
        assert_eq!(bw.capacity(), 100);

        for _ in 0..100 {
            bw.update(false);
        }
        assert_eq!(bw.failures(), 100);
        assert!(bw.is_full());

        for _ in 0..100 {
            bw.update(true);
        }
        assert_eq!(bw.failures(), 0);
    }

    #[test]
    fn priming() {
        let mut bw = BoolWindow::new(64).unwrap();
        bw.update(false);
        assert_eq!(bw.count(), 1);
        assert!(!bw.is_full());
        assert_eq!(bw.failure_rate(), 1.0);
    }

    #[test]
    fn reset() {
        let mut bw = BoolWindow::new(64).unwrap();
        for _ in 0..64 {
            bw.update(false);
        }
        bw.reset();
        assert_eq!(bw.count(), 0);
        assert_eq!(bw.failures(), 0);
    }

    #[test]
    fn rejects_zero_capacity() {
        assert!(matches!(
            BoolWindow::new(0),
            Err(nexus_stats_core::ConfigError::Invalid(_))
        ));
    }
}
