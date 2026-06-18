/// Liveness detector (integer variant) — fixed-point EMA of inter-arrival ticks.
///
/// Uses kernel-style bit-shift arithmetic for the interval smoothing.
/// Timestamps are integer ticks.
#[derive(Debug, Clone)]
pub struct LivenessI64 {
    acc: i128,
    shift: u32,
    span: u64,
    last_timestamp: i64,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<i64>,
    count: u64,
    min_samples: u64,
    initialized: bool,
}

/// Builder for [`LivenessI64`].
#[derive(Debug, Clone)]
pub struct LivenessI64Builder {
    span: Option<u64>,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<i64>,
    min_samples: u64,
}

impl LivenessI64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LivenessI64Builder {
        LivenessI64Builder {
            span: None,
            deadline_multiple: None,
            deadline_absolute: None,
            min_samples: 2,
        }
    }

    /// Updates with an event at the given tick. Returns `true` if alive.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: i64) -> bool {
        self.count += 1;

        if self.count == 1 {
            self.last_timestamp = timestamp;
            return true;
        }

        let dt = timestamp - self.last_timestamp;
        self.last_timestamp = timestamp;

        if self.initialized {
            let dt_shifted = (dt as i128) << self.shift;
            self.acc += (dt_shifted - self.acc) >> self.shift;
        } else {
            self.acc = (dt as i128) << self.shift;
            self.initialized = true;
        }

        if self.count < self.min_samples {
            return true;
        }

        let smoothed = (self.acc >> self.shift) as i64;
        self.is_alive_with(dt, smoothed)
    }

    /// Checks liveness at the given tick without recording.
    #[inline]
    #[must_use]
    pub fn check(&self, now: i64) -> bool {
        if self.count < self.min_samples || !self.initialized {
            return true;
        }

        let dt = now - self.last_timestamp;
        let smoothed = (self.acc >> self.shift) as i64;
        self.is_alive_with(dt, smoothed)
    }

    #[inline]
    fn is_alive_with(&self, dt: i64, smoothed: i64) -> bool {
        if let Some(multiple) = self.deadline_multiple {
            return dt <= smoothed * (multiple as i64);
        }
        if let Some(absolute) = self.deadline_absolute {
            return dt <= absolute;
        }
        true
    }

    /// Current smoothed inter-arrival interval, or `None` if < 2 events.
    #[inline]
    #[must_use]
    pub fn interval(&self) -> Option<i64> {
        if self.count >= 2 && self.initialized {
            Some((self.acc >> self.shift) as i64)
        } else {
            None
        }
    }

    /// Effective span after rounding.
    #[inline]
    #[must_use]
    pub fn effective_span(&self) -> u64 {
        self.span
    }

    /// Number of events recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the detector has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.acc = 0;
        self.last_timestamp = 0;
        self.count = 0;
        self.initialized = false;
    }
}

impl LivenessI64Builder {
    /// Smoothing span. Rounded up to next `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.span = Some(n);
        self
    }

    /// Alert when interval exceeds `n * smoothed_interval`.
    #[inline]
    #[must_use]
    pub fn deadline_multiple(mut self, n: u64) -> Self {
        self.deadline_multiple = Some(n);
        self
    }

    /// Alert when interval exceeds a fixed deadline (in ticks).
    #[inline]
    #[must_use]
    pub fn deadline_absolute(mut self, t: i64) -> Self {
        self.deadline_absolute = Some(t);
        self
    }

    /// Minimum events before liveness checking activates. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the liveness detector.
    ///
    /// # Errors
    ///
    /// - Span must have been set and >= 1.
    /// - At least one deadline must be set.
    #[inline]
    pub fn build(self) -> Result<LivenessI64, crate::ConfigError> {
        let requested = self.span.ok_or(crate::ConfigError::Missing("span"))?;
        if requested < 1 {
            return Err(crate::ConfigError::Invalid("Liveness span must be >= 1"));
        }
        if self.deadline_multiple.is_none() && self.deadline_absolute.is_none() {
            return Err(crate::ConfigError::Invalid("Liveness requires a deadline"));
        }

        let effective = crate::smoothing::ema::next_power_of_two_minus_one(requested);
        let shift = crate::smoothing::ema::log2_of_span_plus_one(effective);

        Ok(LivenessI64 {
            acc: 0,
            shift,
            span: effective,
            last_timestamp: 0,
            deadline_multiple: self.deadline_multiple,
            deadline_absolute: self.deadline_absolute,
            count: 0,
            min_samples: self.min_samples,
            initialized: false,
        })
    }
}

/// Liveness detector (integer variant) — fixed-point EMA of inter-arrival ticks.
///
/// Uses kernel-style bit-shift arithmetic for the interval smoothing.
/// Timestamps are integer ticks.
#[derive(Debug, Clone)]
pub struct LivenessU64 {
    acc: i128,
    shift: u32,
    span: u64,
    last_timestamp: u64,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<u64>,
    count: u64,
    min_samples: u64,
    initialized: bool,
}

/// Builder for [`LivenessU64`].
#[derive(Debug, Clone)]
pub struct LivenessU64Builder {
    span: Option<u64>,
    deadline_multiple: Option<u64>,
    deadline_absolute: Option<u64>,
    min_samples: u64,
}

impl LivenessU64 {
    /// Creates a builder.
    #[inline]
    #[must_use]
    pub fn builder() -> LivenessU64Builder {
        LivenessU64Builder {
            span: None,
            deadline_multiple: None,
            deadline_absolute: None,
            min_samples: 2,
        }
    }

    /// Updates with an event at the given tick. Returns `true` if alive.
    #[inline]
    #[must_use]
    pub fn update(&mut self, timestamp: u64) -> bool {
        self.count += 1;

        if self.count == 1 {
            self.last_timestamp = timestamp;
            return true;
        }

        let dt = timestamp.wrapping_sub(self.last_timestamp) as i64;
        self.last_timestamp = timestamp;

        if self.initialized {
            let dt_shifted = (dt as i128) << self.shift;
            self.acc += (dt_shifted - self.acc) >> self.shift;
        } else {
            self.acc = (dt as i128) << self.shift;
            self.initialized = true;
        }

        if self.count < self.min_samples {
            return true;
        }

        let smoothed = (self.acc >> self.shift) as i64;
        self.is_alive_with(dt, smoothed)
    }

    /// Checks liveness at the given tick without recording.
    #[inline]
    #[must_use]
    pub fn check(&self, now: u64) -> bool {
        if self.count < self.min_samples || !self.initialized {
            return true;
        }

        let dt = now.wrapping_sub(self.last_timestamp) as i64;
        let smoothed = (self.acc >> self.shift) as i64;
        self.is_alive_with(dt, smoothed)
    }

    #[inline]
    fn is_alive_with(&self, dt: i64, smoothed: i64) -> bool {
        if let Some(multiple) = self.deadline_multiple {
            return dt <= smoothed * (multiple as i64);
        }
        if let Some(absolute) = self.deadline_absolute {
            return dt >= 0 && (dt as u64) <= absolute;
        }
        true
    }

    /// Current smoothed inter-arrival interval, or `None` if < 2 events.
    #[inline]
    #[must_use]
    pub fn interval(&self) -> Option<i64> {
        if self.count >= 2 && self.initialized {
            Some((self.acc >> self.shift) as i64)
        } else {
            None
        }
    }

    /// Effective span after rounding.
    #[inline]
    #[must_use]
    pub fn effective_span(&self) -> u64 {
        self.span
    }

    /// Number of events recorded.
    #[inline]
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Whether the detector has reached `min_samples`.
    #[inline]
    #[must_use]
    pub fn is_primed(&self) -> bool {
        self.count >= self.min_samples
    }

    /// Resets to uninitialized state.
    #[inline]
    pub fn reset(&mut self) {
        self.acc = 0;
        self.last_timestamp = 0;
        self.count = 0;
        self.initialized = false;
    }
}

impl LivenessU64Builder {
    /// Smoothing span. Rounded up to next `2^k - 1`.
    #[inline]
    #[must_use]
    pub fn span(mut self, n: u64) -> Self {
        self.span = Some(n);
        self
    }

    /// Alert when interval exceeds `n * smoothed_interval`.
    #[inline]
    #[must_use]
    pub fn deadline_multiple(mut self, n: u64) -> Self {
        self.deadline_multiple = Some(n);
        self
    }

    /// Alert when interval exceeds a fixed deadline (in ticks).
    #[inline]
    #[must_use]
    pub fn deadline_absolute(mut self, t: u64) -> Self {
        self.deadline_absolute = Some(t);
        self
    }

    /// Minimum events before liveness checking activates. Default: 2.
    #[inline]
    #[must_use]
    pub fn min_samples(mut self, min: u64) -> Self {
        self.min_samples = min;
        self
    }

    /// Builds the liveness detector.
    ///
    /// # Errors
    ///
    /// - Span must have been set and >= 1.
    /// - At least one deadline must be set.
    #[inline]
    pub fn build(self) -> Result<LivenessU64, crate::ConfigError> {
        let requested = self.span.ok_or(crate::ConfigError::Missing("span"))?;
        if requested < 1 {
            return Err(crate::ConfigError::Invalid("Liveness span must be >= 1"));
        }
        if self.deadline_multiple.is_none() && self.deadline_absolute.is_none() {
            return Err(crate::ConfigError::Invalid("Liveness requires a deadline"));
        }

        let effective = crate::smoothing::ema::next_power_of_two_minus_one(requested);
        let shift = crate::smoothing::ema::log2_of_span_plus_one(effective);

        Ok(LivenessU64 {
            acc: 0,
            shift,
            span: effective,
            last_timestamp: 0,
            deadline_multiple: self.deadline_multiple,
            deadline_absolute: self.deadline_absolute,
            count: 0,
            min_samples: self.min_samples,
            initialized: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alive_while_events_arrive_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..20 {
            assert!(lv.update(i * 10), "should be alive at event {i}");
        }
    }

    #[test]
    fn dead_after_silence_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..10 {
            let _ = lv.update(i as u64 * 10);
        }

        // Check after long silence — should be dead
        // Smoothed interval ~= 10, deadline = 3 * 10 = 30, silence = 100
        assert!(!lv.check(190), "should be dead after long silence");
    }

    #[test]
    fn recovery_after_resume_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as u64 * 10);
        }

        // Dead check
        assert!(!lv.check(200));

        // Resume events — should recover
        assert!(!lv.update(200)); // records, interval updates
        assert!(lv.update(210));
    }

    #[test]
    fn absolute_deadline_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_absolute(50)
            .build()
            .unwrap();

        let _ = lv.update(0);
        let _ = lv.update(10);

        // Within deadline
        assert!(lv.check(55));
        // Exceeds deadline
        assert!(!lv.check(65));
    }

    #[test]
    fn not_primed_always_alive_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .min_samples(5)
            .build()
            .unwrap();

        // Even with huge gaps, returns true before primed
        assert!(lv.update(0));
        assert!(lv.update(1000));
        assert!(!lv.is_primed());
    }

    #[test]
    fn i64_basic() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            assert!(lv.update(i * 100));
        }

        // Long silence
        assert!(!lv.check(2000));
    }

    #[test]
    fn reset_clears_state_u64() {
        let mut lv = LivenessU64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as u64 * 10);
        }

        lv.reset();
        assert_eq!(lv.count(), 0);
        assert!(lv.interval().is_none());
    }

    #[test]
    fn errors_without_span_u64() {
        let result = LivenessU64::builder().deadline_multiple(3).build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("span"))));
    }

    #[test]
    fn errors_without_deadline_u64() {
        let result = LivenessU64::builder().span(7).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }

    #[test]
    fn alive_while_events_arrive_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..20 {
            assert!(lv.update(i * 10), "should be alive at event {i}");
        }
    }

    #[test]
    fn dead_after_silence_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        // Regular events every 10 units
        for i in 0..10 {
            let _ = lv.update(i as i64 * 10);
        }

        // Check after long silence — should be dead
        // Smoothed interval ~= 10, deadline = 3 * 10 = 30, silence = 100
        assert!(!lv.check(190), "should be dead after long silence");
    }

    #[test]
    fn recovery_after_resume_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as i64 * 10);
        }

        // Dead check
        assert!(!lv.check(200));

        // Resume events — should recover
        assert!(!lv.update(200)); // records, interval updates
        assert!(lv.update(210));
    }

    #[test]
    fn absolute_deadline_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_absolute(50)
            .build()
            .unwrap();

        let _ = lv.update(0);
        let _ = lv.update(10);

        // Within deadline
        assert!(lv.check(55));
        // Exceeds deadline
        assert!(!lv.check(65));
    }

    #[test]
    fn not_primed_always_alive_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .min_samples(5)
            .build()
            .unwrap();

        // Even with huge gaps, returns true before primed
        assert!(lv.update(0));
        assert!(lv.update(1000));
        assert!(!lv.is_primed());
    }

    #[test]
    fn reset_clears_state_i64() {
        let mut lv = LivenessI64::builder()
            .span(7)
            .deadline_multiple(3)
            .build()
            .unwrap();

        for i in 0..10 {
            let _ = lv.update(i as i64 * 10);
        }

        lv.reset();
        assert_eq!(lv.count(), 0);
        assert!(lv.interval().is_none());
    }

    #[test]
    fn errors_without_span_i64() {
        let result = LivenessI64::builder().deadline_multiple(3).build();
        assert!(matches!(result, Err(crate::ConfigError::Missing("span"))));
    }

    #[test]
    fn errors_without_deadline_i64() {
        let result = LivenessI64::builder().span(7).build();
        assert!(matches!(result, Err(crate::ConfigError::Invalid(_))));
    }
}
