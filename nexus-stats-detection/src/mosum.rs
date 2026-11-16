use nexus_stats_core::Direction;

/// Generates the MOSUM update method — float variant validates input,
/// integer variant passes through without validation.
#[cfg(feature = "alloc")]
macro_rules! impl_mosum_update {
    (float, $ty:ty) => {
        /// Feeds a sample. Returns shift direction once primed.
        ///
        /// # Errors
        ///
        /// Returns `DataError::NotANumber` if the sample is NaN, or
        /// `DataError::Infinite` if the sample is infinite.
        #[inline]
        pub fn update(
            &mut self,
            sample: $ty,
        ) -> Result<Option<Direction>, nexus_stats_core::DataError> {
            check_finite!(sample);
            let target = self.target;
            let head = self.head;
            let window = self.window;
            let sum = self.sum;
            let deviation = sample - target;
            let ring = self.ring_mut();
            let new_sum = sum - ring[head] + deviation;
            ring[head] = deviation;
            self.sum = new_sum;
            self.head = head + 1;
            if self.head == window {
                self.head = 0;
            }
            self.count += 1;

            if self.count < self.min_samples {
                return Ok(Option::None);
            }
            Ok(if self.sum > self.threshold {
                Option::Some(Direction::Rising)
            } else if self.sum < -self.threshold {
                Option::Some(Direction::Falling)
            } else {
                Option::Some(Direction::Neutral)
            })
        }
    };
}

#[cfg(feature = "alloc")]
macro_rules! impl_mosum {
    ($name:ident, $builder:ident, $ty:ty, $kind:tt, $zero:expr) => {
        /// MOSUM — Moving Sum change detector.
        ///
        /// Windowed complement to CUSUM. Detects transient shifts (spikes)
        /// rather than persistent shifts. Uses a ring buffer of deviations
        /// from target and tests whether their sum exceeds a threshold.
        ///
        /// The ring buffer is heap-allocated once during `build()` — no
        /// allocation after construction.
        ///
        /// Requires the `alloc` feature.
        pub struct $name {
            target: $ty,
            threshold: $ty,
            buffer: *mut $ty,
            window: usize,
            head: usize,
            sum: $ty,
            count: u64,
            min_samples: u64,
        }

        // SAFETY: buffer is exclusively owned, T is Copy + Send
        unsafe impl Send for $name {}

        impl $name {
            #[inline]
            fn ring(&self) -> &[$ty] {
                // SAFETY: buffer allocated with capacity `window`, all elements initialized
                unsafe { core::slice::from_raw_parts(self.buffer, self.window) }
            }

            #[inline]
            fn ring_mut(&mut self) -> &mut [$ty] {
                // SAFETY: buffer exclusively owned, all elements initialized
                unsafe { core::slice::from_raw_parts_mut(self.buffer, self.window) }
            }
        }

        /// Builder for [`
        #[doc = stringify!($name)]
        /// `].
        #[derive(Debug, Clone)]
        pub struct $builder {
            target: $ty,
            window: Option<usize>,
            threshold: Option<$ty>,
            min_samples: Option<u64>,
        }

        impl $name {
            /// Creates a builder with the target (expected baseline mean).
            #[inline]
            #[must_use]
            pub fn builder(target: $ty) -> $builder {
                $builder {
                    target,
                    window: Option::None,
                    threshold: Option::None,
                    min_samples: Option::None,
                }
            }

            impl_mosum_update!($kind, $ty);

            /// Current moving sum of deviations.
            #[inline]
            #[must_use]
            pub fn sum(&self) -> $ty { self.sum }

            /// Window size.
            #[inline]
            #[must_use]
            pub fn window_size(&self) -> usize { self.window }

            /// Number of samples processed.
            #[inline]
            #[must_use]
            pub fn count(&self) -> u64 { self.count }

            /// Whether the window is full and detection is active.
            #[inline]
            #[must_use]
            pub fn is_primed(&self) -> bool { self.count >= self.min_samples }

            /// Resets to empty state. Parameters unchanged.
            #[inline]
            pub fn reset(&mut self) {
                self.ring_mut().fill($zero);
                self.head = 0;
                self.sum = $zero;
                self.count = 0;
            }
        }

        impl Drop for $name {
            fn drop(&mut self) {
                // SAFETY: buffer was allocated by Vec::with_capacity(window).
                // T is Copy so no element drops needed. Reclaim the allocation.
                unsafe {
                    let _ = alloc::vec::Vec::from_raw_parts(self.buffer, 0, self.window);
                }
            }
        }

        impl Clone for $name {
            fn clone(&self) -> Self {
                let mut vec = alloc::vec![$zero; self.window];
                vec.copy_from_slice(self.ring());
                let mut cloned = core::mem::ManuallyDrop::new(vec);
                let buffer = cloned.as_mut_ptr();
                Self {
                    target: self.target,
                    threshold: self.threshold,
                    buffer,
                    window: self.window,
                    head: self.head,
                    sum: self.sum,
                    count: self.count,
                    min_samples: self.min_samples,
                }
            }
        }

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($name))
                    .field("window", &self.window)
                    .field("count", &self.count)
                    .field("sum", &self.sum)
                    .finish()
            }
        }

        impl $builder {
            /// Window size (number of samples in the ring buffer).
            #[inline]
            #[must_use]
            pub fn window_size(mut self, n: usize) -> Self {
                self.window = Option::Some(n);
                self
            }

            /// Decision threshold.
            #[inline]
            #[must_use]
            pub fn threshold(mut self, threshold: $ty) -> Self {
                self.threshold = Option::Some(threshold);
                self
            }

            /// Minimum samples before detection activates. Default: window size.
            #[inline]
            #[must_use]
            pub fn min_samples(mut self, min: u64) -> Self {
                self.min_samples = Option::Some(min);
                self
            }

            /// Builds the MOSUM detector.
            ///
            /// # Errors
            ///
            /// - Window size must have been set and > 0.
            /// - Threshold must have been set and positive.
            #[inline]
            pub fn build(self) -> Result<$name, nexus_stats_core::ConfigError> {
                let window = self.window.ok_or(nexus_stats_core::ConfigError::Missing("window_size"))?;
                if window == 0 {
                    return Err(nexus_stats_core::ConfigError::Invalid("window_size must be > 0"));
                }
                let threshold = self.threshold.ok_or(nexus_stats_core::ConfigError::Missing("threshold"))?;
                if threshold <= $zero {
                    return Err(nexus_stats_core::ConfigError::Invalid("threshold must be positive"));
                }
                let min_samples = self.min_samples.unwrap_or(window as u64);

                let mut vec = core::mem::ManuallyDrop::new(alloc::vec![$zero; window]);
                let buffer = vec.as_mut_ptr();

                Ok($name {
                    target: self.target,
                    threshold,
                    buffer,
                    window,
                    head: 0,
                    sum: $zero,
                    count: 0,
                    min_samples,
                })
            }
        }
    };
}

#[cfg(feature = "alloc")]
impl_mosum!(Mosum, MosumBuilder, f64, float, 0.0);
#[cfg(feature = "alloc")]
#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn no_detection_at_target() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = mosum.update(100.0);
        }
        for _ in 0..100 {
            assert_eq!(mosum.update(100.0).unwrap(), Some(Direction::Neutral));
        }
    }

    #[test]
    fn detects_upward_spike() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..10 {
            let _ = mosum.update(100.0);
        }

        let mut triggered = false;
        for _ in 0..10 {
            if mosum.update(110.0).unwrap() == Some(Direction::Rising) {
                triggered = true;
                break;
            }
        }
        assert!(triggered, "should detect upward spike");
    }

    #[test]
    fn transient_clears_after_window() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(5)
            .threshold(40.0)
            .build()
            .unwrap();

        for _ in 0..5 {
            let _ = mosum.update(100.0);
        }
        for _ in 0..5 {
            let _ = mosum.update(120.0);
        }
        for _ in 0..5 {
            let _ = mosum.update(100.0);
        }
        assert!(
            mosum.sum().abs() < 1e-10,
            "sum should return to ~0, got {}",
            mosum.sum()
        );
    }

    #[test]
    #[allow(clippy::float_cmp)]
    fn reset_clears_state() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..20 {
            let _ = mosum.update(120.0);
        }
        mosum.reset();
        assert_eq!(mosum.count(), 0);
        assert_eq!(mosum.sum(), 0.0);
    }

    #[test]
    fn clone_works() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(5)
            .threshold(50.0)
            .build()
            .unwrap();

        for _ in 0..5 {
            let _ = mosum.update(110.0);
        }

        let cloned = mosum.clone();
        assert_eq!(cloned.count(), mosum.count());
        assert_eq!(cloned.sum(), mosum.sum());
    }

    #[test]
    fn errors_without_threshold() {
        let result = Mosum::builder(100.0).window_size(10).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("threshold"))
        ));
    }

    #[test]
    fn errors_without_window() {
        let result = Mosum::builder(100.0).threshold(50.0).build();
        assert!(matches!(
            result,
            Err(nexus_stats_core::ConfigError::Missing("window_size"))
        ));
    }

    #[test]
    fn rejects_nan_and_inf() {
        let mut mosum = Mosum::builder(100.0)
            .window_size(10)
            .threshold(50.0)
            .build()
            .unwrap();

        assert_eq!(
            mosum.update(f64::NAN).unwrap_err(),
            nexus_stats_core::DataError::NotANumber
        );
        assert_eq!(
            mosum.update(f64::INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(
            mosum.update(f64::NEG_INFINITY).unwrap_err(),
            nexus_stats_core::DataError::Infinite
        );
        assert_eq!(mosum.count(), 0);
    }
}
