/// Writes an interval type: two ends, both included, and the readers the
/// three kinds share. Each kind is its own type, so a signature says which
/// it means.
macro_rules! interval {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        ///
        /// Both ends are part of the range.
        #[derive(Debug, Clone, Copy, PartialEq)]
        pub struct $name {
            lower: f64,
            upper: f64,
        }

        impl $name {
            /// The range from `lower` to `upper`. It holds what it is
            /// given: nothing is checked.
            #[inline]
            #[must_use]
            pub const fn new(lower: f64, upper: f64) -> Self {
                Self { lower, upper }
            }

            /// The lower end.
            #[inline]
            #[must_use]
            pub const fn lower(&self) -> f64 {
                self.lower
            }

            /// The upper end.
            #[inline]
            #[must_use]
            pub const fn upper(&self) -> f64 {
                self.upper
            }

            /// `upper - lower`.
            #[inline]
            #[must_use]
            pub fn width(&self) -> f64 {
                self.upper - self.lower
            }

            /// Half of the width: the distance from the midpoint to
            /// either end.
            #[inline]
            #[must_use]
            pub fn half_width(&self) -> f64 {
                0.5 * self.width()
            }

            /// The point halfway between the ends. It is not the estimate:
            /// these ranges reach further on one side of it than the other.
            #[inline]
            #[must_use]
            pub fn midpoint(&self) -> f64 {
                0.5 * (self.lower + self.upper)
            }

            /// Whether `x` is in the range, `lower <= x <= upper`. A value
            /// on an end is inside. NaN never is.
            #[inline]
            #[must_use]
            pub fn contains(&self, x: f64) -> bool {
                self.lower <= x && x <= self.upper
            }

            /// Whether either end is NaN, which it is when the estimator
            /// was fed something that is not a number.
            #[inline]
            #[must_use]
            pub const fn is_nan(&self) -> bool {
                self.lower.is_nan() || self.upper.is_nan()
            }
        }
    };
}

interval! {
    /// The range a fitted parameter lies in with a stated probability, given
    /// the prior and the data.
    CredibleInterval
}

interval! {
    /// The range the data alone supports for a parameter, with no prior: the
    /// classical interval, built to hold the true value at the stated rate
    /// over repeated samples.
    ConfidenceInterval
}

interval! {
    /// The range a count not yet seen will fall in with a stated probability,
    /// from a model whose parameters are known.
    PredictionInterval
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_ends_are_inside_and_nan_is_not() {
        let interval = PredictionInterval::new(74.0, 111.0);
        assert!(interval.contains(74.0) && interval.contains(111.0) && interval.contains(90.0));
        assert!(!interval.contains(73.999) && !interval.contains(111.001));
        assert!(!interval.contains(f64::NAN));
    }

    #[test]
    fn the_midpoint_and_half_width_rebuild_the_ends() {
        let interval = CredibleInterval::new(2.0, 5.0);
        assert_eq!((interval.lower(), interval.upper()), (2.0, 5.0));
        assert_eq!(
            (interval.width(), interval.half_width(), interval.midpoint()),
            (3.0, 1.5, 3.5)
        );
    }

    /// A NaN at either end marks the interval, and nothing is inside it.
    #[test]
    fn an_interval_with_a_nan_end_says_so() {
        assert!(!ConfidenceInterval::new(0.0, 1.0).is_nan());
        for interval in [
            ConfidenceInterval::new(f64::NAN, 1.0),
            ConfidenceInterval::new(0.0, f64::NAN),
        ] {
            assert!(interval.is_nan());
            assert!(!interval.contains(0.5));
        }
    }
}
