use crate::ConfigError;

/// The confidence of an interval: a probability strictly between 0 and 1.
///
/// It is checked once, where it is made. A method that takes a
/// `Confidence` cannot be handed a bad level, and does no check of its own
/// on each call.
///
/// # Examples
///
/// In a `const`, the level is checked when the program is compiled:
///
/// ```
/// use nexus_stats_core::Confidence;
///
/// const NINETY_FIVE: Confidence = Confidence::new(0.95);
/// assert_eq!(NINETY_FIVE.level(), 0.95);
/// ```
///
/// A level that is out of range does not compile there:
///
/// ```compile_fail
/// use nexus_stats_core::Confidence;
///
/// const BAD: Confidence = Confidence::new(1.5);
/// ```
///
/// For a level that arrives at run time, from a configuration file say,
/// use the checked form:
///
/// ```
/// use nexus_stats_core::Confidence;
///
/// let from_config = 0.99;
/// let confidence = Confidence::checked_new(from_config)?;
/// assert!(Confidence::checked_new(1.0).is_err());
/// # Ok::<(), nexus_stats_core::ConfigError>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Confidence(f64);

impl Confidence {
    /// A confidence of `level`.
    ///
    /// # Panics
    ///
    /// If `level` is not strictly between 0 and 1, NaN included. In a
    /// `const` that is an error at compile time.
    #[must_use]
    pub const fn new(level: f64) -> Self {
        assert!(
            Self::is_valid(level),
            "confidence must be strictly between 0 and 1"
        );
        Self(level)
    }

    /// A confidence of `level`, for a level known only at run time.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `level` is not strictly between 0 and 1,
    /// NaN included.
    pub const fn checked_new(level: f64) -> Result<Self, ConfigError> {
        if !Self::is_valid(level) {
            return Err(ConfigError::Invalid(
                "confidence must be strictly between 0 and 1",
            ));
        }
        Ok(Self(level))
    }

    /// The level, strictly between 0 and 1.
    #[inline]
    #[must_use]
    pub const fn level(self) -> f64 {
        self.0
    }

    /// The probability an equal-tailed interval leaves outside at each
    /// end: `(1 - level) / 2`. Above zero and below one half.
    #[inline]
    #[must_use]
    pub const fn tail(self) -> f64 {
        (1.0 - self.0) / 2.0
    }

    /// NaN fails both comparisons.
    const fn is_valid(level: f64) -> bool {
        level > 0.0 && level < 1.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_level_inside_the_range_is_kept() {
        for level in [
            f64::from_bits(1),
            1e-300,
            0.5,
            0.95,
            1.0 - f64::EPSILON / 2.0,
        ] {
            assert_eq!(Confidence::new(level).level(), level);
            assert_eq!(Confidence::checked_new(level), Ok(Confidence::new(level)));
        }
    }

    #[test]
    fn checked_new_refuses_a_level_outside_the_range() {
        for level in [
            0.0,
            -0.0,
            1.0,
            1.5,
            -0.1,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            assert!(Confidence::checked_new(level).is_err(), "{level}");
        }
    }

    #[test]
    #[should_panic(expected = "confidence must be strictly between 0 and 1")]
    fn new_refuses_a_level_of_one() {
        let _ = Confidence::new(std::hint::black_box(1.0));
    }

    #[test]
    #[should_panic(expected = "confidence must be strictly between 0 and 1")]
    fn new_refuses_a_level_that_is_not_a_number() {
        let _ = Confidence::new(std::hint::black_box(f64::NAN));
    }

    /// Usable in a `const`, where a bad level would not compile.
    #[test]
    fn it_is_usable_in_a_const() {
        const NINETY_FIVE: Confidence = Confidence::new(0.95);
        const TAIL: f64 = NINETY_FIVE.tail();
        assert_eq!((NINETY_FIVE.level(), TAIL), (0.95, (1.0 - 0.95) / 2.0));
    }

    /// The tail is above zero and below one half for every level, the
    /// ones a rounding step from either end included.
    #[test]
    fn the_tail_is_strictly_between_zero_and_one_half() {
        for level in [
            f64::from_bits(1),
            1e-300,
            0.5,
            0.999_999,
            1.0 - f64::EPSILON / 2.0,
        ] {
            let tail = Confidence::new(level).tail();
            assert!(tail > 0.0 && tail <= 0.5, "{level}: {tail}");
        }
        assert_eq!(Confidence::new(0.5).tail(), 0.25);
        // The closest level to one leaves a tail of 2^-54.
        assert_eq!(
            Confidence::new(1.0 - f64::EPSILON / 2.0).tail(),
            0.5_f64.powi(54)
        );
    }
}
