use crate::ConfigError;

/// A probability: a number from 0 to 1, both included.
///
/// It is checked once, where it is made. A method that takes a
/// `Probability` cannot be handed a bad value, and does no check of its
/// own on each call. [`value`](Self::value) or `f64::from` gives the
/// number back.
///
/// # Examples
///
/// In a `const`, the value is checked when the program is compiled:
///
/// ```
/// use nexus_stats_core::Probability;
///
/// const ONE_IN_FOUR: Probability = Probability::new(0.25);
/// assert_eq!(ONE_IN_FOUR.value(), 0.25);
/// assert_eq!(f64::from(ONE_IN_FOUR), 0.25);
/// ```
///
/// A value that is out of range does not compile there:
///
/// ```compile_fail
/// use nexus_stats_core::Probability;
///
/// const BAD: Probability = Probability::new(1.5);
/// ```
///
/// For a value that arrives at run time use the checked form, or
/// `TryFrom`:
///
/// ```
/// use nexus_stats_core::Probability;
///
/// let from_config = 0.99;
/// let probability = Probability::checked_new(from_config)?;
/// assert_eq!(Probability::try_from(0.99)?, probability);
/// assert!(Probability::checked_new(-0.1).is_err());
/// # Ok::<(), nexus_stats_core::ConfigError>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Probability(f64);

impl Probability {
    /// A probability of `value`.
    ///
    /// # Panics
    ///
    /// If `value` is not from 0 to 1, NaN included. In a `const` that is
    /// an error at compile time.
    #[must_use]
    pub const fn new(value: f64) -> Self {
        assert!(Self::is_valid(value), "probability must be from 0 to 1");
        // `-0.0 + 0.0` is `0.0`.
        Self(value + 0.0)
    }

    /// A probability of `value`, for a value known only at run time.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` if `value` is not from 0 to 1, NaN included.
    pub const fn checked_new(value: f64) -> Result<Self, ConfigError> {
        if !Self::is_valid(value) {
            return Err(ConfigError::Invalid("probability must be from 0 to 1"));
        }
        Ok(Self(value + 0.0))
    }

    /// The number, from 0 to 1.
    #[inline]
    #[must_use]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// NaN fails both comparisons.
    const fn is_valid(value: f64) -> bool {
        value >= 0.0 && value <= 1.0
    }
}

impl From<Probability> for f64 {
    /// The number.
    #[inline]
    fn from(probability: Probability) -> Self {
        probability.0
    }
}

impl TryFrom<f64> for Probability {
    type Error = ConfigError;

    /// As [`Probability::checked_new`].
    #[inline]
    fn try_from(value: f64) -> Result<Self, ConfigError> {
        Self::checked_new(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Checked when this is compiled.
    const CERTAIN: Probability = Probability::new(1.0);

    #[test]
    fn the_ends_are_probabilities() {
        assert_eq!(CERTAIN.value(), 1.0);
        assert_eq!(Probability::new(0.0).value(), 0.0);
        assert!(Probability::checked_new(0.0).is_ok() && Probability::checked_new(1.0).is_ok());
    }

    #[test]
    fn checked_new_refuses_what_is_not_a_probability() {
        for bad in [-0.1, 1.000_000_1, f64::NAN, f64::INFINITY, -f64::INFINITY] {
            assert!(Probability::checked_new(bad).is_err(), "{bad}");
            assert!(Probability::try_from(bad).is_err(), "{bad}");
        }
    }

    #[test]
    #[should_panic(expected = "probability must be from 0 to 1")]
    fn new_panics_on_a_bad_value() {
        let _ = Probability::new(core::hint::black_box(1.5));
    }

    #[test]
    fn a_negative_zero_is_kept_as_zero() {
        assert!(Probability::new(-0.0).value().is_sign_positive());
        assert!(
            Probability::checked_new(-0.0)
                .unwrap()
                .value()
                .is_sign_positive()
        );
    }

    #[test]
    fn it_converts_to_and_from_f64() {
        assert_eq!(f64::from(Probability::new(0.3)), 0.3);
        assert_eq!(Probability::try_from(0.3), Ok(Probability::new(0.3)));
    }
}
