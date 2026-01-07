//! Error types for bit field operations.

/// Value exceeds field capacity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Overflow<T> {
    /// The value that was too large.
    pub value: T,
    /// Maximum value the field can hold.
    pub max: T,
}

impl<T: core::fmt::Display> core::fmt::Display for Overflow<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "value {} exceeds max {}", self.value, self.max)
    }
}
