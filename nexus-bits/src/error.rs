// nexus-bits/src/error.rs

//! Error types for bit field operations.

use core::fmt;

/// Value exceeds field capacity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Overflow<T> {
    /// The value that was too large.
    pub value: T,
    /// Maximum value the field can hold.
    pub max: T,
}

impl<T: fmt::Display> fmt::Display for Overflow<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "value {} exceeds max {}", self.value, self.max)
    }
}

/// Field overflow during pack with field name context.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldOverflow<T> {
    /// Field name that overflowed.
    pub field: &'static str,
    /// The overflow details.
    pub overflow: Overflow<T>,
}

impl<T: fmt::Display> fmt::Display for FieldOverflow<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "field '{}': {}", self.field, self.overflow)
    }
}

/// Unknown discriminant during tagged enum unpack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnknownDiscriminant<T> {
    /// The discriminant value that wasn't recognized.
    pub value: T,
}

impl<T: fmt::Display> fmt::Display for UnknownDiscriminant<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown discriminant: {}", self.value)
    }
}

/// Unknown enum variant value during struct field unpack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnknownVariant<T> {
    /// Field name with unknown variant.
    pub field: &'static str,
    /// The value that didn't map to a variant.
    pub value: T,
}

impl<T: fmt::Display> fmt::Display for UnknownVariant<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "field '{}': unknown variant value {}",
            self.field, self.value
        )
    }
}
