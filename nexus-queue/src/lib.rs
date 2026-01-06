use core::fmt;

pub mod spsc;

/// Error returned when the ring buffer is full.
///
/// Contains the value that could not be pushed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Full<T>(pub T);

impl<T> Full<T> {
    /// Returns the value that could not be pushed.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Display for Full<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ring buffer is full")
    }
}

impl<T: fmt::Debug> std::error::Error for Full<T> {}
