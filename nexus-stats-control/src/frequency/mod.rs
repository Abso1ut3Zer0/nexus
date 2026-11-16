//! Frequency counting and scoring.

mod flex_proportion;
#[cfg(feature = "alloc")]
mod topk;

#[cfg(any(feature = "std", feature = "libm"))]
mod decay_accum;

pub use flex_proportion::*;
#[cfg(feature = "alloc")]
pub use topk::*;

#[cfg(any(feature = "std", feature = "libm"))]
pub use decay_accum::*;
