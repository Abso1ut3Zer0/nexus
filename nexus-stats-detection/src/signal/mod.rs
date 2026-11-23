//! Signal analysis and information theory.

#[cfg(feature = "alloc")]
mod autocorrelation;
#[cfg(feature = "alloc")]
mod cross_correlation;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod entropy;
#[cfg(any(feature = "std", feature = "libm"))]
mod half_life;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod hurst;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod predictive_info;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod transfer_entropy;

#[cfg(feature = "alloc")]
pub use autocorrelation::*;
#[cfg(feature = "alloc")]
pub use cross_correlation::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use entropy::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use half_life::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use hurst::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use predictive_info::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use transfer_entropy::*;
