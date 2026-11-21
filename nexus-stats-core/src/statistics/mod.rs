//! Core streaming statistics.

mod amihud;
#[cfg(any(feature = "std", feature = "libm"))]
mod bipower;
mod bucket;
mod covariance;
#[cfg(feature = "alloc")]
mod covariance_matrix;
mod cvar;
mod ewm_var;
#[cfg(any(feature = "std", feature = "libm"))]
mod half_life;
mod harmonic_mean;
mod hit_rate;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod hurst;
mod lpm;
mod moments;
mod percentile;
#[cfg(any(feature = "std", feature = "libm"))]
mod roll_spread;
mod running_mean;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod two_scale_rv;
#[cfg(feature = "alloc")]
mod variance_ratio;
mod welford;

pub use amihud::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use bipower::*;
pub use bucket::*;
pub use covariance::*;
#[cfg(feature = "alloc")]
pub use covariance_matrix::*;
pub use cvar::*;
pub use ewm_var::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use half_life::*;
pub use harmonic_mean::*;
pub use hit_rate::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use hurst::*;
pub use lpm::*;
pub use moments::*;
pub use percentile::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use roll_spread::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use two_scale_rv::*;
#[cfg(feature = "alloc")]
pub use variance_ratio::*;
pub use welford::*;
