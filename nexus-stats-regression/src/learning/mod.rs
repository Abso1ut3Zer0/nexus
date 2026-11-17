//! Adaptive filters, online learning, and optimization.

#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod adagrad;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod adam;
#[cfg(feature = "alloc")]
mod huber_regression;
#[cfg(feature = "alloc")]
mod lms;
#[cfg(feature = "alloc")]
mod online_gd;
#[cfg(feature = "alloc")]
mod online_kmeans;
#[cfg(feature = "alloc")]
mod rls;

#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use adagrad::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use adam::*;
#[cfg(feature = "alloc")]
pub use huber_regression::*;
#[cfg(feature = "alloc")]
pub use lms::*;
#[cfg(feature = "alloc")]
pub use online_gd::*;
#[cfg(feature = "alloc")]
pub use online_kmeans::*;
#[cfg(feature = "alloc")]
pub use rls::*;

#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod arm_bank;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod epsilon_greedy;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod exp3;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod sampling;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod thompson_beta;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod thompson_gamma;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod ucb1;

#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use epsilon_greedy::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use exp3::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use thompson_beta::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use thompson_gamma::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use ucb1::*;
