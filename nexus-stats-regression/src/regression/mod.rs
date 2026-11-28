//! Regression and classification.

mod ew_polynomial_regression;
mod hit_rate;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod lagged_predictor;
pub(crate) mod linear_regression;
#[cfg(all(test, feature = "std"))]
mod polynomial_fuzz;
pub(crate) mod polynomial_regression;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod signal_decay;

#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
mod logistic_regression;
#[cfg(any(feature = "std", feature = "libm"))]
mod transformed_regression;

pub use ew_polynomial_regression::*;
pub use hit_rate::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use lagged_predictor::*;
pub use linear_regression::*;
pub use polynomial_regression::*;
#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use signal_decay::*;

#[cfg(all(feature = "alloc", any(feature = "std", feature = "libm")))]
pub use logistic_regression::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use transformed_regression::*;
