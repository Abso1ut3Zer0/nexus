//! Smoothers: each takes a sample and returns the smoothed value.
//!
//! # Which type do I use?
//!
//! - [`Ema`]: an exponential moving average. Recent samples count more and
//!   old ones fade. The default choice.
//! - [`AsymEma`]: an average that rises at one speed and falls at another,
//!   for a fast attack and a slow decay, or the reverse.
//! - [`Slew`]: follows the input, but moves by no more than a set amount
//!   per sample.
//!
//! Smoothers that resist outliers, follow a trend, or take a median over a
//! window are in the `nexus-stats-smoothing` crate.

mod asym_ema;
pub(crate) mod ema;
mod slew;

pub use asym_ema::*;
pub use ema::*;
pub use slew::*;
