//! System monitoring and operational health.
//!
//! # Weighting clocks
//!
//! Every type here states what one `update` is worth in a `# Weighting
//! clock` section of its docs: per call, per event with its own timestamp,
//! the caller's timestamps, or none. The one rule that follows: never update
//! a per-call type from a loop whose iteration time depends on the quantity
//! being measured. Sampling queue fill once per spin iteration into an EMA is
//! the classic failure: under load the loop iterates less often, so the
//! smoother sees fewer samples exactly when it matters, and a published value
//! can read healthy while most messages are late. Use a per-event type with
//! timestamps, or `PollSaturation`, which is weighted per message by
//! construction.

mod codel;
mod drawdown;
mod error_rate;
mod event_rate;
#[cfg(any(feature = "std", feature = "libm"))]
mod hawkes;
mod jitter;
mod liveness;
mod max_gauge;
mod peak_hold;
mod poll_saturation;
mod running;
mod sojourn_saturation;
pub(crate) mod windowed;

pub use codel::*;
pub use drawdown::*;
pub use error_rate::*;
pub use event_rate::*;
#[cfg(any(feature = "std", feature = "libm"))]
pub use hawkes::*;
pub use jitter::*;
pub use liveness::*;
pub use max_gauge::*;
pub use peak_hold::*;
pub use poll_saturation::*;
pub use running::*;
pub use sojourn_saturation::*;
pub use windowed::*;
