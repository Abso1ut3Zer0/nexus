//! High-performance timer wheel with O(1) insert and cancel.
//!
//! `nexus-timer` provides a hierarchical timer wheel inspired by the Linux
//! kernel's timer infrastructure (Gleixner 2016). Timers are placed into
//! coarser slots at higher levels — no cascading, no entry movement after
//! insertion.
//!
//! # Design
//!
//! - **No cascade:** Once placed, an entry never moves. Poll checks each
//!   entry's exact deadline. This eliminates the latency spikes that
//!   cascading timer wheels exhibit.
//! - **Intrusive active-slot lists:** Only non-empty slots are visited
//!   during poll and next-deadline queries. No bitmap, no full scan.
//! - **Embedded refcounting:** Lightweight `Cell<u8>` refcount per entry
//!   enables fire-and-forget timers alongside cancellable timers without
//!   external reference-counting machinery.
//! - **Generic storage:** Parameterized over slab backend — bounded
//!   (fixed-capacity) or unbounded (growable).
//!
//! # Quick Start
//!
//! ```
//! use std::time::{Duration, Instant};
//! use nexus_timer::Wheel;
//!
//! let now = Instant::now();
//! let mut wheel: Wheel<u64> = Wheel::unbounded(4096, now);
//!
//! // Schedule a timer 100ms from now
//! let handle = wheel.schedule(now + Duration::from_millis(100), 42u64);
//!
//! // Cancel before it fires — get the value back
//! let value = wheel.cancel(handle);
//! assert_eq!(value, Some(42));
//! ```

#![warn(missing_docs)]

mod entry;
mod handle;
mod level;
pub mod store;
pub mod timeout_list;
mod wheel;

pub use entry::WheelEntry;
pub use handle::TimerHandle;
pub use timeout_list::{
    BoundedTimeoutList, BoundedTimeoutListBuilder, TimeoutList, TimeoutListBuilder,
    UnboundedTimeoutListBuilder,
};
pub use wheel::{
    BoundedWheel, BoundedWheelBuilder, TimerWheel, UnboundedWheelBuilder, Wheel, WheelBuilder,
};

// Re-export Full for bounded wheel users
pub use nexus_slab::Full;
