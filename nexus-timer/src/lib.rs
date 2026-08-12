//! Low-latency timer primitives: a hierarchical **timer wheel** (O(1) insert +
//! cancel) for arbitrary deadlines, and a fixed-duration **[`TimeoutQueue`]** for
//! the common case where every timer shares one timeout.
//!
//! # Two structures — pick by workload
//!
//! - [`TimerWheel`] ([`Wheel`] / [`BoundedWheel`]) — **arbitrary deadlines**:
//!   timers that fire at different, unrelated future times.
//! - [`TimeoutQueue`] ([`BoundedTimeoutQueue`]) — **a single fixed timeout**:
//!   every timer expires the *same* duration after it is scheduled.
//!
//! The tell: *"do all my timers time out after the same amount of time?"* —
//! yes → [`TimeoutQueue`], no → the wheel.
//!
//! | | [`TimerWheel`] | [`TimeoutQueue`] |
//! |---|---|---|
//! | Timeout per timer | arbitrary | one fixed duration |
//! | Poll | O(active population) | **O(fired)** |
//! | `next_deadline` | lower bound (cached) | **O(1) exact** |
//! | Clock | any monotone source | monotone, non-decreasing |
//!
//! Reach for [`TimeoutQueue`] on the hot path when it fits — idle timeouts (all
//! 30 s), request deadlines (all 5 s), a fixed retry/debounce delay, uniform
//! TTL expiry. Fixed duration ⇒ monotone deadlines ⇒ a sorted list, so a
//! nothing-due poll stays flat (~12 cycles) no matter how many timers are
//! outstanding. A handful of distinct durations → one list each; many or
//! arbitrary deadlines → the wheel.
//!
//! # The clock
//!
//! Every constructor takes `now` — it fixes the **reference epoch**. An
//! `Instant` has no absolute zero (you can only measure durations *between*
//! instants), so deadlines are stored relative to this epoch. Pass one monotone
//! clock source (e.g. `Instant::now()`) to the constructor *and* to every
//! `schedule` / `poll`. A `now` that goes backwards is a bug — [`TimeoutQueue`]
//! debug-asserts on it.
//!
//! # Timer wheel design
//!
//! The wheel is hierarchical: a timer is placed into a slot at the level whose
//! granularity matches how far away its deadline is — coarse levels for distant
//! deadlines, fine levels for near ones.
//!
//! - **Rebalance, don't re-walk:** as a timer's deadline approaches it is moved
//!   ("rebalanced") down to finer levels, so `poll` collects ready timers from
//!   small, exact fine-level slots instead of walking a fat coarse slot on every
//!   call. Rebalancing can be folded into the poll
//!   ([`TimerWheel::poll_and_rebalance`]), bounded per poll
//!   ([`WheelBuilder::max_rebalances_per_poll`]), or run proactively off the hot
//!   path ([`TimerWheel::rebalance`]) to keep the poll tail flat under a large
//!   number of timers. Timers still fire at their exact tick.
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
pub mod timeout_queue;
mod wheel;

pub use entry::WheelEntry;
pub use handle::TimerHandle;
pub use timeout_queue::{
    BoundedTimeoutQueue, BoundedTimeoutQueueBuilder, TimeoutQueue, TimeoutQueueBuilder,
    UnboundedTimeoutQueueBuilder,
};
pub use wheel::{
    BoundedWheel, BoundedWheelBuilder, ConfigError, TimerWheel, UnboundedWheelBuilder, Wheel,
    WheelBuilder,
};

// Re-export Full for bounded wheel users
pub use nexus_slab::Full;
