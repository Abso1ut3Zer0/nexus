//! Cross-thread notification with conflation and FIFO delivery.
//!
//! Two primitives:
//!
//! - **[`event_queue()`]** → `(Notifier, Poller)` — non-blocking.
//!   The consumer polls when it chooses.
//!
//! - **[`event_channel()`]** → `(Sender, Receiver)` — blocking.
//!   The consumer blocks when idle and is woken by the producer.
//!   Wraps the event queue with crossbeam parker/unparker.
//!
//! [`event_queue()`] creates a `(Notifier, Poller)` pair for signaling which
//! items are ready for processing. An IO thread writes data into shared
//! storage (e.g., a conflation slot) and calls [`Notifier::notify`]. The
//! main event loop calls [`Poller::poll`] or [`Poller::poll_limit`] to
//! discover which tokens fired.
//!
//! # Architecture
//!
//! Two concerns, cleanly separated:
//!
//! - **Dedup flags** — one [`AtomicBool`](core::sync::atomic::AtomicBool)
//!   per token. If the flag is already `true` when a producer calls
//!   [`notify()`](Notifier::notify), the notification is a no-op (conflated).
//!   Single atomic swap, no queue interaction.
//!
//! - **Delivery queue** — a [`nexus_queue`] MPSC ring buffer. When a
//!   producer wins the flag swap (`false → true`), it pushes the token
//!   index into the FIFO queue. The consumer pops and clears the flag,
//!   re-arming it for future notifications.
//!
//! Both [`Notifier`] and [`Poller`] store the flags as `Arc<[AtomicBool]>` —
//! a single pointer deref to reach the flag array on every operation.
//!
//! # Operations
//!
//! Only three operations matter:
//!
//! - **[`notify(token)`](Notifier::notify)** — signal readiness. Conflated
//!   if already flagged. Returns `Result` so the caller owns the error
//!   policy (`.unwrap()` to crash, `.ok()` to swallow, or match to log).
//!
//! - **[`poll(events)`](Poller::poll)** — drain all ready tokens into the
//!   events buffer.
//!
//! - **[`poll_limit(events, limit)`](Poller::poll_limit)** — drain up to
//!   `limit` tokens. Remaining items stay in the queue for the next call.
//!   Oldest notifications drain first (FIFO) — no starvation under budget.
//!
//! # Invariants
//!
//! - **Flag = `true` ⟺ token is in the queue (or being pushed).** The
//!   consumer clears the flag on pop. Producers only set flags.
//!
//! - **At most one queue entry per token.** The flag gates admission.
//!   Two producers racing on the same token: one wins (pushes), the other
//!   sees `true` (conflated). Never two entries for the same index.
//!
//! - **Queue cannot overflow.** The flag ensures at most one entry per
//!   token. The underlying queue is sized to hold at least `max_tokens`
//!   entries. Overflow is an invariant violation (logic bug), reported
//!   via [`NotifyError`].
//!
//! - **FIFO delivery.** The MPSC ring buffer preserves push order. The
//!   consumer sees tokens in the order they were first notified.
//!
//! # Spurious Wakeups
//!
//! If a slab key is freed and reassigned to a new item, a [`notify()`](Notifier::notify)
//! in-flight for the old item fires the token for the new item. The
//! consumer must tolerate spurious wakeups during the transition.
//!
//! The user's responsibilities:
//! 1. Stop calling `notify()` for a token before its key is reused.
//! 2. A callback's token cannot change without informing the producer.
//! 3. Tolerate spurious wakeups during the deregister window.
//!
//! Same contract as mio.
//!
//! # Memory Ordering
//!
//! The producer's flag swap uses `Acquire`. The consumer's flag clear
//! uses `Release`. This establishes a happens-before chain: when the
//! producer sees the flag cleared (`false`), the queue slot freed by
//! the consumer's pop is guaranteed to be visible. Without this,
//! the producer could see the flag cleared but the queue slot still
//! occupied under weak memory models (validated by MIRI).
//!
//! # Performance (p50 cycles, measured)
//!
//! | Operation | Cycles | Notes |
//! |-----------|--------|-------|
//! | notify (conflated) | 16 | flag swap only |
//! | notify (new) | 16 | flag swap + CAS push |
//! | poll empty | 2 | single failed pop |
//! | poll N=8 | 48 | |
//! | poll N=128 | 684 | ~5.3 cy/token |
//! | poll_limit=32 (4096 ready) | 162 | O(limit) |
//! | cross-thread roundtrip | 362 | ~100ns @ 3.5GHz |
//!
//! # Memory
//!
//! For `max_tokens = 4096`: flags = 4 KB, MPSC queue = 64 KB (rounded
//! to power-of-two), total ~68 KB.
//!
//! # Example
//!
//! ```
//! use nexus_notify::{event_queue, Token};
//!
//! // Setup
//! let (notifier, poller) = event_queue(64);
//! let mut events = nexus_notify::Events::with_capacity(64);
//!
//! // Producer: signal readiness
//! let token = Token::new(0);
//! notifier.notify(token).unwrap();
//!
//! // Consumer: discover what's ready
//! poller.poll(&mut events);
//! assert_eq!(events.len(), 1);
//! assert_eq!(events.as_slice()[0].index(), 0);
//! ```
//!
//! ## With poll_limit (budgeted drain)
//!
//! ```
//! use nexus_notify::{event_queue, Token};
//!
//! let (notifier, poller) = event_queue(256);
//! let mut events = nexus_notify::Events::with_capacity(256);
//!
//! // Many tokens ready
//! for i in 0..100 {
//!     notifier.notify(Token::new(i)).unwrap();
//! }
//!
//! // Drain only 10 per iteration (oldest first)
//! poller.poll_limit(&mut events, 10);
//! let batch: Vec<usize> = events.drain().map(|t| t.index()).collect();
//! assert_eq!(batch.len(), 10);
//! assert_eq!(batch[0], 0);  // FIFO: oldest first
//!
//! // Remaining 90 stay in the queue
//! poller.poll(&mut events);
//! assert_eq!(events.len(), 90);
//! ```

#![warn(missing_docs)]

mod event_channel;
mod event_queue;
pub mod local;
mod loom_impl;

pub use event_channel::{Receiver, Sender, event_channel};
pub use event_queue::{Drain, Events, Notifier, NotifyError, Poller, Token, event_queue};
pub use local::LocalNotify;
