//! High-performance lock-free queues for latency-critical applications.
//!
//! `nexus-queue` provides bounded SPSC (single-producer, single-consumer) queues
//! optimized for trading systems and other low-latency workloads.
//!
//! # Quick Start
//!
//! ```
//! use nexus_queue::spsc;
//!
//! let (mut tx, mut rx) = spsc::ring_buffer::<u64>(1024);
//!
//! tx.push(42).unwrap();
//! assert_eq!(rx.pop(), Some(42));
//! ```
//!
//! # Implementations
//!
//! Two SPSC implementations are available with different performance
//! characteristics depending on hardware topology:
//!
//! - **index** (default): Cached head/tail indices on separate cache lines
//! - **slot**: Per-slot lap counters on the same cache line as data
//!
//! The key difference is cache line ownership. The index-based design has
//! producer and consumer writing to separate cache lines, while slot-based
//! has both writing to the same cache line. Which performs better depends
//! on your NUMA configuration and cache hierarchy.
//!
//! **Benchmark both on your target hardware.**
//!
//! ```toml
//! # Use slot-based implementation
//! nexus-queue = { version = "...", features = ["slot-based"] }
//! ```
//!
//! # Feature Flags
//!
//! - `spsc-slot`: Use slot-based implementation for top-level re-exports

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs, missing_debug_implementations)]

use core::fmt;

pub mod spsc;

/// Error returned when pushing to a full queue.
///
/// Contains the value that could not be pushed, returning ownership to the caller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Full<T>(pub T);

impl<T> Full<T> {
    /// Returns the value that could not be pushed.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> fmt::Display for Full<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "queue is full")
    }
}

impl<T: fmt::Debug> std::error::Error for Full<T> {}
