//! # nexus-queue
//!
//! High-performance lock-free ring buffer queues designed for trading systems
//! and other latency-sensitive applications.
//!
//! ## Features
//!
//! - **SPSC**: Single-producer single-consumer queue with minimal atomic operations
//! - **MPSC**: Multi-producer single-consumer queue (coming soon)
//!
//! ## Design Goals
//!
//! - Sub-microsecond latency on the hot path
//! - Predictable performance (minimal jitter)
//! - No allocations after construction
//! - Cache-line isolation to prevent false sharing
//! - Single contiguous allocation (no pointer chasing)
//!
//! ## Example
//!
//! ```
//! use nexus_queue::spsc;
//!
//! // Create a channel with capacity for 1024 elements
//! // (will be rounded up to next power of two)
//! let (tx, rx) = spsc::channel::<u64>(1024);
//!
//! // Send a value
//! tx.try_send(42).unwrap();
//!
//! // Receive the value
//! assert_eq!(rx.try_recv().unwrap(), 42);
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![allow(clippy::module_name_repetitions)]

pub mod mpsc;
pub mod spsc;
