//! Single-Producer Single-Consumer (SPSC) queues.
//!
//! This module provides two SPSC queue variants:
//!
//! - [`bounded`] - Returns `Full` when the queue is at capacity
//! - [`overwriting`] - Overwrites oldest unread values when full
//!
//! Both variants are optimized for the single-producer single-consumer case,
//! using only acquire/release semantics with no compare-and-swap operations
//! on the hot path.
//!
//! # Choosing a Variant
//!
//! Use [`bounded`] when:
//! - Every message must be delivered
//! - Backpressure to the producer is acceptable
//!
//! Use [`overwriting`] when:
//! - Latest data matters more than completeness
//! - Producer must never block (real-time feeds, sensors)
//! - Consumer can tolerate detecting missed messages

pub mod bounded;
pub mod overwriting;
