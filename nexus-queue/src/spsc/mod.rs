//! Single-producer single-consumer bounded queue.
//!
//! Two implementations are available:
//!
//! - **index** (default): Cached head/tail indices on separate cache lines
//! - **slot**: Per-slot lap counters
//!
//! Both are exposed as submodules for benchmarking. The top-level re-exports
//! use the implementation selected by feature flag.
//!
//! ```toml
//! # Use slot-based implementation
//! nexus-queue = { version = "...", features = ["slot-based"] }
//! ```

#[cfg(not(feature = "spsc-slot"))]
mod index;

#[cfg(not(feature = "spsc-slot"))]
pub use index::{ring_buffer, Producer, Consumer};

#[cfg(feature = "spsc-slot")]
mod slot;

#[cfg(feature = "spsc-slot")]
pub use slot::{ring_buffer, Producer, Consumer};
