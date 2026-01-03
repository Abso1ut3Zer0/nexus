//! High-performance collections with external storage.
//!
//! This crate provides data structures optimized for latency-critical systems
//! like trading infrastructure. The key insight: separate storage from structure.
//!
//! # Design Philosophy
//!
//! Traditional collections own their data:
//!
//! ```text
//! Vec<Order>     - owns orders, indices unstable on removal
//! BTreeMap<K,V>  - owns values, allocates on insert
//! LinkedList<T>  - owns nodes, pointer chasing, poor cache locality
//! ```
//!
//! This crate inverts the model:
//!
//! ```text
//! Storage (Slab)     - owns data, provides stable indices
//! List/Heap/SkipList - coordinate indices, don't own data
//! ```
//!
//! Benefits:
//! - **Stable indices**: Remove from middle without invalidating other indices
//! - **Zero allocation on hot path**: Pre-allocate storage at startup
//! - **O(1) operations**: Internal links enable O(1) removal from lists
//! - **Shared storage**: Multiple data structures can reference the same pool
//! - **Cache-friendly**: Slab-backed storage has good locality
//!
//! # Quick Start
//!
//! ```
//! use nexus_collections::{BoxedListStorage, List};
//!
//! // Storage owns the data (wrapped in ListNode internally)
//! let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(1000);
//!
//! // List coordinates indices into storage
//! let mut queue: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! // Insert returns stable index for O(1) access later
//! let idx = queue.push_back(&mut storage, 42).unwrap();
//!
//! // O(1) removal from anywhere
//! assert_eq!(queue.remove(&mut storage, idx), Some(42));
//! ```
//!
//! # Moving Between Lists
//!
//! Use `unlink` and `link_back` to move elements without deallocating.
//! The storage index stays valid.
//!
//! ```
//! use nexus_collections::{BoxedListStorage, List};
//!
//! let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(100);
//! let mut queue_a: List<u64, BoxedListStorage<u64>> = List::new();
//! let mut queue_b: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! let idx = queue_a.push_back(&mut storage, 42).unwrap();
//!
//! // Move to queue_b - index remains valid
//! queue_a.unlink(&mut storage, idx);
//! queue_b.link_back(&mut storage, idx);
//!
//! assert!(queue_a.is_empty());
//! assert_eq!(queue_b.get(&storage, idx), Some(&42));
//! ```
//!
//! # Critical Invariant: Same Storage Instance
//!
//! All operations on a list must use the same storage instance.
//! This is the caller's responsibility (same discipline as the `slab` crate).
//! Passing a different storage causes undefined behavior.
//!
//! ```no_run
//! use nexus_collections::{BoxedListStorage, List};
//!
//! let mut storage_a: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
//! let mut storage_b: BoxedListStorage<u64> = BoxedListStorage::with_capacity(16);
//! let mut list: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! let idx = list.push_back(&mut storage_a, 1).unwrap();
//!
//! // WRONG: using storage_b with a list that references storage_a
//! // list.remove(&mut storage_b, idx);  // Undefined behavior!
//! ```
//!
//! # Storage Options
//!
//! | Storage | Capacity | Allocation | Use Case |
//! |---------|----------|------------|----------|
//! | [`BoxedStorage`] | Fixed (runtime) | Single heap alloc | Default choice |
//! | `slab::Slab` | Growable | May reallocate | When size unknown |
//! | `nexus_slab::Slab` | Fixed | Page-aligned, mlockable | Latency-critical |
//!
//! Enable `slab` or `nexus-slab` features to use external storage backends.
//!
//! # Data Structures
//!
//! | Structure | Use Case | Key Operations |
//! |-----------|----------|----------------|
//! | [`List`] | FIFO queues, LRU caches | O(1) push/pop/remove |
//!
//! # Performance
//!
//! Benchmarked on Intel Core Ultra 7 155H, single P-core:
//!
//! | Operation | Cycles (p50) | Notes |
//! |-----------|--------------|-------|
//! | List push_back | 22 | O(1) |
//! | List remove | 24 | O(1), from anywhere |
//!
//! # Feature Flags
//!
//! - `slab` - Enable [`Storage`] impl for `slab::Slab`
//! - `nexus-slab` - Enable [`Storage`] impl for `nexus_slab::Slab`

mod heap;
mod index;
mod list;
mod owned;
mod storage;

pub use heap::{Heap, HeapEntry};
pub use index::Index;
pub use list::{BoxedListStorage, Cursor, Indices, Iter, IterMut, List};
pub use owned::OwnedHeap;
pub use storage::{BoxedStorage, Full, Storage};

#[cfg(feature = "nexus-slab")]
pub use list::NexusListStorage;
#[cfg(feature = "slab")]
pub use list::SlabListStorage;
