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
//! Storage (Slab)     - owns data, provides stable keys
//! List/Heap/SkipList - coordinate keys, don't own data
//! ```
//!
//! Benefits:
//! - **Stable keys**: Remove from middle without invalidating other keys
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
//! // List coordinates keys into storage
//! let mut queue: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! // Insert returns stable key for O(1) access later
//! let key = queue.try_push_back(&mut storage, 42).unwrap();
//!
//! // O(1) removal from anywhere
//! assert_eq!(queue.remove(&mut storage, key), Some(42));
//! ```
//!
//! # Moving Between Lists
//!
//! Use `unlink` and `link_back` to move elements without deallocating.
//! The storage key stays valid.
//!
//! ```
//! use nexus_collections::{BoxedListStorage, List};
//!
//! let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(100);
//! let mut queue_a: List<u64, BoxedListStorage<u64>> = List::new();
//! let mut queue_b: List<u64, BoxedListStorage<u64>> = List::new();
//!
//! let key = queue_a.try_push_back(&mut storage, 42).unwrap();
//!
//! // Move to queue_b - key remains valid
//! queue_a.unlink(&mut storage, key);
//! queue_b.link_back(&mut storage, key);
//!
//! assert!(queue_a.is_empty());
//! assert_eq!(queue_b.get(&storage, key), Some(&42));
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
//! let key = list.try_push_back(&mut storage_a, 1).unwrap();
//!
//! // WRONG: using storage_b with a list that references storage_a
//! // list.remove(&mut storage_b, key);  // Undefined behavior!
//! ```
//!
//! # Storage Options
//!
//! | Storage | Capacity | Allocation | Use Case |
//! |---------|----------|------------|----------|
//! | [`BoxedStorage`] | Fixed (runtime) | Single heap alloc | Default choice |
//! | `slab::Slab` | Growable | May reallocate | When size unknown |
//! | `nexus_slab::Slab` | Fixed | Page-aligned, mlockable | Latency-critical |
//! | `HashMap<K, V>` | Growable | May reallocate | When keys are in values |
//!
//! Enable `slab` or `nexus-slab` features to use external storage backends.
//!
//! # Storage Traits
//!
//! Storage is split into bounded and unbounded variants:
//!
//! ```text
//! Storage<T>           - base trait: get, remove, len
//!     │
//!     ├── BoundedStorage<T>   - fixed capacity, try_insert -> Result
//!     │
//!     └── UnboundedStorage<T> - growable, insert -> Key (infallible)
//! ```
//!
//! This enables different APIs for data structures:
//! - `try_push` for bounded storage (returns `Result<K, Full<T>>`)
//! - `push` for unbounded storage (returns `K`, infallible)
//!
//! # Data Structures
//!
//! | Structure | Use Case | Key Operations |
//! |-----------|----------|----------------|
//! | [`List`] | FIFO queues, LRU caches | O(1) push/pop/remove |
//! | [`Heap`] | Priority queues, timers | O(log n) push/pop, O(1) decrease-key |
//!
//! # Performance
//!
//! Benchmarked on Intel Core Ultra 7 155H, single P-core:
//!
//! | Operation | Cycles (p50) | Notes |
//! |-----------|--------------|-------|
//! | List push_back | 22 | O(1) |
//! | List remove | 24 | O(1), from anywhere |
//! | Heap push | 30-46 | O(log n) |
//! | Heap pop | 30-46 | O(log n) |
//!
//! # Feature Flags
//!
//! - `slab` - Enable [`Storage`] impl for `slab::Slab`
//! - `nexus-slab` - Enable [`Storage`] impl for `nexus_slab::Slab`

#![warn(missing_docs)]

pub mod heap;
pub mod key;
pub mod list;
pub mod owned;
pub mod skiplist;
pub mod storage;

pub use heap::{BoxedHeapStorage, Heap};
pub use key::Key;
pub use list::{BoxedListStorage, List};
pub use owned::{OwnedHeap, OwnedList};
pub use skiplist::{BoxedSkipStorage, Entry, OccupiedEntry, SkipList, SkipNode, VacantEntry};
pub use storage::{BoundedStorage, BoxedStorage, Full, Keyed, Storage, UnboundedStorage};

#[cfg(feature = "nexus-slab")]
pub use heap::NexusHeapStorage;
#[cfg(feature = "nexus-slab")]
pub use list::NexusListStorage;
#[cfg(feature = "nexus-slab")]
pub use skiplist::NexusSkipStorage;

#[cfg(feature = "slab")]
pub use heap::SlabHeapStorage;
#[cfg(feature = "slab")]
pub use list::SlabListStorage;
#[cfg(feature = "slab")]
pub use skiplist::SlabSkipStorage;

