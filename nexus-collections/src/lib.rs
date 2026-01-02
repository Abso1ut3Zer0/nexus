//! High-performance intrusive collections with external storage.
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
//! - **O(1) operations**: Intrusive links enable O(1) removal from lists
//! - **Shared storage**: Multiple data structures can reference the same pool
//! - **Cache-friendly**: Slab-backed storage has good locality
//!
//! # Quick Start
//!
//! ```
//! use nexus_collections::{BoxedStorage, Index, Linked, List, Storage};
//!
//! // Define your data with embedded links
//! #[derive(Debug)]
//! struct Order {
//!     id: u64,
//!     price: u64,
//!     // Intrusive links for O(1) list operations
//!     next: u32,
//!     prev: u32,
//! }
//!
//! impl Linked<u32> for Order {
//!     fn next(&self) -> u32 { self.next }
//!     fn prev(&self) -> u32 { self.prev }
//!     fn set_next(&mut self, idx: u32) { self.next = idx; }
//!     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
//! }
//!
//! // Storage owns the data
//! let mut storage: BoxedStorage<Order> = BoxedStorage::with_capacity(10_000);
//!
//! // List just coordinates indices
//! let mut queue: List<u32> = List::new();
//!
//! // Insert into storage first, then add to list
//! let idx = storage.try_insert(Order {
//!     id: 1, price: 100, next: u32::NONE, prev: u32::NONE
//! }).unwrap();
//! queue.push_back(&mut storage, idx);
//!
//! // O(1) removal from middle - no search required
//! queue.remove(&mut storage, idx);
//! storage.remove(idx);
//! ```
//!
//! # Critical Invariants
//!
//! These data structures rely on invariants that are **not checked at runtime**
//! (except via `debug_assert!` in debug builds). Violating them causes undefined
//! behavior or data corruption:
//!
//! ## 1. Same Storage Instance
//!
//! All operations on a data structure must use the same storage instance.
//! Passing a different storage will access wrong memory.
//!
//! ```no_run
//! # use nexus_collections::{BoxedStorage, Index, Linked, List, Storage};
//! # #[derive(Debug)]
//! # struct Node { next: u32, prev: u32 }
//! # impl Linked<u32> for Node {
//! #     fn next(&self) -> u32 { self.next }
//! #     fn prev(&self) -> u32 { self.prev }
//! #     fn set_next(&mut self, idx: u32) { self.next = idx; }
//! #     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
//! # }
//! let mut storage_a: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
//! let mut storage_b: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
//! let mut list: List<u32> = List::new();
//!
//! let idx = storage_a.try_insert(Node { next: u32::NONE, prev: u32::NONE }).unwrap();
//! list.push_back(&mut storage_a, idx);
//!
//! // WRONG: using storage_b with a list that references storage_a
//! // list.remove(&mut storage_b, idx);  // Undefined behavior!
//! ```
//!
//! ## 2. No Shared Elements (Single Ownership)
//!
//! An element can only be in **one** data structure at a time. The embedded
//! links (next/prev for lists, heap_idx for heaps) would conflict.
//!
//! ```no_run
//! # use nexus_collections::{BoxedStorage, Index, Linked, List, Storage};
//! # #[derive(Debug)]
//! # struct Node { next: u32, prev: u32 }
//! # impl Linked<u32> for Node {
//! #     fn next(&self) -> u32 { self.next }
//! #     fn prev(&self) -> u32 { self.prev }
//! #     fn set_next(&mut self, idx: u32) { self.next = idx; }
//! #     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
//! # }
//! let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
//! let mut list_a: List<u32> = List::new();
//! let mut list_b: List<u32> = List::new();
//!
//! let idx = storage.try_insert(Node { next: u32::NONE, prev: u32::NONE }).unwrap();
//! list_a.push_back(&mut storage, idx);
//!
//! // WRONG: same element in two lists
//! // list_b.push_back(&mut storage, idx);  // Corrupts both lists!
//! ```
//!
//! **Exception**: If your type has multiple link pairs, it can participate in
//! multiple lists simultaneously:
//!
//! ```
//! # use nexus_collections::{Index, Linked};
//! struct Order {
//!     // Links for price-level queue
//!     price_next: u32,
//!     price_prev: u32,
//!     // Links for time-priority queue
//!     time_next: u32,
//!     time_prev: u32,
//! }
//!
//! // Implement Linked for each queue using newtype wrappers or separate traits
//! ```
//!
//! ## 3. Storage Lifetime
//!
//! Never remove an element from storage while it's still in a data structure.
//! The data structure would hold a dangling index.
//!
//! ```no_run
//! # use nexus_collections::{BoxedStorage, Index, Linked, List, Storage};
//! # #[derive(Debug)]
//! # struct Node { next: u32, prev: u32 }
//! # impl Linked<u32> for Node {
//! #     fn next(&self) -> u32 { self.next }
//! #     fn prev(&self) -> u32 { self.prev }
//! #     fn set_next(&mut self, idx: u32) { self.next = idx; }
//! #     fn set_prev(&mut self, idx: u32) { self.prev = idx; }
//! # }
//! let mut storage: BoxedStorage<Node> = BoxedStorage::with_capacity(16);
//! let mut list: List<u32> = List::new();
//!
//! let idx = storage.try_insert(Node { next: u32::NONE, prev: u32::NONE }).unwrap();
//! list.push_back(&mut storage, idx);
//!
//! // WRONG: removing from storage without removing from list
//! // storage.remove(idx);  // list now has dangling index!
//! // list.pop_front(&mut storage);  // Undefined behavior!
//!
//! // CORRECT: remove from data structure first, then storage
//! list.remove(&mut storage, idx);
//! storage.remove(idx);
//! ```
//!
//! ## 4. Index Validity
//!
//! Indices passed to data structure methods must be valid in storage.
//! In release builds, invalid indices cause undefined behavior.
//! In debug builds, they trigger a panic via `debug_assert!`.
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
//! | [`Heap`] | Priority queues, timers | O(log n) push/pop, O(log n) remove |
//!
//! # Performance
//!
//! Benchmarked on Intel Core Ultra 7 155H, single P-core:
//!
//! | Operation | Cycles (p50) | Notes |
//! |-----------|--------------|-------|
//! | List push_back | 22 | O(1) |
//! | List remove | 24 | O(1), from anywhere |
//! | Heap push | 30 | O(log n), n=1024 |
//! | Heap pop | 46 | O(log n), n=1024 |
//!
//! # Feature Flags
//!
//! - `slab` - Enable [`Storage`] impl for `slab::Slab`
//! - `nexus-slab` - Enable [`Storage`] impl for `nexus_slab::Slab`

mod heap;
mod index;
mod linked;
mod owned;
mod storage;

pub use heap::{Heap, HeapEntry};
pub use index::Index;
pub use linked::{Indices, Iter, IterMut, Linked, List};
pub use owned::{OwnedHeap, OwnedList};
pub use storage::{BoxedStorage, Full, Storage};
