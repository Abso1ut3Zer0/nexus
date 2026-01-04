//! Convenience wrappers that own their storage.
//!
//! The types in this module combine a data structure with its backing storage,
//! providing a simpler API for cases where you don't need to share storage
//! across multiple data structures.
//!
//! # When to use owned variants
//!
//! Use [`OwnedList`] or [`OwnedHeap`] when:
//! - You have a single data structure (not multiple queues sharing storage)
//! - You want a simpler API without passing `&mut storage` to every method
//! - You don't need to move elements between data structures
//!
//! # When to use the raw variants
//!
//! Use [`List`](crate::List) or [`Heap`](crate::Heap) with external storage when:
//! - Multiple data structures share one storage pool (e.g., order queues per price level)
//! - You need to move elements between structures via `unlink`/`link_*`
//! - You want finer control over memory layout and allocation
//!
//! # Example
//!
//! ```
//! use nexus_collections::{OwnedList, OwnedHeap};
//!
//! // Simple FIFO queue
//! let mut queue: OwnedList<u64> = OwnedList::with_capacity(100);
//! queue.try_push_back(1).unwrap();
//! queue.try_push_back(2).unwrap();
//! assert_eq!(queue.pop_front(), Some(1));
//!
//! // Simple priority queue
//! let mut pq: OwnedHeap<u64> = OwnedHeap::with_capacity(100);
//! pq.try_push(5).unwrap();
//! pq.try_push(1).unwrap();
//! pq.try_push(3).unwrap();
//! assert_eq!(pq.pop(), Some(1)); // min first
//! ```

mod heap;
mod list;

pub use heap::OwnedHeap;
pub use list::OwnedList;
