# nexus-collections

High-performance collections with external storage for latency-critical systems.

## Why This Crate?

Traditional collections own their data, which creates problems for low-latency systems:

- **`Vec<T>`** - indices shift on removal
- **`LinkedList<T>`** - no handle to remove specific elements in O(1)
- **`BinaryHeap<T>`** - no way to update priorities or remove arbitrary elements

This crate inverts the model: **storage is separate from structure**.

```
Storage (slab)          →  owns the data, provides stable keys
List / Heap / SkipList  →  coordinate keys, don't own data
```

Benefits:
- **Stable keys**: Remove from middle, keys stay valid
- **Zero allocation on hot path**: Pre-allocate storage at startup
- **O(1) operations**: Remove any element by key, not just head/tail
- **Shared storage**: Multiple data structures reference one pool
- **Cache-friendly**: Slab-backed storage has good locality

## Quick Start

```rust
use nexus_collections::{BoxedListStorage, List};

// Storage owns the data
let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(1000);

// List coordinates keys into storage
let mut queue: List<u64, BoxedListStorage<u64>> = List::new();

// Insert returns a stable key
let key = queue.try_push_back(&mut storage, 42).unwrap();

// O(1) access and removal by key
assert_eq!(queue.get(&storage, key), Some(&42));
assert_eq!(queue.remove(&mut storage, key), Some(42));
```

## Comparison with intrusive-collections

The [`intrusive-collections`](https://crates.io/crates/intrusive-collections) crate is a well-engineered library for intrusive data structures. The two crates serve different use cases:

| Aspect | nexus-collections | intrusive-collections |
|--------|-------------------|----------------------|
| **Model** | External storage pool | Links embedded in your type |
| **Handles** | Stable keys into storage | Cursors into structure |
| **Multi-membership** | One structure at a time | Node in multiple lists simultaneously |
| **Capacity** | Pre-allocated, bounded | Grows with insertions |

**Choose nexus-collections for:**
- Low latency systems, timer wheels, bounded queues
- Elements that move between structures while keeping external references
- Pre-allocated storage pools with zero hot-path allocation

**Choose intrusive-collections for:**
- Kernel-style code, complex graph structures
- Nodes that must belong to multiple lists simultaneously
- When you control the node type and can embed links

## Data Structures

| Structure | Use Case | Key Operations |
|-----------|----------|----------------|
| [`List`] | FIFO queues, LRU caches | O(1) push/pop/remove anywhere |
| [`Heap`] | Priority queues, timers | O(log n) push/pop, O(1) peek |
| [`OwnedList`] | Simple queue (owns storage) | Same as List, simpler API |
| [`OwnedHeap`] | Simple priority queue | Same as Heap, simpler API |

## Performance

Benchmarked with `rdtscp`, turbo boost off, Intel Core Ultra 7 155H:

### List Operations

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| push_back | 86 | 92 | 92 |
| push_front | 62 | 70 | 72 |
| pop_front | 66 | 76 | 98 |
| pop_back | 68 | 80 | 96 |
| get | 64 | 70 | 82 |
| remove | 70 | 80 | 120 |
| unlink | 62 | 70 | 92 |
| link_back | 58 | 66 | 86 |
| move_to_back | 64 | 70 | 94 |

*Cycles per operation*

### Heap Operations

| Operation | p50 | p99 | p999 |
|-----------|-----|-----|------|
| push | 64 | 90 | 92 |
| pop | 64 | 90 | 98 |
| peek | 60 | 66 | 70 |
| remove | 90 | 110 | 140 |
| decrease_key | 110 | 230 | 252 |
| increase_key | 90 | 140 | 242 |
| contains | 62 | 70 | 124 |

*Cycles per operation*

### Real-World Workflows

**Order Queue** (insert → price amend → cancel):
| Operation | p50 | p99 |
|-----------|-----|-----|
| insert | 64 | 92 |
| move | 66 | 94 |
| cancel | 64 | 94 |

**Timer Wheel** (schedule → fire → cancel):
| Operation | p50 | p99 |
|-----------|-----|-----|
| schedule | 66 | 78 |
| fire | 64 | 72 |
| cancel | 70 | 80 |

At 3 GHz base clock: **~20-30 ns** for most operations.

## Moving Between Lists

The key feature for order books: move elements without deallocating.

```rust
use nexus_collections::{BoxedListStorage, List};

let mut storage: BoxedListStorage<u64> = BoxedListStorage::with_capacity(100);
let mut price_100: List<u64, _> = List::new();
let mut price_101: List<u64, _> = List::new();

// New order at price 100
let order_key = price_100.try_push_back(&mut storage, 42).unwrap();

// Price amendment: move to 101
price_100.unlink(&mut storage, order_key);
price_101.link_back(&mut storage, order_key);

// Key still valid - client can still cancel by key
assert_eq!(price_101.get(&storage, order_key), Some(&42));
```

## Storage Options

| Storage | Capacity | Allocation | Use Case |
|---------|----------|------------|----------|
| `BoxedStorage` | Fixed | Single heap alloc | Default choice |
| `slab::Slab` | Growable | May reallocate | Unknown size |
| `nexus_slab::Slab` | Fixed | Page-aligned, mlockable | Latency-critical |
| `HashMap<K,V>` | Growable | May reallocate | Keyed by value field |

## Feature Flags

- **`slab`** - Enable `slab::Slab` as unbounded storage
- **`nexus-slab`** - Enable `nexus_slab::Slab` as bounded storage

```toml
[dependencies]
nexus-collections = { version = "0.1", features = ["slab"] }
```

## Owned vs Raw API

**Use `OwnedList` / `OwnedHeap` when:**
- Single data structure, not sharing storage
- Want simpler API without `&mut storage` everywhere

**Use `List` / `Heap` with external storage when:**
- Multiple structures share one storage pool
- Need to move elements between structures
- Want control over memory allocation

```rust
// Simple case - owned
let mut queue: OwnedList<u64> = OwnedList::with_capacity(100);
queue.try_push_back(1).unwrap();

// Shared storage - raw
let mut storage = BoxedListStorage::with_capacity(100);
let mut queue_a: List<u64, _> = List::new();
let mut queue_b: List<u64, _> = List::new();
// Both queues share `storage`
```

## Safety

**Critical invariant**: A data structure must always be used with the same storage instance. Passing a different storage is undefined behavior.

```rust
// WRONG - undefined behavior
let key = list.try_push_back(&mut storage_a, 1).unwrap();
list.remove(&mut storage_b, key); // UB!
```

This is the same discipline required by the `slab` crate.

## License

Licensed under the MIT License. See [LICENSE](LICENSE) for details.
