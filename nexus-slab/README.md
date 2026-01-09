# nexus-slab

A high-performance slab allocator optimized for **predictable tail latency**.

## Why nexus-slab?

Traditional slab allocators using `Vec` exhibit bimodal p999 latency — most operations are fast, but occasional reallocations cause multi-thousand cycle spikes. For latency-critical systems like trading engines, a single slow operation can mean a missed fill.

`nexus-slab` eliminates reallocation copying by using independently-allocated slabs. When growth occurs, only the new slab is allocated — existing data never moves.

## Performance

Benchmarked on Intel Core Ultra 7 155H, pinned to a physical core. Growth phase (where realloc/new allocation happens):

| Metric | nexus-slab | slab crate |
|--------|------------|------------|
| p50    | 24 cycles  | 22 cycles  |
| p99    | 28 cycles  | 24 cycles  |
| p999   | **40-48 cycles** | 30-2400 cycles (bimodal) |
| max    | **500-800K cycles** | 1.5-2M cycles |

Trade 2-4 cycles on median for **60x better worst-case p999**.

## Architecture

### Two-Level Freelist
```
slabs_head ─► Slab 2 ─► Slab 0 ─► NONE      Slab 1 (full)
                │         │                     │
                ▼         ▼                     ▼
             [slots]   [slots]              [no space]
```

- **Slab freelist**: O(1) access to a slab with available space
- **Slot freelist**: Per-slab LIFO chain of freed slots

### Memory Layout
```
Slab 0 (independent allocation)    Slab 1 (independent allocation)
┌─────────────────────────────┐    ┌─────────────────────────────┐
│ Slot 0: [tag|value]         │    │ Slot 0: [tag|value]         │
│ Slot 1: [tag|value]         │    │ Slot 1: [tag|value]         │
│ ...                         │    │ ...                         │
└─────────────────────────────┘    └─────────────────────────────┘

SlabMeta[] (small Vec)
┌─────────────────────────────┐
│ freelist_head: u32          │  ← Per-slab slot freelist
│ bump_cursor: u32            │  ← Sequential allocation pointer
│ occupied: u32               │  ← Slot count
│ next_free_slab: u32         │  ← Slab freelist chain
└─────────────────────────────┘
```

Each slab is allocated independently — no contiguous backing array that needs reallocation.

### Allocation Strategy

1. **Slab freelist head**: O(1) access to a slab with space
2. **Slot freelist (LIFO)**: Reuse recently-freed slots for cache locality
3. **Bump allocation**: Sequential allocation when slot freelist is empty
4. **Pop exhausted slabs**: Remove from slab freelist when full
5. **Growth** (dynamic mode): Allocate new slab when slab freelist is empty

### Remove: LIFO Behavior

When removing from a **full** slab, that slab is pushed to the **front** of the slab freelist. This means:

- The next insert uses cache-hot memory (just touched by the remove)
- High-churn workloads stay concentrated in fewer slabs
- Better cache utilization overall

### Per-Slab Freelists

Unlike global freelists, each slab maintains its own chain:

- **Cache locality**: Freed slots reused LIFO within the same slab
- **Independent draining**: Slabs can be fully emptied without affecting others
- **No cross-slab pointers**: Simpler invariants, no fragmentation across slabs

### Why Direct mmap? (Unix)

On Unix systems, `nexus-slab` bypasses `std::alloc` and calls `mmap` directly:

| | mmap | std::alloc |
|---|---|---|
| p999 | 40-48 cycles | 50-60 cycles |
| max | 500-800K cycles | 1.5-2M cycles |
| Huge pages | ✓ | ✗ |
| mlock | ✓ | ✗ |

The system allocator adds bookkeeping overhead. For the last 10-20% of tail latency, direct mmap wins. Non-Unix platforms fall back to `std::alloc` with the same API (minus `huge_pages` and `mlock`).

## Usage

### Dynamic Slab (grows as needed)
```rust
use nexus_slab::DynamicSlab;

// Pre-allocate for expected capacity
let mut slab: DynamicSlab<u64> = DynamicSlab::with_capacity(10_000)?;

// O(1) operations
let key = slab.insert(42);
assert_eq!(*slab.get(key), 42);

let value = slab.remove(key);
assert_eq!(value, 42);

// Grows automatically when needed (allocates new slab, never copies)
for i in 0..100_000 {
    slab.insert(i);
}
```

### Fixed Slab (pre-allocated, no growth)
```rust
use nexus_slab::{SlabBuilder, FixedSlab, Full};

// All memory allocated upfront
let mut slab: FixedSlab<Order> = SlabBuilder::new()
    .fixed()
    .capacity(100_000)
    .build()?;

// Returns Err(Full) when exhausted — no surprise allocations
match slab.try_insert(order) {
    Ok(key) => { /* ... */ }
    Err(Full(value)) => { /* handle backpressure */ }
}
```

### Builder API
```rust
use nexus_slab::SlabBuilder;

let slab: DynamicSlab<Order> = SlabBuilder::new()
    .capacity(100_000)           // Initial capacity hint
    .slab_bytes(2 * 1024 * 1024) // 2MB slabs (matches huge page size)
    .huge_pages(true)            // Unix: use MAP_HUGETLB
    .mlock(true)                 // Unix: lock pages in RAM
    .build()?;
```

### Memory Control (Unix)
```rust
// Huge pages reduce TLB pressure for large slabs
let slab: DynamicSlab<Order> = SlabBuilder::new()
    .capacity(1_000_000)
    .huge_pages(true)  // Requires: echo 512 > /proc/sys/vm/nr_hugepages
    .build()?;

// mlock prevents swap-induced latency spikes
let slab: DynamicSlab<Order> = SlabBuilder::new()
    .capacity(100_000)
    .mlock(true)  // Requires: CAP_IPC_LOCK or sufficient RLIMIT_MEMLOCK
    .build()?;
```

## API

### Core Operations

| Method | DynamicSlab | FixedSlab | Description |
|--------|-------------|-----------|-------------|
| `insert(value)` | `Key` | — | Insert, grow if needed (panics on alloc failure) |
| `try_insert(value)` | — | `Result<Key, Full>` | Insert, returns `Err` if full |
| `get(key)` | `&T` | `&T` | Get reference by key |
| `get_mut(key)` | `&mut T` | `&mut T` | Get mutable reference |
| `remove(key)` | `T` | `T` | Remove and return value |
| `contains(key)` | `bool` | `bool` | Check if key is occupied |
| `len()` | `usize` | `usize` | Number of occupied slots |
| `capacity()` | `usize` | `usize` | Total slots available |

### Vacant Entry Pattern

For self-referential structures:
```rust
// DynamicSlab
let entry = slab.vacant_entry();
let key = entry.key();
entry.insert(Node { self_key: key, data: 42 });

// FixedSlab
if let Some(entry) = slab.try_vacant_entry() {
    let key = entry.key();
    entry.insert(Node { self_key: key, data: 42 });
}
```

## Key Design

Keys encode `(slab_index, slot_index)` in a `u64`. Keys are valid until removed:
```rust
let key = slab.insert(42);
assert!(slab.contains(key));

slab.remove(key);
assert!(!slab.contains(key));  // Key no longer valid
```

**Note**: There is no generation counter — reusing a key after removal is undefined behavior. The caller is responsible for tracking key validity.

## When to Use This

**Good fit:**
- Systems requiring large slabs with low latency operations
- Trading systems, matching engines
- Real-time audio/video processing
- Game servers with strict latency budgets
- Any system where p999 matters more than a few cycles on p50

**Use `slab` crate instead when:**
- Median performance is the priority
- You don't need huge pages or mlock
- Simpler dependency is preferred

## Platform Support

| Platform | Allocator | Huge Pages | mlock |
|----------|-----------|------------|-------|
| Linux | mmap | ✓ | ✓ |
| macOS | mmap | ✗ | ✓ |
| Other | std::alloc | ✗ | ✗ |

## License

MIT OR Apache-2.0
