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
│ freelist_head: u32          │  ← Per-slab freelist for draining
│ bump_cursor: u32            │  ← Sequential allocation pointer
│ occupied: u32               │  ← Count for slab selection
└─────────────────────────────┘
```

Each slab is allocated independently — no contiguous backing array that needs reallocation.

### Allocation Strategy

1. **Freelist first (LIFO)**: Check active slab's freelist for recently-freed slots
2. **Bump allocation**: Sequential allocation when freelist is empty (fresh slab)
3. **Cross-slab fallback**: Search other slabs when active slab exhausted
4. **Growth** (dynamic mode): Allocate new slab when all are full

LIFO freelist reuse means inserts write to cache-hot memory, reducing cache misses on high-churn workloads.

### Per-Slab Freelists

Unlike global freelists, each slab maintains its own chain. This enables:

- **Cache locality**: Freed slots are reused LIFO, so the next insert writes to cache-hot memory
- **Slab affinity**: After a remove, the active slab switches to where the free slot is, concentrating activity
- **Independent growth**: New slabs don't touch existing slab structures

Allocation priority:
1. **Freelist** (LIFO): Reuse recently-freed slots from active slab
2. **Bump cursor**: Allocate untouched slots if freelist is empty
3. **Cross-slab**: Search other slabs when active slab is exhausted

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
let key = slab.insert(42)?;
assert_eq!(*slab.get(key), 42);

let value = slab.remove(key);
assert_eq!(value, 42);

// Grows automatically when needed (allocates new slab, never copies)
for i in 0..100_000 {
    slab.insert(i)?;
}
```

### Fixed Slab (pre-allocated, no growth)
```rust
use nexus_slab::FixedSlab;

// All memory allocated upfront
let mut slab: FixedSlab<Order> = FixedSlab::with_capacity(100_000)?;

// Returns Err(Full) when exhausted — no surprise allocations
match slab.insert(order) {
    Ok(key) => { /* ... */ }
    Err(Full { value }) => { /* handle backpressure */ }
}
```

### Builder API
```rust
use nexus_slab::SlabBuilder;

let slab: DynamicSlab<Order> = SlabBuilder::new()
    .capacity(100_000)          // Initial capacity hint
    .slab_bytes(2 * 1024 * 1024) // 2MB slabs (matches huge page size)
    .huge_pages(true)           // Unix: use MAP_HUGETLB
    .mlock(true)                // Unix: lock pages in RAM
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

| Method | Complexity | Description |
|--------|------------|-------------|
| `insert(value)` | O(1) | Insert value, returns key |
| `get(key)` | O(1) | Get reference by key |
| `get_mut(key)` | O(1) | Get mutable reference |
| `remove(key)` | O(1) | Remove and return value |
| `contains(key)` | O(1) | Check if key is occupied |
| `len()` | O(1) | Number of occupied slots |
| `capacity()` | O(1) | Total slots available |

### Vacant Entry Pattern

For self-referential structures:
```rust
let entry = slab.vacant_entry()?;
let key = entry.key();

let node = Node { self_key: key, data: 42 };
entry.insert(node);
```

## Key Design

Keys encode `(slab_index, slot_index, generation)` in a `u64`. Generation counters detect use-after-remove:
```rust
let key = slab.insert(1)?;
slab.remove(key);
slab.insert(2)?;  // Reuses same slot with new generation

assert!(slab.get(key).is_none());  // Old key returns None, not new value
```

## When to Use This

**Good fit:**
- Trading systems, matching engines
- Real-time audio/video processing
- Game servers with strict latency budgets
- Any system where p999 matters more than p50

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
