# nexus-slab

A pre-allocated slab data structure with OS-level memory control for latency-critical systems.

## Overview

`nexus-slab` provides O(1) insert, get, and remove operations with a fixed-capacity design. Performance is **on par with the excellent [`slab`](https://crates.io/crates/slab) crate** — this is not a faster alternative. Instead, it targets systems that need explicit control over memory residency and allocation behavior.

**Use `nexus-slab` when you need:**

- `mlock()` to pin pages in RAM and prevent swap-induced latency spikes
- Huge page support (`MAP_HUGETLB`) for very large slabs with reduced TLB pressure
- Page-aligned allocation via direct `mmap`/`VirtualAlloc`
- Fixed, pre-allocated capacity with no runtime growth

**Use the `slab` crate when you need:**

- Dynamic growth
- Smaller memory footprint for small collections
- Battle-tested, widely-used implementation

## Performance

Benchmarked on Intel Core Ultra 7 155H, pinned to a physical core with turbo disabled:

| Operation | nexus-slab | slab crate |
|-----------|------------|------------|
| INSERT p50 | ~58 cycles | ~58 cycles |
| GET p50 | ~144 cycles | ~144 cycles |
| REMOVE p50 | ~140 cycles | ~134 cycles |
| p999 tails | ~900 cycles | ~900 cycles |

The two implementations perform equivalently. Choose based on features, not speed.

## Usage

```rust
use nexus_slab::{Slab, Key};

// Create and allocate
let mut slab: Slab<String> = Slab::new();
slab.alloc(10_000)?;  // Pre-allocate for 10K items

// Optional: lock pages in RAM (requires privileges)
if let Err(e) = slab.mlock() {
    eprintln!("mlock failed (may need CAP_IPC_LOCK): {}", e);
}

// O(1) operations
let key: Key = slab.insert("hello".to_string())?;
assert_eq!(slab.get(key), Some(&"hello".to_string()));

let value = slab.remove(key);
assert_eq!(value, Some("hello".to_string()));
```

## Memory Control Features

### Page Locking (`mlock`)

Prevent the OS from swapping slab memory to disk. Essential for latency-critical systems where a page fault during operation is unacceptable.

```rust
let mut slab: Slab<Order> = Slab::new();
slab.alloc(100_000)?;

// Lock all pages in physical RAM
slab.mlock()?;

// Pages remain locked until drop (or explicit munlock)
```

**Requirements:**
- Linux: `CAP_IPC_LOCK` capability or sufficient `RLIMIT_MEMLOCK`
- macOS: Generally works without special privileges
- Windows: `SeLockMemoryPrivilege`

### Huge Pages (Linux)

For very large slabs, 2MB huge pages reduce TLB misses and can improve tail latency consistency.

```rust
// Guaranteed huge pages (fails if unavailable)
let mut slab: Slab<Order> = Slab::new();
slab.alloc_hugetlb(1_000_000)?;  // 1M entries on 2MB pages

// Or request collapse of existing allocation (best-effort)
let mut slab: Slab<Order> = Slab::new();
slab.alloc(1_000_000)?;
let _ = slab.try_collapse();  // Hint to use huge pages if possible
```

**Hugetlb setup:**
```bash
# Reserve huge pages at boot or runtime
echo 512 | sudo tee /proc/sys/vm/nr_hugepages  # 512 × 2MB = 1GB
```

### Allocation Modes

```rust
// By capacity: "I need space for N items"
slab.alloc(100_000)?;  // Capacity >= 100K guaranteed

// By memory budget: "I have X bytes available"  
slab.alloc_bytes(256 * 1024 * 1024)?;  // Uses <= 256MB
```

## API

### Core Operations

| Method | Description |
|--------|-------------|
| `insert(value) -> Result<Key, Full<T>>` | Insert value, returns key |
| `get(key) -> Option<&T>` | Get reference by key |
| `get_mut(key) -> Option<&mut T>` | Get mutable reference |
| `remove(key) -> Option<T>` | Remove and return value |
| `contains(key) -> bool` | Check if key is occupied |
| `len() -> usize` | Number of occupied slots |
| `capacity() -> usize` | Total slots available |
| `is_full() -> bool` | True if at capacity |
| `clear()` | Remove all values |

### Memory Control

| Method | Description |
|--------|-------------|
| `alloc(n)` | Allocate for at least N items |
| `alloc_bytes(n)` | Allocate using at most N bytes |
| `alloc_hugetlb(n)` | Allocate on huge pages (Linux) |
| `mlock()` | Lock pages in RAM |
| `munlock()` | Unlock pages |
| `try_collapse()` | Request huge page backing (Linux 6.1+) |
| `memory_size() -> usize` | Bytes allocated |

### Vacant Entry Pattern

For self-referential structures where you need the key before inserting:

```rust
let entry = slab.vacant_entry()?;
let key = entry.key();  // Know the key before insert

let node = Node {
    self_key: key,
    data: 42,
};
entry.insert(node);
```

## Key Safety

Like the `slab` crate, keys are simple indices without generation counters. **It is the caller's responsibility to not use stale keys.** Accessing a slot after removal and reuse will return the new value, not an error.

If you need ABA protection, track key validity externally or use a different data structure.

## Platform Support

| Platform | Status |
|----------|--------|
| Linux | Full support (mlock, hugetlb, madvise) |
| macOS | Supported (mlock works, no hugetlb) |
| Windows | Experimental (`unstable-windows` feature) |

## When to Use This

✅ **Good fit:**
- Trading systems, market data handlers
- Real-time audio/video processing  
- Game servers with strict latency budgets
- Any system where page faults are unacceptable

❌ **Not ideal for:**
- General-purpose applications
- Collections that need to grow dynamically
- Small slabs (< 1000 items) — overhead not justified

## License

MIT OR Apache-2.0
