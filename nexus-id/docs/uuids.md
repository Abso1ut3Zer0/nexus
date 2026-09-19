# UUIDs and ULIDs

Three 128-bit unique identifiers with different sortability and time-leak
tradeoffs.

## Decision tree

```text
Need a 128-bit ID?
├── Do you want it to be time-sortable?
│   ├── Yes → UuidV7 (binary) or Ulid (string-friendly)
│   └── No  → UuidV4 (random)
└── Are you logging/urlifying it?
    ├── UuidV4/V7 → 36-char hyphenated or 32-char compact
    └── Ulid      → 26-char Crockford Base32 (URL-safe, no hyphens)
```

## UuidV4 — random

```rust
use nexus_id::{UuidV4, Uuid};

let mut gen = UuidV4::from_entropy();  // seeds PCG from OsRng
let id: Uuid = gen.generate();

println!("{}", id);  // "f47ac10b-58cc-4372-a567-0e02b2c3d479"
```

~48 cycles per ID. Uses PCG internally — fast and well-distributed but *not*
cryptographically secure. Don't use for session tokens or anything secret.

Collision resistance: 122 random bits (6 bits are version/variant). Generate
a trillion UUIDs per second for a decade and your birthday collision
probability is still < 10⁻⁹.

## UuidV7 — time-ordered

```rust
use nexus_id::{UuidV7, Uuid};

let mut gen = UuidV7::from_entropy();
let id: Uuid = gen.generate();
```

RFC 9562. First 48 bits are a Unix millisecond timestamp, remaining 74 bits
are random (plus 6 bits version/variant). k-sortable — two IDs generated in
different milliseconds sort by time. Within the same millisecond, ordering
is random.

**Why prefer V7 over V4:** database indexes on UUID columns fragment badly
with random V4s because inserts go everywhere. V7s append to the right of
the index (timestamp prefix) — much friendlier to B-trees.

**Why you might not want V7:** it leaks creation time. If your IDs are
user-visible and you care about that (e.g. exposing a user's signup date via
an exposed resource ID), use V4.

## Ulid

```rust
use nexus_id::{UlidGenerator, Ulid};
use std::time::Instant;

let mut generator = UlidGenerator::from_entropy(epoch, unix_base);
let id: Ulid = generator.next(Instant::now()).unwrap();

println!("{}", id);  // "01HKXB7VHN6FV2T7W8P9K3M4R5"
```

`next` returns `Result<Ulid, SequenceExhausted>` — matching the `ulid`
crate's `Generator::generate()`. Exhaustion requires overflowing the 80-bit
random field within a single millisecond (physically impossible), so callers
typically `.unwrap()`.

26 characters, Crockford Base32 (no ambiguous `0/O`, `1/I/L`). Case-insensitive
on parse. Time-sortable like UuidV7, but the monotonic guarantee is *stronger*:
`UlidGenerator` increments the random tail within the same millisecond, so
two Ulids from the same generator never collide or reorder within a tick.

ULIDs are the friendliest option when IDs end up in URLs, filenames, or
human-facing UIs.

## Parsing

All three types implement `FromStr` and `TryFrom<&[u8]>`:

```rust
use nexus_id::{Uuid, Ulid};

let u: Uuid = "f47ac10b-58cc-4372-a567-0e02b2c3d479".parse()?;
let l: Ulid = "01HKXB7VHN6FV2T7W8P9K3M4R5".parse()?;
# Ok::<(), Box<dyn std::error::Error>>(())
```

Parsers are SIMD-accelerated (SSE2 hex decode). Parsing is typically faster
than allocating the resulting `String` would be.

## Interop

- `uuid` feature: `From`/`Into` between `nexus_id::Uuid` and `uuid::Uuid`.
- `serde` feature: standard string serialization for all three types.
- `bytes` feature: `BufMut::put_uuid(&id)` for wire protocols.
