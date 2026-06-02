# nexus-shm: ShmJournal — design notes (#391)

Append-only durable log over mmap'd segments. Builds on the #390 foundation
(`Segment`, `Mapping`, `Pod`, two-tier liveness). Primary caller: FIX message
journaling for resend (#411). Aeron Archive model.

Most of the design is already resolved in `nexus-shm.md` (commit ordering,
checksum policy, liveness tier). This pins the one open question — sequence
awareness — and specifies the record/commit/recovery/segment layout.

---

## Resolved already (from nexus-shm.md, for reference)

- **Commit ordering** is the correctness property: write body → release fence →
  publish commit marker. Recovery scans forward, stops at first uncommitted
  record. (Aeron sentinel + PAD frame model.)
- **Checksums** deferred. The reviewed frame layout carries no checksum field,
  and a config flag wired to nothing is dead code; the commit marker alone covers
  the crash case fully. A checksum (trailing CRC + its own `commit_len`
  accounting) is a follow-up with its own layout review.
- **Liveness:** in-process journal (FIX same-process read+write) needs only
  Tier-1 atomic. Cross-process read-only attach uses Tier-2 OFD opt-in.
- **Segmented layout**, default 64 MB segment size.

---

## Open question resolved: sequence awareness → Path C (pluggable header)

`ShmJournal<H: RecordHeader>`. The journal frames `[frame header][H][payload]`
and reads/writes `H` but never interprets it.

- FIX (#411) uses `H = FixHeader { seq: u64, timestamp: u64 }` and gets
  `read_range` by sequence.
- Non-FIX callers use `H = ()` — zero per-record overhead, position-only
  semantics identical to Path A.

Rationale: Path A forces a separate seq→position indexer for FIX resend (the
doc's own con); Path B bakes FIX semantics (seq+ts) into every record including
non-FIX callers. Path C is general without the waste — the header is the
caller's, the framing and recovery are ours.

`RecordHeader` is `Pod` (reuses the #390 trait) + a const size; `()` qualifies
trivially. No heap, fixed layout, valid for recovery scanning.

---

## Record layout

Each record starts on an 8-byte boundary and opens with an 8-byte frame header:

```
┌──────────────┬────────────┬─────────┬───────────┬───────────┬──────────┐
│ commit_len   │ frame_type │  flags  │  header H │  payload  │ padding  │
│   u32 (LE)   │  u16 (LE)  │ u16 (LE)│ size_of H │ len bytes │  to 8    │
└──────────────┴────────────┴─────────┴───────────┴───────────┴──────────┘
     ^commit marker (published last)
```

This is the Aeron frame model: header size == alignment (8). The original i32
sign-as-sentinel was Aeron's accommodation of Java's lack of unsigned types; we
have no such constraint, so an explicit type discriminant is cleaner and removes
an edge case (below).

- `commit_len` is the **commit marker**, an aligned `u32` written **last** with
  `Ordering::Release`. It is the **unpadded** body size (`header H + payload`).
  - `0` — uncommitted / end of log. Recovery stops here. Always unambiguous.
  - `> 0` with `frame_type == DATA` — committed record. `payload_len =
    commit_len - size_of::<H>()`; reader advances `8 + align_8(commit_len)`.
  - `> 0` with `frame_type == PAD` — dead space at a segment tail too small for
    a record. `commit_len` is the full span to skip; reader advances
    `align_8(commit_len)`, yields nothing.
- `flags` is reserved (0) for future use (CRC, compression, …).

Because the frame header is 8 bytes and records are 8-aligned, every footprint
(`8 + align_8(body)`) is a multiple of 8, so the space left at a segment tail is
always either 0 or ≥ 8 — a PAD header always fits. **The "remaining == marker
size" collision that an i32 (4-byte) marker allowed is structurally impossible.**

`u32` body length caps a record at 4 GiB (and `try_claim` rejects anything larger
than the segment), with no sign trick. A claim that can't fit an empty segment →
`RecordTooLarge`.

**Endianness:** the frame header and `H` fields are native byte order (LE on
x86-64, the only supported target). Cross-process readers on the same host see
the same order; the on-disk format is not portable across differing-endian
architectures (explicit-LE would be future work).

---

## Commit protocol (write path)

`try_claim(header, len) -> Result<WriteClaim, JournalError>`:

1. Compute footprint (`8 + align_8(body)`). If it doesn't fit the current
   segment's remaining space, write a PAD frame over the tail and roll to the
   next segment (see Segments). If it can't fit an empty segment →
   `RecordTooLarge`.
2. Reserve the region (advance the writer's local tail). The `commit_len` slot
   stays `0`.
3. Return `WriteClaim` exposing `as_mut_slice()` over the payload region (the
   header is supplied at `try_claim` and written at commit).

`WriteClaim::commit(self)`:

1. Write header `H` and the `frame_type = DATA` / `flags = 0` fields.
2. Zero the next slot's `commit_len` (so recovery still stops there over stale
   bytes), then store this record's `commit_len` (`> 0`) with `Ordering::Release`
   — the single store that publishes the record.

Drop without commit leaves `commit_len == 0`; the space is reclaimed on recovery
as the stop point. SPSC single-writer means an uncommitted claim is always the
tail. RAII commit mirrors nexus-logbuf's `WriteClaim`.

Hot path cost: one memcpy of the payload + a few small stores. No syscall, no
allocation.

---

## Read path

`next_record() -> Result<Option<ReadRecord<'_>>, JournalError>`:

1. Load `commit_len` at the reader cursor with `Ordering::Acquire`.
2. `0` → caught up, return `Ok(None)`.
3. `frame_type == PAD` → advance by `align_8(commit_len)`, retry.
4. `frame_type == DATA` → yield `ReadRecord { header: H, payload: &[u8] }` and
   advance cursor by `8 + align_8(commit_len)`.

The header is returned **by value** (`H: Pod` is `Copy`); the payload is a
zero-copy `&'a [u8]` into the mapping, its lifetime tied to the reader so a
segment can't be unmapped under a live record. Returning a result (not an
option) lets a real I/O failure while opening a rolled segment surface as `Err`
instead of being mistaken for end-of-log — `NotFound` alone means "caught up".

Cross-process readers open segments and run the same scan. `commit_len`'s
acquire load paired with the writer's release store gives the happens-before
edge across the process boundary.

---

## Recovery

On `open`, scan the **last** segment from its start:

1. Walk records by `commit_len` (skipping PAD frames) until the first
   `commit_len == 0` — that offset is the write tail.
2. The writer resumes appending at the recovered tail.

No unwinding, no allocation — a forward pointer-walk. The sentinel guarantees
recovery never reads a committed-but-torn record (the marker is the last store).

---

## Segments

- Files named `{base}.{index}` (e.g. `journal.0`, `journal.1`), each a #390
  `Segment` of `segment_size` bytes.
- Writer rolls to `index + 1` when a record doesn't fit the current tail,
  PAD-framing the leftover. Segment roll is the only place a new file is
  created/mapped.
- Reader follows the same sequence, mapping the next segment when it exhausts
  the current one. A cross-process read-only reader that hits a `0` marker at a
  segment tail (rather than mid-segment) probes for `{base}.{index+1}`; if it
  exists the writer has rolled, so the reader opens it and continues. In-process
  readers share the writer's segment list directly. (A shared metadata region
  for the active segment index is possible but unnecessary for SPSC roll — the
  filename probe is the discovery mechanism.)
- `read_range` (FIX, when `H = FixHeader`): a thin layer over the position scan
  — locate the start segment, scan forward yielding records whose `seq` falls
  in range. O(1) recent-seq lookup via an optional fixed-size ring index is
  deferred (not needed for correctness; note it as future work).

> `read_range` lives behind an impl bound `where H: SeqHeader` so it's only
> available when the header actually carries a sequence. `()` callers never see
> it. Keeps FIX semantics off the general primitive while still living in one
> crate.

---

## API sketch

```rust
let cfg = JournalConfig { segment_size, map };
let (mut writer, mut reader) = Journal::<FixHeader>::open(base_path, cfg)?;

// Write (hot path)
let mut claim = writer.try_claim(FixHeader { seq, timestamp }, payload.len())?;
claim.as_mut_slice().copy_from_slice(payload);
claim.commit();

// Sequential read — Result<Option<_>>: Err is a real I/O fault, not end-of-log
while let Some(rec) = reader.next_record()? {
    process(rec.header(), rec.payload());
}

// FIX resend — only when H: SeqHeader
for rec in reader.read_range(start_seq..=end_seq)? {
    retransmit(rec.payload());
}
```

---

## Scope for the PR

- `Journal<H>` open/recovery, `WriteClaim` (commit protocol), `ReadRecord`,
  segment roll, `JournalConfig`, `()` and a `FixHeader` reference header.
- `read_range` behind `H: SeqHeader`.
- Tests: roundtrip, multi-segment roll, recovery (uncommitted tail), PAD skip
  including the `remaining == frame-header` boundary, range query, too-large /
  empty rejection.
- Criterion bench for `try_claim`+`commit` (hot path) and `next_record`.

Out of scope: checksum (deferred, above), the O(1) ring index, MPSC (SPSC only),
the durable fsync policy (mmap-is-persistence; fsync is a caller concern).

## Open questions — resolved in review (#416)

1. **Frame marker** — moved from i32 sign-as-sentinel to an 8-byte frame header
   (`u32 commit_len` + `u16 frame_type` + `u16 flags`). Header size == alignment,
   so footprints are multiples of 8 and the "remaining == marker size" sentinel
   collision is structurally impossible. The i32 was Aeron's Java-unsigned
   workaround, which we don't need.
2. **PAD on graceful drop** — not needed. SPSC means an uncommitted claim is
   always the tail; "leave 0, recovery stops" suffices.
3. **`read_range` return** — borrowing iterator, matches `next_record`; caller
   `.collect()`s if needed.
4. **`next_record` signature** — returns `Result<Option<_>>` so real I/O errors
   surface instead of being swallowed as end-of-log.
5. **Header access** — returned by value (`H: Pod` is `Copy`); payload stays
   zero-copy `&[u8]`.
