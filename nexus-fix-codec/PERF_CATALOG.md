# nexus-fix-codec Performance Optimization Catalog

Systematic record of the optimizations applied to the FIX read/write
primitives, and — just as importantly — the optimizations that were
*tried and rejected*. Intended as an audit reference so future work
doesn't rediscover dead ends or miss the context on why something was
(or wasn't) done.

The hot paths are `FieldReader::next_field` (decode) and
`FieldWriter::field` / `encode_field` (encode). SIMD scanning targets
SSE2 (x86_64 baseline), AVX2, and AVX-512BW via compile-time `cfg`
dispatch, with a SWAR + scalar fallback for the tail and other
architectures. Build with `target-cpu=native` (or `+avx2`) to get the
wide tiers; a default `cargo build` is SSE2-only.

Numbers below were measured on an Intel Core Ultra 7 165U (Meteor Lake;
AVX2 + BMI2, **no** AVX-512), pinned with `taskset -c 0`, best-of-N to
suppress turbo/thermal noise. See [BENCHMARKS.md](./BENCHMARKS.md) for
the full tables and methodology.

---

## Methodology notes (read first)

Two measurement hazards dominated this work and are worth stating up front:

- **Measurement floor.** The original cycle harness timed a single call
  between a bare `rdtsc()` pair. That bottoms out at a ~16–30 cycle
  floor (the timestamp + `black_box` barrier cost), which *masks* any
  kernel cheaper than the floor. The scan and `checksum()` rows all read
  a flat ~16 cyc regardless of size — pure floor. The harness now
  **batches** `BATCH` back-to-back calls between a single
  `lfence`-serialized `rdtsc`/`rdtscp` pair and divides, resolving
  per-call costs well below the floor. (`examples/perf_scan.rs`.)

- **Code-layout noise.** These kernels are 150–180 cycles, and a change
  to *one* function shifts the binary layout enough to move an
  *unrelated* function's measured p50 by ±8–10 cycles. Several apparent
  "regressions" were this artifact. The defence: prove the machine code
  of the unchanged function is byte-identical (`cargo asm` diff), and
  use `perf stat` **instructions-retired** (layout- and
  frequency-independent) when cycle counts are ambiguous.

---

## Writer: `encode_field` / `write_tag` (`src/writer.rs`) — OPTIMIZED

The single real win of this pass. The original `encode_field` wrote each
byte through a separately bounds-checked store, and copied the value via
`copy_from_slice` (a `memcpy` *call* for a runtime length). For a typical
field that is ~7–8 per-byte bounds-check branches plus a call.

### Single up-front capacity check + unchecked interior

`encode_field` now computes the bytes the field needs and bounds-checks
**once**, then writes the tag digits, `=`, value, and SOH through
unchecked stores:

```rust
let need = digits + 2 + value.len();
assert!(pos <= buf.len() && need <= buf.len() - pos, ...);
// SAFETY: assert proves pos + need <= buf.len(); all writes land in pos..pos+need.
unsafe { /* write_tag_unchecked; '='; copy_nonoverlapping(value); SOH */ }
```

- The capacity check is `assert!` (release-active), not `debug_assert!`:
  it is the **sole guard** between caller-provided buffer sizing and the
  unchecked writes, and buffer length is external, fallible input.
  Downgrading it to `debug_assert!` would make a too-small buffer silent
  UB in a release trading build. (The `digits == tag_digits(tag)` /
  in-bounds-span contract inside `write_tag_unchecked` *is* a
  `debug_assert!` — it is guaranteed by construction, so it's a
  development tripwire at zero release cost.)
- The `need` computation is overflow-free (`digits <= 10`,
  `value.len() <= isize::MAX`), and `pos <= buf.len()` is checked first so
  the `buf.len() - pos` subtraction cannot underflow.
- `copy_from_slice` → `core::ptr::copy_nonoverlapping`: skips the
  length-equality assert and the surrounding bounds machinery, inlining
  the value copy. Non-overlap is guaranteed by the borrow checker
  (`value: &[u8]` cannot alias `buf: &mut [u8]`).
- `write_tag` magnitude cascade → `tag_digits` + `write_tag_unchecked`
  (back-to-front `% 10` / `/ 10`). When `tag` is a compile-time constant
  — the generated-encoder case — `tag_digits` folds to a constant and
  the digit loop unrolls to straight-line stores, so the per-field
  overhead nearly vanishes in real usage.

### Latent bug fixed

The old `write_tag` had no branch beyond 5 digits, so tags `>= 100000`
emitted a corrupt `:` byte (digit `10 + b'0'`) and the wrong length. The
new path handles 1–10 digit tags up to `u32::MAX` correctly. (No real
FIX tag is that wide, but the rewrite is strictly more correct.)

### Codegen verification

`cargo asm` confirms the per-byte bounds checks collapse to a single
`cmp/ja → panic_fmt`, with the panic path out-of-line (cold). The value
copy is a clean `memcpy` with no length assert.

### Soundness

Adversarially reviewed: the full `(buf.len(), pos, tag, value)` grid was
brute-forced (buf_len 0..=40 × pos 0..=42 incl. `pos > buf_len`/empty ×
all tag-width boundaries incl. `u32::MAX` × value_len 0..=20) with zero
out-of-bounds writes, and all 2³² `u32` values verified that
`tag_digits(tag)` equals the true width and `write_tag_unchecked` writes
exactly that many correct digit bytes. Miri clean across the writer tests.

### Result

~**−12%** on a 15-field NewOrderSingle encode (AVX2, batched/fenced:
178 → 156 cyc; 11.8 → 10.3 cyc/field). Single-shot deltas were larger
(AVX2 158→134, SSE2 172→132); the bounds-hoist is SIMD-independent so it
helps both tiers. Real-world (constant-tag) gains are larger than this
runtime-tag worst case.

---

## Reader: `find_next_soh` / `next_field` (`src/reader.rs`) — LEFT AS-IS

Investigated thoroughly; **already near-optimal**, left unchanged.

- The scan/checksum fusion (`cmpeq` for SOH + `PSADBW` for checksum on
  one chunk load) is sound; the SIMD mask cache means the chunk loop
  fires once per ~16/32/64 bytes, not per field.
- `parse_tag` compiles to a `lea`-based `tag*10 + digit` chain (no
  `imul`, no `div`); the structural validation is 3 well-predicted
  branches.
- Decode is ~11 cyc/field, and **AVX2 ≈ SSE2** for full decode — the
  scan is not the bottleneck (it's ~20–26 cyc); the per-field cost is
  real tag-parse + checksum + bookkeeping work that's already lean.

The decode machine code (`find_next_soh`, the inlined `next_field`) is
**byte-identical before and after this pass** — every reader experiment
below was reverted.

---

## `checksum()` standalone (`src/reader.rs`) — LEFT AS-IS

The encode-side body sum (`data.iter().map(|&b| b as u32).sum() as u8`)
*looks* scalar but LLVM auto-vectorizes it well: because the result is
`as u8`, it accumulates in **byte lanes** with `vpaddb` (mod-256 wrap is
correct) and does a single `vpsadbw` reduction at the end. Measured
**0.02 cyc/byte** at 512 B once the harness floor was removed. A
hand-rolled kernel would not beat it. Left untouched.

---

## Rejected approaches

These were implemented, measured, and reverted. Documented so they
aren't re-attempted.

### Branchless `swar_to_byte_mask` (multiply-shift gather)

The SWAR tail converts a high-bit-per-byte mask to bit-per-byte via a
`trailing_zeros` loop. A branchless gather
(`(m >> 7).wrapping_mul(0x0102_0408_1020_4080) >> 56`) is correct
(verified exhaustively over all 256 patterns — the test
`swar_mask_conversion_exhaustive` stays as a guard) and tempting.

**Rejected:** measured slower on realistic decode. The result feeds
`emit_soh_mask` on the **critical path** (it becomes the returned SOH
position), so the multiply's latency lands directly on the dependency
chain. For the common sparse case (one SOH in the 8-byte tail window)
the loop runs a *single* cheap iteration and wins by doing less work.
Branchless ≠ faster when the branchy version does less for the common
input.

### `parse_tag` digit cap (`MAX_TAG_DIGITS`)

Capping the digit loop at 9 (the widest `u32`-safe width) bounds
worst-case work and prevents silent `u32` overflow on adversarial
all-digit input.

**Rejected (for now):** a constant trip-count ceiling let LLVM unroll
the digit loop, pessimizing the common 1–2 digit case across 15 fields.
The robustness benefit is real but did not justify a hot-path
regression; the overflow is also benign for the checksum (mod 256
survives the wrap) and a `>9`-digit tag fails the trailing-`=` check
anyway. Parked, not killed — revisit if a hardened decoder variant is
wanted.

### Tag-10 exclusion as a `#[cold] #[inline(never)]` helper

The FIX-checksum tag-10 exclusion loop auto-vectorizes inside
`next_field` into a ~30-instruction AVX2 block with a `>= 32`-byte fast
path that is **dead** (tag 10 is always the 7-byte `10=XXX\x01`).
Out-of-lining it shrank the hot decode function from 252 → 187
instructions (36 → 3 vector ops; the 3 survivors are the legitimate scan
PSADBW).

**Rejected:** despite *fewer* instructions, it **regressed decode ~8%**
(reproducible: ~4.65B → ~5.03B cycles for 20M decodes; IPC 5.9 → 4.8).
The `call` into the `#[inline]` hot loop clobbers caller-saved registers
and wrecks the loop's register allocation — a cost larger than the
footprint it reclaims. Crucially, the dead vector block sits *past a
not-taken branch*, so it is never fetched/executed in a warm loop and
costs **zero** cycles there; its only cost is static I-cache footprint,
which this fix made *worse* (the call) rather than better. Lesson:
out-lining a cold path is not free when it's called from inside an
inlined hot function.

### Deferred PSADBW horizontal sum

The per-chunk `hsum_sad_*` reduction (~5 instrs) and the per-chunk
`self.checksum` store could be deferred — accumulate lane sums in a
vector across chunks and reduce once.

**Not done:** off the critical path (OoO hides the SAD→hsum→add behind
the `cmpeq`→branch chain), and with mask caching the chunk loop usually
runs *once* per `next_field` call, so there's nothing to defer for the
realistic short-field workload. It only helps value-heavy messages
(long values spanning many chunks), and storing a SIMD accumulator in
the struct (cfg-gated, per-tier) adds complexity disproportionate to
that narrow gain.

---

## Value-type layer: error contract + encode unification

The FIX 5.0 SP2 domain-type batch (`FixMonthYear`, `FixTenor`,
`FixTzTime`/`FixTzTimestamp`, `char`/text/multi-value parsers) plus the
`Option → Result` migration. The perf-relevant decisions:

- **`Option<T>` → `Result<T, FixValueError>` is free on the happy path.**
  `Ok(v)` lowers identically to `Some(v)`; `FixValueError` is a one-byte,
  `Copy`, fieldless enum, and an error value is only *constructed* on the cold
  failure path. A successful parse has the same codegen as before — the
  type-parser numbers in BENCHMARKS.md are expected to be unchanged by this
  migration (re-confirm with a controlled run).

- **Encode unification: the writer's unchecked pattern does NOT transfer.**
  The plan was to apply `encode_field`'s "single up-front `assert!` +
  unchecked interior" to `FixDecimal`/`Date`/`Time`/`Timestamp::encode`. On
  inspection that win doesn't exist here: those encoders route digits through
  `encode_u64`/`encode_u64_padded`, which build into a fixed stack buffer and
  emit **one** `copy_from_slice` — there is no per-output-byte bounds-check
  loop like the old writer had. So the change made is the single up-front
  capacity `assert!` only: it gives an atomic, clearly-messaged failure
  (replacing a mid-write index panic) and hands LLVM the length invariant to
  elide the handful of in-method `buf[pos]` checks. Hand-written `unsafe`
  stores were deliberately NOT added — they would buy a couple of
  cross-function copy-length checks at the cost of real UB risk. The data
  structure already avoids the per-byte tax.

- **New types reuse the spine.** Every numeric/temporal type routes its digit
  run through `parse_unsigned_digits` (SWAR) and emits through the shared
  `DIGIT_PAIRS` LUT; fixed-width codes validate via one
  `AsciiTextStr::try_from_bytes` printable scan; multi-value parsers validate
  once then yield borrowing iterators (the `MultipleStringValue` iterator uses
  `AsciiTextStr::from_bytes_unchecked` on validated subslices — miri-clean).

### Measured cost — floor-free (`benches/perf_parse_cycles.rs`, `taskset -c 0`, turbo on)

The cycle harness was rewritten from single-shot `rdtscp(); f(); rdtscp()` to
**batched/fenced** — each sample times `BATCH = 100` back-to-back calls between
one `lfence`-fenced `rdtsc`/`rdtscp` pair and divides (the same fix already in
`examples/perf_scan.rs`). A single-shot pair bottoms out at a **~16–20 cycle
floor** that masked the real cost of every cheap kernel — the older "Type
parsers" table in BENCHMARKS.md is floor-inflated by that amount and should be
re-run on the batched harness. p50 (turbo on) is the stable signal; the 4-figure
`max` outliers are scheduler deschedules.

| type | parse (cyc, p50) | encode (cyc, p50) |
|---|--:|--:|
| `char` / `bool` | ~2 | ~1 |
| `FixDate` | 8 | 6 |
| `FixTime` (no-frac / frac) | 18 / 26 | 10 / 22 |
| text (`AsciiTextStr`) | 7 | copy |
| `FixMonthYear` | 8–12 | 6–26 |
| `FixTenor` | 28 | 11 |
| multi-char / multi-string | 36 / 35 | — |
| `parse_fix_int` (1–19 digit) | 21–38 | 19–25 |
| `FixDecimal` | 28–77 | 21–42 |
| `FixTimestamp` | 32–44 | 60–77 |
| `FixTzTime` / `FixTzTimestamp` | 28 / 35 | 24 / 69 |

**Cost ladder:** trivial char/bool ≈ 2 cyc → fixed-width date/time/MonthYear 6–18
→ SWAR numerics (int/uint/seqnum/Tenor) 21–39 → decimal 52–77 → the timestamp
family 32–77. Every numeric routes through the SWAR spine
(`parse_unsigned_digits`, ~2 cyc/digit); the shared 200-byte `DIGIT_PAIRS` LUT
carries all encode.

### The one hot-path target: `i128` decompose

`FixTimestamp::encode` (60–77) and `FixTzTimestamp::encode` (69) are the heaviest
value-layer paths, and they track each other because both go through
`FixTimestamp::decompose()` — an `i128` `div_euclid`/`rem_euclid` that splits
nanos-since-epoch into (date, time). **The 128-bit division is the cost.** If a
timestamp encoder ever lands on a hot loop, that is the single thing to attack:
reciprocal-multiply instead of 128-bit division, or keep the epoch math in `i64`
(the wire domain fits — years ≤ 9999). Parse is cheaper (32–44) because it builds
the instant additively, with no decompose.

### Leap second costs nothing

Accepting `23:59:60` (FIX permits `SS=60`) uses a sentinel: the leap second lands
in `nanos_since_midnight ∈ [NANOS_PER_DAY, +1s)`, which the `FixTime` accessors
and encoder branch on. Measured: `FixTime` parse is **18 cyc normal vs 18 cyc
leap** — the extra branch is free on the happy path. `:60` is restricted to
`23:59` (elsewhere it would alias a normal time, e.g. `00:00:60 == 00:01:00`).

### Error contract: three axes, zero hot-path tax

`Result<T, FixValueError>` is free on success (`Ok` lowers like `Some`; the
one-byte `Copy` error enum is built only on the cold path). The contract is a
two-axis split, never conflated: **presence** and **validity** are orthogonal.
Frame-structure → `DecodeError` (reader). Then, per field: presence → `Option`
(the accessor returns `None` when the tag is absent); validity → `Result`
(`FieldView::checked`, on a *present* field). `FixValueError` therefore carries
only content variants — there is no `Missing` arm — because absence is the
accessor's `None`, never an error.

### Codegen integration: the FieldView flyweight (landed)

`nexus-fix-codegen` is the schema→codec layer; the codec does the real work. The
generated accessors are a **flyweight over the read buffer**: the decode does one
scan recording a `FieldSpan` per field, and each accessor returns
`Option<FieldView<'buf, T>>` — `None` if absent, else a zero-sized-after-inlining
handle that parses the value *on demand* via the monomorphized `FromFixValue`
trait (no `fn`-pointer indirection). One method per field, not five: the handle
carries `get` / `checked` / `is_valid` / `as_bytes`.

This realizes the two-axis contract directly. Presence is the outer `Option`;
validity is `FieldView::checked() -> Result<T, FixValueError>`. The bare value
parsers stay canonical — the generator's duplicate `Option` parsers (`convert.rs`)
were **removed**, and DATA-length encoding uses `encode_fix_seqnum` (byte-exact
drop-in for the removed `format_uint`). `FieldView::new` is a fallible constructor
(`Option<Self>`, like `NonZero::new`) so a `FieldView` always denotes a present
field. The header decoder uses the same shape. 40/40 roundtrips pass (decode +
framed encode).

- **Staged (parse-once memoization):** the flyweight re-parses on each `get()`.
  The cost ladder above *is* the caching policy: memoize `FixDecimal` (52–77) and
  the timestamp family (32–77) via a message-owned `Cell` the handle reads/writes;
  don't cache a 2-cyc char (the memo check costs as much as re-parsing). The
  `FieldView`/`Option` API is forward-compatible — memoization is a body change
  behind the same accessors, no signature churn.

### Framed encode: the encoder owns 8/9/10

The generated encoder is the write-side mirror. `FrameWriter` owns the framing the
wire mandates so the caller can't get it wrong: it reserves a front prefix, streams
typed body fields forward, and at `finish()` writes a **canonical** BodyLength
**right-aligned** to abut the body, then the real checksum and tag 10. Overflow is a
sticky `Result` (`EncodeError::BufferFull`) — encoding never panics on a small buffer.

The right-align is the perf-relevant trick. BodyLength (tag 9) is ASCII decimal,
variable-width, and sits at the *front* measuring everything after it — a forward
reference. Rather than leading-zero-pad (non-canonical; rejected by signature venues
like Coinbase) or memmove the body to close the slack, `finish()` writes the canonical
`8=…9=…` prefix *backwards* from a reserved boundary so it abuts `35=`. **The body
never moves** — the message just starts a few bytes into the buffer (`finish()`
returns the slice). Every byte is touched once.

Measured — full framed `NewOrderSingle` (15 fields; `taskset -c 0`, best-of-5):

| path | p50 (cyc) | cyc/field |
|---|---|---|
| `FieldWriter` raw field writes | ~131 | 8.7 |
| `FrameWriter` encode + frame | ~151 | 10.1 |

Framing costs **~20 cyc (~15%)** over raw writes — the real BodyLength compute +
right-align + checksum that produce a *valid* message (the old `FieldWriter` bench
wrote a hard-coded `9=`/`10=`). At ~10 cyc/field it's right at the per-field write
cost; the framing is nearly free, and the right-align keeps it memmove-free. The
generated ordered-header typestate monomorphizes to exactly this `FrameWriter`
sequence — zero runtime cost for the compile-time required/optional enforcement.

> **Methodology caveat:** these are `taskset`-pinned, best-of-5, but **turbo-on**
> (the canonical BENCHMARKS.md tiers are turbo-off — `FieldWriter` reads 131 here vs
> 155 canonical on identical code). The *relative* +20 cyc holds; the absolutes want
> a turbo-off rerun before they replace the canonical numbers.

### DATA field + checksum: single-pass resync

A length-prefixed DATA value (`95`/`96`, `212`/`213`, …) can contain embedded SOH, so
the scanner can't cross it — the generated decoder computes the value end from the
length and jumps past it. That jump used to build a *fresh* `FieldReader`, resetting
the fused checksum to `0`, so any DATA-field message *with* a checksum failed to
decode. `FieldReader::resync_after_data` keeps the same reader: the accumulator holds
the invariant `checksum == sum(buf[..scan_pos])` (PSADBW folds whole chunks, `scan_pos`
tracks the chunk boundary), so it folds only the short stretch between `scan_pos` and
the data end — a **local correction, single pass, no prefix rescan**, undoing any SIMD
chunk-ahead overshoot.

### Robustness posture

`tests/property.rs` (proptest) proves the two invariants a FIX engine depends on:
every parser **never panics on arbitrary / printable / structured wire bytes**,
and every type **round-trips** (`construct → encode → parse`) across its full
domain (all `i64`×scale decimals, all dates, all times incl. the leap-second
band, all tenors, every `MonthYear` form, the TZ types). 296 unit + 12 property +
10 doctests on both SIMD tiers; the one new `unsafe` (the `MultipleStringValue`
borrowing iterator over validated subslices) is miri-clean.

## Open / deferred

- **#429 (length-prefixed DATA fields) — partially closed.** The checksum corner
  is fixed (`resync_after_data`, above), and generated decoders handle the
  structural embedded-SOH case via the length-computed value span. To fully close
  it:
  1. **Bare-reader escape hatch** — expose `FieldReader::read_raw(len)` /
     `next_data_field(len)` (the issue's Option B) so a hand-rolled reader (not just
     generated code) can consume a DATA value literally. `resync_after_data` is the
     building block; this is the public consume-N-bytes API on top of it.
  2. **Malformed length → `DecodeError`** — the generated path currently *clamps*
     (`.min(buf.len())`); `N > remaining`, `N = 0`, or a non-numeric length should
     return a decode error, not silently truncate.
  3. **DATA fields inside repeating groups** — the length→data pairing is detected
     at message level only; the group decode path needs the same handling.
- **Memoization** (above) — `FieldView` parse-once caching for the heavy types, a
  body change behind the same accessors.
- **Turbo-off rerun** of the framed-encode bench to fold canonical numbers into
  BENCHMARKS.md (the table above is `taskset`/best-of-5 but turbo-on).
- **Runtime SIMD detection.** Dispatch is compile-time only (no
  `is_x86_feature_detected!`), matching the workspace's
  build-for-your-target stance. Documented here rather than changed.
- **`parse_tag` hardening** parked above, pending a real caller that
  needs adversarial-input bounds.
