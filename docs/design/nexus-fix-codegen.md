# nexus-fix-codegen — draft PR description (#407)

#406 (PR #415) is merged; this is aligned to the shipped `nexus-fix-codec` API
and simplified to reflect what the codec now provides.

---

**Title:** `feat: nexus-fix-codegen — dictionary-driven code generator (#407)`

> Closes #407. Depends on #406 (uses `nexus-fix-codec` as the runtime the
> generated code calls). Builds on the plan in #412.

## What

A standalone generator (lib + `clap` CLI + `build.rs` API) that reads a QuickFIX
dictionary XML and emits readable, dependency-light Rust that sits directly on
the #406 codec primitives.

Generated output:

- **`fields.rs`** — `TAG_*: u32` consts; typed enums per FIX `<field>` with
  values. Single-char → `from_byte(u8) -> Option<Self>` / `as_byte(self) -> u8`;
  multi-char → `from_bytes(&[u8]) -> Option<Self>` /
  `as_bytes(self) -> &'static [u8]`. Enum lookup keys off
  `RawField.value.slice(buf)`.
- **`messages.rs`** — per-`MsgType` flyweight decoder. One forward pass with
  `codec::FieldReader`, dispatching each `RawField.tag` via `match` into the
  message's `FieldSpan` slots; random-access fields use `codec::find_tag`.
  Decoder borrows `&[u8]`, zero-copy, zero-alloc.
- **`groups.rs`** — repeating-group iterators + per-entry decoders, built over
  `GroupSpan` + a bounded `FieldReader` sub-scan.
- **`encoders.rs`** — consume-self builders over `codec::FieldWriter` /
  `encode_field`, `finish() -> usize`, trailer + `format_checksum`.
- **`mod.rs`** — re-exports, `MsgType` dispatch enum.

## Design

- **Dictionary-driven, not version-driven** — one codepath, any QuickFIX XML
  (4.2 / 4.4 / 5.0 / custom).
- **Unknown tags: silent skip** — forward iteration already does this; no slot,
  no error.
- **No encoder-side validation** — the generator emits structure, not policy;
  required-field enforcement is the engine's job (#409).
- **Decode model — two shapes, no watermark.** The codec already supplies both
  a single forward pass (`FieldReader`) and random access (`find_tag`), so the
  `Cell<FieldSpan>` watermark layer from the plan is dropped entirely. Generated
  decoders pick:
  - *one-pass populate* — run `FieldReader` once, `match` each `RawField.tag`
    into the message's `FieldSpan` slots. O(n) once; the default for full decode.
  - *lazy accessors* — typed getters that call `find_tag(buf, body_start, TAG)`
    on demand. O(n) per access; for sparse reads of a few fields.

  No bespoke scanner, no cache machine — both shapes are thin wrappers over codec
  primitives.
- **DATA fields are the one sharp edge** (95/96, 90/91, 212/213, 348/349,
  358/359). `FieldReader` is SOH-driven, and a binary DATA value can contain
  `0x01`, which a naive pass would mis-split. Generated decoders must handle DATA
  length-delimited: read the preceding length tag, take exactly that many bytes,
  then re-seat a fresh `FieldReader` past the value — never let the scanner cross
  a DATA field. The codec does not special-case this; it is codegen's job.

## Open questions

1. **XML parser** — `quick-xml` (pull, fast, no DOM alloc) vs `roxmltree`. Lean
   `quick-xml`.
2. **Formatting emitted code** — shell out to `rustfmt` as a post-step (makes
   `rustfmt` a CLI runtime dep) vs emit pre-formatted. Lean post-step `rustfmt`,
   gated so `build.rs` use degrades gracefully if absent.
3. **Component/group nesting** — cap depth or fully recursive? Real dictionaries
   rarely exceed 2; lean fully recursive with a sane guard.

(The earlier watermark-vs-forward-pass question is resolved: the merged codec
supplies both `FieldReader` and `find_tag`, so the watermark layer is dropped —
see Decode model above.)

## Modeled after Prost (Michael's pointer)

Prost is the model for the **tooling**, not the decode model.

Adopt from `prost` / `prost-build`:
- **`build.rs` integration** — a `Config`-style builder (`generate().out_dir(..)
  .dictionary(..).run()`) mirroring `prost_build::Config::compile_protos`, so a
  consumer crate generates in `build.rs` and pulls the result with
  `include!(concat!(env!("OUT_DIR"), "/fix.rs"))`.
- **Generated code is plain, readable Rust** — no runtime reflection, no dynamic
  dictionary at runtime; the dictionary is consumed entirely at generation time.
- **Builder knobs** — type attributes / derives, module layout, opt-in
  per-message selection, analogous to Prost's `type_attribute` /
  `btree_map` style configuration.
- **A checked-in CLI** alongside the `build.rs` path, like `protoc` + `prost`'s
  split, for ahead-of-time generation into the repo when preferred.

Diverge from Prost where the data model differs:
- Prost decodes length-delimited binary into **owned structs** (it copies). FIX
  here is **zero-copy flyweight** — generated "messages" are decoders holding
  `&[u8]` + `FieldSpan` slots that point into the original buffer; nothing is
  copied on decode. So model Prost's *ergonomics and build pipeline*, keep our
  span-based decode.
- No `Default`/owned round-trip in the Prost sense; encode side is the separate
  consume-self builder over `FieldWriter`.

## Out of scope

Session/transport (#409/#410), persistence (#411). Generator targets the codec
layer only.

## Deltas from the plan stub (#412), now that #406 is real

- Decoders build on **`FieldReader` / `find_tag`** — the `Cell<FieldSpan>`
  watermark layer is dropped; generated decoders are thin wrappers over the two
  codec primitives (one-pass populate or lazy `find_tag`).
- Encoders build on **`FieldWriter` / `encode_field` / `format_checksum`**, which
  already exist, so encoder generation is thinner than the stub implied.
- The generator emits no scanning/checksum/encoding plumbing of its own — only
  tag consts, typed enums, per-message dispatch, and group boundary logic
  (templated on the codec's own repeating-group tests).
