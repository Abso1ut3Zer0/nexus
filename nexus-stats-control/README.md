# nexus-stats-control

Control and frequency primitives for [nexus-stats](https://crates.io/crates/nexus-stats): thresholds, switches, peak detection, and counting what is frequent.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` protects the state.** A type has one when some input does damage that outlasts the sample, or when `update` drops a sample you should be told about (a NaN it ignores, a timestamp that goes back). It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reader reports what the arithmetic gives,** NaN included where the true answer is undefined. It never substitutes a number. The library protects the state. It does not promise a reading is never NaN.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.

**Not yet migrated:** every type in this crate. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## Which type do I use?

**Acting on a stream** (`control`)

- **DeadBand**: passes a value on only once it has changed by more than a threshold
- **Hysteresis**: an on/off decision with one threshold to turn on and another to turn off, so it does not chatter
- **Debounce**: triggers only after a number of events in a row
- **LevelCrossing**: detects crossings of a level, with their direction, and counts them
- **PeakDetector**: local highs and lows that stand out by a set margin
- **BoolWindow**: the share of passes over the last so many events (requires `alloc`)

**Counting** (`frequency`)

- **TopK**: the most frequent items in a stream, in fixed memory (requires `alloc`)
- **FlexProportionGlobal / FlexProportionLocal**: each key's share of an event count that decays (the kernel's `flex_proportions`)
- **DecayAccum**: a score that builds with events and decays with time, in `u64` ticks (requires `std` or `libm`)

Each type's docs give its definition and how to read it.

## Usage

Enable the `control` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::control::PeakDetector;
use nexus_stats::frequency::TopK;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
