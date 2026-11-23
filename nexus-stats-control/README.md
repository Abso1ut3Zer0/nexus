# nexus-stats-control

Control and frequency primitives for [nexus-stats](https://crates.io/crates/nexus-stats): thresholds, switches, peak detection, and counting what is frequent.

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
