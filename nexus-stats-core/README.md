# nexus-stats-core

Core types shared across the nexus-stats ecosystem.

The foundation of the nexus-stats crates, and the descriptive statistics they build on:

- the shared pieces: error enums, the `Accuracy` report, the `Sample` and `Float` traits, math utilities, ring storage, and the clock traits (`Tick`, `Span`, `Timestamp`) with the named time types (`Nanos`, `Micros`, `Millis`, `Seconds`);
- the descriptive statistics: Welford, Moments, Covariance, CovarianceMatrix, HarmonicMean, Percentile, BucketAccumulator, FirstDiff, SecondDiff.

Every other concept (smoothing, detection, monitoring, control, normalization, regression, trading) has its own crate.

**Not intended for direct use** — import from
[`nexus-stats`](https://crates.io/crates/nexus-stats) instead.

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` protects the state.** A type has one when some input does damage that outlasts the sample, or when `update` drops a sample you should be told about (a NaN it ignores, a timestamp that goes back). It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reader reports what the arithmetic gives,** NaN included where the true answer is undefined. It never substitutes a number. The library protects the state. It does not promise a reading is never NaN.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.

**Not yet migrated:** `BucketAccumulator`, `CovarianceMatrix`, `FirstDiff`, `Percentile`, `SecondDiff`. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
