# nexus-stats-regression

Online regression, learning, and estimation for [nexus-stats](https://crates.io/crates/nexus-stats).

## Guarantees

- **Fixed memory.** A type allocates only when it is built. `update` never allocates.
- **Configuration is checked once, when the type is built,** and reported as a `ConfigError`.
- **`update` does the arithmetic and nothing else.** No validation, no `Result`. Floats follow IEEE 754, as `+` does. After an input the type cannot use, it promises nothing unless its docs say otherwise.
- **`checked_update` exists only where it has a job.** A type has one when some input can leave it unable to give a right reading until `reset()`. It refuses exactly those inputs, its docs list them, and a refusal leaves the type unchanged. A type without one has no such input.
- **A reading is an `Option`.** `None` until there is enough data, never a placeholder value.
- **A published algorithm is implemented as published.** A type that comes from a paper or a standard follows it. Where floating point needs more care than the source gives (cancellation, overflow, a divisor near zero), the type adds the guard practitioners use, and its docs say which.

**Not yet migrated:** every type in this crate except `HitRate`. They have not been moved to these guarantees. Most still validate in `update` and return a `Result`.

## Regression Types

- **LinearRegression** — Online linear regression
- **PolynomialRegression** — Online polynomial regression
- **EwPolynomialRegression** — Exponentially weighted polynomial regression
- **ExponentialRegression / LogarithmicRegression / PowerRegression** (+ `Ew*` forgetful forms) — Linearized exp/log/power fits (requires `std` or `libm`)
- **LogisticRegression** — Online logistic regression (requires `alloc` + (`std` or `libm`))
- **HitRate** — How often a forecast has the direction right

## Learning Types

- **LmsFilter** — Least Mean Squares adaptive filter (requires `alloc`)
- **RlsFilter** — Recursive Least Squares adaptive filter (requires `alloc`)
- **OnlineKMeans** — Online K-Means clustering (requires `alloc`)
- **OnlineGd** — Online gradient descent (requires `alloc`)
- **AdaGrad** — AdaGrad optimizer (requires `alloc` + (`std` or `libm`))
- **Adam** — Adam optimizer (requires `alloc` + (`std` or `libm`))
- **Ucb1** — UCB1 multi-armed bandit (requires `alloc` + (`std` or `libm`))
- **ThompsonBeta** — Thompson Sampling with Beta prior (requires `alloc` + (`std` or `libm`))
- **ThompsonGamma** — Thompson Sampling with Gamma prior (requires `alloc` + (`std` or `libm`))
- **EpsilonGreedy** — Epsilon-greedy bandit (requires `alloc` + (`std` or `libm`))
- **Exp3** — EXP3 adversarial bandit (requires `alloc` + (`std` or `libm`))

## Estimation Types

- **Kalman1d / Kalman2d / Kalman3d** — 1D/2D/3D Kalman filters
- **BetaBinomial** — Beta-Binomial conjugate estimator
- **GammaPoisson** — Gamma-Poisson conjugate estimator

## Usage

Enable the `regression` feature on `nexus-stats` for unified import paths:

```rust
use nexus_stats::regression::LinearRegression;
use nexus_stats::learning::Adam;
use nexus_stats::estimation::Kalman2d;
```

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or
[MIT license](../LICENSE-MIT) at your option.
