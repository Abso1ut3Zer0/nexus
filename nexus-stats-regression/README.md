# nexus-stats-regression

Online regression, learning, and estimation for [nexus-stats](https://crates.io/crates/nexus-stats).

## Regression Types

- **LinearRegression** — Online linear regression
- **PolynomialRegression** — Online polynomial regression
- **EwPolynomialRegression** — Exponentially weighted polynomial regression
- **ExponentialRegression / LogarithmicRegression / PowerRegression** (+ `Ew*` forgetful forms) — Linearized exp/log/power fits (requires `std` or `libm`)
- **LogisticRegression** — Online logistic regression (requires `alloc` + (`std` or `libm`))

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

- **Kalman2d / Kalman3d** — 2D/3D Kalman filters
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
