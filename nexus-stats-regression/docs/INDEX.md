# nexus-stats-regression Documentation

Online regression, adaptive learning, and Bayesian estimation. Three submodules:

- `regression` — closed-form and EW regressors.
- `learning` — gradient-based and recursive adaptive filters.
- `estimation` — Kalman filters and Bayesian conjugate estimators.

All types are streaming, O(1) or O(N) per update in feature dimension, and zero-allocation on the hot path (after construction).

## Start Here

- [Overview](overview.md) — Design conventions, feature flags, the regression API shape.
- [Regression](regression.md) — Linear, polynomial, EW-polynomial, transformed, logistic, lagged predictor, Kyle lambda, signal decay.
- [Learning (adaptive filters)](learning.md) — LMS, NLMS, RLS, Huber regression, online K-Means, OnlineGD / AdaGrad / Adam.
- [Estimation](estimation.md) — Kalman2d, Kalman3d, BetaBinomial, GammaPoisson.
- [Bandits](bandits.md) — UCB1, ThompsonBeta, ThompsonGamma, EpsilonGreedy, EXP3. Decision tree, discounting, reward normalization, trading examples.

## Algorithms

### regression (closed-form + EW)

| Type | Fits |
|------|------|
| `LinearRegression` | y = a + bx (ordinary least squares, closed-form, streaming) |
| `EwLinearRegression` | EW variant of above |
| `PolynomialRegression` | y = a0 + a1 x + a2 x² + ... + ad x^d |
| `EwPolynomialRegression` | EW variant |
| `ExponentialRegression` / `LogarithmicRegression` / `PowerRegression` (+ `Ew*`) | Exp / log / power fits via linearization |
| `LogisticRegression` | Binary classifier via online gradient steps |
| `LaggedPredictor` | y_t = a + b * x_{t-lag} — trading-specific |
| `KyleLambda` | Price impact slope from volume (market microstructure) |
| `SignalDecayCurve` | Fits an exponential decay to IC vs horizon |

### learning (adaptive filters + optimizers)

| Type | Algorithm |
|------|-----------|
| `LmsFilter` | Least Mean Squares — simplest adaptive filter |
| `NlmsFilter` | Normalized LMS — step-size invariant to input power |
| `RlsFilter` | Recursive Least Squares — fast-converging, matrix-inversion-style |
| `HuberRegression` | Outlier-robust linear regression via Huber loss |
| `OnlineKMeans` | Streaming k-means cluster assignment |
| `OnlineGd` | Plain gradient descent |
| `AdaGrad` | Per-feature adaptive learning rate |
| `Adam` | Adam / AdamW optimizer |
| `Ucb1` | UCB1 multi-armed bandit — deterministic, no RNG |
| `ThompsonBeta` | Thompson Sampling with Beta prior (binary/[0,1] rewards) |
| `ThompsonGamma` | Thompson Sampling with Gamma prior (positive rewards) |
| `EpsilonGreedy` | Epsilon-greedy bandit |
| `Exp3` | EXP3 adversarial bandit (log-space weights) |

### estimation

| Type | What it is |
|------|------------|
| `Kalman2d` | 2D Kalman filter with customizable dynamics |
| `Kalman3d` | 3D Kalman filter |
| `BetaBinomial` | Bayesian rate estimation (success/failure) |
| `GammaPoisson` | Bayesian rate estimation (Poisson count / exposure) |

## Cross-references

- Scalar Kalman: [`Kalman1d`](../../nexus-stats-smoothing/docs/kalman1d.md) in `nexus-stats-smoothing`.
- Half-life / Hurst / variance ratio (complement regression for regime classification): [`nexus-stats-core::statistics`](../../nexus-stats-core/docs/statistics.md).
- Umbrella long-form: [`nexus-stats/docs`](../../nexus-stats/docs/INDEX.md).
