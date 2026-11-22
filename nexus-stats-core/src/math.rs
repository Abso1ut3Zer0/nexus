/// Returns `Err(DataError::NotANumber)` / `Err(DataError::Infinite)` from the
/// enclosing function when a float input is not finite. The first line of
/// every `update` that takes a float, in this crate and the subcrates.
#[doc(hidden)]
#[macro_export]
macro_rules! check_finite {
    ($val:expr) => {
        if !$val.is_finite() {
            return Err(if $val.is_nan() {
                $crate::DataError::NotANumber
            } else {
                $crate::DataError::Infinite
            });
        }
    };
}

/// Returns `Ok` if `value` is a number no larger in magnitude than `limit`.
///
/// # Errors
///
/// - [`DataError::NotANumber`](crate::DataError::NotANumber) if `value` is
///   NaN.
/// - [`DataError::Infinite`](crate::DataError::Infinite) if `value` is
///   infinite.
/// - [`DataError::OutOfRange`](crate::DataError::OutOfRange) if `value` is
///   finite and larger in magnitude than `limit`.
#[inline]
pub fn check_input(value: f64, limit: f64) -> Result<(), crate::DataError> {
    // PERF: cold, so naming the reason stays off the accepted path.
    #[cold]
    fn refusal(value: f64) -> crate::DataError {
        if value.is_nan() {
            crate::DataError::NotANumber
        } else if value.is_infinite() {
            crate::DataError::Infinite
        } else {
            crate::DataError::OutOfRange
        }
    }

    // PERF: NaN and infinity fail this comparison too, so one test accepts.
    if value.abs() <= limit {
        return Ok(());
    }
    Err(refusal(value))
}

/// [`check_input`] for each value in turn, with one limit:
/// `check_inputs!(limit; a, b)?`. Without a limit, `check_inputs!(a, b)?`
/// refuses only NaN and infinity.
///
/// Evaluates to a `Result`, naming the first value refused. The values are
/// evaluated inside closures, so an argument cannot `return`, `break` or
/// `.await`.
#[doc(hidden)]
#[macro_export]
macro_rules! check_inputs {
    ($limit:expr; $($value:expr),+ $(,)?) => {{
        let limit: f64 = $limit;
        Ok(()) $(.and_then(|()| $crate::math::check_input($value, limit)))+
    }};
    ($($value:expr),+ $(,)?) => {
        $crate::math::check_inputs!(f64::MAX; $($value),+)
    };
}
pub use crate::check_inputs;

/// `2^64`: more samples than a `u64` count can hold.
const TWO_POW_64: f64 = 18_446_744_073_709_551_616.0;

/// The largest value one powered term may reach: `1e240`.
///
/// Our choice, far below the overflow threshold `f64::MAX` (written Ω in
/// the floating-point literature). A difference of two inputs can be twice
/// an input, so its fourth power is `2^4` times larger; `2^64` terms that
/// size still sum below the threshold.
pub const POWER_LIMIT: f64 = 1e240;
const _: () = assert!(TWO_POW_64 * 16.0 * POWER_LIMIT < f64::MAX);

/// The largest input whose square stays within [`POWER_LIMIT`]: `1e120`.
pub const LIMIT_FOR_SQUARES: f64 = 1e120;
const _: () = assert!(LIMIT_FOR_SQUARES * LIMIT_FOR_SQUARES <= POWER_LIMIT);

/// A divisor below this has lost precision to underflow.
///
/// The smallest normal number over machine epsilon: the form of LAPACK's
/// `SMLNUM` (safe minimum over precision), which it uses to guard a
/// division.
pub const SMALLEST_DIVISOR: f64 = f64::MIN_POSITIVE / f64::EPSILON;

/// The variance that rounding alone produces around `mean`:
/// `(f64::EPSILON * mean)^2`.
///
/// A variance at or below it means the values are equal to within
/// rounding. This is the test SciPy's `skew` and `kurtosis` use.
#[must_use]
pub const fn rounding_variance(mean: f64) -> f64 {
    let rounding = f64::EPSILON * mean;
    rounding * rounding
}

/// The sum of `(x - center)^2` over `count` values, from the sums of
/// `x^2` and of `x`: `squares - 2 * center * sum + count * center^2`.
///
/// The terms cancel when `center` is far from zero next to the spread of
/// the values, and digits go with them.
#[inline]
#[must_use]
pub fn squares_about(squares: f64, sum: f64, count: f64, center: f64) -> f64 {
    (count * center).fma(center, (-2.0 * center).fma(sum, squares))
}

/// An estimate of the rounding error a running total has accumulated.
///
/// Each add to a total is rounded by up to half a unit in the last place
/// of the result, so the error depends on how large the total was at each
/// add. It stays in the total, and matters once the total has become much
/// smaller than it was: this is for totals that are added to and removed
/// from, as over a sliding window.
///
/// This treats each add's error as independent and equally likely to fall
/// either way, with variance `(f64::EPSILON * total)^2 / 12`. The errors
/// then partly cancel, and their sum is close to normal (Higham and Mary,
/// 2019, "A New Approach to Probabilistic Rounding Error Analysis"). It
/// describes the error seen in practice; it is not a guarantee. See
/// [`RoundingBound`] for one.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::math::RoundingEstimate;
///
/// let mut rounding = RoundingEstimate::new();
/// let mut total = 0.0;
/// for x in [1e8, 2.5, -1e8] {
///     total += x;
///     rounding.record(total);
/// }
/// // Four standard deviations: what `total` may be off by.
/// let error = rounding.error(4.0);
/// assert!(error > 1e-8 && error < 1e-7);
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct RoundingEstimate {
    /// Sum over the adds of the total squared.
    squares: f64,
    adds: usize,
}

impl RoundingEstimate {
    /// Creates an estimate with no adds recorded.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            squares: 0.0,
            adds: 0,
        }
    }

    /// Records one add that left the total at `total`.
    #[inline]
    pub fn record(&mut self, total: f64) {
        self.record_n(total, 1);
    }

    /// Records `adds` adds, each of which left a total near `total`.
    #[inline]
    pub fn record_n(&mut self, total: f64, adds: usize) {
        self.squares = (total * adds as f64).fma(total, self.squares);
        self.adds += adds;
    }

    /// The variance of the accumulated rounding error.
    #[inline]
    #[must_use]
    pub fn variance(&self) -> f64 {
        Self::variance_of(1.0, 1) * self.squares
    }

    /// The accumulated rounding error at `confidence` standard deviations.
    ///
    /// At 4, a normal error is larger about once in 16,000.
    #[cfg(any(feature = "std", feature = "libm"))]
    #[inline]
    #[must_use]
    pub fn error(&self, confidence: f64) -> f64 {
        confidence * sqrt(self.variance())
    }

    /// The variance of the rounding error of `adds` adds that each leave a
    /// total near `total`: `adds * (f64::EPSILON * total)^2 / 12`.
    #[inline]
    #[must_use]
    pub fn variance_of(total: f64, adds: usize) -> f64 {
        let rounding = f64::EPSILON * total;
        rounding * rounding * (adds as f64 / 12.0)
    }

    /// The number of adds recorded.
    #[inline]
    #[must_use]
    pub const fn adds(&self) -> usize {
        self.adds
    }

    /// Forgets every add, as when the total is recomputed.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

/// A bound on the rounding error a running total has accumulated.
///
/// The worst case of what [`RoundingEstimate`] estimates: every add is
/// taken to be off by the full half unit in the last place,
/// `f64::EPSILON / 2 * |total|`, all in the same direction. The total's
/// error cannot be larger, as long as no add overflowed or was not a
/// number. It grows with the number of adds where the estimate grows with
/// its square root, so over a long run it is far above the error seen.
///
/// # Examples
///
/// ```
/// use nexus_stats_core::math::RoundingBound;
///
/// let mut rounding = RoundingBound::new();
/// let mut total = 0.0;
/// for x in [1e8, 2.5, -1e8] {
///     total += x;
///     rounding.record(total);
/// }
/// assert!((total - 2.5).abs() <= rounding.error());
/// ```
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct RoundingBound {
    /// Sum over the adds of the total's size.
    sizes: f64,
    adds: usize,
}

impl RoundingBound {
    /// Creates a bound with no adds recorded.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            sizes: 0.0,
            adds: 0,
        }
    }

    /// Records one add that left the total at `total`.
    #[inline]
    pub fn record(&mut self, total: f64) {
        self.record_n(total, 1);
    }

    /// Records `adds` adds, each of which left a total no larger than
    /// `total` in size.
    #[inline]
    pub fn record_n(&mut self, total: f64, adds: usize) {
        self.sizes = (adds as f64).fma(total.abs(), self.sizes);
        self.adds += adds;
    }

    /// The most the total can be off by.
    #[inline]
    #[must_use]
    pub fn error(&self) -> f64 {
        // Rounded up a little, so that summing the sizes cannot undercut it.
        (0.5 * f64::EPSILON) * self.sizes * (self.adds as f64).fma(f64::EPSILON, 1.0)
    }

    /// The number of adds recorded.
    #[inline]
    #[must_use]
    pub const fn adds(&self) -> usize {
        self.adds
    }

    /// Forgets every add, as when the total is recomputed.
    #[inline]
    pub fn reset(&mut self) {
        *self = Self::new();
    }
}

/// f32 variant of [`check_finite`].
#[doc(hidden)]
#[inline]
pub fn check_finite_f32(val: f32) -> Result<(), crate::DataError> {
    if !val.is_finite() {
        return Err(if val.is_nan() {
            crate::DataError::NotANumber
        } else {
            crate::DataError::Infinite
        });
    }
    Ok(())
}

/// Square root.
///
/// Requires `std` or `libm` feature. Types using this (`std_dev()`,
/// `ShiryaevRoberts`) won't compile without one of these features.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn sqrt(x: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.sqrt()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::sqrt(x)
    }
}

/// Exponential function.
///
/// Requires `std` or `libm` feature. Types using this (`ShiryaevRoberts`,
/// `halflife()` constructors) won't compile without one of these features.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn exp(x: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.exp()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::exp(x)
    }
}

/// Natural logarithm.
///
/// Requires `std` or `libm` feature. Types using this (`Entropy`,
/// `TransferEntropy`) won't compile without one of these features.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn ln(x: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.ln()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::log(x)
    }
}

/// `x` raised to the power `y`.
///
/// Requires `std` or `libm` feature.
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn powf(x: f64, y: f64) -> f64 {
    #[cfg(feature = "std")]
    {
        x.powf(y)
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::pow(x, y)
    }
}

/// Natural logarithm (f32).
///
/// Requires `std` or `libm` feature.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn ln_f32(x: f32) -> f32 {
    #[cfg(feature = "std")]
    {
        x.ln()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::logf(x)
    }
}

/// Exponential function (f32).
///
/// Requires `std` or `libm` feature.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
pub fn exp_f32(x: f32) -> f32 {
    #[cfg(feature = "std")]
    {
        x.exp()
    }
    #[cfg(all(not(feature = "std"), feature = "libm"))]
    {
        libm::expf(x)
    }
}

/// Log-gamma function via Lanczos approximation (g=7).
///
/// Accurate to ~15 digits for x > 0.
#[doc(hidden)]
#[cfg(any(feature = "std", feature = "libm"))]
#[allow(
    clippy::excessive_precision,
    clippy::unreadable_literal,
    clippy::suboptimal_flops
)]
pub fn ln_gamma(x: f64) -> f64 {
    const G: f64 = 7.5;
    const C: [f64; 9] = [
        0.99999999999980993,
        676.5203681218851,
        -1259.1392167224028,
        771.32342877765313,
        -176.61502916214059,
        12.507343278686905,
        -0.13857109526572012,
        9.9843695780195716e-6,
        1.5056327351493116e-7,
    ];

    let x = x - 1.0;
    let mut sum = C[0];
    for i in 1..9 {
        sum += C[i] / (x + i as f64);
    }
    let t = x + G;
    0.5 * ln(2.0 * core::f64::consts::PI) + (x + 0.5) * ln(t) - t + ln(sum)
}

/// Multiply-add: `self * b + c`, fused when the target does it in one
/// instruction.
///
/// Rust's `f64::mul_add` is an FMA instruction only when the target has the
/// feature (x86_64 with `-C target-cpu=native` or `-C target-feature=+fma`;
/// always on aarch64). Without it, LLVM lowers `mul_add` to a call into
/// compiler-builtins' software `fma`, which costs more than the arithmetic
/// it replaces. So this shim fuses when `std` is available and the target
/// has FMA, and otherwise computes `self * b + c` with two roundings. The
/// two differ in the last bit; neither path ever calls out.
#[doc(hidden)]
pub trait MulAdd {
    /// `self * b + c`, fused when the target has FMA.
    fn fma(self, b: Self, c: Self) -> Self;
}

#[cfg(all(feature = "std", any(target_feature = "fma", target_arch = "aarch64")))]
macro_rules! impl_mul_add {
    ($t:ty) => {
        impl MulAdd for $t {
            #[inline(always)]
            fn fma(self, b: $t, c: $t) -> $t {
                self.mul_add(b, c)
            }
        }
    };
}

#[cfg(not(all(feature = "std", any(target_feature = "fma", target_arch = "aarch64"))))]
macro_rules! impl_mul_add {
    ($t:ty) => {
        impl MulAdd for $t {
            // PERF: the lint's suggestion is the software-fma call this path
            // exists to avoid.
            #[allow(clippy::suboptimal_flops)]
            #[inline(always)]
            fn fma(self, b: $t, c: $t) -> $t {
                self * b + c
            }
        }
    };
}

impl_mul_add!(f64);
impl_mul_add!(f32);

/// `1.0` for `true`, `0.0` for `false`, as a conversion rather than a select:
/// a select between two float constants lowers to a jump on the predicate.
#[inline]
#[must_use]
pub fn indicator(b: bool) -> f64 {
    f64::from(u8::from(b))
}

/// EMA weight for a half-life of `halflife` samples: `1 - exp(-ln 2 / halflife)`.
///
/// The result is in `(0, 1)` for a positive finite `halflife`; builders reach
/// this through [`EwWeight::resolve`], which validates it first.
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
#[must_use]
pub fn alpha_from_halflife(halflife: f64) -> f64 {
    1.0 - exp(-core::f64::consts::LN_2 / halflife)
}

/// EMA weight for a span of `n` samples: `2 / (n + 1)`, the pandas `span`
/// convention. In `(0, 1)` for `n >= 2`.
#[inline]
#[must_use]
#[allow(clippy::cast_precision_loss)]
pub fn alpha_from_span(n: u64) -> f64 {
    2.0 / (n as f64 + 1.0)
}

/// How a builder was told its exponential weight: directly, as a half-life,
/// or as a span. Builders store the knob the caller set and resolve it in
/// `build`, so a bad value is reported under the name the caller used.
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EwWeight {
    /// The weight itself, in `(0, 1)`.
    Alpha(f64),
    /// Samples for a weight to decay by half; positive and finite.
    #[cfg(any(feature = "std", feature = "libm"))]
    Halflife(f64),
    /// Pandas `span`; at least 2.
    Span(u64),
}

impl EwWeight {
    /// The smallest usable weight: half of machine epsilon.
    ///
    /// Our choice. Below it `1 - alpha` rounds to 1 and nothing is ever
    /// forgotten. The `halflife` knob already stops here, by rounding.
    const SMALLEST: f64 = f64::EPSILON / 2.0;

    /// The weight in `(0, 1)`.
    ///
    /// # Errors
    ///
    /// `ConfigError::Invalid` naming the knob that was set: `alpha` outside
    /// `(0, 1)`, a `halflife` that is not positive and finite, a `span`
    /// below 2, or any of the three giving a weight too small to use.
    pub fn resolve(self) -> Result<f64, crate::ConfigError> {
        let alpha = match self {
            Self::Alpha(a) => {
                if !in_unit_interval(a) {
                    return Err(crate::ConfigError::Invalid("alpha must be in (0, 1)"));
                }
                if a < Self::SMALLEST {
                    return Err(crate::ConfigError::Invalid(
                        "alpha is too small for a usable weight",
                    ));
                }
                a
            }
            #[cfg(any(feature = "std", feature = "libm"))]
            Self::Halflife(h) => {
                if !positive_finite(h) {
                    return Err(crate::ConfigError::Invalid(
                        "halflife must be positive and finite",
                    ));
                }
                // A half-life so short that `1 - exp(-x)` rounds to one, or
                // so long that it rounds to zero, has no usable weight.
                let alpha = alpha_from_halflife(h);
                if !in_unit_interval(alpha) {
                    return Err(crate::ConfigError::Invalid(
                        "halflife is too small or too large for a usable weight",
                    ));
                }
                alpha
            }
            Self::Span(n) => {
                if n < 2 {
                    return Err(crate::ConfigError::Invalid("span must be at least 2"));
                }
                let alpha = alpha_from_span(n);
                if alpha < Self::SMALLEST {
                    return Err(crate::ConfigError::Invalid(
                        "span is too large for a usable weight",
                    ));
                }
                alpha
            }
        };
        Ok(alpha)
    }
}

/// `z` such that `P(Z > z) = p` for a standard normal, for `p` in `(0, 0.5]`:
/// the Abramowitz & Stegun 26.2.23 rational approximation (|error| < 4.5e-4).
///
/// Used for the two-sided credible intervals (`p = (1 - confidence) / 2`).
#[cfg(any(feature = "std", feature = "libm"))]
#[inline]
#[must_use]
pub fn upper_tail_z(p: f64) -> f64 {
    let t = sqrt(-2.0 * ln(p));
    let num = 0.010_328f64.fma(t, 0.802_853).fma(t, 2.515_517);
    let den = 0.001_308f64.fma(t, 0.189_269).fma(t, 1.432_788).fma(t, 1.0);
    t - num / den
}

/// Dot product `Σ a[i] · b[i]` as one fused chain (`fma` per term).
///
/// `b` is indexed by `a`'s length: one bounds check up front, and the loop
/// count is `a.len()`. Pass the slice whose length the compiler can see
/// first (a caller's feature slice rather than a boxed weight vector), and
/// the loop unrolls to that length where it is a constant.
///
/// # Panics
///
/// If `b` is shorter than `a`.
#[inline]
#[must_use]
pub fn dot(a: &[f64], b: &[f64]) -> f64 {
    let b = &b[..a.len()];
    a.iter().zip(b).fold(0.0, |acc, (&x, &y)| x.fma(y, acc))
}

/// `y[i] += alpha · x[i]` for every `i` (BLAS `axpy`), fused per element.
///
/// `y` is indexed by `x`'s length, like [`dot`].
///
/// # Panics
///
/// If `y` is shorter than `x`.
#[inline]
pub fn axpy(alpha: f64, x: &[f64], y: &mut [f64]) {
    let y = &mut y[..x.len()];
    for (yi, &xi) in y.iter_mut().zip(x) {
        *yi = alpha.fma(xi, *yi);
    }
}

/// `true` for a finite value strictly greater than zero; `false` for NaN.
///
/// The builders' validation idiom: `x <= 0.0` is `false` for NaN and lets it
/// through, this does not.
#[inline]
#[must_use]
pub fn positive_finite(x: f64) -> bool {
    x.is_finite() && x > 0.0
}

/// `true` for a finite value greater than or equal to zero; `false` for NaN.
#[inline]
#[must_use]
pub fn nonnegative_finite(x: f64) -> bool {
    x.is_finite() && x >= 0.0
}

/// `true` for a value strictly inside `(0, 1)`; `false` for NaN.
#[inline]
#[must_use]
pub fn in_unit_interval(x: f64) -> bool {
    x > 0.0 && x < 1.0
}

#[cfg(test)]
mod tests {
    /// Uniform values in `[-1, 1)`.
    fn noise(state: &mut u64) -> f64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        (*state >> 11) as f64 / (1u64 << 52) as f64 - 1.0
    }

    /// A sliding-window sum of `values * scale(i)`, kept as a running total
    /// in `f64`, against the same window summed exactly: the error at the
    /// end, with the trackers that watched every add.
    fn running_total_error(
        seed: u64,
        steps: usize,
        scale: impl Fn(usize) -> f64,
    ) -> (f64, super::RoundingEstimate, super::RoundingBound) {
        extern crate std;
        const WINDOW: usize = 64;
        let mut state = seed;
        let mut window = std::collections::VecDeque::new();
        let mut total = 0.0f64;
        let (mut estimate, mut bound) =
            (super::RoundingEstimate::new(), super::RoundingBound::new());
        for i in 0..steps {
            let x = noise(&mut state) * scale(i);
            if window.len() == WINDOW {
                total -= window.pop_front().unwrap();
                estimate.record(total);
                bound.record(total);
            }
            window.push_back(x);
            total += x;
            estimate.record(total);
            bound.record(total);
        }
        // Every value is a multiple of 2^-80 below 2^10: exact in i128.
        let exact: i128 = window.iter().map(|x| (x * 2f64.powi(80)) as i128).sum();
        let error = (total * 2f64.powi(80)) as i128 - exact;
        (error as f64 / 2f64.powi(80), estimate, bound)
    }

    #[test]
    fn the_rounding_trackers_cover_a_running_total_that_shrinks() {
        // Values near 1 for a long spell, then a million times smaller: the
        // error left from the busy spell is what remains.
        let scale = |i: usize| if i < 50_000 { 1.0 } else { 2f64.powi(-20) };
        let mut within_one_sd = 0;
        for seed in 1..=200u64 {
            let (error, estimate, bound) = running_total_error(seed, 50_200, scale);
            assert!(error != 0.0, "seed {seed}: no rounding to measure");
            assert!(error.abs() <= bound.error(), "seed {seed}");
            assert!(error.abs() <= estimate.error(4.0), "seed {seed}");
            // The bound grows with the adds, the estimate with their root.
            assert!(bound.error() > 50.0 * estimate.error(1.0), "seed {seed}");
            within_one_sd += usize::from(error.abs() <= estimate.error(1.0));
        }
        // The estimate is the right size, not merely large: about 68% of
        // normal errors fall inside one standard deviation.
        assert!((100..=190).contains(&within_one_sd), "{within_one_sd}");
    }

    #[test]
    fn squares_about_matches_the_sum_taken_directly() {
        let values = [3.0, -1.5, 0.25, 8.0, 2.0];
        let (squares, sum): (f64, f64) = values
            .iter()
            .fold((0.0, 0.0), |(squares, sum), x| (squares + x * x, sum + x));
        for center in [0.0, 2.35, -4.0] {
            let direct: f64 = values.iter().map(|x| (x - center) * (x - center)).sum();
            let got = super::squares_about(squares, sum, values.len() as f64, center);
            assert!(
                (got - direct).abs() <= 1e-12 * direct,
                "{center}: {got} {direct}"
            );
        }
        // About zero it is the sum of squares itself.
        assert_eq!(super::squares_about(squares, sum, 5.0, 0.0), squares);
    }

    #[test]
    fn the_rounding_trackers_count_and_reset() {
        let eps = f64::EPSILON;
        let mut estimate = super::RoundingEstimate::new();
        estimate.record(3.0);
        estimate.record_n(-2.0, 4);
        assert_eq!(estimate.adds(), 5);
        // 3^2 + 4 * 2^2 = 25, over 12.
        let close = |got: f64, want: f64| (got - want).abs() <= 1e-12 * want;
        assert!(close(estimate.variance(), eps * eps * 25.0 / 12.0));
        assert_eq!(estimate.error(2.0), 2.0 * super::sqrt(estimate.variance()));
        assert!(close(
            super::RoundingEstimate::variance_of(-2.0, 4),
            eps * eps * 16.0 / 12.0
        ));
        estimate.reset();
        assert_eq!(estimate, super::RoundingEstimate::new());
        assert_eq!((estimate.adds(), estimate.error(4.0)), (0, 0.0));

        let mut bound = super::RoundingBound::new();
        bound.record(3.0);
        bound.record_n(-2.0, 4);
        assert_eq!(bound.adds(), 5);
        // 3 + 4 * 2 = 11 half units, and never less.
        assert!(bound.error() >= 0.5 * eps * 11.0);
        assert!(close(bound.error(), 0.5 * eps * 11.0));
        bound.reset();
        assert_eq!((bound.adds(), bound.error()), (0, 0.0));
    }

    #[test]
    fn rounding_variance_is_epsilon_times_the_mean_squared() {
        let eps = f64::EPSILON;
        assert_eq!(super::rounding_variance(1.0), eps * eps);
        assert_eq!(super::rounding_variance(-1e6), (eps * 1e6) * (eps * 1e6));
        assert_eq!(super::rounding_variance(0.0), 0.0);

        // Usable where a type derives a constant of its own.
        const AT_TWO: f64 = super::rounding_variance(2.0);
        assert_eq!(AT_TWO, 4.0 * eps * eps);
    }

    #[test]
    fn a_weight_too_small_to_use_is_refused_under_every_knob() {
        use super::EwWeight::{Alpha, Span};
        use crate::ConfigError::Invalid;

        let smallest = f64::EPSILON / 2.0;
        assert_eq!(Alpha(smallest).resolve(), Ok(smallest));
        let too_small = Err(Invalid("alpha is too small for a usable weight"));
        assert_eq!(Alpha(smallest / 2.0).resolve(), too_small);
        assert_eq!(Alpha(5e-324).resolve(), too_small);

        assert!(Span(1 << 50).resolve().is_ok());
        assert_eq!(
            Span(u64::MAX).resolve(),
            Err(Invalid("span is too large for a usable weight"))
        );
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn a_halflife_too_long_to_use_is_refused() {
        use super::EwWeight::Halflife;
        use crate::ConfigError::Invalid;

        assert!(Halflife(10.0).resolve().is_ok());
        assert_eq!(
            Halflife(1e18).resolve(),
            Err(Invalid(
                "halflife is too small or too large for a usable weight"
            ))
        );
    }

    #[test]
    fn check_inputs_checks_each_value_and_names_the_first_refused() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        assert_eq!(check_inputs!(1.0, -2.0), Ok(()));
        assert_eq!(check_inputs!(1.0, -2.0, 3.0,), Ok(()));
        assert_eq!(check_inputs!(f64::MAX), Ok(()));
        assert_eq!(check_inputs!(1.0, f64::NAN), Err(NotANumber));
        assert_eq!(check_inputs!(f64::INFINITY, f64::NAN), Err(Infinite));
        assert_eq!(check_inputs!(f64::NAN, f64::INFINITY), Err(NotANumber));

        assert_eq!(check_inputs!(10.0; 10.0, -10.0), Ok(()));
        assert_eq!(check_inputs!(10.0; 1.0, 2.0,), Ok(()));
        assert_eq!(check_inputs!(10.0; 1.0, 11.0), Err(OutOfRange));
        assert_eq!(check_inputs!(10.0; 11.0, f64::NAN), Err(OutOfRange));
        assert_eq!(check_inputs!(10.0; 1.0, 2.0, f64::NAN), Err(NotANumber));
    }

    #[test]
    fn check_inputs_evaluates_the_limit_once() {
        let mut evaluated = 0;
        let mut limit = || {
            evaluated += 1;
            10.0
        };
        assert_eq!(check_inputs!(limit(); 1.0, 2.0, 3.0), Ok(()));
        assert_eq!(evaluated, 1);
    }

    #[test]
    fn check_inputs_stops_at_the_first_refusal() {
        let mut evaluated = 0;
        let mut next = |value: f64| {
            evaluated += 1;
            value
        };
        assert!(check_inputs!(next(f64::NAN), next(1.0)).is_err());
        assert_eq!(evaluated, 1);
    }

    #[test]
    fn check_input_accepts_up_to_the_limit_and_names_each_refusal() {
        use crate::DataError::{Infinite, NotANumber, OutOfRange};

        // 5e-324 is the smallest subnormal.
        for accepted in [0.0, -0.0, 1.5, -1.5, 10.0, -10.0, 5e-324, -5e-324] {
            assert_eq!(super::check_input(accepted, 10.0), Ok(()), "{accepted}");
        }
        assert_eq!(super::check_input(f64::NAN, 10.0), Err(NotANumber));
        assert_eq!(super::check_input(f64::INFINITY, 10.0), Err(Infinite));
        assert_eq!(super::check_input(f64::NEG_INFINITY, 10.0), Err(Infinite));
        assert_eq!(super::check_input(10.000_001, 10.0), Err(OutOfRange));
        assert_eq!(super::check_input(-10.000_001, 10.0), Err(OutOfRange));
        assert_eq!(super::check_input(f64::MAX, 10.0), Err(OutOfRange));
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    #[test]
    fn powf_matches_integer_powers() {
        assert!((powf(2.0, 10.0) - 1024.0).abs() < 1e-9);
        assert!((powf(9.0, 0.5) - 3.0).abs() < 1e-12);
    }

    #[cfg(any(feature = "std", feature = "libm"))]
    use super::*;

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn ln_gamma_factorial_values() {
        // Γ(1) = 1, so ln_gamma(1) = 0
        assert!((ln_gamma(1.0) - 0.0).abs() < 1e-12);
        // Γ(5) = 4! = 24, so ln_gamma(5) = ln(24)
        assert!((ln_gamma(5.0) - ln(24.0)).abs() < 1e-12);
        // Γ(1/2) = √π, so ln_gamma(0.5) = 0.5 * ln(π)
        assert!(
            0.5f64
                .mul_add(-ln(core::f64::consts::PI), ln_gamma(0.5))
                .abs()
                < 1e-12
        );
    }

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn ln_f32_matches_f64() {
        for &x in &[0.5f32, 1.0, 2.0, 10.0, 100.0] {
            let f32_result = ln_f32(x);
            let f64_result = ln(x as f64) as f32;
            assert!(
                (f32_result - f64_result).abs() < 1e-6,
                "ln_f32({x}) = {f32_result}, expected ≈ {f64_result}"
            );
        }
    }

    #[test]
    #[cfg(any(feature = "std", feature = "libm"))]
    fn exp_f32_matches_f64() {
        for &x in &[-2.0f32, -1.0, 0.0, 1.0, 2.0] {
            let f32_result = exp_f32(x);
            let f64_result = exp(x as f64) as f32;
            assert!(
                (f32_result - f64_result).abs() < 1e-5,
                "exp_f32({x}) = {f32_result}, expected ≈ {f64_result}"
            );
        }
    }
}
