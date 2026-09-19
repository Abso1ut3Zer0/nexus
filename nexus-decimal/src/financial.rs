//! Financial-domain methods for `Decimal`.
//!
//! Trading operations that would otherwise be error-prone to implement
//! manually: midpoint, spread, tick rounding, basis points, percentage
//! calculations, and fused multiply-divide.

use crate::Decimal;

macro_rules! impl_decimal_financial {
    ($backing:ty) => {
        impl<const D: u8> Decimal<$backing, D> {
            // ========================================================
            // Price operations
            // ========================================================

            /// Midpoint of two prices: `(self + other) / 2`.
            ///
            /// Overflow-safe midpoint: `(self + other) / 2`.
            ///
            /// Uses the bit-manipulation formula `(a & b) + ((a ^ b) >> 1)`
            /// which is correct for all representable values without
            /// intermediate overflow.
            ///
            /// # Examples
            ///
            /// ```
            /// use nexus_decimal::Decimal;
            /// type D64 = Decimal<i64, 8>;
            ///
            /// let bid = D64::new(100, 0);
            /// let ask = D64::new(101, 0);
            /// assert_eq!(bid.midpoint(ask), D64::new(100, 50_000_000));
            /// ```
            #[inline(always)]
            pub const fn midpoint(self, other: Self) -> Self {
                // Overflow-safe integer average:
                // avg(a, b) = (a & b) + ((a ^ b) >> 1)
                // Correct for all values of the backing type, no overflow possible.
                let a = self.value;
                let b = other.value;
                Self {
                    value: (a & b) + ((a ^ b) >> 1),
                }
            }

            /// Spread between two prices: `self - other`.
            ///
            /// Returns `None` if `self < other` (crossed market).
            #[inline(always)]
            pub const fn spread(self, other: Self) -> Option<Self> {
                if self.value < other.value {
                    None
                } else {
                    match self.value.checked_sub(other.value) {
                        Some(v) => Some(Self { value: v }),
                        None => None,
                    }
                }
            }

            /// Round to nearest tick size.
            ///
            /// `tick` must be positive. Rounds to the nearest multiple
            /// of `tick` using banker's rounding on the remainder.
            ///
            /// # Examples
            ///
            /// ```
            /// use nexus_decimal::Decimal;
            /// type D64 = Decimal<i64, 8>;
            ///
            /// let price = D64::new(1, 23_700_000); // 1.237
            /// let tick = D64::new(0, 5_000_000);   // 0.05
            /// assert_eq!(price.round_to_tick(tick), Some(D64::new(1, 25_000_000))); // 1.25
            /// ```
            #[inline(always)]
            pub const fn round_to_tick(self, tick: Self) -> Option<Self> {
                assert!(tick.value > 0, "tick must be positive");
                let remainder = self.value % tick.value;
                if remainder == 0 {
                    return Some(self);
                }
                let base = self.value - remainder;

                // Compare 2*|remainder| against tick without dividing.
                // Division truncates for odd ticks (e.g. tick=3, tick/2=1 not 1.5),
                // causing remainder==1 to trigger the midpoint branch incorrectly.
                // complement = tick - |remainder|; the three cases are:
                //   |remainder| > complement  -> past midpoint, round away from zero
                //   |remainder| == complement -> true midpoint, banker's rounding
                //   |remainder| < complement  -> before midpoint, truncate
                // Safe: |remainder| < tick, so complement is in (0, tick), no overflow.
                if remainder > 0 {
                    let complement = tick.value - remainder;
                    if remainder > complement {
                        match base.checked_add(tick.value) {
                            Some(v) => Some(Self { value: v }),
                            None => None,
                        }
                    } else if remainder == complement {
                        let quotient = self.value / tick.value;
                        if quotient % 2 != 0 {
                            match base.checked_add(tick.value) {
                                Some(v) => Some(Self { value: v }),
                                None => None,
                            }
                        } else {
                            Some(Self { value: base })
                        }
                    } else {
                        Some(Self { value: base })
                    }
                } else {
                    // remainder < 0; Rust % carries the dividend sign.
                    // neg_rem = |remainder|; safe since |remainder| < tick <= $backing::MAX.
                    let neg_rem = -remainder;
                    let complement = tick.value - neg_rem;
                    if neg_rem > complement {
                        match base.checked_sub(tick.value) {
                            Some(v) => Some(Self { value: v }),
                            None => None,
                        }
                    } else if neg_rem == complement {
                        let quotient = self.value / tick.value;
                        if quotient % 2 != 0 {
                            match base.checked_sub(tick.value) {
                                Some(v) => Some(Self { value: v }),
                                None => None,
                            }
                        } else {
                            Some(Self { value: base })
                        }
                    } else {
                        Some(Self { value: base })
                    }
                }
            }

            /// Floor to tick: round down to nearest multiple of `tick`.
            ///
            /// Returns `None` if the result would overflow.
            #[inline(always)]
            pub const fn floor_to_tick(self, tick: Self) -> Option<Self> {
                assert!(tick.value > 0, "tick must be positive");
                let remainder = self.value % tick.value;
                if remainder >= 0 {
                    Some(Self {
                        value: self.value - remainder,
                    })
                } else {
                    match (self.value - remainder).checked_sub(tick.value) {
                        Some(v) => Some(Self { value: v }),
                        None => None,
                    }
                }
            }

            /// Ceil to tick: round up to nearest multiple of `tick`.
            ///
            /// Returns `None` if the result would overflow.
            #[inline(always)]
            pub const fn ceil_to_tick(self, tick: Self) -> Option<Self> {
                assert!(tick.value > 0, "tick must be positive");
                let remainder = self.value % tick.value;
                if remainder > 0 {
                    match (self.value - remainder).checked_add(tick.value) {
                        Some(v) => Some(Self { value: v }),
                        None => None,
                    }
                } else if remainder < 0 {
                    Some(Self {
                        value: self.value - remainder,
                    })
                } else {
                    Some(self)
                }
            }

            // ========================================================
            // Division shortcuts
            // ========================================================

            /// Divide by 2 using integer division. Truncates toward zero.
            ///
            /// The compiler optimizes this to a shift + sign-bit adjustment.
            #[inline(always)]
            pub const fn halve(self) -> Self {
                Self {
                    value: self.value / 2,
                }
            }

            /// Divide by 10 using integer division.
            #[inline(always)]
            pub const fn div10(self) -> Self {
                Self {
                    value: self.value / 10,
                }
            }

            /// Divide by 100 using integer division.
            #[inline(always)]
            pub const fn div100(self) -> Self {
                Self {
                    value: self.value / 100,
                }
            }

            // ========================================================
            // Comparison helpers
            // ========================================================

            /// Returns `true` if `self` is within `tolerance` of `other`.
            ///
            /// Equivalent to `|self - other| <= tolerance`. Returns `false`
            /// when the difference overflows (values with opposite signs
            /// near `MAX`/`MIN`).
            #[inline]
            pub const fn approx_eq(self, other: Self, tolerance: Self) -> bool {
                let (diff, overflow) = if self.value >= other.value {
                    self.value.overflowing_sub(other.value)
                } else {
                    other.value.overflowing_sub(self.value)
                };
                !overflow && diff <= tolerance.value
            }

            /// Clamp to a price range `[min, max]`.
            #[inline]
            pub const fn clamp_price(self, min: Self, max: Self) -> Self {
                if self.value < min.value {
                    min
                } else if self.value > max.value {
                    max
                } else {
                    self
                }
            }

            // ========================================================
            // Tick alignment and bps rounding
            // ========================================================

            /// Returns `true` if `self` is aligned to the given tick size.
            ///
            /// Panics if `tick` is not positive.
            #[inline(always)]
            pub const fn is_tick_aligned(self, tick: Self) -> bool {
                assert!(tick.value > 0, "tick must be positive");
                self.value % tick.value == 0
            }

            /// Round to nearest N basis points.
            ///
            /// Returns `None` if `n == 0` or the tick computation overflows.
            ///
            /// # Compile-time constraint
            ///
            /// Requires `D >= 4`. Referencing this method on a `Decimal`
            /// with `D < 4` is a compile error.
            #[inline(always)]
            pub const fn round_bps(self, n: u32) -> Option<Self> {
                const { assert!(D >= 4, "round_bps requires D >= 4") };
                if n == 0 {
                    return None;
                }
                let bp_raw = Self::SCALE / 10000;
                let Some(tick_wide) = (bp_raw as i128).checked_mul(n as i128) else {
                    return None;
                };
                if tick_wide > <$backing>::MAX as i128 || tick_wide <= 0 {
                    return None;
                }
                self.round_to_tick(Self {
                    value: tick_wide as $backing,
                })
            }

            /// Floor to N basis points.
            ///
            /// Returns `None` if `n == 0` or the tick computation overflows.
            ///
            /// # Compile-time constraint
            ///
            /// Requires `D >= 4`. Referencing this method on a `Decimal`
            /// with `D < 4` is a compile error.
            #[inline(always)]
            pub const fn floor_bps(self, n: u32) -> Option<Self> {
                const { assert!(D >= 4, "floor_bps requires D >= 4") };
                if n == 0 {
                    return None;
                }
                let bp_raw = Self::SCALE / 10000;
                let Some(tick_wide) = (bp_raw as i128).checked_mul(n as i128) else {
                    return None;
                };
                if tick_wide > <$backing>::MAX as i128 || tick_wide <= 0 {
                    return None;
                }
                self.floor_to_tick(Self {
                    value: tick_wide as $backing,
                })
            }

            /// Ceil to N basis points.
            ///
            /// Returns `None` if `n == 0` or the tick computation overflows.
            ///
            /// # Compile-time constraint
            ///
            /// Requires `D >= 4`. Referencing this method on a `Decimal`
            /// with `D < 4` is a compile error.
            #[inline(always)]
            pub const fn ceil_bps(self, n: u32) -> Option<Self> {
                const { assert!(D >= 4, "ceil_bps requires D >= 4") };
                if n == 0 {
                    return None;
                }
                let bp_raw = Self::SCALE / 10000;
                let Some(tick_wide) = (bp_raw as i128).checked_mul(n as i128) else {
                    return None;
                };
                if tick_wide > <$backing>::MAX as i128 || tick_wide <= 0 {
                    return None;
                }
                self.ceil_to_tick(Self {
                    value: tick_wide as $backing,
                })
            }
        }
    };
}

impl_decimal_financial!(i32);
impl_decimal_financial!(i64);
impl_decimal_financial!(i128);

// ============================================================================
// Methods that need widening (per-backing-type, not in shared macro)
// ============================================================================

// --- i32: widen to i64 for percent/bps calculations ---

impl<const D: u8> Decimal<i32, D> {
    /// Compute `self * percent / 100` via single truncating division.
    ///
    /// `percent` is in percentage points: 50 means 50%.
    #[inline]
    pub const fn percent_of(self, percent: Self) -> Option<Self> {
        let product = (self.value as i64) * (percent.value as i64);
        let scale_100 = (Self::SCALE as i64) * 100;
        let result = product / scale_100;
        if result > i32::MAX as i64 || result < i32::MIN as i64 {
            None
        } else {
            Some(Self {
                value: result as i32,
            })
        }
    }

    /// Convert to basis points: `self * 10000`.
    #[inline]
    pub const fn to_bps(self) -> Option<Self> {
        self.mul_int(10_000)
    }

    /// Create from basis points: `bps / 10000`.
    #[inline]
    pub const fn from_bps(bps: i32) -> Option<Self> {
        let scaled = bps as i64 * Self::SCALE as i64 / 10_000;
        if scaled > i32::MAX as i64 || scaled < i32::MIN as i64 {
            None
        } else {
            Some(Self {
                value: scaled as i32,
            })
        }
    }

    /// Fused multiply-divide: `(self * a) / b` with single rounding.
    #[inline]
    pub const fn mul_div(self, mul: Self, div: Self) -> Option<Self> {
        if div.value == 0 {
            return None;
        }
        let product = (self.value as i64) * (mul.value as i64);
        let result = product / (div.value as i64);
        if result > i32::MAX as i64 || result < i32::MIN as i64 {
            None
        } else {
            Some(Self {
                value: result as i32,
            })
        }
    }
}

// --- i64: widen to i128 for percent/bps calculations ---

impl<const D: u8> Decimal<i64, D> {
    /// Compute `self * percent / 100` via single truncating division.
    ///
    /// `percent` is in percentage points: 50 means 50%.
    #[inline]
    pub const fn percent_of(self, percent: Self) -> Option<Self> {
        let product = (self.value as i128) * (percent.value as i128);
        let scale_100 = (Self::SCALE as i128) * 100;
        let result = product / scale_100;
        if result > i64::MAX as i128 || result < i64::MIN as i128 {
            None
        } else {
            Some(Self {
                value: result as i64,
            })
        }
    }

    /// Convert to basis points: `self * 10000`.
    #[inline]
    pub const fn to_bps(self) -> Option<Self> {
        self.mul_int(10_000)
    }

    /// Create from basis points: `bps / 10000`.
    #[inline]
    pub const fn from_bps(bps: i64) -> Option<Self> {
        let scaled = (bps as i128) * (Self::SCALE as i128);
        let value = scaled / 10_000;
        if value > i64::MAX as i128 || value < i64::MIN as i128 {
            None
        } else {
            Some(Self {
                value: value as i64,
            })
        }
    }

    /// Fused multiply-divide: `(self * a) / b` with single rounding.
    ///
    /// Keeps the full i128 intermediate — single rounding at the end.
    /// The primitive behind fee calculation, VWAP, cross-rates.
    #[inline]
    pub const fn mul_div(self, mul: Self, div: Self) -> Option<Self> {
        if div.value == 0 {
            return None;
        }
        let product = (self.value as i128) * (mul.value as i128);
        let result = product / (div.value as i128);
        if result > i64::MAX as i128 || result < i64::MIN as i128 {
            None
        } else {
            Some(Self {
                value: result as i64,
            })
        }
    }
}

// ============================================================================
// Bps/pct/tick operations (per-backing, widening)
// ============================================================================

macro_rules! impl_financial_widening {
    ($backing:ty, $wider:ty) => {
        impl<const D: u8> Decimal<$backing, D> {
            /// N basis points of self: `self * bps / 10000`.
            #[inline]
            pub const fn bps_of(self, bps: i32) -> Option<Self> {
                let product = (self.value as $wider) * (bps as $wider);
                let result = product / 10000;
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// N percent of self: `self * pct / 100`.
            #[inline]
            pub const fn pct_of(self, pct: i32) -> Option<Self> {
                let product = (self.value as $wider) * (pct as $wider);
                let result = product / 100;
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// Adjust self by N basis points: `self * (10000 + bps) / 10000`.
            #[inline]
            pub const fn shift_bps(self, bps: i32) -> Option<Self> {
                let factor = 10000_i64 + bps as i64;
                let product = (self.value as $wider) * (factor as $wider);
                let result = product / 10000;
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// Adjust self by N percent: `self * (100 + pct) / 100`.
            #[inline]
            pub const fn shift_pct(self, pct: i32) -> Option<Self> {
                let factor = 100_i64 + pct as i64;
                let product = (self.value as $wider) * (factor as $wider);
                let result = product / 100;
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// Difference in bps relative to divisor:
            /// `(self - other) / divisor * 10000`, returned as a Decimal.
            ///
            /// Uses multiply-before-divide: `diff * SCALE / divisor * 10000`
            /// to preserve precision through the fixed-point division.
            #[inline]
            pub const fn bps_diff_by(self, other: Self, divisor: Self) -> Option<Self> {
                if divisor.value == 0 {
                    return None;
                }
                let diff = (self.value as $wider) - (other.value as $wider);
                let diff_scaled = diff * (Self::SCALE as $wider);
                let divisor_w = divisor.value as $wider;
                let q = diff_scaled / divisor_w;
                let r = diff_scaled % divisor_w;
                let Some(main) = q.checked_mul(10000) else {
                    return None;
                };
                let frac = r * 10000 / divisor_w;
                let Some(result) = main.checked_add(frac) else {
                    return None;
                };
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// Difference in bps: `(self - other) * 10000 / other`.
            #[inline]
            pub const fn bps_diff(self, other: Self) -> Option<Self> {
                self.bps_diff_by(other, other)
            }

            /// Percentage difference relative to divisor:
            /// `(self - other) / divisor * 100`, returned as a Decimal.
            #[inline]
            pub const fn pct_diff_by(self, other: Self, divisor: Self) -> Option<Self> {
                if divisor.value == 0 {
                    return None;
                }
                let diff = (self.value as $wider) - (other.value as $wider);
                let diff_scaled = diff * (Self::SCALE as $wider);
                let divisor_w = divisor.value as $wider;
                let q = diff_scaled / divisor_w;
                let r = diff_scaled % divisor_w;
                let Some(main) = q.checked_mul(100) else {
                    return None;
                };
                let frac = r * 100 / divisor_w;
                let Some(result) = main.checked_add(frac) else {
                    return None;
                };
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// Percentage difference: `(self - other) * 100 / other`.
            #[inline]
            pub const fn pct_diff(self, other: Self) -> Option<Self> {
                self.pct_diff_by(other, other)
            }

            /// Returns `true` if `|self - other| <= |other| * bps / 10000`.
            #[inline]
            pub const fn within_bps(self, other: Self, bps: i32) -> bool {
                if bps < 0 {
                    return false;
                }
                let diff = if self.value >= other.value {
                    (self.value as $wider) - (other.value as $wider)
                } else {
                    (other.value as $wider) - (self.value as $wider)
                };
                let other_abs = (other.value as $wider).abs();
                let threshold = other_abs * (bps as $wider) / 10000;
                diff <= threshold
            }

            /// Returns `true` if `|self - other| <= n * tick`.
            ///
            /// Panics if `tick` is not positive.
            #[inline]
            pub const fn within_ticks(self, other: Self, n: i64, tick: Self) -> bool {
                assert!(tick.value > 0, "tick must be positive");
                let diff = if self.value >= other.value {
                    (self.value as $wider) - (other.value as $wider)
                } else {
                    (other.value as $wider) - (self.value as $wider)
                };
                let Some(threshold) = (n as $wider).checked_mul(tick.value as $wider) else {
                    return n > 0;
                };
                diff <= threshold
            }

            /// `self + n * tick`. Returns `None` on overflow.
            ///
            /// Panics if `tick` is not positive.
            #[inline]
            pub const fn add_ticks(self, n: i64, tick: Self) -> Option<Self> {
                assert!(tick.value > 0, "tick must be positive");
                let Some(offset) = (n as $wider).checked_mul(tick.value as $wider) else {
                    return None;
                };
                let Some(result) = (self.value as $wider).checked_add(offset) else {
                    return None;
                };
                if result > <$backing>::MAX as $wider || result < <$backing>::MIN as $wider {
                    None
                } else {
                    Some(Self {
                        value: result as $backing,
                    })
                }
            }

            /// `(self - other) / tick` as an integer tick count.
            ///
            /// Truncates toward zero (partial ticks dropped, matching Rust
            /// integer division).
            ///
            /// # Panics
            ///
            /// Panics if `tick` is not positive.
            #[inline]
            pub const fn tick_diff(self, other: Self, tick: Self) -> Option<i64> {
                assert!(tick.value > 0, "tick must be positive");
                let diff = (self.value as $wider) - (other.value as $wider);
                let ticks = diff / (tick.value as $wider);
                if ticks > i64::MAX as $wider || ticks < i64::MIN as $wider {
                    None
                } else {
                    Some(ticks as i64)
                }
            }
        }
    };
}

impl_financial_widening!(i32, i64);
impl_financial_widening!(i64, i128);

// --- i128: uses wide arithmetic for percent/bps ---

impl<const D: u8> Decimal<i128, D> {
    /// Convert to basis points: `self * 10000`.
    #[inline]
    pub const fn to_bps(self) -> Option<Self> {
        self.mul_int(10_000)
    }

    /// Create from basis points: `bps / 10000`.
    #[inline]
    pub const fn from_bps(bps: i128) -> Option<Self> {
        match (bps).checked_mul(Self::SCALE) {
            Some(scaled) => Some(Self {
                value: scaled / 10_000,
            }),
            None => None,
        }
    }

    /// Fused multiply-divide: `(self * a) / b` with single rounding.
    ///
    /// For i128, delegates to checked_mul then checked_div.
    /// Not truly fused (two rounding events) — a 256-bit intermediate
    /// would be needed for true single-rounding on i128.
    #[inline]
    pub fn mul_div(self, mul: Self, div: Self) -> Option<Self> {
        if div.value == 0 {
            return None;
        }
        let product = self.checked_mul(mul)?;
        product.checked_div(div)
    }

    /// N basis points of self: `self * bps / 10000`.
    ///
    /// Uses decomposition to avoid intermediate overflow.
    #[inline]
    pub const fn bps_of(self, bps: i32) -> Option<Self> {
        let q = self.value / 10000;
        let r = self.value % 10000;
        let Some(main) = q.checked_mul(bps as i128) else {
            return None;
        };
        let frac = r * (bps as i128) / 10000;
        match main.checked_add(frac) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// N percent of self: `self * pct / 100`.
    ///
    /// Uses decomposition to avoid intermediate overflow.
    #[inline]
    pub const fn pct_of(self, pct: i32) -> Option<Self> {
        let q = self.value / 100;
        let r = self.value % 100;
        let Some(main) = q.checked_mul(pct as i128) else {
            return None;
        };
        let frac = r * (pct as i128) / 100;
        match main.checked_add(frac) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// Adjust self by N basis points: `self * (10000 + bps) / 10000`.
    #[inline]
    pub const fn shift_bps(self, bps: i32) -> Option<Self> {
        let factor = 10000_i64 + bps as i64;
        let q = self.value / 10000;
        let r = self.value % 10000;
        let Some(main) = q.checked_mul(factor as i128) else {
            return None;
        };
        let frac = r * (factor as i128) / 10000;
        match main.checked_add(frac) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// Adjust self by N percent: `self * (100 + pct) / 100`.
    #[inline]
    pub const fn shift_pct(self, pct: i32) -> Option<Self> {
        let factor = 100_i64 + pct as i64;
        let q = self.value / 100;
        let r = self.value % 100;
        let Some(main) = q.checked_mul(factor as i128) else {
            return None;
        };
        let frac = r * (factor as i128) / 100;
        match main.checked_add(frac) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// Difference in bps relative to divisor:
    /// `(self - other) / divisor * 10000`, returned as a Decimal.
    ///
    /// Decomposes diff = q*divisor + r, then computes
    /// `q * SCALE * 10000 + r * SCALE * 10000 / divisor`
    /// to avoid intermediate overflow on i128.
    #[inline]
    pub const fn bps_diff_by(self, other: Self, divisor: Self) -> Option<Self> {
        if divisor.value == 0 {
            return None;
        }
        let Some(diff) = self.value.checked_sub(other.value) else {
            return None;
        };
        let q = diff / divisor.value;
        let r = diff % divisor.value;

        let main = if q == 0 {
            0
        } else {
            let Some(qs) = q.checked_mul(Self::SCALE) else {
                return None;
            };
            let Some(qs10k) = qs.checked_mul(10000) else {
                return None;
            };
            qs10k
        };

        let Some(rs) = r.checked_mul(Self::SCALE) else {
            return None;
        };
        let rs_q = rs / divisor.value;
        let rs_r = rs % divisor.value;
        let Some(frac_main) = rs_q.checked_mul(10000) else {
            return None;
        };
        // Sub-fractional term bounded by 9999 ULP; only overflows when
        // |divisor| > i128::MAX / 10000 (~10^34 raw). Precision loss is
        // negligible relative to the main result at that magnitude.
        let frac_sub = match rs_r.checked_mul(10000) {
            Some(v) => v / divisor.value,
            None => 0,
        };
        let Some(frac) = frac_main.checked_add(frac_sub) else {
            return None;
        };

        match main.checked_add(frac) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// Difference in bps: `(self - other) * 10000 / other`.
    #[inline]
    pub const fn bps_diff(self, other: Self) -> Option<Self> {
        self.bps_diff_by(other, other)
    }

    /// Percentage difference relative to divisor:
    /// `(self - other) / divisor * 100`, returned as a Decimal.
    #[inline]
    pub const fn pct_diff_by(self, other: Self, divisor: Self) -> Option<Self> {
        if divisor.value == 0 {
            return None;
        }
        let Some(diff) = self.value.checked_sub(other.value) else {
            return None;
        };
        let q = diff / divisor.value;
        let r = diff % divisor.value;

        let main = if q == 0 {
            0
        } else {
            let Some(qs) = q.checked_mul(Self::SCALE) else {
                return None;
            };
            let Some(qs100) = qs.checked_mul(100) else {
                return None;
            };
            qs100
        };

        let Some(rs) = r.checked_mul(Self::SCALE) else {
            return None;
        };
        let rs_q = rs / divisor.value;
        let rs_r = rs % divisor.value;
        let Some(frac_main) = rs_q.checked_mul(100) else {
            return None;
        };
        // Sub-fractional term bounded by 99 ULP; same overflow condition
        // as bps_diff_by — negligible precision loss at extreme magnitudes.
        let frac_sub = match rs_r.checked_mul(100) {
            Some(v) => v / divisor.value,
            None => 0,
        };
        let Some(frac) = frac_main.checked_add(frac_sub) else {
            return None;
        };

        match main.checked_add(frac) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// Percentage difference: `(self - other) * 100 / other`.
    #[inline]
    pub const fn pct_diff(self, other: Self) -> Option<Self> {
        self.pct_diff_by(other, other)
    }

    /// Returns `true` if `|self - other| <= |other| * bps / 10000`.
    #[inline]
    pub const fn within_bps(self, other: Self, bps: i32) -> bool {
        if bps < 0 {
            return false;
        }
        let abs_diff = if self.value >= other.value {
            self.value.checked_sub(other.value)
        } else {
            other.value.checked_sub(self.value)
        };
        let Some(diff) = abs_diff else {
            return false;
        };
        let other_abs = if other.value >= 0 {
            Some(other.value)
        } else {
            other.value.checked_neg()
        };
        let Some(other_abs) = other_abs else {
            return false;
        };
        match other_abs.checked_mul(bps as i128) {
            Some(product) => diff <= product / 10000,
            None => true,
        }
    }

    /// Returns `true` if `|self - other| <= n * tick`.
    ///
    /// Panics if `tick` is not positive.
    #[inline]
    pub const fn within_ticks(self, other: Self, n: i64, tick: Self) -> bool {
        assert!(tick.value > 0, "tick must be positive");
        let abs_diff = if self.value >= other.value {
            self.value.checked_sub(other.value)
        } else {
            other.value.checked_sub(self.value)
        };
        let Some(diff) = abs_diff else {
            return false;
        };
        if n <= 0 {
            return diff == 0 && n == 0;
        }
        match (n as i128).checked_mul(tick.value) {
            Some(threshold) => diff <= threshold,
            None => true,
        }
    }

    /// `self + n * tick`. Returns `None` on overflow.
    ///
    /// Panics if `tick` is not positive.
    #[inline]
    pub const fn add_ticks(self, n: i64, tick: Self) -> Option<Self> {
        assert!(tick.value > 0, "tick must be positive");
        let Some(offset) = (n as i128).checked_mul(tick.value) else {
            return None;
        };
        match self.value.checked_add(offset) {
            Some(v) => Some(Self { value: v }),
            None => None,
        }
    }

    /// `(self - other) / tick` as an integer tick count.
    ///
    /// Truncates toward zero (partial ticks dropped, matching Rust
    /// integer division).
    ///
    /// # Panics
    ///
    /// Panics if `tick` is not positive.
    #[inline]
    pub const fn tick_diff(self, other: Self, tick: Self) -> Option<i64> {
        assert!(tick.value > 0, "tick must be positive");
        let Some(diff) = self.value.checked_sub(other.value) else {
            return None;
        };
        let ticks = diff / tick.value;
        if ticks > i64::MAX as i128 || ticks < i64::MIN as i128 {
            None
        } else {
            Some(ticks as i64)
        }
    }
}
