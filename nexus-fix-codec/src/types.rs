use core::{fmt, num::NonZeroU32};

use nexus_ascii::{AsciiChar, AsciiTextStr};

use crate::error::FixValueError;

/// Parsed FIX decimal value (FLOAT, PRICE, QTY, AMT, PERCENTAGE, PRICEOFFSET).
///
/// Captures the wire representation without imposing a precision opinion.
/// `"123.456"` parses to `mantissa: 123_456, scale: 3`.
///
/// Convert to your preferred decimal type at the call site:
/// ```
/// # use nexus_fix_codec::FixDecimal;
/// let d = FixDecimal::parse(b"99.50").unwrap();
/// let price: f64 = d.into();
/// assert!((price - 99.5).abs() < f64::EPSILON);
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FixDecimal {
    mantissa: i64,
    scale: u8,
}

impl FixDecimal {
    pub fn new(mantissa: i64, scale: u8) -> Result<Self, FixValueError> {
        if scale > 19 {
            return Err(FixValueError::Overflow);
        }

        Ok(Self { mantissa, scale })
    }

    /// Parse a FIX decimal from wire bytes.
    ///
    /// Accepts: optional sign, digits, optional `.` + fractional digits.
    ///
    /// Uses SWAR (SIMD Within A Register) to parse up to 8 ASCII digits
    /// in parallel per block — three multiply+shift stages vs one
    /// multiply-add per digit in the scalar loop.
    ///
    /// # Errors
    /// - [`FixValueError::Empty`] on empty input (or a bare sign)
    /// - [`FixValueError::NotNumeric`] on a non-digit byte
    /// - [`FixValueError::BadFormat`] on a lone `.`
    /// - [`FixValueError::Overflow`] if the mantissa exceeds `i64` range
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        if bytes.is_empty() {
            return Err(FixValueError::Empty);
        }

        let (negative, start) = match bytes[0] {
            b'-' => (true, 1),
            b'+' => (false, 1),
            _ => (false, 0),
        };

        let src = &bytes[start..];
        if src.is_empty() {
            return Err(FixValueError::Empty);
        }

        let dot_pos = src.iter().position(|&b| b == b'.');

        let (mantissa_u64, scale) = if let Some(dp) = dot_pos {
            let int_part = &src[..dp];
            let frac_part = &src[dp + 1..];
            if frac_part.is_empty() && int_part.is_empty() {
                return Err(FixValueError::BadFormat);
            }
            let scale = frac_part.len() as u8;

            let int_val = if int_part.is_empty() {
                0u64
            } else {
                parse_unsigned_digits(int_part)?
            };

            let frac_val = if frac_part.is_empty() {
                0u64
            } else {
                parse_unsigned_digits(frac_part)?
            };

            let scale_mul = 10u64
                .checked_pow(scale as u32)
                .ok_or(FixValueError::Overflow)?;
            let mantissa = int_val
                .checked_mul(scale_mul)
                .and_then(|m| m.checked_add(frac_val))
                .ok_or(FixValueError::Overflow)?;
            (mantissa, scale)
        } else {
            let val = parse_unsigned_digits(src)?;
            (val, 0u8)
        };

        let mantissa = if negative {
            let signed = mantissa_u64 as i128;
            let neg = -signed;
            if neg < i64::MIN as i128 {
                return Err(FixValueError::Overflow);
            }
            neg as i64
        } else {
            if mantissa_u64 > i64::MAX as u64 {
                return Err(FixValueError::Overflow);
            }
            mantissa_u64 as i64
        };

        Ok(Self { mantissa, scale })
    }

    /// Encode this decimal to wire bytes.
    ///
    /// Writes the FIX representation (e.g., `"-123.456"`) into `buf` and
    /// returns the number of bytes written.
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 22 bytes — the widest a FIX decimal
    /// with an `i64` mantissa can occupy (`"-0."` + 19 fractional digits, the
    /// `i64::MIN`-magnitude mantissa at scale 19). The single up-front check
    /// gives an atomic, clearly-messaged failure and lets the optimizer elide
    /// the per-store bounds checks in the body.
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 22,
            "FixDecimal::encode: buffer too small (need up to 22 bytes, have {})",
            buf.len()
        );
        let mut pos = 0;

        if self.mantissa < 0 {
            buf[pos] = b'-';
            pos += 1;
        }

        let abs = self.mantissa.unsigned_abs();

        debug_assert!(
            self.scale <= 19,
            "FixDecimal::encode: scale over 19 ({}) will result in an integer overflow",
            self.scale
        );
        if self.scale == 0 {
            pos += encode_u64(abs, &mut buf[pos..]);
            return pos;
        }

        let scale_pow = 10u64.pow(self.scale as u32);
        let integer = abs / scale_pow;
        let frac = abs % scale_pow;

        pos += encode_u64(integer, &mut buf[pos..]);
        buf[pos] = b'.';
        pos += 1;
        encode_u64_padded(frac, self.scale as usize, &mut buf[pos..]);
        pos += self.scale as usize;

        pos
    }
}

impl From<FixDecimal> for f64 {
    #[inline]
    fn from(d: FixDecimal) -> Self {
        d.mantissa as f64 / 10_f64.powi(d.scale as i32)
    }
}

impl From<FixDecimal> for f32 {
    #[inline]
    fn from(d: FixDecimal) -> Self {
        d.mantissa as f32 / 10_f32.powi(d.scale as i32)
    }
}

impl fmt::Display for FixDecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_assert!(
            self.scale <= 19,
            "<FixDecimal as std::fmt::Display>::fmt: scale over 19 ({}) will result in an integer overflow",
            self.scale
        );
        if self.scale == 0 {
            return write!(f, "{}", self.mantissa);
        }
        // u64 divisor: scale can reach 19, and 10^19 overflows i64 (it fits in
        // u64). Split the magnitude in u64 and carry the sign separately.
        let divisor = 10_u64.pow(self.scale as u32);
        let abs = self.mantissa.unsigned_abs();
        let integer = abs / divisor;
        let frac = abs % divisor;
        let width = self.scale as usize;
        if self.mantissa < 0 {
            write!(f, "-{integer}.{frac:0>width$}")
        } else {
            write!(f, "{integer}.{frac:0>width$}")
        }
    }
}

/// Parsed FIX timestamp as nanos since unix epoch.
///
/// FIX timestamps are UTC by convention (`YYYYMMDD-HH:MM:SS[.sss[sss[sss]]]`).
///
/// The inner value is nanoseconds since the Unix epoch. [`parse`](Self::parse)
/// only produces instants within the FIX `YYYYMMDD` year range (≤ 9999), for
/// which [`as_secs`](Self::as_secs) and [`decompose`](Self::decompose) are
/// lossless. Constructing a `FixTimestamp` directly from an out-of-range raw
/// nanosecond count (e.g. near `i128::MAX`) is garbage-in: the `i64`/`i32`
/// conversions in those accessors wrap, as with any nanosecond-based instant
/// type. The accessors are Euclidean, so for any in-range instant (including
/// pre-epoch negatives) `as_secs() * 1e9 + subsec_nanos() == as_nanos()`.
///
/// ```
/// # use nexus_fix_codec::FixTimestamp;
/// let ts = FixTimestamp::parse(b"20260602-14:30:00.123456").unwrap();
/// assert_eq!(ts.subsec_nanos(), 123_456_000);
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FixTimestamp(pub i128);

impl FixTimestamp {
    const NANOS_PER_SEC: i128 = 1_000_000_000;
    const SECS_PER_DAY: i128 = 86400;

    /// Parse a FIX UTC timestamp: `YYYYMMDD-HH:MM:SS[.sss[sss[sss]]]`.
    ///
    /// The entire input must be consumed — trailing bytes are rejected, since
    /// the field value is SOH-delimited and any trailing byte is part of it.
    ///
    /// The leap second `23:59:60` is accepted; since Unix time has no leap
    /// seconds it is stored as the equivalent instant (`00:00:00` the next
    /// day) and re-encodes as such.
    ///
    /// # Errors
    /// - [`FixValueError::BadFormat`] if too short, the `-` separator is
    ///   missing, or trailing bytes remain
    /// - propagates [`FixDate::parse`]/time errors (`NotNumeric`, `OutOfRange`)
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        // Minimum: YYYYMMDD-HH:MM:SS = 17 bytes
        if bytes.len() < 17 {
            return Err(FixValueError::BadFormat);
        }

        let date = FixDate::parse(&bytes[..8])?;
        if bytes[8] != b'-' {
            return Err(FixValueError::BadFormat);
        }
        let (time, consumed) = parse_time_of_day(&bytes[9..])?;
        if 9 + consumed != bytes.len() {
            return Err(FixValueError::BadFormat);
        }

        let epoch_days = date.to_epoch_days().ok_or(FixValueError::OutOfRange)? as i128;
        let secs = epoch_days * Self::SECS_PER_DAY
            + time.nanos_since_midnight as i128 / Self::NANOS_PER_SEC;
        let sub_nanos = time.nanos_since_midnight as i128 % Self::NANOS_PER_SEC;

        Ok(Self(secs * Self::NANOS_PER_SEC + sub_nanos))
    }

    /// Nanosecond value (nanos since unix epoch).
    #[inline]
    pub const fn as_nanos(self) -> i128 {
        self.0
    }

    /// Microseconds since the Unix epoch (floored toward negative infinity,
    /// consistent with [`subsec_nanos`](Self::subsec_nanos)).
    #[inline]
    pub const fn as_micros(self) -> i128 {
        self.0.div_euclid(1_000)
    }

    /// Milliseconds since the Unix epoch (floored toward negative infinity).
    #[inline]
    pub const fn as_millis(self) -> i128 {
        self.0.div_euclid(1_000_000)
    }

    /// Whole seconds since the Unix epoch (floored, matching
    /// [`decompose`](Self::decompose)).
    #[inline]
    pub const fn as_secs(self) -> i64 {
        self.0.div_euclid(Self::NANOS_PER_SEC) as i64
    }

    /// Sub-second component in `0..1_000_000_000` for **any** instant — the
    /// Euclidean remainder, so `as_secs() * 1e9 + subsec_nanos() == as_nanos()`
    /// holds for negative (pre-epoch) timestamps too.
    #[inline]
    pub const fn subsec_nanos(self) -> u32 {
        self.0.rem_euclid(Self::NANOS_PER_SEC) as u32
    }

    /// Decompose into date and time-of-day components.
    pub fn decompose(self) -> (FixDate, FixTime) {
        let total_secs = self.0.div_euclid(Self::NANOS_PER_SEC);
        let sub_nanos = self.0.rem_euclid(Self::NANOS_PER_SEC) as u64;

        let epoch_days = total_secs.div_euclid(Self::SECS_PER_DAY) as i32;
        let secs_in_day = total_secs.rem_euclid(Self::SECS_PER_DAY) as u64;

        let date = FixDate::from_epoch_days(epoch_days);
        let time = FixTime {
            nanos_since_midnight: secs_in_day * FixTime::NANOS_PER_SEC + sub_nanos,
        };
        (date, time)
    }

    /// Encode as FIX timestamp wire bytes (`YYYYMMDD-HH:MM:SS[.fractional]`).
    ///
    /// Fractional precision is auto-detected: millis (3), micros (6), or nanos (9).
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 27 bytes
    /// (`YYYYMMDD-HH:MM:SS.nnnnnnnnn`).
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 27,
            "FixTimestamp::encode: buffer too small (need up to 27 bytes, have {})",
            buf.len()
        );
        let (date, time) = self.decompose();
        let mut pos = date.encode(buf);
        buf[pos] = b'-';
        pos += 1;
        pos += time.encode(&mut buf[pos..]);
        pos
    }
}

impl fmt::Display for FixTimestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}ns", self.0)
    }
}

/// Parsed FIX date (`YYYYMMDD`, UTC by convention).
///
/// ```
/// # use nexus_fix_codec::FixDate;
/// let d = FixDate::parse(b"20260602").unwrap();
/// assert_eq!(d.year, 2026);
/// assert_eq!(d.month, 6);
/// assert_eq!(d.day, 2);
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixDate {
    pub year: u16,
    pub month: u8,
    pub day: u8,
}

impl FixDate {
    /// Parse `YYYYMMDD` from wire bytes (exactly 8 bytes; trailing bytes are
    /// rejected since the SOH-delimited field value includes them).
    ///
    /// # Errors
    /// - [`FixValueError::BadFormat`] if the length is not exactly 8
    /// - [`FixValueError::NotNumeric`] on a non-digit byte
    /// - [`FixValueError::OutOfRange`] if month ∉ 1..=12 or day ∉ 1..=31
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        if bytes.len() != 8 {
            return Err(FixValueError::BadFormat);
        }

        let year = parse_digits_u16(&bytes[..4])?;
        let month = parse_digits_u8(&bytes[4..6])?;
        let day = parse_digits_u8(&bytes[6..8])?;

        if month == 0 || month > 12 || day == 0 || day > 31 {
            return Err(FixValueError::OutOfRange);
        }

        Ok(Self { year, month, day })
    }

    /// Days since the Unix epoch (1970-01-01); negative for earlier dates.
    ///
    /// Always returns `Some` for a well-formed `FixDate`; the `Option`
    /// return is retained for forward compatibility.
    pub fn to_epoch_days(&self) -> Option<i32> {
        // Rata Die algorithm (Howard Hinnant)
        let y = if self.month <= 2 {
            self.year as i32 - 1
        } else {
            self.year as i32
        };
        let m = if self.month <= 2 {
            self.month as i32 + 9
        } else {
            self.month as i32 - 3
        };
        let era = y.div_euclid(400);
        let yoe = y.rem_euclid(400);
        let doy = (153 * m + 2) / 5 + self.day as i32 - 1;
        let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
        let days = era * 146_097 + doe - 719_468;
        Some(days)
    }

    /// Construct a date from days since unix epoch (1970-01-01).
    ///
    /// Inverse of [`to_epoch_days`](Self::to_epoch_days). Uses the Hinnant
    /// civil-from-days algorithm.
    pub fn from_epoch_days(days: i32) -> Self {
        let z = days + 719_468;
        let era = z.div_euclid(146_097);
        let doe = z.rem_euclid(146_097) as u32;
        let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
        let y = yoe as i32 + era * 400;
        let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
        let mp = (5 * doy + 2) / 153;
        let d = doy - (153 * mp + 2) / 5 + 1;
        let m = if mp < 10 { mp + 3 } else { mp - 9 };
        let y = if m <= 2 { y + 1 } else { y };
        Self {
            year: y as u16,
            month: m as u8,
            day: d as u8,
        }
    }

    /// Encode as `YYYYMMDD` wire bytes. Always writes exactly 8 bytes.
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 8 bytes.
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 8,
            "FixDate::encode: buffer too small (need 8 bytes, have {})",
            buf.len()
        );
        encode_4_digits(buf, self.year);
        encode_2_digits(&mut buf[4..], self.month);
        encode_2_digits(&mut buf[6..], self.day);
        8
    }
}

impl fmt::Display for FixDate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:04}{:02}{:02}", self.year, self.month, self.day)
    }
}

/// Parsed FIX time of day (`HH:MM:SS[.sss[sss[sss]]]`, UTC by convention).
///
/// ```
/// # use nexus_fix_codec::FixTime;
/// let t = FixTime::parse(b"14:30:00.500").unwrap();
/// assert_eq!(t.nanos_since_midnight, 52_200_500_000_000);
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FixTime {
    pub nanos_since_midnight: u64,
}

impl FixTime {
    const NANOS_PER_SEC: u64 = 1_000_000_000;
    const NANOS_PER_MIN: u64 = 60 * Self::NANOS_PER_SEC;
    const NANOS_PER_HOUR: u64 = 3600 * Self::NANOS_PER_SEC;
    /// One full day. A `nanos_since_midnight` at or beyond this encodes the
    /// leap second `23:59:60` (the only valid `SS=60`); the components below
    /// special-case that range so it reports `23:59:60` and round-trips.
    const NANOS_PER_DAY: u64 = 86_400 * Self::NANOS_PER_SEC;

    /// Parse `HH:MM:SS[.sss[sss[sss]]]` from wire bytes.
    ///
    /// The entire input must be consumed — trailing bytes are rejected, since
    /// the field value is SOH-delimited and any trailing byte is part of it.
    ///
    /// # Errors
    /// - [`FixValueError::BadFormat`] if too short, a `:` separator is missing,
    ///   or trailing bytes remain
    /// - [`FixValueError::NotNumeric`] on a non-digit byte
    /// - [`FixValueError::OutOfRange`] if hour/minute/second is out of range
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        let (time, consumed) = parse_time_of_day(bytes)?;
        if consumed != bytes.len() {
            return Err(FixValueError::BadFormat);
        }
        Ok(time)
    }

    /// Hours component (`0..=23`).
    #[inline]
    pub const fn hour(&self) -> u8 {
        if self.nanos_since_midnight >= Self::NANOS_PER_DAY {
            23 // leap second 23:59:60
        } else {
            (self.nanos_since_midnight / Self::NANOS_PER_HOUR) as u8
        }
    }

    /// Minutes component (`0..=59`).
    #[inline]
    pub const fn minute(&self) -> u8 {
        if self.nanos_since_midnight >= Self::NANOS_PER_DAY {
            59 // leap second 23:59:60
        } else {
            ((self.nanos_since_midnight % Self::NANOS_PER_HOUR) / Self::NANOS_PER_MIN) as u8
        }
    }

    /// Seconds component (`0..=60`; `60` only for the leap second `23:59:60`).
    #[inline]
    pub const fn second(&self) -> u8 {
        if self.nanos_since_midnight >= Self::NANOS_PER_DAY {
            60 // leap second 23:59:60
        } else {
            ((self.nanos_since_midnight % Self::NANOS_PER_MIN) / Self::NANOS_PER_SEC) as u8
        }
    }

    /// Sub-second nanos (`0..=999_999_999`).
    #[inline]
    pub const fn subsec_nanos(&self) -> u32 {
        if self.nanos_since_midnight >= Self::NANOS_PER_DAY {
            (self.nanos_since_midnight - Self::NANOS_PER_DAY) as u32
        } else {
            (self.nanos_since_midnight % Self::NANOS_PER_SEC) as u32
        }
    }

    /// Encode as `HH:MM:SS[.sss[sss[sss]]]` wire bytes.
    ///
    /// Returns the number of bytes written (8, 12, 15, or 18).
    /// Fractional precision is auto-detected from the value.
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 18 bytes (`HH:MM:SS.nnnnnnnnn`).
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 18,
            "FixTime::encode: buffer too small (need up to 18 bytes, have {})",
            buf.len()
        );
        encode_2_digits(buf, self.hour());
        buf[2] = b':';
        encode_2_digits(&mut buf[3..], self.minute());
        buf[5] = b':';
        encode_2_digits(&mut buf[6..], self.second());

        let sub = self.subsec_nanos();
        if sub == 0 {
            return 8;
        }

        buf[8] = b'.';

        if sub.is_multiple_of(1_000_000) {
            encode_u64_padded(sub as u64 / 1_000_000, 3, &mut buf[9..]);
            12
        } else if sub.is_multiple_of(1_000) {
            encode_u64_padded(sub as u64 / 1_000, 6, &mut buf[9..]);
            15
        } else {
            encode_u64_padded(sub as u64, 9, &mut buf[9..]);
            18
        }
    }
}

impl fmt::Display for FixTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sub = self.subsec_nanos();
        if sub == 0 {
            write!(
                f,
                "{:02}:{:02}:{:02}",
                self.hour(),
                self.minute(),
                self.second()
            )
        } else {
            write!(
                f,
                "{:02}:{:02}:{:02}.{:09}",
                self.hour(),
                self.minute(),
                self.second(),
                sub
            )
        }
    }
}

/// Parsed FIX `MonthYear` field.
///
/// Three on-the-wire forms, preserved exactly for byte-faithful round-trip:
/// `YYYYMM`, `YYYYMMDD`, and `YYYYMM` + `wW` (week-of-month `1..=5`). The
/// forms are NOT interchangeable — `202603`, `20260318`, and `202603w3` are
/// distinct values and re-encode to exactly what was parsed.
///
/// IMM-ness (3rd-Wednesday futures expiry) has no FIX wire type; it is
/// derived by the application from `(year, month)` and is never a variant
/// here.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FixMonthYear {
    /// `YYYYMM` — year and month only.
    YearMonth {
        /// Four-digit year.
        year: u16,
        /// Month, `1..=12`.
        month: u8,
    },
    /// `YYYYMMDD` — year, month, and day.
    YearMonthDay(FixDate),
    /// `YYYYMM` + `wW` — year, month, and week-of-month (`1..=5`).
    YearMonthWeek {
        /// Four-digit year.
        year: u16,
        /// Month, `1..=12`.
        month: u8,
        /// Week of month, `1..=5`.
        week: u8,
    },
}

impl FixMonthYear {
    /// Parse a FIX `MonthYear` from wire bytes.
    ///
    /// # Errors
    /// - [`FixValueError::BadFormat`] on an unrecognized length/shape
    /// - [`FixValueError::NotNumeric`] on a non-digit where digits are required
    /// - [`FixValueError::OutOfRange`] if month ∉ `1..=12`, day ∉ `1..=31`,
    ///   or week ∉ `1..=5`
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        match bytes.len() {
            6 => {
                // YYYYMM
                let year = parse_digits_u16(&bytes[..4])?;
                let month = parse_digits_u8(&bytes[4..6])?;
                if month == 0 || month > 12 {
                    return Err(FixValueError::OutOfRange);
                }
                Ok(Self::YearMonth { year, month })
            }
            8 if bytes[6] == b'w' => {
                // YYYYMM + "wW" — disambiguated from YYYYMMDD by the 'w' at [6]
                let year = parse_digits_u16(&bytes[..4])?;
                let month = parse_digits_u8(&bytes[4..6])?;
                let week = parse_digits_u8(&bytes[7..8])?;
                if month == 0 || month > 12 {
                    return Err(FixValueError::OutOfRange);
                }
                if week == 0 || week > 5 {
                    return Err(FixValueError::OutOfRange);
                }
                Ok(Self::YearMonthWeek { year, month, week })
            }
            8 => {
                // YYYYMMDD — defer to FixDate (validates month/day range)
                Ok(Self::YearMonthDay(FixDate::parse(bytes)?))
            }
            _ => Err(FixValueError::BadFormat),
        }
    }

    /// Encode as wire bytes; returns the number written (6 or 8).
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 8 bytes.
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 8,
            "FixMonthYear::encode: buffer too small (need up to 8 bytes, have {})",
            buf.len()
        );
        match *self {
            Self::YearMonth { year, month } => {
                encode_4_digits(buf, year);
                encode_2_digits(&mut buf[4..], month);
                6
            }
            Self::YearMonthDay(date) => date.encode(buf),
            Self::YearMonthWeek { year, month, week } => {
                encode_4_digits(buf, year);
                encode_2_digits(&mut buf[4..], month);
                buf[6] = b'w';
                buf[7] = b'0' + week;
                8
            }
        }
    }
}

impl fmt::Display for FixMonthYear {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::YearMonth { year, month } => write!(f, "{year:04}{month:02}"),
            Self::YearMonthDay(d) => write!(f, "{d}"),
            Self::YearMonthWeek { year, month, week } => {
                write!(f, "{year:04}{month:02}w{week}")
            }
        }
    }
}

/// FIX `Tenor` unit. The grammar admits exactly four units.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TenorUnit {
    /// `D` — days.
    Day,
    /// `W` — weeks.
    Week,
    /// `M` — months.
    Month,
    /// `Y` — years.
    Year,
}

impl TenorUnit {
    #[inline]
    const fn from_byte(b: u8) -> Option<Self> {
        match b {
            b'D' => Some(Self::Day),
            b'W' => Some(Self::Week),
            b'M' => Some(Self::Month),
            b'Y' => Some(Self::Year),
            _ => None,
        }
    }

    /// The wire byte for this unit (`D`/`W`/`M`/`Y`).
    #[inline]
    pub const fn as_byte(self) -> u8 {
        match self {
            Self::Day => b'D',
            Self::Week => b'W',
            Self::Month => b'M',
            Self::Year => b'Y',
        }
    }
}

/// Parsed FIX `Tenor` value: a unit and a positive count.
///
/// Wire grammar (FIX 5.0 SP2): `^[DWMY][1-9][0-9]*$` — a unit letter
/// (`D`/`W`/`M`/`Y`) followed by a positive integer. Examples: `D5`, `W13`,
/// `M3`, `Y1`. Strict/canonical: leading zeros are rejected so the value
/// round-trips byte-for-byte.
///
/// FX market codes (`ON`/`TN`/`SN`/`SW`) and `SettlType` enums (`B`/`C`/`0`–`9`)
/// are NOT `Tenor` values — they belong to the *field* that uses the Tenor
/// datatype, not the datatype itself, and live in the application/codegen
/// layer.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixTenor {
    /// The tenor unit (day/week/month/year).
    pub unit: TenorUnit,
    /// The positive count (`> 0`).
    pub value: NonZeroU32,
}

impl FixTenor {
    /// Parse a FIX `Tenor` from wire bytes.
    ///
    /// # Errors
    /// - [`FixValueError::Empty`] on empty input
    /// - [`FixValueError::BadFormat`] on a missing/invalid unit letter, no
    ///   digits, or a leading zero
    /// - [`FixValueError::NotNumeric`] on a non-digit in the count
    /// - [`FixValueError::Overflow`] if the count exceeds `u32`
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        let (&unit_byte, rest) = bytes.split_first().ok_or(FixValueError::Empty)?;
        let unit = TenorUnit::from_byte(unit_byte).ok_or(FixValueError::BadFormat)?;
        // Count must be present, with no leading zero (canonical form, so the
        // value re-encodes byte-for-byte). A leading '0' also rules out "0".
        if rest.is_empty() || rest[0] == b'0' {
            return Err(FixValueError::BadFormat);
        }
        let n = parse_unsigned_digits(rest)?;
        let n = u32::try_from(n).map_err(|_| FixValueError::Overflow)?;
        // n >= 1 here (first digit is 1..=9), so this never returns OutOfRange.
        let value = NonZeroU32::new(n).ok_or(FixValueError::OutOfRange)?;
        Ok(Self { unit, value })
    }

    /// Encode as wire bytes (`<unit><count>`); returns the number written.
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 11 bytes (`Y4294967295`).
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 11,
            "FixTenor::encode: buffer too small (need up to 11 bytes, have {})",
            buf.len()
        );
        buf[0] = self.unit.as_byte();
        1 + encode_u64(self.value.get() as u64, &mut buf[1..])
    }
}

impl fmt::Display for FixTenor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.unit.as_byte() as char, self.value)
    }
}

// ---------------------------------------------------------------------------
// Timezone-qualified temporal types (FIX TZTimeOnly / TZTimestamp)
// ---------------------------------------------------------------------------

/// Parse a timezone offset suffix in canonical form: `Z` or `±HH:MM`.
///
/// Returns the offset east of UTC in minutes (`Z` => 0). Accepts the `±HH:MM`
/// form (not the minutes-omitted `±HH`) and `Z`. `+00:00`/`-00:00` parse to a
/// zero offset and re-encode as `Z` (a zero offset is canonically `Z`).
fn parse_tz_offset(bytes: &[u8]) -> Result<i16, FixValueError> {
    if bytes == b"Z" {
        return Ok(0);
    }
    if bytes.len() != 6 || (bytes[0] != b'+' && bytes[0] != b'-') || bytes[3] != b':' {
        return Err(FixValueError::BadFormat);
    }
    let hh = parse_digits_u8(&bytes[1..3])?;
    let mm = parse_digits_u8(&bytes[4..6])?;
    if hh > 23 || mm > 59 {
        return Err(FixValueError::OutOfRange);
    }
    let total = hh as i16 * 60 + mm as i16;
    Ok(if bytes[0] == b'-' { -total } else { total })
}

/// Encode a timezone offset (minutes east of UTC) as `Z` or `±HH:MM`.
/// Returns the number of bytes written (1 or 6).
///
/// # Panics
/// Panics if `|offset_minutes|` exceeds `23:59` (the widest `±HH:MM` form).
/// `unsigned_abs` keeps the magnitude total over the full `i16` domain (no
/// negation overflow on `i16::MIN`), and the range check turns an invalid
/// constructed offset into a clear panic instead of an out-of-bounds index.
fn encode_tz_offset(offset_minutes: i16, buf: &mut [u8]) -> usize {
    if offset_minutes == 0 {
        buf[0] = b'Z';
        return 1;
    }
    let mag = offset_minutes.unsigned_abs();
    assert!(
        mag <= 23 * 60 + 59,
        "encode_tz_offset: offset {offset_minutes} out of range (±23:59 max)"
    );
    buf[0] = if offset_minutes < 0 { b'-' } else { b'+' };
    encode_2_digits(&mut buf[1..], (mag / 60) as u8);
    buf[3] = b':';
    encode_2_digits(&mut buf[4..], (mag % 60) as u8);
    6
}

fn write_tz_offset(f: &mut fmt::Formatter<'_>, offset_minutes: i16) -> fmt::Result {
    if offset_minutes == 0 {
        return f.write_str("Z");
    }
    // `unsigned_abs` is total over the full i16 domain (no `i16::MIN` overflow);
    // Display stays panic-free even for an out-of-range constructed offset.
    let sign = if offset_minutes < 0 { '-' } else { '+' };
    let mag = offset_minutes.unsigned_abs();
    write!(f, "{sign}{:02}:{:02}", mag / 60, mag % 60)
}

/// FIX `TZTimeOnly`: a time of day with an explicit UTC offset.
///
/// Parses `HH:MM:SS[.frac]` followed by a canonical offset (`Z` or `±HH:MM`).
/// Both the wall-clock time and the wire offset are preserved, so the value
/// re-encodes byte-for-byte. Seconds are required, matching [`FixTime`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixTzTime {
    /// The local wall-clock time of day.
    pub time: FixTime,
    /// Offset east of UTC, in minutes (`Z` => 0).
    pub offset_minutes: i16,
}

impl FixTzTime {
    /// Parse `HH:MM:SS[.frac]±HH:MM` (or a trailing `Z`).
    ///
    /// # Errors
    /// Propagates [`FixTime`] parse errors and adds [`FixValueError::BadFormat`]
    /// / [`FixValueError::OutOfRange`] for a malformed or out-of-range offset.
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        let (time, consumed) = parse_time_of_day(bytes)?;
        let offset_minutes = parse_tz_offset(&bytes[consumed..])?;
        Ok(Self {
            time,
            offset_minutes,
        })
    }

    /// Encode as `HH:MM:SS[.frac]±HH:MM`/`Z`; returns the number written.
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 24 bytes.
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 24,
            "FixTzTime::encode: buffer too small (need up to 24 bytes, have {})",
            buf.len()
        );
        let mut pos = self.time.encode(buf);
        pos += encode_tz_offset(self.offset_minutes, &mut buf[pos..]);
        pos
    }
}

impl fmt::Display for FixTzTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.time)?;
        write_tz_offset(f, self.offset_minutes)
    }
}

/// FIX `TZTimestamp`: a date-time with an explicit UTC offset.
///
/// Stored as the UTC instant (`utc_nanos`, nanoseconds since the Unix epoch)
/// plus the wire offset, so the value re-encodes byte-for-byte. UTC-only
/// timestamps should use [`FixTimestamp`]; this type exists solely to carry a
/// non-UTC offset.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FixTzTimestamp {
    /// The instant, in nanoseconds since the Unix epoch (UTC).
    pub utc_nanos: i128,
    /// Offset east of UTC, in minutes (`Z` => 0).
    pub offset_minutes: i16,
}

impl FixTzTimestamp {
    const NANOS_PER_SEC: i128 = 1_000_000_000;
    const SECS_PER_DAY: i128 = 86_400;

    /// Parse `YYYYMMDD-HH:MM:SS[.frac]±HH:MM` (or a trailing `Z`).
    ///
    /// # Errors
    /// [`FixValueError::BadFormat`] if too short or the `-` separator is
    /// missing; propagates date/time/offset errors.
    pub fn parse(bytes: &[u8]) -> Result<Self, FixValueError> {
        if bytes.len() < 17 {
            return Err(FixValueError::BadFormat);
        }
        let date = FixDate::parse(&bytes[..8])?;
        if bytes[8] != b'-' {
            return Err(FixValueError::BadFormat);
        }
        let (time, consumed) = parse_time_of_day(&bytes[9..])?;
        let offset_minutes = parse_tz_offset(&bytes[9 + consumed..])?;

        let epoch_days = date.to_epoch_days().ok_or(FixValueError::OutOfRange)? as i128;
        let local_nanos = epoch_days * Self::SECS_PER_DAY * Self::NANOS_PER_SEC
            + time.nanos_since_midnight as i128;
        let utc_nanos = local_nanos - offset_minutes as i128 * 60 * Self::NANOS_PER_SEC;
        Ok(Self {
            utc_nanos,
            offset_minutes,
        })
    }

    /// Encode as `YYYYMMDD-HH:MM:SS[.frac]±HH:MM`/`Z`; returns bytes written.
    ///
    /// # Panics
    /// Panics if `buf` is shorter than 33 bytes.
    pub fn encode(&self, buf: &mut [u8]) -> usize {
        assert!(
            buf.len() >= 33,
            "FixTzTimestamp::encode: buffer too small (need up to 33 bytes, have {})",
            buf.len()
        );
        let local_nanos = self.utc_nanos + self.offset_minutes as i128 * 60 * Self::NANOS_PER_SEC;
        let (date, time) = FixTimestamp(local_nanos).decompose();
        let mut pos = date.encode(buf);
        buf[pos] = b'-';
        pos += 1;
        pos += time.encode(&mut buf[pos..]);
        pos += encode_tz_offset(self.offset_minutes, &mut buf[pos..]);
        pos
    }
}

impl fmt::Display for FixTzTimestamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let local_nanos = self.utc_nanos + self.offset_minutes as i128 * 60 * Self::NANOS_PER_SEC;
        let (date, time) = FixTimestamp(local_nanos).decompose();
        write!(f, "{date}-{time}")?;
        write_tz_offset(f, self.offset_minutes)
    }
}

// ---------------------------------------------------------------------------
// Tier 1 parsing helpers (used by generated code)
// ---------------------------------------------------------------------------

/// Parse a FIX integer field (INT type) from wire bytes.
///
/// Handles optional leading sign. Uses SWAR for the digit portion.
///
/// # Errors
/// - [`FixValueError::Empty`] on empty input (or sign with no digits)
/// - [`FixValueError::NotNumeric`] on a non-digit byte
/// - [`FixValueError::Overflow`] if the value exceeds `i64` range
pub fn parse_fix_int(bytes: &[u8]) -> Result<i64, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }

    let (negative, start) = match bytes[0] {
        b'-' => (true, 1),
        b'+' => (false, 1),
        _ => (false, 0),
    };

    let digits = &bytes[start..];
    if digits.is_empty() {
        return Err(FixValueError::Empty);
    }

    let unsigned = parse_unsigned_digits(digits)?;

    if negative {
        let signed = unsigned as i128;
        let neg = -signed;
        if neg < i64::MIN as i128 {
            return Err(FixValueError::Overflow);
        }
        Ok(neg as i64)
    } else {
        if unsigned > i64::MAX as u64 {
            return Err(FixValueError::Overflow);
        }
        Ok(unsigned as i64)
    }
}

/// Parse a FIX unsigned integer (LENGTH, NUMINGROUP) from wire bytes.
///
/// Uses SWAR for the digit portion. Returns [`FixValueError::Empty`] on
/// empty input, [`FixValueError::NotNumeric`] on a non-digit byte, and
/// [`FixValueError::Overflow`] if the value exceeds `u32` range.
pub fn parse_fix_uint(bytes: &[u8]) -> Result<u32, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }
    let val = parse_unsigned_digits(bytes)?;
    u32::try_from(val).map_err(|_| FixValueError::Overflow)
}

/// Parse a FIX sequence number (SEQNUM) from wire bytes.
///
/// Uses SWAR for the digit portion. Returns [`FixValueError::Empty`] on
/// empty input, [`FixValueError::NotNumeric`] on a non-digit byte, and
/// [`FixValueError::Overflow`] if the value exceeds `u64` range.
pub fn parse_fix_seqnum(bytes: &[u8]) -> Result<u64, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }
    parse_unsigned_digits(bytes)
}

/// Parse a FIX boolean (`Y` / `N`) from wire bytes.
///
/// Returns [`FixValueError::Empty`] on empty input and
/// [`FixValueError::BadFormat`] for anything other than a single `Y`/`N`.
#[inline]
pub fn parse_fix_bool(bytes: &[u8]) -> Result<bool, FixValueError> {
    match bytes {
        [b'Y'] => Ok(true),
        [b'N'] => Ok(false),
        [] => Err(FixValueError::Empty),
        _ => Err(FixValueError::BadFormat),
    }
}

/// Parse a FIX `char` field (a single ASCII character).
///
/// Returns [`FixValueError::Empty`] on empty input,
/// [`FixValueError::BadFormat`] if the value is not exactly one byte, and
/// [`FixValueError::NotPrintable`] if the byte is not valid ASCII.
///
/// The codec hands back the raw [`AsciiChar`]; mapping a char field to a
/// typed enum (`Side`, `OrdType`, ...) is the application/codegen layer's
/// job, not the wire codec's.
#[inline]
pub fn parse_fix_char(bytes: &[u8]) -> Result<AsciiChar, FixValueError> {
    match bytes {
        [b] => AsciiChar::try_new(*b).map_err(|_| FixValueError::NotPrintable),
        [] => Err(FixValueError::Empty),
        _ => Err(FixValueError::BadFormat),
    }
}

/// Parse a FIX `DayOfMonth` field (`1..=31`).
///
/// Returns [`FixValueError::Empty`] on empty input,
/// [`FixValueError::NotNumeric`] on a non-digit byte, and
/// [`FixValueError::OutOfRange`] if the value is not in `1..=31`.
pub fn parse_fix_day_of_month(bytes: &[u8]) -> Result<u8, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }
    let day = parse_unsigned_digits(bytes)?;
    if (1..=31).contains(&day) {
        Ok(day as u8)
    } else {
        Err(FixValueError::OutOfRange)
    }
}

/// Parse a FIX text field (`String`, `Currency`, `Exchange`, `Country`,
/// `Language`, `Symbol`, ...) as a zero-copy printable-ASCII borrow.
///
/// The returned [`AsciiTextStr`] borrows from `bytes` — no allocation, no
/// copy. To key on the value (e.g. a symbol → order-book map), extract an
/// owned `AsciiText<CAP>` at the call site, e.g.
/// `nexus_ascii::AsciiText::<8>::try_from(text.as_str())`.
///
/// Returns [`FixValueError::Empty`] on empty input and
/// [`FixValueError::NotPrintable`] if any byte is a control or non-ASCII
/// byte. Note this is stricter than the raw field value, which is always
/// available as `&[u8]` for callers that want to skip validation.
#[inline]
pub fn parse_fix_text(bytes: &[u8]) -> Result<&AsciiTextStr, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }
    AsciiTextStr::try_from_bytes(bytes).map_err(|_| FixValueError::NotPrintable)
}

/// Parse a FIX `MultipleCharValue` field: space-delimited single characters.
///
/// Validates the whole field once (printable ASCII, single-char tokens),
/// then yields each [`AsciiChar`] with no allocation. Borrows from `bytes`.
///
/// # Errors
/// - [`FixValueError::Empty`] on empty input
/// - [`FixValueError::NotPrintable`] on a control/non-ASCII byte
/// - [`FixValueError::BadFormat`] if any space-delimited token is not exactly
///   one character (leading/trailing/double spaces produce zero-length tokens)
pub fn parse_fix_multi_char(
    bytes: &[u8],
) -> Result<impl Iterator<Item = AsciiChar> + '_, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }
    AsciiTextStr::try_from_bytes(bytes).map_err(|_| FixValueError::NotPrintable)?;
    if bytes.split(|&b| b == b' ').any(|tok| tok.len() != 1) {
        return Err(FixValueError::BadFormat);
    }
    Ok(bytes.split(|&b| b == b' ').map(|tok| {
        // Each token is exactly one printable byte (validated above), so
        // `try_new` cannot fail.
        AsciiChar::try_new(tok[0]).expect("validated single printable char")
    }))
}

/// Parse a FIX `MultipleStringValue` field: space-delimited strings.
///
/// Validates the whole field once (printable ASCII, no empty tokens), then
/// yields each token as a zero-copy [`AsciiTextStr`] borrowed from `bytes`.
///
/// # Errors
/// - [`FixValueError::Empty`] on empty input
/// - [`FixValueError::NotPrintable`] on a control/non-ASCII byte
/// - [`FixValueError::BadFormat`] on leading/trailing/double spaces
pub fn parse_fix_multi_string(
    bytes: &[u8],
) -> Result<impl Iterator<Item = &AsciiTextStr> + '_, FixValueError> {
    if bytes.is_empty() {
        return Err(FixValueError::Empty);
    }
    AsciiTextStr::try_from_bytes(bytes).map_err(|_| FixValueError::NotPrintable)?;
    if bytes.first() == Some(&b' ')
        || bytes.last() == Some(&b' ')
        || bytes.windows(2).any(|w| matches!(w, [b' ', b' ']))
    {
        return Err(FixValueError::BadFormat);
    }
    Ok(bytes.split(|&b| b == b' ').map(|tok| {
        // SAFETY: the whole field validated as printable ASCII above, so every
        // space-delimited subslice is also printable ASCII.
        unsafe { AsciiTextStr::from_bytes_unchecked(tok) }
    }))
}

// ---------------------------------------------------------------------------
// Tier 1 encoding helpers (used by generated code)
// ---------------------------------------------------------------------------

/// The maximum number of bytes any owned FIX value type encodes to.
///
/// The widest is [`FixTzTimestamp`] (`YYYYMMDD-HH:MM:SS.nnnnnnnnn±HH:MM`, 33
/// bytes). Generated encoder scratch buffers for the owned value types
/// (decimal/timestamp/date/time/…) are sized to this constant so a scratch
/// buffer can never silently fall behind a type's `encode()` requirement; each
/// `encode()` keeps its own tighter buffer assert. Bump this if a wider value
/// type is added — the `max_value_encode_len_covers_widest_type` test guards it.
pub const MAX_VALUE_ENCODE_LEN: usize = 33;

/// Encode a FIX integer field (INT type) to wire bytes.
///
/// Writes the decimal representation (with leading `-` for negatives).
/// Buffer must be at least 20 bytes. Returns the number of bytes written.
pub fn encode_fix_int(value: i64, buf: &mut [u8]) -> usize {
    let mut pos = 0;
    if value < 0 {
        buf[pos] = b'-';
        pos += 1;
    }
    pos += encode_u64(value.unsigned_abs(), &mut buf[pos..]);
    pos
}

/// Encode a FIX unsigned integer (LENGTH, NUMINGROUP) to wire bytes.
///
/// Buffer must be at least 10 bytes. Returns the number of bytes written.
pub fn encode_fix_uint(value: u32, buf: &mut [u8]) -> usize {
    encode_u64(value as u64, buf)
}

/// Encode a FIX sequence number (SEQNUM) to wire bytes.
///
/// Buffer must be at least 20 bytes. Returns the number of bytes written.
pub fn encode_fix_seqnum(value: u64, buf: &mut [u8]) -> usize {
    encode_u64(value, buf)
}

/// Encode a FIX boolean as a single byte (`Y` or `N`).
#[inline]
pub fn encode_fix_bool(value: bool) -> u8 {
    if value { b'Y' } else { b'N' }
}

/// Encode a FIX `char` field as a single byte.
#[inline]
pub fn encode_fix_char(value: AsciiChar) -> u8 {
    value.as_u8()
}

// Note: there is no `encode_fix_text`. A FIX text value is already its wire
// form — callers pass `text.as_bytes()` straight to the writer. (Decoding earns
// `parse_fix_text` because it validates printable ASCII; encoding is a plain
// byte copy with nothing to add.)

// ---------------------------------------------------------------------------
// SWAR digit parsing
// ---------------------------------------------------------------------------

/// Parse up to 8 ASCII digits in parallel using SWAR.
///
/// Digits are left-padded with '0' in an 8-byte register, then combined
/// pairwise: 8 single digits -> 4 two-digit pairs -> 2 four-digit values -> result.
/// Three multiply+shift stages vs 8 scalar multiply-add iterations.
#[inline]
fn swar_parse_8(digits: &[u8]) -> Result<u32, FixValueError> {
    debug_assert!(!digits.is_empty() && digits.len() <= 8);

    let mut buf = [b'0'; 8];
    buf[8 - digits.len()..].copy_from_slice(digits);

    let v = u64::from_le_bytes(buf).wrapping_sub(0x3030_3030_3030_3030);

    // Validate: every byte must be 0..=9. Adding 6 to any value >= 10
    // sets bits in the 0xF0 mask; values that wrapped (original < '0')
    // already have those bits set.
    let chk = v.wrapping_add(0x0606_0606_0606_0606);
    if (chk | v) & 0xF0F0_F0F0_F0F0_F0F0 != 0 {
        return Err(FixValueError::NotNumeric);
    }

    // Combine adjacent byte pairs: d0*10+d1, d2*10+d3, d4*10+d5, d6*10+d7
    let lo = v & 0x00FF_00FF_00FF_00FF;
    let hi = (v >> 8) & 0x00FF_00FF_00FF_00FF;
    let v = lo * 10 + hi;

    // Combine u16 pairs: pair0*100+pair1, pair2*100+pair3
    let lo = v & 0x0000_FFFF_0000_FFFF;
    let hi = (v >> 16) & 0x0000_FFFF_0000_FFFF;
    let v = lo * 100 + hi;

    // Combine u32 halves: lo*10000 + hi
    let lo = v as u32;
    let hi = (v >> 32) as u32;
    Ok(lo * 10_000 + hi)
}

/// Parse up to 16 ASCII digits using two SWAR blocks.
#[inline]
fn swar_parse_16(digits: &[u8]) -> Result<u64, FixValueError> {
    debug_assert!(!digits.is_empty() && digits.len() <= 16);

    if digits.len() <= 8 {
        return swar_parse_8(digits).map(|v| v as u64);
    }

    let split = digits.len() - 8;
    let hi = swar_parse_8(&digits[..split])? as u64;
    let lo = swar_parse_8(&digits[split..])? as u64;
    Ok(hi * 100_000_000 + lo)
}

/// Parse an unsigned digit string into u64. SWAR for <= 16 digits, scalar fallback for 17-19.
fn parse_unsigned_digits(digits: &[u8]) -> Result<u64, FixValueError> {
    if digits.is_empty() {
        return Err(FixValueError::Empty);
    }
    if digits.len() > 19 {
        return Err(FixValueError::Overflow);
    }
    if digits.len() <= 16 {
        return swar_parse_16(digits);
    }
    // 17-19 digits: parse leading scalar digits, then two SWAR blocks
    let leading = digits.len() - 16;
    let mut hi = 0u64;
    for &b in &digits[..leading] {
        match b {
            b'0'..=b'9' => hi = hi * 10 + (b - b'0') as u64,
            _ => return Err(FixValueError::NotNumeric),
        }
    }
    let lo = swar_parse_16(&digits[leading..])?;
    hi.checked_mul(10_000_000_000_000_000)
        .and_then(|h| h.checked_add(lo))
        .ok_or(FixValueError::Overflow)
}

// ---------------------------------------------------------------------------
// Digit encoding helpers
// ---------------------------------------------------------------------------

const DIGIT_PAIRS: [u8; 200] = {
    let mut lut = [0u8; 200];
    let mut i = 0;
    while i < 100 {
        lut[i * 2] = b'0' + (i / 10) as u8;
        lut[i * 2 + 1] = b'0' + (i % 10) as u8;
        i += 1;
    }
    lut
};

#[inline]
fn encode_2_digits(buf: &mut [u8], value: u8) {
    let idx = value as usize * 2;
    buf[0] = DIGIT_PAIRS[idx];
    buf[1] = DIGIT_PAIRS[idx + 1];
}

#[inline]
fn encode_4_digits(buf: &mut [u8], value: u16) {
    encode_2_digits(buf, (value / 100) as u8);
    encode_2_digits(&mut buf[2..], (value % 100) as u8);
}

/// Encode a u64 as decimal ASCII. Returns the number of bytes written.
fn encode_u64(value: u64, buf: &mut [u8]) -> usize {
    if value == 0 {
        buf[0] = b'0';
        return 1;
    }

    let mut tmp = [0u8; 20];
    let mut pos = 20usize;
    let mut v = value;

    while v >= 100 {
        let rem = (v % 100) as usize;
        v /= 100;
        pos -= 2;
        tmp[pos] = DIGIT_PAIRS[rem * 2];
        tmp[pos + 1] = DIGIT_PAIRS[rem * 2 + 1];
    }

    if v >= 10 {
        pos -= 2;
        tmp[pos] = DIGIT_PAIRS[v as usize * 2];
        tmp[pos + 1] = DIGIT_PAIRS[v as usize * 2 + 1];
    } else {
        pos -= 1;
        tmp[pos] = b'0' + v as u8;
    }

    let len = 20 - pos;
    buf[..len].copy_from_slice(&tmp[pos..]);
    len
}

/// Encode a u64 as zero-padded decimal ASCII of exactly `width` digits.
fn encode_u64_padded(value: u64, width: usize, buf: &mut [u8]) {
    debug_assert!(width <= 20);
    let mut tmp = [b'0'; 20];
    let mut pos = 20usize;
    let mut v = value;

    while v > 0 {
        let rem = (v % 100) as usize;
        v /= 100;
        pos -= 2;
        tmp[pos] = DIGIT_PAIRS[rem * 2];
        tmp[pos + 1] = DIGIT_PAIRS[rem * 2 + 1];
    }

    buf[..width].copy_from_slice(&tmp[20 - width..]);
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Parse `HH:MM:SS[.fractional]`, returning the time and bytes consumed.
fn parse_time_of_day(bytes: &[u8]) -> Result<(FixTime, usize), FixValueError> {
    // Minimum: HH:MM:SS = 8 bytes
    if bytes.len() < 8 {
        return Err(FixValueError::BadFormat);
    }

    let hour = parse_digits_u8(&bytes[..2])?;
    if bytes[2] != b':' {
        return Err(FixValueError::BadFormat);
    }
    let minute = parse_digits_u8(&bytes[3..5])?;
    if bytes[5] != b':' {
        return Err(FixValueError::BadFormat);
    }
    let second = parse_digits_u8(&bytes[6..8])?;

    if hour > 23 || minute > 59 || second > 60 {
        return Err(FixValueError::OutOfRange);
    }
    // FIX permits the leap second SS=60, but only at 23:59:60 — the resulting
    // nanos land in the [NANOS_PER_DAY, +1s) range that the FixTime accessors
    // and encoder special-case. A :60 anywhere else (e.g. 00:00:60) would
    // alias a normal time (00:01:00), so reject it.
    if second == 60 && (hour != 23 || minute != 59) {
        return Err(FixValueError::OutOfRange);
    }

    let mut nanos = hour as u64 * FixTime::NANOS_PER_HOUR
        + minute as u64 * FixTime::NANOS_PER_MIN
        + second as u64 * FixTime::NANOS_PER_SEC;

    let mut consumed = 8;

    // Optional fractional seconds: .sss, .ssssss, or .sssssssss
    if bytes.len() > 8 && bytes[8] == b'.' {
        consumed = 9;
        let mut frac: u64 = 0;
        let mut frac_digits: u32 = 0;

        for &b in &bytes[9..] {
            match b {
                b'0'..=b'9' if frac_digits < 9 => {
                    frac = frac * 10 + (b - b'0') as u64;
                    frac_digits += 1;
                    consumed += 1;
                }
                _ => break,
            }
        }

        // A '.' must be followed by at least one fractional digit.
        if frac_digits == 0 {
            return Err(FixValueError::BadFormat);
        }

        // Scale to nanoseconds (pad with zeros if fewer than 9 digits).
        while frac_digits < 9 {
            frac *= 10;
            frac_digits += 1;
        }
        nanos += frac;
    }

    Ok((
        FixTime {
            nanos_since_midnight: nanos,
        },
        consumed,
    ))
}

fn parse_digits_u16(bytes: &[u8]) -> Result<u16, FixValueError> {
    let mut value: u16 = 0;
    for &b in bytes {
        match b {
            b'0'..=b'9' => {
                value = value
                    .checked_mul(10)
                    .and_then(|v| v.checked_add((b - b'0') as u16))
                    .ok_or(FixValueError::Overflow)?;
            }
            _ => return Err(FixValueError::NotNumeric),
        }
    }
    Ok(value)
}

fn parse_digits_u8(bytes: &[u8]) -> Result<u8, FixValueError> {
    let mut value: u8 = 0;
    for &b in bytes {
        match b {
            b'0'..=b'9' => {
                value = value
                    .checked_mul(10)
                    .and_then(|v| v.checked_add(b - b'0'))
                    .ok_or(FixValueError::Overflow)?;
            }
            _ => return Err(FixValueError::NotNumeric),
        }
    }
    Ok(value)
}

// ---------------------------------------------------------------------------
// Feature-gated conversions
// ---------------------------------------------------------------------------

#[cfg(feature = "nexus-decimal")]
mod decimal_conv {
    use super::FixDecimal;
    use nexus_decimal::{Backing, Decimal};

    /// Error when a [`FixDecimal`] cannot be represented in the target decimal type.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct DecimalConvError {
        pub mantissa: i64,
        pub scale: u8,
    }

    impl core::fmt::Display for DecimalConvError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(
                f,
                "cannot convert FixDecimal(mantissa={}, scale={}) to target decimal: overflow on rescale",
                self.mantissa, self.scale
            )
        }
    }

    impl std::error::Error for DecimalConvError {}

    impl<const D: u8> TryFrom<FixDecimal> for Decimal<i128, D>
    where
        i128: Backing,
    {
        type Error = DecimalConvError;

        fn try_from(d: FixDecimal) -> Result<Self, Self::Error> {
            let err = || DecimalConvError {
                mantissa: d.mantissa,
                scale: d.scale,
            };
            let mantissa = d.mantissa as i128;
            let scaled = if D >= d.scale {
                mantissa
                    .checked_mul(10_i128.checked_pow((D - d.scale) as u32).ok_or_else(err)?)
                    .ok_or_else(err)?
            } else {
                mantissa / 10_i128.checked_pow((d.scale - D) as u32).ok_or_else(err)?
            };
            Ok(Self::from_raw(scaled))
        }
    }

    // i64 backing: fallible — rescale can overflow i64.
    impl<const D: u8> TryFrom<FixDecimal> for Decimal<i64, D>
    where
        i64: Backing,
    {
        type Error = DecimalConvError;

        fn try_from(d: FixDecimal) -> Result<Self, Self::Error> {
            let err = || DecimalConvError {
                mantissa: d.mantissa,
                scale: d.scale,
            };

            let scaled = if D >= d.scale {
                d.mantissa
                    .checked_mul(10_i64.checked_pow((D - d.scale) as u32).ok_or_else(err)?)
                    .ok_or_else(err)?
            } else {
                d.mantissa / 10_i64.checked_pow((d.scale - D) as u32).ok_or_else(err)?
            };
            Ok(Self::from_raw(scaled))
        }
    }

    // i32 backing: fallible — even more constrained.
    impl<const D: u8> TryFrom<FixDecimal> for Decimal<i32, D>
    where
        i32: Backing,
    {
        type Error = DecimalConvError;

        fn try_from(d: FixDecimal) -> Result<Self, Self::Error> {
            let err = || DecimalConvError {
                mantissa: d.mantissa,
                scale: d.scale,
            };

            let scaled = if D >= d.scale {
                d.mantissa
                    .checked_mul(10_i64.checked_pow((D - d.scale) as u32).ok_or_else(err)?)
                    .ok_or_else(err)?
            } else {
                d.mantissa / 10_i64.checked_pow((d.scale - D) as u32).ok_or_else(err)?
            };
            let narrow = i32::try_from(scaled).map_err(|_| err())?;
            Ok(Self::from_raw(narrow))
        }
    }

    // -- Reverse: Decimal → FixDecimal --

    // i64 backing → FixDecimal: infallible — i64 mantissa maps directly.
    impl<const D: u8> From<Decimal<i64, D>> for FixDecimal
    where
        i64: Backing,
    {
        fn from(d: Decimal<i64, D>) -> Self {
            Self {
                mantissa: d.to_raw(),
                scale: D,
            }
        }
    }

    // i32 backing → FixDecimal: infallible — i32 widens to i64.
    impl<const D: u8> From<Decimal<i32, D>> for FixDecimal
    where
        i32: Backing,
    {
        fn from(d: Decimal<i32, D>) -> Self {
            Self {
                mantissa: d.to_raw() as i64,
                scale: D,
            }
        }
    }

    /// Error when a decimal mantissa exceeds i64 range for [`FixDecimal`].
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct DecimalToFixError;

    impl core::fmt::Display for DecimalToFixError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "decimal mantissa exceeds i64 range for FixDecimal")
        }
    }

    impl std::error::Error for DecimalToFixError {}

    // i128 backing → FixDecimal: fallible — i128 may not fit in i64.
    impl<const D: u8> TryFrom<Decimal<i128, D>> for FixDecimal
    where
        i128: Backing,
    {
        type Error = DecimalToFixError;

        fn try_from(d: Decimal<i128, D>) -> Result<Self, Self::Error> {
            let mantissa = i64::try_from(d.to_raw()).map_err(|_| DecimalToFixError)?;
            Ok(Self { mantissa, scale: D })
        }
    }
}

#[cfg(feature = "nexus-decimal")]
pub use decimal_conv::DecimalConvError;

#[cfg(feature = "nexus-decimal")]
pub use decimal_conv::DecimalToFixError;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- FixDecimal --

    #[test]
    fn decimal_parse_integer() {
        let d = FixDecimal::parse(b"12345").unwrap();
        assert_eq!(d.mantissa, 12345);
        assert_eq!(d.scale, 0);
    }

    #[test]
    fn decimal_parse_fractional() {
        let d = FixDecimal::parse(b"123.456").unwrap();
        assert_eq!(d.mantissa, 123_456);
        assert_eq!(d.scale, 3);
    }

    #[test]
    fn decimal_parse_negative() {
        let d = FixDecimal::parse(b"-99.5").unwrap();
        assert_eq!(d.mantissa, -995);
        assert_eq!(d.scale, 1);
    }

    #[test]
    fn decimal_parse_positive_sign() {
        let d = FixDecimal::parse(b"+42.0").unwrap();
        assert_eq!(d.mantissa, 420);
        assert_eq!(d.scale, 1);
    }

    #[test]
    fn decimal_parse_leading_zero() {
        let d = FixDecimal::parse(b"0.001").unwrap();
        assert_eq!(d.mantissa, 1);
        assert_eq!(d.scale, 3);
    }

    #[test]
    fn decimal_parse_zero() {
        let d = FixDecimal::parse(b"0").unwrap();
        assert_eq!(d.mantissa, 0);
        assert_eq!(d.scale, 0);
    }

    #[test]
    fn decimal_parse_empty() {
        assert_eq!(FixDecimal::parse(b""), Err(FixValueError::Empty));
    }

    #[test]
    fn decimal_parse_sign_only() {
        assert_eq!(FixDecimal::parse(b"-"), Err(FixValueError::Empty));
        assert_eq!(FixDecimal::parse(b"+"), Err(FixValueError::Empty));
    }

    #[test]
    fn decimal_parse_non_digit() {
        assert_eq!(FixDecimal::parse(b"12.3a4"), Err(FixValueError::NotNumeric));
    }

    #[test]
    fn decimal_parse_double_dot() {
        assert!(FixDecimal::parse(b"12.3.4").is_err());
    }

    #[test]
    fn decimal_to_f64() {
        let d = FixDecimal::parse(b"123.456").unwrap();
        let f: f64 = d.into();
        assert!((f - 123.456).abs() < 1e-10);
    }

    #[test]
    fn decimal_to_f64_negative() {
        let d = FixDecimal::parse(b"-0.5").unwrap();
        let f: f64 = d.into();
        assert!((f - (-0.5)).abs() < 1e-10);
    }

    #[test]
    fn decimal_display_integer() {
        let d = FixDecimal {
            mantissa: 42,
            scale: 0,
        };
        assert_eq!(d.to_string(), "42");
    }

    #[test]
    fn decimal_display_fractional() {
        let d = FixDecimal {
            mantissa: 12345,
            scale: 2,
        };
        assert_eq!(d.to_string(), "123.45");
    }

    #[test]
    fn decimal_display_negative_frac() {
        let d = FixDecimal {
            mantissa: -5,
            scale: 1,
        };
        assert_eq!(d.to_string(), "-0.5");
    }

    #[test]
    fn decimal_display_leading_zeros() {
        let d = FixDecimal {
            mantissa: 1,
            scale: 3,
        };
        assert_eq!(d.to_string(), "0.001");
    }

    // -- FixDate --

    #[test]
    fn date_parse() {
        let d = FixDate::parse(b"20260602").unwrap();
        assert_eq!(d.year, 2026);
        assert_eq!(d.month, 6);
        assert_eq!(d.day, 2);
    }

    #[test]
    fn date_parse_too_short() {
        assert_eq!(FixDate::parse(b"2026060"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn date_parse_trailing_bytes() {
        // exact-length grammar: a 9th byte is part of the SOH-delimited field
        assert_eq!(FixDate::parse(b"202606021"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn date_parse_invalid_month() {
        assert_eq!(FixDate::parse(b"20261302"), Err(FixValueError::OutOfRange));
    }

    #[test]
    fn date_parse_zero_month() {
        assert_eq!(FixDate::parse(b"20260002"), Err(FixValueError::OutOfRange));
    }

    #[test]
    fn date_parse_zero_day() {
        assert_eq!(FixDate::parse(b"20260600"), Err(FixValueError::OutOfRange));
    }

    #[test]
    fn date_epoch_days() {
        // 1970-01-01 is day 0
        let d = FixDate {
            year: 1970,
            month: 1,
            day: 1,
        };
        assert_eq!(d.to_epoch_days(), Some(0));
    }

    #[test]
    fn date_epoch_days_known() {
        // 2000-01-01 = 10957 days after epoch
        let d = FixDate {
            year: 2000,
            month: 1,
            day: 1,
        };
        assert_eq!(d.to_epoch_days(), Some(10957));
    }

    #[test]
    fn date_display() {
        let d = FixDate {
            year: 2026,
            month: 6,
            day: 2,
        };
        assert_eq!(d.to_string(), "20260602");
    }

    // -- FixTime --

    #[test]
    fn time_parse_no_frac() {
        let t = FixTime::parse(b"14:30:00").unwrap();
        assert_eq!(t.hour(), 14);
        assert_eq!(t.minute(), 30);
        assert_eq!(t.second(), 0);
        assert_eq!(t.subsec_nanos(), 0);
    }

    #[test]
    fn time_parse_millis() {
        let t = FixTime::parse(b"09:05:30.123").unwrap();
        assert_eq!(t.hour(), 9);
        assert_eq!(t.minute(), 5);
        assert_eq!(t.second(), 30);
        assert_eq!(t.subsec_nanos(), 123_000_000);
    }

    #[test]
    fn time_parse_micros() {
        let t = FixTime::parse(b"23:59:59.123456").unwrap();
        assert_eq!(t.subsec_nanos(), 123_456_000);
    }

    #[test]
    fn time_parse_nanos() {
        let t = FixTime::parse(b"00:00:00.000000001").unwrap();
        assert_eq!(t.subsec_nanos(), 1);
    }

    #[test]
    fn time_parse_too_short() {
        assert_eq!(FixTime::parse(b"14:30:0"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn time_parse_invalid_hour() {
        assert_eq!(FixTime::parse(b"24:00:00"), Err(FixValueError::OutOfRange));
    }

    #[test]
    fn time_parse_invalid_minute() {
        assert_eq!(FixTime::parse(b"14:60:00"), Err(FixValueError::OutOfRange));
    }

    #[test]
    fn time_parse_leap_second() {
        // FIX permits the leap second 23:59:60 — accept and report it faithfully.
        let t = FixTime::parse(b"23:59:60").unwrap();
        assert_eq!(t.hour(), 23);
        assert_eq!(t.minute(), 59);
        assert_eq!(t.second(), 60);
        assert_eq!(t.subsec_nanos(), 0);
    }

    #[test]
    fn time_leap_second_roundtrips() {
        for input in &[
            &b"23:59:60"[..],
            &b"23:59:60.500"[..],
            &b"23:59:60.123456789"[..],
        ] {
            let t = FixTime::parse(input).unwrap();
            let mut buf = [0u8; 18];
            let n = t.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "leap-second roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn time_parse_rejects_misplaced_60() {
        // :60 only valid as the leap second 23:59:60; elsewhere it would alias
        // a normal time (00:00:60 == 00:01:00), so reject.
        assert_eq!(FixTime::parse(b"00:00:60"), Err(FixValueError::OutOfRange));
        assert_eq!(FixTime::parse(b"12:30:60"), Err(FixValueError::OutOfRange));
    }

    #[test]
    fn time_parse_rejects_trailing_bytes() {
        assert_eq!(
            FixTime::parse(b"14:30:00garbage"),
            Err(FixValueError::BadFormat)
        );
    }

    #[test]
    fn time_parse_rejects_excess_frac_digits() {
        // a 10th fractional digit is leftover -> not fully consumed -> rejected
        assert_eq!(
            FixTime::parse(b"00:00:00.1234567890"),
            Err(FixValueError::BadFormat)
        );
    }

    #[test]
    fn time_display_no_frac() {
        let t = FixTime {
            nanos_since_midnight: 14 * 3_600_000_000_000 + 30 * 60_000_000_000,
        };
        assert_eq!(t.to_string(), "14:30:00");
    }

    #[test]
    fn time_display_with_nanos() {
        let t = FixTime {
            nanos_since_midnight: 500_000_000,
        };
        assert_eq!(t.to_string(), "00:00:00.500000000");
    }

    // -- FixTimestamp --

    #[test]
    fn timestamp_parse_no_frac() {
        let ts = FixTimestamp::parse(b"19700101-00:00:00").unwrap();
        assert_eq!(ts.as_nanos(), 0);
    }

    #[test]
    fn timestamp_parse_with_frac() {
        let ts = FixTimestamp::parse(b"19700101-00:00:01.500").unwrap();
        assert_eq!(ts.as_nanos(), 1_500_000_000);
    }

    #[test]
    fn timestamp_parse_2026() {
        let ts = FixTimestamp::parse(b"20260602-14:30:00").unwrap();
        assert!(ts.as_nanos() > 0);
        assert_eq!(ts.subsec_nanos(), 0);
    }

    #[test]
    fn timestamp_accessors() {
        let ts = FixTimestamp(1_500_000_000_i128); // 1.5 seconds
        assert_eq!(ts.as_secs(), 1);
        assert_eq!(ts.as_millis(), 1500);
        assert_eq!(ts.as_micros(), 1_500_000);
        assert_eq!(ts.subsec_nanos(), 500_000_000);
    }

    #[test]
    fn timestamp_too_short() {
        assert_eq!(
            FixTimestamp::parse(b"20260602-14:30"),
            Err(FixValueError::BadFormat)
        );
    }

    #[test]
    fn timestamp_bad_separator() {
        assert_eq!(
            FixTimestamp::parse(b"20260602T14:30:00"),
            Err(FixValueError::BadFormat)
        );
    }

    #[test]
    fn timestamp_rejects_trailing_bytes() {
        assert_eq!(
            FixTimestamp::parse(b"20260602-14:30:00X"),
            Err(FixValueError::BadFormat)
        );
    }

    #[test]
    fn timestamp_leap_second_normalizes() {
        // FIX permits 23:59:60; in Unix time (no leap seconds) it is the same
        // instant as 00:00:00 the next day. Accept it; do not crash/corrupt.
        let leap = FixTimestamp::parse(b"20261231-23:59:60").unwrap();
        let next = FixTimestamp::parse(b"20270101-00:00:00").unwrap();
        assert_eq!(leap.as_nanos(), next.as_nanos());
    }

    // -- parse_fix_int --

    #[test]
    fn int_parse_positive() {
        assert_eq!(parse_fix_int(b"12345"), Ok(12345));
    }

    #[test]
    fn int_parse_negative() {
        assert_eq!(parse_fix_int(b"-42"), Ok(-42));
    }

    #[test]
    fn int_parse_zero() {
        assert_eq!(parse_fix_int(b"0"), Ok(0));
    }

    #[test]
    fn int_parse_empty() {
        assert_eq!(parse_fix_int(b""), Err(FixValueError::Empty));
    }

    #[test]
    fn int_parse_non_digit() {
        assert_eq!(parse_fix_int(b"12x"), Err(FixValueError::NotNumeric));
    }

    #[test]
    fn int_parse_overflow() {
        // one past i64::MAX
        assert_eq!(
            parse_fix_int(b"9223372036854775808"),
            Err(FixValueError::Overflow)
        );
    }

    // -- parse_fix_uint --

    #[test]
    fn uint_parse() {
        assert_eq!(parse_fix_uint(b"256"), Ok(256));
    }

    #[test]
    fn uint_parse_zero() {
        assert_eq!(parse_fix_uint(b"0"), Ok(0));
    }

    #[test]
    fn uint_parse_overflow() {
        // 2^32, one past u32::MAX
        assert_eq!(parse_fix_uint(b"4294967296"), Err(FixValueError::Overflow));
    }

    // -- parse_fix_seqnum --

    #[test]
    fn seqnum_parse() {
        assert_eq!(parse_fix_seqnum(b"1000000"), Ok(1_000_000));
    }

    // -- parse_fix_bool --

    #[test]
    fn bool_parse_y() {
        assert_eq!(parse_fix_bool(b"Y"), Ok(true));
    }

    #[test]
    fn bool_parse_n() {
        assert_eq!(parse_fix_bool(b"N"), Ok(false));
    }

    #[test]
    fn bool_parse_invalid() {
        assert_eq!(parse_fix_bool(b"y"), Err(FixValueError::BadFormat));
        assert_eq!(parse_fix_bool(b""), Err(FixValueError::Empty));
        assert_eq!(parse_fix_bool(b"YES"), Err(FixValueError::BadFormat));
    }

    // -- SWAR boundary tests --

    #[test]
    fn swar_single_digit() {
        assert_eq!(parse_fix_int(b"7"), Ok(7));
        assert_eq!(parse_fix_seqnum(b"1"), Ok(1));
    }

    #[test]
    fn swar_exactly_8_digits() {
        assert_eq!(parse_fix_int(b"12345678"), Ok(12_345_678));
        assert_eq!(parse_fix_seqnum(b"99999999"), Ok(99_999_999));
    }

    #[test]
    fn swar_9_digits_crosses_block() {
        assert_eq!(parse_fix_int(b"123456789"), Ok(123_456_789));
    }

    #[test]
    fn swar_16_digits_two_blocks() {
        assert_eq!(
            parse_fix_seqnum(b"1234567890123456"),
            Ok(1_234_567_890_123_456)
        );
    }

    #[test]
    fn swar_17_digits_scalar_plus_blocks() {
        assert_eq!(
            parse_fix_seqnum(b"12345678901234567"),
            Ok(12_345_678_901_234_567)
        );
    }

    #[test]
    fn swar_19_digits_max_i64() {
        assert_eq!(parse_fix_int(b"9223372036854775807"), Ok(i64::MAX));
    }

    #[test]
    fn swar_19_digits_min_i64() {
        assert_eq!(parse_fix_int(b"-9223372036854775808"), Ok(i64::MIN));
    }

    #[test]
    fn swar_decimal_8_digit_mantissa() {
        let d = FixDecimal::parse(b"1234.5678").unwrap();
        assert_eq!(d.mantissa, 12_345_678);
        assert_eq!(d.scale, 4);
    }

    #[test]
    fn swar_decimal_16_digit_mantissa() {
        let d = FixDecimal::parse(b"12345678.90123456").unwrap();
        assert_eq!(d.mantissa, 1_234_567_890_123_456);
        assert_eq!(d.scale, 8);
    }

    #[test]
    fn swar_decimal_realistic_price() {
        let d = FixDecimal::parse(b"50123.45000000").unwrap();
        assert_eq!(d.mantissa, 5_012_345_000_000);
        assert_eq!(d.scale, 8);
        let f: f64 = d.into();
        assert!((f - 50123.45).abs() < 1e-6);
    }

    #[test]
    fn swar_all_digit_lengths() {
        for n in 1..=19u64 {
            let s = n.to_string();
            assert_eq!(parse_fix_seqnum(s.as_bytes()), Ok(n), "failed for {n}");
        }
    }

    // -- Encode: encode_fix_int --

    #[test]
    fn encode_int_positive() {
        let mut buf = [0u8; 20];
        let n = encode_fix_int(12345, &mut buf);
        assert_eq!(&buf[..n], b"12345");
    }

    #[test]
    fn encode_int_negative() {
        let mut buf = [0u8; 20];
        let n = encode_fix_int(-42, &mut buf);
        assert_eq!(&buf[..n], b"-42");
    }

    #[test]
    fn encode_int_zero() {
        let mut buf = [0u8; 20];
        let n = encode_fix_int(0, &mut buf);
        assert_eq!(&buf[..n], b"0");
    }

    #[test]
    fn encode_int_max() {
        let mut buf = [0u8; 20];
        let n = encode_fix_int(i64::MAX, &mut buf);
        assert_eq!(&buf[..n], b"9223372036854775807");
    }

    #[test]
    fn encode_int_min() {
        let mut buf = [0u8; 20];
        let n = encode_fix_int(i64::MIN, &mut buf);
        assert_eq!(&buf[..n], b"-9223372036854775808");
    }

    // -- Encode: encode_fix_uint --

    #[test]
    fn encode_uint() {
        let mut buf = [0u8; 10];
        let n = encode_fix_uint(256, &mut buf);
        assert_eq!(&buf[..n], b"256");
    }

    #[test]
    fn encode_uint_zero() {
        let mut buf = [0u8; 10];
        let n = encode_fix_uint(0, &mut buf);
        assert_eq!(&buf[..n], b"0");
    }

    // -- Encode: encode_fix_seqnum --

    #[test]
    fn encode_seqnum() {
        let mut buf = [0u8; 20];
        let n = encode_fix_seqnum(1_000_000, &mut buf);
        assert_eq!(&buf[..n], b"1000000");
    }

    // -- Encode: encode_fix_bool --

    #[test]
    fn encode_bool_true() {
        assert_eq!(encode_fix_bool(true), b'Y');
    }

    #[test]
    fn encode_bool_false() {
        assert_eq!(encode_fix_bool(false), b'N');
    }

    // -- Encode: FixDecimal --

    #[test]
    fn decimal_encode_integer() {
        let d = FixDecimal {
            mantissa: 12345,
            scale: 0,
        };
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"12345");
    }

    #[test]
    fn decimal_encode_fractional() {
        let d = FixDecimal {
            mantissa: 123_456,
            scale: 3,
        };
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"123.456");
    }

    #[test]
    fn decimal_encode_negative() {
        let d = FixDecimal {
            mantissa: -995,
            scale: 1,
        };
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"-99.5");
    }

    #[test]
    fn decimal_encode_leading_frac_zeros() {
        let d = FixDecimal {
            mantissa: 1,
            scale: 3,
        };
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"0.001");
    }

    #[test]
    fn decimal_encode_zero() {
        let d = FixDecimal {
            mantissa: 0,
            scale: 0,
        };
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"0");
    }

    #[test]
    fn decimal_encode_negative_sub_unit() {
        let d = FixDecimal {
            mantissa: -5,
            scale: 1,
        };
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"-0.5");
    }

    // -- Encode: FixDate --

    #[test]
    fn date_encode() {
        let d = FixDate {
            year: 2026,
            month: 6,
            day: 2,
        };
        let mut buf = [0u8; 8];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"20260602");
    }

    #[test]
    fn date_from_epoch_days_epoch() {
        let d = FixDate::from_epoch_days(0);
        assert_eq!(
            d,
            FixDate {
                year: 1970,
                month: 1,
                day: 1
            }
        );
    }

    #[test]
    fn date_from_epoch_days_y2k() {
        let d = FixDate::from_epoch_days(10957);
        assert_eq!(
            d,
            FixDate {
                year: 2000,
                month: 1,
                day: 1
            }
        );
    }

    #[test]
    fn date_epoch_days_roundtrip() {
        for days in [0, 1, 365, 10957, 20000, -1, -365] {
            let date = FixDate::from_epoch_days(days);
            assert_eq!(date.to_epoch_days(), Some(days), "failed for days={days}");
        }
    }

    // -- Encode: FixTime --

    #[test]
    fn time_encode_no_frac() {
        let t = FixTime {
            nanos_since_midnight: 14 * 3_600_000_000_000 + 30 * 60_000_000_000,
        };
        let mut buf = [0u8; 18];
        let n = t.encode(&mut buf);
        assert_eq!(&buf[..n], b"14:30:00");
    }

    #[test]
    fn time_encode_millis() {
        let t = FixTime {
            nanos_since_midnight: 9 * 3_600_000_000_000
                + 5 * 60_000_000_000
                + 30_000_000_000
                + 123_000_000,
        };
        let mut buf = [0u8; 18];
        let n = t.encode(&mut buf);
        assert_eq!(&buf[..n], b"09:05:30.123");
    }

    #[test]
    fn time_encode_micros() {
        let t = FixTime {
            nanos_since_midnight: 23 * 3_600_000_000_000
                + 59 * 60_000_000_000
                + 59_000_000_000
                + 123_456_000,
        };
        let mut buf = [0u8; 18];
        let n = t.encode(&mut buf);
        assert_eq!(&buf[..n], b"23:59:59.123456");
    }

    #[test]
    fn time_encode_nanos() {
        let t = FixTime {
            nanos_since_midnight: 1,
        };
        let mut buf = [0u8; 18];
        let n = t.encode(&mut buf);
        assert_eq!(&buf[..n], b"00:00:00.000000001");
    }

    // -- Encode: FixTimestamp --

    #[test]
    fn timestamp_encode_epoch() {
        let ts = FixTimestamp(0);
        let mut buf = [0u8; 27];
        let n = ts.encode(&mut buf);
        assert_eq!(&buf[..n], b"19700101-00:00:00");
    }

    #[test]
    fn timestamp_encode_with_frac() {
        let ts = FixTimestamp(1_500_000_000);
        let mut buf = [0u8; 27];
        let n = ts.encode(&mut buf);
        assert_eq!(&buf[..n], b"19700101-00:00:01.500");
    }

    // -- Encode: too-small buffer panics (atomic up-front check) --

    #[test]
    #[should_panic(expected = "buffer too small")]
    fn decimal_encode_panics_when_too_small() {
        let d = FixDecimal {
            mantissa: 12345,
            scale: 0,
        };
        // 21 is one short of the 22-byte worst case.
        let mut buf = [0u8; 21];
        d.encode(&mut buf);
    }

    #[test]
    fn decimal_encode_max_width() {
        // i64::MIN magnitude at scale 19 is the widest decimal: "-0." + 19 frac.
        let d = FixDecimal::parse(b"-0.9223372036854775808").unwrap();
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(n, 22);
        assert_eq!(&buf[..n], b"-0.9223372036854775808");
    }

    #[test]
    fn decimal_display_scale_19_no_panic() {
        // scale 19: 10^19 overflows i64 but fits u64 — Display must not panic.
        let d = FixDecimal::parse(b"0.0000000000000000001").unwrap();
        assert_eq!(d.scale, 19);
        assert_eq!(d.to_string(), "0.0000000000000000001");
    }

    #[test]
    #[should_panic(expected = "buffer too small")]
    fn date_encode_panics_when_too_small() {
        let d = FixDate {
            year: 2026,
            month: 6,
            day: 2,
        };
        let mut buf = [0u8; 7];
        d.encode(&mut buf);
    }

    #[test]
    #[should_panic(expected = "buffer too small")]
    fn time_encode_panics_when_too_small() {
        let t = FixTime {
            nanos_since_midnight: 0,
        };
        let mut buf = [0u8; 17];
        t.encode(&mut buf);
    }

    #[test]
    #[should_panic(expected = "buffer too small")]
    fn timestamp_encode_panics_when_too_small() {
        let ts = FixTimestamp(0);
        let mut buf = [0u8; 26];
        ts.encode(&mut buf);
    }

    // -- Roundtrip: parse → encode --

    #[test]
    fn decimal_roundtrip() {
        for input in &[
            &b"12345"[..],
            &b"123.456"[..],
            &b"0.001"[..],
            &b"99.50"[..],
            &b"12345678"[..],
            &b"50123.45000000"[..],
            &b"1234567.890123456"[..],
        ] {
            let d = FixDecimal::parse(input).unwrap();
            let mut buf = [0u8; 22];
            let n = d.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn decimal_roundtrip_negative() {
        let d = FixDecimal::parse(b"-123.456").unwrap();
        let mut buf = [0u8; 22];
        let n = d.encode(&mut buf);
        assert_eq!(&buf[..n], b"-123.456");
    }

    #[test]
    fn date_roundtrip() {
        for input in &[b"20260602", b"19700101", b"20000101", b"19991231"] {
            let d = FixDate::parse(&input[..]).unwrap();
            let mut buf = [0u8; 8];
            let n = d.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                &input[..],
                "roundtrip failed for {:?}",
                core::str::from_utf8(&input[..]).unwrap()
            );
        }
    }

    #[test]
    fn time_roundtrip() {
        for input in &[
            &b"14:30:00"[..],
            &b"09:05:30.123"[..],
            &b"23:59:59.123456"[..],
            &b"00:00:00.000000001"[..],
        ] {
            let t = FixTime::parse(input).unwrap();
            let mut buf = [0u8; 18];
            let n = t.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn timestamp_roundtrip() {
        for input in &[
            &b"19700101-00:00:00"[..],
            &b"20260602-14:30:00"[..],
            &b"20260602-14:30:00.123"[..],
            &b"20260602-14:30:00.123456"[..],
            &b"20260602-14:30:00.123456789"[..],
        ] {
            let ts = FixTimestamp::parse(input).unwrap();
            let mut buf = [0u8; 27];
            let n = ts.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn int_roundtrip() {
        for val in [0i64, 1, -1, 42, -42, 12345, -12345, i64::MAX, i64::MIN] {
            let s = val.to_string();
            let parsed = parse_fix_int(s.as_bytes()).unwrap();
            assert_eq!(parsed, val);
            let mut buf = [0u8; 20];
            let n = encode_fix_int(parsed, &mut buf);
            assert_eq!(&buf[..n], s.as_bytes(), "roundtrip failed for {val}");
        }
    }

    // -- parse_fix_char / encode_fix_char --

    #[test]
    fn char_parse_valid() {
        assert_eq!(parse_fix_char(b"1").unwrap().as_u8(), b'1');
        assert_eq!(parse_fix_char(b"D").unwrap().as_u8(), b'D');
    }

    #[test]
    fn char_parse_empty() {
        assert_eq!(parse_fix_char(b"").err(), Some(FixValueError::Empty));
    }

    #[test]
    fn char_parse_too_long() {
        assert_eq!(parse_fix_char(b"AB").err(), Some(FixValueError::BadFormat));
    }

    #[test]
    fn char_parse_non_ascii() {
        assert_eq!(
            parse_fix_char(&[0x80]).err(),
            Some(FixValueError::NotPrintable)
        );
    }

    #[test]
    fn char_encode_roundtrip() {
        let c = parse_fix_char(b"2").unwrap();
        assert_eq!(encode_fix_char(c), b'2');
    }

    // -- parse_fix_day_of_month --

    #[test]
    fn day_of_month_valid() {
        assert_eq!(parse_fix_day_of_month(b"1"), Ok(1));
        assert_eq!(parse_fix_day_of_month(b"31"), Ok(31));
    }

    #[test]
    fn day_of_month_out_of_range() {
        assert_eq!(parse_fix_day_of_month(b"0"), Err(FixValueError::OutOfRange));
        assert_eq!(
            parse_fix_day_of_month(b"32"),
            Err(FixValueError::OutOfRange)
        );
    }

    #[test]
    fn day_of_month_non_digit() {
        assert_eq!(parse_fix_day_of_month(b"x"), Err(FixValueError::NotNumeric));
    }

    // -- parse_fix_text --

    #[test]
    fn text_parse_valid() {
        let t = parse_fix_text(b"BTC-USD").unwrap();
        assert_eq!(t.as_str(), "BTC-USD");
    }

    #[test]
    fn text_parse_currency_4char() {
        // crypto currency that breaks the ISO-4217 3-char assumption
        let t = parse_fix_text(b"USDT").unwrap();
        assert_eq!(t.as_str(), "USDT");
    }

    #[test]
    fn text_parse_empty() {
        assert_eq!(parse_fix_text(b"").err(), Some(FixValueError::Empty));
    }

    #[test]
    fn text_parse_non_printable() {
        assert_eq!(
            parse_fix_text(&[b'A', 0x07, b'B']).err(),
            Some(FixValueError::NotPrintable)
        );
    }

    // -- FixMonthYear --

    #[test]
    fn month_year_year_month() {
        let my = FixMonthYear::parse(b"202603").unwrap();
        assert_eq!(
            my,
            FixMonthYear::YearMonth {
                year: 2026,
                month: 3
            }
        );
    }

    #[test]
    fn month_year_year_month_day() {
        let my = FixMonthYear::parse(b"20260318").unwrap();
        assert_eq!(
            my,
            FixMonthYear::YearMonthDay(FixDate {
                year: 2026,
                month: 3,
                day: 18
            })
        );
    }

    #[test]
    fn month_year_year_month_week() {
        let my = FixMonthYear::parse(b"202603w3").unwrap();
        assert_eq!(
            my,
            FixMonthYear::YearMonthWeek {
                year: 2026,
                month: 3,
                week: 3
            }
        );
    }

    #[test]
    fn month_year_invalid_month() {
        assert_eq!(
            FixMonthYear::parse(b"202613"),
            Err(FixValueError::OutOfRange)
        );
    }

    #[test]
    fn month_year_invalid_week() {
        assert_eq!(
            FixMonthYear::parse(b"202603w6"),
            Err(FixValueError::OutOfRange)
        );
        assert_eq!(
            FixMonthYear::parse(b"202603w0"),
            Err(FixValueError::OutOfRange)
        );
    }

    #[test]
    fn month_year_bad_length() {
        assert_eq!(FixMonthYear::parse(b"2026"), Err(FixValueError::BadFormat));
        assert_eq!(FixMonthYear::parse(b"20260"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn month_year_roundtrip_all_forms() {
        for input in &[&b"202603"[..], &b"20260318"[..], &b"202603w3"[..]] {
            let my = FixMonthYear::parse(input).unwrap();
            let mut buf = [0u8; 8];
            let n = my.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn month_year_forms_distinct() {
        // same year/month, different wire forms must not compare equal
        let a = FixMonthYear::parse(b"202603").unwrap();
        let b = FixMonthYear::parse(b"202603w1").unwrap();
        assert_ne!(a, b);
    }

    // -- FixTenor --

    #[test]
    fn tenor_parse_all_units() {
        for (input, unit, val) in &[
            (&b"D5"[..], TenorUnit::Day, 5u32),
            (&b"W13"[..], TenorUnit::Week, 13),
            (&b"M3"[..], TenorUnit::Month, 3),
            (&b"Y1"[..], TenorUnit::Year, 1),
        ] {
            let t = FixTenor::parse(input).unwrap();
            assert_eq!(t.unit, *unit);
            assert_eq!(t.value.get(), *val);
        }
    }

    #[test]
    fn tenor_multi_digit() {
        let t = FixTenor::parse(b"D365").unwrap();
        assert_eq!(t.unit, TenorUnit::Day);
        assert_eq!(t.value.get(), 365);
    }

    #[test]
    fn tenor_bad_unit() {
        assert_eq!(FixTenor::parse(b"X5"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn tenor_no_digits() {
        assert_eq!(FixTenor::parse(b"D"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn tenor_empty() {
        assert_eq!(FixTenor::parse(b""), Err(FixValueError::Empty));
    }

    #[test]
    fn tenor_zero_rejected() {
        assert_eq!(FixTenor::parse(b"D0"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn tenor_leading_zero_rejected() {
        // canonical form only — preserves byte-exact round-trip
        assert_eq!(FixTenor::parse(b"D05"), Err(FixValueError::BadFormat));
    }

    #[test]
    fn tenor_non_digit() {
        assert_eq!(FixTenor::parse(b"D5x"), Err(FixValueError::NotNumeric));
    }

    #[test]
    fn tenor_roundtrip() {
        for input in &[
            &b"D5"[..],
            &b"W13"[..],
            &b"M3"[..],
            &b"Y1"[..],
            &b"D365"[..],
        ] {
            let t = FixTenor::parse(input).unwrap();
            let mut buf = [0u8; 11];
            let n = t.encode(&mut buf);
            assert_eq!(&buf[..n], *input);
        }
    }

    // -- MultipleValue iterators --

    #[test]
    fn multi_char_basic() {
        let chars: Vec<u8> = parse_fix_multi_char(b"A B C")
            .unwrap()
            .map(AsciiChar::as_u8)
            .collect();
        assert_eq!(chars, vec![b'A', b'B', b'C']);
    }

    #[test]
    fn multi_char_single() {
        let chars: Vec<u8> = parse_fix_multi_char(b"X")
            .unwrap()
            .map(AsciiChar::as_u8)
            .collect();
        assert_eq!(chars, vec![b'X']);
    }

    #[test]
    fn multi_char_rejects_multichar_token() {
        assert_eq!(
            parse_fix_multi_char(b"A BC").err(),
            Some(FixValueError::BadFormat)
        );
    }

    #[test]
    fn multi_char_empty() {
        assert_eq!(parse_fix_multi_char(b"").err(), Some(FixValueError::Empty));
    }

    #[test]
    fn multi_string_basic() {
        let toks: Vec<&str> = parse_fix_multi_string(b"FOO BAR BAZ")
            .unwrap()
            .map(AsciiTextStr::as_str)
            .collect();
        assert_eq!(toks, vec!["FOO", "BAR", "BAZ"]);
    }

    #[test]
    fn multi_string_single() {
        let toks: Vec<&str> = parse_fix_multi_string(b"SOLO")
            .unwrap()
            .map(AsciiTextStr::as_str)
            .collect();
        assert_eq!(toks, vec!["SOLO"]);
    }

    #[test]
    fn multi_string_rejects_double_space() {
        assert_eq!(
            parse_fix_multi_string(b"A  B").err(),
            Some(FixValueError::BadFormat)
        );
    }

    #[test]
    fn multi_string_rejects_leading_trailing_space() {
        assert_eq!(
            parse_fix_multi_string(b" A").err(),
            Some(FixValueError::BadFormat)
        );
        assert_eq!(
            parse_fix_multi_string(b"A ").err(),
            Some(FixValueError::BadFormat)
        );
    }

    #[test]
    fn multi_string_non_printable() {
        assert_eq!(
            parse_fix_multi_string(&[b'A', 0x01, b'B']).err(),
            Some(FixValueError::NotPrintable)
        );
    }

    // -- FixTzTime --

    #[test]
    fn tz_time_positive_offset() {
        let t = FixTzTime::parse(b"14:30:00+01:00").unwrap();
        assert_eq!(t.time.hour(), 14);
        assert_eq!(t.offset_minutes, 60);
    }

    #[test]
    fn tz_time_zulu() {
        let t = FixTzTime::parse(b"14:30:00Z").unwrap();
        assert_eq!(t.offset_minutes, 0);
    }

    #[test]
    fn tz_time_negative_offset_with_frac() {
        let t = FixTzTime::parse(b"23:59:59.500-05:30").unwrap();
        assert_eq!(t.time.subsec_nanos(), 500_000_000);
        assert_eq!(t.offset_minutes, -(5 * 60 + 30));
    }

    #[test]
    fn tz_time_bad_offset() {
        assert_eq!(
            FixTzTime::parse(b"14:30:00+1").err(),
            Some(FixValueError::BadFormat)
        );
    }

    #[test]
    fn tz_time_plus_zero_normalizes_to_zulu() {
        // "+00:00" is valid FIX (== UTC); accept it. A zero offset re-encodes
        // canonically as "Z".
        let t = FixTzTime::parse(b"14:30:00+00:00").unwrap();
        assert_eq!(t.offset_minutes, 0);
        let mut buf = [0u8; 24];
        let n = t.encode(&mut buf);
        assert_eq!(&buf[..n], b"14:30:00Z");
    }

    #[test]
    fn tz_time_roundtrip() {
        for input in &[
            &b"14:30:00Z"[..],
            &b"14:30:00+01:00"[..],
            &b"23:59:59.500-05:30"[..],
            &b"00:00:00.123456789+14:00"[..],
        ] {
            let t = FixTzTime::parse(input).unwrap();
            let mut buf = [0u8; 24];
            let n = t.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    // -- FixTzTimestamp --

    #[test]
    fn tz_timestamp_offset_converts_to_utc() {
        // 14:30+01:00 local == 13:30 UTC
        let ts = FixTzTimestamp::parse(b"20260602-14:30:00+01:00").unwrap();
        let utc = FixTimestamp::parse(b"20260602-13:30:00").unwrap();
        assert_eq!(ts.utc_nanos, utc.as_nanos());
        assert_eq!(ts.offset_minutes, 60);
    }

    #[test]
    fn tz_timestamp_zulu_matches_utc() {
        let ts = FixTzTimestamp::parse(b"20260602-14:30:00Z").unwrap();
        let utc = FixTimestamp::parse(b"20260602-14:30:00").unwrap();
        assert_eq!(ts.utc_nanos, utc.as_nanos());
        assert_eq!(ts.offset_minutes, 0);
    }

    #[test]
    fn tz_timestamp_roundtrip() {
        for input in &[
            &b"20260602-14:30:00Z"[..],
            &b"20260602-14:30:00+01:00"[..],
            &b"20260602-00:30:00+02:00"[..],
            &b"20260602-14:30:00.123-05:00"[..],
        ] {
            let ts = FixTzTimestamp::parse(input).unwrap();
            let mut buf = [0u8; 33];
            let n = ts.encode(&mut buf);
            assert_eq!(
                &buf[..n],
                *input,
                "roundtrip failed for {:?}",
                core::str::from_utf8(input).unwrap()
            );
        }
    }

    #[test]
    fn max_value_encode_len_covers_widest_type() {
        // FixTzTimestamp at full nanosecond precision with a non-zero offset is
        // the widest owned value type (33 bytes). Encoding it into a buffer of
        // exactly MAX_VALUE_ENCODE_LEN must not trip the encode() buffer assert
        // — this is the invariant generated encoder scratch buffers rely on.
        let ts = FixTzTimestamp::parse(b"20260605-12:34:56.123456789+05:30").unwrap();
        let mut buf = [0u8; MAX_VALUE_ENCODE_LEN];
        let n = ts.encode(&mut buf);
        assert_eq!(n, MAX_VALUE_ENCODE_LEN);
        assert_eq!(&buf[..n], b"20260605-12:34:56.123456789+05:30");
    }

    // -- Copilot review fixes --

    #[test]
    fn timestamp_accessors_negative_instant() {
        // pre-epoch instant -1.5s: accessors must agree with each other and
        // with decompose() (Euclidean — sub-second stays in 0..1e9).
        let ts = FixTimestamp(-1_500_000_000);
        assert_eq!(ts.as_secs(), -2);
        assert_eq!(ts.subsec_nanos(), 500_000_000);
        assert_eq!(ts.as_millis(), -1500);
        assert_eq!(
            ts.as_secs() as i128 * 1_000_000_000 + ts.subsec_nanos() as i128,
            ts.as_nanos()
        );
        let (_d, t) = ts.decompose();
        assert_eq!(t.subsec_nanos(), ts.subsec_nanos());
    }

    #[test]
    fn time_rejects_bare_trailing_dot() {
        // a '.' with no fractional digits is malformed
        assert_eq!(FixTime::parse(b"14:30:00."), Err(FixValueError::BadFormat));
    }

    #[test]
    fn tz_time_rejects_bare_trailing_dot() {
        assert_eq!(
            FixTzTime::parse(b"14:30:00.+01:00").err(),
            Some(FixValueError::BadFormat)
        );
    }

    #[test]
    fn tz_offset_display_total_over_i16() {
        // i16::MIN offset is out of range, but Display must not panic
        // (unsigned_abs, not negation).
        let t = FixTzTime {
            time: FixTime {
                nanos_since_midnight: 0,
            },
            offset_minutes: i16::MIN,
        };
        let _ = t.to_string();
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn tz_offset_encode_rejects_out_of_range() {
        // out-of-range offset is a clear panic, not an OOB index in the LUT
        let t = FixTzTime {
            time: FixTime {
                nanos_since_midnight: 0,
            },
            offset_minutes: i16::MIN,
        };
        let mut buf = [0u8; 24];
        t.encode(&mut buf);
    }

    // -- nexus-decimal conversions --

    #[cfg(feature = "nexus-decimal")]
    mod decimal_conv_tests {
        use super::*;
        use nexus_decimal::Decimal;

        #[test]
        fn to_i128_decimal_widening() {
            let d = FixDecimal::parse(b"123.45").unwrap();
            let dec: Decimal<i128, 8> = d.try_into().unwrap();
            assert_eq!(dec.to_raw(), 12_345_000_000);
        }

        #[test]
        fn to_i128_decimal_narrowing() {
            let d = FixDecimal::parse(b"1.123456789").unwrap();
            let dec: Decimal<i128, 4> = d.try_into().unwrap();
            assert_eq!(dec.to_raw(), 11234);
        }

        #[test]
        fn to_i64_decimal_ok() {
            let d = FixDecimal::parse(b"99.50").unwrap();
            let dec: Decimal<i64, 8> = d.try_into().unwrap();
            assert_eq!(dec.to_raw(), 9_950_000_000);
        }

        #[test]
        fn to_i64_decimal_overflow() {
            let d = FixDecimal {
                mantissa: i64::MAX,
                scale: 0,
            };
            let result: Result<Decimal<i64, 8>, _> = d.try_into();
            assert!(result.is_err());
        }

        #[test]
        fn to_i32_decimal_ok() {
            let d = FixDecimal::parse(b"1.25").unwrap();
            let dec: Decimal<i32, 4> = d.try_into().unwrap();
            assert_eq!(dec.to_raw(), 12500);
        }

        #[test]
        fn to_i32_decimal_overflow() {
            let d = FixDecimal::parse(b"999999999.99").unwrap();
            let result: Result<Decimal<i32, 4>, _> = d.try_into();
            assert!(result.is_err());
        }

        // -- Reverse: Decimal → FixDecimal --

        #[test]
        fn from_i64_decimal() {
            let dec = Decimal::<i64, 8>::from_raw(9_950_000_000);
            let d: FixDecimal = dec.into();
            assert_eq!(d.mantissa, 9_950_000_000);
            assert_eq!(d.scale, 8);
        }

        #[test]
        fn from_i32_decimal() {
            let dec = Decimal::<i32, 4>::from_raw(12500);
            let d: FixDecimal = dec.into();
            assert_eq!(d.mantissa, 12500);
            assert_eq!(d.scale, 4);
        }

        #[test]
        fn from_i128_decimal_ok() {
            let dec = Decimal::<i128, 8>::from_raw(12_345_000_000);
            let d: FixDecimal = dec.try_into().unwrap();
            assert_eq!(d.mantissa, 12_345_000_000);
            assert_eq!(d.scale, 8);
        }

        #[test]
        fn from_i128_decimal_overflow() {
            let dec = Decimal::<i128, 8>::from_raw(i128::MAX);
            let result: Result<FixDecimal, _> = dec.try_into();
            assert!(result.is_err());
        }

        #[test]
        fn decimal_roundtrip_through_nexus_decimal() {
            let d = FixDecimal::parse(b"99.50").unwrap();
            let dec: Decimal<i64, 8> = d.try_into().unwrap();
            let back: FixDecimal = dec.into();
            assert_eq!(back.mantissa, 9_950_000_000);
            assert_eq!(back.scale, 8);
            let f1: f64 = d.into();
            let f2: f64 = back.into();
            assert!((f1 - f2).abs() < 1e-10);
        }
    }
}
