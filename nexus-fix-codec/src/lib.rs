//! Zero-copy FIX protocol reading and writing with SIMD acceleration.
//!
//! Provides the core building blocks for FIX message handling:
//! - SOH and `=` delimiter scanning (SWAR + SSE2 + AVX2 + AVX-512)
//! - [`DelimiterScanner`] iterator with SIMD mask caching
//! - [`FieldReader`], a pure SOH-delimited field scanner; the FIX checksum is a
//!   separate single-pass verification, so trusted feeds can skip it
//! - [`FieldWriter`] for writing `tag=value` fields into a buffer
//! - [`FieldSpan`] / [`GroupSpan`] for zero-copy field access
//! - [`validate_checksum`] for FIX checksum verification
//! - [`SessionCustomizer`] for per-venue Logon auth — the engine runs it after
//!   stamping the session header and before framing `9`/`10`, so venue fields
//!   (and signatures over the stamped header) are covered by both
//! - Value-type parsers/encoders covering the FIX 5.0 SP2 field data types —
//!   numerics and decimals ([`FixDecimal`]), temporals ([`FixDate`],
//!   [`FixTime`], [`FixTimestamp`], [`FixTzTime`], [`FixTzTimestamp`]),
//!   [`FixMonthYear`], [`FixTenor`], `char`, text ([`AsciiTextStr`]), and the
//!   multi-value list iterators — returning [`FixValueError`] on malformed input
//!
//! Generated FIX codecs (from `nexus-fix-codegen`) depend on these primitives.

#![deny(
    rustdoc::broken_intra_doc_links,
    rustdoc::private_intra_doc_links,
    rustdoc::redundant_explicit_links
)]

pub mod admin;
pub mod customizer;
pub mod dict;
mod error;
mod field;
mod header;
mod span;
mod types;

pub mod reader;
pub mod scan;
pub mod writer;

pub use admin::{
    AdminEncode, Heartbeat, Logon, LogonReset, Logout, Reject, ResendRequest, SequenceReset,
    TestReqId, TestRequest,
};
pub use customizer::{AdminMsgOut, NoCustomizer, SessionCustomizer};
pub use dict::{AdminHeader, FixAdminMsg, FixDictionary, FixHeader};
pub use error::{ChecksumError, DecodeError, EncodeError, FixValueError};
pub use field::{FieldView, FromFixValue};
pub use nexus_ascii::{AsciiChar, AsciiText, AsciiTextStr};
pub use reader::{FieldReader, RawField, checksum, find_tag, parse_tag, validate_checksum};
pub use scan::DelimiterScanner;
pub use span::{FieldSpan, GroupSpan};
pub use types::{
    FixDate, FixDecimal, FixMonthYear, FixTenor, FixTime, FixTimestamp, FixTzTime, FixTzTimestamp,
    MAX_VALUE_ENCODE_LEN, TenorUnit, encode_fix_bool, encode_fix_char, encode_fix_int,
    encode_fix_seqnum, encode_fix_uint, parse_fix_bool, parse_fix_char, parse_fix_day_of_month,
    parse_fix_int, parse_fix_multi_char, parse_fix_multi_string, parse_fix_seqnum, parse_fix_text,
    parse_fix_uint,
};
pub use writer::{FieldWriter, FrameFormatter, FromFormatter, encode_field, format_checksum};

#[cfg(feature = "nexus-decimal")]
pub use types::DecimalConvError;

#[cfg(feature = "nexus-decimal")]
pub use types::DecimalToFixError;
