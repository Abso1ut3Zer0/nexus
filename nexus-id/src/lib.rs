//! High-performance unique ID generators for low-latency systems.
//!
//! # Overview
//!
//! `nexus-id` provides unique ID generation optimized for trading systems and
//! other latency-sensitive applications. All generators avoid syscalls on the
//! hot path and produce stack-allocated output.
//!
//! | Generator | Speed (p50) | Time-ordered | Output | Use Case |
//! |-----------|-------------|--------------|--------|----------|
//! | [`Snowflake64`] | ~22 cycles | Yes | [`SnowflakeId64`] | Numeric IDs with extraction |
//! | [`Snowflake32`] | ~22 cycles | Yes | [`SnowflakeId32`] | Compact numeric IDs |
//! | [`UuidV4`] | ~48 cycles | No | [`Uuid`] | Random unique IDs |
//! | [`UuidV7`] | ~62 cycles | Yes | [`Uuid`] | Time-ordered UUIDs |
//! | [`UlidGenerator`] | ~80 cycles | Yes | [`Ulid`] | Sortable 26-char IDs |
//!
//! # ID Types
//!
//! | Type | Format | Use Case |
//! |------|--------|----------|
//! | [`SnowflakeId64`] | Packed u64 | Numeric IDs with field extraction |
//! | [`MixedId64`] | Fibonacci-mixed u64 | Identity hasher-safe keys |
//! | [`Uuid`] | `xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx` | Standard UUIDs |
//! | [`UuidCompact`] | 32-char hex | Compact UUIDs |
//! | [`Ulid`] | 26-char Crockford Base32 | Sortable string IDs |
//! | [`HexId64`] | 16-char hex | Hex-encoded u64 |
//! | [`Base62Id`] | 11-char alphanumeric | Short encoded u64 |
//! | [`Base36Id`] | 13-char alphanumeric | Case-insensitive u64 |
//! | [`TypeId`] | `prefix_suffix` | Domain-typed sortable IDs |
//!
//! # Parsing
//!
//! All string types support parsing from strings:
//!
//! ```rust
//! use nexus_id::{Uuid, Ulid, HexId64};
//!
//! let uuid: Uuid = "01234567-89ab-cdef-fedc-ba9876543210".parse().unwrap();
//! let hex: HexId64 = "deadbeefcafebabe".parse().unwrap();
//! ```
//!
//! # Snowflake ID Newtypes
//!
//! ```rust
//! use nexus_id::{Snowflake64, SnowflakeId64, MixedId64};
//!
//! let mut generator: Snowflake64<42, 6, 16> = Snowflake64::new(5);
//!
//! // Typed ID with field extraction
//! let id: SnowflakeId64<42, 6, 16> = generator.next_id(0).unwrap();
//! assert_eq!(id.worker(), 5);
//! assert_eq!(id.sequence(), 0);
//!
//! // Mixed for identity hashers (Fibonacci multiply, ~1 cycle)
//! let mixed: MixedId64<42, 6, 16> = id.mixed();
//! let recovered = mixed.unmix();
//! assert_eq!(recovered, id);
//! ```
//!
//! # HashMap Usage
//!
//! Snowflake IDs have poor bit distribution for power-of-2 hash tables.
//! Use either a real hasher or the mixed ID type:
//!
//! ```rust, ignore
//! use rustc_hash::FxHashMap;
//!
//! // Option 1: Use a real hasher with raw IDs
//! let map: FxHashMap<SnowflakeId64<42, 6, 16>, Order> = FxHashMap::default();
//!
//! // Option 2: Use mixed IDs with identity hasher (fastest)
//! let map: HashMap<MixedId64<42, 6, 16>, Order, nohash::BuildNoHashHasher<u64>> = ...;
//! ```
//!
//! # Features
//!
//! | Feature | Description |
//! |---------|-------------|
//! | `std` (default) | UUID/ULID generators, `Error` impls, `from_entropy()` |
//! | `serde` | `Serialize`/`Deserialize` for all types |
//! | `uuid` | Interop with the [`uuid`](https://docs.rs/uuid) crate |
//! | `bytes` | `BufMut` writing via the [`bytes`](https://docs.rs/bytes) crate |

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

pub(crate) mod encode;
mod parse;
mod simd;
mod snowflake_id;
mod typeid;
mod types;

mod snowflake;

#[cfg(feature = "std")]
mod prng;
#[cfg(feature = "std")]
pub mod ulid;
#[cfg(feature = "std")]
pub mod uuid;

pub use snowflake::{
    IdInt, SequenceExhausted, Snowflake, Snowflake32, Snowflake64, SnowflakeError,
    SnowflakeSigned32, SnowflakeSigned64,
};

pub use parse::{DecodeError, ParseError, TypeIdParseError, UuidParseError};
pub use snowflake_id::{MixedId32, MixedId64, SnowflakeId32, SnowflakeId64};
pub use typeid::TypeId;
pub use types::{Base36Id, Base62Id, HexId64, Ulid, Uuid, UuidCompact};

#[cfg(feature = "std")]
pub use ulid::UlidGenerator;
#[cfg(feature = "std")]
pub use uuid::{UuidV4, UuidV7};

// Re-export serde traits when feature is enabled
#[cfg(feature = "serde")]
mod serde_impl;

#[cfg(feature = "uuid")]
mod uuid_impl;

#[cfg(feature = "bytes")]
mod bytes_impl;
