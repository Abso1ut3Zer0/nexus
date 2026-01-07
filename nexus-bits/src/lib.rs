//! Bit field packing for integer IDs.
//!
//! `nexus-bits` provides ergonomic bit field manipulation for packing
//! multiple values into integers - common in trading systems for
//! instrument IDs, order IDs, and wire protocols.
//!
//! # Example
//!
//! ```
//! use nexus_bits::{BitField, Flag};
//!
//! // Define layout
//! const KIND: BitField<u64> = BitField::<u64>::new(0, 4);
//! const EXCHANGE: BitField<u64> = BitField::<u64>::new(4, 8);
//! const SYMBOL: BitField<u64> = BitField::<u64>::new(12, 20);
//! const IS_TEST: Flag<u64> = Flag::<u64>::new(63);
//!
//! // Pack
//! let mut id: u64 = 0;
//! id = KIND.set(id, 1).unwrap();
//! id = EXCHANGE.set(id, 5).unwrap();
//! id = SYMBOL.set(id, 12345).unwrap();
//! id = IS_TEST.set(id);
//!
//! // Unpack
//! assert_eq!(KIND.get(id), 1);
//! assert_eq!(EXCHANGE.get(id), 5);
//! assert_eq!(SYMBOL.get(id), 12345);
//! assert!(IS_TEST.is_set(id));
//! ```

#![no_std]
#![warn(missing_docs)]

mod error;
mod field;
mod flag;
mod int_enum;

pub use error::{FieldOverflow, Overflow, UnknownDiscriminant};
pub use field::BitField;
pub use flag::Flag;
pub use int_enum::IntEnum;

#[cfg(feature = "derive")]
pub use nexus_bits_derive::{BitPacked, IntEnum};
