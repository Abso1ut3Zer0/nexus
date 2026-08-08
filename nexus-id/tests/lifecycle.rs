//! Integration tests: full lifecycle per ID type.
//!
//! Each test exercises: generate → format → parse → hash key → extract → bytes → reconstruct.
//! If these tests read naturally, the API is ready.

use std::collections::HashMap;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use nexus_id::{
    Base36Id, Base62Id, HexId64, MixedId64, Snowflake64, SnowflakeId64, Ulid, Uuid, UuidCompact,
};

// =============================================================================
// Snowflake64 lifecycle
// =============================================================================

#[test]
fn snowflake64_lifecycle() {
    type Id = SnowflakeId64<42, 6, 16>;

    let mut id_gen: Snowflake64<42, 6, 16> = Snowflake64::new(7);

    // Generate
    let id: Id = id_gen.next_id(100).unwrap();

    // Extract fields
    assert_eq!(id.timestamp(), 100);
    assert_eq!(id.worker(), 7);
    assert_eq!(id.sequence(), 0);
    let (ts, wk, sq) = id.unpack();
    assert_eq!((ts, wk, sq), (100, 7, 0));

    // Integer round-trip via From
    let raw: u64 = id.into();
    let recovered = Id::from_raw(raw);
    assert_eq!(id, recovered);

    // String encodings
    let hex = id.to_hex();
    assert_eq!(hex.decode(), id.raw());
    assert_eq!(hex.as_str().len(), 16);

    let b62 = id.to_base62();
    assert_eq!(b62.decode(), id.raw());
    assert_eq!(b62.as_str().len(), 11);

    let b36 = id.to_base36();
    assert_eq!(b36.decode(), id.raw());
    assert_eq!(b36.as_str().len(), 13);

    // Parse back from string
    let hex_parsed: HexId64 = hex.as_str().parse().unwrap();
    assert_eq!(hex_parsed, hex);

    let b62_parsed: Base62Id = b62.as_str().parse().unwrap();
    assert_eq!(b62_parsed, b62);

    let b36_parsed: Base36Id = b36.as_str().parse().unwrap();
    assert_eq!(b36_parsed, b36);

    // Mix for hash tables
    let mixed: MixedId64<42, 6, 16> = id.mixed();
    let unmixed = mixed.unmix();
    assert_eq!(unmixed, id);
    let mixed_raw: u64 = mixed.into();
    assert_ne!(mixed_raw, raw); // mixed differs from raw

    // Use as HashMap key
    let mut map: HashMap<Id, &str> = HashMap::new();
    map.insert(id, "order_1");
    assert_eq!(map.get(&id), Some(&"order_1"));

    // Ordering
    let id2: Id = id_gen.next_id(100).unwrap();
    assert!(id2 > id); // same timestamp, higher sequence
    let id3: Id = id_gen.next_id(101).unwrap();
    assert!(id3 > id2); // higher timestamp
}

// =============================================================================
// UUID lifecycle
// =============================================================================

#[test]
fn uuid_v4_lifecycle() {
    use nexus_id::UuidV4;

    let mut id_gen = UuidV4::new(42);

    // Generate
    let id: Uuid = id_gen.next();

    // String access
    assert_eq!(id.as_str().len(), 36);
    assert_eq!(&id.as_str()[8..9], "-");
    assert_eq!(id.version(), 4);

    // Parse round-trip
    let parsed: Uuid = id.as_str().parse().unwrap();
    assert_eq!(parsed, id);

    // Bytes round-trip
    let bytes = id.to_bytes();
    assert_eq!(bytes.len(), 16);
    let from_bytes = Uuid::from_bytes(&bytes).unwrap();
    assert_eq!(from_bytes, id);

    // Unsafe bytes round-trip
    // SAFETY: bytes came from id.to_bytes(), so it encodes a valid Uuid.
    let from_unchecked = unsafe { Uuid::from_bytes_unchecked(&bytes) };
    assert_eq!(from_unchecked, id);

    // Raw round-trip
    let (hi, lo) = id.decode();
    let from_raw = Uuid::from_raw(hi, lo);
    assert_eq!(from_raw, id);

    // Compact conversion
    let compact: UuidCompact = id.into();
    let back: Uuid = compact.into();
    assert_eq!(back, id);

    // Use as HashMap key
    let mut map: HashMap<Uuid, u32> = HashMap::new();
    map.insert(id, 1);
    assert_eq!(map.get(&id), Some(&1));

    // Uniqueness
    let id2 = id_gen.next();
    assert_ne!(id, id2);
}

#[test]
fn uuid_v7_lifecycle() {
    use nexus_id::UuidV7;

    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut id_gen = UuidV7::new(epoch, unix_base, 42);

    // Generate
    let id: Uuid = id_gen.next(epoch).unwrap();

    assert_eq!(id.version(), 7);
    assert!(id.timestamp_ms().is_some());

    // Ordering (time-ordered)
    let id2: Uuid = id_gen.next(epoch).unwrap();
    assert!(id2 > id);

    // Bytes round-trip
    let bytes = id.to_bytes();
    let recovered = Uuid::from_bytes(&bytes).unwrap();
    assert_eq!(recovered, id);
}

// =============================================================================
// UuidCompact lifecycle
// =============================================================================

#[test]
fn uuid_compact_lifecycle() {
    use nexus_id::UuidV4;

    let mut id_gen = UuidV4::new(99);
    let uuid = id_gen.next();

    // Convert to compact
    let compact = uuid.to_compact();
    assert_eq!(compact.as_str().len(), 32);
    assert!(!compact.as_str().contains('-'));

    // Parse round-trip
    let parsed: UuidCompact = compact.as_str().parse().unwrap();
    assert_eq!(parsed, compact);

    // Bytes round-trip
    let bytes = compact.to_bytes();
    let from_bytes = UuidCompact::from_bytes(&bytes).unwrap();
    assert_eq!(from_bytes, compact);

    // Back to dashed
    let back = compact.to_dashed();
    assert_eq!(back, uuid);

    // Raw round-trip
    let (hi, lo) = compact.decode();
    let from_raw = UuidCompact::from_raw(hi, lo);
    assert_eq!(from_raw, compact);
}

// =============================================================================
// ULID lifecycle
// =============================================================================

#[test]
fn ulid_lifecycle() {
    use nexus_id::UlidGenerator;

    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut id_gen = UlidGenerator::new(epoch, unix_base, 42);

    // Generate
    let id: Ulid = id_gen.next(epoch);

    // String access
    assert_eq!(id.as_str().len(), 26);

    // Timestamp extraction
    let ts = id.timestamp_ms();
    assert!(ts >= unix_base); // should be at or after base

    // Random extraction
    let (rand_hi, rand_lo) = id.random();
    let _ = rand_hi;
    let _ = rand_lo;

    // Parse round-trip
    let parsed: Ulid = id.as_str().parse().unwrap();
    assert_eq!(parsed, id);

    // Bytes round-trip
    let bytes = id.to_bytes();
    assert_eq!(bytes.len(), 16);
    let from_bytes = Ulid::from_bytes(&bytes).unwrap();
    assert_eq!(from_bytes, id);

    // Unsafe bytes round-trip
    // SAFETY: bytes came from id.to_bytes(), so it encodes a valid Ulid.
    let from_unchecked = unsafe { Ulid::from_bytes_unchecked(&bytes) };
    assert_eq!(from_unchecked, id);

    // Raw round-trip
    let from_raw = Ulid::from_raw(ts, rand_hi, rand_lo);
    assert_eq!(from_raw, id);

    // Convert to UUID
    let uuid: Uuid = id.into();
    assert_eq!(uuid.version(), 7);

    // Ordering (time-ordered)
    let id2 = id_gen.next(epoch);
    assert!(id2 > id);

    // Use as HashMap key
    let mut map: HashMap<Ulid, &str> = HashMap::new();
    map.insert(id, "event_1");
    assert_eq!(map.get(&id), Some(&"event_1"));
}

// =============================================================================
// HexId64 lifecycle
// =============================================================================

#[test]
fn hex_id64_lifecycle() {
    let value: u64 = 0xDEAD_BEEF_CAFE_BABE;

    // Encode
    let id: HexId64 = HexId64::encode(value);
    assert_eq!(id.as_str(), "deadbeefcafebabe");
    assert_eq!(id.as_bytes(), b"deadbeefcafebabe");

    // Decode
    assert_eq!(id.decode(), value);

    // Parse round-trip
    let parsed: HexId64 = "deadbeefcafebabe".parse().unwrap();
    assert_eq!(parsed, id);

    // Case-insensitive parse
    let upper: HexId64 = "DEADBEEFCAFEBABE".parse().unwrap();
    assert_eq!(upper.decode(), value);

    // Display
    assert_eq!(format!("{}", id), "deadbeefcafebabe");

    // HashMap
    let mut map: HashMap<HexId64, u32> = HashMap::new();
    map.insert(id, 42);
    assert_eq!(map.get(&id), Some(&42));
}

// =============================================================================
// Base62Id lifecycle
// =============================================================================

#[test]
fn base62_lifecycle() {
    let value: u64 = 123_456_789_012;

    let id: Base62Id = Base62Id::encode(value);
    assert_eq!(id.as_str().len(), 11);

    // Decode round-trip
    assert_eq!(id.decode(), value);

    // Parse round-trip
    let parsed: Base62Id = id.as_str().parse().unwrap();
    assert_eq!(parsed, id);

    // Edge cases
    let zero: Base62Id = Base62Id::encode(0);
    assert_eq!(zero.decode(), 0);

    let max: Base62Id = Base62Id::encode(u64::MAX);
    assert_eq!(max.decode(), u64::MAX);
    let max_parsed: Base62Id = max.as_str().parse().unwrap();
    assert_eq!(max_parsed.decode(), u64::MAX);
}

// =============================================================================
// Base36Id lifecycle
// =============================================================================

#[test]
fn base36_lifecycle() {
    let value: u64 = 123_456_789_012;

    let id: Base36Id = Base36Id::encode(value);
    assert_eq!(id.as_str().len(), 13);

    // Decode round-trip
    assert_eq!(id.decode(), value);

    // Parse round-trip (case-insensitive)
    let parsed: Base36Id = id.as_str().parse().unwrap();
    assert_eq!(parsed, id);

    let upper = id.as_str().to_uppercase();
    let parsed_upper: Base36Id = upper.parse().unwrap();
    assert_eq!(parsed_upper.decode(), value);
}

// =============================================================================
// TypeId lifecycle
// =============================================================================

#[test]
fn typeid_lifecycle() {
    use nexus_id::{TypeId, UlidGenerator};

    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut id_gen = UlidGenerator::new(epoch, unix_base, 42);

    let ulid = id_gen.next(epoch);

    // Construct
    let id: TypeId<40> = TypeId::new("order", ulid).unwrap();
    assert_eq!(id.prefix(), "order");
    assert_eq!(id.suffix_str(), ulid.as_str());
    assert!(id.as_str().starts_with("order_"));

    // Timestamp extraction
    assert_eq!(id.timestamp_ms(), ulid.timestamp_ms());

    // Parse round-trip
    let parsed: TypeId<40> = id.as_str().parse().unwrap();
    assert_eq!(parsed, id);

    // Ordering (same prefix → ordered by suffix)
    let ulid2 = id_gen.next(epoch);
    let id2: TypeId<40> = TypeId::new("order", ulid2).unwrap();
    assert!(id2 > id);

    // HashMap
    let mut map: HashMap<TypeId<40>, u32> = HashMap::new();
    map.insert(id, 100);
    assert_eq!(map.get(&id), Some(&100));

    // Deref to str
    let s: &str = &id;
    assert!(s.starts_with("order_"));
}

// =============================================================================
// Cross-type conversions
// =============================================================================

#[test]
fn cross_type_conversions() {
    use nexus_id::UuidV4;

    let mut id_gen = UuidV4::new(77);
    let uuid = id_gen.next();

    // Uuid → UuidCompact → Uuid
    let compact: UuidCompact = uuid.into();
    let back: Uuid = compact.into();
    assert_eq!(back, uuid);

    // Uuid ↔ UuidCompact decode to same raw values
    assert_eq!(uuid.decode(), compact.decode());
    assert_eq!(uuid.to_bytes(), compact.to_bytes());
}

#[test]
fn ulid_to_uuid_conversion() {
    use nexus_id::UlidGenerator;

    let epoch = Instant::now();
    let unix_base = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let mut id_gen = UlidGenerator::new(epoch, unix_base, 42);

    let ulid = id_gen.next(epoch);
    let uuid: Uuid = ulid.into();

    // Version and variant set correctly
    assert_eq!(uuid.version(), 7);

    // Timestamp preserved
    assert_eq!(uuid.timestamp_ms(), Some(ulid.timestamp_ms()));
}

#[test]
fn snowflake_to_integer() {
    let id = SnowflakeId64::<42, 6, 16>::from_raw(12345);
    let raw: u64 = id.into();
    assert_eq!(raw, 12345);

    let mixed = id.mixed();
    let mixed_raw: u64 = mixed.into();
    assert_ne!(mixed_raw, 12345); // mixed value differs
}
