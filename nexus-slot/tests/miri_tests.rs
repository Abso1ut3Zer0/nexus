//! Miri tests for nexus-slot conflation slot.
//!
//! Run: `cargo +nightly miri test -p nexus-slot --test miri_tests`

use nexus_slot::spsc;

#[test]
fn write_and_read() {
    let (mut writer, mut reader) = spsc::slot::<u64>();
    writer.write(42);
    assert_eq!(reader.read(), Some(42));
}

#[test]
fn overwrite_conflation() {
    let (mut writer, mut reader) = spsc::slot::<u64>();

    writer.write(10);
    writer.write(20);
    writer.write(30);

    assert_eq!(reader.read(), Some(30));
}

#[test]
fn read_before_write_returns_none() {
    let (_writer, mut reader) = spsc::slot::<u64>();
    assert_eq!(reader.read(), None);
}
