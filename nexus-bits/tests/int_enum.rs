use nexus_bits::IntEnum;

#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Exchange {
    Nasdaq = 0,
    Nyse = 1,
    Cboe = 2,
}

#[test]
fn into_repr() {
    assert_eq!(Exchange::Nasdaq.into_repr(), 0u8);
    assert_eq!(Exchange::Nyse.into_repr(), 1u8);
    assert_eq!(Exchange::Cboe.into_repr(), 2u8);
}

#[test]
fn try_from_repr_valid() {
    assert_eq!(Exchange::try_from_repr(0), Some(Exchange::Nasdaq));
    assert_eq!(Exchange::try_from_repr(1), Some(Exchange::Nyse));
    assert_eq!(Exchange::try_from_repr(2), Some(Exchange::Cboe));
}

#[test]
fn try_from_repr_invalid() {
    assert_eq!(Exchange::try_from_repr(3), None);
    assert_eq!(Exchange::try_from_repr(255), None);
}

#[test]
fn roundtrip() {
    for &e in &[Exchange::Nasdaq, Exchange::Nyse, Exchange::Cboe] {
        assert_eq!(Exchange::try_from_repr(e.into_repr()), Some(e));
    }
}

// Non-contiguous discriminants
#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Sparse {
    A = 0,
    B = 10,
    C = 200,
}

#[test]
fn sparse_roundtrip() {
    assert_eq!(Sparse::A.into_repr(), 0);
    assert_eq!(Sparse::B.into_repr(), 10);
    assert_eq!(Sparse::C.into_repr(), 200);

    assert_eq!(Sparse::try_from_repr(0), Some(Sparse::A));
    assert_eq!(Sparse::try_from_repr(10), Some(Sparse::B));
    assert_eq!(Sparse::try_from_repr(200), Some(Sparse::C));

    assert_eq!(Sparse::try_from_repr(1), None);
    assert_eq!(Sparse::try_from_repr(100), None);
}

// Signed repr
#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(i8)]
pub enum Signed {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

#[test]
fn signed_repr() {
    assert_eq!(Signed::Neg.into_repr(), -1i8);
    assert_eq!(Signed::Zero.into_repr(), 0i8);
    assert_eq!(Signed::Pos.into_repr(), 1i8);

    assert_eq!(Signed::try_from_repr(-1), Some(Signed::Neg));
    assert_eq!(Signed::try_from_repr(0), Some(Signed::Zero));
    assert_eq!(Signed::try_from_repr(1), Some(Signed::Pos));
    assert_eq!(Signed::try_from_repr(2), None);
}

// u16 repr
#[derive(IntEnum, Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum Wide {
    Small = 0,
    Large = 1000,
    Max = 65535,
}

#[test]
fn wide_repr() {
    assert_eq!(Wide::Small.into_repr(), 0u16);
    assert_eq!(Wide::Large.into_repr(), 1000u16);
    assert_eq!(Wide::Max.into_repr(), 65535u16);
}
