use std::fmt;

#[derive(Debug)]
#[non_exhaustive]
pub enum ShmError {
    BadMagic { found: u32 },
    UnsupportedLayout { found: u16, expected: u16 },
    EmptySegment,
    SizeOverflow,
    MappingTooSmall { required: usize, actual: usize },
    HugePagesUnavailable(std::io::Error),
    OwnerActive,
    Os(std::io::Error),
}

impl fmt::Display for ShmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadMagic { found } => write!(f, "not a nexus-shm segment (magic {found:#010x})"),
            Self::UnsupportedLayout { found, expected } => {
                write!(f, "unsupported layout version {found}, expected {expected}")
            }
            Self::EmptySegment => write!(f, "segment has zero data length"),
            Self::SizeOverflow => write!(f, "segment size overflows usize"),
            Self::MappingTooSmall { required, actual } => {
                write!(f, "mapping too small: need {required} bytes, got {actual}")
            }
            Self::HugePagesUnavailable(e) => write!(f, "huge pages unavailable: {e}"),
            Self::OwnerActive => write!(f, "segment already owned by a live process"),
            Self::Os(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for ShmError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::HugePagesUnavailable(e) | Self::Os(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for ShmError {
    fn from(e: std::io::Error) -> Self {
        Self::Os(e)
    }
}

impl From<nexus_platform::MapError> for ShmError {
    fn from(e: nexus_platform::MapError) -> Self {
        match e {
            nexus_platform::MapError::Io(e) => Self::Os(e),
            nexus_platform::MapError::EmptyFile => Self::EmptySegment,
            nexus_platform::MapError::OutOfBounds => Self::SizeOverflow,
            nexus_platform::MapError::HugePagesUnavailable(e) => Self::HugePagesUnavailable(e),
        }
    }
}
