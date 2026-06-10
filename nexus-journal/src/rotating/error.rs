use std::fmt;

/// Errors from opening, recovering, or configuring a [`RotatingJournal`](super::RotatingJournal).
///
/// Returned by [`RotatingJournalBuilder::open`](super::RotatingJournalBuilder::open),
/// [`Conductor::open`](super::Conductor::open), and related setup methods.
#[derive(Debug)]
#[non_exhaustive]
pub enum OpenError {
    ConfigMismatch {
        field: &'static str,
        expected: u64,
        found: u64,
    },
    SessionInUse {
        session_id: u32,
    },
    SessionNotFound {
        session_id: u32,
    },
    SegmentTooLarge {
        size: usize,
    },
    BadMagic {
        found: u32,
    },
    UnsupportedLayout {
        found: u16,
        expected: u16,
    },
    Map(nexus_platform::MapError),
    Io(std::io::Error),
}

impl fmt::Display for OpenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ConfigMismatch {
                field,
                expected,
                found,
            } => {
                write!(
                    f,
                    "manifest {field} mismatch: expected {expected}, found {found}"
                )
            }
            Self::SessionInUse { session_id } => {
                write!(f, "session {session_id} is already open")
            }
            Self::SessionNotFound { session_id } => {
                write!(f, "no manifest found for session {session_id}")
            }
            Self::SegmentTooLarge { size } => {
                write!(
                    f,
                    "segment size {size} exceeds u32::MAX (LogOffset packs \
                     local offsets into 32 bits)"
                )
            }
            Self::BadMagic { found } => {
                write!(f, "not a nexus journal manifest (magic {found:#010x})")
            }
            Self::UnsupportedLayout { found, expected } => {
                write!(f, "unsupported layout version {found}, expected {expected}")
            }
            Self::Map(e) => write!(f, "{e}"),
            Self::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for OpenError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Map(e) => Some(e),
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for OpenError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<nexus_platform::MapError> for OpenError {
    fn from(e: nexus_platform::MapError) -> Self {
        Self::Map(e)
    }
}

/// Errors from live [`RotatingJournal`](super::RotatingJournal) operations.
///
/// Returned by [`append`](super::RotatingJournal::append) and internal
/// rotation.
#[derive(Debug)]
#[non_exhaustive]
pub enum WriteError {
    RecordTooLarge { max: usize },
    StandbyNotReady,
}

impl fmt::Display for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RecordTooLarge { max } => {
                write!(f, "payload exceeds segment capacity ({max} bytes max)")
            }
            Self::StandbyNotReady => {
                write!(f, "conductor has not finished cleaning the standby segment")
            }
        }
    }
}

impl std::error::Error for WriteError {}
