use std::fmt;

use crate::error::ShmError;

/// Errors from opening, recovering, or configuring a [`SegmentedLog`](super::SegmentedLog).
///
/// Returned by [`SegmentedLogBuilder::open`](super::SegmentedLogBuilder::open),
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
    Shm(ShmError),
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
            Self::Shm(e) => write!(f, "{e}"),
            Self::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for OpenError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Shm(e) => Some(e),
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<ShmError> for OpenError {
    fn from(e: ShmError) -> Self {
        Self::Shm(e)
    }
}

impl From<std::io::Error> for OpenError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<nexus_platform::MapError> for OpenError {
    fn from(e: nexus_platform::MapError) -> Self {
        Self::Shm(ShmError::from(e))
    }
}

/// Errors from live [`SegmentedLog`](super::SegmentedLog) operations.
///
/// Returned by [`append`](super::SegmentedLog::append) and internal
/// rotation.
#[derive(Debug)]
#[non_exhaustive]
pub enum LogError {
    RecordTooLarge { max: usize },
    StandbyNotReady,
}

impl fmt::Display for LogError {
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

impl std::error::Error for LogError {}
