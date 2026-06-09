use std::fmt;

use crate::error::ShmError;

#[derive(Debug)]
#[non_exhaustive]
pub enum JournalError {
    RecordTooLarge { frame: usize, capacity: usize },
    EmptyRecord,
    Shm(ShmError),
    Os(std::io::Error),
}

impl fmt::Display for JournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RecordTooLarge { frame, capacity } => {
                write!(
                    f,
                    "record frame {frame} exceeds segment capacity {capacity}"
                )
            }
            Self::EmptyRecord => write!(f, "empty record"),
            Self::Shm(e) => write!(f, "{e}"),
            Self::Os(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for JournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Shm(e) => Some(e),
            Self::Os(e) => Some(e),
            _ => None,
        }
    }
}

impl From<ShmError> for JournalError {
    fn from(e: ShmError) -> Self {
        Self::Shm(e)
    }
}

impl From<std::io::Error> for JournalError {
    fn from(e: std::io::Error) -> Self {
        Self::Os(e)
    }
}

impl From<nexus_platform::MapError> for JournalError {
    fn from(e: nexus_platform::MapError) -> Self {
        Self::Shm(ShmError::from(e))
    }
}
