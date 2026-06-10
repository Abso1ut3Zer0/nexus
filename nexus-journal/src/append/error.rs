use std::fmt;

#[derive(Debug)]
#[non_exhaustive]
pub enum AppendOnlyJournalError {
    RecordTooLarge { frame: usize, capacity: usize },
    EmptyRecord,
    Map(nexus_platform::MapError),
    Io(std::io::Error),
}

impl fmt::Display for AppendOnlyJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RecordTooLarge { frame, capacity } => {
                write!(
                    f,
                    "record frame {frame} exceeds segment capacity {capacity}"
                )
            }
            Self::EmptyRecord => write!(f, "empty record"),
            Self::Map(e) => write!(f, "{e}"),
            Self::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for AppendOnlyJournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Map(e) => Some(e),
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<nexus_platform::MapError> for AppendOnlyJournalError {
    fn from(e: nexus_platform::MapError) -> Self {
        Self::Map(e)
    }
}

impl From<std::io::Error> for AppendOnlyJournalError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}
