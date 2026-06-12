use std::path::{Path, PathBuf};

use nexus_journal::{
    AppendOnlyJournal, AppendOnlyJournalConfig, AppendOnlyJournalError, FixHeader, Reader, Writer,
};

use crate::store::{MessageStore, SessionStore, StoredMsg};

pub struct JournalMessageStore {
    writer: Writer<FixHeader>,
    reader: Reader<FixHeader>,
}

impl JournalMessageStore {
    pub fn open(
        path: impl AsRef<Path>,
        cfg: AppendOnlyJournalConfig,
    ) -> Result<Self, AppendOnlyJournalError> {
        let (writer, reader) = AppendOnlyJournal::<FixHeader>::open(path, cfg)?;
        Ok(Self { writer, reader })
    }
}

impl MessageStore for JournalMessageStore {
    type Error = AppendOnlyJournalError;

    fn store(&mut self, seq_num: u32, msg: &[u8]) -> Result<(), Self::Error> {
        let header = FixHeader {
            seq: seq_num as u64,
            timestamp: 0,
        };
        let mut claim = self.writer.try_claim(header, msg.len())?;
        claim.as_mut_slice().copy_from_slice(msg);
        claim.commit();
        Ok(())
    }

    fn retrieve(
        &mut self,
        begin: u32,
        end: Option<u32>,
    ) -> impl Iterator<Item = Result<StoredMsg, Self::Error>> + '_ {
        let hi = end.map_or(u64::MAX, |e| e as u64);
        match self.reader.read_range(begin as u64..=hi) {
            Err(e) => vec![Err(e)].into_iter(),
            Ok(range) => range
                .map(|rec| {
                    Ok(StoredMsg {
                        seq_num: rec.header().seq as u32,
                        bytes: rec.payload().to_vec(),
                    })
                })
                .collect::<Vec<_>>()
                .into_iter(),
        }
    }
}

pub struct FileSessionStore {
    path: PathBuf,
}

impl FileSessionStore {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
        }
    }
}

impl SessionStore for FileSessionStore {
    type Error = std::io::Error;

    fn save(&mut self, next_inbound: u32, next_outbound: u32) -> Result<(), Self::Error> {
        let mut buf = [0u8; 8];
        buf[..4].copy_from_slice(&next_inbound.to_le_bytes());
        buf[4..].copy_from_slice(&next_outbound.to_le_bytes());
        std::fs::write(&self.path, buf)
    }

    fn load(&self) -> Result<Option<(u32, u32)>, Self::Error> {
        match std::fs::read(&self.path) {
            Ok(b) if b.len() == 8 => {
                let inbound = u32::from_le_bytes(b[..4].try_into().unwrap());
                let outbound = u32::from_le_bytes(b[4..].try_into().unwrap());
                Ok(Some((inbound, outbound)))
            }
            Ok(_) => Ok(None),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e),
        }
    }
}
