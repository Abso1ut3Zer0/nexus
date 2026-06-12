pub struct StoredMsg {
    pub seq_num: u32,
    pub bytes: Vec<u8>,
}

pub trait MessageStore {
    type Error;

    fn store(&mut self, seq_num: u32, msg: &[u8]) -> Result<(), Self::Error>;

    /// Yield messages with sequence numbers in `[begin, end]`.
    /// `end = None` means all stored from `begin` onward.
    fn retrieve(
        &mut self,
        begin: u32,
        end: Option<u32>,
    ) -> impl Iterator<Item = Result<StoredMsg, Self::Error>> + '_;
}

pub trait SessionStore {
    type Error;

    fn save(&mut self, next_inbound: u32, next_outbound: u32) -> Result<(), Self::Error>;

    /// `None` on first startup — no prior state.
    fn load(&self) -> Result<Option<(u32, u32)>, Self::Error>;
}
