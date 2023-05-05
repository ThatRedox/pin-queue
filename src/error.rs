pub type Result<T> = core::result::Result<T, Error>;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// Cannot attach a node that is already attached.
    Attached,
}
