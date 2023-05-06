pub type Result<T> = core::result::Result<T, Error>;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// Cannot attach a node that is already attached.
    Attached,
}

#[cfg(test)]
mod test {
    extern crate std;
    use std::format;
    use super::*;

    #[test]
    fn test_error() {
        // Just for the coverage goblins
        assert_eq!(Error::Attached, Error::Attached);
        assert_eq!(Error::Attached.clone(), Error::Attached);
        let _ = format!("{:?}", Error::Attached);
    }
}
