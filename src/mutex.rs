//! The mutex trait used by the queue.

/// The raw mutex trait.
///
/// # Safety
/// This is declared as `unsafe` since the `lock` function must call the passed function in a
/// critical section.
pub unsafe trait Mutex {
    fn lock<R>(&self, f: impl FnOnce() -> R) -> R;
}

#[cfg(feature = "critical-section")]
mod critical_section {
    use super::Mutex;

    /// A simple `Mutex` implementation using `critical_section`
    pub struct CriticalSectionMutex;
    unsafe impl Mutex for CriticalSectionMutex {
        fn lock<R>(&self, f: impl FnOnce() -> R) -> R {
            critical_section::with(|_| f())
        }
    }
    unsafe impl Send for CriticalSectionMutex {}
    unsafe impl Sync for CriticalSectionMutex {}
    impl CriticalSectionMutex {
        pub const fn new() -> Self { Self }
    }
    impl Default for CriticalSectionMutex {
        fn default() -> Self { Self::new() }
    }
}
#[cfg(feature = "critical-section")]
pub use crate::mutex::critical_section::CriticalSectionMutex;
