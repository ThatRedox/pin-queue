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

    #[cfg(test)]
    mod test {
        use critical_section::RawRestoreState;
        use crate::mutex::{CriticalSectionMutex, Mutex};

        /// No-op implementation of critical section so the test can run
        struct TestCS;
        critical_section::set_impl!(TestCS);
        unsafe impl critical_section::Impl for TestCS {
            unsafe fn acquire() -> RawRestoreState {
            }
            unsafe fn release(_restore_state: RawRestoreState) {
            }
        }

        #[test]
        fn test_mutex() {
            let mutex = CriticalSectionMutex::default();
            let res = mutex.lock(|| 42);
            assert_eq!(res, 42);
        }
    }
}
#[cfg(feature = "critical-section")]
pub use crate::mutex::critical_section::CriticalSectionMutex;