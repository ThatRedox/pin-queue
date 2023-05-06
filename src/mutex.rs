//! The mutex trait used by the queue.

/// The raw mutex trait.
///
/// # Safety
/// This is declared as `unsafe` since the `lock` function must call the passed function in a
/// critical section.
pub unsafe trait Mutex {
    fn lock<R>(&self, f: impl FnOnce() -> R) -> R;
}

/// A no-op mutex for single-threaded applications. It does not implement `Send` or `Sync` so
/// it cannot be sent between threads. If you need a thread-safe mutex, consider using the
/// `critical-section` feature.
///
/// ``` compile_fail
/// use pin_queue::mutex::NoopMutex;
///
/// let mutex = NoopMutex::default();
/// std::thread::spawn(move || {
///     // Should not be able to send the mutex across threads
///     let m = mutex;
/// });
/// ```
pub struct NoopMutex {
    /// This field is here to make sure `NoopMutex` does not implement `Send` and `Sync`.
    phantom: PhantomData<*mut NoopMutex>
}
unsafe impl Mutex for NoopMutex {
    fn lock<R>(&self, f: impl FnOnce() -> R) -> R { f() }
}
impl NoopMutex {
    pub const fn new() -> Self { Self { phantom: PhantomData } }
}
impl Default for NoopMutex {
    fn default() -> Self { Self::new() }
}

#[cfg(test)]
mod test {
    use crate::mutex::{NoopMutex, Mutex};

    #[test]
    fn test_mutex() {
        let mutex = NoopMutex::default();
        let res = mutex.lock(|| 42);
        assert_eq!(res, 42);
    }
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
        use crate::mutex::{CriticalSectionMutex, Mutex};

        #[test]
        fn test_mutex() {
            let mutex = CriticalSectionMutex::default();
            let res = mutex.lock(|| 42);
            assert_eq!(res, 42);
        }
    }
}

use core::marker::PhantomData;
#[cfg(feature = "critical-section")]
pub use crate::mutex::critical_section::CriticalSectionMutex;
