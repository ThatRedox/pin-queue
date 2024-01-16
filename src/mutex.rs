//! The mutex trait used by the queue.

use core::marker::PhantomData;

#[cfg(feature = "critical-section")]
pub use crate::mutex::critical_section::CriticalSectionMutex;

#[cfg(feature = "parking_lot")]
pub use crate::mutex::parking_lot::ParkingLotMutex;

/// The raw mutex trait.
///
/// # Safety
/// Implementations must ensure that, while locked, no other thread can lock concurrently. Mutexes may
/// be reentrant.
pub unsafe trait Mutex {
    fn lock<R>(&self, f: impl FnOnce() -> R) -> R;
}

/// A no-op mutex for single-threaded applications. It does not implement `Send` or `Sync` so
/// it cannot be sent between threads. If you need a thread-safe mutex, consider using the
/// `critical-section` or `parking_lot` features.
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
    fn test_noop_mutex() {
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
        fn test_critical_section_mutex() {
            let mutex = CriticalSectionMutex;
            let res = mutex.lock(|| 42);
            assert_eq!(res, 42);
        }
    }
}

#[cfg(feature = "parking_lot")]
mod parking_lot {
    use super::Mutex;

    /// A simple `Mutex` using `parking_lot::ReentrantMutex`
    pub struct ParkingLotMutex {
        inner: parking_lot::ReentrantMutex<()>,
    }
    unsafe impl Mutex for ParkingLotMutex {
        fn lock<R>(&self, f: impl FnOnce() -> R) -> R {
            let _guard = self.inner.lock();
            f()
        }
    }
    unsafe impl Send for ParkingLotMutex {}
    unsafe impl Sync for ParkingLotMutex {}
    impl ParkingLotMutex {
        pub const fn new() -> Self {
            Self {
                inner: parking_lot::ReentrantMutex::new(())
            }
        }
    }
    impl Default for ParkingLotMutex {
        fn default() -> Self { Self::new() }
    }

    #[cfg(test)]
    mod test {
        use crate::mutex::{ParkingLotMutex, Mutex};

        #[test]
        fn test_parking_lot_mutex() {
            let mutex = ParkingLotMutex::default();
            let res = mutex.lock(|| 42);
            assert_eq!(res, 42);
        }
    }
}
