//! A doubly linked list deque with pinned nodes.
//!
//! It is often useful to have an unbounded queue in an environment without dynamic memory
//! allocation. This queue works by having each node be pinned to a fixed location in memory,
//! where it can then be attached to a queue. Memory safety is achieved by using lifetimes to
//! ensure the queue lives longer than it's nodes, and ensuring that if a node is dropped, it's
//! safely detached from the queue.
//!
//! # Example
//! ```
//! use pin_queue::mutex::CriticalSectionMutex;
//! use pin_queue::Deque;
//! use core::pin::pin;
//!
//! // Create a new queue of `u32`, using the `CriticalSectionMutex` mutex.
//! let queue = Deque::<CriticalSectionMutex, u32>::new(CriticalSectionMutex::new());
//! {
//!     // Create a node, and pin it to the stack.
//!     let mut node = pin!(queue.new_node(1));
//!     // Push the node onto the queue.
//!     queue.push_back(node.as_mut()).unwrap();
//!     // Pop our node off the queue.
//!     assert_eq!(queue.pop_front_copy().unwrap(), 1);
//!     // Push our node back onto the queue.
//!     queue.push_back(node.as_mut()).unwrap();
//! } // Node gets dropped and automatically removed from the queue
//! assert!(queue.is_empty());
//! ```
//!
//! # Note: The queue must live longer than it's nodes
//! ``` compile_fail
//! use pin_queue::mutex::CriticalSectionMutex;
//! use pin_queue::Deque;
//!
//! let queue = Deque::<CriticalSectionMutex, u32>::default();
//! let node = queue.new_node(1);
//! drop(queue);
//! ```
//! This fails to compile with a message like:
//! ``` text
//! error[E0505]: cannot move out of `queue` because it is borrowed
//!   --> src\queue.rs:37:6
//!    |
//! 8  | let node = queue.new_node(1);
//!    |            ----------------- borrow of `queue` occurs here
//! 9  | drop(queue);
//!    |      ^^^^^ move out of `queue` occurs here
//! 10 | } _doctest_main_src_queue_rs_31_0() }
//!    | - borrow might be used here, when `node` is dropped and runs the `Drop` code for type `QueueNode`
// ```
//!

use core::cell::UnsafeCell;
use core::marker::PhantomPinned;
use core::pin::Pin;
use crate::mutex::Mutex;
use crate::error::{Error, Result};

/// The root of the doubly-linked list queue.
pub struct Deque<M: Mutex, T> {
    mutex: M,
    inner: UnsafeCell<DequeInner<T>>,
}

unsafe impl <M: Mutex, T> Send for Deque<M, T> where M: Send, T: Send {}
unsafe impl <M: Mutex, T> Sync for Deque<M, T> where M: Sync, T: Send {}

struct DequeInner<T> {
    size: usize,
    head: *mut NodeInner<T>,
    tail: *mut NodeInner<T>,
}

impl <M: Mutex, T> Default for Deque<M, T> where M: Default {
    fn default() -> Self { Self::new(M::default()) }
}

impl <M: Mutex, T> Deque<M, T> {
    pub const fn new(mutex: M) -> Self {
        Self {
            mutex, inner: UnsafeCell::new(DequeInner {
                size: 0,
                head: core::ptr::null_mut(),
                tail: core::ptr::null_mut(),
            }),
        }
    }

    fn do_push<'a>(&'a self, mut node: Pin<&mut DequeNode<'a, M, T>>, push: impl FnOnce(Pin<&mut NodeInner<T>>)) -> Result<()> {
        if !core::ptr::eq(node.as_ref().queue, self) {
            return Err(Error::Attached);
        }
        self.mutex.lock(||
            if node.attached() {
                Err(Error::Attached)
            } else {
                push(node.as_mut().get_inner());
                Ok(())
            }
        )
    }

    /// Push a node onto the front of the queue.
    pub fn push_front<'a>(&'a self, node: Pin<&mut DequeNode<'a, M, T>>) -> Result<()> {
        self.do_push(node, |n| unsafe { n.push_front(self) })
    }

    /// Push a node onto the back of the queue.
    pub fn push_back<'a>(&'a self, node: Pin<&mut DequeNode<'a, M, T>>) -> Result<()> {
        self.do_push(node, |n| unsafe { n.push_back(self) })
    }

    /// Pop a node from the front of the queue and call `f` on it. This will return `None` if the
    /// queue was empty, and `Some(R)` if the queue was not empty, where `R` is the return value
    /// of `f`. Note that this will lock the queue for the duration of the call to `f`.
    ///
    /// * If `T` is Copy, consider [Deque::pop_front_copy] instead.
    /// * If `T` is Clone, consider [Deque::pop_front_clone] instead.
    /// * If your queue is of `Option<T>` consider [Deque::take_front] instead.
    pub fn pop_front<R>(&self, f: impl FnOnce(&mut T) -> R) -> Option<R> {
        self.mutex.lock(|| {
            // Safety: inner is always valid
            let inner = unsafe { self.inner.get().as_mut().unwrap() };
            if inner.head.is_null() {
                None
            } else {
                let mut node = unsafe { Pin::new_unchecked(&mut *inner.head) };
                unsafe { node.as_mut().detach(self) }
                Some(f(unsafe { node.get_value() }))
            }
        })
    }

    /// Pop a node from the back of the queue and call `f` on it. This will return `None` if the
    /// queue was empty, and `Some(R)` if the queue was not empty, where `R` is the return value
    /// of `f`. Note that this will lock the queue for the duration of the call to `f`.
    ///
    /// * If `T` is Copy, consider [Deque::pop_back_copy] instead.
    /// * If `T` is Clone, consider [Deque::pop_back_clone] instead.
    /// * If your queue is of `Option<T>` consider [Deque::take_back] instead.
    pub fn pop_back<R>(&self, f: impl FnOnce(&mut T) -> R) -> Option<R> {
        self.mutex.lock(|| {
            // Safety: inner is always valid
            let inner = unsafe { self.inner.get().as_mut().unwrap() };
            if inner.tail.is_null() {
                None
            } else {
                let mut node = unsafe { Pin::new_unchecked(&mut *inner.tail) };
                unsafe { node.as_mut().detach(self) }
                Some(f(unsafe { node.get_value() }))
            }
        })
    }

    /// Get the length of the queue. This may not be accurate if the queue is being concurrently
    /// modified.
    pub fn len(&self) -> usize {
        self.mutex.lock(|| {
            // Safety: inner is always valid
            unsafe { self.inner.get().as_ref().unwrap().size }
        })
    }

    /// Check if the queue is empty. This may not be accurate if the queue is being concurrently
    /// modified.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Create a node ready to be pinned and attached to this queue.
    #[must_use = "Node should be pinned and attached to the queue."]
    pub fn new_node(&self, value: T) -> DequeNode<'_, M, T> {
        DequeNode::new(self, value)
    }
}

impl <M: Mutex, T> Deque<M, T> where T: Copy {
    /// Pop a node from the front of the queue.
    pub fn pop_front_copy(&self) -> Option<T> {
        self.pop_front(|v| *v)
    }
    /// Pop a node from the back of the queue.
    pub fn pop_back_copy(&self) -> Option<T> {
        self.pop_back(|v| *v)
    }
}

impl <M: Mutex, T> Deque<M, T> where T: Clone {
    /// Pop a node from the front of the queue and clone its value.
    pub fn pop_front_clone(&self) -> Option<T> {
        self.pop_front(|v| v.clone())
    }
    /// Pop a node from the back of the queue and clone its value.
    pub fn pop_back_clone(&self) -> Option<T> {
        self.pop_back(|v| v.clone())
    }
}

impl <M: Mutex, T> Deque<M, Option<T>> {
    /// Pop a node from the front of the queue and take its value replacing it with `None`.
    pub fn take_front(&self) -> Option<Option<T>> {
        self.pop_front(|v| v.take())
    }
    /// Pop a node from the back of the queue and take its value replacing it with `None`.
    pub fn take_back(&self) -> Option<Option<T>> {
        self.pop_back(|v| v.take())
    }
}

/// An individual node in a queue. To create a node, see [Deque::new_node].
pub struct DequeNode<'a, M: Mutex, T> {
    queue: &'a Deque<M, T>,
    inner: NodeInner<T>,
}

impl <'a, M: Mutex, T> DequeNode<'a, M, T> {
    fn new(queue: &'a Deque<M, T>, value: T) -> DequeNode<'a, M, T> {
        Self {
            queue,
            inner: NodeInner {
                value, attached: false,
                next: core::ptr::null_mut(),
                prev: core::ptr::null_mut(),
                _pin: PhantomPinned,
            }
        }
    }

    fn get_inner(self: Pin<&mut Self>) -> Pin<&mut NodeInner<T>> {
        // Safety: `inner` is pinned when `self` is pinned
        unsafe { self.map_unchecked_mut(|s| &mut s.inner) }
    }

    /// Return true if this node is currently in a queue.
    pub fn attached(&self) -> bool {
        self.inner.attached
    }

    /// Detach this node from any queue it is in. This makes no changes if the node is not in a queue.
    pub fn detach(mut self: Pin<&mut Self>) {
        self.queue.mutex.lock(|| {
            if self.attached() {
                let queue = self.queue;
                unsafe { self.as_mut().get_inner().detach(queue) }
            }
        });
    }

    /// Replace the value of this node with a new value and return the old value. This operates
    /// on a node that has not been pinned.
    pub fn replace(&mut self, value: T) -> T {
        core::mem::replace(&mut self.inner.value, value)
    }

    /// Replace the value of this node with a new value and return the old value. This operates
    /// on a node that has been pinned.
    pub fn replace_pin(self: Pin<&mut Self>, value: T) -> T {
        self.mutate(|v| core::mem::replace(v, value))
    }

    /// Mutate the value of this node in-place. This locks the queue and calls `f` with a
    /// mutable reference to the value of this node and returns the result.
    ///
    /// * If you want to replace the value inside this node, consider using [DequeNode::replace_pin] instead.
    /// * If you want the value and `T` implements `Copy`, consider using [DequeNode::value] instead.
    /// * If you want the value and `T` implements `Clone`, consider using [DequeNode::value_clone] instead.
    pub fn mutate<R>(mut self: Pin<&mut Self>, f: impl FnOnce(&mut T) -> R) -> R {
        self.queue.mutex.lock(|| {
            f(unsafe { self.as_mut().get_inner().get_value() })
        })
    }
}

impl <'a, M: Mutex, T> Drop for DequeNode<'a, M, T> {
    fn drop(&mut self) {
        // Safety: We know we are never using this value again after being dropped
        unsafe { Pin::new_unchecked(self) }.detach();
    }
}

impl <'a, M: Mutex, T> DequeNode<'a, M, T> where T: Copy {
    /// Get a copy of the value inside this node.
    pub fn value(self: Pin<&mut Self>) -> T {
        self.mutate(|v| *v)
    }
}

impl <'a, M: Mutex, T> DequeNode<'a, M, T> where T: Clone {
    /// Get a clone of the value inside this node.
    pub fn value_clone(self: Pin<&mut Self>) -> T {
        self.mutate(|v| v.clone())
    }
}

/// This struct does all the magic required for the queue to work. This represents a single
/// element on the queue.
struct NodeInner<T> {
    value: T,
    attached: bool,
    next: *mut NodeInner<T>,
    prev: *mut NodeInner<T>,
    _pin: PhantomPinned,
}

impl <T> NodeInner<T> {
    /// Attach this node to the end of a queue. The node MUST not be attached to another queue.
    /// The queue mutex MUST be locked before calling.
    pub unsafe fn push_back<M: Mutex>(mut self: Pin<&mut NodeInner<T>>, queue: &Deque<M, T>) {
        let self_ref = self.as_mut().get_unchecked_mut();
        self_ref.attached = true;

        let inner = queue.inner.get().as_mut().unwrap();
        inner.size += 1;

        self_ref.next = core::ptr::null_mut();

        if let Some(tail) = inner.tail.as_mut() {
            tail.next = self_ref;
            self_ref.prev = tail;
        } else {
            inner.head = self_ref;
            self_ref.prev = core::ptr::null_mut();
        }
        inner.tail = self_ref;
    }

    /// Attach this node to the front of a queue. The node MUST not be attached to another queue.
    /// The queue mutex MUST be locked before calling.
    pub unsafe fn push_front<M: Mutex>(mut self: Pin<&mut NodeInner<T>>, queue: &Deque<M, T>) {
        let self_ref = self.as_mut().get_unchecked_mut();
        self_ref.attached = true;

        let inner = queue.inner.get().as_mut().unwrap();
        inner.size += 1;

        self_ref.prev = core::ptr::null_mut();

        if let Some(head) = inner.head.as_mut() {
            head.prev = self_ref;
            self_ref.next = head;
        } else {
            inner.tail = self_ref;
            self_ref.next = core::ptr::null_mut();
        }
        inner.head = self_ref;
    }

    /// Detach this struct from a queue. The queue mutex MUST be locked before calling.
    pub unsafe fn detach<M: Mutex>(mut self: Pin<&mut NodeInner<T>>, queue: &Deque<M, T>) {
        let self_ref = self.as_mut().get_unchecked_mut();
        let inner = queue.inner.get().as_mut().unwrap();
        inner.size -= 1;

        if let Some(next) = self_ref.next.as_mut() {
            // Another node after this one
            next.prev = self_ref.prev;
        } else if core::ptr::eq(inner.tail, self_ref) {
            // We are the tail
            inner.tail = self_ref.prev;
        }

        if let Some(prev) = self_ref.prev.as_mut() {
            // Another node before this one
            prev.next = self_ref.next;
        } else if core::ptr::eq(inner.head, self_ref) {
            // We are the head
            inner.head = self_ref.next;
        }

        self_ref.next = core::ptr::null_mut();
        self_ref.prev = core::ptr::null_mut();
        self_ref.attached = false;
    }

    /// There must be exclusive access to the node before calling. If attached to a queue,
    /// the queue mutex MUST be locked before calling.
    pub unsafe fn get_value(self: Pin<&mut NodeInner<T>>) -> &mut T {
        // Safety: `value` is never considered pinned.
        unsafe { &mut self.get_unchecked_mut().value }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use core::pin::pin;
    use crate::mutex::NoopMutex;

    extern crate std;
    use std::prelude::rust_2021::*;

    #[test]
    fn queue_smoke() {
        let queue: Deque<NoopMutex, u32> = Default::default();
        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());

        {
            let mut node = pin!(queue.new_node(1));
            queue.push_back(node.as_mut()).unwrap();
            assert_eq!(queue.push_front(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue.push_back(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue.len(), 1);
            assert!(!queue.is_empty());

            let mut node = pin!(queue.new_node(2));
            queue.push_back(node.as_mut()).unwrap();
            assert_eq!(queue.push_front(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue.push_back(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue.len(), 2);

            let mut node = pin!(queue.new_node(3));
            queue.push_front(node.as_mut()).unwrap();
            assert_eq!(queue.push_front(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue.push_back(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue.len(), 3);

            assert_eq!(queue.pop_back_copy().unwrap(), 2);
            assert_eq!(queue.len(), 2);

            assert_eq!(queue.pop_front_copy().unwrap(), 3);
            assert_eq!(queue.len(), 1);

            assert_eq!(queue.pop_front_copy().unwrap(), 1);
            assert_eq!(queue.len(), 0);
            assert!(queue.is_empty());

            assert_eq!(queue.pop_front_clone(), None);
            assert_eq!(queue.pop_back_clone(), None);
        }
        assert!(queue.is_empty());
    }

    #[test]
    fn queue_drop() {
        let queue: Deque<NoopMutex, u32> = Default::default();
        assert!(queue.is_empty());

        {
            let mut node = pin!(queue.new_node(1));
            queue.push_back(node.as_mut()).unwrap();
            assert_eq!(queue.len(), 1);

            let mut node = pin!(queue.new_node(2));
            queue.push_back(node.as_mut()).unwrap();
            assert_eq!(queue.len(), 2);

            let mut node = pin!(queue.new_node(3));
            queue.push_front(node.as_mut()).unwrap();
            assert_eq!(queue.len(), 3);
        }
        assert!(queue.is_empty());
    }

    #[test]
    fn queue_many() {
        // Miri is too slow to run 1 items
        #[cfg(miri)]
        const TEST_COUNT: u32 = 1_000;
        #[cfg(not(miri))]
        const TEST_COUNT: u32 = 1_000_000;

        let queue: Deque<NoopMutex, u32> = Default::default();
        assert!(queue.is_empty());

        let mut nodes = Vec::new();
        for i in 0..TEST_COUNT {
            let mut node = Box::pin(queue.new_node(i));
            queue.push_back(node.as_mut()).unwrap();
            nodes.push(node);
        }

        assert_eq!(queue.len(), TEST_COUNT as usize);
        for i in 0..TEST_COUNT {
            let v = queue.pop_front_copy().unwrap();
            assert_eq!(v, i);
        }

        assert!(queue.is_empty());
        for node in nodes.iter_mut() {
            queue.push_front(node.as_mut()).unwrap();
        }

        assert_eq!(queue.len(), TEST_COUNT as usize);
        drop(nodes);
        assert!(queue.is_empty());
    }

    #[test]
    fn queue_error() {
        let queue1: Deque<NoopMutex, u32> = Default::default();
        let queue2: Deque<NoopMutex, u32> = Default::default();

        {
            let mut node = pin!(queue1.new_node(1));
            assert_eq!(queue2.push_back(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue2.push_front(node.as_mut()), Err(Error::Attached));

            queue1.push_back(node.as_mut()).unwrap();

            assert_eq!(queue1.push_back(node.as_mut()), Err(Error::Attached));
            assert_eq!(queue1.push_front(node.as_mut()), Err(Error::Attached));
        }
    }

    #[test]
    fn queue_option() {
        let queue: Deque<NoopMutex, Option<u32>> = Default::default();

        {
            let mut node = queue.new_node(Some(0));
            assert_eq!(node.replace(Some(1)), Some(0));
            let mut node = pin!(node);

            queue.push_back(node.as_mut()).unwrap();
            assert_eq!(queue.len(), 1);
            assert_eq!(queue.take_front(), Some(Some(1)));
            assert_eq!(queue.len(), 0);
            assert_eq!(node.as_mut().value(), None);
            assert_eq!(node.as_mut().value_clone(), None);

            assert_eq!(node.as_mut().replace_pin(Some(2)), None);

            queue.push_back(node.as_mut()).unwrap();
            assert_eq!(queue.len(), 1);
            assert_eq!(queue.take_back(), Some(Some(2)));
            assert_eq!(queue.len(), 0);
            assert_eq!(node.as_mut().value(), None);
        }
    }
}
