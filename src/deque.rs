//! A doubly linked list deque with pinned nodes.
//!
//! It is often useful to have an unbounded queue in an environment without dynamic memory
//! allocation. This queue works by having each node be pinned to a fixed location in memory,
//! where it can then be attached to a queue. Memory safety is achieved by using lifetimes to
//! ensure the queue lives longer than it's nodes, and ensuring that if a node is dropped, it's
//! safely detached from the queue.
//!

use core::cell::RefCell;
use core::marker::{PhantomPinned, PhantomData};
use core::pin::Pin;
use crate::mutex::Mutex;
use crate::error::{Result, Error};

pub enum Side {
    Front,
    Back,
}

/// A cursor of a deque
pub struct Cursor<'a, 'b, M: Mutex, T> {
    queue: &'a Deque<M, T>,
    inner: &'a mut DequeInner<T>,
    prev: *const NodeInner<T>,
    next: *const NodeInner<T>,
    _phantom: PhantomData<&'b M>,
}

impl <'a, 'b, M: Mutex, T> Cursor<'a, 'b, M, T> {
    unsafe fn new_front(deque: &'a Deque<M, T>, inner: &'a mut DequeInner<T>) -> Cursor<'a, 'b, M, T> {
        Self {
            prev: core::ptr::null(),
            next: inner.head,
            inner, queue: deque,
            _phantom: PhantomData,
        }
    }
    
    unsafe fn new_back(deque: &'a Deque<M, T>, inner: &'a mut DequeInner<T>) -> Cursor<'a, 'b, M, T> {
        Self {
            prev: inner.tail,
            next: core::ptr::null(),
            inner, queue: deque,
            _phantom: PhantomData,
        }
    }

    fn get_prev_next(&self) -> (Option<&'a NodeInner<T>>, Option<&'a NodeInner<T>>) {
        // Safety: As long as the queue is well formed, the following are true:
        // * Pointer is properly aligned
        // * Pointer is dereferenceable
        // * Pointer points to a valid instance
        // Since the mutex is held:
        // * The memory the pointer points to will not be mutated
        // The lifetime of 'a is while we have the mutable reference to the queue, which must be
        // shorter than the time the mutex is held.
        unsafe {
            (self.prev.as_ref(), self.next.as_ref())
        }
    }

    /// Insert a node to the left of this cursor.
    pub fn insert(&mut self, node: Pin<&mut DequeNode<'b, M, T>>) -> Result<()> {
        if node.attached() {
            return Err(Error::Attached);
        }
        if !core::ptr::eq(self.queue, node.queue) {
            return Err(Error::WrongQueue);
        }
        
        unsafe {
            let (prev, next) = self.get_prev_next();
            
            // Safety: We won't move out of the reference
            let node_inner = &mut node.get_unchecked_mut().inner;

            // Safety: The queue mutex is locked
            node_inner.attach(
                self.inner, next, prev
            );

            // Advance the cursor to be between the newly inserted node and the next node
            self.prev = node_inner;
        }

        Ok(())
    }

    /// Pop the node to the left of this cursor
    pub fn pop<R>(&mut self, function: impl FnOnce(&mut T) -> R) -> Option<R> {
        let (prev, _next) = self.get_prev_next();

        if let Some(prev) = prev {
            // Patch our pointers
            self.prev = prev.data.borrow().next;

            // Safety: The queue mutex is locked
            unsafe { prev.detach(self.inner) };
            
            let mut data = prev.data.borrow_mut();
            Some(function(&mut data.value))
        } else {
            // Nothing to pop
            None
        }
    }

    pub fn move_next(&mut self) -> bool {
        let (_prev, next) = self.get_prev_next();

        if let Some(next) = next {
            self.prev = next;
            self.next = next.data.borrow().next;

            true
        } else {
            false
        }
    }
}

/// The root of the doubly-linked list queue.
pub struct Deque<M: Mutex, T> {
    mutex: M,
    inner: RefCell<DequeInner<T>>,
    _pin: PhantomPinned,
}

unsafe impl <M: Mutex, T> Send for Deque<M, T> where M: Send, T: Send {}
unsafe impl <M: Mutex, T> Sync for Deque<M, T> where M: Sync, T: Send {}

struct DequeInner<T> {
    size: usize,
    head: *const NodeInner<T>,
    tail: *const NodeInner<T>,
}

impl <M: Mutex, T> Default for Deque<M, T> where M: Default {
    fn default() -> Self { Self::new(M::default()) }
}

impl <M: Mutex, T> Deque<M, T> {
    pub const fn new(mutex: M) -> Self {
        Self {
            mutex,
            inner: RefCell::new(DequeInner {
                size: 0,
                head: core::ptr::null_mut(),
                tail: core::ptr::null_mut(),
            }),
            _pin: PhantomPinned,
        }
    }

    pub fn with_cursor<'a, R>(&'a self, side: Side, function: impl FnOnce(Cursor<'_, 'a, M, T>) -> R) -> R {
        self.mutex.lock(|| {
            let mut inner = self.inner.borrow_mut();
            // Safety: The mutex is held so we have exclusive access.
            let cursor = unsafe {match side {
                Side::Front => Cursor::new_front(self, &mut inner),
                Side::Back => Cursor::new_back(self, &mut inner),
            }};
            function(cursor)
        })
    }

    /// Push a node onto the front of the queue.
    pub fn push_front<'a>(&'a self, node: Pin<&mut DequeNode<'a, M, T>>) -> Result<()> {
        self.with_cursor(Side::Front, |mut cursor| cursor.insert(node))
    }

    /// Push a node onto the back of the queue.
    pub fn push_back<'a>(&'a self, node: Pin<&mut DequeNode<'a, M, T>>) -> Result<()> {
        self.with_cursor(Side::Back, |mut cursor| cursor.insert(node))
    }

    /// Get the length of the queue. This may not be accurate if the queue is being concurrently
    /// modified.
    pub fn len(&self) -> usize {
        self.mutex.lock(|| {
            self.inner.borrow().size
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
                data: NodeData {
                    value,
                    attached: false,
                    next: core::ptr::null(),
                    prev: core::ptr::null(),
                }.into(),
                _pin: PhantomPinned,
            }
        }
    }

    /// Return true if this node is currently in a queue.
    pub fn attached(&self) -> bool {
        self.inner.data.borrow().attached
    }

    /// Detach this node from any queue it is in. This makes no changes if the node is not in a queue.
    pub fn detach(self: Pin<&mut Self>) {
        self.queue.mutex.lock(|| unsafe {
            if !self.attached() {
                return;
            }

            let mut queue = self.queue.inner.borrow_mut();

            // Safety: We don't move out of the mutable reference
            let self_mut = self.get_unchecked_mut();
            let inner = &mut self_mut.inner;

            // Safety: Mutex is locked and we are well formed
            inner.detach(&mut queue);
        });
    }

    /// Replace the value of this node with a new value and return the old value. This operates
    /// on a node that has not been pinned.
    pub fn replace(&mut self, value: T) -> T {
        let mut inner = self.inner.data.borrow_mut();
        core::mem::replace(&mut inner.value, value)
    }

    /// Replace the value of this node with a new value and return the old value. This operates
    /// on a node that has been pinned.
    pub fn replace_pin(self: Pin<&mut Self>, value: T) -> T {
        self.mutate(|v| core::mem::replace(v, value))
    }

    /// Mutate the value stored in this node.
    pub fn mutate<R>(self: Pin<&mut Self>, function: impl FnOnce(&mut T) -> R) -> R {
        self.queue.mutex.lock(|| unsafe {
            // Safety: We don't move out of the mutable reference
            let self_mut = self.get_unchecked_mut();
            let inner = &mut self_mut.inner;
            // Safety: Mutex is locked
            inner.with_value(function)
        })
    }
}

impl <'a, M: Mutex, T> Drop for DequeNode<'a, M, T> {
    fn drop(&mut self) {
        // Safety: We know we are never using this value again after being dropped
        unsafe { Pin::new_unchecked(self) }.detach();
    }
}

/// This struct does all the magic required for the queue to work. This represents a single
/// element on the queue.
struct NodeInner<T> {
    data: RefCell<NodeData<T>>,
    _pin: PhantomPinned,
}

struct NodeData<T> {
    value: T,
    attached: bool,
    next: *const NodeInner<T>,
    prev: *const NodeInner<T>,
}

impl <T> NodeInner<T> {
    /// Patch this node into a list. The queue mutex MUST be locked before calling.
    pub unsafe fn attach(&self, queue: &mut DequeInner<T>, next: Option<&NodeInner<T>>, prev: Option<&NodeInner<T>>) {
        let mut self_inner = self.data.borrow_mut();

        self_inner.attached = true;
        queue.size += 1;

        if let Some(prev) = prev {
            self_inner.prev = prev;
            prev.data.borrow_mut().next = self;
        } else {
            self_inner.prev = core::ptr::null();
            queue.head = self;
        }

        if let Some(next) = next {
            self_inner.next = next;
            next.data.borrow_mut().prev = self;
        } else {
            self_inner.next = core::ptr::null();
            queue.tail = self;
        }
    }

    /// Detach this node from it's queue. The queue mutex MUST be locked before calling.
    pub unsafe fn detach(&self, queue: &mut DequeInner<T>) {
        queue.size -= 1;

        let mut self_inner = self.data.borrow_mut();

        // Safety: As long as the queue is well formed, the following are true:
        // * Pointer is properly aligned
        // * Pointer is dereferenceable
        // * Pointer points to a valid instance
        // Since the mutex is held:
        // * The memory the pointer points to will not be mutated
        if let Some(next) = unsafe { self_inner.next.as_ref() } {
            // Another node after this one
            let mut next = next.data.borrow_mut();
            next.prev = self_inner.prev;
        } else if core::ptr::eq(queue.tail, self) {
            // We are the tail
            queue.tail = self_inner.prev;
        }
        
        // Safety: See above
        if let Some(prev) = unsafe { self_inner.prev.as_ref() } {
            // Another node before this one
            let mut prev = prev.data.borrow_mut();
            prev.next = self_inner.next;
        } else if core::ptr::eq(queue.head, self) {
            // We are the head
            queue.head = self_inner.next;
        }

        self_inner.next = core::ptr::null();
        self_inner.prev = core::ptr::null();
        self_inner.attached = false;
    }

    /// Call a function with the value stored inside this node. The queue mutex MUST be locked before calling if this node is attached.
    pub unsafe fn with_value<R>(&self, function: impl FnOnce(&mut T) -> R) -> R {
        let mut self_inner = self.data.borrow_mut();
        function(&mut self_inner.value)
    }
}


impl <M: Mutex, T> Deque<M, T> where T: Copy {
    /// Pop a node from the front of the queue.
    pub fn pop_front_copy(&self) -> Option<T> {
        self.with_cursor(Side::Front, |mut cursor| {
            cursor.move_next();
            cursor.pop(|v| *v)
        })
    }
    /// Pop a node from the back of the queue.
    pub fn pop_back_copy(&self) -> Option<T> {
        self.with_cursor(Side::Back, |mut cursor| {
            cursor.pop(|v| *v)
        })
    }
}

impl <M: Mutex, T> Deque<M, T> where T: Clone {
    /// Pop a node from the front of the queue and clone its value.
    pub fn pop_front_clone(&self) -> Option<T> {
        self.with_cursor(Side::Front, |mut cursor| {
            cursor.move_next();
            cursor.pop(|v| v.clone())
        })
    }
    /// Pop a node from the back of the queue and clone its value.
    pub fn pop_back_clone(&self) -> Option<T> {
        self.with_cursor(Side::Back, |mut cursor| {
            cursor.pop(|v| v.clone())
        })
    }
}

impl <M: Mutex, T> Deque<M, Option<T>> {
    /// Pop a node from the front of the queue and take its value replacing it with `None`.
    pub fn take_front(&self) -> Option<Option<T>> {
        self.with_cursor(Side::Front, |mut cursor| {
            cursor.move_next();
            cursor.pop(|v| v.take())
        })
    }
    /// Pop a node from the back of the queue and take its value replacing it with `None`.
    pub fn take_back(&self) -> Option<Option<T>> {
        self.with_cursor(Side::Back, |mut cursor| {
            cursor.pop(|v| v.take())
        })
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

#[cfg(test)]
mod test {
    use super::*;
    use core::pin::pin;
    use crate::{mutex::NoopMutex, error::Error};

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
            assert_eq!(queue2.push_back(node.as_mut()), Err(Error::WrongQueue));
            assert_eq!(queue2.push_front(node.as_mut()), Err(Error::WrongQueue));

            assert_eq!(queue1.push_back(node.as_mut()), Ok(()));
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
