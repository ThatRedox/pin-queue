#![no_std]
#![doc = include_str!("../README.md")]

extern crate alloc;

pub mod queue;
pub mod mutex;
pub mod error;

pub use queue::Queue;
