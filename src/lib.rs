#![no_std]
#![doc = include_str!("../README.md")]

extern crate alloc;

pub mod deque;
pub mod mutex;
pub mod error;

pub use deque::Deque;
