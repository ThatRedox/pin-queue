#![no_std]
#![doc = include_str!("../README.md")]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod deque;
pub mod mutex;
pub mod error;

pub use deque::Deque;
