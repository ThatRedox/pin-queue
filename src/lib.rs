#![no_std]
#![doc = include_str!("../README.md")]

pub mod deque;
pub mod mutex;
pub mod error;

pub use deque::Deque;
