# pin-queue

[![Rust](https://github.com/ThatRedox/pin-queue/actions/workflows/rust.yml/badge.svg?branch=master)](https://github.com/ThatRedox/pin-queue/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/ThatRedox/pin-queue/branch/master/graph/badge.svg?token=KRVE1PZK52)](https://codecov.io/gh/ThatRedox/pin-queue)

An unbounded queue that doesn't require dynamic memory allocation.

## Example
```rust
use pin_queue::mutex::CriticalSectionMutex;
use pin_queue::Deque;
use core::pin::pin;

// Create a new queue of `u32`, using the `CriticalSectionMutex` mutex.
let queue = Deque::<CriticalSectionMutex, u32>::new(CriticalSectionMutex::new());
{
    // Create a node, and pin it to the stack.
    let mut node = pin!(queue.new_node(1));
    // Push the node onto the queue.
    queue.push_back(node.as_mut()).unwrap();
    // Pop our node off the queue.
    assert_eq!(queue.pop_front().unwrap(), 1);
    // Push our node back onto the queue.
    queue.push_back(node.as_mut()).unwrap();
} // Node gets dropped and automatically removed from the queue
assert!(queue.is_empty());
```

# License
Copyright 2023 That Redox

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

[http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0)

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
