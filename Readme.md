# contbuf

## Continuous Buffer Module
Provides tooling for Continuous Buffer
(i.e. a Circular Buffer that is expected to overrun).

Uses `core` (and nothing else) so it can be used in `#[no_std]` projects.

All logic is implemented in [`ContBufCtrl`].
## Examples
```rust
use contbuf::*;

// Define MyBuffer as a continuous buffer
// which will operate on an u32 array of size 2
// and will be initialized to 0
define_buf!{MyBuffer [u32; 2] = 0}

let mut b = MyBuffer::new();
assert_eq!(b.is_empty(), true);
assert_eq!(b.data, [0, 0]);

b.stuff(1);
assert_eq!(b.is_empty(), false);
assert_eq!(b.data, [1, 0]);

b.stuff(2);
assert_eq!(b.is_full(), true);
assert_eq!(b.data, [1, 2]);

b.stuff(3);
assert_eq!(b.data, [3, 2]);

b.stuff(4);
assert_eq!(b.data, [3, 4]);

```
