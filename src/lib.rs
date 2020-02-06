//! # Continuous Buffer Module
//! Provides tooling for Continuous Buffer
//! (i.e. a Circular Buffer that is expected to overrun).
//!
//! Uses `core` (and nothing else) so it can be used in `#[no_std]` projects.
//!
//! All logic is implemented in [`ContBufCtrl`].
//! # Examples
//! ```rust
//! use contbuf::*;
//!
//! // Define MyBuffer as a continuous buffer
//! // which will operate on an u32 array of size 2
//! // and will be initialized to 0
//! define_buf!{MyBuffer [u32; 2] = 0}
//!
//! let mut b = MyBuffer::new();
//! assert_eq!(b.is_empty(), true);
//! assert_eq!(b.data, [0, 0]);
//! assert_eq!(b.get_head(), 0);
//!
//! b.stuff(1);
//! assert_eq!(b.is_empty(), false);
//! assert_eq!(b.data, [1, 0]);
//!
//! b.stuff(2);
//! assert_eq!(b.is_full(), true);
//! assert_eq!(b.data, [1, 2]);
//!
//! b.stuff(3);
//! assert_eq!(b.data, [3, 2]);
//! assert_eq!(b.get_head(), 1);
//!
//!
//! b.reset();
//! assert_eq!(b.is_empty(), true);
//! assert_eq!(b.get_head(), 0);
//! // as we don't keep track of the init value
//! assert_eq!(b.data, [3, 2]);
//! ```
#![no_std]

use core::marker::PhantomData;

/// # Macro for defining continuous buffers
///
/// All functions just pass the input and data buffer (if necessary) to a function of the same name in [`ContBufCtrl`].
/// All logic is implemented there.
///
/// # Examples
/// Define a continous buffer called `MyBuffer`.
///
/// Every instance will own an array of type `u32` and length `2`.
/// The array will be initialized with `0`.
/// ```
/// use contbuf::*;
/// define_buf!{MyBuffer [u32; 2] = 0}
/// let mut b1 = MyBuffer::new();
/// let mut b2 = MyBuffer::new();
/// b1.stuff(1);
/// b2.stuff(9);
/// assert_eq!([1, 0], b1.data);
/// assert_eq!([9, 0], b2.data);
/// ```
///
/// Define a continous buffer called `SpecialBuffer` with your own `Special` type. Note that the
/// type needs to implement `Copy` and `Clone` (to pass data around) and needs to be `pub`, as
/// `SpecialBuffer` will be a public interface that cannot have content of private type.
/// ```
/// use contbuf::*;
/// #[derive(Copy, Clone)]
/// pub struct Special {
///     special_number: u8,
/// }
///
/// define_buf!{SpecialBuffer [Special; 2] = Special {special_number : 0}}
///
///
/// ```
///
#[macro_export]
macro_rules! define_buf {
    ($contbuffername:ident [$T:ty; $size:expr] = $default:expr) => {
        pub struct $contbuffername {
            data: [$T; $size],
            ctrl: ContBufCtrl<$T>,
        }

        impl $contbuffername {
            pub fn new() -> Self {
                let data: [$T; $size] = [$default; $size];
                let ctrl = ContBufCtrl::new(&data);
                Self { data, ctrl }
            }

            pub fn is_empty(&self) -> bool {
                self.ctrl.is_empty()
            }

            pub fn is_full(&self) -> bool {
                self.ctrl.is_full()
            }

            pub fn stuff(&mut self, val: $T) {
                self.ctrl.stuff(&mut self.data, val);
            }

            pub fn get_oldest(&self) -> $T {
                self.ctrl.get_oldest(&self.data)
            }

            pub fn get_newest(&self) -> $T {
                self.ctrl.get_newest(&self.data)
            }

            pub fn reset(&mut self) {
                self.ctrl.reset();
            }

            pub fn get_head(&self) -> usize {
                self.ctrl.get_head()
            }
        }
    };
}

/// # Continuous Buffer Control Struct
///
/// Should only be used indirectly with a Continuous Buffer that can be defined using the
/// [`define_buf!`] macro.
/// However for each `pub fn` here there is also a function with the same name in each Continuous Buffer defined by that macro.
///
/// # Examples
///
/// Assume we defined the following buffer.
/// ```
/// # use contbuf::*;
/// define_buf!{MyBuffer [u32; 2] = 0}
/// let mut b = MyBuffer::new();
/// ```
/// Now for each function in the Control Struct (e.g.:)
/// ```ignore
/// pub fn stuff(&mut self, data: &mut [T], val: T)
/// ```
/// the Continuous Buffer implements a wrapper like this:
/// ```ignore
/// pub fn stuff(&mut self, val: u32) {
///     self.ctrl.stuff(&mut self.data, val);
/// }
/// ```
/// So all functions in this Contorl Struct can be called via the Continuous Buffer by omitting the
/// reference to the data (which is owned and handled by the Continuous Buffer):
/// ```
/// # use contbuf::*;
/// # define_buf!{MyBuffer [u32; 2] = 0}
/// # let mut b = MyBuffer::new();
/// b.stuff(42);
/// ```
#[derive(Debug)]
pub struct ContBufCtrl<T> {
    head: usize,
    filled: bool,
    len: usize,
    phantom: PhantomData<T>,
}

impl<T: Copy> ContBufCtrl<T> {
    /// Initializes a new control unit for a data buffer of type T.
    pub fn new(data: &[T]) -> Self {
        Self {
            head: 0,
            filled: false,
            len: data.len(),
            phantom: PhantomData,
        }
    }

    /// Checks if there was data written to the data buffer.
    pub fn is_empty(&self) -> bool {
        self.head == 0 && !self.filled
    }

    /// Checks if the data buffer is filled.
    pub fn is_full(&self) -> bool {
        self.filled
    }

    /// Increments the head with respect to the data length.
    fn inc_head(&mut self) {
        self.head = (self.head + 1) % self.len;
    }

    /// Stuffs data into the data buffer, overwriting old data.
    pub fn stuff(&mut self, data: &mut [T], val: T) {
        data[self.head] = val;
        self.inc_head();
        if !self.filled {
            if self.head == 0 {
                self.filled = true;
            }
        }
    }

    /// Returns the newest entry in the data buffer.
    pub fn get_newest(&self, data: &[T]) -> T {
        if self.head > 0 {
            return data[self.head - 1];
        } else {
            return data[self.len - 1];
        }
    }

    /// Returns the oldest entry in the data buffer.
    pub fn get_oldest(&self, data: &[T]) -> T {
        data[self.head]
    }

    /// Reset the buffer
    pub fn reset(&mut self) {
        self.head = 0;
        self.filled = false;
    }

    pub fn get_head(&self) -> usize {
        self.head
    }
}
