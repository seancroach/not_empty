#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

#![deny(clippy::pedantic)]
#![allow(clippy::module_name_repetitions, clippy::wildcard_imports)]

#[cfg(all(feature = "alloc", feature = "std"))]
compile_error!("`not_empty` cannot have both `alloc` and `std` features enabled");

mod imports;
#[cfg(any(feature = "alloc", feature = "std"))]
mod iter;
pub mod slice;
#[cfg(any(feature = "alloc", feature = "std"))]
mod vec;

#[cfg(any(feature = "alloc", feature = "std"))]
pub use iter::IteratorExt;
pub use slice::NonEmptySlice;
#[cfg(any(feature = "alloc", feature = "std"))]
pub use vec::NonEmptyVec;

use core::fmt;

/// The prelude imports for `not_empty`. The intention is so you can include
/// `use not_empty::prelude::*` and have easy access to this crate's types
/// and traits.
pub mod prelude {
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[doc(inline)]
    pub use super::not_empty_vec;
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[doc(inline)]
    // The name is made verbose as to not collide with other iterator extension
    // traits in scope.
    pub use super::IteratorExt as NotEmptyIteratorExt;
    #[doc(inline)]
    pub use super::NonEmptySlice;
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[doc(inline)]
    pub use super::NonEmptyVec;
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[doc(hidden)]
#[allow(unused_imports)]
/// A cute hack to prevent my need for using `cfg` to control how the macro
/// operates (and since nested macros are a pain).
pub mod __private {
    #[cfg(feature = "alloc")]
    extern crate alloc;
    #[cfg(feature = "alloc")]
    pub use alloc::vec;
    #[cfg(feature = "std")]
    pub use std::vec;
}

/// Creates a [`NonEmptyVec`] containing the arguments.
///
/// # Panics
///
/// When using the `not_empty_vec!` macro in the form of `not_empty_vec![E; N]`,
/// if `N` is a non-literal expression that resolves to `0`, the program will
/// panic **only when `debug_assertions` is enabled**.
///
/// If it is a literal `0`, a compiler error is still thrown as expected.
///
/// # Examples
///
/// Create a [`NonEmptyVec`] containing a given list of elements:
///
/// ```
/// use not_empty::{not_empty_vec, NonEmptyVec};
///
/// let vec: NonEmptyVec<_> = not_empty_vec![1, 2, 3];
/// assert_eq!(vec[0], 1);
/// assert_eq!(vec[1], 2);
/// assert_eq!(vec[2], 3);
/// ```
///
/// Create a [`NonEmptyVec`] from a given element and size:
///
/// ```
/// use not_empty::{not_empty_vec, NonEmptyVec};
///
/// let vec: NonEmptyVec<_> = not_empty_vec![1; 3];
/// assert_eq!(vec, [1, 1, 1]);
/// ```
///
/// *Note*: Unlike array expressions, this syntax supports all elements which
/// implement [`Clone`] and the number of elements doesn't have to be constant.
///
/// Because it will use [`Clone::clone`] to duplicate an expression, you should
/// be careful using this with types having a nonstandard [`Clone`]
/// implementation. For example, `not_empty_vec![Rc::new(1); 5]` will create a
/// vector of five references to the same boxed integer value, not five
/// references pointing to independently boxed integers.
///
/// Unlike [`std::vec!`], all of the following cases are compiler errors:
///
/// ```compile_fail
/// // error: cannot initialize non-empty vector with zero length
/// not_empty::vec![1; 0];
/// ```
///
/// ```compile_fail
/// // error: cannot initialize non-empty vector with zero length
/// not_empty::vec![1; 0usize];
/// ```
///
/// ```compile_fail
/// // error: cannot initialize non-empty vector with zero length
/// not_empty::vec![];
/// ```
///
/// And, as stated previously, with `debug_assertions` enabled, `not_empty_vec!`
/// will panic if initialized with a length of zero at runtime:
///
/// ```should_panic
/// let n = 0;
///
/// // panic: non-empty vector initialized with an empty vector
/// not_empty::vec![10; n];
/// ```
#[macro_export]
#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
macro_rules! not_empty_vec {
    () => {{
        compile_error!("cannot initialize non-empty vector with zero length")
    }};
    ($elem:expr; 0) => {{
        compile_error!("cannot initialize non-empty vector with zero length");
    }};
    ($elem:expr; 0usize) => {{
        compile_error!("cannot initialize non-empty vector with zero length");
    }};
    ($elem:expr; $n:expr) => {{
        unsafe { $crate::NonEmptyVec::new_unchecked($crate::__private::vec![$elem; $n]) }
    }};
    ($($x:expr),+ $(,)?) => {{
        unsafe { $crate::NonEmptyVec::new_unchecked($crate::__private::vec![$($x),+]) }
    }};
}

/// An alias of [`NonEmptySlice<T>`] if `not_empty::Slice<T>` usage is
/// preferred.
pub type Slice<T> = NonEmptySlice<T>;

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
/// An alias of [`NonEmptyVec<T>`] if `not_empty::Vec<T>` usage is preferred.
pub type Vec<T> = NonEmptyVec<T>;

/// An alias of [`not_empty_vec`] if `not_empty::vec` usage is preferred.
#[macro_export]
#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
macro_rules! vec {
    ($($tt:tt)*) => {{
        $crate::not_empty_vec!($($tt)*)
    }};
}

/// An error thrown when the input collection is empty.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EmptyError;

impl fmt::Display for EmptyError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("empty collection")
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, cfg(feature = "std"))]
impl std::error::Error for EmptyError {}
