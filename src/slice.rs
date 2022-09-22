#[cfg(any(feature = "alloc", feature = "std"))]
use crate::NonEmptyVec;
use crate::{imports::*, EmptyError};

use core::{
    array::TryFromSliceError,
    cmp::Ordering,
    convert::{TryFrom, TryInto},
    fmt,
    hash::{Hash, Hasher},
    hint,
    num::NonZeroUsize,
    ops,
    slice::{self, SliceIndex},
};

/// A slice that is guaranteed to not be empty.
///
/// The layout of a [`NonEmptySlice<T>`] is idential to [`[T]`](prim@slice).
/// However, many methods have been overridden or optimized to reflect that the
/// slice's length can never be zero.
#[repr(transparent)]
pub struct NonEmptySlice<T> {
    pub(crate) inner: [T],
}

impl<T> NonEmptySlice<T> {
    ////////////////////////////////////////////////////////////////////////////
    // Constructors
    ////////////////////////////////////////////////////////////////////////////

    /// Converts [`&[T]`](prim@slice) to [`&NonEmptySlice<T>`](Self) without
    /// checking if the given slice is not empty.
    ///
    /// This is a cost-free conversion.
    ///
    /// # Safety
    ///
    /// The slice must not be empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// let slice = &[1, 2, 3];
    /// let nonempty: &NonEmptySlice<_> = unsafe { NonEmptySlice::new_unchecked(slice) };
    /// ```
    #[inline]
    #[track_caller]
    pub const unsafe fn new_unchecked(slice: &[T]) -> &NonEmptySlice<T> {
        debug_assert!(
            !slice.is_empty(),
            "non-empty slice initialized with an empty slice"
        );
        &*(slice as *const [T] as *const NonEmptySlice<T>)
    }

    /// Creates a non-empty slice if the given slice is not empty.
    ///
    /// # Errors
    ///
    /// Returns an [`EmptyError`] if the given slice is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[1, 2, 3];
    /// let nonempty: &NonEmptySlice<_> = NonEmptySlice::new(slice)?;
    /// assert!(nonempty.len().get() == 3);
    ///
    /// let empty: &[i32] = &[];
    /// assert!(NonEmptySlice::new(empty).is_err());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub const fn new(slice: &[T]) -> Result<&NonEmptySlice<T>, EmptyError> {
        if slice.is_empty() {
            Err(EmptyError)
        } else {
            Ok(unsafe { NonEmptySlice::new_unchecked(slice) })
        }
    }

    /// Converts [`&mut [T]`](prim@slice) to [`&mut NonEmptySlice<T>`](Self)
    /// without checking if the given mutable slice is not empty.
    ///
    /// This is a cost-free conversion.
    ///
    /// # Safety
    ///
    /// The mutable slice must not be empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// let slice = &mut [1, 2, 3];
    /// let nonempty: &mut NonEmptySlice<_> = unsafe { NonEmptySlice::new_mut_unchecked(slice) };
    /// ```
    #[must_use]
    #[inline]
    pub unsafe fn new_mut_unchecked(slice: &mut [T]) -> &mut NonEmptySlice<T> {
        debug_assert!(
            !slice.is_empty(),
            "mutable non-empty slice initialized with an empty mutable slice"
        );
        &mut *(slice as *mut [T] as *mut NonEmptySlice<T>)
    }

    /// Creates a non-empty mutable slice if the given mutable slice is not
    /// empty.
    ///
    /// # Errors
    ///
    /// Returns an [`EmptyError`] if the given mutable slice is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &mut [1, 2, 3];
    /// let nonempty: &mut NonEmptySlice<_> = NonEmptySlice::new_mut(slice)?;
    /// assert!(nonempty.len().get() == 3);
    ///
    /// let empty: &mut [i32] = &mut [];
    /// assert!(NonEmptySlice::new_mut(empty).is_err());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn new_mut(slice: &mut [T]) -> Result<&mut NonEmptySlice<T>, EmptyError> {
        (!slice.is_empty())
            .then(|| unsafe { NonEmptySlice::new_mut_unchecked(slice) })
            .ok_or(EmptyError)
    }

    ////////////////////////////////////////////////////////////////////////////
    // `not_empty` overrides to slice
    ////////////////////////////////////////////////////////////////////////////

    /// Returns the number of elements in the slice.
    ///
    /// Unlike [`slice::len`], this returns a [`NonZeroUsize`] instead of a
    /// [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[1, 2, 3];
    /// let nonempty = NonEmptySlice::new(slice)?;
    /// assert_eq!(nonempty.len(), NonZeroUsize::new(3).unwrap());
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// A method which always returns `true`.
    ///
    /// Unlike a normal slice, this slice is never empty. It's incredibly likely
    /// that, if you are using this check, it is absolutely unnecessary.
    #[must_use]
    #[inline]
    #[allow(clippy::unused_self)]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Returns the first element of the slice.
    ///
    /// Unlike [`slice::first`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[1, 2, 3];
    /// let nonempty = NonEmptySlice::new(slice)?;
    /// assert_eq!(nonempty.first(), &1);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub const fn first(&self) -> &T {
        match self.inner.first() {
            Some(element) => element,
            None => unsafe { hint::unreachable_unchecked() },
        }
    }
    /// Returns a mutable pointer to the first element of the slice.
    ///
    /// Unlike [`slice::first_mut`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &mut [0, 1, 2];
    /// let nonempty = NonEmptySlice::new_mut(slice)?;
    /// *nonempty.first_mut() = 5;
    /// assert_eq!(nonempty, &[5, 1, 2]);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub fn first_mut(&mut self) -> &mut T {
        unsafe { self.inner.first_mut().unwrap_unchecked() }
    }

    /// Returns the first and all the rest of the elements of the slice.
    ///
    /// Unlike [`slice::split_first`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[0, 1, 2];
    /// let nonempty = NonEmptySlice::new(slice)?;
    ///
    /// let (first, elements) = nonempty.split_first();
    /// assert_eq!(first, &0);
    /// assert_eq!(elements, &[1, 2]);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub const fn split_first(&self) -> (&T, &[T]) {
        match self.inner.split_first() {
            Some(tuple) => tuple,
            None => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns the first and all the rest of the elements of the slice.
    ///
    /// Unlike [`slice::split_first_mut`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &mut [0, 1, 2];
    /// let nonempty = NonEmptySlice::new_mut(slice)?;
    ///
    /// let (first, elements) = nonempty.split_first_mut();
    /// *first = 3;
    /// elements[0] = 4;
    /// elements[1] = 5;
    ///
    /// assert_eq!(slice, &[3, 4, 5]);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub fn split_first_mut(&mut self) -> (&mut T, &mut [T]) {
        unsafe { self.inner.split_first_mut().unwrap_unchecked() }
    }

    /// Returns the last element of the slice.
    ///
    /// Unlike [`slice::last`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[1, 2, 3];
    /// let nonempty = NonEmptySlice::new(slice)?;
    /// assert_eq!(nonempty.last(), &3);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub const fn last(&self) -> &T {
        match self.inner.last() {
            Some(element) => element,
            None => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns a mutable pointer to the last element of the slice.
    ///
    /// Unlike [`slice::last_mut`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &mut [0, 1, 2];
    /// let nonempty = NonEmptySlice::new_mut(slice)?;
    /// *nonempty.last_mut() = 10;
    /// assert_eq!(nonempty, &[0, 1, 10]);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub fn last_mut(&mut self) -> &mut T {
        unsafe { self.inner.last_mut().unwrap_unchecked() }
    }

    /// Returns the last and all the rest of the elements of the slice.
    ///
    /// Unlike [`slice::split_last`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[0, 1, 2];
    /// let nonempty = NonEmptySlice::new(slice)?;
    ///
    /// let (last, elements) = nonempty.split_last();
    /// assert_eq!(last, &2);
    /// assert_eq!(elements, &[0, 1]);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub const fn split_last(&self) -> (&T, &[T]) {
        match self.inner.split_last() {
            Some(tuple) => tuple,
            None => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns the last and all the rest of the elements of the slice.
    ///
    /// Unlike [`slice::split_last_mut`], this **does not** return an [`Option`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &mut [0, 1, 2];
    /// let nonempty = NonEmptySlice::new_mut(slice)?;
    ///
    /// let (last, elements) = nonempty.split_last_mut();
    /// *last = 3;
    /// elements[0] = 4;
    /// elements[1] = 5;
    ///
    /// assert_eq!(slice, &[4, 5, 3]);
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    #[inline]
    pub fn split_last_mut(&mut self) -> (&mut T, &mut [T]) {
        unsafe { self.inner.split_last_mut().unwrap_unchecked() }
    }

    ////////////////////////////////////////////////////////////////////////////
    // `alloc` methods
    ////////////////////////////////////////////////////////////////////////////

    /// Copies `self` into a new [`NonEmptyVec`].
    ///
    /// Unlike [`slice::to_vec`], this returns a [`NonEmptyVec<T>`] instead of a
    /// [`Vec<T>`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::{NonEmptySlice, NonEmptyVec};
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let slice = &[1, 2, 3];
    /// let nonempty: &NonEmptySlice<_> = NonEmptySlice::new(slice)?;
    /// let nonempty_vec: NonEmptyVec<_> = nonempty.to_vec();
    ///
    /// assert_eq!(nonempty_vec, not_empty::vec![1, 2, 3]);
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    #[inline]
    pub fn to_vec(&self) -> NonEmptyVec<T>
    where
        T: Clone,
    {
        let vec = self.inner.to_vec();
        unsafe { NonEmptyVec::new_unchecked(vec) }
    }

    /// Converts `self` into a non-empty vector without clones or allocation.
    ///
    /// Unlike [`slice::into_vec`], this returns a [`NonEmptyVec<T>`] instead of
    /// a [`Vec<T>`].
    ///
    /// The resulting [`NonEmptyVec<T>`] can get converted back into a box
    /// via [`NonEmptyVec::into_boxed_slice`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::{NonEmptySlice, NonEmptyVec};
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let boxed_slice: Box<[_]> = Box::new([10, 40, 30]);
    /// let boxed_nonempty: Box<NonEmptySlice<_>> = boxed_slice.try_into()?;
    /// let nonempty_vec = boxed_nonempty.into_vec();
    ///
    /// assert_eq!(nonempty_vec, not_empty::vec![10, 40, 30]);
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    #[inline]
    pub fn into_vec(self: Box<NonEmptySlice<T>>) -> NonEmptyVec<T> {
        let len = self.len();
        let ptr = Box::into_raw(self).cast::<T>();
        unsafe { NonEmptyVec::from_raw_parts(ptr, len, len) }
    }
}

impl NonEmptySlice<u8> {
    /// Returns a non-empty vector containing a copy of this slice where each
    /// byte is mapped to its ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z', but non-ASCII letters
    /// are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_uppercase`].
    ///
    /// [`make_ascii_uppercase`]: slice::make_ascii_uppercase
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    #[inline]
    pub fn to_ascii_uppercase(&self) -> NonEmptyVec<u8> {
        unsafe { NonEmptyVec::new_unchecked(self.inner.to_ascii_uppercase()) }
    }

    /// Returns a non-empty vector containing a copy of this slice where each
    /// byte is mapped to its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z', but non-ASCII letters
    /// are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// [`make_ascii_lowercase`]: slice::make_ascii_lowercase
    #[cfg(any(feature = "alloc", feature = "std"))]
    #[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
    #[must_use]
    #[inline]
    pub fn to_ascii_lowercase(&self) -> NonEmptyVec<u8> {
        unsafe { NonEmptyVec::new_unchecked(self.inner.to_ascii_lowercase()) }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Formatting implementations
////////////////////////////////////////////////////////////////////////////////

impl<T> fmt::Debug for NonEmptySlice<T>
where
    T: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Dereferencing implementations
////////////////////////////////////////////////////////////////////////////////

impl<T> ops::Deref for NonEmptySlice<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> ops::DerefMut for NonEmptySlice<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

////////////////////////////////////////////////////////////////////////////////
// Indexing implementations
////////////////////////////////////////////////////////////////////////////////

impl<T, I: SliceIndex<[T]>> ops::Index<I> for NonEmptySlice<T> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::<I>::index(&self.inner, index)
    }
}

impl<T, I: SliceIndex<[T]>> ops::IndexMut<I> for NonEmptySlice<T> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(&mut self.inner, index)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Iterator traits
////////////////////////////////////////////////////////////////////////////////

impl<'a, T> IntoIterator for &'a NonEmptySlice<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut NonEmptySlice<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

////////////////////////////////////////////////////////////////////////////////
// `as_*` implementations
////////////////////////////////////////////////////////////////////////////////

impl<T> AsRef<[T]> for NonEmptySlice<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<T> AsMut<[T]> for NonEmptySlice<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.inner
    }
}

////////////////////////////////////////////////////////////////////////////////
// `borrow` implementations
////////////////////////////////////////////////////////////////////////////////

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> Borrow<[T]> for NonEmptySlice<T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> BorrowMut<[T]> for NonEmptySlice<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T: Clone> ToOwned for NonEmptySlice<T> {
    type Owned = NonEmptyVec<T>;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.to_vec()
    }

    #[inline]
    fn clone_into(&self, target: &mut Self::Owned) {
        target.truncate(self.len());

        let (init, tail) = self.split_at(target.len().get());

        target.clone_from_slice(init);
        target.extend_from_slice(tail);
    }
}

////////////////////////////////////////////////////////////////////////////////
// Partial equivalence implementations
////////////////////////////////////////////////////////////////////////////////

impl<T, U> PartialEq<NonEmptySlice<U>> for NonEmptySlice<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptySlice<U>) -> bool {
        self.inner == other.inner
    }
}

impl<T, U> PartialEq<[U]> for NonEmptySlice<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &[U]) -> bool {
        &self.inner == other
    }
}

impl<T, U> PartialEq<NonEmptySlice<U>> for [T]
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptySlice<U>) -> bool {
        self == &other.inner
    }
}

impl<T, U, const N: usize> PartialEq<[U; N]> for NonEmptySlice<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &[U; N]) -> bool {
        &self.inner == other
    }
}

impl<T, U, const N: usize> PartialEq<NonEmptySlice<U>> for [T; N]
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptySlice<U>) -> bool {
        self == &other.inner
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, U> PartialEq<VecDeque<U>> for NonEmptySlice<T>
where
    T: PartialEq<U>,
{
    // This is a workaround since rustlib's PartialEq implementation isn't
    // symmetric.
    fn eq(&self, other: &VecDeque<U>) -> bool {
        if self.inner.len() != other.len() {
            return false;
        }

        let (oa, ob) = other.as_slices();
        let (sa, sb) = self.split_at(oa.len());

        sa == oa && sb == ob
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, U> PartialEq<NonEmptySlice<U>> for VecDeque<T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &NonEmptySlice<U>) -> bool {
        self == &&other.inner
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, U> PartialEq<Vec<U>> for NonEmptySlice<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &Vec<U>) -> bool {
        &self.inner == other
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, U> PartialEq<NonEmptySlice<U>> for Vec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptySlice<U>) -> bool {
        self == &other.inner
    }
}

////////////////////////////////////////////////////////////////////////////////
// Other comparison traits
////////////////////////////////////////////////////////////////////////////////

impl<T> Eq for NonEmptySlice<T> where T: Ord {}

impl<T> PartialOrd for NonEmptySlice<T>
where
    T: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<T> Ord for NonEmptySlice<T>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Hashing
////////////////////////////////////////////////////////////////////////////////

impl<T> Hash for NonEmptySlice<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

////////////////////////////////////////////////////////////////////////////////
// Conversions
////////////////////////////////////////////////////////////////////////////////

impl<'a, T> From<&'a NonEmptySlice<T>> for &'a [T] {
    #[inline]
    fn from(slice: &'a NonEmptySlice<T>) -> Self {
        slice
    }
}

impl<'a, T> From<&'a mut NonEmptySlice<T>> for &'a mut [T] {
    #[inline]
    fn from(slice: &'a mut NonEmptySlice<T>) -> Self {
        slice
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> From<Box<NonEmptySlice<T>>> for Box<[T]> {
    fn from(boxed: Box<NonEmptySlice<T>>) -> Self {
        let raw = Box::into_raw(boxed) as *mut [T];
        unsafe { Box::from_raw(raw) }
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<'a, T> From<&'a NonEmptySlice<T>> for Cow<'a, NonEmptySlice<T>>
where
    T: Clone,
{
    fn from(s: &'a NonEmptySlice<T>) -> Self {
        Cow::Borrowed(s)
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> From<&NonEmptySlice<T>> for Arc<NonEmptySlice<T>>
where
    T: Clone,
{
    #[inline]
    fn from(s: &NonEmptySlice<T>) -> Self {
        let arc: Arc<[T]> = Arc::from(&s.inner);
        let ptr = Arc::into_raw(arc) as *const NonEmptySlice<T>;
        unsafe { Arc::from_raw(ptr) }
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> From<&NonEmptySlice<T>> for Rc<NonEmptySlice<T>>
where
    T: Clone,
{
    #[inline]
    fn from(s: &NonEmptySlice<T>) -> Self {
        let rc: Rc<[T]> = Rc::from(&s.inner);
        let ptr = Rc::into_raw(rc) as *const NonEmptySlice<T>;
        unsafe { Rc::from_raw(ptr) }
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<'a, T> From<&'a NonEmptySlice<T>> for NonEmptyVec<T>
where
    T: Clone,
{
    #[inline]
    fn from(slice: &'a NonEmptySlice<T>) -> Self {
        let vec: Vec<T> = slice.inner.into();
        unsafe { NonEmptyVec::new_unchecked(vec) }
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<'a, T> From<&'a mut NonEmptySlice<T>> for NonEmptyVec<T>
where
    T: Clone,
{
    #[inline]
    fn from(slice: &'a mut NonEmptySlice<T>) -> Self {
        let vec: Vec<T> = slice.inner.into();
        unsafe { NonEmptyVec::new_unchecked(vec) }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Failable conversions
////////////////////////////////////////////////////////////////////////////////

impl<T, const N: usize> TryFrom<&NonEmptySlice<T>> for [T; N]
where
    T: Copy,
{
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(value: &NonEmptySlice<T>) -> Result<Self, Self::Error> {
        value.inner.try_into()
    }
}

impl<T, const N: usize> TryFrom<&mut NonEmptySlice<T>> for [T; N]
where
    T: Copy,
{
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(value: &mut NonEmptySlice<T>) -> Result<Self, Self::Error> {
        value.inner.try_into()
    }
}

impl<'a, T, const N: usize> TryFrom<&'a NonEmptySlice<T>> for &'a [T; N] {
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(value: &'a NonEmptySlice<T>) -> Result<Self, Self::Error> {
        value.inner.try_into()
    }
}

impl<'a, T, const N: usize> TryFrom<&'a mut NonEmptySlice<T>> for &'a mut [T; N] {
    type Error = TryFromSliceError;

    #[inline]
    fn try_from(value: &'a mut NonEmptySlice<T>) -> Result<Self, Self::Error> {
        (&mut value.inner).try_into()
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, const N: usize> TryFrom<[T; N]> for Box<NonEmptySlice<T>> {
    type Error = EmptyError;

    /// Converts a `[T; N]` into a `Box<NonEmptySlice<T>>` if `N` is not zero.
    ///
    /// This conversion moves the array to newly heap-allocated memory.
    ///
    /// # Errors
    ///
    /// Returns an [`EmptyError`] if `N` is equal to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let boxed: Box<NonEmptySlice<u8>> = Box::try_from([1, 2, 3])?;
    /// println!("{boxed:?}");
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    fn try_from(array: [T; N]) -> Result<Self, Self::Error> {
        let boxed_array: Box<[T]> = Box::new(array);
        boxed_array.try_into()
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> TryFrom<Box<[T]>> for Box<NonEmptySlice<T>> {
    type Error = EmptyError;

    /// Converts a boxed slice into a boxed non-empty slice if the given slice
    /// is not empty.
    ///
    /// # Errors
    ///
    /// Returns an [`EmptyError`] if the input slice is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use not_empty::NonEmptySlice;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let boxed_slice: Box<[i32]> = Box::from([1, 2, 3]);
    /// let boxed_nonempty: Box<NonEmptySlice<i32>> = boxed_slice.try_into()?;
    /// # Ok(())
    /// # }
    /// ```
    fn try_from(boxed_slice: Box<[T]>) -> Result<Self, Self::Error> {
        if boxed_slice.is_empty() {
            Err(EmptyError)
        } else {
            let raw = Box::into_raw(boxed_slice) as *mut NonEmptySlice<T>;
            Ok(unsafe { Box::from_raw(raw) })
        }
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> TryFrom<Box<[T]>> for NonEmptyVec<T> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: Box<[T]>) -> Result<Self, Self::Error> {
        value.try_into().map(NonEmptySlice::into_vec)
    }
}

impl<'a, T> TryFrom<&'a [T]> for &'a NonEmptySlice<T> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: &'a [T]) -> Result<Self, Self::Error> {
        NonEmptySlice::new(value)
    }
}

impl<'a, T> TryFrom<&'a mut [T]> for &'a mut NonEmptySlice<T> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: &'a mut [T]) -> Result<Self, Self::Error> {
        NonEmptySlice::new_mut(value)
    }
}

////////////////////////////////////////////////////////////////////////////////
// `net` implementations
////////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl<'a> ToSocketAddrs for &'a NonEmptySlice<SocketAddr> {
    type Iter = core::iter::Cloned<slice::Iter<'a, SocketAddr>>;

    #[inline]
    fn to_socket_addrs(&self) -> io::Result<Self::Iter> {
        (&self.inner).to_socket_addrs()
    }
}

////////////////////////////////////////////////////////////////////////////////
// `serde` implementations
////////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "serde")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "serde")))]
impl<T> serde::Serialize for NonEmptySlice<T>
where
    T: serde::Serialize,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serde::Serialize::serialize(&self.inner, serializer)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "serde")))]
impl<'de: 'a, 'a> serde::Deserialize<'de> for &'a NonEmptySlice<u8> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let slice: &'de [u8] = serde::Deserialize::deserialize(deserializer)?;
        NonEmptySlice::new(slice).map_err(|_| {
            serde::de::Error::custom("cannot deserialize `NonEmptySlice` from an empty sequence")
        })
    }
}

/// The nonempty equivalent of [`slice::from_raw_parts`].
#[allow(clippy::missing_safety_doc)]
#[must_use]
#[inline]
pub unsafe fn from_raw_parts<'a, T>(data: *const T, len: NonZeroUsize) -> &'a NonEmptySlice<T> {
    NonEmptySlice::new_unchecked(slice::from_raw_parts(data, len.get()))
}

/// The nonempty equivalent of [`slice::from_raw_parts_mut`].
#[allow(clippy::missing_safety_doc)]
#[must_use]
#[inline]
pub unsafe fn from_raw_parts_mut<'a, T>(data: *mut T, len: NonZeroUsize) -> &'a NonEmptySlice<T> {
    NonEmptySlice::new_mut_unchecked(slice::from_raw_parts_mut(data, len.get()))
}

/// Converts a reference to T into a slice of length 1 (without copying).
#[must_use]
#[inline]
pub const fn from_ref<T>(s: &T) -> &NonEmptySlice<T> {
    unsafe { NonEmptySlice::new_unchecked(slice::from_ref(s)) }
}

/// Converts a mutable reference to T into a mutable slice of length 1 (without
/// copying).
#[must_use]
#[inline]
pub fn from_mut<T>(s: &mut T) -> &mut NonEmptySlice<T> {
    unsafe { NonEmptySlice::new_mut_unchecked(slice::from_mut(s)) }
}
