use crate::{imports::*, EmptyError, NonEmptySlice};

use core::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    mem::MaybeUninit,
    num::{NonZeroU8, NonZeroUsize},
    ops, ptr,
    slice::{self, SliceIndex},
};

/// A vector that is guaranteed to not be empty.
///
/// # [`Deref`](ops::Deref) Behavior
///
/// While [`NonEmptyVec<T>`] should be percieved as a smart pointer to a vector,
/// [`NonEmptyVec<T>`] **does not** dereference to a [`Vec<T>`]. Instead, it
/// dereferences to a [`NonEmptySlice<T>`], which dereferences to
/// [`[T]`](prim@slice). The vector methods present are manual implementations
/// or delegations that preserve the state of the non-empty vector.
///
/// # Layout
///
/// The layout of a [`NonEmptyVec<T>`] is *idential* to [`Vec<T>`].
///
/// # Caveats
///
/// Because [`NonEmptyVec<T>`] **does not** dereference to a vector, using one
/// as a [`&Vec<T>`](Vec) parameter will require the use of [`as_vec`] to
/// "dereference" the [`NonEmptyVec<T>`] as a [`&Vec<T>`](Vec). This is judged
/// as acceptable since [`&Vec<T>`](Vec) parameters are rare in the wild.
///
/// Also, while you **can not** collect a [`NonEmptyVec<T>`] using
/// [`Iterator::collect`], you **can** collect a [`NonEmptyVec<T>`] with the
/// aid of [`IteratorExt`].
///
/// However, unlike most other "not empty" libraries, all other interoperability
/// is remained intact without the need for a new interface. While the previous
/// two cases are incredibly minor, they still are worth listing and considering
/// before you adopt usage.
///
/// [`as_vec`]: NonEmptyVec::as_vec
/// [`IteratorExt`]: crate::iter::IteratorExt
///
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
#[repr(transparent)]
pub struct NonEmptyVec<T> {
    pub(crate) inner: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    /// This is an incredibly unsafe constructor.
    ///
    /// This creates an *empty* [`NonEmptyVec<T>`]... You understand the risks
    /// of that, right? If I could somehow write `unsafe unsafe`, it would be
    /// appropriate here.
    ///
    /// You **can not** use any methods inspecting the vector *until* you
    /// populate it with at least one element. To fail in doing so results in
    /// undefined behavior.
    ///
    /// Unlike [`NonEmptyVec::new_unchecked`], there's no debug assertion. For
    /// your sanity, I hope you know what you're doing.
    ///
    /// # Safety
    ///
    /// Using the non-empty vector before populating it is undefined behavior.
    ///
    /// # Examples
    ///
    /// Do not do this:
    ///
    /// ```should_panic
    /// use not_empty::NonEmptyVec;
    ///
    /// let empty_nonempty = unsafe { NonEmptyVec::<i32>::empty() };
    ///
    /// // Well, well, well. If it isn't the consequences of my actions.
    /// let first = empty_nonempty.first(); // signal 4 (SIGILL); illegal instruction
    /// ```
    ///
    /// This, however, is technically fine.
    ///
    /// ```
    /// extern crate alloc;
    ///
    /// use alloc::collections::TryReserveError;
    /// use not_empty::prelude::*;
    ///
    /// fn process_data(data: &NonEmptySlice<u32>) -> Result<NonEmptyVec<u32>, TryReserveError> {
    ///     let mut output = unsafe { NonEmptyVec::empty() };
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len().get())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&not_empty_vec![1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[must_use]
    #[inline]
    pub unsafe fn empty() -> Self {
        NonEmptyVec { inner: Vec::new() }
    }

    /// An incredibly unsafe constructor. Constructs a new, empty,
    /// [`NonEmptyVec<T>`] with at least the specified capacity.
    ///
    /// You **can not** use any methods inspecting the vector *until* you
    /// populate it with at least one element. To fail in doing so results in
    /// undefined behavior.
    ///
    /// For more information on capacity, refer to [`Vec::with_capacity`].
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds [`isize::MAX`] bytes.
    ///
    /// # Safety
    ///
    /// Using the non-empty vector before populating it is undefined behavior.
    ///
    /// # Examples
    ///
    /// Do not do this:
    ///
    /// ```should_panic
    /// use core::num::NonZeroUsize;
    /// use not_empty::NonEmptyVec;
    ///
    /// let ten = unsafe { NonZeroUsize::new_unchecked(10) };
    /// let empty_nonempty = unsafe { NonEmptyVec::<i32>::with_capacity(ten) };
    ///
    /// // Well, well, well. If it isn't the consequences of my actions.
    /// let first = empty_nonempty.first(); // signal 4 (SIGILL); illegal instruction
    /// ```
    ///
    /// This, however, is acceptable. However, be sure that it's absolutely
    /// required first.
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    /// use not_empty::NonEmptyVec;
    ///
    /// let ten = unsafe { NonZeroUsize::new_unchecked(10) };
    /// let mut nonempty = unsafe { NonEmptyVec::with_capacity(ten) };
    /// // Inspecting capacity is literally the only safe operation at this
    /// // point in the example.
    /// assert!(nonempty.capacity().get() >= 10);
    ///
    /// // These are all done without reallocating...
    /// for i in 1..=10 {
    ///     nonempty.push(i);
    /// }
    ///
    /// // Further inspection is now okay since elements have been added:
    /// assert_eq!(nonempty.len().get(), 10);
    /// assert!(nonempty.capacity().get() >= 10);
    ///
    /// // ... but this may make the vector reallocate
    /// nonempty.push(11);
    /// assert_eq!(nonempty.len().get(), 11);
    /// assert!(nonempty.capacity().get() >= 11);
    ///
    /// // A vector of a zero-sized type will always over-allocate, since no
    /// // allocation is necessary.
    /// let vec_units: NonEmptyVec<()> = unsafe { NonEmptyVec::with_capacity(ten) };
    /// assert_eq!(vec_units.capacity().get(), usize::MAX);
    /// ```
    #[must_use]
    #[inline]
    pub unsafe fn with_capacity(capacity: NonZeroUsize) -> Self {
        NonEmptyVec { inner: Vec::with_capacity(capacity.get()) }
    }

    /// Creates a new non-empty vector without checking if the given vector is
    /// not empty.
    ///
    /// This is a cost-free conversion.
    ///
    /// # Safety
    ///
    /// The vector must not be empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptyVec;
    ///
    /// let vec = vec![1, 2, 3];
    /// let nonempty: NonEmptyVec<_> = unsafe { NonEmptyVec::new_unchecked(vec) };
    /// ```
    ///
    /// For your convenience, consider using
    /// [`not_empty_vec!`](crate::not_empty_vec) instead:
    ///
    /// ```
    /// use not_empty::not_empty_vec;
    ///
    /// let nonempty = not_empty_vec![1, 2, 3];
    /// ```
    #[must_use]
    #[inline]
    #[track_caller]
    pub unsafe fn new_unchecked(vec: Vec<T>) -> Self {
        debug_assert!(
            !vec.is_empty(),
            "non-empty vector initialized with an empty vector"
        );
        NonEmptyVec { inner: vec }
    }

    /// Creates a new non-empty vector if the given vector is not empty.
    ///
    /// # Errors
    ///
    /// Returns an [`EmptyError`] if the given vector is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use not_empty::NonEmptyVec;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let vec = vec![1, 2, 3];
    /// let nonempty: NonEmptyVec<_> = NonEmptyVec::new(vec)?;
    /// assert!(nonempty.len().get() == 3);
    ///
    /// let empty: Vec<i32> = vec![];
    /// assert!(NonEmptyVec::new(empty).is_err());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn new(vec: Vec<T>) -> Result<Self, EmptyError> {
        (!vec.is_empty())
            .then(|| unsafe { NonEmptyVec::new_unchecked(vec) })
            .ok_or(EmptyError)
    }

    /// Creates a `NonEmptyVec<T>` directly from the raw components of another
    /// vector.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` needs to have been previously allocated via
    ///   [`String`]/[`Vec<T>`] (at least, it's highly likely to be incorrect
    ///   if it wasn't.)
    /// * `T` needs to have the same alignment as what `ptr` was allocated with.
    ///   (`T` having a less strict alignment is not sufficient, the alignment
    ///   really needs to be equal to satisfy the [`dealloc`] requirement that
    ///   memory must be allocated and deallocated with the same layout.)
    /// * The size of `T` times the `capacity` (ie. the allocated size in bytes)
    ///   needs to be the same size as the pointer was allocated with. (Because
    ///   similar to alignment, [`dealloc`] must be called with the same layout
    ///   `size`.)
    /// * `length` needs to be less than or equal to `capacity`.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is normally **not** safe
    /// to build a [`NonEmptyVec<u8>`] from a pointer to a C `char` array with
    /// length `size_t`, doing so is only safe if the array was initially
    /// allocated by a `Vec` or `String`. It's also not safe to build one from a
    /// `NonEmptyVec<u16>` and its length, because the allocator cares about the
    /// alignment, and these two types have different alignments. The buffer was
    /// allocated with alignment 2 (for `u16`), but after turning it into a
    /// `NonEmptyVec<u8>` it'll be deallocated with alignment 1. To avoid these
    /// issues, it is often preferable to do casting/transmuting using
    /// [`slice::from_raw_parts`](crate::slice::from_raw_parts) instead.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// [`NonEmptyVec<T>`] which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`dealloc`]: std::alloc::GlobalAlloc::dealloc
    #[must_use]
    #[inline]
    pub unsafe fn from_raw_parts(
        ptr: *mut T,
        length: NonZeroUsize,
        capacity: NonZeroUsize,
    ) -> Self {
        let vec = Vec::from_raw_parts(ptr, length.get(), capacity.get());
        NonEmptyVec::new_unchecked(vec)
    }

    /// Returns a reference to the underlying vector.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// fn needs_vec_ref(vec: &Vec<i32>) {
    ///     // ...
    /// }
    ///
    /// let nonempty = not_empty::vec![1, 2, 3];
    /// needs_vec_ref(nonempty.as_vec());
    /// ```
    #[must_use]
    #[inline]
    pub fn as_vec(&self) -> &Vec<T> {
        &self.inner
    }

    /// Converts the [`NonEmptyVec<T>`] back into a [`Vec<T>`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// fn needs_vec(vec: Vec<i32>) {
    ///     // ...
    /// }
    ///
    /// let nonempty = not_empty::vec![1, 2, 3];
    /// needs_vec(nonempty.into_vec());
    /// ```
    #[must_use]
    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }

    /// Returns the number of elements the vector can hold without reallocating.
    ///
    /// Unlike [`Vec::capacity`], this returns a [`NonZeroUsize`] instead of
    /// a [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// let nonempty = not_empty::vec![1, 2, 3];
    /// assert!(nonempty.capacity().get() == 3);
    /// ```
    #[must_use]
    #[inline]
    pub fn capacity(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.capacity()) }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `NonEmptyVec<T>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// For more information, refer to [`Vec::reserve`].
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut nonempty = not_empty::vec![1];
    /// nonempty.reserve(10);
    /// assert!(nonempty.capacity().get() >= 11);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to
    /// be inserted in the given `NonEmptyVec<T>`. Unlike [`reserve`], this will
    /// not deliberately over-allocate to speculatively avoid frequent
    /// allocations. After calling `reserve_exact`, capacity will be greater
    /// than or equal to `self.len() + additional`. Does nothing if the capacity
    /// is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`reserve`] if future insertions are expected.
    ///
    /// For more information, refer to [`Vec::reserve_exact`]
    ///
    /// [`reserve`]: NonEmptyVec::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut nonempty = not_empty::vec![1];
    /// nonempty.reserve_exact(10);
    /// assert!(nonempty.capacity().get() >= 11);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be
    /// inserted in the given `NonEmptyVec<T>`. The collection may reserve more
    /// space to speculatively avoid frequent reallocations. After calling
    /// `try_reserve`, capacity will be  greater than or equal to
    /// `self.len() + additional` if it returns `Ok(())`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// For more information, refer to [`Vec::try_reserve`].
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate alloc;
    /// use alloc::collections::TryReserveError;
    /// use not_empty::prelude::*;
    ///
    /// fn process_data(data: &NonEmptySlice<u32>) -> Result<NonEmptyVec<u32>, TryReserveError> {
    ///     let mut output = unsafe { NonEmptyVec::empty() };
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len().get())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&not_empty_vec![1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional`
    /// elements to be inserted in the given `Vec<T>`. Unlike [`try_reserve`],
    /// this will not deliberately over-allocate to speculatively avoid frequent
    /// allocations. After calling `try_reserve_exact`, capacity will be greater
    /// than or equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: NonEmptyVec::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate alloc;
    /// use alloc::collections::TryReserveError;
    /// use not_empty::prelude::*;
    ///
    /// fn process_data(data: &NonEmptySlice<u32>) -> Result<NonEmptyVec<u32>, TryReserveError> {
    ///     let mut output = unsafe { NonEmptyVec::empty() };
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len().get())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&not_empty_vec![1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the vector that there is space for a few more elements.
    ///
    /// For more information, refer to [`Vec::shrink_to_fit`].
    ///
    /// # Examples
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    /// use not_empty::NonEmptyVec;
    ///
    /// let mut nonempty = unsafe { NonEmptyVec::with_capacity(NonZeroUsize::new_unchecked(10)) };
    /// nonempty.extend([1, 2, 3]);
    /// assert_eq!(nonempty.capacity().get(), 10);
    /// nonempty.shrink_to_fit();
    /// assert!(nonempty.capacity().get() >= 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length and the
    /// supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// For more information, refer to [`Vec::shrink_to`].
    ///
    /// # Examples
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    /// use not_empty::NonEmptyVec;
    ///
    /// let mut nonempty = unsafe { NonEmptyVec::with_capacity(NonZeroUsize::new_unchecked(10)) };
    /// nonempty.extend([1, 2, 3]);
    /// assert_eq!(nonempty.capacity().get(), 10);
    ///
    /// nonempty.shrink_to(4);
    /// assert!(nonempty.capacity().get() >= 4);
    ///
    /// nonempty.shrink_to(0);
    /// assert!(nonempty.capacity().get() >= 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity);
    }

    /// Converts this [`NonEmptyVec<T>`] into [`Box<NonEmptySlice<T>>`].
    ///
    /// This will drop any excess capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let nonempty = not_empty::vec![1, 2, 3];
    /// let slice = nonempty.into_boxed_slice();
    /// ```
    ///
    /// Any excess capacity is removed:
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    /// use not_empty::{NonEmptySlice, NonEmptyVec};
    ///
    /// let mut nonempty = unsafe { NonEmptyVec::with_capacity(NonZeroUsize::new_unchecked(10)) };
    /// nonempty.extend([1, 2 ,3]);
    /// assert_eq!(nonempty.capacity().get(), 10);
    ///
    /// let slice: Box<NonEmptySlice<_>> = nonempty.into_boxed_slice();
    /// assert_eq!(slice.into_vec().capacity().get(), 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[must_use]
    #[inline]
    pub fn into_boxed_slice(self) -> Box<NonEmptySlice<T>> {
        let b = self.inner.into_boxed_slice();
        let raw = Box::into_raw(b) as *mut NonEmptySlice<T>;
        unsafe { Box::from_raw(raw) }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the
    /// rest.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// The [`drain`](NonEmptyVec::drain) method can emulate `truncate`, but
    /// causes the excess elements to be returned instead of dropped.
    ///
    /// This method has no effect on the allocated capacity of the vector.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    ///
    /// let mut vec = not_empty::vec![1, 2, 3, 4, 5];
    /// vec.truncate(unsafe { NonZeroUsize::new_unchecked(2) });
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// use core::num::NonZeroUsize;
    ///
    /// let mut vec = not_empty::vec![1, 2, 3];
    /// vec.truncate(unsafe { NonZeroUsize::new_unchecked(8) });
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    #[inline]
    pub fn truncate(&mut self, len: NonZeroUsize) {
        self.inner.truncate(len.get());
    }

    /// Extracts a [`NonEmptySlice`] containing the entire vector.
    #[must_use]
    #[inline]
    pub fn as_slice(&self) -> &NonEmptySlice<T> {
        unsafe { NonEmptySlice::new_unchecked(&self.inner) }
    }

    /// Extracts a mutable [`NonEmptySlice`] containing the entire vector.
    #[must_use]
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut NonEmptySlice<T> {
        unsafe { NonEmptySlice::new_mut_unchecked(&mut self.inner) }
    }

    /// Returns a raw pointer to the vector’s buffer, or a dangling raw pointer
    /// valid for zero sized reads if the vector didn’t allocate.
    ///
    /// For more information, refer to [`Vec::as_ptr`].
    #[must_use]
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.inner.as_ptr()
    }

    /// Returns an unsafe mutable pointer to the vector’s buffer, or a dangling
    /// raw pointer valid for zero sized reads if the vector didn’t allocate.
    ///
    /// For more information, refer to [`Vec::as_mut_ptr`].
    #[must_use]
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.as_mut_ptr()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// For more information, refer to [`Vec::set_len`].
    ///
    /// # Safety
    ///
    /// * `new_len` must be less than or equal to
    ///   [`capacity()`](NonEmptyVec::capacity).
    /// * The elements at `old_len..new_len` must be initialized.
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: NonZeroUsize) {
        debug_assert!(new_len < self.capacity());
        self.inner.set_len(new_len.get());
    }

    #[inline]
    #[track_caller]
    fn assert_nonempty(&self, method_name: &'static str) {
        #[cfg_attr(panic = "abort", inline)]
        #[cfg_attr(not(panic = "abort"), inline(never))]
        #[cold]
        #[track_caller]
        fn assert_failed(method_name: &'static str) {
            panic!("{method_name} left the NonEmptyVec empty");
        }

        if cfg!(debug_assertions) && self.inner.is_empty() {
            assert_failed(method_name);
        }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector..
    ///
    /// This does not preserve ordering, but is *O*(1). If you need to preserve
    /// the element order, use [`remove`](NonEmptyVec::remove) instead.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Safety
    ///
    /// This can not leave the [`NonEmptyVec`] empty. If it does, on debug
    /// builds, it will panic. Otherwise, it is undefined behavior. Consider
    /// whether or not a [`NonEmptyVec`] is really the right choice for your
    /// application.
    #[must_use]
    #[inline]
    #[track_caller]
    pub unsafe fn swap_remove(&mut self, index: usize) -> T {
        let element = self.inner.swap_remove(index);
        self.assert_nonempty("swap_remove");
        element
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// For more information, refer to [`Vec::insert`].
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    #[track_caller]
    pub fn insert(&mut self, index: usize, element: T) {
        self.inner.insert(index, element);
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// Because this shifts over the remaining elements, it has a worst-case
    /// performance of *O*(*n*). If you don't need the order of elements
    /// to be preserved, use [`swap_remove`](NonEmptyVec::swap_remove) instead.
    ///
    /// For more information, refer to [`Vec::swap_remove`].
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Safety
    ///
    /// This can not leave the [`NonEmptyVec`] empty. If it does, on debug
    /// builds, it will panic. Otherwise, it is undefined behavior. Consider
    /// whether or not a [`NonEmptyVec`] is really the right choice for your
    /// application.
    #[must_use]
    #[inline]
    #[track_caller]
    pub unsafe fn remove(&mut self, index: usize) -> T {
        let element = self.inner.remove(index);
        self.assert_nonempty("remove");
        element
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// For more information, refer to [`Vec::retain`].
    ///
    /// # Safety
    ///
    /// This can not leave the [`NonEmptyVec`] empty. If it does, on debug
    /// builds, it will panic. Otherwise, it is undefined behavior. Consider
    /// whether or not a [`NonEmptyVec`] is really the right choice for your
    /// application.
    #[inline]
    #[track_caller]
    pub unsafe fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.inner.retain(f);
        self.assert_nonempty("retain");
    }

    /// Retains only the elements specified by the predicate, passing a mutable
    /// reference to it.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns
    /// `false`. This method operates in place, visiting each element exactly
    /// once in the original order, and preserves the order of the retained
    /// elements.
    ///
    /// For more information, refer to [`Vec::retain_mut`].
    ///
    /// # Safety
    ///
    /// This can not leave the [`NonEmptyVec`] empty. If it does, on debug
    /// builds, it will panic. Otherwise, it is undefined behavior. Consider
    /// whether or not a [`NonEmptyVec`] is really the right choice for your
    /// application.
    #[inline]
    #[track_caller]
    pub unsafe fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        self.inner.retain_mut(f);
        self.assert_nonempty("retain_mut");
    }

    /// Removes all but the first of consecutive elements in the vector that
    /// resolve to the same key.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// For more information, refer to [`Vec::dedup_by_key`].
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.inner.dedup_by_key(key);
    }

    /// Removes all but the first of consecutive elements in the vector
    /// satisfying a given equality relation.
    ///
    /// The `same_bucket` function is passed references to two elements from the
    /// vector and must determine if the elements compare equal. The elements
    /// are passed in opposite order from their order in the slice, so if
    /// `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// For more information, refer to [`Vec::dedup_by`].
    #[inline]
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        self.inner.dedup_by(same_bucket);
    }

    /// Appends an element to the back of a collection.
    ///
    /// For more information, refer to [`Vec::push`].
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds [`isize::MAX`] bytes.
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    #[track_caller]
    pub fn push(&mut self, value: T) {
        self.inner.push(value);
    }

    /// Removes the last element from a vector and returns it.
    ///
    /// Unlike [`Vec::pop`], this is never an [`Option`].
    ///
    /// # Safety
    ///
    /// This can not leave the [`NonEmptyVec`] empty. If it does, on debug
    /// builds, it will panic. Otherwise, it is undefined behavior. Consider
    /// whether or not a [`NonEmptyVec`] is really the right choice for your
    /// application.
    #[inline]
    #[track_caller]
    pub unsafe fn pop(&mut self) -> T {
        let element = self.inner.pop().unwrap_unchecked();
        self.assert_nonempty("pop");
        element
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// For more information, refer to [`Vec::append`].
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    #[track_caller]
    pub fn append(&mut self, other: &mut Vec<T>) {
        self.inner.append(other);
    }

    /// Removes the specified range from the vector in bulk, returning all
    /// removed elements as an iterator. If the iterator is dropped before
    /// being fully consumed, it drops the remaining removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Safety
    ///
    /// This can not leave the [`NonEmptyVec`] empty. If it does, on debug
    /// builds, it will panic. Otherwise, it is undefined behavior. Consider
    /// whether or not a [`NonEmptyVec`] is really the right choice for your
    /// application.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the vector may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    #[inline]
    #[track_caller]
    pub unsafe fn drain<R>(&mut self, range: R) -> vec::Drain<'_, T>
    where
        R: ops::RangeBounds<usize>,
    {
        // TODO: Use slice::range once stable
        #[must_use]
        #[track_caller]
        fn slice_range_hack<R>(range: R, bounds: ops::RangeTo<usize>) -> ops::Range<usize>
        where
            R: ops::RangeBounds<usize>,
        {
            #[cfg_attr(panic = "abort", inline)]
            #[cfg_attr(not(panic = "abort"), inline(never))]
            #[cold]
            #[track_caller]
            const fn slice_start_index_overflow_fail() -> ! {
                panic!("attempted to index slice from after maximum usize");
            }

            #[cfg_attr(panic = "abort", inline)]
            #[cfg_attr(not(panic = "abort"), inline(never))]
            #[cold]
            #[track_caller]
            const fn slice_end_index_overflow_fail() -> ! {
                panic!("attempted to index slice up to maximum usize");
            }

            #[cfg_attr(panic = "abort", inline)]
            #[cfg_attr(not(panic = "abort"), inline(never))]
            #[cold]
            #[track_caller]
            const fn slice_index_order_fail() -> ! {
                panic!("slice index start is larger than end");
            }
            #[cfg_attr(panic = "abort", inline)]
            #[cfg_attr(not(panic = "abort"), inline(never))]
            #[cold]
            #[track_caller]
            const fn slice_end_index_len_fail() -> ! {
                panic!("slice end index is out of range for slice");
            }

            let len = bounds.end;
            let start = match range.start_bound() {
                ops::Bound::Included(&n) => n,
                ops::Bound::Excluded(&n) => n
                    .checked_add(1)
                    .unwrap_or_else(|| slice_start_index_overflow_fail()),
                ops::Bound::Unbounded => 0,
            };
            let end = match range.end_bound() {
                ops::Bound::Included(&n) => n
                    .checked_add(1)
                    .unwrap_or_else(|| slice_end_index_overflow_fail()),
                ops::Bound::Excluded(&n) => n,
                ops::Bound::Unbounded => len,
            };

            if start > end {
                slice_index_order_fail();
            }
            if end > len {
                slice_end_index_len_fail();
            }

            ops::Range { start, end }
        }

        #[cfg_attr(panic = "abort", inline)]
        #[cfg_attr(not(panic = "abort"), inline(never))]
        #[cold]
        #[track_caller]
        const fn assert_failed() -> ! {
            panic!("attempted to drain the entire vector");
        }

        let len = self.inner.len();
        let normalized_range = slice_range_hack(range, ..len);

        if cfg!(debug_assertions)
            && normalized_range.start == 0
            && normalized_range.end == (len - 1)
        {
            assert_failed();
        }

        self.inner.drain(normalized_range)
    }

    /// Returns the number of elements in the vector, also referred to as its
    /// 'length'.
    ///
    /// Unlike [`Vec::len`], this returrns a [`NonZeroUsize`].
    ///
    /// For more information, refer to [`Vec::len`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let a = not_empty::vec![1, 2, 3];
    /// assert_eq!(a.len().get(), 3);
    /// ```
    #[must_use]
    #[inline]
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.inner.len()) }
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing the elements in the range
    /// `[at, len)`. After the call, the original vector will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// Unlike [`Vec::split_off`], it's impossible to split at index zero.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    #[inline]
    #[track_caller]
    pub fn split_off(&mut self, at: NonZeroUsize) -> Vec<T> {
        self.inner.split_off(at.get())
    }

    /// Resizes the `NonEmptyVec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `NonEmptyVec` is extended by the
    /// difference, with each additional slot filled with the result of
    /// calling the closure `f`. The return values from `f` will end up
    /// in the `NonEmptyVec` in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, the `NonEmptyVec` is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If
    /// you'd rather [`Clone`] a given value, use [`NonEmptyVec::resize`]. If
    /// you want to use the [`Default`] trait to generate values, you can
    /// pass [`Default::default`] as the second argument.
    ///
    /// For more information, refer to [`Vec::resize_with`].
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn resize_with<F>(&mut self, new_len: NonZeroUsize, f: F)
    where
        F: FnMut() -> T,
    {
        self.inner.resize_with(new_len.get(), f);
    }

    /// Consumes and leaks the `NonEmptyVec`, returning a mutable reference to
    /// the contents, `&'a mut NonEmptySlice<T>`. Note that the type `T` must
    /// outlive the chosen lifetime `'a`. If the type has only static
    /// references, or none at all, then this may be chosen to be `'static`.
    ///
    /// As of Rust 1.57, this method does not reallocate or shrink the
    /// `NonEmptyVec`, so the leaked allocation may include unused capacity that
    /// is not part of the returned slice.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak.
    ///
    /// For more information, refer to [`Vec::leak`].
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[must_use]
    #[inline]
    pub fn leak<'a>(self) -> &'a mut NonEmptySlice<T> {
        unsafe { NonEmptySlice::new_mut_unchecked(self.inner.leak()) }
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// For more information, refer to [`Vec::spare_capacity_mut`].
    #[must_use]
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self.inner.spare_capacity_mut()
    }
}

impl<T: Clone> NonEmptyVec<T> {
    /// Resizes the `NonEmptyVec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `NonEmptyVec` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, the `NonEmptyVec` is simply truncated.
    ///
    /// This method requires `T` to implement [`Clone`],
    /// in order to be able to clone the passed value.
    /// If you need more flexibility (or want to rely on [`Default`] instead of
    /// [`Clone`]), use [`NonEmptyVec::resize_with`].
    /// If you only need to resize to a smaller size, use
    /// [`NonEmptyVec::truncate`].
    ///
    /// For more information, refer to [`Vec::resize`].
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn resize(&mut self, new_len: NonZeroUsize, value: T) {
        self.inner.resize(new_len.get(), value);
    }

    /// Clones and appends all elements in a slice to the `NonEmptyVec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `NonEmptyVec`. The `other` slice is traversed in-order.
    ///
    /// Note that this function is same as [`extend`] except that it is
    /// specialized to work with slices instead. If and when Rust gets
    /// specialization this function will likely be deprecated (but still
    /// available).
    ///
    /// For more information, refer to [`Vec::extend_from_slice`].
    ///
    /// [`extend`]: NonEmptyVec::extend
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.inner.extend_from_slice(other);
    }

    /// Copies elements from `src` range to the end of the vector.
    ///
    /// For more information, refer to [`Vec::extend_from_within`].
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    #[cfg(not(no_global_oom_handling))]
    #[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
    #[inline]
    #[track_caller]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: ops::RangeBounds<usize>,
    {
        self.inner.extend_from_within(src);
    }
}

impl<T: PartialEq> NonEmptyVec<T> {
    /// Removes consecutive repeated elements in the vector according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// For more information, refer to [`Vec::dedup`].
    #[inline]
    pub fn dedup(&mut self) {
        self.inner.dedup();
    }
}

////////////////////////////////////////////////////////////////////////////////
// Formatting
////////////////////////////////////////////////////////////////////////////////

impl<T> fmt::Debug for NonEmptyVec<T>
where
    T: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Cloning
////////////////////////////////////////////////////////////////////////////////

impl<T> Clone for NonEmptyVec<T>
where
    T: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        let vec = self.inner.clone();
        unsafe { NonEmptyVec::new_unchecked(vec) }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.inner.clone_from(&source.inner);
    }
}

////////////////////////////////////////////////////////////////////////////////
// Dereferencing
////////////////////////////////////////////////////////////////////////////////

impl<T> ops::Deref for NonEmptyVec<T> {
    type Target = NonEmptySlice<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> ops::DerefMut for NonEmptyVec<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

////////////////////////////////////////////////////////////////////////////////
// `as_*` traits
////////////////////////////////////////////////////////////////////////////////

impl<T> AsRef<[T]> for NonEmptyVec<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice().as_ref()
    }
}

impl<T> AsMut<[T]> for NonEmptyVec<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice().as_mut()
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> AsRef<NonEmptySlice<T>> for NonEmptyVec<T> {
    #[inline]
    fn as_ref(&self) -> &NonEmptySlice<T> {
        self.as_slice()
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> AsMut<NonEmptySlice<T>> for NonEmptyVec<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut NonEmptySlice<T> {
        self.as_mut_slice()
    }
}

impl<T> AsRef<Vec<T>> for NonEmptyVec<T> {
    #[inline]
    fn as_ref(&self) -> &Vec<T> {
        &self.inner
    }
}

////////////////////////////////////////////////////////////////////////////////
// `borrow` implementations
////////////////////////////////////////////////////////////////////////////////

impl<T> Borrow<[T]> for NonEmptyVec<T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<T> BorrowMut<[T]> for NonEmptyVec<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> Borrow<NonEmptySlice<T>> for NonEmptyVec<T> {
    #[inline]
    fn borrow(&self) -> &NonEmptySlice<T> {
        self
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> BorrowMut<NonEmptySlice<T>> for NonEmptyVec<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut NonEmptySlice<T> {
        self
    }
}

////////////////////////////////////////////////////////////////////////////////
// Index operations
////////////////////////////////////////////////////////////////////////////////

impl<T, I> ops::Index<I> for NonEmptyVec<T>
where
    I: SliceIndex<[T]>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(&self.inner, index)
    }
}

impl<T, I> ops::IndexMut<I> for NonEmptyVec<T>
where
    I: SliceIndex<[T]>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(&mut self.inner, index)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Iterator traits
////////////////////////////////////////////////////////////////////////////////

#[cfg(not(no_global_oom_handling))]
#[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
impl<'a, T> Extend<&'a T> for NonEmptyVec<T>
where
    T: 'a + Copy,
{
    #[inline]
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

#[cfg(not(no_global_oom_handling))]
#[cfg_attr(doc_cfg, doc(cfg(not(no_global_oom_handling))))]
impl<T> Extend<T> for NonEmptyVec<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

impl<'a, T> IntoIterator for &'a NonEmptyVec<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut NonEmptyVec<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> IntoIterator for NonEmptyVec<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

////////////////////////////////////////////////////////////////////////////////
/// Collection equivalence
////////////////////////////////////////////////////////////////////////////////

impl<T, U> PartialEq<VecDeque<U>> for NonEmptyVec<T>
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

impl<T, U> PartialEq<NonEmptyVec<U>> for VecDeque<T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &NonEmptyVec<U>) -> bool {
        self == &other.inner
    }
}

impl<T, U> PartialEq<NonEmptyVec<U>> for NonEmptyVec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptyVec<U>) -> bool {
        self.inner == other.inner
    }
}

impl<T, U> PartialEq<Vec<U>> for NonEmptyVec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &Vec<U>) -> bool {
        &self.inner == other
    }
}

impl<T, U> PartialEq<NonEmptyVec<U>> for Vec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptyVec<U>) -> bool {
        self == &other.inner
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, U> PartialEq<NonEmptySlice<U>> for NonEmptyVec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptySlice<U>) -> bool {
        self.as_slice() == other
    }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T, U> PartialEq<NonEmptyVec<U>> for NonEmptySlice<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptyVec<U>) -> bool {
        self == other.as_slice()
    }
}

impl<T, U> PartialEq<[U]> for NonEmptyVec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &[U]) -> bool {
        self.inner == other
    }
}

impl<T, U> PartialEq<NonEmptyVec<U>> for [T]
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptyVec<U>) -> bool {
        self == other.inner
    }
}

impl<T, U, const N: usize> PartialEq<[U; N]> for NonEmptyVec<T>
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &[U; N]) -> bool {
        self.inner == other
    }
}

impl<T, U, const N: usize> PartialEq<NonEmptyVec<U>> for [T; N]
where
    T: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &NonEmptyVec<U>) -> bool {
        // Workaround for yet another asymmetric PartialEq implementation
        self == other.as_slice()
    }
}

impl<T> Eq for NonEmptyVec<T> where T: Eq {}

impl<T> PartialOrd for NonEmptyVec<T>
where
    T: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.inner, &other.inner)
    }
}

impl<T> Ord for NonEmptyVec<T>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&self.inner, &other.inner)
    }
}

impl<T> Hash for NonEmptyVec<T>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
    }
}

////////////////////////////////////////////////////////////////////////////////
// NonEmptyVec -> smart pointer holding a head-allocated slice
////////////////////////////////////////////////////////////////////////////////

impl<T> From<NonEmptyVec<T>> for Arc<[T]> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        Arc::from(value.inner)
    }
}

impl<T> From<NonEmptyVec<T>> for Box<[T]> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        value.inner.into_boxed_slice()
    }
}

impl<'a, T> From<&'a NonEmptyVec<T>> for Cow<'a, [T]>
where
    T: Clone,
{
    #[inline]
    fn from(v: &'a NonEmptyVec<T>) -> Self {
        Cow::Borrowed(v)
    }
}

impl<T> From<NonEmptyVec<T>> for Rc<[T]> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        Rc::from(value.inner)
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> From<NonEmptyVec<T>> for Arc<NonEmptySlice<T>> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        let arc: Arc<[T]> = Arc::from(value);
        let ptr = Arc::into_raw(arc) as *const NonEmptySlice<T>;
        unsafe { Arc::from_raw(ptr) }
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> From<NonEmptyVec<T>> for Box<NonEmptySlice<T>> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        value.into_boxed_slice()
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<'a, T> From<&'a NonEmptyVec<T>> for Cow<'a, NonEmptySlice<T>>
where
    T: Clone,
{
    #[inline]
    fn from(v: &'a NonEmptyVec<T>) -> Self {
        Cow::Borrowed(v)
    }
}

#[cfg_attr(doc_cfg, doc(cfg(any(feature = "alloc", feature = "std"))))]
impl<T> From<NonEmptyVec<T>> for Rc<NonEmptySlice<T>> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        let rc: Rc<[T]> = Rc::from(value);
        let ptr = Rc::into_raw(rc) as *const NonEmptySlice<T>;
        unsafe { Rc::from_raw(ptr) }
    }
}

////////////////////////////////////////////////////////////////////////////////
// NonEmptyVec -> collections
////////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl From<NonEmptyVec<NonZeroU8>> for CString {
    #[inline]
    fn from(value: NonEmptyVec<NonZeroU8>) -> Self {
        CString::from(value.inner)
    }
}

impl<T> From<NonEmptyVec<T>> for Vec<T> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        value.inner
    }
}

impl<T> From<NonEmptyVec<T>> for VecDeque<T> {
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        VecDeque::from(value.inner)
    }
}

impl<T> From<NonEmptyVec<T>> for BinaryHeap<T>
where
    T: Ord,
{
    #[inline]
    fn from(value: NonEmptyVec<T>) -> Self {
        BinaryHeap::from(value.inner)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Failable conversions: collections -> NonEmptyVec
////////////////////////////////////////////////////////////////////////////////

impl<T> TryFrom<&[T]> for NonEmptyVec<T>
where
    T: Clone,
{
    type Error = EmptyError;

    #[inline]
    fn try_from(value: &[T]) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

impl<T> TryFrom<&mut [T]> for NonEmptyVec<T>
where
    T: Clone,
{
    type Error = EmptyError;

    #[inline]
    fn try_from(value: &mut [T]) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

impl<'a, T> TryFrom<Cow<'a, [T]>> for NonEmptyVec<T>
where
    [T]: ToOwned<Owned = Vec<T>>,
{
    type Error = EmptyError;

    fn try_from(value: Cow<'a, [T]>) -> Result<Self, Self::Error> {
        let vec = value.into_owned();
        NonEmptyVec::new(vec)
    }
}

impl TryFrom<&str> for NonEmptyVec<u8> {
    type Error = EmptyError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

impl TryFrom<String> for NonEmptyVec<u8> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: String) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl TryFrom<CString> for NonEmptyVec<u8> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: CString) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

impl<T> TryFrom<Vec<T>> for NonEmptyVec<T> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value)
    }
}

impl<T> TryFrom<VecDeque<T>> for NonEmptyVec<T> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: VecDeque<T>) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

impl<T> TryFrom<BinaryHeap<T>> for NonEmptyVec<T> {
    type Error = EmptyError;

    #[inline]
    fn try_from(value: BinaryHeap<T>) -> Result<Self, Self::Error> {
        NonEmptyVec::new(value.into())
    }
}

////////////////////////////////////////////////////////////////////////////////
/// Failable conversions: non-empty vector -> X
////////////////////////////////////////////////////////////////////////////////

impl<T, const N: usize> TryFrom<NonEmptyVec<T>> for [T; N] {
    type Error = NonEmptyVec<T>;

    fn try_from(mut value: NonEmptyVec<T>) -> Result<Self, Self::Error> {
        if value.inner.len() != N {
            return Err(value);
        }

        // SAFETY: `.set_len(0)` is always sound. Also, the contract of the
        // newtype is invalidated, but since it drops here it's no issue.
        unsafe { value.inner.set_len(0) };

        // SAFETY: A `Vec`'s pointer is always aligned properly, and the
        // alignment the array needs is the same as the items. It's already
        // known that there's enough items. The items will not double-drop as
        // the `set_len` tells the `Vec` not to also drop them.
        let array = unsafe { ptr::read(value.as_ptr().cast::<[T; N]>()) };
        Ok(array)
    }
}

////////////////////////////////////////////////////////////////////////////////
// `io` implementations
////////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl Write for NonEmptyVec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        Write::write(&mut self.inner, buf)
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
        Write::write_vectored(&mut self.inner, bufs)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        Write::write_all(&mut self.inner, buf)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Write::flush(&mut self.inner)
    }
}

////////////////////////////////////////////////////////////////////////////////
// `serde` implementations
////////////////////////////////////////////////////////////////////////////////

#[cfg(feature = "serde")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "serde")))]
impl<T> serde::Serialize for NonEmptyVec<T>
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

#[cfg(all(feature = "serde", not(no_global_oom_handling)))]
#[cfg_attr(doc_cfg, doc(cfg(all(feature = "serde", not(no_global_oom_handling)))))]
impl<'de, T> serde::Deserialize<'de> for NonEmptyVec<T>
where
    T: serde::Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let vec: Vec<T> = serde::Deserialize::deserialize(deserializer)?;
        NonEmptyVec::new(vec).map_err(|_| {
            serde::de::Error::custom("cannot deserialize `NonEmptyVec` from an empty sequence")
        })
    }
}
