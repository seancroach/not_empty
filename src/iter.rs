use crate::{EmptyError, NonEmptyVec};

/// Extends [`Iterator`] with methods for collecting [`NonEmptyVec`]s as a
/// stop-gap to retain a failable [`Iterator::collect`] functionality.
///
/// Unlike [`Iterator::collect`], the use of the turbofish operator is likely
/// not required as the method only collects into a [`NonEmptyVec`].
pub trait IteratorExt: Iterator {
    /// Transforms an iterator into a [`NonEmptyVec<Self::Item>`] without
    /// validating if the iterator has items.
    ///
    /// If you're not certain that the iterator won't be empty, use
    /// [`IteratorExt::collect_nonempty`] instead.
    ///
    /// # Safety
    ///
    /// The iterator must not be empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use not_empty::{IteratorExt, NonEmptyVec};
    ///
    /// let array = [1, 2, 3];
    ///
    /// unsafe {
    ///     let doubled = array
    ///         .iter()
    ///         .map(|&x| x * 2)
    ///         .collect_nonempty_unchecked();
    ///     assert_eq!(doubled, not_empty::vec![2, 4, 6]);
    /// }
    /// ```
    #[cfg(all(any(feature = "alloc", feature = "std"), not(no_global_oom_handling)))]
    #[cfg_attr(
        doc_cfg,
        doc(cfg(all(any(feature = "alloc", feature = "std"), not(no_global_oom_handling))))
    )]
    #[inline]
    #[must_use = "if you really need to exhaust the iterator, consider `.for_each(drop)` instead"]
    #[track_caller]
    unsafe fn collect_nonempty_unchecked(self) -> NonEmptyVec<Self::Item>
    where
        Self: Sized,
    {
        let vec = self.collect();
        NonEmptyVec::new_unchecked(vec)
    }

    /// Transforms an iterator into a [`NonEmptyVec<Self::Item>`].
    ///
    /// # Errors
    ///
    /// Returns an [`EmptyError`] if the iterator yields no values.
    ///
    /// # Examples
    ///
    /// ```
    /// use not_empty::IteratorExt;
    ///
    /// # fn main() -> Result<(), not_empty::EmptyError> {
    /// let array = [1, 2, 3];
    /// let doubled = array.iter().map(|&x| x * 2).collect_nonempty()?;
    /// assert_eq!(doubled, not_empty::vec![2, 4, 6]);
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(all(any(feature = "alloc", feature = "std"), not(no_global_oom_handling)))]
    #[cfg_attr(
        doc_cfg,
        doc(cfg(all(any(feature = "alloc", feature = "std"), not(no_global_oom_handling))))
    )]
    #[inline]
    #[must_use = "if you really need to exhaust the iterator, consider `.for_each(drop)` instead"]
    fn collect_nonempty(self) -> Result<NonEmptyVec<Self::Item>, EmptyError>
    where
        Self: Sized,
    {
        let vec = self.collect();
        NonEmptyVec::new(vec)
    }
}

impl<I> IteratorExt for I where I: Iterator {}
