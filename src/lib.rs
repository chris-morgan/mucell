//! A cell with the ability to mutate the value through an immutable reference when safe.
//!
//! # Comparison with `RefCell`
//!
//! `RefCell` goes for completely runtime checking, having `try_borrow`, `try_borrow_mut`,
//! `borrow` and `borrow_mut` all taking `&self` and using custom reference types everywhere.
//!
//! `MuCell` (out of pity and the fact that “non-ascii idents are not fully supported” I did not
//! name it `ΜCell` with the crate named `µcell`) makes much more use of true Rust borrow checking
//! for a result that is more efficient and has no possibility of panicking.
//!
//! However, its purpose is not the same as `RefCell`; it is designed specifically for cases where
//! something only *needs* an immutable reference, but where being able to safely take a mutable
//! reference can improve efficiency. Say, for example, where it’s beneficial to be able to cache
//! the result of a calculation, but you don’t really want to *need* to do that.
//!
//! The purpose of all of this is for an accessor for a `T` that can be made more efficient if it
//! can have `&mut self`, but doesn’t strictly require it. For this reason, it’s often going to be
//! paired with [`std::borrow::Cow`](http://doc.rust-lang.org/std/borrow/enum.Cow.html), e.g.
//! `Cow<str>` or `Cow<[T]>`, producing `Borrowed` if you are able to mutate the value or `Owned`
//! of the same data if not.
//!
//! # Examples
//!
//! This example covers most of the surface area of the library:
//!
//! ```rust
//! # use mucell::MuCell;
//! let mut cell = MuCell::new(vec![1, 2, 3]);
//!
//! // You can borrow from the cell mutably at no cost.
//! cell.borrow_mut().push(4);
//!
//! // You can borrow immutably, too, and it’s very cheap.
//! // (Rust’s standard borrow checking prevents you from doing
//! // this while there’s a mutable reference taken out.)
//! assert_eq!(&*cell.borrow(), &[1, 2, 3, 4]);
//!
//! // So long as there are no active borrows,
//! // try_mutate can be used to mutate the value.
//! assert!(cell.try_mutate(|x| x.push(5)));
//! assert_eq!(&*cell.borrow(), &[1, 2, 3, 4, 5]);
//!
//! // But when there is an immutable borrow active,
//! // try_mutate says no.
//! let b = cell.borrow();
//! assert!(!cell.try_mutate(|_| unreachable!()));
//! drop(b);
//!
//! // We can have many immutable borrows at a time, too.
//! {
//!     let a = cell.borrow();
//!     let b = cell.borrow();
//!     let c = cell.borrow();
//!     assert_eq!(&*a as *const Vec<i32>, &*b as *const Vec<i32>);
//! }
//!
//! // Once they’re all cleared, try_mutate is happy again.
//! assert!(cell.try_mutate(|x| x.push(6)));
//! assert_eq!(&*cell.borrow(), &[1, 2, 3, 4, 5, 6]);
//! ```
//!
//! Look at the examples in the repository for some slightly more practical (though still
//! typically contrived) examples.

#![cfg_attr(feature = "no_std", no_std)]
#![cfg_attr(feature = "no_std", feature(no_std, core, collections))]
#![cfg_attr(feature = "const_fn", feature(const_fn))]
#![warn(bad_style, unused, missing_docs)]

#[cfg(feature = "no_std")]
#[macro_use]
extern crate core;
#[cfg(all(feature = "no_std", not(test)))]
extern crate core as std;
// ^^^ Ick! Alas, core’s panic macro currently hardcodes ::core rather than using $crate.
#[cfg(feature = "no_std")]
extern crate collections;

#[cfg(all(feature = "no_std", test))]
extern crate std;

#[cfg(feature = "no_std")]
use std::marker::{Send, Sized};

use std::cell::{Cell, UnsafeCell};
use std::clone::Clone;
use std::cmp::{PartialEq, Eq, PartialOrd, Ord, Ordering};
use std::default::Default;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, Drop, FnOnce};
use std::option::Option;
use std::result::Result;

type BorrowFlag = usize;
const UNUSED: BorrowFlag = 0;
const WRITING: BorrowFlag = !0;

/// A cell with the ability to mutate the value through an immutable reference when safe.
pub struct MuCell<T: ?Sized> {
    borrow: Cell<BorrowFlag>,
    value: UnsafeCell<T>,
}

impl<T> MuCell<T> {
    /// Creates a `MuCell` containing `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mucell::MuCell;
    ///
    /// let c = MuCell::new(5);
    /// ```
    #[inline]
    #[cfg(not(feature = "const_fn"))]
    pub fn new(value: T) -> MuCell<T> {
        MuCell {
            value: UnsafeCell::new(value),
            borrow: Cell::new(UNUSED),
        }
    }

    /// Creates a `MuCell` containing `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mucell::MuCell;
    ///
    /// let c = MuCell::new(5);
    /// ```
    #[inline]
    #[cfg(feature = "const_fn")]
    pub const fn new(value: T) -> MuCell<T> {
        MuCell {
            value: UnsafeCell::new(value),
            borrow: Cell::new(UNUSED),
        }
    }

    /// Consumes the `MuCell`, returning the wrapped value.
    ///
    /// # Examples
    ///
    /// ```
    /// use mucell::MuCell;
    ///
    /// let c = MuCell::new(5);
    ///
    /// let five = c.into_inner();
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        // Since this function takes `self` (the `RefCell`) by value, the
        // compiler statically verifies that it is not currently borrowed.
        // Therefore the following assertion is just a `debug_assert!`.
        debug_assert!(self.borrow.get() == UNUSED);
        unsafe { self.value.into_inner() }
    }
}

impl<T: ?Sized> MuCell<T> {
    // Explicitly not implemented from RefCell is borrow_state.
    //
    // - Returning `Writing` would indicate you are in a `try_mutate` block, and so calling
    //   `borrow()` would panic, but you should definitely know that already.
    // - Returning `Reading` would indicate there are immutable borrows alive, and so calling
    //   `try_mutate()` would return `false`, but there’s no real value in knowing that.
    //
    // In short, there just doesn’t seem much point in providing it.

    /// Immutably borrows the wrapped value.
    ///
    /// The borrow lasts until the returned `Ref` exits scope.
    /// Multiple immutable borrows can be taken out at the same time.
    ///
    /// # Panics
    ///
    /// Panics if called inside the `try_mutate()` mutator function.
    /// But that’s generally a nonsensical thing to do, anyway, so just be sensible and you’re OK.
    #[inline]
    pub fn borrow(&self) -> Ref<&T> {
        Ref {
            _borrow: BorrowRef::new(&self.borrow),
            _value: unsafe { &*self.value.get() },
        }
    }

    /// Mutably borrows the wrapped value.
    ///
    /// Unlike `RefCell.borrow_mut`, this method lets Rust’s type system prevent aliasing
    /// and so cannot have anything go wrong. It is also, in consequence, completely free,
    /// unlike `RefCell` or `MuCell.borrow` which all have to keep track of borrows at runtime.
    #[inline]
    pub fn borrow_mut(&mut self) -> &mut T {
        unsafe { &mut *self.value.get() }
    }

    /// Mutate the contained object if possible.
    ///
    /// If any immutable references produced by calling `borrow()` are active,
    /// this will return false, not executing the function given.
    ///
    /// If there are no immutable references active,
    /// this will execute the mutator function and return true.
    ///
    /// The mutator function should not touch `self` (not that it would really
    /// make much sense to be touching it, anyway); most notably, you may not call `borrow` on
    /// `self` inside the mutator, which includes things like the `==` implementation which borrow
    /// the value briefly; while calling `try_mutate` inside it will just return false, calling
    /// `borrow` will panic.
    #[inline]
    pub fn try_mutate<F: FnOnce(&mut T)>(&self, mutator: F) -> bool {
        if self.borrow.get() == UNUSED {
            self.borrow.set(WRITING);
            mutator(unsafe { &mut *self.value.get() });
            self.borrow.set(UNUSED);
            true
        } else {
            false
        }
    }

    // Not implemented at present from RefCell: as_unsafe_cell. I don’t see the point of it,
    // but it can easily be added at a later date if desired.
}

struct BorrowRef<'b> {
    _borrow: &'b Cell<BorrowFlag>,
}

impl<'b> BorrowRef<'b> {
    #[inline]
    fn new(borrow: &'b Cell<BorrowFlag>) -> BorrowRef<'b> {
        match borrow.get() {
            WRITING => panic!("borrow() called inside try_mutate"),
            b => {
                borrow.set(b + 1);
                BorrowRef { _borrow: borrow }
            },
        }
    }
}

impl<'b> Drop for BorrowRef<'b> {
    #[inline]
    fn drop(&mut self) {
        let borrow = self._borrow.get();
        debug_assert!(borrow != WRITING && borrow != UNUSED);
        self._borrow.set(borrow - 1);
    }
}

impl<'b> Clone for BorrowRef<'b> {
    #[inline]
    fn clone(&self) -> BorrowRef<'b> {
        // Since this BorrowRef exists,
        // we know the borrow flag is not set to WRITING.
        let borrow = self._borrow.get();
        debug_assert!(borrow != WRITING && borrow != UNUSED);
        self._borrow.set(borrow + 1);
        BorrowRef { _borrow: self._borrow }
    }
}

/// An immutable reference to a `MuCell`.
/// Normally you should dereference to get at the object,
/// but after transformation with `Ref::map` or `Ref::filter_map`
/// you might instead use `.into_inner()`.
pub struct Ref<'b, T: 'b> {
    // FIXME #12808: strange name to try to avoid interfering with
    // field accesses of the contained type via Deref
    _value: T,
    _borrow: BorrowRef<'b>
}

impl<'b, T: Deref + 'b> Deref for Ref<'b, T> {
    type Target = T::Target;

    #[inline]
    fn deref(&self) -> &T::Target {
        &*self._value
    }
}

impl<'b, T: Clone> Ref<'b, T> {
    /// Copies a `Ref`.
    ///
    /// The `MuCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `Ref::clone(...)`.  A `Clone` implementation or a method would interfere
    /// with the widespread use of `r.borrow().clone()` to clone the contents of
    /// a `MuCell`.
    #[inline]
    pub fn clone(orig: &Ref<'b, T>) -> Ref<'b, T> {
        Ref {
            _value: orig._value.clone(),
            _borrow: orig._borrow.clone(),
        }
    }
}

impl<'b, T: 'static> Ref<'b, T> {
    /// Consumes the `Ref`, returning the wrapped value.
    ///
    /// The `'static` constraint on `T` is what makes this possible; there is no longer any need to
    /// keep the borrow alive, and so the `Ref` itself can be consumed while keeping the contained
    /// value.
    ///
    /// # Examples
    ///
    /// ```
    /// use mucell::{MuCell, Ref};
    /// use std::borrow::Cow;
    ///
    /// let c = MuCell::new("foo");
    ///
    /// let r1: Ref<Cow<str>> = Ref::map(c.borrow(), |s| Cow::from(*s));
    /// let r2: Ref<String> = Ref::map(r1, |s| s.into_owned());
    /// let string: String = r2.into_inner();
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self._value
    }
}

impl<'b, T> Ref<'b, T> {
    /// Make a new `Ref` for a component of the borrowed data.
    ///
    /// The `MuCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as `Ref::map(...)`.
    /// A method would interfere with methods of the same name on the contents
    /// of a `MuCell` used through `Deref`.
    ///
    /// # Example
    ///
    /// ```
    /// use mucell::{MuCell, Ref};
    ///
    /// let c = MuCell::new((5, 'b'));
    /// let b1: Ref<&(u32, char)> = c.borrow();
    /// let b2: Ref<&u32> = Ref::map(b1, |t| &t.0);
    /// assert_eq!(*b2, 5)
    /// ```
    #[inline]
    pub fn map<U, F>(orig: Ref<'b, T>, f: F) -> Ref<'b, U>
        where F: FnOnce(T) -> U
    {
        Ref {
            _value: f(orig._value),
            _borrow: orig._borrow,
        }
    }

    /// Make a new `Ref` for a optional component of the borrowed data, e.g. an
    /// enum variant.
    ///
    /// The `MuCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `Ref::filter_map(...)`.  A method would interfere with methods of the
    /// same name on the contents of a `MuCell` used through `Deref`.
    ///
    /// # Example
    ///
    /// ```
    /// use mucell::{MuCell, Ref};
    ///
    /// let c = MuCell::new(Ok(5));
    /// let b1: Ref<&Result<u32, ()>> = c.borrow();
    /// let b2: Ref<&u32> = Ref::filter_map(b1, |o| o.as_ref().ok()).unwrap();
    /// assert_eq!(*b2, 5)
    /// ```
    #[inline]
    pub fn filter_map<U, F>(orig: Ref<'b, T>, f: F) -> Option<Ref<'b, U>>
        where F: FnOnce(T) -> Option<U>
    {
        let borrow = orig._borrow;
        f(orig._value).map(move |new| Ref {
            _value: new,
            _borrow: borrow,
        })
    }
}

unsafe impl<T: ?Sized> Send for MuCell<T> where T: Send {}

impl<T: ?Sized + PartialEq> PartialEq for MuCell<T> {
    fn eq(&self, other: &MuCell<T>) -> bool {
        *self.borrow() == *other.borrow()
    }
}

impl<T: ?Sized + Eq> Eq for MuCell<T> { }

impl<T: PartialOrd> PartialOrd for MuCell<T> {
    fn partial_cmp(&self, other: &MuCell<T>) -> Option<Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }
}

impl<T: Ord> Ord for MuCell<T> {
    fn cmp(&self, other: &MuCell<T>) -> Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

impl<T: Default> Default for MuCell<T> {
    fn default() -> MuCell<T> {
        MuCell::new(Default::default())
    }
}

impl<T: Clone> Clone for MuCell<T> {
    fn clone(&self) -> MuCell<T> {
        MuCell::new(self.borrow().clone())
    }
}

macro_rules! impl_fmt {
    ($($trait_name:ident)*) => {$(
        impl<T: fmt::$trait_name> fmt::$trait_name for MuCell<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.borrow().fmt(f)
            }
        }
    )*}
}
impl_fmt!(Display Debug Octal LowerHex UpperHex Pointer Binary LowerExp UpperExp);

impl<T> Hash for MuCell<T> where T: Hash {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.borrow().hash(state)
    }
}

// RefCell doesn’t have PartialOrd, Ord, Hash or fmt::*. TODO: why not?

#[test]
#[should_panic]
fn test_borrow_in_try_mutate() {
    let a = MuCell::new(());
    a.try_mutate(|_| { let _ = a.borrow(); });
}

#[test]
fn test_try_mutate_in_try_mutate() {
    let a = MuCell::new(());
    assert!(a.try_mutate(|_| assert!(!a.try_mutate(|_| unreachable!()))));
}
