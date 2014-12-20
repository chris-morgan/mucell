//! A cell with the ability to mutate the value through an immutable reference when safe
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
//! `Cow<String, str>` (a.k.a. `std::str::CowString`) or `Cow<Vec<T>, [T]>` (a.k.a.
//! `std::vec::CowVec`), producing `Borrowed` if you are able to mutate the value or `Owned` of the
//! same data if not.
//!
//! # Examples
//!
//! This example covers most of the surface area of the library:
//!
//! ```rust
//! # use mucell::MuCell;
//! let mut cell = MuCell::new(vec![1i, 2, 3]);
//!
//! // You can borrow from the cell mutably at no cost.
//! cell.borrow_mut().push(4);
//!
//! // You can borrow immutably, too, and it’s very cheap.
//! // (Rust’s standard borrow checking prevents you from doing
//! // this while there’s a mutable reference taken out.)
//! assert_eq!(cell.borrow()[], [1, 2, 3, 4][]);
//!
//! // So long as there are no active borrows,
//! // try_mutate can be used to mutate the value.
//! assert!(cell.try_mutate(|x| x.push(5)));
//! assert_eq!(cell.borrow()[], [1, 2, 3, 4, 5][]);
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
//!     assert_eq!(&*a as *const _, &*b as *const _);
//! }
//!
//! // Once they’re all cleared, try_mutate is happy again.
//! assert!(cell.try_mutate(|x| x.push(6)));
//! assert_eq!(cell.borrow()[], [1, 2, 3, 4, 5, 6][]);
//! ```
//!
//! Look at the examples in the repository for some slightly more practical (though still
//! typically contrived) examples. Also see the <a class="macro" href="macro.mucell_ref_type!.html"
//! title="mucell::mucell_ref_type!">mucell_ref_type!</a> docs for an example of that part of the
//! library.

#![unstable = "almost stable, but not the macro parts"]
#![no_std]
#![feature(unsafe_destructor, macro_rules, phase, default_type_params)]
#![warn(bad_style, unused, missing_docs)]

#[phase(plugin, link)] extern crate core;
extern crate serialize;
extern crate rand;
extern crate collections;

#[cfg(test)] extern crate std;

use core::cell::{Cell, UnsafeCell};
use core::default::Default;
use core::fmt;
use core::kinds::marker;
use serialize::{Encoder, Decoder, Encodable, Decodable};
use rand::{Rand, Rng};
use core::hash::{Hash, sip};
use core::prelude::{Option, Clone, Result, PartialEq, Eq, PartialOrd, Ord, Ordering, Deref, Drop};

const MUTATING: uint = -1;

/// A cell with the ability to mutate the value through an immutable reference when safe
#[stable]
pub struct MuCell<T> {
    value: UnsafeCell<T>,
    borrows: Cell<uint>,
    nocopy: marker::NoCopy,
    noshare: marker::NoSync,
}

#[stable]
impl<T> MuCell<T> {
    /// Construct a new cell containing the given value
    #[inline]
    #[stable]
    pub fn new(value: T) -> MuCell<T> {
        MuCell {
            value: UnsafeCell::new(value),
            borrows: Cell::new(0),
            nocopy: marker::NoCopy,
            noshare: marker::NoSync,
        }
    }

    /// Borrow the contained object mutably.
    ///
    /// This is genuinely and completely free.
    #[inline]
    #[stable]
    pub fn borrow_mut(&mut self) -> &mut T {
        unsafe { &mut *self.value.get() }
    }

    /// Borrow the contained object immutably.
    ///
    /// Unlike `borrow_mut`, this isn’t *quite* free, but oh, so all but! It has a smattering of
    /// reference counting. No branches, though, so it’s as fast as is computationally possible.
    #[inline]
    #[stable]
    pub fn borrow(&self) -> Ref<T> {
        let borrows = self.borrows.get();
        debug_assert!(borrows != MUTATING);
        self.borrows.set(borrows + 1);
        Ref { _parent: self }
    }

    /// Mutate the contained object if possible.
    ///
    /// If any immutable references produced by calling `borrow()` are active,
    /// this will return false, not executing the function given.
    ///
    /// If there are no immutable references active,
    /// this will execute the mutator function and return true.
    ///
    /// **Caution:** you should avoid touching `self` inside the mutator (not that it would really
    /// make much sense to be touching it, anyway); most notably, you MUST NOT call `borrow` on
    /// `self` inside the mutator, which includes things like the `==` implementation which borrow
    /// the value briefly; while calling `try_mutate` inside it will just return false, in debug
    /// builds calling `borrow` will panic and in release builds it will break memory safety as you
    /// will have both a mutable and an immutable reference to the same object at the same time
    /// (yep, it’s not quite preventing aliasing). So don’t do it.
    #[inline]
    #[stable]
    pub fn try_mutate(&self, mutator: |&mut T|) -> bool {
        if self.borrows.get() == 0 {
            self.borrows.set(MUTATING);
            mutator(unsafe { &mut *self.value.get() });
            self.borrows.set(0);
            true
        } else {
            false
        }
    }
}

/// An immutable reference to a `MuCell`. Dereference to get at the object.
#[stable]
pub struct Ref<'a, T: 'a> {
    _parent: &'a MuCell<T>,
}

#[unsafe_destructor]
#[unstable = "trait is not stable"]
impl<'a, T: 'a> Drop for Ref<'a, T> {
    fn drop(&mut self) {
        self._parent.borrows.set(self._parent.borrows.get() - 1);
    }
}

#[unstable = "trait is not stable"]
impl<'a, T: 'a> Deref<T> for Ref<'a, T> {
    fn deref(&self) -> &T {
        unsafe { &*self._parent.value.get() }
    }
}

#[unstable = "trait is not stable"]
impl<T: PartialEq> PartialEq for MuCell<T> {
    fn eq(&self, other: &MuCell<T>) -> bool {
        *self.borrow() == *other.borrow()
    }
}

#[unstable = "trait is not stable"]
impl<T: Eq> Eq for MuCell<T> { }

#[unstable = "trait is not stable"]
impl<T: PartialOrd> PartialOrd for MuCell<T> {
    fn partial_cmp(&self, other: &MuCell<T>) -> Option<Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }
}

#[unstable = "trait is not stable"]
impl<T: Ord> Ord for MuCell<T> {
    fn cmp(&self, other: &MuCell<T>) -> Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

#[unstable = "trait is not stable"]
impl<T: Default> Default for MuCell<T> {
    fn default() -> MuCell<T> {
        MuCell::new(Default::default())
    }
}

#[unstable = "trait is not stable"]
impl<T: Clone> Clone for MuCell<T> {
    fn clone(&self) -> MuCell<T> {
        MuCell::new(self.borrow().clone())
    }
}

macro_rules! impl_fmt {
    ($($trait_name:ident)*) => {$(
        #[unstable = "trait is not stable"]
        impl<T: fmt::$trait_name> fmt::$trait_name for MuCell<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.borrow().fmt(f)
            }
        }
    )*}
}
impl_fmt!(Show Octal Binary LowerHex UpperHex Pointer LowerExp UpperExp);

#[unstable = "trait is not stable"]
impl<S: Encoder<E>, E, T: Encodable<S, E>> Encodable<S, E> for MuCell<T> {
    fn encode(&self, s: &mut S) -> Result<(), E> {
        self.borrow().encode(s)
    }
}

#[unstable = "trait is not stable"]
impl<D: Decoder<E>, E, T: Decodable<D, E>> Decodable<D, E> for MuCell<T> {
    fn decode(d: &mut D) -> Result<MuCell<T>, E> {
        Decodable::decode(d).map(|x| MuCell::new(x))
    }
}

#[unstable = "trait is not stable"]
impl<T: Rand> Rand for MuCell<T> {
    fn rand<R: Rng>(rng: &mut R) -> MuCell<T> {
        MuCell::new(Rand::rand(rng))
    }
}

#[unstable = "trait is not stable"]
impl<T: Hash<S>, S = sip::SipState> Hash<S> for MuCell<T> {
    fn hash(&self, state: &mut S) {
        self.borrow().hash(state)
    }
}

/// Create a new reference type to something inside the cell.
///
/// Why is this necesary? Because of the tracking of immutable references (`Ref<'a, T>` rather than
/// `&'a T`), anything from the object owning the original cell wishing to return a reference to
/// something inside the cell must go producing another such reference type like `Ref`, with its
/// own `Deref` implementation and so forth. (This is the cost of efficient memory safety!)
///
/// Here’s an example of usage:
///
/// ```rust
/// #![feature(phase)]
/// #[phase(plugin, link)] extern crate mucell;
/// use mucell::{MuCell, Ref};
///
/// struct Foo {
///     bar: String,
/// }
///
/// mucell_ref_type! {
///     #[doc = "…"]
///     struct BarRef<'a>(Foo)
///     impl Deref<str>
///     data: &'a str = |x| x.bar.as_slice()
/// }
///
/// fn pull_string_out(foo: &MuCell<Foo>) -> BarRef {
///     // Maybe pretend we did something like `try_mutate` here.
///
///     // We would not be able to return foo.borrow().bar.as_slice()
///     // here because the borrow() lifetime would be too short.
///     // So we use our fancy new ref type!
///     BarRef::from(foo)
/// }
///
/// fn say(s: &str) {
///     println!("The string is “{}”", s);
/// }
///
/// fn demo(foo: &MuCell<Foo>) {
///     say(&*pull_string_out(foo));
/// }
///
/// fn main() {
///     demo(&MuCell::new(Foo { bar: "panic".into_string() }));
/// }
/// ```
///
/// The `vector_munger` example demonstrates a more complex use case.
#[macro_export]
#[experimental]
macro_rules! mucell_ref_type {
    (
        $(#[$attr:meta])*  // suggestions: doc, stability markers
        struct $ref_name:ident<'a>($ty:ty)
        impl Deref<$deref:ty>
        data: $data_ty:ty = |$data_ident:ident| $data_expr:expr
    ) => {
        /// An immutable reference to a `MuCell`. Dereference to get at the object.
        $(#[$attr])*
        pub struct $ref_name<'a> {
            _parent: Ref<'a, $ty>,
            _data: $data_ty,
        }

        #[unstable = "still a little experimental, like the whole macro"]
        impl<'a> $ref_name<'a> {
            /// Construct a reference from the cell.
            #[unstable = "still a little experimental, like the whole macro"]
            fn from(cell: &'a MuCell<$ty>) -> $ref_name<'a> {
                let parent = cell.borrow();
                // This transmutation is to fix the lifetime of the reference so it is 'a rather
                // than the block. Because we keep the parent around in the struct, it’ll be OK;
                // even if the parent destructor is run before any data destructor and it does
                // silly things with any references, because we’re not Sync it doesn’t matter if
                // `borrows` is decremented early. We could just use `transmute(&*parent)` here,
                // but for a macro it’s nice to avoid depending on std or core being in a
                // particular place is of value. (Caring about efficiency? Unoptimised, this way is
                // slightly less efficient, optimised both are noops.)
                let $data_ident: &'a $ty = unsafe { &*(&*parent as *const $ty) };
                let data = $data_expr;
                $ref_name {
                    _parent: parent,
                    _data: data,
                }
            }
        }

        #[unstable = "trait is not stable"]
        impl<'a> Deref<$deref> for $ref_name<'a> {
            fn deref<'b>(&'b self) -> &'b $deref {
                &*self._data
            }
        }
    }
}

#[test]
#[should_fail]
fn test_borrow_in_try_mutate() {
    let a = MuCell::new(());
    a.try_mutate(|_| { let _ = a.borrow(); });
}

#[test]
fn test_try_mutate_in_try_mutate() {
    let a = MuCell::new(());
    assert!(a.try_mutate(|_| assert!(!a.try_mutate(|_| unreachable!()))));
}
