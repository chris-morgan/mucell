mucell 0.1.10
=============

[![Build Status](https://travis-ci.org/chris-morgan/mucell.svg?branch=master)](https://travis-ci.org/chris-morgan/mucell)

<!-- The rest of this section comes straight from the crate docs. -->

A cell with the ability to mutate the value through an immutable reference when safe.

## Comparison with `RefCell`

`RefCell` goes for completely runtime checking, having `try_borrow`, `try_borrow_mut`,
`borrow` and `borrow_mut` all taking `&self` and using custom reference types everywhere.

`MuCell` (out of pity and the fact that “non-ascii idents are not fully supported” I did not
name it `ΜCell` with the crate named `µcell`) makes much more use of true Rust borrow checking
for a result that is more efficient and has no possibility of panicking.

However, its purpose is not the same as `RefCell`; it is designed specifically for cases where
something only *needs* an immutable reference, but where being able to safely take a mutable
reference can improve efficiency. Say, for example, where it’s beneficial to be able to cache
the result of a calculation, but you don’t really want to *need* to do that.

The purpose of all of this is for an accessor for a `T` that can be made more efficient if it
can have `&mut self`, but doesn’t strictly require it. For this reason, it’s often going to be
paired with [`std::borrow::Cow`](http://doc.rust-lang.org/std/borrow/enum.Cow.html), e.g.
`Cow<String, str>` (a.k.a. `std::str::CowString`) or `Cow<Vec<T>, [T]>` (a.k.a.
`std::vec::CowVec`), producing `Borrowed` if you are able to mutate the value or `Owned` of the
same data if not.

## Examples

This example covers most of the surface area of the library:

```rust
# use mucell::MuCell;
let mut cell = MuCell::new(vec![1i, 2, 3]);

// You can borrow from the cell mutably at no cost.
cell.borrow_mut().push(4);

// You can borrow immutably, too, and it’s very cheap.
// (Rust’s standard borrow checking prevents you from doing
// this while there’s a mutable reference taken out.)
assert_eq!(&cell.borrow()[], &[1, 2, 3, 4][]);

// So long as there are no active borrows,
// try_mutate can be used to mutate the value.
assert!(cell.try_mutate(|x| x.push(5)));
assert_eq!(&cell.borrow()[], &[1, 2, 3, 4, 5][]);

// But when there is an immutable borrow active,
// try_mutate says no.
let b = cell.borrow();
assert!(!cell.try_mutate(|_| unreachable!()));
drop(b);

// We can have many immutable borrows at a time, too.
{
    let a = cell.borrow();
    let b = cell.borrow();
    let c = cell.borrow();
    assert_eq!(&*a as *const _, &*b as *const _);
}

// Once they’re all cleared, try_mutate is happy again.
assert!(cell.try_mutate(|x| x.push(6)));
assert_eq!(&cell.borrow()[], &[1, 2, 3, 4, 5, 6][]);
```

Look at the examples in the repository for some slightly more practical (though still
typically contrived) examples. Also see the
`mucell_ref_type!` docs for an example of that part of the
library.

Usage
-----

Cargo all the way. http://crates.io/crates/mucell

Author
------

[Chris Morgan](http://chrismorgan.info/) ([chris-morgan](https://github.com/chris-morgan)) is the primary author and maintainer of this library.

License
-------

This library is distributed under similar terms to Rust: dual licensed under the MIT license and the Apache license (version 2.0).

See LICENSE-APACHE, LICENSE-MIT, and COPYRIGHT for details.
