#![allow(unstable)]
#[macro_use] extern crate mucell;
use mucell::{MuCell, Ref};
use std::collections::HashMap;
use std::borrow::Cow;

struct Inner {
    pub value: Vec<i32>,
    munged: Option<Vec<i32>>,
}

impl Inner {
    pub fn new(value: Vec<i32>) -> Inner {
        Inner {
            value: value,
            munged: None,
        }
    }

    /// Set the value.
    ///
    /// (Demonstration of how anything altering `value` would need to set `munged` to `None`.)
    #[allow(dead_code)]
    pub fn set(&mut self, value: Vec<i32>) {
        self.value = value;
        self.munged = None;
    }

    /// Munge the value in-place, if necessary.
    pub fn munge(&mut self) {
        if self.munged.is_none() {
            self.munged = Some(self.munged().into_owned());
        }
    }

    /// Get the munged value from an immutable reference,
    /// either a reference to the pre-prepared value if it’s
    /// already made or a new vector.
    pub fn munged(&self) -> Cow<Vec<i32>, [i32]> {
        match self.munged {
            Some(ref x) => Cow::Borrowed(x.as_slice()),
            None => Cow::Owned(self.value.iter().map(|&x| x + 1).collect()),
        }
    }

    // Just for demonstration
    pub fn assert_munged_exists(&self) {
        assert!(self.munged.is_some())
    }

    pub fn assert_munged_does_not_exist(&self) {
        assert!(self.munged.is_none())
    }
}

mucell_ref_type! {
    #[doc = "…"]
    struct MungedRef<'a>(Inner),
    impl Deref -> [i32],
    data: Cow<'a, Vec<i32>, [i32]> = |x| x.munged()
}

fn main() {
    // Having these cells as the values in a map is about the most common mode of usage for this
    // library that I can think of.
    let mut items = HashMap::new();
    items.insert("foo", MuCell::new(Inner::new(vec![1, 2, 3])));
    items.insert("bar", MuCell::new(Inner::new(vec![4, 5, 6])));
    items.insert("baz", MuCell::new(Inner::new(vec![7, 8, 9])));

    // foo and baz can be unborrowed, but bar can be borrowed.
    let _active_borrow = items.get("bar").unwrap().borrow();

    let item = items.get("foo").unwrap();
    // First of all, we see—can we ensure that we have the munged version, in place? If we can,
    // that will make retrieving the munged version multiple times (provided `set` is not called in
    // between) more efficient, as it will only need to do the work once. Because MungedRef is
    // operating on munged() which is Cow-based and doesn’t *need* `munge` to have been called,
    // it’s fine if this mutation doesn’t actually happen.
    item.try_mutate(|x| x.munge());

    // In this particular case, we know it’s done it.
    item.borrow().assert_munged_exists();

    // Whether it had happened or not, this part is definitely true:
    let a = MungedRef::from(item);
    assert_eq!(&*a, [2, 3, 4]);

    // Now suppose we do the same for bar, which has been borrowed.
    let item = items.get(&"bar").unwrap();
    // This time, try_mutate will *not* do the munging.
    item.try_mutate(|x| x.munge());
    item.borrow().assert_munged_does_not_exist();

    // … but the MungedRef is still just fine.
    let a = MungedRef::from(item);
    assert_eq!(&*a, [5, 6, 7]);

}
