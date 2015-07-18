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
    pub fn munged(&self) -> Cow<[i32]> {
        match self.munged {
            Some(ref x) => Cow::Borrowed(x.as_ref()),
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
    // between) more efficient, as it will only need to do the work once. Because the
    // `Ref::map(item.borrow(), item.munged())` is operating on the Cow basis and doesn’t *need*
    // `munge` to have been called, it’s fine if this mutation doesn’t actually happen.
    item.try_mutate(|x| x.munge());

    // In this particular case, we know it’s done it.
    item.borrow().assert_munged_exists();

    // Whether it had happened or not, this part is definitely true:
    let a = Ref::map(item.borrow(), |inner| inner.munged());
    assert_eq!(&*a, [2, 3, 4]);

    // Now suppose we do the same for bar, which has been borrowed.
    let item = items.get(&"bar").unwrap();
    // This time, try_mutate will *not* do the munging.
    item.try_mutate(|x| x.munge());
    item.borrow().assert_munged_does_not_exist();

    // … but the munged() Cow is still just fine.
    let a = Ref::map(item.borrow(), |inner| inner.munged());
    assert_eq!(&*a, [5, 6, 7]);

    // With another map call and an into_inner(), we can get the value out of
    // it without cloning it all if it’s already Cow::Owned. Efficiency, yay!
    let _munged: Vec<i32> = Ref::map(a, |a| a.into_owned()).into_inner();

}
