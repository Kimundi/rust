// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Operations on managed box types

use clone::Clone;
use default::Default;
use fmt::{Show, Formatter};
use hash::Hash;
use io::Writer;

#[cfg(not(test))] use cmp::*;

/// Returns the refcount of a shared box (as just before calling this)
#[inline]
pub fn refcount<T>(t: @T) -> uint {
    use raw::Repr;
    unsafe { (*t.repr()).ref_count - 1 }
}

/// Determine if two shared boxes point to the same object
#[inline]
pub fn ptr_eq<T>(a: @T, b: @T) -> bool {
    &*a as *T == &*b as *T
}

#[cfg(not(test))]
impl<T:Eq> Eq for @T {
    #[inline]
    fn eq(&self, other: &@T) -> bool { *(*self) == *(*other) }
    #[inline]
    fn ne(&self, other: &@T) -> bool { *(*self) != *(*other) }
}

#[cfg(not(test))]
impl<T:Ord> Ord for @T {
    #[inline]
    fn lt(&self, other: &@T) -> bool { *(*self) < *(*other) }
    #[inline]
    fn le(&self, other: &@T) -> bool { *(*self) <= *(*other) }
    #[inline]
    fn ge(&self, other: &@T) -> bool { *(*self) >= *(*other) }
    #[inline]
    fn gt(&self, other: &@T) -> bool { *(*self) > *(*other) }
}

#[cfg(not(test))]
impl<T: TotalOrd> TotalOrd for @T {
    #[inline]
    fn cmp(&self, other: &@T) -> Ordering { (**self).cmp(*other) }
}

#[cfg(not(test))]
impl<T: TotalEq> TotalEq for @T {
    #[inline]
    fn equals(&self, other: &@T) -> bool { (**self).equals(*other) }
}

impl<T> Clone for @T {
    /// Return a shallow copy of the managed box.
    #[inline]
    fn clone(&self) -> @T { *self }
}

impl<T: Default + 'static> Default for @T {
    fn default() -> @T { @Default::default() }
}

impl<S: Writer, T: Hash<S>> Hash<S> for @T {
    #[inline]
    fn hash(&self, state: &mut S) {
        (**self).hash(state);
    }
}

impl<T: Show> Show for @T {
    fn fmt(&self, f: &mut Formatter) -> ::fmt::Result { ::fmt::secret_show(&**self, f) }
}

#[test]
fn test() {
    let x = @3;
    let y = @3;
    assert!((ptr_eq::<int>(x, x)));
    assert!((ptr_eq::<int>(y, y)));
    assert!((!ptr_eq::<int>(x, y)));
    assert!((!ptr_eq::<int>(y, x)));
}

#[test]
fn refcount_test() {
    use clone::Clone;

    let x = @3;
    assert_eq!(refcount(x), 1);
    let y = x.clone();
    assert_eq!(refcount(x), 2);
    assert_eq!(refcount(y), 2);
}

#[test]
fn test_managed_clone() {
    let a = @5i;
    let b: @int = a.clone();
    assert_eq!(a, b);
}
