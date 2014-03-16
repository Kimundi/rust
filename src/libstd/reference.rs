// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Utilities for references

use clone::Clone;
use io::Writer;
use hash::Hash;
use fmt::{Show, Formatter};

#[cfg(not(test))]
use cmp::{Eq, Ord, Ordering, TotalEq, TotalOrd};

// Equality for region pointers
#[cfg(not(test))]
impl<'a, T: Eq> Eq for &'a T {
    #[inline]
    fn eq(&self, other: & &'a T) -> bool {
        *(*self) == *(*other)
    }
    #[inline]
    fn ne(&self, other: & &'a T) -> bool {
        *(*self) != *(*other)
    }
}

// Comparison for region pointers
#[cfg(not(test))]
impl<'a, T: Ord> Ord for &'a T {
    #[inline]
    fn lt(&self, other: & &'a T) -> bool {
        *(*self) < *(*other)
    }
    #[inline]
    fn le(&self, other: & &'a T) -> bool {
        *(*self) <= *(*other)
    }
    #[inline]
    fn ge(&self, other: & &'a T) -> bool {
        *(*self) >= *(*other)
    }
    #[inline]
    fn gt(&self, other: & &'a T) -> bool {
        *(*self) > *(*other)
    }
}

#[cfg(not(test))]
impl<'a, T: TotalOrd> TotalOrd for &'a T {
    #[inline]
    fn cmp(&self, other: & &'a T) -> Ordering { (**self).cmp(*other) }
}

#[cfg(not(test))]
impl<'a, T: TotalEq> TotalEq for &'a T {
    #[inline]
    fn equals(&self, other: & &'a T) -> bool { (**self).equals(*other) }
}

impl<'a, T> Clone for &'a T {
    /// Return a shallow copy of the reference.
    #[inline]
    fn clone(&self) -> &'a T { *self }
}

impl<'a, S: Writer, T: Hash<S>> Hash<S> for &'a T {
    #[inline]
    fn hash(&self, state: &mut S) {
        (**self).hash(state);
    }
}

impl<'a, S: Writer, T: Hash<S>> Hash<S> for &'a mut T {
    #[inline]
    fn hash(&self, state: &mut S) {
        (**self).hash(state);
    }
}

impl<'a, T: Show> Show for &'a T {
    fn fmt(&self, f: &mut Formatter) -> ::fmt::Result { ::fmt::secret_show(*self, f) }
}

impl<'a, T> ::fmt::Pointer for &'a T {
    fn fmt(&self, f: &mut ::fmt::Formatter) -> ::fmt::Result {
        ::fmt::secret_pointer::<*T>(&(&**self as *T), f)
    }
}

impl<'a, T> ::fmt::Pointer for &'a mut T {
    fn fmt(&self, f: &mut ::fmt::Formatter) -> ::fmt::Result {
        ::fmt::secret_pointer::<*T>(&(&**self as *T), f)
    }
}

#[test]
fn test_reference_clone() {
    let x = 5i;
    let y: &int = &x;
    let z: &int = (&y).clone();
    assert_eq!(*z, 5);
}
