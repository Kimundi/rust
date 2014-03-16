// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! The `Clone` trait for types that cannot be 'implicitly copied'

In Rust, some simple types are "implicitly copyable" and when you
assign them or pass them as arguments, the receiver will get a copy,
leaving the original value in place. These types do not require
allocation to copy and do not have finalizers (i.e. they do not
contain owned boxes or implement `Drop`), so the compiler considers
them cheap and safe to copy. For other types copies must be made
explicitly, by convention implementing the `Clone` trait and calling
the `clone` method.

*/

/// A common trait for cloning an object.
pub trait Clone {
    /// Returns a copy of the value. The contents of owned pointers
    /// are copied to maintain uniqueness, while the contents of
    /// managed pointers are not copied.
    fn clone(&self) -> Self;

    /// Perform copy-assignment from `source`.
    ///
    /// `a.clone_from(&b)` is equivalent to `a = b.clone()` in functionality,
    /// but can be overridden to reuse the resources of `a` to avoid unnecessary
    /// allocations.
    #[inline(always)]
    fn clone_from(&mut self, source: &Self) {
        *self = source.clone()
    }
}

macro_rules! extern_fn_clone(
    ($($A:ident),*) => (
        impl<$($A,)* ReturnType> Clone for extern "Rust" fn($($A),*) -> ReturnType {
            /// Return a copy of a function pointer
            #[inline]
            fn clone(&self) -> extern "Rust" fn($($A),*) -> ReturnType { *self }
        }
    )
)

extern_fn_clone!()
extern_fn_clone!(A)
extern_fn_clone!(A, B)
extern_fn_clone!(A, B, C)
extern_fn_clone!(A, B, C, D)
extern_fn_clone!(A, B, C, D, E)
extern_fn_clone!(A, B, C, D, E, F)
extern_fn_clone!(A, B, C, D, E, F, G)
extern_fn_clone!(A, B, C, D, E, F, G, H)

#[test]
fn test_extern_fn_clone() {
    trait Empty {}
    impl Empty for int {}

    fn test_fn_a() -> f64 { 1.0 }
    fn test_fn_b<T: Empty>(x: T) -> T { x }
    fn test_fn_c(_: int, _: f64, _: ~[int], _: int, _: int, _: int) {}

    let _ = test_fn_a.clone();
    let _ = test_fn_b::<int>.clone();
    let _ = test_fn_c.clone();
}
