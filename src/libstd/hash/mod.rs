// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Generic hashing support.
 *
 * This module provides a generic way to compute the hash of a value. The
 * simplest way to make a type hashable is to use `#[deriving(Hash)]`:
 *
 * # Example
 *
 * ```rust
 * use std::hash;
 * use std::hash::Hash;
 *
 * #[deriving(Hash)]
 * struct Person {
 *     id: uint,
 *     name: ~str,
 *     phone: u64,
 * }
 *
 * let person1 = Person { id: 5, name: ~"Janet", phone: 555_666_7777 };
 * let person2 = Person { id: 5, name: ~"Bob", phone: 555_666_7777 };
 *
 * assert!(hash::hash(&person1) != hash::hash(&person2));
 * ```
 *
 * If you need more control over how a value is hashed, you need to implement
 * the trait `Hash`:
 *
 * ```rust
 * use std::hash;
 * use std::hash::Hash;
 * use std::hash::sip::SipState;
 *
 * struct Person {
 *     id: uint,
 *     name: ~str,
 *     phone: u64,
 * }
 *
 * impl Hash for Person {
 *     fn hash(&self, state: &mut SipState) {
 *         self.id.hash(state);
 *         self.phone.hash(state);
 *     }
 * }
 *
 * let person1 = Person { id: 5, name: ~"Janet", phone: 555_666_7777 };
 * let person2 = Person { id: 5, name: ~"Bob", phone: 555_666_7777 };
 *
 * assert!(hash::hash(&person1) == hash::hash(&person2));
 * ```
 */

#[allow(unused_must_use)];

/// Reexport the `sip::hash` function as our default hasher.
pub use hash = self::sip::hash;

pub mod sip;

/// A trait that represents a hashable type. The `S` type parameter is an
/// abstract hash state that is used by the `Hash` to compute the hash.
/// It defaults to `std::hash::sip::SipState`.
pub trait Hash<S = sip::SipState> {
    /// Compute a hash of the value.
    fn hash(&self, state: &mut S);
}

/// A trait that computes a hash for a value. The main users of this trait are
/// containers like `HashMap`, which need a generic way hash multiple types.
pub trait Hasher<S> {
    /// Compute a hash of the value.
    fn hash<T: Hash<S>>(&self, value: &T) -> u64;
}

//////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use cast;
    use io::{IoResult, Writer};
    use iter::{Iterator};
    use option::{Some, None};
    use result::Ok;
    use vec::ImmutableVector;

    use super::{Hash, Hasher};

    struct MyWriterHasher;

    impl Hasher<MyWriter> for MyWriterHasher {
        fn hash<T: Hash<MyWriter>>(&self, value: &T) -> u64 {
            let mut state = MyWriter { hash: 0 };
            value.hash(&mut state);
            state.hash
        }
    }

    struct MyWriter {
        hash: u64,
    }

    impl Writer for MyWriter {
        // Most things we'll just add up the bytes.
        fn write(&mut self, buf: &[u8]) -> IoResult<()> {
            for byte in buf.iter() {
                self.hash += *byte as u64;
            }
            Ok(())
        }
    }

    #[test]
    fn test_writer_hasher() {
        let hasher = MyWriterHasher;

        assert_eq!(hasher.hash(&()), 0);

        assert_eq!(hasher.hash(&5u8), 5);
        assert_eq!(hasher.hash(&5u16), 5);
        assert_eq!(hasher.hash(&5u32), 5);
        assert_eq!(hasher.hash(&5u64), 5);
        assert_eq!(hasher.hash(&5u), 5);

        assert_eq!(hasher.hash(&5i8), 5);
        assert_eq!(hasher.hash(&5i16), 5);
        assert_eq!(hasher.hash(&5i32), 5);
        assert_eq!(hasher.hash(&5i64), 5);
        assert_eq!(hasher.hash(&5i), 5);

        assert_eq!(hasher.hash(&false), 0);
        assert_eq!(hasher.hash(&true), 1);

        assert_eq!(hasher.hash(&'a'), 97);

        assert_eq!(hasher.hash(& &"a"), 97 + 0xFF);
        assert_eq!(hasher.hash(& &[1u8, 2u8, 3u8]), 9);

        unsafe {
            let ptr: *int = cast::transmute(5);
            assert_eq!(hasher.hash(&ptr), 5);
        }

        unsafe {
            let ptr: *mut int = cast::transmute(5);
            assert_eq!(hasher.hash(&ptr), 5);
        }
    }

    struct Custom {
        hash: u64
    }

    impl Hash<u64> for Custom {
        fn hash(&self, state: &mut u64) {
            *state = self.hash;
        }
    }

    #[test]
    fn test_custom_state() {
        let custom = Custom { hash: 5 };
        let mut state = 0;
        custom.hash(&mut state);
        assert_eq!(state, 5);
    }
}
