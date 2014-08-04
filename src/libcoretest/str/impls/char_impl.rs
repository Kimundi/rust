// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[test]
fn test1() {
    let s = "abcbdef";
    iter_eq!(s.match_indices('c'), [(2u, "c")]);
    iter_eq!(s.match_indices('c').rev(), [(2u, "c")]);
}

#[test]
fn test2() {
    let s = "abcbdef";
    iter_eq!(s.match_indices('b'), [(1u, "b"), (3, "b")]);
    iter_eq!(s.match_indices('b').rev(), [(3, "b"), (1u, "b")]);
}

#[test]
fn test3() {
    let s = "ศไทย中华Việt Nam; Mary had a little lamb, Little lamb";
    iter_eq!(s.match_indices('a'),
                [(26, "a"), (31, "a"), (36, "a"), (39, "a"), (49u, "a"), (62, "a")]);
    iter_eq!(s.match_indices('a').rev(),
                [(62, "a"), (49u, "a"), (39, "a"), (36, "a"), (31, "a"), (26, "a")]);

    iter_eq!(s.match_indices('中'), [(12u, "中")]);
    iter_eq!(s.match_indices('中').rev(), [(12u, "中")]);
}
