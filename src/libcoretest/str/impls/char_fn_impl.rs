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
    fn f(c: char) -> bool { c == 'c' }
    iter_eq!(s.match_indices(f), [(2u, "c")]);
}

#[test]
fn test2() {
    let s = "abcbdef";
    fn f(c: char) -> bool { c == 'b' }
    iter_eq!(s.match_indices(f), [(1u, "b"), (3, "b")]);
}

#[test]
fn test3() {
    let s = "ศไทย中华Việt Nam; Mary had a little lamb, Little lamb";
    fn f(c: char) -> bool { c == 'm' || c == 'r' || c == 'd' }
    iter_eq!(s.match_indices(f),
                [(27, "m"), (32, "r"), (37, "d"), (50u, "m"), (63, "m")]);

    iter_eq!(s.matches(f), ["m", "r", "d", "m", "m"]);

    fn g(c: char) -> bool { c == '中' }
    iter_eq!(s.match_indices(g), [(12u, "中")]);
}

#[test]
fn test1_rev() {
    let s = "abcbdef";
    fn f(c: char) -> bool { c == 'c' }
    iter_eq!(s.match_indices(f).rev(), [(2u, "c")]);
}

#[test]
fn test2_rev() {
    let s = "abcbdef";
    fn f(c: char) -> bool { c == 'b' }
    iter_eq!(s.match_indices(f).rev(), [(3u, "b"), (1, "b")]);
}

#[test]
fn test3_rev() {
    let s = "ศไทย中华Việt Nam; Mary had a little lamb, Little lamb";
    fn f(c: char) -> bool { c == 'm' || c == 'r' || c == 'd' }
    iter_eq!(s.match_indices(f).rev(),
                [(63, "m"), (50u, "m"), (37, "d"), (32, "r"), (27, "m")]);

    iter_eq!(s.matches(f).rev(), ["m", "m", "d", "r", "m"]);

    fn g(c: char) -> bool { c == '中' }
    iter_eq!(s.match_indices(g).rev(), [(12u, "中")]);
}
