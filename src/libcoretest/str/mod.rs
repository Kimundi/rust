// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

macro_rules! iter_eq {
    ($i:expr, $s:expr) => {
        {
            let i: Vec<_> = $i.collect();
            let s = $s;
            assert_eq!(i.as_slice(), s.as_slice());
        }
    }
}

mod impls;

#[test]
fn test_starts_with() {
    assert!("foobar".starts_with("foo"));
    assert!("foobar".starts_with('f'));

    assert!(!"foobar".starts_with("oba"));
    assert!(!"foobar".starts_with('o'));
}

#[test]
fn test_end_with() {
    assert!("foobar".ends_with("bar"));
    assert!("foobar".ends_with('r'));

    assert!(!"foobar".ends_with("oob"));
    assert!(!"foobar".ends_with('b'));
}

#[test]
fn test_trim_left() {
    assert_eq!("  ajklasd  ".trim_left_matches(" "), "ajklasd  ");
    assert_eq!("  ajklasd  ".trim_left_matches(' '), "ajklasd  ");
}

#[test]
fn test_trim_right() {
    assert_eq!("  ajklasd  ".trim_right_matches(" "), "  ajklasd");
    assert_eq!("  ajklasd  ".trim_right_matches(' '), "  ajklasd");
}

#[test]
fn test_trim() {
    assert_eq!("  ajklasd  ".trim_matches(' '), "ajklasd");
}

#[test]
fn test_find() {
    assert_eq!("abaaaba".find("b"), Some(1));
    assert_eq!("abaaaba".find("a"), Some(0));
    assert_eq!("abaaaba".find("c"), None);
}

#[test]
fn test_rfind() {
    assert_eq!("abaaaba".rfind("b"), Some(5));
    assert_eq!("abaaaba".rfind("a"), Some(6));
    assert_eq!("abaaaba".rfind("c"), None);
}

#[test]
fn test_split_terminator() {
    let s = "asädfadfsdfa";
    iter_eq!(s.split_terminator("a"), ["", "sädf", "dfsdf"]);
    iter_eq!(s.rsplit_terminator("a"), ["dfsdf", "sädf", ""]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.split_terminator("a"), ["", "sädf", "", "", "", "", "dfsdf"]);
    iter_eq!(s.rsplit_terminator("a"), ["dfsdf", "", "", "", "", "sädf", ""]);

    let s = "fffababafff";
    iter_eq!(s.split_terminator("ab"), ["fff", "", "afff"]);
    iter_eq!(s.rsplit_terminator("ab"), ["afff", "", "fff"]);

    let s = "a";
    iter_eq!(s.split_terminator("a"), [""]);
    iter_eq!(s.rsplit_terminator("a"), [""]);
}

#[test]
fn test_split_terminator_overlapping() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.split_terminator("aa"), ["asädf", "", "adfsdfa"]);
    iter_eq!(s.rsplit_terminator("aa"), ["dfsdfa", "", "asädfa"]);

    let s = "fffababafff";
    iter_eq!(s.split_terminator("aba"), ["fff", "bafff"]);
    iter_eq!(s.rsplit_terminator("aba"), ["fff", "fffab"]);
}


#[test]
fn test_rsplitn100() {
    let s = "asädfadfsdfa";
    iter_eq!(s.rsplitn("a", 100), ["", "dfsdf", "sädf", ""]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.rsplitn("a", 100), ["", "dfsdf", "", "", "", "", "sädf", ""]);

    let s = "fffababafff";
    iter_eq!(s.rsplitn("ab", 100), ["afff", "", "fff"]);
}

#[test]
fn test_rsplitn_overlapping100() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.rsplitn("aa", 100), ["dfsdfa", "", "asädfa"]);

    let s = "fffababafff";
    iter_eq!(s.rsplitn("aba", 100), ["fff", "fffab"]);
}

#[test]
fn test_rsplitn2() {
    let s = "asädfadfsdfa";
    iter_eq!(s.rsplitn("a", 2), ["", "dfsdf", "asädf"]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.rsplitn("a", 2), ["", "dfsdf", "asädfaaaa"]);

    let s = "fffababafff";
    iter_eq!(s.rsplitn("ab", 2), ["afff", "", "fff"]);
}

#[test]
fn test_rsplitn_overlapping2() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.rsplitn("aa", 2), ["dfsdfa", "", "asädfa"]);

    let s = "fffababafff";
    iter_eq!(s.rsplitn("aba", 2), ["fff", "fffab"]);
}

#[test]
fn test_rsplitn0() {
    let s = "asädfadfsdfa";
    iter_eq!(s.rsplitn("a", 0), [s]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.rsplitn("a", 0), [s]);

    let s = "fffababafff";
    iter_eq!(s.rsplitn("ab", 0), [s]);
}

#[test]
fn test_rsplitn_overlapping0() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.rsplitn("aa", 0), [s]);

    let s = "fffababafff";
    iter_eq!(s.rsplitn("aba", 0), [s]);
}


#[test]
fn test_splitn100() {
    let s = "asädfadfsdfa";
    iter_eq!(s.splitn("a", 100), ["", "sädf", "dfsdf", ""]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.splitn("a", 100), ["", "sädf", "", "", "", "", "dfsdf", ""]);

    let s = "fffababafff";
    iter_eq!(s.splitn("ab", 100), ["fff", "", "afff"]);
}

#[test]
fn test_splitn_overlapping100() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.splitn("aa", 100), ["asädf", "", "adfsdfa"]);

    let s = "fffababafff";
    iter_eq!(s.splitn("aba", 100), ["fff", "bafff"]);
}

#[test]
fn test_splitn2() {
    let s = "asädfadfsdfa";
    iter_eq!(s.splitn("a", 2), ["", "sädf", "dfsdfa"]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.splitn('a', 2), ["", "sädf", "aaaadfsdfa"]);

    let s = "fffababafff";
    iter_eq!(s.splitn("ab", 2), ["fff", "", "afff"]);
}

#[test]
fn test_splitn_overlapping2() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.splitn("aa", 2), ["asädf", "", "adfsdfa"]);

    let s = "fffababafff";
    iter_eq!(s.splitn("aba", 2), ["fff", "bafff"]);
}

#[test]
fn test_splitn0() {
    let s = "asädfadfsdfa";
    iter_eq!(s.splitn("a", 0), [s]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.splitn("a", 0), [s]);

    let s = "fffababafff";
    iter_eq!(s.splitn("ab", 0), [s]);
}

#[test]
fn test_splitn_overlapping0() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.splitn("aa", 0), [s]);

    let s = "fffababafff";
    iter_eq!(s.splitn("aba", 0), [s]);
}


#[test]
fn test_split() {
    let s = "asädfadfsdfa";
    iter_eq!(s.split("a"), ["", "sädf", "dfsdf", ""]);
    iter_eq!(s.rsplit("a"), ["", "dfsdf", "sädf", ""]);

    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.split("a"), ["", "sädf", "", "", "", "", "dfsdf", ""]);
    iter_eq!(s.rsplit("a"), ["", "dfsdf", "", "", "", "", "sädf", ""]);

    let s = "fffababafff";
    iter_eq!(s.split("ab"), ["fff", "", "afff"]);
    iter_eq!(s.rsplit("ab"), ["afff", "", "fff"]);

    let s = "a";
    iter_eq!(s.split("a"), ["", ""]);
    iter_eq!(s.rsplit("a"), ["", ""]);
}

#[test]
fn test_split_overlapping() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.split("aa"), ["asädf", "", "adfsdfa"]);
    iter_eq!(s.rsplit("aa"), ["dfsdfa", "", "asädfa"]);

    let s = "fffababafff";
    iter_eq!(s.split("aba"), ["fff", "bafff"]);
    iter_eq!(s.rsplit("aba"), ["fff", "fffab"]);
}

#[test]
fn test_double_ended_match_indices() {
    let s = "asädfaaaaadfsdfa";
    iter_eq!(s.match_indices("aa"), [(6u, "aa"), (8, "aa")]);
    iter_eq!(s.rmatch_indices("aa"), [(9u, "aa"), (7, "aa")]);
}

#[test]
fn test_empty_haystack() {
    let haystack = "";
    let needle = "asädf";
    let arr: [(uint, &str), ..0] = [];
    iter_eq!(haystack.match_indices(needle), arr);
}

#[test]
fn test_empty_needle() {
    let haystack = "asädf";
    let needle = "";
    iter_eq!(haystack.match_indices(needle), [(0u, ""), (1, ""), (2, ""), (4, ""), (5, "")]);
}

#[test]
fn test_empty_haystack_needle() {
    let haystack = "";
    let needle = "";
    iter_eq!(haystack.match_indices(needle), [(0u, "")]);
}
