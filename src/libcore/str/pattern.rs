// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::raw;
use super::{Pattern, LeftMatcher, Matcher, RightMatcher, DoubleEndedMatcher};
use super::{Searcher, Utf8Char, CharOffsets, StrSlice, CharEq};

use char::Char;
use iter::{DoubleEndedIterator, Iterator};
use option::{Option, Some, None};

////////////////////////////////////////////////////////////////////////////
// Pattern implementation for `&str`
////////////////////////////////////////////////////////////////////////////

/// A matcher for `&str`.
///
/// This gets used in combination with `str::Pattern`
/// and the methods of `&str`.
#[deriving(Clone)]
pub struct StrMatcher<'a, 'b> {
    searcher: Searcher<'a, &'b str>
}

impl<'a, 'b> Pattern<'a, StrMatcher<'a, 'b>> for &'b str {
    #[inline]
    fn into_matcher(self, haystack: &'a str) -> StrMatcher<'a, 'b> {
        StrMatcher {
            searcher: Searcher::new(haystack, self)
        }
    }

    #[inline]
    fn is_contained_in(self, haystack: &str) -> bool {
        self.into_matcher(haystack).next_match().is_some()
    }
}

impl<'a, 'b> Matcher<'a> for StrMatcher<'a, 'b> {
    #[inline]
    fn get_haystack(&self) -> &'a str {
        self.searcher.get_haystack()
    }
}

impl<'a, 'b> LeftMatcher<'a> for StrMatcher<'a, 'b> {
    #[inline]
    fn next_match(&mut self) -> Option<(uint, &'a str)> {
        self.searcher.find_front()
    }
}

impl<'a, 'b> RightMatcher<'a> for StrMatcher<'a, 'b> {
    #[inline]
    fn next_match_back(&mut self) -> Option<(uint, &'a str)> {
        self.searcher.find_back()
    }
}

////////////////////////////////////////////////////////////////////////////
// Pattern implementation for `char`
////////////////////////////////////////////////////////////////////////////

/// A matcher for `char`.
///
/// This gets used in combination with `str::Pattern`
/// and the methods of `&str`.
#[deriving(Clone)]
pub struct CharMatcher<'a> {
    searcher: Searcher<'a, Utf8Char>
}

impl<'a> Pattern<'a, CharMatcher<'a>> for char {
    #[inline]
    fn into_matcher(self, s: &'a str) -> CharMatcher<'a> {
        let utf8char = Utf8Char::new(self);
        CharMatcher {
            searcher: Searcher::new(s, utf8char)
        }
    }

    #[inline]
    fn is_contained_in(self, s: &str) -> bool {
        self.into_matcher(s).next_match().is_some()
    }
}

impl<'a> Matcher<'a> for CharMatcher<'a> {
    #[inline]
    fn get_haystack(&self) -> &'a str {
        self.searcher.get_haystack()
    }
}

impl<'a> LeftMatcher<'a> for CharMatcher<'a> {
    #[inline]
    fn next_match(&mut self) -> Option<(uint, &'a str)> {
        self.searcher.find_front()
    }
}

impl<'a> RightMatcher<'a> for CharMatcher<'a> {
    #[inline]
    fn next_match_back(&mut self) -> Option<(uint, &'a str)> {
        self.searcher.find_back()
    }
}

impl<'a> DoubleEndedMatcher<'a> for CharMatcher<'a> { }

////////////////////////////////////////////////////////////////////////////
// Pattern implementation for `|char| -> bool`
////////////////////////////////////////////////////////////////////////////

/// A matcher for `|char| -> bool`.
///
/// This gets used in combination with `str::Pattern`
/// and the methods of `&str`.
pub type CharClosureMatcher<'a, 'b> = CharEqMatcher<'a, |char|:'b -> bool>;

impl<'a, 'b> Pattern<'a, CharClosureMatcher<'a, 'b>> for |char|:'b -> bool {
    #[inline]
    fn into_matcher(self, s: &'a str) -> CharClosureMatcher<'a, 'b> {
        CharEqPattern(self).into_matcher(s)
    }

    #[inline]
    fn is_contained_in(self, s: &str) -> bool {
        CharEqPattern(self).is_contained_in(s)
    }
}

////////////////////////////////////////////////////////////////////////////
// Pattern implementation for `fn(char) -> bool`
////////////////////////////////////////////////////////////////////////////

/// A matcher for `fn(char) -> bool`.
///
/// This gets used in combination with `str::Pattern`
/// and the methods of `&str`.
pub type CharFnMatcher<'a> = CharEqMatcher<'a, fn(char) -> bool>;

impl<'a> Pattern<'a, CharFnMatcher<'a>> for fn(char) -> bool {
    #[inline]
    fn into_matcher(self, s: &'a str) -> CharFnMatcher<'a> {
        CharEqPattern(self).into_matcher(s)
    }

    #[inline]
    fn is_contained_in(self, s: &str) -> bool {
        CharEqPattern(self).is_contained_in(s)
    }
}

////////////////////////////////////////////////////////////////////////////
// Pattern implementation for `&[char]`
////////////////////////////////////////////////////////////////////////////

/// A matcher for `&[char]`.
///
/// This gets used in combination with `str::Pattern`
/// and the methods of `&str`.
pub type CharSliceMatcher<'a, 'b> = CharEqMatcher<'a, &'b [char]>;

impl<'a, 'b> Pattern<'a, CharSliceMatcher<'a, 'b>> for &'b [char] {
    #[inline]
    fn into_matcher(self, s: &'a str) -> CharSliceMatcher<'a, 'b> {
        CharEqPattern(self).into_matcher(s)
    }

    #[inline]
    fn is_contained_in(self, s: &str) -> bool {
        CharEqPattern(self).is_contained_in(s)
    }
}

////////////////////////////////////////////////////////////////////////////
// Pattern implementation for types implementing `CharEq`
////////////////////////////////////////////////////////////////////////////

/// A string matching pattern that dispatches to the `CharEq` trait
pub struct CharEqPattern<T>(pub T);

impl<'a, T: CharEq> Pattern<'a, CharEqMatcher<'a, T>> for CharEqPattern<T> {
    #[inline]
    fn into_matcher(self, s: &'a str) -> CharEqMatcher<'a, T> {
        let CharEqPattern(char_eq) = self;
        CharEqMatcher {
            str: s,
            chars: s.char_indices(),
            only_ascii: char_eq.only_ascii(),
            char_eq: char_eq,
        }
    }

    #[inline]
    fn is_contained_in(self, s: &str) -> bool {
        self.into_matcher(s).next_match().is_some()
    }
}

/// A matcher for types implementing `CharEq`.
///
/// This gets used in combination with `str::Pattern`
/// and the methods of `&str`.
#[deriving(Clone)]
pub struct CharEqMatcher<'a, T> {
    str: &'a str,
    chars: CharOffsets<'a>,
    char_eq: T,
    only_ascii: bool
}

impl<'a, T: CharEq> Matcher<'a> for CharEqMatcher<'a, T> {
    #[inline]
    fn get_haystack(&self) -> &'a str {
        self.str
    }
}

impl<'a, T: CharEq> LeftMatcher<'a> for CharEqMatcher<'a, T> {
    #[inline]
    fn next_match(&mut self) -> Option<(uint, &'a str)> {
        loop {
            match self.chars.next() {
                Some((i, c)) => if self.char_eq.matches(c) {
                    let a = i;
                    let b = i + c.len_utf8_bytes();
                    let s = unsafe {
                        raw::slice_unchecked(self.str, a, b)
                    };
                    return Some((a, s))
                } else {
                    continue
                },
                None => break
            }
        }
        None
    }
}

impl<'a, T: CharEq> RightMatcher<'a> for CharEqMatcher<'a, T> {
    #[inline]
    fn next_match_back(&mut self) -> Option<(uint, &'a str)> {
        loop {
            match self.chars.next_back() {
                Some((i, c)) => if self.char_eq.matches(c) {
                    let a = i;
                    let b = i + c.len_utf8_bytes();
                    let s = unsafe {
                        raw::slice_unchecked(self.str, a, b)
                    };
                    return Some((a, s))
                } else {
                    continue
                },
                None => break,
            }
        }
        None
    }
}

impl<'a, T: CharEq> DoubleEndedMatcher<'a> for CharEqMatcher<'a, T> { }
