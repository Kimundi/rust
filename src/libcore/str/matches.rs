// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{Pattern, LeftMatcher, DoubleEndedMatcher, RightMatcher};

use iter::{DoubleEndedIterator, Iterator};
use option::Option;

////////////////////////////////////////////////////////////////////////////
// Implementation for `.matches()`
////////////////////////////////////////////////////////////////////////////

/// An iterator over all non-overlapping matches of a string pattern
/// in a `&str` starting from the front.
#[deriving(Clone)]
pub struct Matches<M> {
    matcher: M
}

impl<M> Matches<M> {
    /// Constructor of `Matches` from a `Pattern`.
    ///
    /// Can also be constructed with the `.matches()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> Matches<M> {
        let string_matcher = pat.into_matcher(s);
        Matches { matcher: string_matcher }
    }
}

impl<'a, M: LeftMatcher<'a>> Iterator<&'a str> for Matches<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.matcher.next_match().map(|(_, s)| s)
    }
}

impl<'a, M: DoubleEndedMatcher<'a>> DoubleEndedIterator<&'a str> for Matches<M> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.matcher.next_match_back().map(|(_, s)| s)
    }
}

////////////////////////////////////////////////////////////////////////////
// Implementation for `.rmatches()`
////////////////////////////////////////////////////////////////////////////

/// An iterator over all non-overlapping matches of a string pattern
/// in a `&str` starting from the back.
#[deriving(Clone)]
pub struct RMatches<M> {
    matcher: M
}

impl<M> RMatches<M> {
    /// Constructor of `RMatches` from a `Pattern`.
    ///
    /// Can also be constructed with the `.rmatches()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> RMatches<M> {
        let string_matcher = pat.into_matcher(s);
        RMatches { matcher: string_matcher }
    }
}

impl<'a, M: RightMatcher<'a>> Iterator<&'a str> for RMatches<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.matcher.next_match_back().map(|(_, s)| s)
    }
}

////////////////////////////////////////////////////////////////////////////
// Implementation for `.matches_indices()`
////////////////////////////////////////////////////////////////////////////

/// An iterator over all non-overlapping matches of a string pattern
/// in a `&str` with their byte indices starting from the front.
#[deriving(Clone)]
pub struct MatchIndices<M> {
    matcher: M
}

impl<M> MatchIndices<M> {
    /// Constructor of `MatchIndices` from a `Pattern`.
    ///
    /// Can also be constructed with the `.match_indices()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> MatchIndices<M> {
        let string_matcher = pat.into_matcher(s);
        MatchIndices { matcher: string_matcher }
    }
}

impl<'a, M: LeftMatcher<'a>> Iterator<(uint, &'a str)> for MatchIndices<M> {
    #[inline]
    fn next(&mut self) -> Option<(uint, &'a str)> {
        self.matcher.next_match()
    }
}

impl<'a, M: DoubleEndedMatcher<'a>> DoubleEndedIterator<(uint, &'a str)> for MatchIndices<M> {
    #[inline]
    fn next_back(&mut self) -> Option<(uint, &'a str)> {
        self.matcher.next_match_back()
    }
}

////////////////////////////////////////////////////////////////////////////
// Implementation for `.rmatches_indices()`
////////////////////////////////////////////////////////////////////////////

/// An iterator over all non-overlapping matches of a string pattern
/// in a `&str` with their byte indices starting from the back.
#[deriving(Clone)]
pub struct RMatchIndices<M> {
    matcher: M
}

impl<M> RMatchIndices<M> {
    /// Constructor of `RMatchIndices` from a `Pattern`.
    ///
    /// Can also be constructed with the `.rmatch_indices()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> RMatchIndices<M> {
        let string_matcher = pat.into_matcher(s);
        RMatchIndices { matcher: string_matcher }
    }
}

impl<'a, M: RightMatcher<'a>> Iterator<(uint, &'a str)> for RMatchIndices<M> {
    #[inline]
    fn next(&mut self) -> Option<(uint, &'a str)> {
        self.matcher.next_match_back()
    }
}
