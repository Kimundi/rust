// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::StrSlice;
use super::{Pattern, LeftMatcher, Matcher, DoubleEndedMatcher, RightMatcher};

use collections::Collection;
use iter::{DoubleEndedIterator, Iterator};
use option::{Option, Some, None};

fn splits_next<'a, M: LeftMatcher<'a>>(self_: &mut SplitsInternal<M>) -> Option<(uint, uint)> {
    if self_.finished {
        return None;
    }
    // In case of overlapping matches, consider them one big seperator
    loop {
        match self_.matcher.next_match() {
            Some((a, s)) => {
                let b = a + s.len();
                let current_prev_start = self_.prev_start;
                self_.prev_start = b;
                if current_prev_start <= a {
                    return Some((current_prev_start, a));
                }
            }
            None => {
                self_.finished = true;
                return Some((self_.prev_start, self_.matcher.get_haystack().len()));
            }
        }
    }
}

fn splits_next_back<'a, M: RightMatcher<'a>>(self_: &mut SplitsInternal<M>)
-> Option<(uint, uint)> {
        if self_.finished {
            return None;
        }
        // In case of overlapping matches, consider them one big seperator
        loop {
            match self_.matcher.next_match_back() {
                Some((a, s)) => {
                    let b = a + s.len();
                    let current_prev_end = self_.prev_end;
                    self_.prev_end = a;
                    if b <= current_prev_end {
                        return Some((b, current_prev_end));
                    }
                }
                None => {
                    self_.finished = true;
                    return Some((0, self_.prev_end));
                }
            }
        }
}

////////////////////////////////////////////////////////////////////////////
// Implementation for `.split()` and `.rsplit()`
////////////////////////////////////////////////////////////////////////////

#[deriving(Clone)]
struct SplitsInternal<M> {
    matcher: M,
    finished: bool,
    prev_start: uint,
    prev_end: uint,
}

impl<M> SplitsInternal<M> {
    #[inline]
    fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> SplitsInternal<M> {
        SplitsInternal {
            matcher: pat.into_matcher(s),
            finished: false,
            prev_start: 0,
            prev_end: s.len()
        }
    }
}

impl<'a, M: LeftMatcher<'a>> SplitsInternal<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        let string = self.matcher.get_haystack();
        splits_next(self).map(|(a, b)| {
            string.slice(a, b)
        })
    }
}

impl<'a, M: RightMatcher<'a>> SplitsInternal<M> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        let string = self.matcher.get_haystack();
        splits_next_back(self).map(|(a, b)| {
            string.slice(a, b)
        })
    }
}

/// An iterator over all substrings of a `&str` split at the
/// non-overlapping match of a string pattern matched from the left.
#[deriving(Clone)]
pub struct Splits<M> {
    splits: SplitsInternal<M>
}

impl<M> Splits<M> {
    /// Constructor for `Splits`.
    ///
    /// Can also be constructed with the `.split()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(haystack: &'a str, pat: P) -> Splits<M> {
        Splits {
            splits: SplitsInternal::new(haystack, pat)
        }
    }
}

impl<'a, M: LeftMatcher<'a>> Iterator<&'a str> for Splits<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.splits.next()
    }
}

impl<'a, M: DoubleEndedMatcher<'a>> DoubleEndedIterator<&'a str> for Splits<M> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.splits.next_back()
    }
}

/// An iterator over all substrings of a `&str` split at the
/// non-overlapping match of a string pattern matched from the right.
#[deriving(Clone)]
pub struct RSplits<M> {
    splits: SplitsInternal<M>
}

impl<M> RSplits<M> {
    /// Constructor for `RSplits`.
    ///
    /// Can also be constructed with the `.rsplit()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(haystack: &'a str, pat: P) -> RSplits<M> {
        RSplits {
            splits: SplitsInternal::new(haystack, pat)
        }
    }
}

impl<'a, M: RightMatcher<'a>> Iterator<&'a str> for RSplits<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.splits.next_back()
    }
}

////////////////////////////////////////////////////////////////////////////
// Implementation for `.splitn()` and `.rsplitn()`
////////////////////////////////////////////////////////////////////////////

#[deriving(Clone)]
struct NSplitsInternal<M> {
    splits: SplitsInternal<M>,
    count: uint
}

impl<M> NSplitsInternal<M> {
    #[inline]
    fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P, n: uint) -> NSplitsInternal<M> {
        NSplitsInternal {
            splits: SplitsInternal::new(s, pat),
            count: n
        }
    }
}

impl<'a, M: LeftMatcher<'a>> NSplitsInternal<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        if self.count == 0 {
            let start = self.splits.prev_start;
            let s = self.splits.matcher.get_haystack();
            if self.splits.finished {
                None
            } else {
                self.splits.finished = true;
                Some(s.slice_from(start))
            }
        } else {
            self.count -= 1;
            self.splits.next()
        }
    }
}

impl<'a, M: RightMatcher<'a>> NSplitsInternal<M> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        if self.count == 0 {
            let end = self.splits.prev_end;
            let s = self.splits.matcher.get_haystack();
            if self.splits.finished {
                None
            } else {
                self.splits.finished = true;
                Some(s.slice_to(end))
            }
        } else {
            self.count -= 1;
            self.splits.next_back()
        }
    }
}

/// An iterator over all substrings of a `&str` split at the first `N`
/// non-overlapping matches of a string pattern matched from the front.
#[deriving(Clone)]
pub struct NSplits<M> {
    splits: NSplitsInternal<M>
}

impl<M> NSplits<M> {
    /// Constructor for `NSplits`.
    ///
    /// Can also be constructed with the `.splitn()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, n: uint, pat: P) -> NSplits<M> {
        NSplits {
            splits: NSplitsInternal::new(s, pat, n)
        }
    }
}

impl<'a, M: LeftMatcher<'a>> Iterator<&'a str> for NSplits<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.splits.next()
    }
}

/// An iterator over all substrings of a `&str` split at the last `N`
/// non-overlapping matches of a string pattern matched from the back.
#[deriving(Clone)]
pub struct RNSplits<M> {
    splits: NSplitsInternal<M>
}

impl<M> RNSplits<M> {
    /// Constructor for `RNSplits`.
    ///
    /// Can also be constructed with the `.rsplitn()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, n: uint, pat: P) -> RNSplits<M> {
        RNSplits {
            splits: NSplitsInternal::new(s, pat, n)
        }
    }
}

impl<'a, M: RightMatcher<'a>> Iterator<&'a str> for RNSplits<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.splits.next_back()
    }
}

////////////////////////////////////////////////////////////////////////////
// Implementation for `.split_terminator()` and `.rsplit_terminator()`
////////////////////////////////////////////////////////////////////////////

/// An iterator over all non-overlapping substrings of a `&str` split
/// at the match of a string pattern, not including a trailing empty string.
#[deriving(Clone)]
struct TermSplitsInternal<M> {
    splits: SplitsInternal<M>
}

impl<M> TermSplitsInternal<M> {
    #[inline]
    fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> TermSplitsInternal<M> {
        TermSplitsInternal {
            splits: SplitsInternal::new(s, pat)
        }
    }
}

impl<'a, M: LeftMatcher<'a>> TermSplitsInternal<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        let string = self.splits.matcher.get_haystack();
        loop {
            match splits_next(&mut self.splits) {
                Some((a, b)) if a == b && b == string.len() => continue,
                Some((a, b)) => return Some(string.slice(a, b)),
                None => return None
            }
        }
    }
}

impl<'a, M: RightMatcher<'a>> TermSplitsInternal<M> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        let string = self.splits.matcher.get_haystack();
        loop {
            match splits_next_back(&mut self.splits) {
                Some((a, b)) if a == b && b == string.len() => continue,
                Some((a, b)) => return Some(string.slice(a, b)),
                None => return None
            }
        }
    }
}

/// An iterator over all non-overlapping substrings of a `&str` split
/// at the match of a string pattern from the front,
/// not including a trailing empty string.
#[deriving(Clone)]
pub struct TermSplits<M> {
    splits: TermSplitsInternal<M>
}

impl<M> TermSplits<M> {
    /// Constructor of `TermSplits`
    ///
    /// Can also be constructed with the `.split_terminator()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> TermSplits<M> {
        TermSplits {
            splits: TermSplitsInternal::new(s, pat)
        }
    }
}

impl<'a, M: LeftMatcher<'a>> Iterator<&'a str> for TermSplits<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.splits.next()
    }
}

impl<'a, M: DoubleEndedMatcher<'a>> DoubleEndedIterator<&'a str> for TermSplits<M> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a str> {
        self.splits.next_back()
    }
}

/// An iterator over all non-overlapping substrings of a `&str` split
/// at the match of a string pattern from the back,
/// not including a trailing empty string.
#[deriving(Clone)]
pub struct RTermSplits<M> {
    splits: TermSplitsInternal<M>
}

impl<M> RTermSplits<M> {
    /// Constructor of `RTermSplits`
    ///
    /// Can also be constructed with the `.split_terminator()` method of `&str`.
    #[inline]
    pub fn new<'a, P: Pattern<'a, M>>(s: &'a str, pat: P) -> RTermSplits<M> {
        RTermSplits {
            splits: TermSplitsInternal::new(s, pat)
        }
    }
}

impl<'a, M: RightMatcher<'a>> Iterator<&'a str> for RTermSplits<M> {
    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        self.splits.next_back()
    }
}
