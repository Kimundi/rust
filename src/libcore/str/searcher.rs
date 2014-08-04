// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// ignore-lexer-test FIXME #15679

use super::{raw, Str, StrSlice};

use clone::Clone;
use cmp;
use collections::Collection;
use iter::range;
use iter::{DoubleEndedIterator, ExactSize};
use iter::Iterator;
use option::{Option, None, Some};
use slice;
use slice::ImmutableSlice;
use uint;

type Ascii = u8; // Should be the actual `Ascii`, but it lives in std...

/// The internal state of an iterator that searches for matches of a substring
/// within a larger string using a dynamically chosen search algorithm
#[deriving(Clone)]
pub struct Searcher<'a, T> {
    haystack: &'a str,
    state: SearcherInternal<'a, T>
}

#[deriving(Clone)]
enum SearcherInternal<'a, T> {
    NaiveAscii(Ascii, Cursor),
    NaiveStr(T, Cursor),
    TwoWay(T, TwoWaySearcher),
    TwoWayLong(T, TwoWaySearcher)
}

impl<'a, T: Str> Searcher<'a, T> {
    /// Create a new searcher from a haystack and a needle
    #[inline]
    pub fn new(haystack: &'a str, needle: T) -> Searcher<'a, T> {
        if needle.as_slice().len() == 1 {
            let first_byte = unsafe {
                *needle.as_slice().as_bytes().unsafe_get(0)
            };
            Searcher {
                haystack: haystack,
                state: NaiveAscii(first_byte, Cursor {
                    start: 0,
                    end: haystack.len()
                })
            }
        } else if haystack.len() == 0
               || needle.as_slice().len() == 0
               || needle.as_slice().len() + 20 > haystack.len() {
            // FIXME: Tune this ^
            Searcher {
                haystack: haystack,
                state: NaiveStr(needle, Cursor {
                    start: 0,
                    end: haystack.len()
                })
            }
        } else {
            let searcher = TwoWaySearcher::new(haystack, needle.as_slice());
            if searcher.memory == uint::MAX { // If the period is long
                Searcher {
                    haystack: haystack,
                    state: TwoWayLong(needle, searcher)
                }
            } else {
                Searcher {
                    haystack: haystack,
                    state: TwoWay(needle, searcher)
                }
            }
        }
    }

    /// Return the original haystack string
    #[inline]
    pub fn get_haystack(&self) -> &'a str {
        self.haystack
    }

    /// Find the next match from the front
    #[inline]
    pub fn find_front(&mut self) -> Option<(uint, &'a str)> {
        let Searcher { haystack, ref mut state } = *self;
        match *state {
            NaiveAscii(needle, ref mut cursor) => unsafe {
                find_front_ascii(haystack, needle, cursor)
                    .map_slice_unchecked(haystack, 1)
            },
            NaiveStr(ref needle, ref mut cursor) => unsafe {
                find_front_str(haystack, needle.as_slice(), cursor)
                    .map_slice_unchecked(haystack, needle.as_slice().len())
            },
            TwoWay(ref needle, ref mut searcher) => unsafe {
                searcher.next(haystack, needle.as_slice(), false)
                    .map_slice_unchecked(haystack, needle.as_slice().len())
            },
            TwoWayLong(ref needle, ref mut searcher) => unsafe {
                searcher.next(haystack, needle.as_slice(), true)
                    .map_slice_unchecked(haystack, needle.as_slice().len())
            },
        }
    }

    /// Find the next match from the back
    #[inline]
    pub fn find_back(&mut self) -> Option<(uint, &'a str)> {
        let Searcher { haystack, ref mut state } = *self;
        match *state {
            NaiveAscii(needle, ref mut cursor) => unsafe {
                find_back_ascii(haystack, needle, cursor)
                    .map_slice_unchecked(haystack, 1)
            },
            NaiveStr(ref needle, ref mut cursor)                          |
            TwoWay(ref needle, TwoWaySearcher { ref mut cursor, .. })     |
            TwoWayLong(ref needle, TwoWaySearcher { ref mut cursor, .. }) => unsafe {
                // FIXME: Implement TwoWaySearch for reverse searching
                find_back_str(haystack, needle.as_slice(), cursor)
                    .map_slice_unchecked(haystack, needle.as_slice().len())
            },
        }
    }
}

#[deriving(Clone)]
struct Cursor {
    start: uint,
    end: uint
}

/// A little something to make the implementation of Searcher less verbose
trait SliceHelper {
    /// Maps a start index and length to a start index and string slice
    unsafe fn map_slice_unchecked<'a>(self,
                                      haystack: &'a str,
                                      len: uint) -> Option<(uint, &'a str)>;
}

impl SliceHelper for Option<uint> {
    #[inline]
    unsafe fn map_slice_unchecked<'a>(self,
                                      haystack: &'a str,
                                      len: uint) -> Option<(uint, &'a str)> {
        self.map(|start| (start, raw::slice_unchecked(haystack, start, start + len)))
    }
}

#[inline]
fn find_front_ascii<'a>(haystack: &'a str,
                        needle: Ascii,
                        cursor: &mut Cursor) -> Option<uint> {
    while cursor.start < cursor.end {
        let start = cursor.start;
        cursor.start += 1;
        let current = unsafe {
            *haystack.as_bytes().unsafe_get(start)
        };
        if current == needle {
            return Some(start);
        }
    }
    None
}

#[inline]
fn find_back_ascii<'a>(haystack: &'a str,
                       needle: Ascii,
                       cursor: &mut Cursor) -> Option<uint> {
    while cursor.start < cursor.end {
        let end = cursor.end;
        cursor.end -= 1;
        let current = unsafe {
            *haystack.as_bytes().unsafe_get(end - 1)
        };
        if current == needle {
            return Some(end - 1);
        }
    }
    None
}

#[inline]
fn find_front_str<'a>(haystack: &'a str,
                      needle: &str,
                      cursor: &mut Cursor) -> Option<uint> {
    // start can end up as -1
    while (cursor.start + needle.len()) as int <= cursor.end as int {
        let start = cursor.start;
        let needle_candidate = unsafe {
            slice::raw::slice_unchecked(haystack.as_bytes(),
                                        start,
                                        start + needle.len())
        };
        if needle_candidate == needle.as_bytes() {
            // needle might be empty
            cursor.start += cmp::max(needle.len(), 1);
            return Some(start);
        } else {
            cursor.start += 1;
        }
    }
    None
}

#[inline]
fn find_back_str<'a>(haystack: &'a str,
                     needle: &str,
                     cursor: &mut Cursor) -> Option<uint> {
    // start can end up as -1
    while (cursor.start + needle.len()) as int <= cursor.end as int{
        let end = cursor.end;
        let needle_candidate = unsafe {
            slice::raw::slice_unchecked(haystack.as_bytes(),
                                        end - needle.len(),
                                        end)
        };
        if needle_candidate == needle.as_bytes() {
            // needle might be empty
            cursor.end -= cmp::max(needle.len(), 1);
            return Some(end - needle.len());
        } else {
            cursor.end -= 1;
        }
    }
    None
}

/// The internal state of an iterator that searches for matches of a substring
/// within a larger string using two-way search
#[deriving(Clone)]
struct TwoWaySearcher {
    // constants
    critPos: uint,
    period: uint,
    byteset: u64,

    // variables
    cursor: Cursor,
    memory: uint
}

impl TwoWaySearcher {
    #[inline(never)]
    fn new(haystack: &str, needle: &str) -> TwoWaySearcher {
        let needle = needle.as_bytes();
        let (critPos1, period1) = TwoWaySearcher::maximal_suffix(needle);
        let (critPos2, period2) = TwoWaySearcher::maximal_suffix_reversed(needle);

        let critPos;
        let period;
        if critPos1 > critPos2 {
            critPos = critPos1;
            period = period1;
        } else {
            critPos = critPos2;
            period = period2;
        }

        let byteset = needle.iter()
                            .fold(0, |a, &b| (1 << ((b & 0x3f) as uint)) | a);
        let cursor = Cursor { start: 0, end: haystack.len() };
        if needle.slice_to(critPos) == needle.slice_from(needle.len() - critPos) {
            TwoWaySearcher {
                critPos: critPos,
                period: period,
                byteset: byteset,

                cursor: cursor,
                memory: 0
            }
        } else {
            TwoWaySearcher {
                critPos: critPos,
                period: cmp::max(critPos, needle.len() - critPos) + 1,
                byteset: byteset,

                cursor: cursor,
                memory: uint::MAX // Dummy value to signify that the period is long
            }
        }
    }

    /// Beware!
    /// This function does not do bounds checking and also doesn't like getting
    /// called with empty strings
    #[inline]
    unsafe fn next(&mut self, haystack: &str, needle: &str, longPeriod: bool) -> Option<uint> {
        let haystack = |i: uint| *haystack.as_bytes().unsafe_get(i);
        let needle = needle.as_bytes();
        'search: loop {
            // Check that we have room to search in
            if self.cursor.start + needle.len() > self.cursor.end {
                return None;
            }

            // Quickly skip by large portions unrelated to our substring
            if (self.byteset >>
                    ((haystack(self.cursor.start + needle.len() - 1) & 0x3f)
                     as uint)) & 1 == 0 {
                self.cursor.start += needle.len();
                continue 'search;
            }

            // See if the right part of the needle matches
            let start = if longPeriod { self.critPos } else { cmp::max(self.critPos, self.memory) };
            for i in range(start, needle.len()) {
                if needle[i] != haystack(self.cursor.start + i) {
                    self.cursor.start += i - self.critPos + 1;
                    if !longPeriod {
                        self.memory = 0;
                    }
                    continue 'search;
                }
            }

            // See if the left part of the needle matches
            let start = if longPeriod { 0 } else { self.memory };
            for i in range(start, self.critPos).rev() {
                if needle[i] != haystack(self.cursor.start + i) {
                    self.cursor.start += self.period;
                    if !longPeriod {
                        self.memory = needle.len() - self.period;
                    }
                    continue 'search;
                }
            }

            // We have found a match!
            let matchPos = self.cursor.start;
            self.cursor.start += needle.len(); // add self.period for all matches
            if !longPeriod {
                self.memory = 0; // set to needle.len() - self.period for all matches
            }
            return Some(matchPos);
        }
    }

    /// This is mostly duplication with `maximal_suffix()` because
    /// llvm does not remove the bound checks if the code gets merged with
    /// an "is reversed" conditional in the loop
    #[inline]
    fn maximal_suffix_reversed(arr: &[u8]) -> (uint, uint) {
        let mut left = -1; // Corresponds to i in the paper
        let mut right = 0; // Corresponds to j in the paper
        let mut offset = 1; // Corresponds to k in the paper
        let mut period = 1; // Corresponds to p in the paper

        while right + offset < arr.len() {
            let a = arr[left + offset];
            let b = arr[right + offset];
            if a < b {
                // Suffix is smaller, period is entire prefix so far.
                right += offset;
                offset = 1;
                period = right - left;
            } else if a == b {
                // Advance through repetition of the current period.
                if offset == period {
                    right += offset;
                    offset = 1;
                } else {
                    offset += 1;
                }
            } else {
                // Suffix is larger, start over from current location.
                left = right;
                right += 1;
                offset = 1;
                period = 1;
            }
        }
        (left + 1, period)
    }

    /// This is mostly duplication with `maximal_suffix_reversed()` because
    /// llvm does not remove the bound checks if the code gets merged with
    /// an "is reversed" conditional in the loop
    #[inline]
    fn maximal_suffix(arr: &[u8]) -> (uint, uint) {
        let mut left = -1; // Corresponds to i in the paper
        let mut right = 0; // Corresponds to j in the paper
        let mut offset = 1; // Corresponds to k in the paper
        let mut period = 1; // Corresponds to p in the paper

        while right + offset < arr.len() {
            let a = arr[right + offset];
            let b = arr[left + offset];
            if a < b {
                // Suffix is smaller, period is entire prefix so far.
                right += offset;
                offset = 1;
                period = right - left;
            } else if a == b {
                // Advance through repetition of the current period.
                if offset == period {
                    right += offset;
                    offset = 1;
                } else {
                    offset += 1;
                }
            } else {
                // Suffix is larger, start over from current location.
                left = right;
                right += 1;
                offset = 1;
                period = 1;
            }
        }
        (left + 1, period)
    }
}
