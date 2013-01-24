// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! An interface for numeric types
use cmp::Eq;
use option::{None, Option, Some};

pub trait Num {
    // FIXME: Trait composition. (#2616)
    pure fn add(&self, other: &self) -> self;
    pure fn sub(&self, other: &self) -> self;
    pure fn mul(&self, other: &self) -> self;
    pure fn div(&self, other: &self) -> self;
    pure fn modulo(&self, other: &self) -> self;
    pure fn neg(&self) -> self;

    pure fn to_int(&self) -> int;
    static pure fn from_int(n: int) -> self;
}

pub trait Zero {
    static pure fn zero() -> self;
}

pub trait One {
    static pure fn one() -> self;
}

pub trait Round {
    pure fn round(&self, mode: RoundMode) -> self;

    pure fn floor(&self) -> self;
    pure fn ceil(&self)  -> self;
    pure fn fract(&self) -> self;
}

pub enum RoundMode {
    RoundDown,
    RoundUp,
    RoundToZero,
    RoundFromZero
}

pub trait ToStrRadix {
    pub pure fn to_str_radix(&self, radix: uint) -> ~str;
}

pub trait FromStrRadix {
    static pub pure fn from_str_radix(str: &str, radix: uint) -> Option<self>;
}