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
use core::cmp::{Ord, Eq};
use option::{None, Option, Some};
use char;
use str;
use kinds::Copy;
use vec;

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
    pure fn round_to_integer(&self, mode: RoundModeInteger) -> self;
    
    pure fn floor(&self) -> self;
    pure fn ceil(&self)  -> self;
    pure fn fract(&self) -> self;
}

pub enum RoundModeInteger {
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

// Generic math functions:

/// Dynamically calculates the value `inf` (`1/0`).
/// Can fail on integer types.
#[inline(always)]
pub pure fn infinity<T: Num One Zero>() -> T {
    let _0: T = Zero::zero();
    let _1: T = One::one();
    _1 / _0
}

/// Dynamically calculates the value `-inf` (`-1/0`).
/// Can fail on integer types.
#[inline(always)]
pub pure fn neg_infinity<T: Num One Zero>() -> T {
    let _0: T = Zero::zero();
    let _1: T = One::one();
    - _1 / _0
}

/// Dynamically calculates the value `NaN` (`0/0`).
/// Can fail on integer types.
#[inline(always)]
pub pure fn NaN<T: Num Zero>() -> T {
    let _0: T = Zero::zero();
    _0 / _0
}

/// Returns `true` if `num` has the value `inf` (`1/0`).
/// Can fail on integer types.
#[inline(always)]
pub pure fn is_infinity<T: Num One Zero Eq>(num: &T) -> bool {
    (*num) == (infinity::<T>())
}

/// Returns `true` if `num` has the value `-inf` (`-1/0`).
/// Can fail on integer types.
#[inline(always)]
pub pure fn is_neg_infinity<T: Num One Zero Eq>(num: &T) -> bool {
    (*num) == (neg_infinity::<T>())
}

/// Returns `true` if `num` has the value `NaN` (is not equal to itself).
#[inline(always)]
pub pure fn is_NaN<T: Num Eq>(num: &T) -> bool {
    (*num) != (*num)
}

/// Returns `true` if `num` has the value `-0` (`1/num == -1/0`).
/// Can fail on integer types.
#[inline(always)]
pub pure fn is_neg_zero<T: Num One Zero Eq>(num: &T) -> bool {
    let _1: T = One::one();
    let _0: T = Zero::zero();
    *num == _0 && is_neg_infinity(&(_1 / *num))
}

/**
 * Calculates a power to a given radix, optimized for uint `pow` and `radix`.
 *
 * Returns `radix^pow` as `T`.
 *
 * Note:
 * Also returns `1` for `0^0`, despite that technically being an
 * undefined number. The reason for this is twofold:
 * - If code written to use this function cares about that special case, it's
 *   probably going to catch it before making the call.
 * - If code written to use this function doesn't care about it, it's
 *   probably assuming that `x^0` always equals `1`.
 */
pub pure fn pow_with_uint<T: Num One Zero>(radix: uint, pow: uint) -> T {
    let _0: T = Zero::zero();
    let _1: T = One::one();

    if pow   == 0u { return _1; }
    if radix == 0u { return _0; }
    let mut my_pow     = pow;
    let mut total      = _1;
    let mut multiplier = Num::from_int(radix as int);
    while (my_pow > 0u) {
        if my_pow % 2u == 1u {
            total *= multiplier;
        }
        my_pow     /= 2u;
        multiplier *= multiplier;
    }
    total
}

pub enum ExponentFormat {
    ExpNone,
    ExpDec,
    ExpBin
}

pub enum SignificantDigits {
    DigAll,
    DigMax(uint),
    DigExact(uint)
}

pub enum SignFormat {
    SignNone,
    SignNeg,
    SignAll
}

use io;

priv pure fn ioprint(s: &str) {
    unsafe {
        io::print(s);
        io::print("\n");
    }
}

use int;

/**
 * Converts a number to its string representation as a byte vector.
 * This is meant to be a common base implementation for all numeric string
 * conversion functions like `to_str()` or `to_str_radix()`.
 *
 * # Arguments
 * - `num`           - The number to convert. Accepts any number that
 *                     implements the numeric traits.
 * - `radix`         - Base to use. Accepts only the values 2-36.
 * - `special`       - Whether to attempt to compare to special values like
 *                     `inf` or `NaN`. Also needed to detect negative 0.
 *                     Can fail if it doesn't match `num`s type
 *                     (see safety note).
 * - `negative_zero` - Whether to treat the special value `-0` as
 *                     `-0` or as `+0`.
 * - `sign`          - How to emit the sign. Options are:
 *     - `SignNone`: No sign at all. Basically emits `abs(num)`.
 *     - `SignNeg`:  Only `-` on negative values.
 *     - `SignAll`:  Both `+` on positive, and `-` on negative numbers.
 * - `digits`        - The amount of digits to use for emitting the
 *                     fractional part, if any. Options are:
 *     - `DigAll`:         All calculatable digits. Beware of bignums or
 *                         fractions!
 *     - `DigMax(uint)`:   Maximum N digits, truncating any trailing zeros.
 *     - `DigExact(uint)`: Exactly N digits.
 *
 * # Return value
 * A tuple containing the byte vector, and a boolean flag indicating
 * whether it represents a special value like `inf`, `-inf`, `NaN` or not.
 * It returns a tuple because there can be ambiguity between a special value
 * and a number representation at higher bases.
 *
 * # Failure
 * - Fails if `radix` < 2 or `radix` > 36.
 * - Fails on wrong value for `special` (see safety note).
 *
 * # Safety note
 * The function detects the special values `inf`, `-inf` and `NaN` by
 * dynamically comparing `num` to `1 / 0`, `-1 / 0` and `0 / 0`
 * (each of type T) if `special` is `true`. This will fail on integer types
 * with a 'divide by zero'. Likewise, it will fail if `num` **is** one of
 * those special values, and `special` is `false`, because then the
 * algorithm just does normal calculations on them.
 *
 * # Possible improvements
 * - Currently performs no rounding if truncating trailing digits.
 * - Make function handle numbers with expensive copies better.
 */
pub pure fn num_to_str(i: int, radix: uint) -> ~str {
    return int::to_str_bytes_orig(i, radix, |bytes| {
        str::from_bytes(bytes)
    })
}


pub pure fn to_str_bytes_common<T: Num Zero One Eq Ord Round Copy>(
        num: &T, radix: uint, special: bool, negative_zero: bool,
        sign: SignFormat, digits: SignificantDigits) -> (~[u8], bool) {
    //ioprint(fmt!("to_str_bytes args: %?, %?, %?, %?, %?, %?", num, radix, special, negative_zero, sign, digits));
    if radix as int <  2 {
        fail fmt!("to_str_bytes_common: radix %? to low, \
                   must lie in the range [2, 36]", radix);
    } else if radix as int > 36 {
        fail fmt!("to_str_bytes_common: radix %? to low, \
                   must lie in the range [2, 36]", radix);
    }

    let _0: T = Zero::zero();
    let _1: T = One::one();

    if special {
        if is_NaN(num) {
            return (str::to_bytes("NaN"), true);
        } else if is_infinity(num){
            return match sign {
                SignAll => (str::to_bytes("+inf"), true),
                _       => (str::to_bytes("inf"), true)
            }
        } else if is_neg_infinity(num) {
            return match sign {
                SignNone => (str::to_bytes("inf"), true),
                _        => (str::to_bytes("-inf"), true),
            }
        }
    }

    let neg = *num < _0 || (negative_zero && *num == _0
                            && special && is_neg_zero(num));
    //let num_abs        = if (neg) { -*num } else { *num };
    let mut buf: ~[u8] = ~[];
    let mut deccum     = num.round_to_integer(RoundToZero);
    let radix_gen      = Num::from_int::<T>(radix as int);

    let (limit_digits, max_digits, exact) = match digits {
        DigAll          => (false, 0u, false),
        DigMax(count)   => (true, count, false),
        DigExact(count) => (true, count, true)
    };

    // make sure we have at least a leading '0' by looping at least once
    loop {
        let current_digit = deccum % radix_gen;
        let current_digit = if current_digit < _0 { -current_digit } else { current_digit };
        
        deccum /= radix_gen;
        deccum = deccum.round_to_integer(RoundToZero);
        unsafe { // FIXME: Pureness workaround (#4568)
            match char::from_digit(current_digit.to_int() as uint, radix) {
                Some(cc) => buf.push(cc as u8),
                None     => {
                    ioprint("option unwrap fail");
                    ioprint(fmt!("from_dig args: %?, %?", current_digit.to_int(), radix));
                    ioprint(fmt!("from_dig args: %?, %?", current_digit.to_int() as uint, radix));
                    let num_s = num_to_str(num.to_int(), radix);
                    ioprint(fmt!("to_str_bytes args: %?, %?, %?, %?, %?, %?", num_s, radix, special, negative_zero, sign, digits));
                    let num_s = num_to_str((num/Num::from_int(10000)).to_int(), radix);
                    ioprint(fmt!("to_str_bytes args: %?, %?, %?, %?, %?, %?", num_s, radix, special, negative_zero, sign, digits));
                    
                    
                    fail ~"option unwrap fail";
                }
            }
            
        }
        if (deccum == _0) { break; }
    }

    let digits_start;

    // Decide what sign to put in front:
    match sign {
        SignNone => {
            digits_start = 0
        }
        SignNeg | SignAll if neg => {
            unsafe { // FIXME: Pureness workaround (#4568)
                buf.push('-' as u8);
            }
            digits_start = 1;
        }
        SignNeg => {
            digits_start = 0;
        }
        SignAll => {
            unsafe { // FIXME: Pureness workaround (#4568)
                buf.push('+' as u8);
            }
            digits_start = 1;
        }
    }
    unsafe { // FIXME: Pureness workaround (#4568)
        vec::reverse(buf);
    }
    deccum = num.fract();
    if deccum != _0 || (limit_digits && exact && max_digits > 0){
        unsafe { // FIXME: Pureness workaround (#4568)
            buf.push('.' as u8);
        }
        let mut dig = 0u;

        while                           // calculate new digits while
        (!limit_digits && deccum != _0)  // - there is no limit and
        || (limit_digits &&             //   there are digits left
            dig < max_digits && (       // - or there is a limit,
                exact ||                //   it's not reached yet and
                (!exact && deccum != _0) //   - it's exact
            )                           //   - or it's a maximum,
        ) {                             //     and there are still digits left
            deccum *= radix_gen;
            let current_digit = deccum.round_to_integer(RoundToZero);
            unsafe { // FIXME: Pureness workaround (#4568)
                match char::from_digit(current_digit.to_int() as uint, radix) {
                    Some(cc) => buf.push(cc as u8),
                    None     => {
                    ioprint("option unwrap fail");
                    ioprint(fmt!("from_dig args: %?, %?", current_digit.to_int(), radix));
                    ioprint(fmt!("from_dig args: %?, %?", current_digit.to_int() as uint, radix));
                    ioprint(fmt!("to_str_bytes args: %?, %?, %?, %?, %?, %?", num, radix, special, negative_zero, sign, digits));
                    fail ~"option unwrap fail";
                    }
                }
            }
            deccum = deccum.fract();
            dig += 1u;
        }
    }

    // if number of digits is not exact, remove all trailing '0's up to
    // and including the '.'
    if !exact {
        let mut i = buf.len() - 1;
        while buf[i] == '0' as u8 && buf.len() > digits_start + 1 {
            i -= 1;
        }

        // Truncate only if trailing zeros of *fractional* part:
        if buf[i] == '.' as u8 {
            i -= 1;
            buf = buf.slice(0, i + 1);
        }
    }

    (buf, false)
}

/**
 * Converts a number to its string representation. This is a wrapper for
 * `to_str_bytes_common()`, for details see there.
 */
#[inline(always)]
pub pure fn to_str_common<T: Num Zero One Eq Ord Round Copy>(
        num: &T, radix: uint, special: bool, negative_zero: bool,
        sign: SignFormat, digits: SignificantDigits) -> (~str, bool) {
    let (bytes, special) = to_str_bytes_common(num, radix, special,
                               negative_zero, sign, digits);
    (str::from_bytes(bytes), special)
}

// Some constants for from_str_bytes_common's input validation,
// they define minimum radix values for which the character is a valid digit.
priv const DIGIT_P_RADIX: uint = ('p' as uint) - ('a' as uint) + 11u;
priv const DIGIT_I_RADIX: uint = ('i' as uint) - ('a' as uint) + 11u;
priv const DIGIT_E_RADIX: uint = ('e' as uint) - ('a' as uint) + 11u;

/**
 * Parses a byte slice as a number. This is meant to
 * be a common base implementation for all numeric string conversion
 * functions like `from_str()` or `from_str_radix()`.
 *
 * # Arguments
 * - `buf`        - The byte slice to parse.
 * - `radix`      - Which base to parse the number as. Accepts 2-36.
 * - `negative`   - Whether to accept negative numbers.
 * - `fractional` - Whether to accept numbers with fractional parts.
 * - `special`    - Whether to accept special values like `inf`
 *                  and `NaN`. Can conflict with `radix`, see Failure.
 * - `exponent`   - Which exponent format to accept. Options are:
 *     - `ExpNone`: No Exponent, accepts just plain numbers like `42` or
 *                  `-8.2`.
 *     - `ExpDec`:  Accepts numbers with a decimal exponent like `42e5` or
 *                  `8.2E-2`. The exponent string itself is always base 10.
 *                  Can conflict with `radix`, see Failure.
 *     - `ExpBin`:  Accepts numbers with a binary exponent like `42P-8` or
 *                  `FFp128`. The exponent string itself is always base 10.
 *                  Can conflict with `radix`, see Failure.
 * - `empty_zero` - Whether to accept a empty `buf` as a 0 or not.
 *
 * # Return value
 * Returns `Some(n)` if `buf` successfully parses to a number n, or `None` if
 * `buf`s content is not parsable, depending on the constraints set by the
 * other arguments.
 *
 * # Failure
 * - Fails if `radix` < 2 or `radix` > 36.
 * - Fails if `radix` > 14 and `exponent` is `ExpDec` due to conflict
 *   between digit and exponent sign `'e'`.
 * - Fails if `radix` > 25 and `exponent` is `ExpBin` due to conflict
 *   between digit and exponent sign `'p'`.
 * - Fails if `radix` > 18 and `special == true` due to conflict
 *   between digit and lowest first character in `inf` and `NaN`, the `'i'`.
 *
 * # Possible improvements
 * - Could accept option to allow ignoring underscores, allowing for numbers
 *   formated like `FF_AE_FF_FF`.
 */
pub pure fn from_str_bytes_common<T: Num Zero One Copy>(
        buf: &[u8], radix: uint, negative: bool, fractional: bool,
        special: bool, exponent: ExponentFormat, empty_zero: bool
        ) -> Option<T> {
    //ioprint(fmt!("from_str_bytes args: %?, %?, %?, %?, %?, %?, %?", buf, radix, negative, fractional, special, exponent, empty_zero));

    match exponent {
        ExpDec if radix >= DIGIT_E_RADIX       // decimal exponent 'e'
          => fail fmt!("from_str_bytes_common: radix %? incompatible with \
                        use of 'e' as decimal exponent", radix),
        ExpBin if radix >= DIGIT_P_RADIX       // binary exponent 'p'
          => fail fmt!("from_str_bytes_common: radix %? incompatible with \
                        use of 'p' as binary exponent", radix),
        _ if special && radix >= DIGIT_I_RADIX // first digit of 'inf'
          => fail fmt!("from_str_bytes_common: radix %? incompatible with \
                        special values 'inf' and 'NaN'", radix),
        _ if radix as int < 2
          => fail fmt!("from_str_bytes_common: radix %? to low, \
                        must lie in the range [2, 36]", radix),
        _ if radix as int > 36
          => fail fmt!("from_str_bytes_common: radix %? to high, \
                        must lie in the range [2, 36]", radix),
        _ => ()
    }

    let _0: T = Zero::zero();
    let _1: T = One::one();
    let radix_gen: T = Num::from_int(radix as int);

    let len = buf.len();

    if len == 0 {
        if empty_zero {
            return Some(_0);
        } else {
            return None;
        }
    }

    if special {
        if buf == str::to_bytes("inf") || buf == str::to_bytes("+inf") {
            return Some(infinity());
        } else if buf == str::to_bytes("-inf") {
            if negative {
                return Some(neg_infinity());
            } else {
                return None;
            }
        } else if buf == str::to_bytes("NaN") {
            return Some(NaN());
        }
    }

    let (start, sign) = match buf[0] {
      '-' as u8 if !negative => return None,
      '-' as u8 => (1u, -_1),
      '+' as u8 => (1u,  _1),
       _        => (0u,  _1)
    };

    let mut accum     = _0;
    let mut i         = start;
    let mut exp_found = false;

    while i < len {
        let c = buf[i] as char;

        match char::to_digit(c, radix) {
            Some(digit) => {
                accum *= radix_gen;                   // move accum one left
                accum += Num::from_int(digit as int); // add current position
            }
            None => match c {
                'e' | 'E' | 'p' | 'P' => {
                    exp_found = true;
                    break;                       // start of exponent
                }
                '.' if fractional => {
                    i += 1u;                     // skip the '.'
                    break;                       // start of fractional part
                }
                _ => return None                 // invalid number
            }
        }

        i += 1u;
    }

    if !exp_found {                              // prevents 2. parse attempt
        let mut power = _1;

        while i < len {
            let c = buf[i] as char;

            match char::to_digit(c, radix) {
                Some(digit) => {
                    power /= radix_gen;
                    accum += Num::from_int::<T>(digit as int) * power;
                }
                None => match c {
                    'e' | 'E' | 'p' | 'P' => {
                        exp_found = true;
                        break;                   // start of exponent
                    }
                    _ => return None             // invalid number
                }
            }

            i += 1u;
        }
    }

    // Special case: buf not empty, but does not contain any digit in front
    // of the exponent sign
    if i == start {
        if empty_zero {
            return Some(_0);
        } else {
            return None;
        }
    }

    let mut multiplier = _1;

    if exp_found {
        let c = buf[i] as char;
        let base = match (c, exponent) {
            ('e', ExpDec) | ('E', ExpDec) => 10u,
            ('p', ExpBin) | ('P', ExpBin) => 2u,
            _ => return None // char doesn't fit given exponent format
        };

        // parse remaining bytes as decimal integer,
        // skipping the exponent char
        let exp: Option<int> = from_str_bytes_common(
            buf.view(i+1, len), 10, true, false, false, ExpNone, false);

        match exp {
            Some(exp_pow) => {
                multiplier = if exp_pow < 0 {
                    _1 / pow_with_uint::<T>(base, (-exp_pow.to_int()) as uint)
                } else {
                    pow_with_uint::<T>(base, exp_pow.to_int() as uint)
                }
            }
            None => return None // invalid exponent; invalid number
        }
    }

    Some(sign * accum * multiplier)
}

/**
 * Parses a string as a number. This is a wrapper for
 * `from_str_bytes_common()`, for details see there.
 */
#[inline(always)]
pub pure fn from_str_common<T: Num Zero One Copy>(
        buf: &str, radix: uint, negative: bool, fractional: bool,
        special: bool, exponent: ExponentFormat, empty_zero: bool
        ) -> Option<T> {
    from_str_bytes_common(str::to_bytes(buf), radix, negative,
                            fractional, special, exponent, empty_zero)
}