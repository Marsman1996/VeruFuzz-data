//! num-integer **harness zone** -- the Average property assertion theorems.
//! This file = the transcription vehicle of
//! tests/average.rs (3 cases each of ceil/floor at 6 widths + the
//! extreme-neighborhood overflow invariants) and of the code/src/average.rs
//! doc examples (:14-20 / :32-40).
//!
//! Structure (reference-style organization, the product rule): the
//! upstream exec transcriptions and their contract/bit-level bridges went back
//! to the **src zone** verified/src/average.rs (the single library-side fact
//! source); this file references it via `#[path] mod` without copying specs or
//! lemmas; the assertion theorems are proven along the "example -> call the
//! contract -> spec constant folding" chain (z3 fully evaluates concrete ints).
//!
//! Coverage map:
//!   - tests/average.rs:8-15  ceil same_sign (the i64 width; :33-50 is the
//!     same-shaped floor block)
//!   - tests/average.rs:18-25 ceil different_sign (the MIN/MAX neighborhood)
//!   - tests/average.rs:30-39 floor same_sign / :43-49 different_sign
//!   - tests/average.rs:57-68 u8..u128 bounded/overflow (the u64/u8 widths)
//!   - the doc examples average.rs:14-20 / :32-40 (the i8/u8 widths)
//!
//! Run: VERUS_Z3_PATH=<z3> <verus> database/num-integer/verified/harness/average.rs
//! Reading the output: expected Nv/0e.

use vstd::prelude::*;

#[path = "../src/average.rs"]
mod average_src;
use average_src::{
    average_ceil_upstream_i64, average_ceil_upstream_i8, average_ceil_upstream_u64,
    average_ceil_upstream_u8, average_floor_upstream_i64, average_floor_upstream_i8,
    average_floor_upstream_u64, average_floor_upstream_u8,
};

verus! {

// =========================================================================
// 1. i64 instances -- the tests/average.rs i64 module (6 cases after the macro expansion)
// =========================================================================

/// tests/average.rs:4-25 (i64::ceil) + the doc examples average.rs:15-20.
pub exec fn ut_average_ceil_examples_i64() -> (ok: bool)
    ensures
        ok == true,
{
    // same_sign (tests:9-14)
    let a = average_ceil_upstream_i64(14, 16);
    if a != 15 { return false; }
    let b = average_ceil_upstream_i64(14, 17);
    if b != 16 { return false; }
    let max: i64 = 9223372036854775807;
    let c = average_ceil_upstream_i64(max - 3, max - 1);          // tests:13
    if c != max - 2 { return false; }
    let d = average_ceil_upstream_i64(max - 3, max - 2);          // tests:14
    if d != max - 2 { return false; }
    // different_sign (tests:19-24)
    let e = average_ceil_upstream_i64(14, -4);
    if e != 5 { return false; }
    let f = average_ceil_upstream_i64(14, -5);                    // tests:20
    if f != 5 { return false; }
    let min: i64 = 0 - 9223372036854775807 - 1;
    let g = average_ceil_upstream_i64(min, max);                  // tests:24
    if g != 0 { return false; }
    true
}

/// tests/average.rs:28-49 (i64::floor) + the doc examples average.rs:33-39.
pub exec fn ut_average_floor_examples_i64() -> (ok: bool)
    ensures
        ok == true,
{
    let a = average_floor_upstream_i64(14, 16);
    if a != 15 { return false; }
    let b = average_floor_upstream_i64(14, 17);                   // tests:34
    if b != 15 { return false; }
    let max: i64 = 9223372036854775807;
    let c = average_floor_upstream_i64(max - 3, max - 1);        // tests:37
    if c != max - 2 { return false; }
    let d = average_floor_upstream_i64(max - 3, max - 2);        // tests:38
    if d != max - 3 { return false; }
    let e = average_floor_upstream_i64(14, -4);                   // tests:43
    if e != 5 { return false; }
    let f = average_floor_upstream_i64(14, -5);                   // tests:44
    if f != 4 { return false; }
    let min: i64 = 0 - 9223372036854775807 - 1;
    let g = average_floor_upstream_i64(min, max);                 // tests:48
    if g != -1 { return false; }
    true
}

// =========================================================================
// 2. u64 instances -- the tests/average.rs u64 module
// =========================================================================

/// tests/average.rs:56-68 (u64: ceil bounded + overflow).
pub exec fn ut_average_ceil_examples_u64() -> (ok: bool)
    ensures
        ok == true,
{
    let a = average_ceil_upstream_u64(14, 16);
    if a != 15 { return false; }
    let b = average_ceil_upstream_u64(14, 17);
    if b != 16 { return false; }
    let max: u64 = 18446744073709551615;
    let c = average_ceil_upstream_u64(max - 3, max - 1);          // tests:66
    if c != max - 2 { return false; }
    let d = average_ceil_upstream_u64(max - 3, max - 2);          // tests:67
    if d != max - 2 { return false; }
    true
}

/// tests/average.rs:73-85 (u64: floor bounded + overflow).
pub exec fn ut_average_floor_examples_u64() -> (ok: bool)
    ensures
        ok == true,
{
    let a = average_floor_upstream_u64(14, 16);
    if a != 15 { return false; }
    let b = average_floor_upstream_u64(14, 17);                   // tests:76
    if b != 15 { return false; }
    let max: u64 = 18446744073709551615;
    let c = average_floor_upstream_u64(max - 3, max - 1);        // tests:83
    if c != max - 2 { return false; }
    let d = average_floor_upstream_u64(max - 3, max - 2);        // tests:84
    if d != max - 3 { return false; }
    true
}

// =========================================================================
// 3. u8 / i8 instances -- tests/average.rs + the doc examples (average.rs:12-40)
// =========================================================================

/// The doc examples average.rs:18-20 + the tests/average.rs u8 macro expansion.
pub exec fn ut_average_ceil_examples_u8() -> (ok: bool)
    ensures
        ok == true,
{
    // tests u8 bounded (:59-60)
    let a = average_ceil_upstream_u8(14, 16);
    if a != 15 { return false; }
    let b = average_ceil_upstream_u8(14, 17);
    if b != 16 { return false; }
    // tests u8 overflow (:65-67)
    let max: u8 = 255;
    let c = average_ceil_upstream_u8(max - 3, max - 1);
    if c != max - 2 { return false; }
    let d = average_ceil_upstream_u8(max - 3, max - 2);
    if d != max - 2 { return false; }
    // doc average.rs:18  `u8::max_value().average_ceil(&2) == 129`
    let e0 = average_ceil_upstream_u8(255, 2);
    if e0 != 129 { return false; }
    true
}

/// The doc examples average.rs:14-16, ceil i8.
pub exec fn ut_average_ceil_examples_i8() -> (ok: bool)
    ensures
        ok == true,
{
    // `( 3).average_ceil(&10) == 7`
    let a = average_ceil_upstream_i8(3, 10);
    if a != 7 { return false; }
    // `(-2).average_ceil(&-5) == -3`
    let b = average_ceil_upstream_i8(-2, -5);
    if b != -3 { return false; }
    // `( 4).average_ceil(& 4) == 4`
    let c = average_ceil_upstream_i8(4, 4);
    if c != 4 { return false; }
    // `i8::min_value().average_ceil(&-1) == -64`
    let min: i8 = 0 - 127 - 1;
    let d = average_ceil_upstream_i8(min, -1);
    if d != -64 { return false; }
    // `i8::min_value().average_ceil(&i8::max_value()) == 0`
    let e = average_ceil_upstream_i8(min, 127);
    if e != 0 { return false; }
    // tests i8 isomorphic: same_sign / different_sign (:8-25 macro expansion)
    let f = average_ceil_upstream_i8(14, 16);
    if f != 15 { return false; }
    let g = average_ceil_upstream_i8(14, -5);
    if g != 5 { return false; }
    true
}

/// The doc examples average.rs:32-34 (floor i8) + the :37 u8 example.
pub exec fn ut_average_floor_examples_i8() -> (ok: bool)
    ensures
        ok == true,
{
    // `( 3).average_floor(&10) == 6`
    let a = average_floor_upstream_i8(3, 10);
    if a != 6 { return false; }
    // `(-2).average_floor(&-5) == -4`
    let b = average_floor_upstream_i8(-2, -5);
    if b != -4 { return false; }
    // `( 4).average_floor(& 4) == 4`
    let c = average_floor_upstream_i8(4, 4);
    if c != 4 { return false; }
    // `i8::min_value().average_floor(&-1) == -65`
    let min: i8 = 0 - 127 - 1;
    let d = average_floor_upstream_i8(min, -1);
    if d != -65 { return false; }
    // `i8::min_value().average_floor(&i8::max_value()) == -1`
    let e = average_floor_upstream_i8(min, 127);
    if e != -1 { return false; }
    // tests i8 isomorphic (:33-34)
    let f = average_floor_upstream_i8(14, 16);
    if f != 15 { return false; }
    let g = average_floor_upstream_i8(14, -5);
    if g != 4 { return false; }
    true
}

/// The doc example average.rs:37 (u8 floor) + tests u8 floor bounded/overflow.
pub exec fn ut_average_floor_examples_u8() -> (ok: bool)
    ensures
        ok == true,
{
    // `u8::max_value().average_floor(&2) == 128`
    let e0 = average_floor_upstream_u8(255, 2);
    if e0 != 128 { return false; }
    // tests u8 floor bounded (:74-77)
    let a = average_floor_upstream_u8(14, 16);
    if a != 15 { return false; }
    let b = average_floor_upstream_u8(14, 17);
    if b != 15 { return false; }
    // tests u8 floor overflow (:83-84)
    let max: u8 = 255;
    let c = average_floor_upstream_u8(max - 3, max - 1);
    if c != max - 2 { return false; }
    let d = average_floor_upstream_u8(max - 3, max - 2);
    if d != max - 3 { return false; }
    true
}

}

fn main() {}
