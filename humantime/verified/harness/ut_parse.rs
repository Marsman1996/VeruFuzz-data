//! humantime **harness zone** -- parsing-side UT exemplars / G obligation
//! anchors (mirrors the parse face of the upstream date.rs:405-742 mod test
//! and the error-example face of duration.rs:537-854).
//!
//! Reference-style structure: `#[path = "../src/date.rs"] mod date;` and
//! `#[path = "../src/duration.rs"] mod duration;` -- they reference the
//! src-side verified spec/exec directly (the date-side full-sem family:
//! parse_rfc3339_sem / rfc3339_weak_value_sem / rfc3339_date_sem /
//! frac_scan_sem / two_digits_sem; the duration base sems:
//! parse_first_char_sem / frac_part_sem), duplicating no fact source.
//!
//! Exemplar surface:
//!   - date: value exemplars of the upstream smoke_tests_parse /
//!     smoke_tests_format; upper_bound / leap_second / milliseconds /
//!     weak_smoke_tests / parse_offset_00 / the per-position break_data and
//!     the seven should_panic domain checks (recast as Err-semantics
//!     exemplars);
//!   - **G3 obligation anchor** (upstream parse_rfc3339 doc :77-83 "Any
//!     precision of fractional digits"): `w_frac_trunc_10_digits` (the 10th
//!     fractional digit is silently truncated) and `w_frac_empty_dotz` (the
//!     empty fraction ".Z" is accepted) -- two pieces of directional
//!     evidence that the doc text disagrees with the implementation (runtime
//!     re-confirmation: out/poc/f3-frac-precision);
//!   - duration: the sem-level anchors of the upstream test_error_cases /
//!     test_fractional_bad_input / allow_0_with_no_unit + the **G2
//!     obligation anchor** (upstream duration.rs:23 doc "byte offset of the
//!     erroneous character"): w_first_char_g2_offset asserts that
//!     NumberExpected reports position = the scan start 8 (whitespace),
//!     while the erroneous character 'm' really sits at 9.
//!
//! Verdict: expects 0 errors.

use vstd::prelude::*;

#[path = "../src/date.rs"]
mod date;

#[path = "../src/duration.rs"]
mod duration;

verus! {
// ===========================================================================
// Proof lemmas (parsing-side UT exemplars and doc-obligation anchors, placed
// at the end of the file so the exec implementation reads directly)
// ===========================================================================
/// UT exemplar: "1970-01-01T00:00:00Z" (smoke/offset/bound family).
pub proof fn w_parse_smoke_epoch() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((0u64, 0u32)));
}
/// UT exemplar: "2018-02-13T23:08:32Z" (smoke/offset/bound family).
pub proof fn w_parse_smoke_2018() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x31, 0x38, 0x2d, 0x30, 0x32, 0x2d, 0x31, 0x33, 0x54, 0x32, 0x33, 0x3a, 0x30, 0x38, 0x3a, 0x33, 0x32, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((1_518_563_312u64, 0u32)));
}
/// UT exemplar: "2012-01-01T00:00:00Z" (smoke/offset/bound family).
pub proof fn w_parse_smoke_2012() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x31, 0x32, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((1_325_376_000u64, 0u32)));
}
/// UT exemplar: "2018-02-13T23:08:32+00:00" (smoke/offset/bound family).
pub proof fn w_parse_offset_00() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x31, 0x38, 0x2d, 0x30, 0x32, 0x2d, 0x31, 0x33, 0x54, 0x32, 0x33, 0x3a, 0x30, 0x38, 0x3a, 0x33, 0x32, 0x2b, 0x30, 0x30, 0x3a, 0x30, 0x30];
    assert(date::parse_rfc3339_sem(b) === Ok((1_518_563_312u64, 0u32)));
}
/// UT exemplar: "2016-12-31T23:59:60Z" (smoke/offset/bound family).
pub proof fn w_parse_leap_second() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x31, 0x36, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x31, 0x54, 0x32, 0x33, 0x3a, 0x35, 0x39, 0x3a, 0x36, 0x30, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((1_483_228_799u64, 0u32)));
}
/// UT exemplar: "2038-01-19T03:14:07Z" (smoke/offset/bound family).
pub proof fn w_parse_2038_max32() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x33, 0x38, 0x2d, 0x30, 0x31, 0x2d, 0x31, 0x39, 0x54, 0x30, 0x33, 0x3a, 0x31, 0x34, 0x3a, 0x30, 0x37, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((2_147_483_647u64, 0u32)));
}
/// UT exemplar: "9999-12-31T23:59:59Z" (smoke/offset/bound family).
pub proof fn w_parse_upper_bound() {
    let b: Seq<u8> = seq![0x39, 0x39, 0x39, 0x39, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x31, 0x54, 0x32, 0x33, 0x3a, 0x35, 0x39, 0x3a, 0x35, 0x39, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((253_402_300_799u64, 0u32)));
}
/// UT exemplar: "1970-01-01T00:00:00.123Z" (smoke/offset/bound family).
pub proof fn w_parse_millis_frac() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x31, 0x32, 0x33, 0x5a];
    assert(b.len() == 24);
    assert(date::frac_scan_sem(b, 20, 0, 100000000) === date::frac_scan_sem(b, 21, 100000000, 10000000));
    assert(date::frac_scan_sem(b, 21, 100000000, 10000000) === date::frac_scan_sem(b, 22, 120000000, 1000000));
    assert(date::frac_scan_sem(b, 22, 120000000, 1000000) === date::frac_scan_sem(b, 23, 123000000, 100000));
    assert(date::frac_scan_sem(b, 23, 123000000, 100000) === Ok(123000000u32));
    assert(date::parse_rfc3339_sem(b) === Ok((0u64, 123_000_000u32)));
}
pub proof fn w_parse_nanos_frac() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x5a];
    assert(b.len() == 30);
    assert(date::frac_scan_sem(b, 20, 0, 100000000) === date::frac_scan_sem(b, 21, 100000000, 10000000));
    assert(date::frac_scan_sem(b, 21, 100000000, 10000000) === date::frac_scan_sem(b, 22, 120000000, 1000000));
    assert(date::frac_scan_sem(b, 22, 120000000, 1000000) === date::frac_scan_sem(b, 23, 123000000, 100000));
    assert(date::frac_scan_sem(b, 23, 123000000, 100000) === date::frac_scan_sem(b, 24, 123400000, 10000));
    assert(date::frac_scan_sem(b, 24, 123400000, 10000) === date::frac_scan_sem(b, 25, 123450000, 1000));
    assert(date::frac_scan_sem(b, 25, 123450000, 1000) === date::frac_scan_sem(b, 26, 123456000, 100));
    assert(date::frac_scan_sem(b, 26, 123456000, 100) === date::frac_scan_sem(b, 27, 123456700, 10));
    assert(date::frac_scan_sem(b, 27, 123456700, 10) === date::frac_scan_sem(b, 28, 123456780, 1));
    assert(date::frac_scan_sem(b, 28, 123456780, 1) === date::frac_scan_sem(b, 29, 123456789, 0));
    assert(date::frac_scan_sem(b, 29, 123456789, 0) === Ok(123456789u32));
    assert(date::parse_rfc3339_sem(b) === Ok((0u64, 123_456_789u32)));
}
/// **G3 obligation anchor, part 1** (upstream parse_rfc3339 doc :77-83 "Any
/// precision of fractional digits"): the 10th fractional digit (the '1' at
/// idx 29) is **silently dropped** once mult has dropped to 0 -- the return
/// value stays .123456789 (no error, no rounding). Runtime re-confirmation:
/// out/poc/f3-frac-precision.
pub proof fn w_frac_trunc_10_digits() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x31, 0x5a];
    assert(b.len() == 31);
    assert(date::frac_scan_sem(b, 20, 0, 100000000) === date::frac_scan_sem(b, 21, 100000000, 10000000));
    assert(date::frac_scan_sem(b, 21, 100000000, 10000000) === date::frac_scan_sem(b, 22, 120000000, 1000000));
    assert(date::frac_scan_sem(b, 22, 120000000, 1000000) === date::frac_scan_sem(b, 23, 123000000, 100000));
    assert(date::frac_scan_sem(b, 23, 123000000, 100000) === date::frac_scan_sem(b, 24, 123400000, 10000));
    assert(date::frac_scan_sem(b, 24, 123400000, 10000) === date::frac_scan_sem(b, 25, 123450000, 1000));
    assert(date::frac_scan_sem(b, 25, 123450000, 1000) === date::frac_scan_sem(b, 26, 123456000, 100));
    assert(date::frac_scan_sem(b, 26, 123456000, 100) === date::frac_scan_sem(b, 27, 123456700, 10));
    assert(date::frac_scan_sem(b, 27, 123456700, 10) === date::frac_scan_sem(b, 28, 123456780, 1));
    assert(date::frac_scan_sem(b, 28, 123456780, 1) === date::frac_scan_sem(b, 29, 123456789, 0));
    // the 10th digit '1' (idx 29): mult == 0 => nanos unchanged (silent truncation)
    assert(date::frac_scan_sem(b, 29, 123456789, 0) === date::frac_scan_sem(b, 30, 123456789, 0));
    assert(date::frac_scan_sem(b, 30, 123456789, 0) === Ok(123456789u32));
    assert(date::parse_rfc3339_sem(b) === Ok((0u64, 123_456_789u32)));
}
/// UT exemplar: "1970-01-01T00:00:00.Z" (smoke/offset/bound family).
pub proof fn w_frac_empty_dotz() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x5a];
    assert(date::parse_rfc3339_sem(b) === Ok((0u64, 0u32)));
}
pub proof fn w_frac_nines() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x39, 0x5a];
    assert(b.len() == 30);
    assert(date::frac_scan_sem(b, 20, 0, 100000000) === date::frac_scan_sem(b, 21, 900000000, 10000000));
    assert(date::frac_scan_sem(b, 21, 900000000, 10000000) === date::frac_scan_sem(b, 22, 990000000, 1000000));
    assert(date::frac_scan_sem(b, 22, 990000000, 1000000) === date::frac_scan_sem(b, 23, 999000000, 100000));
    assert(date::frac_scan_sem(b, 23, 999000000, 100000) === date::frac_scan_sem(b, 24, 999900000, 10000));
    assert(date::frac_scan_sem(b, 24, 999900000, 10000) === date::frac_scan_sem(b, 25, 999990000, 1000));
    assert(date::frac_scan_sem(b, 25, 999990000, 1000) === date::frac_scan_sem(b, 26, 999999000, 100));
    assert(date::frac_scan_sem(b, 26, 999999000, 100) === date::frac_scan_sem(b, 27, 999999900, 10));
    assert(date::frac_scan_sem(b, 27, 999999900, 10) === date::frac_scan_sem(b, 28, 999999990, 1));
    assert(date::frac_scan_sem(b, 28, 999999990, 1) === date::frac_scan_sem(b, 29, 999999999, 0));
    assert(date::frac_scan_sem(b, 29, 999999999, 0) === Ok(999999999u32));
    assert(date::parse_rfc3339_sem(b) === Ok((0u64, 999_999_999u32)));
}
/// UT exemplar: "1970-01-01 00:00:00" (weak_smoke_tests).
pub proof fn w_weak_space_only() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x20, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30];
    assert(date::rfc3339_weak_value_sem(b) === Ok((0u64, 0u32)));
}
pub proof fn w_weak_space_frac() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x20, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x2e, 0x30, 0x30, 0x30, 0x31, 0x32, 0x33];
    assert(b.len() == 26);
    assert(date::frac_scan_sem(b, 20, 0, 100000000) === date::frac_scan_sem(b, 21, 0, 10000000));
    assert(date::frac_scan_sem(b, 21, 0, 10000000) === date::frac_scan_sem(b, 22, 0, 1000000));
    assert(date::frac_scan_sem(b, 22, 0, 1000000) === date::frac_scan_sem(b, 23, 0, 100000));
    assert(date::frac_scan_sem(b, 23, 0, 100000) === date::frac_scan_sem(b, 24, 100000, 10000));
    assert(date::frac_scan_sem(b, 24, 100000, 10000) === date::frac_scan_sem(b, 25, 120000, 1000));
    assert(date::frac_scan_sem(b, 25, 120000, 1000) === date::frac_scan_sem(b, 26, 123000, 100));
    assert(date::frac_scan_sem(b, 26, 123000, 100) === Ok(123000u32));
    assert(date::rfc3339_weak_value_sem(b) === Ok((0u64, 123_000u32)));
}
/// UT exemplar: the space-separated serial form of the weak format
/// (the reverse companion of weak_smoke_tests): strict parse_rfc3339 rejects it
/// (upstream :89 b[10] != 'T').
pub proof fn w_weak_strict_rejects() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x31, 0x20, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30];
    assert(date::parse_rfc3339_sem(b) === Err(date::DERR_INVALID_FORMAT));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-00-01T00:00:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_zero_month() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x30, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-32-01T00:00:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_big_month() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x33, 0x32, 0x2d, 0x30, 0x31, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-01-00T00:00:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_zero_day() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x31, 0x2d, 0x30, 0x30, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-12-35T00:00:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_big_day() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x35, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-02-30T00:00:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_big_day2_feb() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x30, 0x32, 0x2d, 0x33, 0x30, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-12-30T00:00:78Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_big_second() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x30, 0x54, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x3a, 0x37, 0x38, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-12-30T00:78:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_big_minute() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x30, 0x54, 0x30, 0x30, 0x3a, 0x37, 0x38, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1970-12-30T24:00:00Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_big_hour() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x37, 0x30, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x30, 0x54, 0x32, 0x34, 0x3a, 0x30, 0x30, 0x3a, 0x30, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "1969-12-31T23:59:59Z" -> date::DERR_OUT_OF_RANGE.
pub proof fn w_year_pre_epoch() {
    let b: Seq<u8> = seq![0x31, 0x39, 0x36, 0x39, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x31, 0x54, 0x32, 0x33, 0x3a, 0x35, 0x39, 0x3a, 0x35, 0x39, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_OUT_OF_RANGE));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "x016-12-31T23:59:60Z" -> date::DERR_INVALID_DIGIT.
pub proof fn w_break_data_d0() {
    let b: Seq<u8> = seq![0x78, 0x30, 0x31, 0x36, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x31, 0x54, 0x32, 0x33, 0x3a, 0x35, 0x39, 0x3a, 0x36, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_INVALID_DIGIT));
}
/// UT exemplar (the upstream should_panic family, recast as Err
/// semantics): "2016-12-31x23:59:60Z" -> date::DERR_INVALID_FORMAT.
pub proof fn w_break_data_t() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x31, 0x36, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x31, 0x78, 0x32, 0x33, 0x3a, 0x35, 0x39, 0x3a, 0x36, 0x30, 0x5a];
    assert(date::rfc3339_weak_value_sem(b) === Err(date::DERR_INVALID_FORMAT));
}
/// UT exemplar (the fractional-domain variant of break_data):
/// "2016-12-31T23:59:60.12x4Z": the fractional scanner hits the non-digit
/// 'x' at scan position 22 -> InvalidDigit (upstream :184).
pub proof fn w_bad_frac_dig() {
    let b: Seq<u8> = seq![0x32, 0x30, 0x31, 0x36, 0x2d, 0x31, 0x32, 0x2d, 0x33, 0x31, 0x54, 0x32, 0x33, 0x3a, 0x35, 0x39, 0x3a, 0x36, 0x30, 0x2e, 0x31, 0x32, 0x78, 0x34, 0x5a];
    assert(b.len() == 25);
    assert(date::frac_scan_sem(b, 20, 0, 100000000) === date::frac_scan_sem(b, 21, 100000000, 10000000));
    assert(date::frac_scan_sem(b, 21, 100000000, 10000000) === date::frac_scan_sem(b, 22, 120000000, 1000000));
    assert(date::frac_scan_sem(b, 22, 120000000, 1000000) === Err(date::DERR_INVALID_DIGIT));
}
// ---------- duration base-sem anchors (the G2 obligation + the test_error_cases face) ----------

/// Upstream test_units first-digit exemplar: "2" -> (Some(2), 1).
pub proof fn w_first_char_digit2() {
    let b: Seq<u8> = seq![0x32];
    assert(duration::parse_first_char_sem(b, 0) === Ok((Some(2u64), 1usize)));
}

pub proof fn w_first_char_ws_only() {
    let b: Seq<u8> = seq![0x0d];
    assert(duration::parse_first_char_go(b, 0, 0) === duration::parse_first_char_go(b, 1, 0));
    assert(duration::parse_first_char_go(b, 1, 0) === Ok((None, 1usize)));
    assert(duration::parse_first_char_sem(b, 0) === Ok((None, 1usize)));
}

/// Upstream test_error_cases "\0": NumberExpected(0).
pub proof fn w_first_char_nul() {
    let b: Seq<u8> = seq![0x00];
    assert(duration::parse_first_char_sem(b, 0) === Err((duration::P2_ERR_NUMBER_EXPECTED, 0usize)));
}

/// **G2 obligation anchor** (upstream duration.rs:21-23): input
/// "2 hours  min" -- after the "2 hours" span, the scan for the next number
/// starts at position 8 (the second whitespace); upstream :174's `let off =
/// self.off()` **freezes the off at the scan start**, so the error exit
/// reports NumberExpected(**8**) even though the real erroneous character
/// 'm' sits at position 9 (position 8 is the whitespace itself). The
/// upstream :23 doc nevertheless claims the field is the offset of the
/// "erroneous character". Runtime re-confirmation:
/// out/poc/f5-number-expected-offset.
pub proof fn w_first_char_g2_offset() {
    let b: Seq<u8> = seq![0x32, 0x20, 0x68, 0x6f, 0x75, 0x72, 0x73, 0x20, 0x20, 0x6d, 0x69, 0x6e];
    assert(b.len() == 12);
    assert(b[8] == 0x20);   // reported offset 8 is whitespace (the erroneous character is not here)
    assert(b[9] == 0x6d);   // 'm': the real erroneous character at position 9
    assert(duration::parse_first_char_go(b, 8, 8) === duration::parse_first_char_go(b, 9, 8));
    assert(duration::parse_first_char_go(b, 9, 8) === Err((duration::P2_ERR_NUMBER_EXPECTED, 8usize)));
    assert(duration::parse_first_char_sem(b, 8) === Err((duration::P2_ERR_NUMBER_EXPECTED, 8usize)));
}

/// Upstream test_fractional_bad_input "1.s": the den==1 empty fraction => InvalidCharacter(dot=1).
pub proof fn w_frac_empty_err() {
    let b: Seq<u8> = seq![0x31, 0x2e, 0x73];
    assert(duration::frac_part_sem(b, 1, 2, 0, 1, true)
        === Err((duration::P2_ERR_INVALID_CHARACTER, 1usize)));
}

pub proof fn w_frac_23() {
    let b: Seq<u8> = seq![0x31, 0x2e, 0x32, 0x33];
    assert(duration::frac_part_sem(b, 1, 2, 0, 1, true) === duration::frac_part_sem(b, 1, 3, 2, 10, false));
    assert(duration::frac_part_sem(b, 1, 3, 2, 10, false) === duration::frac_part_sem(b, 1, 4, 23, 100, false));
    assert(duration::frac_part_sem(b, 1, 4, 23, 100, false) === Ok((23u64, 100u64, 4usize, 4usize)));
}
}
fn main() {}

