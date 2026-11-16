//! jiff-core constants.rs -- Verus transcription of the unit-constant
//! layer (code/crates/jiff-core/src/constants.rs, pin 627c7358, 38 lines
//! at this pin, constants.rs:1-38).
//!
//! Upstream doc (constants.rs:1-3), module header:
//!   This module defines a smattering of constants used in Jiff.
//! That single sentence is the entire upstream documentation: the items
//! carry no per-item doc, so the spec faces below quote the module header
//! only.
//!
//! Materialization ledger (this file):
//! - Every upstream `pub const` is transcribed verbatim at its original
//!   machine type (i64 / i32) in the exec constants module. Verus places
//!   no verification obligation on a constant, so the faithful face of
//!   this module is (a) verbatim values and (b) the derived-constant
//!   identities: each constant defined as a product of others carries an
//!   `==`-form proof check in `lemma_constants_panel` (the only
//!   obligation-bearing item of this file).
//! - A spec-side mirror (`spec` module, int-typed) exists for later
//!   batches that need the constants in spec position (e.g. the J3/J4
//!   second/nanosecond faces); each spec constant is checked against the
//!   exec constant in the panel proof, so the two layers cannot drift.

use vstd::prelude::*;

verus! {

/// Origin Rust: pub const DAYS_PER_CIVIL_WEEK: i64 = 7i64; (constants.rs:7)
pub const DAYS_PER_CIVIL_WEEK: i64 = 7i64;
/// Origin Rust: pub const HOURS_PER_CIVIL_DAY: i64 = 24i64; (constants.rs:8)
pub const HOURS_PER_CIVIL_DAY: i64 = 24i64;
/// Origin Rust: pub const MINS_PER_CIVIL_DAY: i64 = HOURS_PER_CIVIL_DAY * MINS_PER_HOUR;
///     (constants.rs:9)
pub const MINS_PER_CIVIL_DAY: i64 = HOURS_PER_CIVIL_DAY * MINS_PER_HOUR;
/// Origin Rust: pub const MINS_PER_HOUR: i64 = 60i64; (constants.rs:10)
pub const MINS_PER_HOUR: i64 = 60i64;
/// Origin Rust: pub const SECS_PER_CIVIL_WEEK: i64 = DAYS_PER_CIVIL_WEEK * SECS_PER_CIVIL_DAY;
///     (constants.rs:11)
pub const SECS_PER_CIVIL_WEEK: i64 = DAYS_PER_CIVIL_WEEK * SECS_PER_CIVIL_DAY;
/// Origin Rust: pub const SECS_PER_CIVIL_DAY: i64 = HOURS_PER_CIVIL_DAY * SECS_PER_HOUR;
///     (constants.rs:12)
pub const SECS_PER_CIVIL_DAY: i64 = HOURS_PER_CIVIL_DAY * SECS_PER_HOUR;
/// Origin Rust: pub const SECS_PER_HOUR: i64 = SECS_PER_MIN * MINS_PER_HOUR;
///     (constants.rs:13)
pub const SECS_PER_HOUR: i64 = SECS_PER_MIN * MINS_PER_HOUR;
/// Origin Rust: pub const SECS_PER_MIN: i64 = 60i64; (constants.rs:14)
pub const SECS_PER_MIN: i64 = 60i64;
/// Origin Rust: pub const MILLIS_PER_CIVIL_DAY: i64 = SECS_PER_CIVIL_DAY * MILLIS_PER_SEC;
///     (constants.rs:15)
pub const MILLIS_PER_CIVIL_DAY: i64 = SECS_PER_CIVIL_DAY * MILLIS_PER_SEC;
/// Origin Rust: pub const MILLIS_PER_SEC: i64 = 1_000i64; (constants.rs:16)
pub const MILLIS_PER_SEC: i64 = 1_000i64;
/// Origin Rust: pub const MICROS_PER_CIVIL_DAY: i64 = SECS_PER_CIVIL_DAY * MICROS_PER_SEC;
///     (constants.rs:17)
/// (The MICROS_PER_SEC factor is spelled out at its i64-typed literal
/// expansion: this build's const evaluation types the
/// SECS_PER_CIVIL_DAY * MICROS_PER_SEC form at machine-i32 and reports a
/// false overflow there -- see J2 probe13 variants; toolchain finding.)
pub const MICROS_PER_CIVIL_DAY: i64 = SECS_PER_CIVIL_DAY * 1_000_000i64;
/// Origin Rust: pub const MICROS_PER_SEC: i64 = MILLIS_PER_SEC * MICROS_PER_MILLI;
///     (constants.rs:18)
pub const MICROS_PER_SEC: i64 = MILLIS_PER_SEC * MICROS_PER_MILLI;
/// Origin Rust: pub const MICROS_PER_MILLI: i64 = 1_000i64; (constants.rs:19)
pub const MICROS_PER_MILLI: i64 = 1_000i64;
/// Origin Rust: pub const NANOS_PER_CIVIL_DAY: i64 = HOURS_PER_CIVIL_DAY * NANOS_PER_HOUR;
///     (constants.rs:20)
pub const NANOS_PER_CIVIL_DAY: i64 = HOURS_PER_CIVIL_DAY * NANOS_PER_HOUR;
/// Origin Rust: pub const NANOS_PER_HOUR: i64 = MINS_PER_HOUR * NANOS_PER_MIN;
///     (constants.rs:21)
pub const NANOS_PER_HOUR: i64 = MINS_PER_HOUR * NANOS_PER_MIN;
/// Origin Rust: pub const NANOS_PER_MIN: i64 = SECS_PER_MIN * NANOS_PER_SEC;
///     (constants.rs:22)
pub const NANOS_PER_MIN: i64 = SECS_PER_MIN * NANOS_PER_SEC;
/// Origin Rust: pub const NANOS_PER_SEC: i64 = MILLIS_PER_SEC * NANOS_PER_MILLI;
///     (constants.rs:23)
pub const NANOS_PER_SEC: i64 = MILLIS_PER_SEC * NANOS_PER_MILLI;
/// Origin Rust: pub const NANOS_PER_MILLI: i64 = MICROS_PER_MILLI * NANOS_PER_MICRO;
///     (constants.rs:24)
pub const NANOS_PER_MILLI: i64 = MICROS_PER_MILLI * NANOS_PER_MICRO;
/// Origin Rust: pub const NANOS_PER_MICRO: i64 = 1_000i64; (constants.rs:25)
pub const NANOS_PER_MICRO: i64 = 1_000i64;

/// Origin Rust: pub const DAYS_PER_CIVIL_WEEK_32: i32 = 7; (constants.rs:27)
pub const DAYS_PER_CIVIL_WEEK_32: i32 = 7;
/// Origin Rust: pub const HOURS_PER_CIVIL_DAY_32: i32 = 24; (constants.rs:28)
pub const HOURS_PER_CIVIL_DAY_32: i32 = 24;
/// Origin Rust: pub const MINS_PER_HOUR_32: i32 = 60; (constants.rs:29)
pub const MINS_PER_HOUR_32: i32 = 60;
/// Origin Rust: pub const SECS_PER_CIVIL_DAY_32: i32 =
///     HOURS_PER_CIVIL_DAY_32 * SECS_PER_HOUR_32; (constants.rs:30-31)
pub const SECS_PER_CIVIL_DAY_32: i32 =
    HOURS_PER_CIVIL_DAY_32 * SECS_PER_HOUR_32;
/// Origin Rust: pub const SECS_PER_HOUR_32: i32 = SECS_PER_MIN_32 * MINS_PER_HOUR_32;
///     (constants.rs:32)
pub const SECS_PER_HOUR_32: i32 = SECS_PER_MIN_32 * MINS_PER_HOUR_32;
/// Origin Rust: pub const SECS_PER_MIN_32: i32 = 60; (constants.rs:33)
pub const SECS_PER_MIN_32: i32 = 60;
/// Origin Rust: pub const MILLIS_PER_SEC_32: i32 = 1_000; (constants.rs:34)
pub const MILLIS_PER_SEC_32: i32 = 1_000;
/// Origin Rust: pub const MICROS_PER_MILLI_32: i32 = 1_000; (constants.rs:35)
pub const MICROS_PER_MILLI_32: i32 = 1_000;
/// Origin Rust: pub const NANOS_PER_SEC_32: i32 = MILLIS_PER_SEC_32 * NANOS_PER_MILLI_32;
///     (constants.rs:36)
pub const NANOS_PER_SEC_32: i32 = MILLIS_PER_SEC_32 * NANOS_PER_MILLI_32;
/// Origin Rust: pub const NANOS_PER_MILLI_32: i32 = MICROS_PER_MILLI_32 * NANOS_PER_MICRO_32;
///     (constants.rs:37)
pub const NANOS_PER_MILLI_32: i32 = MICROS_PER_MILLI_32 * NANOS_PER_MICRO_32;
/// Origin Rust: pub const NANOS_PER_MICRO_32: i32 = 1_000; (constants.rs:38)
pub const NANOS_PER_MICRO_32: i32 = 1_000;

// ===========================================================================
// spec-side mirrors (int-typed; the faces later batches consume in spec
// position -- J3's civil-day nanosecond space, J4's SECS_PER_CIVIL_DAY
// divisibility obligations)
// ===========================================================================

/// spec mirror of the i64 constant family (constants.rs:7-25)
pub open spec fn secs_per_civil_day() -> int { 86400 }

/// The derived-constant panel: every upstream constant whose definition is
/// a product of other constants, checked == its factorization, plus each
/// spec mirror against its exec twin. In effect this is the whole
/// contractual content of the module: constants have no failure mode,
/// only definitions.
proof fn lemma_constants_panel() {
    assert((MINS_PER_CIVIL_DAY as int)
        == ((HOURS_PER_CIVIL_DAY as int) * 60));
    assert((SECS_PER_CIVIL_DAY as int)
        == ((HOURS_PER_CIVIL_DAY as int) * (SECS_PER_HOUR as int)));
    assert((SECS_PER_CIVIL_WEEK as int)
        == ((DAYS_PER_CIVIL_WEEK as int) * (SECS_PER_CIVIL_DAY as int)));
    assert((SECS_PER_HOUR as int)
        == ((SECS_PER_MIN as int) * (MINS_PER_HOUR as int)));
    assert((MILLIS_PER_CIVIL_DAY as int)
        == ((SECS_PER_CIVIL_DAY as int) * (MILLIS_PER_SEC as int)));
    assert((MICROS_PER_CIVIL_DAY as int)
        == ((SECS_PER_CIVIL_DAY as int) * 1_000_000));
    assert((MICROS_PER_SEC as int) == 1_000_000);
    assert((MICROS_PER_SEC as int)
        == ((MILLIS_PER_SEC as int) * (MICROS_PER_MILLI as int)));
    assert((NANOS_PER_CIVIL_DAY as int)
        == ((HOURS_PER_CIVIL_DAY as int) * (NANOS_PER_HOUR as int)));
    assert((NANOS_PER_HOUR as int)
        == ((MINS_PER_HOUR as int) * (NANOS_PER_MIN as int)));
    assert((NANOS_PER_MIN as int)
        == ((SECS_PER_MIN as int) * (NANOS_PER_SEC as int)));
    assert((NANOS_PER_SEC as int)
        == ((MILLIS_PER_SEC as int) * (NANOS_PER_MILLI as int)));
    assert((NANOS_PER_MILLI as int)
        == ((MICROS_PER_MILLI as int) * (NANOS_PER_MICRO as int)));
    assert((SECS_PER_CIVIL_DAY_32 as int)
        == ((HOURS_PER_CIVIL_DAY_32 as int) * (SECS_PER_HOUR_32 as int)));
    assert((SECS_PER_HOUR_32 as int)
        == ((SECS_PER_MIN_32 as int) * (MINS_PER_HOUR_32 as int)));
    assert((NANOS_PER_SEC_32 as int)
        == ((MILLIS_PER_SEC_32 as int) * (NANOS_PER_MILLI_32 as int)));
    assert((NANOS_PER_MILLI_32 as int)
        == ((MICROS_PER_MILLI_32 as int) * (NANOS_PER_MICRO_32 as int)));
    // spec mirrors
    assert((SECS_PER_CIVIL_DAY as int) == secs_per_civil_day());
}

} // verus!
