//! jiff 0.2.43 Span core arithmetic (crates/jiff/src/span.rs, 7587
//! lines, pin tree read-only) -- Verus translation, batch J5.
//!
//! Scope (the span core arithmetic family, per out/harness-inventory.md
//! "Batch J5"): `Span` construction and lifecycle (`Span::new`, the
//! unit-aware `years()/months()/.../nanoseconds()` setter family with
//! its `try_*` fallible twins and the `_unchecked` internal setters),
//! the `resign` sign bookkeeping helper, the getter family
//! (`get_years()/.../get_nanoseconds()`, `get_*_unsigned`, `get_unit`,
//! `get_sign`), the sign predicates (`signum/is_zero/is_positive/
//! is_negative`) plus `abs`/`negate` and the `Neg` operator face, and
//! `checked_mul` with its `Mul<i64>` / `Mul<Span> for i64` operators.
//! The `SignedDuration::as_nanos64` meeting point (upstream
//! signed_duration.rs:997-1009, NOT in span.rs -- see the notes)
//! is transcribed at the bottom of this file.
//!
//! Driver mount: `verified/j5-driver.rs` mounts this file plus, via
//! `#[path]`, the closed J1 panel `src/bounds.rs` (this file needs the
//! `Sign` enum and the `const_check`/`checked_mul` width-indexed range
//! helpers; the J1 ledger's "Sign Mul/From cut" faces are re-cut inside
//! this file as free helpers, citing the upstream jcore lines).
//! `src/jcore_signed_duration.rs` is NOT mounted: this batch's span
//! surface interacts with SignedDuration only through the deferred
//! checked_add/relative-date path (see notes).
//!
//! List of modeling losses (upstream shape -> this translation), each
//! also annotated at its site:
//! 1. `Result<Span, Error>` surfaces materialize as `Option<Span>`
//!    (the J1 bounds-error precedent: the error value is a zero-sized
//!    kind witness; message text is not verified).
//! 2. `UnitSet` (span.rs:5747, `UnitSet(u16)` bitmap with
//!    `1 << unit as usize` bits) materializes as ten structural bool
//!    flags: the bitmap is a memory-shape detail behind
//!    set/contains/largest_unit contracts; every bit_vector obligation
//!    dissolves. `Unit`'s upstream discriminants (`Year = 9` ...
//!    `Nanosecond = 0`, span.rs:3876-3916 only back the bitmap; they
//!    do not survive into the verus enum, whose value embodiment is
//!    the variant identity).
//! 3. `impl Into<i64>` parameters materialize as `i64` (the J1
//!    const-cut precedent; every in-tree call site passes an i64).
//! 4. `Multiplication-by-value` receiver chains (`self.years(v)`)
//!    materialize as `&self` -> `Span` functions with the same
//!    field-preservation contracts.
//! 5. Panicking faces (the `.expect` setters and the Mul operators)
//!    carry an in-range `requires` plus a dead arm routed through
//!    `assert(false)` (the J2 `Date::constant` precedent). The arm
//!    sites carry the upstream panic line numbers; this batch wraps
//!    no panic sites in opaque body attributes.
//!
//! File-wide contract shape: the field-domain invariant
//! `sp_field_inv` is the primary requires tier (the J4 recommendation:
//! start at the field-domain tier, not at any canonical tier), with
//! the zero-sign consistency tier `sp_zero_sign_ok` added where the
//! `resign` bookkeeping needs it.

use vstd::prelude::*;
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_commutative, lemma_mul_strictly_positive,
    lemma_mul_unary_negation, lemma_mul_cancels_negatives,
    lemma_mul_by_zero_is_zero, lemma_mul_nonzero,
};

use crate::bounds::Sign;
use crate::jcore_signed_duration::{SignedDuration, sd_inv, sd_total_nanos};

verus! {

// ===========================================================================
// Span unit bounds (jiff src/util/b.rs:192-231, the b::Span* boundary
// types; the factorizations are jcore-derived: SpanYears::MAX =
// (Year::LEN - 1) as i16 with Year::LEN = 19999 (jcore bounds.rs:71,
// :399), SpanMonths::MAX = SpanYears::MAX * 12, SpanWeeks::MAX =
// SpanDays::MAX / 7, ..., SpanSeconds::MAX = DeltaSeconds::MAX =
// next_multiple_of(UnixEpochSeconds::LEN + OffsetTotalSeconds::MAX +
// SECS_PER_CIVIL_DAY, SECS_PER_CIVIL_DAY) (jcore bounds.rs:200-210)).
// The setter docs on span.rs quote these values back verbatim.
// ===========================================================================

pub const SPAN_YEARS_MAX: i16 = 19_998;
pub const SPAN_MONTHS_MAX: i32 = 239_976;
pub const SPAN_WEEKS_MAX: i32 = 1_043_497;
pub const SPAN_DAYS_MAX: i32 = 7_304_484;
pub const SPAN_HOURS_MAX: i32 = 175_307_616;
pub const SPAN_MINUTES_MAX: i64 = 10_518_456_960;
pub const SPAN_SECONDS_MAX: i64 = 631_107_417_600;
pub const SPAN_MILLIS_MAX: i64 = 631_107_417_600_000;
pub const SPAN_MICROS_MAX: i64 = 631_107_417_600_000_000;
// SpanNanoseconds (util/b.rs:230): MIN = i64::MIN + 1, MAX = i64::MAX
// ("our min is equal to -max, so that the total number of values ... is
// one less than i64, ... so that the absolute value is always defined").
// SpanMultiple (util/b.rs:220): the same range; it is only inhabited by
// the magnitudes of checked_mul's checked_abs, so it materializes as
// the plain signed-magnitude reasoning in sp_mul_err_cond.

/// Constants ledger: each derived bound equals its upstream
/// factorization (compute-tier parity panel; the upstream values are
/// const-context where this build has no const-verification, so the
/// parity obligations live in this proof fn -- the J2 constants face).
proof fn sp_bounds_panel() {
    // SpanMonths::MAX == SpanYears::MAX * 12 (util/b.rs:194)
    assert((SPAN_MONTHS_MAX as int) == (SPAN_YEARS_MAX as int) * 12);
    // SpanWeeks::MAX == SpanDays::MAX / 7 (util/b.rs:195; 7_304_484 / 7
    // truncates down to 1_043_497)
    assert((SPAN_WEEKS_MAX as int) == (SPAN_DAYS_MAX as int) / 7);
    // SpanDays::MAX == SpanHours::MAX / 24 (util/b.rs:196)
    assert((SPAN_DAYS_MAX as int) == (SPAN_HOURS_MAX as int) / 24);
    // SpanHours::MAX == (SpanMinutes::MAX / 60) truncated to i32
    // (util/b.rs:197)
    assert((SPAN_HOURS_MAX as int) == (SPAN_MINUTES_MAX as int) / 60);
    // SpanMinutes::MAX == SpanSeconds::MAX / 60 (util/b.rs:198)
    assert((SPAN_MINUTES_MAX as int) == (SPAN_SECONDS_MAX as int) / 60);
    // SpanSeconds::MAX == DeltaSeconds::MAX (util/b.rs:200-204), whose
    // jcore factorization (bounds.rs:201-209) is
    // next_multiple_of(UnixEpochSeconds::LEN + OffsetTotalSeconds::MAX
    // + 86400, 86400) = 7_304_484 * 86_400 exactly (the +SECS_PER_CIVIL_
    // DAY tail of the jcore sum pushes the multiple up to the day grid).
    assert((SPAN_SECONDS_MAX as int) == 7_304_484 * 86_400);
    assert((SPAN_SECONDS_MAX as int) % 86_400 == 0);
    // SpanMilliseconds::MAX == SpanSeconds::MAX * 1_000
    // (util/b.rs:211)
    assert((SPAN_MILLIS_MAX as int) == (SPAN_SECONDS_MAX as int) * 1_000);
    // SpanMicroseconds::MAX == SpanMilliseconds::MAX * 1_000
    // (util/b.rs:218)
    assert((SPAN_MICROS_MAX as int) == (SPAN_MILLIS_MAX as int) * 1_000);
    // Day-grid chain parity (the clock arithmetic the invariant path
    // of checked_add will lean on; recorded here as ground facts):
    assert((SPAN_DAYS_MAX as int) == 7_304_484);
    assert((SPAN_YEARS_MAX as int) == 19_998);
}

// ===========================================================================
// Sign auxiliary faces (jcore bounds.rs:1155-1320 family).
// These were explicitly cut from the J1 panel ("Sign Neg / core::ops::
// Mul family / From<i8..i128/f64>: outside the J1 listed surface",
// J1 notes "Cut surface"), and the J1 ledger already flagged the
// overflow hazard: "Sign's Mul impls upstream multiply as_i8() by the
// operand without checked arithmetic (`self.as_i8() * n`, bounds.rs:
// 1247), which panics on overflow (e.g. Sign::Negative * i8::MIN)".
// This batch needs Sign::from(i64) and the i16/i32/i64 Mul faces (every
// Span getter multiplies the span-global sign into a field), so they
// are materialized here with the caller-side excluder the J1 ledger
// prescribed.
// ===========================================================================

/// The `-1/0/+1` value embodiment of a Sign, for spec positions.
pub open spec fn sp_sign_val(s: Sign) -> int {
    if s is Zero {
        0
    } else if s is Positive {
        1
    } else {
        -1
    }
}

/// Sign equality, materialized as a two-case variant test (the J1
/// ledger rule: enum contracts use variant tests, never `==`).
pub open spec fn sp_sign_eq(a: Sign, b: Sign) -> bool {
    ((a is Zero) <==> (b is Zero)) && ((a is Positive) <==> (b is Positive))
}

/// Translation-only: an owned copy of a Sign read from behind a
/// reference. The mounted J1 Sign panel predates this batch and its
/// Sign has no Copy/Clone (bounds.rs:629), so every read of a sign
/// stored in a borrowed Span routes through this helper (binding-free
/// match on the reference -- no move occurs). The ensures restores
/// the full variant identity.
pub(crate) exec fn sp_sign_of_ref(s: &Sign) -> (r: Sign)
    ensures
        ((r is Zero) <==> (s is Zero))
            && ((r is Positive) <==> (s is Positive))
            && ((r is Negative) <==> (s is Negative)),
{
    match s {
        Sign::Zero => Sign::Zero,
        Sign::Positive => Sign::Positive,
        Sign::Negative => Sign::Negative,
    }
}

/// Translation-only: Sign::is_zero without moving out of a borrowed
/// Span (the J1 panel's Sign::is_zero takes ownership; Sign has no
/// Copy/Clone -- see sp_sign_of_ref).
pub(crate) exec fn sp_sign_is_zero(s: &Sign) -> (r: bool)
    ensures
        r <==> (s is Zero),
{
    match s {
        Sign::Zero => true,
        Sign::Positive => false,
        Sign::Negative => false,
    }
}

/// Origin Rust: impl From<i64> for Sign
///     fn from(n: i64) -> Sign (jcore bounds.rs:1174-1179)
/// Upstream doc (jcore bounds.rs:1163-1166, the i32 twin's doc is the
/// family template): none beyond the bodies themselves.
pub exec fn sp_sign_from_i64(n: i64) -> (s: Sign)
    ensures
        (n == 0) <==> (s is Zero),
        (n > 0) <==> (s is Positive),
        (n < 0) <==> (s is Negative),
{
    if n == 0 {
        Sign::Zero
    } else if n > 0 {
        Sign::Positive
    } else {
        Sign::Negative
    }
}

/// Origin Rust: impl core::ops::Mul<Sign> for Sign
///     fn mul(self, rhs: Sign) -> Sign (jcore bounds.rs:1228-1241; the
///     match-based body, NOT an as_i8() product -- this face has no
///     overflow).
/// Upstream doc (jcore bounds.rs:1213-1226): none beyond the bodies.
pub exec fn sp_sign_mul_sign(a: Sign, b: Sign) -> (r: Sign)
    ensures
        (r is Zero) <==> (a is Zero) || (b is Zero),
        (r is Positive) <==> ((a is Positive && b is Positive)
            || (a is Negative && b is Negative)),
        (r is Negative) <==> ((a is Positive && b is Negative)
            || (a is Negative && b is Positive)),
{
    match a {
        Sign::Zero => Sign::Zero,
        Sign::Positive => match b {
            Sign::Zero => Sign::Zero,
            Sign::Positive => Sign::Positive,
            Sign::Negative => Sign::Negative,
        },
        Sign::Negative => match b {
            Sign::Zero => Sign::Zero,
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive,
        },
    }
}

/// Origin Rust: impl core::ops::Mul<i16> for Sign
///     fn mul(self, n: i16) -> i16 (jcore bounds.rs:1261-1268, body
///     `self.as_i16() * n`).
/// The machine product can only overflow on the (Negative, i16::MIN)
/// pair -- the J1 ledger's prescribed caller-side obligation (in-batch
/// callers discharge it from sp_field_inv, whose years range keeps
/// |years| <= 19_998).
pub exec fn sp_sign_mul_i16(s: Sign, n: i16) -> (r: i16)
    requires
        ((s is Negative) ==> (n != i16::MIN)),
    ensures
        (r as int) == (sp_sign_val(s)) * (n as int),
{
    let v: i16 = Sign::as_i16(s);
    v * n
}

/// Origin Rust: impl core::ops::Mul<i32> for Sign
///     fn mul(self, n: i32) -> i32 (jcore bounds.rs:1279-1286, body
///     `self.as_i32() * n`); same excluder note as sp_sign_mul_i16.
pub exec fn sp_sign_mul_i32(s: Sign, n: i32) -> (r: i32)
    requires
        ((s is Negative) ==> (n != i32::MIN)),
    ensures
        (r as int) == (sp_sign_val(s)) * (n as int),
{
    let v: i32 = Sign::as_i32(s);
    v * n
}

/// Origin Rust: impl core::ops::Mul<i64> for Sign
///     fn mul(self, n: i64) -> i64 (jcore bounds.rs:1297-1304, body
///     `self.as_i64() * n`); same excluder note as sp_sign_mul_i16.
pub exec fn sp_sign_mul_i64(s: Sign, n: i64) -> (r: i64)
    requires
        ((s is Negative) ==> (n != i64::MIN)),
    ensures
        (r as int) == (sp_sign_val(s)) * (n as int),
{
    let v: i64 = Sign::as_i64(s);
    v * n
}

// ===========================================================================
// Unit (span.rs:3876-3916) and UnitSet (span.rs:5747-5820).
// ===========================================================================

/// Origin Rust: pub enum Unit { Year = 9, Month = 8, Week = 7, Day = 6,
///     Hour = 5, Minute = 4, Second = 3, Millisecond = 2, Microsecond = 1,
///     Nanosecond = 0 } (span.rs:3876-3916)
/// Upstream doc (span.rs:3822-3874, abridged to the non-Example prose):
///   A way to refer to a single calendar or clock unit.
///   This type is principally used in APIs involving a `Span`, which is a
///   duration of time.
///   ... `Unit` has an ordering defined such that bigger units compare
///   greater than smaller units.
/// Lossy note: the upstream `= 9..= 0` discriminants exist only to feed
/// the UnitSet bitmap (`1 << unit as usize`, span.rs:5762) and do not
/// survive into the verus enum (variant identity is the value
/// embodiment; the ordering face materializes through the largest_unit
/// and only_calendar chains below).
#[derive(Clone, Copy)]
pub enum Unit {
    Year,
    Month,
    Week,
    Day,
    Hour,
    Minute,
    Second,
    Millisecond,
    Microsecond,
    Nanosecond,
}

/// Origin Rust: pub(crate) struct UnitSet(u16) (span.rs:5747).
/// Lossy note (file header, modeling loss 2): the u16 bitmap
/// materializes as ten structural zero-bookkeeping flags. Upstream
/// semantics preserved: a flag is set exactly when the corresponding
/// span field is non-zero (maintained by Span's setters through
/// UnitSet::set(u, field == 0)).
#[derive(Clone, Copy)]
pub struct UnitSet {
    pub year: bool,
    pub month: bool,
    pub week: bool,
    pub day: bool,
    pub hour: bool,
    pub minute: bool,
    pub second: bool,
    pub millisecond: bool,
    pub microsecond: bool,
    pub nanosecond: bool,
}

impl UnitSet {
    /// Origin Rust: const fn empty() -> UnitSet { UnitSet(0) }
    ///     (span.rs:5752-5754)
    /// Upstream doc (span.rs:5750): "Return a bit set representing all
    /// units as zero."
    pub(crate) exec fn empty() -> (s: UnitSet)
        ensures
            !s.year,
            !s.month,
            !s.week,
            !s.day,
            !s.hour,
            !s.minute,
            !s.second,
            !s.millisecond,
            !s.microsecond,
            !s.nanosecond,
    {
        UnitSet {
            year: false,
            month: false,
            week: false,
            day: false,
            hour: false,
            minute: false,
            second: false,
            millisecond: false,
            microsecond: false,
            nanosecond: false,
        }
    }

    /// Origin Rust: const fn set(self, unit: Unit, is_zero: bool)
    ///     -> UnitSet (span.rs:5758-5766, body `UnitSet(self.0 & !bit)`
    ///     / `UnitSet(self.0 | bit)` with `bit = 1 << unit as usize`)
    /// Upstream doc (span.rs:5756-5759): "Set the given `unit` to
    /// `is_zero` status in this set. When `is_zero` is false, the unit
    /// is added to this set. Otherwise, the unit is removed from this
    /// set."
    pub(crate) exec fn set(s: UnitSet, unit: Unit, is_zero: bool) -> (r: UnitSet)
        ensures
            // unit's own bit
            ((unit is Year) ==> ((is_zero ==> !r.year) && (!is_zero ==> r.year))),
            ((unit is Month) ==> ((is_zero ==> !r.month) && (!is_zero ==> r.month))),
            ((unit is Week) ==> ((is_zero ==> !r.week) && (!is_zero ==> r.week))),
            ((unit is Day) ==> ((is_zero ==> !r.day) && (!is_zero ==> r.day))),
            ((unit is Hour) ==> ((is_zero ==> !r.hour) && (!is_zero ==> r.hour))),
            ((unit is Minute) ==> ((is_zero ==> !r.minute) && (!is_zero ==> r.minute))),
            ((unit is Second) ==> ((is_zero ==> !r.second) && (!is_zero ==> r.second))),
            ((unit is Millisecond) ==> ((is_zero ==> !r.millisecond) && (!is_zero ==> r.millisecond))),
            ((unit is Microsecond) ==> ((is_zero ==> !r.microsecond) && (!is_zero ==> r.microsecond))),
            ((unit is Nanosecond) ==> ((is_zero ==> !r.nanosecond) && (!is_zero ==> r.nanosecond))),
            // the other nine bits pass through
            ((unit is Year) ==> (r.month == s.month && r.week == s.week && r.day == s.day
                && r.hour == s.hour && r.minute == s.minute && r.second == s.second
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Month) ==> (r.year == s.year && r.week == s.week && r.day == s.day
                && r.hour == s.hour && r.minute == s.minute && r.second == s.second
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Week) ==> (r.year == s.year && r.month == s.month && r.day == s.day
                && r.hour == s.hour && r.minute == s.minute && r.second == s.second
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Day) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.hour == s.hour && r.minute == s.minute && r.second == s.second
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Hour) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.day == s.day && r.minute == s.minute && r.second == s.second
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Minute) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.day == s.day && r.hour == s.hour && r.second == s.second
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Second) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.day == s.day && r.hour == s.hour && r.minute == s.minute
                && r.millisecond == s.millisecond && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Millisecond) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.day == s.day && r.hour == s.hour && r.minute == s.minute
                && r.second == s.second && r.microsecond == s.microsecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Microsecond) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.day == s.day && r.hour == s.hour && r.minute == s.minute
                && r.second == s.second && r.millisecond == s.millisecond
                && r.nanosecond == s.nanosecond)),
            ((unit is Nanosecond) ==> (r.year == s.year && r.month == s.month && r.week == s.week
                && r.day == s.day && r.hour == s.hour && r.minute == s.minute
                && r.second == s.second && r.millisecond == s.millisecond
                && r.microsecond == s.microsecond)),
    {
        match unit {
            Unit::Year => UnitSet {
                year: !is_zero,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Month => UnitSet {
                year: s.year,
                month: !is_zero,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Week => UnitSet {
                year: s.year,
                month: s.month,
                week: !is_zero,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Day => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: !is_zero,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Hour => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: !is_zero,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Minute => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: !is_zero,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Second => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: !is_zero,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Millisecond => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: !is_zero,
                microsecond: s.microsecond,
                nanosecond: s.nanosecond,
            },
            Unit::Microsecond => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: !is_zero,
                nanosecond: s.nanosecond,
            },
            Unit::Nanosecond => UnitSet {
                year: s.year,
                month: s.month,
                week: s.week,
                day: s.day,
                hour: s.hour,
                minute: s.minute,
                second: s.second,
                millisecond: s.millisecond,
                microsecond: s.microsecond,
                nanosecond: !is_zero,
            },
        }
    }

    /// Origin Rust: pub(crate) fn is_empty(&self) -> bool
    ///     (span.rs:5784-5786, body `self.0 == 0`)
    /// Upstream doc (span.rs:5782): "Returns true if and only if
    /// no units are in this set."
    pub(crate) exec fn is_empty(s: UnitSet) -> (r: bool)
        ensures
            r <==> (!s.year && !s.month && !s.week && !s.day && !s.hour
                && !s.minute && !s.second && !s.millisecond
                && !s.microsecond && !s.nanosecond),
    {
        !(s.year || s.month || s.week || s.day || s.hour || s.minute
            || s.second || s.millisecond || s.microsecond || s.nanosecond)
    }

    /// Origin Rust: pub(crate) fn contains(self, unit: Unit) -> bool
    ///     (span.rs:5791-5793, body `(self.0 & (1 << unit as usize))
    ///     != 0`)
    /// Upstream doc (span.rs:5788-5789): "Returns true when this
    /// `Span` contains a non-zero value for the given unit."
    pub(crate) exec fn contains(s: UnitSet, unit: Unit) -> (r: bool)
        ensures
            (unit is Year) ==> (r <==> s.year),
            (unit is Month) ==> (r <==> s.month),
            (unit is Week) ==> (r <==> s.week),
            (unit is Day) ==> (r <==> s.day),
            (unit is Hour) ==> (r <==> s.hour),
            (unit is Minute) ==> (r <==> s.minute),
            (unit is Second) ==> (r <==> s.second),
            (unit is Millisecond) ==> (r <==> s.millisecond),
            (unit is Microsecond) ==> (r <==> s.microsecond),
            (unit is Nanosecond) ==> (r <==> s.nanosecond),
    {
        match unit {
            Unit::Year => s.year,
            Unit::Month => s.month,
            Unit::Week => s.week,
            Unit::Day => s.day,
            Unit::Hour => s.hour,
            Unit::Minute => s.minute,
            Unit::Second => s.second,
            Unit::Millisecond => s.millisecond,
            Unit::Microsecond => s.microsecond,
            Unit::Nanosecond => s.nanosecond,
        }
    }

    /// Origin Rust: pub(crate) fn largest_unit(self) -> Option<Unit>
    ///     (span.rs:5822-5825: `let zeros = usize::try_from(
    ///     self.0.leading_zeros()).ok()?; 15usize.checked_sub(zeros)
    ///     .and_then(Unit::from_usize)`)
    /// Upstream doc (span.rs:5820): "Returns the largest unit in
    /// this set, or `None` if none are present."
    /// Lossy note: the leading_zeros bit trick materializes as a
    /// descending if-chain over the same ten flags; the None face is
    /// exact (None <==> empty) and every Some face is pinned by the
    /// spec twin sp_largest_unit_spec below (variant-for-variant).
    /// (None of this batch's translated upstream consumers call
    /// largest_unit -- the checked_add relative path is deferred -- but
    /// its contract is carried whole so the deferred consumers inherit
    /// it.)
    pub(crate) exec fn largest_unit(s: UnitSet) -> (r: Option<Unit>)
        ensures
            match r {
                Option::None => sp_largest_unit_spec(s) is None,
                Option::Some(u) => match sp_largest_unit_spec(s) {
                    Option::None => false,
                    Option::Some(v) => ((u is Year) <==> (v is Year))
                        && ((u is Month) <==> (v is Month))
                        && ((u is Week) <==> (v is Week))
                        && ((u is Day) <==> (v is Day))
                        && ((u is Hour) <==> (v is Hour))
                        && ((u is Minute) <==> (v is Minute))
                        && ((u is Second) <==> (v is Second))
                        && ((u is Millisecond) <==> (v is Millisecond))
                        && ((u is Microsecond) <==> (v is Microsecond))
                        && ((u is Nanosecond) <==> (v is Nanosecond)),
                },
            },
    {
        if s.year {
            Option::Some(Unit::Year)
        } else if s.month {
            Option::Some(Unit::Month)
        } else if s.week {
            Option::Some(Unit::Week)
        } else if s.day {
            Option::Some(Unit::Day)
        } else if s.hour {
            Option::Some(Unit::Hour)
        } else if s.minute {
            Option::Some(Unit::Minute)
        } else if s.second {
            Option::Some(Unit::Second)
        } else if s.millisecond {
            Option::Some(Unit::Millisecond)
        } else if s.microsecond {
            Option::Some(Unit::Microsecond)
        } else if s.nanosecond {
            Option::Some(Unit::Nanosecond)
        } else {
            Option::None
        }
    }
}

/// Spec twin of UnitSet::largest_unit (largeness order: Year > Month >
/// Week > Day > Hour > Minute > Second > Millisecond > Microsecond >
/// Nanosecond, the upstream enum discriminant order).
pub open spec fn sp_largest_unit_spec(s: UnitSet) -> Option<Unit> {
    if s.year {
        Option::Some(Unit::Year)
    } else if s.month {
        Option::Some(Unit::Month)
    } else if s.week {
        Option::Some(Unit::Week)
    } else if s.day {
        Option::Some(Unit::Day)
    } else if s.hour {
        Option::Some(Unit::Hour)
    } else if s.minute {
        Option::Some(Unit::Minute)
    } else if s.second {
        Option::Some(Unit::Second)
    } else if s.millisecond {
        Option::Some(Unit::Millisecond)
    } else if s.microsecond {
        Option::Some(Unit::Microsecond)
    } else if s.nanosecond {
        Option::Some(Unit::Nanosecond)
    } else {
        Option::None
    }
}

// ===========================================================================
// Span (span.rs:707-721) and its spec stack.
// ===========================================================================

/// Origin Rust: pub struct Span { sign: Sign, units: UnitSet,
///     years: i16, months: i32, weeks: i32, days: i32, hours: i32,
///     minutes: i64, seconds: i64, milliseconds: i64, microseconds: i64,
///     nanoseconds: i64 } (span.rs:707-721, derive(Clone, Copy, Default))
/// Upstream type doc (span.rs:31-706) -- the sign doctrine the whole
/// setter/getter surface leans on (span.rs:122-130):
///   The sign of a span applies to the entire span. When a span is
///   negative, then all of its units are negative [...]
/// And (span.rs:140-141):
///   And if any of a span's units are negative, then the entire span is
///   regarded as negative
/// The ten unit fields store magnitudes from the public API's
/// perspective (`months.abs()` on every try_* setter, span.rs:920), with
/// the span-global sign carried separately.
pub struct Span {
    pub sign: Sign,
    pub units: UnitSet,
    pub years: i16,
    pub months: i32,
    pub weeks: i32,
    pub days: i32,
    pub hours: i32,
    pub minutes: i64,
    pub seconds: i64,
    pub milliseconds: i64,
    pub microseconds: i64,
    pub nanoseconds: i64,
}

/// The zero face of a span: no unit set, all magnitudes zero.
pub open spec fn sp_all_zero(s: &Span) -> bool {
    s.years == 0
        && s.months == 0
        && s.weeks == 0
        && s.days == 0
        && s.hours == 0
        && s.minutes == 0
        && s.seconds == 0
        && s.milliseconds == 0
        && s.microseconds == 0
        && s.nanoseconds == 0
}

/// The field-domain invariant: every unit field within its b::Span*
/// range (jiff src/util/b.rs:193-231). This is the primary requires
/// tier of the batch (the J4 field-tier doctrine: upstream keeps less
/// than it debug-asserts, so contracts start at this tier, not at any
/// canonical tier).
pub open spec fn sp_field_inv(s: &Span) -> bool {
    &&& ((s.years as int) >= -19_998) && ((s.years as int) <= 19_998)
    &&& ((s.months as int) >= -239_976) && ((s.months as int) <= 239_976)
    &&& ((s.weeks as int) >= -1_043_497) && ((s.weeks as int) <= 1_043_497)
    &&& ((s.days as int) >= -7_304_484) && ((s.days as int) <= 7_304_484)
    &&& ((s.hours as int) >= -175_307_616) && ((s.hours as int) <= 175_307_616)
    &&& ((s.minutes as int) >= -10_518_456_960)
        && ((s.minutes as int) <= 10_518_456_960)
    &&& ((s.seconds as int) >= -631_107_417_600)
        && ((s.seconds as int) <= 631_107_417_600)
    &&& ((s.milliseconds as int) >= -631_107_417_600_000)
        && ((s.milliseconds as int) <= 631_107_417_600_000)
    &&& ((s.microseconds as int) >= -631_107_417_600_000_000)
        && ((s.microseconds as int) <= 631_107_417_600_000_000)
    // SpanNanoseconds: -9_223_372_036_854_775_807 ..= 9_223_372_036_854_775_807
    &&& ((s.nanoseconds as int) >= -9_223_372_036_854_775_807)
        && ((s.nanoseconds as int) <= 9_223_372_036_854_775_807)
}

/// The zero-sign consistency tier upstream maintains through `resign`
/// (span.rs:2957-2988): a span whose sign is Zero has no non-zero
/// units. (The converse -- non-zero units imply a non-Zero sign -- is
/// the tier the setters establish; only the direction `resign` needs
/// for its `(true, false)` arm is required here.)
pub open spec fn sp_zero_sign_ok(s: &Span) -> bool {
    (s.sign is Zero) ==> sp_all_zero(s)
}

/// The unit-flag bookkeeping tier: each UnitSet bit is set exactly
/// when the corresponding field is non-zero (what Span's setters
/// maintain through UnitSet::set(u, field == 0); upstream never
/// debug-asserts this, it is the struct's implicit well-formedness).
pub open spec fn sp_flags_ok(s: &Span) -> bool {
    (s.units.year <==> (s.years != 0))
        && (s.units.month <==> (s.months != 0))
        && (s.units.week <==> (s.weeks != 0))
        && (s.units.day <==> (s.days != 0))
        && (s.units.hour <==> (s.hours != 0))
        && (s.units.minute <==> (s.minutes != 0))
        && (s.units.second <==> (s.seconds != 0))
        && (s.units.millisecond <==> (s.milliseconds != 0))
        && (s.units.microsecond <==> (s.microseconds != 0))
        && (s.units.nanosecond <==> (s.nanoseconds != 0))
}

// The setter Some-faces, one per unit (span.rs:901-1077). Each is the
// conjunction the try_* setters establish: the invariant tiers, the
// magnitude face (the field holds |v|), the other nine fields and unit
// flags pass through, and the resign sign table instantiated on the
// setter's own value.

pub open spec fn sp_set_years_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.years as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.years as int) == (v as int))))
        && (s2.units.year <==> (s2.years != 0))
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_months_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.months as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.months as int) == (v as int))))
        && (s2.units.month <==> (s2.months != 0))
        && s2.years == s.years
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_weeks_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.weeks as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.weeks as int) == (v as int))))
        && (s2.units.week <==> (s2.weeks != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_days_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.days as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.days as int) == (v as int))))
        && (s2.units.day <==> (s2.days != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_hours_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.hours as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.hours as int) == (v as int))))
        && (s2.units.hour <==> (s2.hours != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_minutes_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.minutes as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.minutes as int) == (v as int))))
        && (s2.units.minute <==> (s2.minutes != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_seconds_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.seconds as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.seconds as int) == (v as int))))
        && (s2.units.second <==> (s2.seconds != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_milliseconds_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.milliseconds as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.milliseconds as int) == (v as int))))
        && (s2.units.millisecond <==> (s2.milliseconds != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.microseconds == s.microseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.microsecond == s.units.microsecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_microseconds_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.microseconds as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.microseconds as int) == (v as int))))
        && (s2.units.microsecond <==> (s2.microseconds != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.nanoseconds == s.nanoseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.nanosecond == s.units.nanosecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

pub open spec fn sp_set_nanoseconds_face(s: &Span, s2: &Span, v: i64) -> bool {
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && sp_flags_ok(s2)
        && sp_flags_ok(s)
        && (((v < 0) && ((s2.nanoseconds as int) == (0 - (v as int))))
            || (((v as int) >= 0) && ((s2.nanoseconds as int) == (v as int))))
        && (s2.units.nanosecond <==> (s2.nanoseconds != 0))
        && s2.years == s.years
        && s2.months == s.months
        && s2.weeks == s.weeks
        && s2.days == s.days
        && s2.hours == s.hours
        && s2.minutes == s.minutes
        && s2.seconds == s.seconds
        && s2.milliseconds == s.milliseconds
        && s2.microseconds == s.microseconds
        && s2.units.year == s.units.year
        && s2.units.month == s.units.month
        && s2.units.week == s.units.week
        && s2.units.day == s.units.day
        && s2.units.hour == s.units.hour
        && s2.units.minute == s.units.minute
        && s2.units.second == s.units.second
        && s2.units.millisecond == s.units.millisecond
        && s2.units.microsecond == s.units.microsecond
        && ((v < 0) ==> (s2.sign is Negative))
        && ((v > 0) ==> (((s.sign is Positive) ==> (s2.sign is Positive))
            && ((s.sign is Zero) ==> (s2.sign is Positive))
            && ((s.sign is Negative) ==> (s2.sign is Negative))))
        && ((v == 0) ==> ((sp_all_zero(s2) ==> (s2.sign is Zero))
            && (!sp_all_zero(s2) ==> (((s2.sign is Positive)
                <==> (s.sign is Positive))
                && ((s2.sign is Negative) <==> (s.sign is Negative))))))
}

impl Span {
    /// Origin Rust: pub fn new() -> Span { Span::default() }
    ///     (span.rs:731-733) with the derived Default
    ///     (span.rs:707, derive(Default): Sign::Zero, empty UnitSet,
    ///     all unit fields 0).
    /// Upstream doc (span.rs:729-730): "Creates a new span representing
    /// a zero duration. That is, a duration in which no time has
    /// passed."
    pub exec fn new() -> (s: Span)
        ensures
            sp_field_inv(&s),
            sp_zero_sign_ok(&s),
            sp_flags_ok(&s),
            sp_all_zero(&s),
            s.sign is Zero,
            !s.units.year,
            !s.units.month,
            !s.units.week,
            !s.units.day,
            !s.units.hour,
            !s.units.minute,
            !s.units.second,
            !s.units.millisecond,
            !s.units.microsecond,
            !s.units.nanosecond,
    {
        Span {
            sign: Sign::Zero,
            units: UnitSet::empty(),
            years: 0,
            months: 0,
            weeks: 0,
            days: 0,
            hours: 0,
            minutes: 0,
            seconds: 0,
            milliseconds: 0,
            microseconds: 0,
            nanoseconds: 0,
        }
    }

    // ----------------------------------------------------------------
    // Crate-internal unchecked setters (span.rs:2586-2664).
    // Upstream block doc (span.rs:2583-2587): "Crate internal APIs that
    // permit setting units without checks. Callers should be very
    // careful when using these. These notably also do not handle
    // updating the sign on the `Span` and require the precisely correct
    // integer primitive."
    // ----------------------------------------------------------------

    /// Origin Rust: pub(crate) fn years_unchecked(mut self, years: i16)
    ///     -> Span (span.rs:2590-2594)
    pub(crate) exec fn years_unchecked(&self, years: i16) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.years == years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (years == 0) <==> !r.units.year,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Year, years == 0),
            years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn months_unchecked(mut self, months: i32)
    ///     -> Span (span.rs:2597-2601)
    pub(crate) exec fn months_unchecked(&self, months: i32) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.months == months,
            r.years == self.years,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (months == 0) <==> !r.units.month,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Month, months == 0),
            years: self.years,
            months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn weeks_unchecked(mut self, weeks: i32)
    ///     -> Span (span.rs:2604-2608)
    pub(crate) exec fn weeks_unchecked(&self, weeks: i32) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.weeks == weeks,
            r.years == self.years,
            r.months == self.months,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (weeks == 0) <==> !r.units.week,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Week, weeks == 0),
            years: self.years,
            months: self.months,
            weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn days_unchecked(mut self, days: i32)
    ///     -> Span (span.rs:2611-2615)
    pub(crate) exec fn days_unchecked(&self, days: i32) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.days == days,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (days == 0) <==> !r.units.day,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Day, days == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn hours_unchecked(mut self, hours: i32)
    ///     -> Span (span.rs:2618-2622)
    pub(crate) exec fn hours_unchecked(&self, hours: i32) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.hours == hours,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (hours == 0) <==> !r.units.hour,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Hour, hours == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn minutes_unchecked(mut self, minutes: i64)
    ///     -> Span (span.rs:2625-2629)
    pub(crate) exec fn minutes_unchecked(&self, minutes: i64) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.minutes == minutes,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (minutes == 0) <==> !r.units.minute,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Minute, minutes == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn seconds_unchecked(mut self, seconds: i64)
    ///     -> Span (span.rs:2632-2636)
    pub(crate) exec fn seconds_unchecked(&self, seconds: i64) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.seconds == seconds,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (seconds == 0) <==> !r.units.second,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Second, seconds == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn milliseconds_unchecked(mut self,
    ///     milliseconds: i64) -> Span (span.rs:2639-2643)
    pub(crate) exec fn milliseconds_unchecked(&self, milliseconds: i64) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.milliseconds == milliseconds,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            (milliseconds == 0) <==> !r.units.millisecond,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Millisecond, milliseconds == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn microseconds_unchecked(mut self,
    ///     microseconds: i64) -> Span (span.rs:2646-2650)
    pub(crate) exec fn microseconds_unchecked(&self, microseconds: i64) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.microseconds == microseconds,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.nanoseconds == self.nanoseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.nanosecond == self.units.nanosecond,
            (microseconds == 0) <==> !r.units.microsecond,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Microsecond, microseconds == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn nanoseconds_unchecked(mut self,
    ///     nanoseconds: i64) -> Span (span.rs:2653-2657)
    pub(crate) exec fn nanoseconds_unchecked(&self, nanoseconds: i64) -> (r: Span)
        ensures
            r.sign == self.sign,
            r.nanoseconds == nanoseconds,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            (nanoseconds == 0) <==> !r.units.nanosecond,
    {
        Span {
            sign: sp_sign_of_ref(&self.sign),
            units: UnitSet::set(self.units, Unit::Nanosecond, nanoseconds == 0),
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds,
        }
    }

    /// Origin Rust: pub(crate) fn sign_unchecked(self, sign: Sign)
    ///     -> Span (span.rs:2660-2662, body `Span { sign, ..self }`)
    pub(crate) exec fn sign_unchecked(&self, sign: Sign) -> (r: Span)
        ensures
            r.sign == sign,
            r.units.year == self.units.year,
            r.units.month == self.units.month,
            r.units.week == self.units.week,
            r.units.day == self.units.day,
            r.units.hour == self.units.hour,
            r.units.minute == self.units.minute,
            r.units.second == self.units.second,
            r.units.millisecond == self.units.millisecond,
            r.units.microsecond == self.units.microsecond,
            r.units.nanosecond == self.units.nanosecond,
            r.years == self.years,
            r.months == self.months,
            r.weeks == self.weeks,
            r.days == self.days,
            r.hours == self.hours,
            r.minutes == self.minutes,
            r.seconds == self.seconds,
            r.milliseconds == self.milliseconds,
            r.microseconds == self.microseconds,
            r.nanoseconds == self.nanoseconds,
    {
        Span {
            sign,
            units: self.units,
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        }
    }

    // ----------------------------------------------------------------
    // resign (span.rs:2957-2988) and the unit setters.
    // ----------------------------------------------------------------

    /// Origin Rust: fn resign(&self, units: impl Into<i64>, new: &Span)
    ///     -> Sign (span.rs:2957-2988; the nested `fn imp` body is the
    ///     `units.is_negative()` early return, the `new_is_zero`
    ///     recomputation over all ten fields when `units == 0`, and the
    ///     `(span.is_zero(), new_is_zero)` match).
    /// Upstream doc (span.rs:2956-2957): "Given some new units to set on
    /// this span and the span updates with the new units, this
    /// determines the what the sign of `new` should be."
    /// The requires tier is the caller-side shape every try_* setter
    /// establishes: `new` is the same span with exactly one unit's
    /// magnitude replaced by `|units|`, so a positive `units` value
    /// always leaves `new` non-zero, and a Zero-sign span is all-zero
    /// (sp_zero_sign_ok).
    pub(crate) exec fn resign(&self, units: i64, new: &Span) -> (r: Sign)
        requires
            sp_sign_eq(new.sign, self.sign),
            (self.sign is Zero) ==> sp_all_zero(self),
            (units > 0) ==> !sp_all_zero(new),
        ensures
            (units < 0) ==> (r is Negative),
            ((units == 0) && sp_all_zero(new)) ==> (r is Zero),
            ((self.sign is Positive) && (units >= 0) && !sp_all_zero(new))
                ==> (r is Positive),
            ((self.sign is Negative) && (units >= 0) && !sp_all_zero(new))
                ==> (r is Negative),
            ((self.sign is Zero) && (units == 0)) ==> (r is Zero),
            ((self.sign is Zero) && (units > 0)) ==> (r is Positive),
    {
        // "Negative units anywhere always makes the entire span
        // negative." (span.rs:2961)
        if units < 0 {
            return Sign::Negative;
        }
        // "When `units == 0` and it was previously non-zero, then
        // `new.sign` won't be `0` and thus `new_is_zero` will be false
        // when it should be true. So in this case, we need to re-check
        // all the units to set the sign correctly." (span.rs:2966-2969)
        let mut new_is_zero: bool = sp_sign_is_zero(&new.sign) && units == 0;
        if units == 0 {
            new_is_zero = new.years == 0
                && new.months == 0
                && new.weeks == 0
                && new.days == 0
                && new.hours == 0
                && new.minutes == 0
                && new.seconds == 0
                && new.milliseconds == 0
                && new.microseconds == 0
                && new.nanoseconds == 0;
        }
        let span_is_zero: bool = sp_sign_is_zero(&self.sign);
        if new_is_zero {
            Sign::Zero
        } else if span_is_zero {
            sp_sign_from_i64(units)
        } else {
            sp_sign_of_ref(&new.sign)
        }
    }


    /// Origin Rust: pub fn try_years<I: Into<i64>>(self, years: I)
    ///     -> Result<Span, Error> (span.rs:901-907)
    /// Upstream doc (span.rs:891-899):
    ///   Set the number of years on this span. The value may be negative.
    ///   The panicking version of this method is [`Span::years`].
    ///   # Errors
    ///   This returns an error when the number of years is too small or
    ///   too big. The minimum value is `-19,998`. The maximum value is
    ///   `19,998`.
    pub exec fn try_years(&self, years: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_years_face(self, &s, years),
                Option::None => !(((-19_998int) <= (years as int))
                    && ((years as int) <= 19_998)),
            },
    {
        let checked: Option<i16> =
            crate::bounds::const_check::i16(-19_998, 19_998, years);
        match checked {
            Option::Some(y) => {
                let mag: i16 = if y < 0 { 0 - y } else { y };
                let mid: Span = self.years_unchecked(mag);
                let sg: Sign = self.resign(years, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn years<I: Into<i64>>(self, years: I) -> Span
    ///     (span.rs:745-748, body `self.try_years(years).expect("value
    ///     for years is out of bounds")`)
    /// Upstream doc (span.rs:735-744):
    ///   Set the number of years on this span. The value may be negative.
    ///   The fallible version of this method is [`Span::try_years`].
    ///   # Panics
    ///   This panics when the number of years is too small or too big.
    ///   The minimum value is `-19,998`.
    ///   The maximum value is `19,998`.
    /// (# Panics -> the in-range requires; the upstream expect site's
    ///  dead-arm carries the panic fidelity, span.rs:746.)
    pub exec fn years(&self, years: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-19_998int) <= (years as int)) && ((years as int) <= 19_998),
        ensures
            sp_set_years_face(self, &r, years),
    {
        let t: Option<Span> = self.try_years(years);
        match t {
            Option::Some(s) => s,
            // Dead arm: b::SpanYears::check never errors on the
            // in-bounds domain above.
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_months<I: Into<i64>>(self, months: I)
    ///     -> Result<Span, Error> (span.rs:918-924)
    /// Upstream doc (span.rs:908-916):
    ///   Set the number of months on this span. The value may be negative.
    ///   The panicking version of this method is [`Span::months`].
    ///   # Errors
    ///   This returns an error when the number of months is too small or
    ///   too big. The minimum value is `-239,976`. The maximum value is
    ///   `239,976`.
    pub exec fn try_months(&self, months: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_months_face(self, &s, months),
                Option::None => !(((-239_976int) <= (months as int))
                    && ((months as int) <= 239_976)),
            },
    {
        let checked: Option<i32> =
            crate::bounds::const_check::i32(-239_976, 239_976, months);
        match checked {
            Option::Some(m) => {
                let mag: i32 = if m < 0 { 0 - m } else { m };
                let mid: Span = self.months_unchecked(mag);
                let sg: Sign = self.resign(months, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn months<I: Into<i64>>(self, months: I) -> Span
    ///     (span.rs:759-762, .expect("value for months is out of
    ///     bounds"))
    /// Upstream doc (span.rs:749-758):
    ///   Set the number of months on this span. The value may be negative.
    ///   The fallible version of this method is [`Span::try_months`].
    ///   # Panics
    ///   This panics when the number of months is too small or too big.
    ///   The minimum value is `-239,976`.
    ///   The maximum value is `239,976`.
    pub exec fn months(&self, months: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-239_976int) <= (months as int)) && ((months as int) <= 239_976),
        ensures
            sp_set_months_face(self, &r, months),
    {
        let t: Option<Span> = self.try_months(months);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_weeks<I: Into<i64>>(self, weeks: I)
    ///     -> Result<Span, Error> (span.rs:935-941)
    /// Upstream doc (span.rs:925-933):
    ///   Set the number of weeks on this span. The value may be negative.
    ///   The panicking version of this method is [`Span::weeks`].
    ///   # Errors
    ///   This returns an error when the number of weeks is too small or
    ///   too big. The minimum value is `-1,043,497`. The maximum value
    ///   is `1_043_497`.
    pub exec fn try_weeks(&self, weeks: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_weeks_face(self, &s, weeks),
                Option::None => !(((-1_043_497int) <= (weeks as int))
                    && ((weeks as int) <= 1_043_497)),
            },
    {
        let checked: Option<i32> =
            crate::bounds::const_check::i32(-1_043_497, 1_043_497, weeks);
        match checked {
            Option::Some(w) => {
                let mag: i32 = if w < 0 { 0 - w } else { w };
                let mid: Span = self.weeks_unchecked(mag);
                let sg: Sign = self.resign(weeks, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn weeks<I: Into<i64>>(self, weeks: I) -> Span
    ///     (span.rs:773-776, .expect("value for weeks is out of
    ///     bounds"))
    /// Upstream doc (span.rs:763-772):
    ///   Set the number of weeks on this span. The value may be negative.
    ///   The fallible version of this method is [`Span::try_weeks`].
    ///   # Panics
    ///   This panics when the number of weeks is too small or too big.
    ///   The minimum value is `-1,043,497`.
    ///   The maximum value is `1_043_497`.
    pub exec fn weeks(&self, weeks: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-1_043_497int) <= (weeks as int)) && ((weeks as int) <= 1_043_497),
        ensures
            sp_set_weeks_face(self, &r, weeks),
    {
        let t: Option<Span> = self.try_weeks(weeks);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_days<I: Into<i64>>(self, days: I)
    ///     -> Result<Span, Error> (span.rs:952-958)
    /// Upstream doc (span.rs:942-950):
    ///   Set the number of days on this span. The value may be negative.
    ///   The panicking version of this method is [`Span::days`].
    ///   # Errors
    ///   This returns an error when the number of days is too small or
    ///   too big. The minimum value is `-7,304,484`. The maximum value
    ///   is `7,304,484`.
    pub exec fn try_days(&self, days: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_days_face(self, &s, days),
                Option::None => !(((-7_304_484int) <= (days as int))
                    && ((days as int) <= 7_304_484)),
            },
    {
        let checked: Option<i32> =
            crate::bounds::const_check::i32(-7_304_484, 7_304_484, days);
        match checked {
            Option::Some(d) => {
                let mag: i32 = if d < 0 { 0 - d } else { d };
                let mid: Span = self.days_unchecked(mag);
                let sg: Sign = self.resign(days, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn days<I: Into<i64>>(self, days: I) -> Span
    ///     (span.rs:787-790, .expect("value for days is out of bounds"))
    /// Upstream doc (span.rs:777-786):
    ///   Set the number of days on this span. The value may be negative.
    ///   The fallible version of this method is [`Span::try_days`].
    ///   # Panics
    ///   This panics when the number of days is too small or too big.
    ///   The minimum value is `-7,304,484`.
    ///   The maximum value is `7,304,484`.
    pub exec fn days(&self, days: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-7_304_484int) <= (days as int)) && ((days as int) <= 7_304_484),
        ensures
            sp_set_days_face(self, &r, days),
    {
        let t: Option<Span> = self.try_days(days);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_hours<I: Into<i64>>(self, hours: I)
    ///     -> Result<Span, Error> (span.rs:969-975)
    /// Upstream doc (span.rs:959-967):
    ///   Set the number of hours on this span. The value may be negative.
    ///   The panicking version of this method is [`Span::hours`].
    ///   # Errors
    ///   This returns an error when the number of hours is too small or
    ///   too big. The minimum value is `-175,307,616`. The maximum value
    ///   is `175,307,616`.
    pub exec fn try_hours(&self, hours: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_hours_face(self, &s, hours),
                Option::None => !(((-175_307_616int) <= (hours as int))
                    && ((hours as int) <= 175_307_616)),
            },
    {
        let checked: Option<i32> =
            crate::bounds::const_check::i32(-175_307_616, 175_307_616, hours);
        match checked {
            Option::Some(h) => {
                let mag: i32 = if h < 0 { 0 - h } else { h };
                let mid: Span = self.hours_unchecked(mag);
                let sg: Sign = self.resign(hours, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn hours<I: Into<i64>>(self, hours: I) -> Span
    ///     (span.rs:801-804, .expect("value for hours is out of
    ///     bounds"))
    /// Upstream doc (span.rs:791-800):
    ///   Set the number of hours on this span. The value may be negative.
    ///   The fallible version of this method is [`Span::try_hours`].
    ///   # Panics
    ///   This panics when the number of hours is too small or too big.
    ///   The minimum value is `-175,307,616`.
    ///   The maximum value is `175,307,616`.
    pub exec fn hours(&self, hours: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-175_307_616int) <= (hours as int)) && ((hours as int) <= 175_307_616),
        ensures
            sp_set_hours_face(self, &r, hours),
    {
        let t: Option<Span> = self.try_hours(hours);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_minutes<I: Into<i64>>(self, minutes: I)
    ///     -> Result<Span, Error> (span.rs:986-992)
    /// Upstream doc (span.rs:976-984):
    ///   Set the number of minutes on this span. The value may be
    ///   negative. The panicking version of this method is
    ///   [`Span::try_minutes`].
    ///   # Errors
    ///   This returns an error when the number of minutes is too small
    ///   or too big. The minimum value is `-10,518,456,960`. The maximum
    ///   value is `10,518,456,960`.
    pub exec fn try_minutes(&self, minutes: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_minutes_face(self, &s, minutes),
                Option::None => !(((-10_518_456_960int) <= (minutes as int))
                    && ((minutes as int) <= 10_518_456_960)),
            },
    {
        let checked: Option<i64> =
            crate::bounds::const_check::i64(-10_518_456_960, 10_518_456_960, minutes);
        match checked {
            Option::Some(m) => {
                let mag: i64 = if m < 0 { 0 - m } else { m };
                let mid: Span = self.minutes_unchecked(mag);
                let sg: Sign = self.resign(minutes, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn minutes<I: Into<i64>>(self, minutes: I)
    ///     -> Span (span.rs:815-818, .expect("value for minutes is out
    ///     of bounds"))
    /// Upstream doc (span.rs:805-814):
    ///   Set the number of minutes on this span. The value may be
    ///   negative. The fallible version of this method is
    ///   [`Span::try_minutes`].
    ///   # Panics
    ///   This panics when the number of minutes is too small or too
    ///   big. The minimum value is `-10,518,456,960`.
    ///   The maximum value is `10,518,456,960`.
    pub exec fn minutes(&self, minutes: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-10_518_456_960int) <= (minutes as int))
                && ((minutes as int) <= 10_518_456_960),
        ensures
            sp_set_minutes_face(self, &r, minutes),
    {
        let t: Option<Span> = self.try_minutes(minutes);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_seconds<I: Into<i64>>(self, seconds: I)
    ///     -> Result<Span, Error> (span.rs:1003-1009)
    /// Upstream doc (span.rs:993-1001):
    ///   Set the number of seconds on this span. The value may be
    ///   negative. The panicking version of this method is
    ///   [`Span::try_seconds`].
    ///   # Errors
    ///   This returns an error when the number of seconds is too small
    ///   or too big. The minimum value is `-631,107,417,600`. The
    ///   maximum value is `631,107,417,600`.
    pub exec fn try_seconds(&self, seconds: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_seconds_face(self, &s, seconds),
                Option::None => !(((-631_107_417_600int) <= (seconds as int))
                    && ((seconds as int) <= 631_107_417_600)),
            },
    {
        let checked: Option<i64> = crate::bounds::const_check::i64(
            -631_107_417_600,
            631_107_417_600,
            seconds,
        );
        match checked {
            Option::Some(s0) => {
                let mag: i64 = if s0 < 0 { 0 - s0 } else { s0 };
                let mid: Span = self.seconds_unchecked(mag);
                let sg: Sign = self.resign(seconds, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn seconds<I: Into<i64>>(self, seconds: I)
    ///     -> Span (span.rs:829-832, .expect("value for seconds is out
    ///     of bounds"))
    /// Upstream doc (span.rs:819-828):
    ///   Set the number of seconds on this span. The value may be
    ///   negative. The fallible version of this method is
    ///   [`Span::try_seconds`].
    ///   # Panics
    ///   This panics when the number of seconds is too small or too
    ///   big. The minimum value is `-631,107,417,600`.
    ///   The maximum value is `631,107,417,600`.
    pub exec fn seconds(&self, seconds: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-631_107_417_600int) <= (seconds as int))
                && ((seconds as int) <= 631_107_417_600),
        ensures
            sp_set_seconds_face(self, &r, seconds),
    {
        let t: Option<Span> = self.try_seconds(seconds);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_milliseconds<I: Into<i64>>(
    ///     self, milliseconds: I) -> Result<Span, Error>
    ///     (span.rs:1021-1028)
    /// Upstream doc (span.rs:1010-1019):
    ///   Set the number of milliseconds on this span. The value may be
    ///   negative. The panicking version of this method is
    ///   [`Span::try_milliseconds`].
    ///   # Errors
    ///   This returns an error when the number of milliseconds is too
    ///   small or too big. The minimum value is
    ///   `-631,107,417,600,000`. The maximum value is
    ///   `631,107,417,600,000`.
    pub exec fn try_milliseconds(&self, milliseconds: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_milliseconds_face(self, &s, milliseconds),
                Option::None => !(((-631_107_417_600_000int)
                    <= (milliseconds as int))
                    && ((milliseconds as int) <= 631_107_417_600_000)),
            },
    {
        let checked: Option<i64> = crate::bounds::const_check::i64(
            -631_107_417_600_000,
            631_107_417_600_000,
            milliseconds,
        );
        match checked {
            Option::Some(m0) => {
                let mag: i64 = if m0 < 0 { 0 - m0 } else { m0 };
                let mid: Span = self.milliseconds_unchecked(mag);
                let sg: Sign = self.resign(milliseconds, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn milliseconds<I: Into<i64>>(
    ///     self, milliseconds: I) -> Span (span.rs:843-847,
    ///     .expect("value for milliseconds is out of bounds"))
    /// Upstream doc (span.rs:833-842):
    ///   Set the number of milliseconds on this span. The value may be
    ///   negative. The fallible version of this method is
    ///   [`Span::try_milliseconds`].
    ///   # Panics
    ///   This panics when the number of milliseconds is too small or
    ///   too big. The minimum value is `-631,107,417,600,000`.
    ///   The maximum value is `631,107,417,600,000`.
    pub exec fn milliseconds(&self, milliseconds: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-631_107_417_600_000int) <= (milliseconds as int))
                && ((milliseconds as int) <= 631_107_417_600_000),
        ensures
            sp_set_milliseconds_face(self, &r, milliseconds),
    {
        let t: Option<Span> = self.try_milliseconds(milliseconds);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_microseconds<I: Into<i64>>(
    ///     self, microseconds: I) -> Result<Span, Error>
    ///     (span.rs:1042-1049)
    /// Upstream doc (span.rs:1031-1040):
    ///   Set the number of microseconds on this span. The value may be
    ///   negative. The panicking version of this method is
    ///   [`Span::try_microseconds`].
    ///   # Errors
    ///   This returns an error when the number of microseconds is too
    ///   small or too big. The minimum value is
    ///   `-631,107,417,600,000,000`. The maximum value is
    ///   `631,107,417,600,000,000`.
    pub exec fn try_microseconds(&self, microseconds: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_microseconds_face(self, &s, microseconds),
                Option::None => !(((-631_107_417_600_000_000int)
                    <= (microseconds as int))
                    && ((microseconds as int) <= 631_107_417_600_000_000)),
            },
    {
        let checked: Option<i64> = crate::bounds::const_check::i64(
            -631_107_417_600_000_000,
            631_107_417_600_000_000,
            microseconds,
        );
        match checked {
            Option::Some(u0) => {
                let mag: i64 = if u0 < 0 { 0 - u0 } else { u0 };
                let mid: Span = self.microseconds_unchecked(mag);
                let sg: Sign = self.resign(microseconds, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn microseconds<I: Into<i64>>(
    ///     self, microseconds: I) -> Span (span.rs:858-862,
    ///     .expect("value for microseconds is out of bounds"))
    /// Upstream doc (span.rs:848-857):
    ///   Set the number of microseconds on this span. The value may be
    ///   negative. The fallible version of this method is
    ///   [`Span::try_microseconds`].
    ///   # Panics
    ///   This panics when the number of microseconds is too small or
    ///   too big. The minimum value is `-631,107,417,600,000,000`.
    ///   The maximum value is `631,107,417,600,000,000`.
    pub exec fn microseconds(&self, microseconds: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-631_107_417_600_000_000int) <= (microseconds as int))
                && ((microseconds as int) <= 631_107_417_600_000_000),
        ensures
            sp_set_microseconds_face(self, &r, microseconds),
    {
        let t: Option<Span> = self.try_microseconds(microseconds);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    /// Origin Rust: pub fn try_nanoseconds<I: Into<i64>>(
    ///     self, nanoseconds: I) -> Result<Span, Error>
    ///     (span.rs:1070-1077)
    /// Upstream doc (span.rs:1052-1068):
    ///   Set the number of nanoseconds on this span. The value may be
    ///   negative.
    ///   Note that unlike all other units, a 64-bit integer number of
    ///   nanoseconds is not big enough to represent all possible spans
    ///   between all possible datetimes supported by Jiff. [...]
    ///   The panicking version of this method is
    ///   [`Span::try_nanoseconds`].
    ///   # Errors
    ///   This returns an error when the number of nanoseconds is too
    ///   small or too big. The minimum value is
    ///   `-9,223,372,036,854,775,807`. The maximum value is
    ///   `9,223,372,036,854,775,807`.
    /// (The b::SpanNanoseconds range is i64::MIN + 1 ..= i64::MAX,
    ///  util/b.rs:230 -- "our min is equal to -max, so that [...]
    ///  the absolute value is always defined".)
    pub exec fn try_nanoseconds(&self, nanoseconds: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s) => sp_set_nanoseconds_face(self, &s, nanoseconds),
                Option::None => !(((-9_223_372_036_854_775_807int)
                    <= (nanoseconds as int))
                    && ((nanoseconds as int) <= 9_223_372_036_854_775_807)),
            },
    {
        let checked: Option<i64> = crate::bounds::const_check::i64(
            -9_223_372_036_854_775_807,
            9_223_372_036_854_775_807,
            nanoseconds,
        );
        match checked {
            Option::Some(n0) => {
                let mag: i64 = if n0 < 0 { 0 - n0 } else { n0 };
                let mid: Span = self.nanoseconds_unchecked(mag);
                let sg: Sign = self.resign(nanoseconds, &mid);
                let s: Span = mid.sign_unchecked(sg);
                Option::Some(s)
            }
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub fn nanoseconds<I: Into<i64>>(
    ///     self, nanoseconds: I) -> Span (span.rs:880-886,
    ///     .expect("value for nanoseconds is out of bounds"))
    /// Upstream doc (span.rs:862-879):
    ///   Set the number of nanoseconds on this span. The value may be
    ///   negative.
    ///   Note that unlike all other units, a 64-bit integer number of
    ///   nanoseconds is not big enough to represent all possible spans
    ///   between all possible datetimes supported by Jiff. [...]
    ///   The fallible version of this method is
    ///   [`Span::try_nanoseconds`].
    ///   # Panics
    ///   This panics when the number of nanoseconds is too small or
    ///   too big. The minimum value is
    ///   `-9,223,372,036,854,775,807`.
    ///   The maximum value is `9,223,372,036,854,775,807`.
    pub exec fn nanoseconds(&self, nanoseconds: i64) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
            ((-9_223_372_036_854_775_807int) <= (nanoseconds as int))
                && ((nanoseconds as int) <= 9_223_372_036_854_775_807),
        ensures
            sp_set_nanoseconds_face(self, &r, nanoseconds),
    {
        let t: Option<Span> = self.try_nanoseconds(nanoseconds);
        match t {
            Option::Some(s) => s,
            Option::None => {
                assert(false);
                self.sign_unchecked(Sign::Zero)
            }
        }
    }

    // ----------------------------------------------------------------
    // Field getters (span.rs:1082-1306) and the crate-internal
    // unsigned getters (span.rs:2494-2560).
    // ----------------------------------------------------------------

    /// Origin Rust: pub fn get_years(&self) -> i16
    ///     { self.sign * self.years } (span.rs:1101-1102)
    /// Upstream doc (span.rs:1083-1087):
    ///   Returns the number of year units in this span.
    ///   Note that this is not the same as the total number of years in
    ///   the span. To get that, you'll need to use either [`Span::round`]
    ///   or [`Span::total`].
    /// (The `Sign * i16` machine product is the J1 ledger's
    ///  Sign::Negative * i16::MIN overflow face; sp_field_inv keeps
    ///  |years| <= 19_998 so the excluder always holds under the
    ///  requires here.)
    pub exec fn get_years(&self) -> (r: i16)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.years as int)),
    {
        sp_sign_mul_i16(sp_sign_of_ref(&self.sign), self.years)
    }

    /// Origin Rust: pub fn get_months(&self) -> i32
    ///     { self.sign * self.months } (span.rs:1123-1124)
    /// Upstream doc (span.rs:1105-1109): the get_years doc with
    ///   month/months substituted.
    pub exec fn get_months(&self) -> (r: i32)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.months as int)),
    {
        sp_sign_mul_i32(sp_sign_of_ref(&self.sign), self.months)
    }

    /// Origin Rust: pub fn get_weeks(&self) -> i32
    ///     { self.sign * self.weeks } (span.rs:1145-1146)
    /// Upstream doc (span.rs:1127-1131): the get_years doc with
    ///   week/weeks substituted.
    pub exec fn get_weeks(&self) -> (r: i32)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.weeks as int)),
    {
        sp_sign_mul_i32(sp_sign_of_ref(&self.sign), self.weeks)
    }

    /// Origin Rust: pub fn get_days(&self) -> i32
    ///     { self.sign * self.days } (span.rs:1169-1170)
    /// Upstream doc (span.rs:1149-1153): the get_years doc with
    ///   day/days substituted.
    pub exec fn get_days(&self) -> (r: i32)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.days as int)),
    {
        sp_sign_mul_i32(sp_sign_of_ref(&self.sign), self.days)
    }

    /// Origin Rust: pub fn get_hours(&self) -> i32
    ///     { self.sign * self.hours } (span.rs:1191-1192)
    /// Upstream doc (span.rs:1173-1177): the get_years doc with
    ///   hour/hours substituted.
    pub exec fn get_hours(&self) -> (r: i32)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.hours as int)),
    {
        sp_sign_mul_i32(sp_sign_of_ref(&self.sign), self.hours)
    }

    /// Origin Rust: pub fn get_minutes(&self) -> i64
    ///     { self.sign * self.minutes } (span.rs:1213-1214)
    /// Upstream doc (span.rs:1195-1199): the get_years doc with
    ///   minute/minutes substituted.
    pub exec fn get_minutes(&self) -> (r: i64)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.minutes as int)),
    {
        sp_sign_mul_i64(sp_sign_of_ref(&self.sign), self.minutes)
    }

    /// Origin Rust: pub fn get_seconds(&self) -> i64
    ///     { self.sign * self.seconds } (span.rs:1235-1236)
    /// Upstream doc (span.rs:1217-1221): the get_years doc with
    ///   second/seconds substituted.
    pub exec fn get_seconds(&self) -> (r: i64)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.seconds as int)),
    {
        sp_sign_mul_i64(sp_sign_of_ref(&self.sign), self.seconds)
    }

    /// Origin Rust: pub fn get_milliseconds(&self) -> i64
    ///     { self.sign * self.milliseconds } (span.rs:1257-1258)
    /// Upstream doc (span.rs:1239-1243): the get_years doc with
    ///   millisecond/milliseconds substituted.
    pub exec fn get_milliseconds(&self) -> (r: i64)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.milliseconds as int)),
    {
        sp_sign_mul_i64(sp_sign_of_ref(&self.sign), self.milliseconds)
    }

    /// Origin Rust: pub fn get_microseconds(&self) -> i64
    ///     { self.sign * self.microseconds } (span.rs:1280-1281)
    /// Upstream doc (span.rs:1261-1265): the get_years doc with
    ///   microsecond/microseconds substituted.
    pub exec fn get_microseconds(&self) -> (r: i64)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.microseconds as int)),
    {
        sp_sign_mul_i64(sp_sign_of_ref(&self.sign), self.microseconds)
    }

    /// Origin Rust: pub fn get_nanoseconds(&self) -> i64
    ///     { self.sign * self.nanoseconds } (span.rs:1302-1303)
    /// Upstream doc (span.rs:1284-1288): the get_years doc with
    ///   nanosecond/nanoseconds substituted.
    pub exec fn get_nanoseconds(&self) -> (r: i64)
        requires
            sp_field_inv(self),
        ensures
            (r as int) == (sp_sign_val(self.sign)) * ((self.nanoseconds as int)),
    {
        sp_sign_mul_i64(sp_sign_of_ref(&self.sign), self.nanoseconds)
    }

    /// Origin Rust: pub(crate) fn get_years_unsigned(&self) -> u16
    ///     { self.years as u16 } (span.rs:2512-2514)
    /// Upstream block doc (span.rs:2493): the "ranged integer" impl
    /// block ("Crate internal APIs that operate on ranged integer
    /// types"); the unsigned getters serve the same internal family.
    /// The upstream cast is a bit-cast; the
    /// requires keeps the magnitude tier (field >= 0) under which it
    /// is the identity.
    pub(crate) exec fn get_years_unsigned(&self) -> (r: u16)
        requires
            sp_field_inv(self),
            self.years >= 0,
        ensures
            (r as int) == (self.years as int),
    {
        self.years as u16
    }

    /// Origin Rust: pub(crate) fn get_months_unsigned(&self) -> u32
    ///     { self.months as u32 } (span.rs:2517-2519)
    pub(crate) exec fn get_months_unsigned(&self) -> (r: u32)
        requires
            sp_field_inv(self),
            self.months >= 0,
        ensures
            (r as int) == (self.months as int),
    {
        self.months as u32
    }

    /// Origin Rust: pub(crate) fn get_weeks_unsigned(&self) -> u32
    ///     { self.weeks as u32 } (span.rs:2522-2524)
    pub(crate) exec fn get_weeks_unsigned(&self) -> (r: u32)
        requires
            sp_field_inv(self),
            self.weeks >= 0,
        ensures
            (r as int) == (self.weeks as int),
    {
        self.weeks as u32
    }

    /// Origin Rust: pub(crate) fn get_days_unsigned(&self) -> u32
    ///     { self.days as u32 } (span.rs:2527-2529)
    pub(crate) exec fn get_days_unsigned(&self) -> (r: u32)
        requires
            sp_field_inv(self),
            self.days >= 0,
        ensures
            (r as int) == (self.days as int),
    {
        self.days as u32
    }

    /// Origin Rust: pub(crate) fn get_hours_unsigned(&self) -> u32
    ///     { self.hours as u32 } (span.rs:2532-2534)
    pub(crate) exec fn get_hours_unsigned(&self) -> (r: u32)
        requires
            sp_field_inv(self),
            self.hours >= 0,
        ensures
            (r as int) == (self.hours as int),
    {
        self.hours as u32
    }

    /// Origin Rust: pub(crate) fn get_minutes_unsigned(&self) -> u64
    ///     { self.minutes as u64 } (span.rs:2537-2539)
    pub(crate) exec fn get_minutes_unsigned(&self) -> (r: u64)
        requires
            sp_field_inv(self),
            self.minutes >= 0,
        ensures
            (r as int) == (self.minutes as int),
    {
        self.minutes as u64
    }

    /// Origin Rust: pub(crate) fn get_seconds_unsigned(&self) -> u64
    ///     { self.seconds as u64 } (span.rs:2542-2544)
    pub(crate) exec fn get_seconds_unsigned(&self) -> (r: u64)
        requires
            sp_field_inv(self),
            self.seconds >= 0,
        ensures
            (r as int) == (self.seconds as int),
    {
        self.seconds as u64
    }

    /// Origin Rust: pub(crate) fn get_milliseconds_unsigned(&self) -> u64
    ///     { self.milliseconds as u64 } (span.rs:2547-2549)
    pub(crate) exec fn get_milliseconds_unsigned(&self) -> (r: u64)
        requires
            sp_field_inv(self),
            self.milliseconds >= 0,
        ensures
            (r as int) == (self.milliseconds as int),
    {
        self.milliseconds as u64
    }

    /// Origin Rust: pub(crate) fn get_microseconds_unsigned(&self) -> u64
    ///     { self.microseconds as u64 } (span.rs:2552-2554)
    pub(crate) exec fn get_microseconds_unsigned(&self) -> (r: u64)
        requires
            sp_field_inv(self),
            self.microseconds >= 0,
        ensures
            (r as int) == (self.microseconds as int),
    {
        self.microseconds as u64
    }

    /// Origin Rust: pub(crate) fn get_nanoseconds_unsigned(&self) -> u64
    ///     { self.nanoseconds as u64 } (span.rs:2557-2559)
    pub(crate) exec fn get_nanoseconds_unsigned(&self) -> (r: u64)
        requires
            sp_field_inv(self),
            self.nanoseconds >= 0,
        ensures
            (r as int) == (self.nanoseconds as int),
    {
        self.nanoseconds as u64
    }

    /// Origin Rust: fn get_sign(&self) -> Sign { self.sign }
    ///     (span.rs:2562-2564)
    pub(crate) exec fn get_sign(&self) -> (r: Sign)
        ensures
            ((r is Zero) <==> (self.sign is Zero))
                && ((r is Positive) <==> (self.sign is Positive))
                && ((r is Negative) <==> (self.sign is Negative)),
    {
        sp_sign_of_ref(&self.sign)
    }

    /// Origin Rust: fn get_unit(&self, unit: Unit) -> i64
    ///     (span.rs:2567-2586; the match dispatch `.into()`s each
    ///     getter
    ///     into i64)
    pub(crate) exec fn get_unit(&self, unit: Unit) -> (r: i64)
        requires
            sp_field_inv(self),
        ensures
            ((unit is Year) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.years as int))))
            && ((unit is Month) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.months as int))))
            && ((unit is Week) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.weeks as int))))
            && ((unit is Day) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.days as int))))
            && ((unit is Hour) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.hours as int))))
            && ((unit is Minute) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.minutes as int))))
            && ((unit is Second) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.seconds as int))))
            && ((unit is Millisecond) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.milliseconds as int))))
            && ((unit is Microsecond) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.microseconds as int))))
            && ((unit is Nanosecond) ==> ((r as int)
                == (sp_sign_val(self.sign)) * ((self.nanoseconds as int)))),
    {
        match unit {
            Unit::Year => self.get_years() as i64,
            Unit::Month => self.get_months() as i64,
            Unit::Week => self.get_weeks() as i64,
            Unit::Day => self.get_days() as i64,
            Unit::Hour => self.get_hours() as i64,
            Unit::Minute => self.get_minutes(),
            Unit::Second => self.get_seconds(),
            Unit::Millisecond => self.get_milliseconds(),
            Unit::Microsecond => self.get_microseconds(),
            Unit::Nanosecond => self.get_nanoseconds(),
        }
    }

    /// Origin Rust: fn try_unit(self, unit: Unit, value: i64)
    ///     -> Result<Span, Error> (span.rs:2496-2510)
    /// Upstream block doc (span.rs:2493): the crate-internal
    /// "ranged integer" impl block for Span.
    pub(crate) exec fn try_unit(&self, unit: Unit, value: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            ((unit is Year) ==> (match r {
                Option::Some(s) => sp_set_years_face(self, &s, value),
                Option::None => !(((-19_998int) <= (value as int))
                    && ((value as int) <= 19_998)),
            }))
            && ((unit is Month) ==> (match r {
                Option::Some(s) => sp_set_months_face(self, &s, value),
                Option::None => !(((-239_976int) <= (value as int))
                    && ((value as int) <= 239_976)),
            }))
            && ((unit is Week) ==> (match r {
                Option::Some(s) => sp_set_weeks_face(self, &s, value),
                Option::None => !(((-1_043_497int) <= (value as int))
                    && ((value as int) <= 1_043_497)),
            }))
            && ((unit is Day) ==> (match r {
                Option::Some(s) => sp_set_days_face(self, &s, value),
                Option::None => !(((-7_304_484int) <= (value as int))
                    && ((value as int) <= 7_304_484)),
            }))
            && ((unit is Hour) ==> (match r {
                Option::Some(s) => sp_set_hours_face(self, &s, value),
                Option::None => !(((-175_307_616int) <= (value as int))
                    && ((value as int) <= 175_307_616)),
            }))
            && ((unit is Minute) ==> (match r {
                Option::Some(s) => sp_set_minutes_face(self, &s, value),
                Option::None => !(((-10_518_456_960int) <= (value as int))
                    && ((value as int) <= 10_518_456_960)),
            }))
            && ((unit is Second) ==> (match r {
                Option::Some(s) => sp_set_seconds_face(self, &s, value),
                Option::None => !(((-631_107_417_600int) <= (value as int))
                    && ((value as int) <= 631_107_417_600)),
            }))
            && ((unit is Millisecond) ==> (match r {
                Option::Some(s) => sp_set_milliseconds_face(self, &s, value),
                Option::None => !(((-631_107_417_600_000int) <= (value as int))
                    && ((value as int) <= 631_107_417_600_000)),
            }))
            && ((unit is Microsecond) ==> (match r {
                Option::Some(s) => sp_set_microseconds_face(self, &s, value),
                Option::None => !(((-631_107_417_600_000_000int)
                    <= (value as int))
                    && ((value as int) <= 631_107_417_600_000_000)),
            }))
            && ((unit is Nanosecond) ==> (match r {
                Option::Some(s) => sp_set_nanoseconds_face(self, &s, value),
                Option::None => !(((-9_223_372_036_854_775_807int)
                    <= (value as int))
                    && ((value as int) <= 9_223_372_036_854_775_807)),
            })),
    {
        match unit {
            Unit::Year => self.try_years(value),
            Unit::Month => self.try_months(value),
            Unit::Week => self.try_weeks(value),
            Unit::Day => self.try_days(value),
            Unit::Hour => self.try_hours(value),
            Unit::Minute => self.try_minutes(value),
            Unit::Second => self.try_seconds(value),
            Unit::Millisecond => self.try_milliseconds(value),
            Unit::Microsecond => self.try_microseconds(value),
            Unit::Nanosecond => self.try_nanoseconds(value),
        }
    }

    /// Origin Rust: pub(crate) fn units(&self) -> UnitSet { self.units }
    ///     (span.rs:2905-2907)
    /// Upstream doc (span.rs:2903): "Returns the set of units on
    /// this `Span`."
    pub(crate) exec fn units(&self) -> (r: UnitSet)
        ensures
            r.year == self.units.year
                && r.month == self.units.month
                && r.week == self.units.week
                && r.day == self.units.day
                && r.hour == self.units.hour
                && r.minute == self.units.minute
                && r.second == self.units.second
                && r.millisecond == self.units.millisecond
                && r.microsecond == self.units.microsecond
                && r.nanosecond == self.units.nanosecond,
    {
        self.units
    }

    /// Origin Rust: pub(crate) fn largest_unit(&self) -> Unit {
    ///     self.units().largest_unit().unwrap_or(Unit::Nanosecond) }
    ///     (span.rs:2899-2903)
    /// Upstream doc (span.rs:2892-2898): "Returns the largest non-zero
    /// unit in this span. If all components of this span are zero,
    /// then `Unit::Nanosecond` is returned."
    pub(crate) exec fn largest_unit(&self) -> (r: Unit)
        ensures
            ((r is Year) <==> self.units.year)
                && ((r is Month) <==> (!self.units.year && self.units.month))
                && ((r is Week) <==> (!self.units.year && !self.units.month
                    && self.units.week))
                && ((r is Day) <==> (!self.units.year && !self.units.month
                    && !self.units.week && self.units.day))
                && ((r is Hour) <==> (!self.units.year && !self.units.month
                    && !self.units.week && !self.units.day && self.units.hour))
                && ((r is Minute) <==> (!self.units.year && !self.units.month
                    && !self.units.week && !self.units.day && !self.units.hour
                    && self.units.minute))
                && ((r is Second) <==> (!self.units.year && !self.units.month
                    && !self.units.week && !self.units.day && !self.units.hour
                    && !self.units.minute && self.units.second))
                && ((r is Millisecond) <==> (!self.units.year
                    && !self.units.month && !self.units.week && !self.units.day
                    && !self.units.hour && !self.units.minute
                    && !self.units.second && self.units.millisecond))
                && ((r is Microsecond) <==> (!self.units.year
                    && !self.units.month && !self.units.week && !self.units.day
                    && !self.units.hour && !self.units.minute
                    && !self.units.second && !self.units.millisecond
                    && self.units.microsecond))
                && ((r is Nanosecond) <==> (!self.units.year
                    && !self.units.month && !self.units.week && !self.units.day
                    && !self.units.hour && !self.units.minute
                    && !self.units.second && !self.units.millisecond
                    && !self.units.microsecond)),
    {
        let opt: Option<Unit> = UnitSet::largest_unit(self.units);
        match opt {
            Option::Some(u) => u,
            Option::None => Unit::Nanosecond,
        }
    }

    // ----------------------------------------------------------------
    // Sign predicates and abs/negate (span.rs:1308-1432).
    // ----------------------------------------------------------------

    /// Origin Rust: pub fn signum(self) -> i8 { self.sign.signum() }
    ///     (span.rs:1370-1372)
    /// Upstream doc (span.rs:1364-1368):
    ///   Returns the "sign number" or "signum" of this span.
    ///   The number returned is `-1` when this span is negative,
    ///   `0` when this span is zero and `1` when this span is positive.
    pub exec fn signum(&self) -> (r: i8)
        ensures
            ((self.sign is Zero) ==> (r == 0))
                && ((self.sign is Positive) ==> (r == 1))
                && ((self.sign is Negative) ==> (r == -1))
                && (((self.sign is Zero) || (self.sign is Positive)
                    || (self.sign is Negative))
                    ==> ((r == 0) || (r == 1) || (r == -1))),
    {
        Sign::signum(sp_sign_of_ref(&self.sign))
    }

    /// Origin Rust: pub fn is_positive(self) -> bool {
    ///     self.get_sign().is_positive() } (span.rs:1387-1389)
    /// Upstream doc (span.rs:1374-1385):
    ///   Returns true if and only if this span is positive.
    ///   This returns false when the span is zero or negative.
    pub exec fn is_positive(&self) -> (r: bool)
        ensures
            r <==> (self.sign is Positive),
    {
        Sign::is_positive(self.get_sign())
    }

    /// Origin Rust: pub fn is_negative(self) -> bool {
    ///     self.get_sign().is_negative() } (span.rs:1404-1406)
    /// Upstream doc (span.rs:1391-1401):
    ///   Returns true if and only if this span is negative.
    ///   This returns false when the span is zero or positive.
    pub exec fn is_negative(&self) -> (r: bool)
        ensures
            r <==> (self.sign is Negative),
    {
        Sign::is_negative(self.get_sign())
    }

    /// Origin Rust: pub fn is_zero(self) -> bool {
    ///     self.sign.is_zero() } (span.rs:1422-1424)
    /// Upstream doc (span.rs:1408-1420):
    ///   Returns true if and only if every field in this span is set
    ///   to `0`.
    /// SPEC-DOC note: the doc says "every field ... is set to 0" but
    /// the body tests only the span-global sign. The equivalence of
    /// the two statements is exactly the zero-sign consistency tier
    /// (sp_zero_sign_ok) the resign bookkeeping establishes and every
    /// public constructor maintains; the contract below states the
    /// sign instead. Under a struct-unconstrained value with a Zero
    /// sign and a non-zero field they diverge. Recorded in the J5
    /// notes (notes.md, under Suspects as a doc-precision remark, not
    /// a behavioral break).
    pub exec fn is_zero(&self) -> (r: bool)
        ensures
            r <==> (self.sign is Zero),
    {
        sp_sign_is_zero(&self.sign)
    }

    /// Origin Rust: pub fn abs(self) -> Span { if self.is_zero() {
    ///     return self; } Span { sign: Sign::Positive, ..self } }
    ///     (span.rs:1324-1330)
    /// Upstream doc (span.rs:1308-1316):
    ///   Returns a new span that is the absolute value of this span.
    ///   If this span is zero or positive, then this is a no-op.
    pub exec fn abs(&self) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
        ensures
            sp_field_inv(&r)
                && sp_zero_sign_ok(&r)
                && r.units.year == self.units.year
                && r.units.month == self.units.month
                && r.units.week == self.units.week
                && r.units.day == self.units.day
                && r.units.hour == self.units.hour
                && r.units.minute == self.units.minute
                && r.units.second == self.units.second
                && r.units.millisecond == self.units.millisecond
                && r.units.microsecond == self.units.microsecond
                && r.units.nanosecond == self.units.nanosecond
                && r.years == self.years
                && r.months == self.months
                && r.weeks == self.weeks
                && r.days == self.days
                && r.hours == self.hours
                && r.minutes == self.minutes
                && r.seconds == self.seconds
                && r.milliseconds == self.milliseconds
                && r.microseconds == self.microseconds
                && r.nanoseconds == self.nanoseconds
                && ((self.sign is Zero) ==> (r.sign is Zero))
                && (!(self.sign is Zero) ==> (r.sign is Positive)),
    {
        if self.is_zero() {
            self.sign_unchecked(sp_sign_of_ref(&self.sign))
        } else {
            self.sign_unchecked(Sign::Positive)
        }
    }

    /// Origin Rust: pub fn negate(self) -> Span {
    ///     Span { sign: -self.sign, ..self } } (span.rs:1361-1363)
    /// Upstream doc (span.rs:1319-1349):
    ///   Returns a new span that negates this span.
    ///   If this span is zero, then this is a no-op. If this span is
    ///   negative, then the returned span is positive. If this span is
    ///   positive, then the returned span is negative.
    /// (The `-self.sign` is the jcore Sign Neg impl, bounds.rs:1140-
    ///  1151 -- another J1-cut face, materialized as sp_sign_negated.)
    pub exec fn negate(&self) -> (r: Span)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
        ensures
            sp_field_inv(&r)
                && sp_zero_sign_ok(&r)
                && r.units.year == self.units.year
                && r.units.month == self.units.month
                && r.units.week == self.units.week
                && r.units.day == self.units.day
                && r.units.hour == self.units.hour
                && r.units.minute == self.units.minute
                && r.units.second == self.units.second
                && r.units.millisecond == self.units.millisecond
                && r.units.microsecond == self.units.microsecond
                && r.units.nanosecond == self.units.nanosecond
                && r.years == self.years
                && r.months == self.months
                && r.weeks == self.weeks
                && r.days == self.days
                && r.hours == self.hours
                && r.minutes == self.minutes
                && r.seconds == self.seconds
                && r.milliseconds == self.milliseconds
                && r.microseconds == self.microseconds
                && r.nanoseconds == self.nanoseconds
                && ((self.sign is Zero) ==> (r.sign is Zero))
                && ((self.sign is Positive) ==> (r.sign is Negative))
                && ((self.sign is Negative) ==> (r.sign is Positive)),
    {
        self.sign_unchecked(sp_sign_negated(&self.sign))
    }
}

/// Origin Rust: impl core::ops::Neg for Sign
///     fn neg(self) -> Sign (jcore bounds.rs:1140-1151: the match body
///     Positive => Negative, Zero => Zero, Negative => Positive).
/// Another J1-cut face re-materialized here (sp_sign_of_ref's
/// Copy-less-Sign note applies).
pub(crate) exec fn sp_sign_negated(s: &Sign) -> (r: Sign)
    ensures
        ((s is Zero) ==> (r is Zero))
            && ((s is Positive) ==> (r is Negative))
            && ((s is Negative) ==> (r is Positive)),
{
    match s {
        Sign::Zero => Sign::Zero,
        Sign::Positive => Sign::Negative,
        Sign::Negative => Sign::Positive,
    }
}

// ===========================================================================
// checked_mul (span.rs:1477-1564) and the Mul operators (span.rs:3031-3066).
// For each non-zero unit field, the multiple is breadth-checked against
// the unit's own Span bounds first (b::SpanX::check(rhs) for years
// through hours) and then the field product is machine-checked and
// range-checked (b::SpanX::checked_mul). The multiples for minutes
// through nanoseconds skip the breadth check (their unit ranges are
// i64-wide enough that the product check is the whole story).
// ===========================================================================

/// The nonneg magnitude of the multiple, in spec positions.
pub open spec fn sp_mul_abs(rhs0: i64) -> int {
    if rhs0 < 0 {
        0 - (rhs0 as int)
    } else {
        (rhs0 as int)
    }
}

/// The sign factor of the multiple (+1/0/-1), in spec positions.
pub open spec fn sp_mul_sign_int(rhs0: i64) -> int {
    if rhs0 > 0 {
        1
    } else if rhs0 < 0 {
        -1
    } else {
        0
    }
}

/// The exact checked_mul error condition (b::SpanMultiple::check /
/// b::SpanX::check / b::SpanX::checked_mul arms, span.rs:1505-1560):
/// the checked_abs failure of the i64::MIN multiple, or (unit by
/// unit) a too-wide multiple for years through hours, or a field
/// product out of its unit range. An all-zero span multiplied by
/// i64::MIN is in this set with NO field overflow -- the checked_mul
/// doc face ("If this would cause any individual field in this span
/// to overflow, then this returns an error", span.rs:1461-1462) and the
/// Mul operator doc face ("This panics on overflow", span.rs:3042,
/// :3055) do not cover it -- see the J5-1 suspects entry in the
/// notes.
pub open spec fn sp_mul_err_cond(s: &Span, rhs0: i64) -> bool {
    let r: int = sp_mul_abs(rhs0);
    (rhs0 == i64::MIN)
        || ((s.years != 0)
            && ((r > 19_998)
                || (((s.years as int) * r) > 19_998)
                || (((s.years as int) * r) < -19_998)))
        || ((s.months != 0)
            && ((r > 239_976)
                || (((s.months as int) * r) > 239_976)
                || (((s.months as int) * r) < -239_976)))
        || ((s.weeks != 0)
            && ((r > 1_043_497)
                || (((s.weeks as int) * r) > 1_043_497)
                || (((s.weeks as int) * r) < -1_043_497)))
        || ((s.days != 0)
            && ((r > 7_304_484)
                || (((s.days as int) * r) > 7_304_484)
                || (((s.days as int) * r) < -7_304_484)))
        || ((s.hours != 0)
            && ((r > 175_307_616)
                || (((s.hours as int) * r) > 175_307_616)
                || (((s.hours as int) * r) < -175_307_616)))
        || ((s.minutes != 0)
            && ((((s.minutes as int) * r) > 10_518_456_960)
                || (((s.minutes as int) * r) < -10_518_456_960)))
        || ((s.seconds != 0)
            && ((((s.seconds as int) * r) > 631_107_417_600)
                || (((s.seconds as int) * r) < -631_107_417_600)))
        || ((s.milliseconds != 0)
            && ((((s.milliseconds as int) * r) > 631_107_417_600_000)
                || (((s.milliseconds as int) * r) < -631_107_417_600_000)))
        || ((s.microseconds != 0)
            && ((((s.microseconds as int) * r) > 631_107_417_600_000_000)
                || (((s.microseconds as int) * r) < -631_107_417_600_000_000)))
        || ((s.nanoseconds != 0)
            && ((((s.nanoseconds as int) * r) > 9_223_372_036_854_775_807)
                || (((s.nanoseconds as int) * r) < -9_223_372_036_854_775_807)))
}

/// The checked_mul success face: every unit field scaled by the
/// multiple's magnitude (|rhs0|), the span-global sign equal to the
/// sign product, and the zero-bookkeeping flags preserved (a non-zero
/// field stays non-zero and a zero field stays zero -- multiplication
/// by a non-zero multiple, and of any field by zero, both preserve
/// zero-ness; the rhs0 == 0 arm returns the all-zero span, whose
/// flags are all clear).
pub open spec fn sp_mul_face(s: &Span, s2: &Span, rhs0: i64) -> bool {
    let r: int = sp_mul_abs(rhs0);
    sp_field_inv(s2)
        && sp_zero_sign_ok(s2)
        && (((s2.years as int) == ((s.years as int) * r))
            && ((s2.months as int) == ((s.months as int) * r))
            && ((s2.weeks as int) == ((s.weeks as int) * r))
            && ((s2.days as int) == ((s.days as int) * r))
            && ((s2.hours as int) == ((s.hours as int) * r))
            && ((s2.minutes as int) == ((s.minutes as int) * r))
            && ((s2.seconds as int) == ((s.seconds as int) * r))
            && ((s2.milliseconds as int) == ((s.milliseconds as int) * r))
            && ((s2.microseconds as int) == ((s.microseconds as int) * r))
            && ((s2.nanoseconds as int) == ((s.nanoseconds as int) * r)))
        && (((s2.sign is Zero) <==> (((sp_sign_val(s.sign))
            * ((sp_mul_sign_int(rhs0)) )) == 0))
            && ((s2.sign is Positive) <==> (((sp_sign_val(s.sign))
            * ((sp_mul_sign_int(rhs0)) )) > 0))
            && ((s2.sign is Negative) <==> (((sp_sign_val(s.sign))
            * ((sp_mul_sign_int(rhs0)) )) < 0)))
        && ((rhs0 == 0)
            ==> (!s2.units.year && !s2.units.month && !s2.units.week
                && !s2.units.day && !s2.units.hour && !s2.units.minute
                && !s2.units.second && !s2.units.millisecond
                && !s2.units.microsecond && !s2.units.nanosecond))
        && ((rhs0 != 0)
            ==> (s2.units.year == s.units.year
                && s2.units.month == s.units.month
                && s2.units.week == s.units.week
                && s2.units.day == s.units.day
                && s2.units.hour == s.units.hour
                && s2.units.minute == s.units.minute
                && s2.units.second == s.units.second
                && s2.units.millisecond == s.units.millisecond
                && s2.units.microsecond == s.units.microsecond
                && s2.units.nanosecond == s.units.nanosecond))
}

impl Span {
    /// Origin Rust: pub fn checked_mul(mut self, rhs: i64)
    ///     -> Result<Span, Error> (span.rs:1499-1564)
    /// Upstream doc (span.rs:1459-1462):
    ///   Multiplies each field in this span by a given integer.
    ///   If this would cause any individual field in this span to
    ///   overflow, then this returns an error.
    /// Upstream safety comments (span.rs:1506-1507):
    ///   "This can only fail when `rhs == i64::MIN`, which is out of
    ///   bounds for all possible span units (including nanoseconds)."
    /// -- the checked_abs arm (the checked_neg spelling borrows the J4b
    ///  pitfall-12 precedent; `checked_abs` itself has no builtin spec
    ///  in this build).
    /// (span.rs:1506-1517): the per-unit breadth checks for years
    /// through hours ("the allowable values for our multiple depend on
    /// what we're actually going to multiply with it") -- reflected
    /// row by row in sp_mul_err_cond.
    /// (span.rs:1556-1563): "We don't need to update `self.units`
    /// here since it shouldn't change. The only way it could is if a
    /// unit goes from zero to non-zero (which can't happen, because
    /// multiplication by zero is always zero), or if a unit goes from
    /// non-zero to zero. That also can't happen because we handle the
    /// case of the factor being zero specially above, and it returns
    /// a `Span` will all units zero correctly." -- the flags clause of
    /// sp_mul_face, discharged through the mul lemma family.
    pub exec fn checked_mul(&self, rhs0: i64) -> (r: Option<Span>)
        requires
            sp_field_inv(self),
            sp_zero_sign_ok(self),
            sp_flags_ok(self),
        ensures
            match r {
                Option::Some(s2) => sp_mul_face(self, &s2, rhs0)
                    && !sp_mul_err_cond(self, rhs0),
                Option::None => sp_mul_err_cond(self, rhs0),
            },
    {
        if rhs0 == 0 {
            let z: Span = Span::new();
            proof {
                assert(sp_mul_sign_int(0) == 0);
                lemma_mul_by_zero_is_zero(sp_sign_val(self.sign));
                assert(sp_mul_abs(0) == 0);
                lemma_mul_by_zero_is_zero(((self.years as int)));
                lemma_mul_by_zero_is_zero(((self.months as int)));
                lemma_mul_by_zero_is_zero(((self.weeks as int)));
                lemma_mul_by_zero_is_zero(((self.days as int)));
                lemma_mul_by_zero_is_zero(((self.hours as int)));
                lemma_mul_by_zero_is_zero(((self.minutes as int)));
                lemma_mul_by_zero_is_zero(((self.seconds as int)));
                lemma_mul_by_zero_is_zero(((self.milliseconds as int)));
                lemma_mul_by_zero_is_zero(((self.microseconds as int)));
                lemma_mul_by_zero_is_zero(((self.nanoseconds as int)));
                assert(sp_mul_sign_int(0) == 0);
            }
            assert(!sp_mul_err_cond(self, 0));
            assert(sp_mul_face(self, &z, 0));
            return Option::Some(z);
        }
        if rhs0 == 1 {
            let z: Span = self.sign_unchecked(sp_sign_of_ref(&self.sign));
            proof {
                assert(sp_mul_abs(1) == 1);
                assert(sp_mul_sign_int(1) == 1);
                lemma_mul_basics(((self.years as int)));
                lemma_mul_basics(((self.months as int)));
                lemma_mul_basics(((self.weeks as int)));
                lemma_mul_basics(((self.days as int)));
                lemma_mul_basics(((self.hours as int)));
                lemma_mul_basics(((self.minutes as int)));
                lemma_mul_basics(((self.seconds as int)));
                lemma_mul_basics(((self.milliseconds as int)));
                lemma_mul_basics(((self.microseconds as int)));
                lemma_mul_basics(((self.nanoseconds as int)));
            }
            return Option::Some(z);
        }
        let new_sign: Sign = sp_sign_mul_sign(
            sp_sign_of_ref(&self.sign),
            sp_sign_from_i64(rhs0),
        );
        // rhs.checked_abs().ok_or_else(b::SpanMultiple::error)
        // (span.rs:1508), branch-spelled (upstream safety
        // comment, span.rs:1506-1507: "This can only fail when
        // `rhs == i64::MIN`, which is out of bounds for all possible
        // span units (including nanoseconds).").
        if rhs0 == i64::MIN {
            return Option::None;
        }
        let ar: i64 = if rhs0 < 0 {
            0 - rhs0
        } else {
            rhs0
        };
        let mut s2: Span = self.sign_unchecked(new_sign);
        if s2.years != 0 {
            match crate::bounds::const_check::i16(-19_998, 19_998, ar) {
                Option::None => return Option::None,
                Option::Some(y) => {
                    match crate::bounds::checked_mul::i16(
                        -19_998,
                        19_998,
                        s2.years,
                        y,
                    ) {
                        Option::None => return Option::None,
                        Option::Some(p) => s2.years = p,
                    }
                }
            }
        }
        if s2.months != 0 {
            match crate::bounds::const_check::i32(-239_976, 239_976, ar) {
                Option::None => return Option::None,
                Option::Some(m) => {
                    match crate::bounds::checked_mul::i32(
                        -239_976,
                        239_976,
                        s2.months,
                        m,
                    ) {
                        Option::None => return Option::None,
                        Option::Some(p) => s2.months = p,
                    }
                }
            }
        }
        if s2.weeks != 0 {
            match crate::bounds::const_check::i32(-1_043_497, 1_043_497, ar) {
                Option::None => return Option::None,
                Option::Some(w) => {
                    match crate::bounds::checked_mul::i32(
                        -1_043_497,
                        1_043_497,
                        s2.weeks,
                        w,
                    ) {
                        Option::None => return Option::None,
                        Option::Some(p) => s2.weeks = p,
                    }
                }
            }
        }
        if s2.days != 0 {
            match crate::bounds::const_check::i32(-7_304_484, 7_304_484, ar) {
                Option::None => return Option::None,
                Option::Some(d) => {
                    match crate::bounds::checked_mul::i32(
                        -7_304_484,
                        7_304_484,
                        s2.days,
                        d,
                    ) {
                        Option::None => return Option::None,
                        Option::Some(p) => s2.days = p,
                    }
                }
            }
        }
        if s2.hours != 0 {
            match crate::bounds::const_check::i32(
                -175_307_616,
                175_307_616,
                ar,
            ) {
                Option::None => return Option::None,
                Option::Some(h) => {
                    match crate::bounds::checked_mul::i32(
                        -175_307_616,
                        175_307_616,
                        s2.hours,
                        h,
                    ) {
                        Option::None => return Option::None,
                        Option::Some(p) => s2.hours = p,
                    }
                }
            }
        }
        if s2.minutes != 0 {
            match crate::bounds::checked_mul::i64(
                -10_518_456_960,
                10_518_456_960,
                s2.minutes,
                ar,
            ) {
                Option::None => return Option::None,
                Option::Some(p) => s2.minutes = p,
            }
        }
        if s2.seconds != 0 {
            match crate::bounds::checked_mul::i64(
                -631_107_417_600,
                631_107_417_600,
                s2.seconds,
                ar,
            ) {
                Option::None => return Option::None,
                Option::Some(p) => s2.seconds = p,
            }
        }
        if s2.milliseconds != 0 {
            match crate::bounds::checked_mul::i64(
                -631_107_417_600_000,
                631_107_417_600_000,
                s2.milliseconds,
                ar,
            ) {
                Option::None => return Option::None,
                Option::Some(p) => s2.milliseconds = p,
            }
        }
        if s2.microseconds != 0 {
            match crate::bounds::checked_mul::i64(
                -631_107_417_600_000_000,
                631_107_417_600_000_000,
                s2.microseconds,
                ar,
            ) {
                Option::None => return Option::None,
                Option::Some(p) => s2.microseconds = p,
            }
        }
        if s2.nanoseconds != 0 {
            match crate::bounds::checked_mul::i64(
                -9_223_372_036_854_775_807,
                9_223_372_036_854_775_807,
                s2.nanoseconds,
                ar,
            ) {
                Option::None => return Option::None,
                Option::Some(p) => s2.nanoseconds = p,
            }
        }
        // The general-path exit obligations: field products by a
        // non-zero multiple stay non-zero (the upstream span.rs:1556-
        // 1563 comment), units killed by a zero multiple return early
        // above, and the zero-sign tier follows from sp_zero_sign_ok(
        // self) plus the 0-field product facts.
        proof {
            assert((sp_mul_abs(rhs0)) >= 1);
            lemma_mul_basics((sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.years as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.months as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.weeks as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.days as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.hours as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.minutes as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(((self.seconds as int)), (sp_mul_abs(rhs0)));
            lemma_mul_nonzero(
                ((self.milliseconds as int)),
                (sp_mul_abs(rhs0)),
            );
            lemma_mul_nonzero(
                ((self.microseconds as int)),
                (sp_mul_abs(rhs0)),
            );
            lemma_mul_nonzero(
                ((self.nanoseconds as int)),
                (sp_mul_abs(rhs0)),
            );
            lemma_mul_nonzero(
                (sp_sign_val(self.sign)),
                (sp_mul_sign_int(rhs0)),
            );
        }
        assert(sp_field_inv(&s2));
        assert(sp_zero_sign_ok(&s2));
        assert((s2.years as int) == ((self.years as int) * (sp_mul_abs(rhs0))));
        assert((s2.months as int) == ((self.months as int) * (sp_mul_abs(rhs0))));
        assert((s2.weeks as int) == ((self.weeks as int) * (sp_mul_abs(rhs0))));
        assert((s2.days as int) == ((self.days as int) * (sp_mul_abs(rhs0))));
        assert((s2.hours as int) == ((self.hours as int) * (sp_mul_abs(rhs0))));
        assert((s2.minutes as int) == ((self.minutes as int) * (sp_mul_abs(rhs0))));
        assert((s2.seconds as int) == ((self.seconds as int) * (sp_mul_abs(rhs0))));
        assert((s2.milliseconds as int) == ((self.milliseconds as int) * (sp_mul_abs(rhs0))));
        assert((s2.microseconds as int) == ((self.microseconds as int) * (sp_mul_abs(rhs0))));
        assert((s2.nanoseconds as int) == ((self.nanoseconds as int) * (sp_mul_abs(rhs0))));
        assert(((s2.sign is Zero) <==>
            (((sp_sign_val(self.sign)) * ((sp_mul_sign_int(rhs0)))) == 0)));
        assert(((s2.sign is Positive) <==>
            (((sp_sign_val(self.sign)) * ((sp_mul_sign_int(rhs0)))) > 0)));
        assert(((s2.sign is Negative) <==>
            (((sp_sign_val(self.sign)) * ((sp_mul_sign_int(rhs0)))) < 0)));
        assert(((rhs0 == 0) ==> (!s2.units.year
            && !s2.units.month && !s2.units.week && !s2.units.day
            && !s2.units.hour && !s2.units.minute && !s2.units.second
            && !s2.units.millisecond && !s2.units.microsecond
            && !s2.units.nanosecond)));
        assert(((rhs0 != 0) ==> (s2.units.year == self.units.year
            && s2.units.month == self.units.month
            && s2.units.week == self.units.week
            && s2.units.day == self.units.day
            && s2.units.hour == self.units.hour
            && s2.units.minute == self.units.minute
            && s2.units.second == self.units.second
            && s2.units.millisecond == self.units.millisecond
            && s2.units.microsecond == self.units.microsecond
            && s2.units.nanosecond == self.units.nanosecond)));
        assert(sp_mul_face(self, &s2, rhs0));
        assert(!sp_mul_err_cond(self, rhs0));
        Option::Some(s2)
    }
}

/// Origin Rust: impl core::ops::Mul<i64> for Span
///     fn mul(self, rhs: i64) -> Span (span.rs:3043-3053, body
///     `self.checked_mul(rhs).expect("multiplying `Span` by a scalar
///     overflowed")`)
/// Upstream doc (span.rs:3031-3042):
///   This multiplies each unit in a span by an integer.
///   This panics on overflow. For checked arithmetic, use
///   [`Span::checked_mul`].
/// (# Panics head faithful: the .expect site is the above text; the
///  arm below is dead under the sp_mul_err_cond excluder requires.)
pub exec fn sp_ops_mul(s: &Span, rhs0: i64) -> (r: Span)
    requires
        sp_field_inv(s),
        sp_zero_sign_ok(s),
        sp_flags_ok(s),
        !sp_mul_err_cond(s, rhs0),
    ensures
        sp_mul_face(s, &r, rhs0),
{
    let t: Option<Span> = s.checked_mul(rhs0);
    match t {
        Option::Some(x) => x,
        Option::None => {
            // The None face of checked_mul is exactly the excluder.
            assert(false);
            Span::new()
        }
    }
}

/// Origin Rust: impl core::ops::Mul<Span> for i64
///     fn mul(self, rhs: Span) -> Span (span.rs:3056-3066, body
///     `rhs.checked_mul(self).expect("multiplying `Span` by a scalar
///     overflowed")`, the commutativity delegation)
/// Upstream doc (span.rs:3044-3055):
///   This multiplies each unit in a span by an integer.
///   This panics on overflow. For checked arithmetic, use
///   [`Span::checked_mul`].
pub exec fn sp_ops_mul_i64_lhs(m: i64, s: &Span) -> (r: Span)
    requires
        sp_field_inv(s),
        sp_zero_sign_ok(s),
        sp_flags_ok(s),
        !sp_mul_err_cond(s, m),
    ensures
        sp_mul_face(s, &r, m),
{
    sp_ops_mul(s, m)
}

// ===========================================================================
// J5-1 witness (the checked_mul / Mul-operator doc face).
//
// SPEC-DOC MISMATCH candidate J5-1 (suspects list, notes.md; upstream
// issue number not yet available): the upstream checked_mul doc says
// "If this would cause any
// individual field in this span to overflow, then this returns an
// error." (span.rs:1461-1462) and the Mul<i64> operator docs say "This
// panics on overflow." (span.rs:3042, :3055)
// Both statements fail to cover the i64::MIN
// multiple of an all-zero span: no field is non-zero, so no field can
// overflow (0 * i64::MIN == 0), yet checked_mul errors at the
// checked_abs arm (span.rs:1508) and both operators unwrap that
// error into the panic "multiplying `Span` by a scalar overflowed".
// The witness below is verified evidence of the None arm; the
// operator panic itself is runtime business for the mainline (a
// zero-second span * i64::MIN panics at span.rs:3049's expect).
// ===========================================================================

/// Verified witness: Span::new().checked_mul(i64::MIN) returns None
/// even though every field of the zero span is 0 (no field overflows
/// under the doc's own condition).
pub exec fn sp_audit_mul_zero_span_witness() -> (r: Option<Span>)
    ensures
        r is None,
{
    let z: Span = Span::new();
    z.checked_mul(i64::MIN)
}


// ===========================================================================
// The signed-duration meeting point (upstream signed_duration.rs:992-1009,
// NOT span.rs -- the batch instruction's "as_nanos64" pointer resolves to
// the SignedDuration impl; this is the J4b-designated
// Timestamp/SignedDuration reunion face).
//
// SD64_MIN/MAX are the two constants of the upstream body:
//     const MIN: SignedDuration = SignedDuration::from_nanos(i64::MIN);
//     const MAX: SignedDuration = SignedDuration::from_nanos(i64::MAX);
// (signed_duration.rs:1000-1001), i.e. MIN = {secs: -9_223_372_036,
// nanos: -854_775_808} and MAX = {secs: 9_223_372_036,
// nanos: 854_775_807} (the trunc-division decompositions of the two
// i64 extremes at NANOS_PER_SEC = 1_000_000_000).
//
// The upstream comparison `MIN <= *self && *self <= MAX` is the
// field-lexicographic derived-Ord comparison (secs first, then nanos),
// which is exactly the total-nanoseconds order on canonical
// (sd_inv) values -- the "Ord face" J4b deferred from its own panel.
// ===========================================================================

pub const SD64_MIN_SECS: i64 = -9_223_372_036;
pub const SD64_MIN_NANOS: i32 = -854_775_808;
pub const SD64_MAX_SECS: i64 = 9_223_372_036;
pub const SD64_MAX_NANOS: i32 = 854_775_807;

/// Ledger: the two from_nanos-derived boundary constants decompose
/// the i64 nanosecond extremes exactly (the trunc-division identities;
/// the uniqueness of a trunc decomposition at divisor 1e9 with
/// |nanos| < 1e9 is the standard div_mod-family argument, not
/// re-proved here -- the identities below carry the value parity).
proof fn sd64_consts_panel() {
    assert((-9223372036854775808int)
        == ((-9223372036int) * 1_000_000_000int) + (-854775808int));
    assert((9223372036854775807int)
        == ((9223372036int) * 1_000_000_000int) + 854775807int);
    assert((-854775808int) > (-1_000_000_000int));
    assert((-854775808int) < 0int);
    assert((854775807int) < 1_000_000_000int);
    assert((854775807int) >= 0int);
}

/// The lexicographic range test of the upstream body, in spec terms
/// (the derived-Ord field comparison; equivalent to the total-
/// nanoseconds range test on canonical values -- the lemma below).
pub open spec fn sd64_lex_in_range(d: &SignedDuration) -> bool {
    (((((d.secs as int)) > ((SD64_MIN_SECS as int)))
        || (((d.secs as int)) == ((SD64_MIN_SECS as int))
            && ((d.nanos as int) >= ((SD64_MIN_NANOS as int)))))
        && ((((d.secs as int)) < ((SD64_MAX_SECS as int)))
            || (((d.secs as int)) == ((SD64_MAX_SECS as int))
                && ((d.nanos as int) <= ((SD64_MAX_NANOS as int))))))
}

/// The lex <-> total-nanoseconds equivalence on canonical values
/// (the J4b-deferred "derive semantics" note for this face;
/// requires sd_inv's sign agreement -- without it, a non-canonical
/// {secs: -9_223_372_037, nanos: +999_999_999} would pass the total
/// range test but fail the lex test).
proof fn sd64_lex_equiv(d: &SignedDuration)
    requires
        sd_inv(d),
    ensures
        sd64_lex_in_range(d) <==> (((-(9223372036854775808int))
            <= (sd_total_nanos(d)))
            && ((sd_total_nanos(d)) <= 9223372036854775807int)),
{
    let secs: int = d.secs as int;
    let nanos: int = d.nanos as int;
    // total = secs * 1_000_000_000 + nanos (sd_total_nanos's body)
    assert((sd_total_nanos(d))
        == (secs * 1_000_000_000int) + nanos);
    // Ground products spelling the two i64 extremes on the 1e9 grid.
    assert(((SD64_MIN_SECS as int) * 1_000_000_000int)
        == (-9223372036000000000int));
    assert(((SD64_MAX_SECS as int) * 1_000_000_000int)
        == 9223372036000000000int);
    assert(((((SD64_MIN_SECS as int) - 1) * 1_000_000_000int))
        == (-9223372037000000000int));
    assert(((((SD64_MAX_SECS as int) + 1) * 1_000_000_000int))
        == 9223372037000000000int);
    // Out-of-range, low side: secs < MIN_SECS means (with the
    // sign-agreement nanos <= 0) the total lies strictly below
    // i64::MIN.
    if secs < (SD64_MIN_SECS as int) {
        assert(nanos <= 0);
        assert((secs * 1_000_000_000int) + nanos
            <= (((SD64_MIN_SECS as int) - 1) * 1_000_000_000int));
        assert((secs * 1_000_000_000int) + nanos
            < (-(9223372036854775808int)));
    }
    // In-range, low edge: secs == MIN_SECS and the total sits below
    // i64::MIN exactly when nanos < MIN_NANOS.
    if secs == (SD64_MIN_SECS as int) {
        assert(nanos <= 0);
        assert(((sd_total_nanos(d))
            < (-(9223372036854775808int))) <==> (nanos < (SD64_MIN_NANOS as int)));
    }
    // Strictly inside on the low side (MIN_SECS < secs < MAX_SECS):
    // the total is inside [i64::MIN, i64::MAX] because every
    // intermediate field magnitude is dominated by the extremes.
    if ((SD64_MIN_SECS as int) < secs) && (secs < (SD64_MAX_SECS as int)) {
        assert((-999_999_999int) <= nanos && nanos <= 999_999_999int);
        assert((secs * 1_000_000_000int) + nanos
            >= (((SD64_MIN_SECS as int) + 1) * 1_000_000_000int)
                + (-999_999_999int));
        assert((secs * 1_000_000_000int) + nanos
            <= (((SD64_MAX_SECS as int) - 1) * 1_000_000_000int)
                + 999_999_999int);
        assert(((SD64_MIN_SECS as int) + 1) * 1_000_000_000int
            - 999_999_999int > (-(9223372036854775808int)));
        assert(((SD64_MAX_SECS as int) - 1) * 1_000_000_000int
            + 999_999_999int < 9223372036854775807int);
        assert((-(9223372036854775808int))
            <= (sd_total_nanos(d)));
        assert((sd_total_nanos(d)) <= 9223372036854775807int);
    }
    // Out-of-range, high side: secs > MAX_SECS with nanos >= 0.
    if secs > (SD64_MAX_SECS as int) {
        assert(nanos >= 0);
        assert((secs * 1_000_000_000int) + nanos
            >= (((SD64_MAX_SECS as int) + 1) * 1_000_000_000int));
        assert((secs * 1_000_000_000int) + nanos
            > 9223372036854775807int);
    }
    // In-range, high edge: secs == MAX_SECS.
    if secs == (SD64_MAX_SECS as int) {
        assert(nanos >= 0);
        assert(((sd_total_nanos(d))
            > 9223372036854775807int) <==> (nanos > (SD64_MAX_NANOS as int)));
    }
}

/// Origin Rust: pub(crate) const fn as_nanos64(&self) -> Option<i64>
///     (signed_duration.rs:997-1009)
/// Upstream doc (signed_duration.rs:997-998):
///   Like `SignedDuration::as_nanos()`, but only returns a result when
///   it fits into a 64-bit integer.
/// Upstream body (verbatim, signed_duration.rs:1002-1008):
///     if MIN <= *self && *self <= MAX {
///         let nanos = self.secs * (NANOS_PER_SEC as i64);
///         Some(nanos + (self.nanos as i64))
///     } else {
///         None
///     }
/// Overflow audit (the upstream body carries no safety comment; both
/// machine ops are dischargeable inside the lex range): the lex
/// range pins |secs| <= 9_223_372_036, so the secs product stays
/// inside i64, and the equal-seconds edge cases pin the nanos head
/// room to exactly the i64 remainder.
pub exec fn sp_sd_as_nanos64(d: &SignedDuration) -> (r: Option<i64>)
    requires
        sd_inv(d),
    ensures
        match r {
            Option::Some(v) => ((sd_total_nanos(d)) == (v as int))
                && (((-(9223372036854775808int))) <= (sd_total_nanos(d)))
                && ((sd_total_nanos(d)) <= 9223372036854775807int),
            Option::None => (((sd_total_nanos(d))
                < (-(9223372036854775808int))))
                || ((sd_total_nanos(d)) > 9223372036854775807int),
        },
{
    let ok: bool = ((d.secs > SD64_MIN_SECS)
        || ((d.secs == SD64_MIN_SECS) && (d.nanos >= SD64_MIN_NANOS)))
        && ((d.secs < SD64_MAX_SECS)
            || ((d.secs == SD64_MAX_SECS) && (d.nanos <= SD64_MAX_NANOS)));
    proof {
        sd64_lex_equiv(d);
        assert(ok <==> sd64_lex_in_range(d));
    }
    if ok {
        let nanos: i64 = d.secs * 1_000_000_000;
        let total: i64 = nanos + (d.nanos as i64);
        Option::Some(total)
    } else {
        Option::None
    }
}

} // verus!
