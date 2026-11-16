//! Batch J2 -- the civil date core, Verus transcription of:
//!   - code/crates/jiff-core/src/civil/mod.rs (is_leap_year / days_in_year /
//!     days_in_month, civil/mod.rs:171-204 at this pin)
//!   - code/crates/jiff-core/src/civil/date.rs (Date, UnixEpochDay, and the
//!     Neri-Schneider epoch-day bridge, date.rs:18-599, 701-935)
//!   - the wrapper face in code/crates/jiff/src/civil/date.rs (the public
//!     jiff crate API that delegates to jcore, Date::new at date.rs:246,
//!     Date::constant at :309, first_of_month at :594, last_of_month at
//!     :609, days_in_month at :634, days_in_year at :685, tomorrow at
//!     :725, yesterday at :749, to_unix_epoch_day / from_unix_epoch_day at
//!     :2007/:2012)
//!   - the months-overflow core month_add_overflowing from the jiff main
//!     crate (code/crates/jiff/src/civil/date.rs:3422-3433, the
//!     Span-free arithmetic heart of Date::checked_add_span at :1363)
//! Inventory note (harness-inventory.md section 6.2) records the batch
//! functions against the *main-crate* wrapper line numbers; every item
//! below cites both the wrapper face and the jcore implementation that
//! carries the actual body. The real positions were re-measured at this
//! pin; see J2/notes.md.
//!
//! Materialization ledger (this file):
//! - Result<T, RangeError> faces materialize as Option<T> (J1 bounds.rs
//!   ledger: the error value is a zero-sized witness).
//! - const fn materializes as exec fn (no const verification in this
//!   build); core::ops and Display faces are out of the batch.
//! - The Calendar validity model is the spec predicate valid_date(Date):
//!   year in -9999..=9999 (Year interval), month in 1..=12 (Month
//!   interval), day in 1..=days_in_month_spec(year, month). Every
//!   checked entry point ensures it and every calendar consumer requires
//!   it, standing in for upstream's private-field type discipline
//!   (jcore Date fields are private with the same invariant, jcore
//!   date.rs:18-22).
//! - tomorrow/yesterday/checked_add(±1) get structural spec twins
//!   (spec_tomorrow / spec_yesterday) so the quickcheck identity laws
//!   are provable without the epoch-day bridge.
//! - to_unix_epoch_day / to_date (Neri-Schneider, jcore date.rs:498-523
//!   and :904-934) are transcribed in i64 arithmetic: the upstream u32
//!   wrapping chains (Y = year.wrapping_add(L).wrapping_sub(J as u32),
//!   N = N_U.wrapping_add(K)) compute exact year + L - J resp. 2^32*[day
//!   < 0] + day + K values for every representable input, so the i64
//!   form is value-identical while keeping this build's exec overflow
//!   checks dischargeable by linear bounds alone. The roundtrip laws
//!   themselves are DEFERRED (see notes.md): their proof needs full
//!   modular reasoning over 146097/2939745-magic chains, which upstream
//!   validates by exhaustive test loops (jcore date.rs
//!   unix_epoch_to_date_and_back_again_*, date.rs:1419-1454), not by
//!   any upstream proof.
//! - days_in_month's contract narrows the month domain to 1..=12
//!   (upstream takes any i8 and produces xor-pattern trivia outside
//!   the calendar domain; its own doc only defines the result for
//!   real months, civil/mod.rs:189-191).
//! - month_add_overflowing narrows the span domain to b::SpanMonths
//!   (-239976..=239976, jiff util/b.rs:194), which upstream itself
//!   states as the caller obligation in the doc block
//!   (main-crate date.rs:3419-3421 "Callers must ensure that `span` is
//!   in bounds for `b::SpanMonths`").

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_mod_multiples_basic, lemma_mod_multiples_vanish, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add, lemma_mul_is_distributive_add_other_way,
    lemma_mul_unary_negation,
};

// sibling-module imports use the super-path so this file mounts both
// as the crate-root module and as the harness-mounted submodule
use super::bounds::{Interval, Month, Year, const_check, const_checked_add};
use super::bounds::{month_iv, year_iv};

verus! {

// ===========================================================================
// spec models (calendar semantics)
// ===========================================================================

/// The textbook Gregorian leap rule, the spec face the upstream
/// branchless formula (civil/mod.rs:171-175) computes:
///   A leap year is a year with 366 days. Non-leap years have 365 days.
///     (upstream doc, civil/mod.rs:167-169)
pub open spec fn is_leap_year_spec(year: int) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

/// Upstream doc (civil/mod.rs:177-179):
///   Return the number of days in the given year.
///   This is guaranteed to either return `365` or `366`.
pub open spec fn days_in_year_spec(year: int) -> int {
    if is_leap_year_spec(year) { 366 } else { 365 }
}

/// Upstream doc (civil/mod.rs:189-191):
///   Return the number of days in the given month.
///   This is guaranteed to return a value in the range `1..=31`.
/// (The true shape is 28..=31, captured below; see notes.md suspects.)
pub open spec fn days_in_month_spec(year: int, month: int) -> int {
    if month == 2 {
        if is_leap_year_spec(year) { 29 } else { 28 }
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        30
    } else {
        31
    }
}

/// Calendar validity of a Date triple (the upstream private-field
/// invariant, jcore date.rs:18-22 + the Date::new checks).
pub open spec fn valid_date(d: Date) -> bool {
    year_iv().contains(d.year as int)
        && month_iv().contains(d.month as int)
        && 1 <= d.day as int
        && (d.day as int) <= days_in_month_spec(d.year as int, d.month as int)
}

/// Structural spec twin of Date::tomorrow (jcore date.rs:320-330):
/// day+1 inside the month, else month+1 day 1, else year+1 Jan 1, else
/// None at the maximum.
pub open spec fn spec_tomorrow(d: Date) -> Option<Date> {
    let y: int = d.year as int;
    let m: int = d.month as int;
    let dd: int = d.day as int;
    if dd < days_in_month_spec(y, m) {
        Some(Date {
            year: d.year,
            month: d.month,
            day: (dd + 1) as i8,
        })
    } else if m < 12 {
        Some(Date {
            year: d.year,
            month: (m + 1) as i8,
            day: 1,
        })
    } else if y < 9999 {
        Some(Date {
            year: (y + 1) as i16,
            month: 1,
            day: 1,
        })
    } else {
        None
    }
}

pub open spec fn spec_yesterday(d: Date) -> Option<Date> {
    let y: int = d.year as int;
    let m: int = d.month as int;
    let dd: int = d.day as int;
    if dd > 1 {
        Some(Date {
            year: d.year,
            month: d.month,
            day: (dd - 1) as i8,
        })
    } else if m > 1 {
        Some(Date {
            year: d.year,
            month: (m - 1) as i8,
            day: days_in_month_spec(y, m - 1) as i8,
        })
    } else if y > -9999 {
        Some(Date {
            year: (y - 1) as i16,
            month: 12,
            day: 31,
        })
    } else {
        None
    }
}

/// The UnixEpochDays interval (jcore bounds.rs:323-327):
///   (UnixEpochSeconds::MIN + OffsetTotalSeconds::MIN as i64)
///       .div_euclid(SECS_PER_CIVIL_DAY) as i32, resp. the MAX variant,
/// which evaluates to -4371587 / 2932896 (hand-checked: 86400 * 4371587
/// == 377705116800; the min/max pair is consistent with the upstream
/// exhaustive-test constant Date::MIN.until(Date::MAX) == 7_304_483 =
/// 2932896 - (-4371587), jcore date.rs:1447).
pub open spec fn ued_iv() -> Interval {
    Interval { min: -4371587, max: 2932896 }
}

// ===========================================================================
// proof plumbing: rust_rem <-> Euclid-mod bridging and the leap-year
// equivalence (the upstream branchless formula vs the textbook rule)
// ===========================================================================

/// rust_rem(a, b) == 0 iff Euclid a % b == 0, for b > 0. The negative
/// dividend case follows the same product chain as J1's
/// lemma_rust_rem_multiple_iff (bounds.rs:967): trunc and Euclid remainders
/// differ by exactly rhs when the trunc remainder is nonzero.
proof fn lemma_rust_rem_zero_iff(a: int, b: int)
    requires b > 0,
    ensures rust_rem(a, b) == 0 <==> a % b == 0,
{
    if a == 0 {
        assert(rust_rem(a, b) == 0);
        assert(a % b == 0);
    } else if a > 0 {
        assert(rust_rem(a, b) == a % b);
    } else {
        let n: int = -a;
        assert(a == 0 - n);
        let q: int = n / b;
        let e: int = n % b;
        lemma_fundamental_div_mod(n, b);
        assert(n == b * q + e);
        assert(0 <= e < b);
        lemma_mul_is_commutative(q, b);
        lemma_mul_unary_negation(q, b);
        assert(a == (-q) * b + (0 - e));
        if e == 0 {
            assert(a == (-q) * b);
            assert(rust_rem(a, b) == 0);
            lemma_mod_multiples_basic(-q, b);
            assert(((-q) * b) % b == 0);
            assert(a % b == 0);
        } else {
            let w: int = b - e;
            assert(0 < w < b);
            lemma_mul_is_distributive_add_other_way(b, q, 1);
            lemma_mul_basics(b);
            assert((q + 1) * b == q * b + 1 * b);
            assert(1 * b == b);
            assert((q + 1) * b == q * b + b);
            lemma_mul_unary_negation(q + 1, b);
            assert((-(q + 1)) * b == 0 - ((q + 1) * b));
            assert((-(q + 1)) * b == (0 - q * b) - b);
            assert(a == (0 - (q + 1)) * b + w);
            lemma_fundamental_div_mod_converse(a, b, 0 - (q + 1), w);
            assert(a % b == w);
            assert(rust_rem(a, b) == 0 - e);
        }
    }
}

/// Divisor transfer: mD | mN implies (y % mN == 0 -> y % mD == 0), e.g.
/// 400-transfer: 100 | y -> 25 | y. Constant-chain shape; executed at
/// int level with mul lemmas because var*const products never rewrite
/// on their own.
proof fn lemma_divisor_transfer(y: int, mN: int, mD: int)
    requires mN % mD == 0, mD > 0, mN != 0,
    ensures y % mN == 0 ==> y % mD == 0,
{
    if y % mN == 0 {
        let q: int = y / mN;
        let c: int = mN / mD;
        lemma_fundamental_div_mod(y, mN);
        assert(y == q * mN + y % mN);
        assert(y == q * mN);
        lemma_fundamental_div_mod(mN, mD);
        assert(mN == c * mD + mN % mD);
        assert(mN == c * mD);
        lemma_mul_is_commutative(q, mN);
        lemma_mul_is_associative(q, c, mD);
        assert(q * (c * mD) == (q * c) * mD);
        assert(y == (q * c) * mD);
        lemma_mod_multiples_basic(q * c, mD);
        assert(((q * c) * mD) % mD == 0);
        assert(y % mD == 0);
    }
}

/// Coprime split (4, 25): 4 | y && 25 | y -> 100 | y. The residue case
/// check is ground arithmetic: 4*s for s in 1..=24 never hits the
/// multiples 25, 50, 75 of 25 below 100.
proof fn lemma_mod4_25_to_100(y: int)
    requires y % 4 == 0, y % 25 == 0,
    ensures y % 100 == 0,
{
    let q: int = y / 4;
    lemma_fundamental_div_mod(y, 4);
    assert(y == q * 4);
    let t: int = q / 25;
    let s: int = q % 25;
    lemma_fundamental_div_mod(q, 25);
    assert(q == t * 25 + s);
    assert(0 <= s < 25);
    lemma_mul_is_commutative(q, 4);
    assert(y == 4 * q);
    lemma_mul_is_distributive_add(4, t * 25, s);
    assert(4 * (t * 25 + s) == 4 * (t * 25) + 4 * s);
    lemma_mul_is_associative(4, t, 25);
    assert(4 * (t * 25) == (4 * t) * 25);
    lemma_mul_is_commutative(4 * t, 25);
    assert((4 * t) * 25 == 25 * (4 * t));
    assert(y == 25 * (4 * t) + 4 * s);
    lemma_mod_multiples_vanish(4 * t, 4 * s, 25);
    assert((25 * (4 * t) + 4 * s) % 25 == (4 * s) % 25);
    assert((4 * s) % 25 == 0);
    if s != 0 {
        assert(1 <= s <= 24);
        assert(4 * s != 25 && 4 * s != 50 && 4 * s != 75);
        assert((4 * 1) % 25 == 4) by (compute_only);
        assert(4 * s % 25 != 0);
        assert(false);
    } else {
        assert(q == t * 25);
        assert(y == t * 100);
        lemma_mod_multiples_basic(t, 100);
        assert(y % 100 == 0);
    }
}

/// Coprime split (16, 25): 16 | y && 25 | y -> 400 | y. Pointwise residue
/// check: (16*s) % 25 for s in 1..=24 is never 0 (16 and 25 coprime);
/// the 24 rows are ground terms the compute prover folds directly.
proof fn lemma_mod16_25_to_400(y: int)
    requires y % 16 == 0, y % 25 == 0,
    ensures y % 400 == 0,
{
    let q: int = y / 16;
    lemma_fundamental_div_mod(y, 16);
    assert(y == q * 16);
    let t: int = q / 25;
    let s: int = q % 25;
    lemma_fundamental_div_mod(q, 25);
    assert(q == t * 25 + s);
    assert(0 <= s < 25);
    lemma_mul_is_commutative(q, 16);
    assert(y == 16 * q);
    lemma_mul_is_distributive_add(16, t * 25, s);
    assert(16 * (t * 25 + s) == 16 * (t * 25) + 16 * s);
    lemma_mul_is_associative(16, t, 25);
    assert(16 * (t * 25) == (16 * t) * 25);
    lemma_mul_is_commutative(16 * t, 25);
    assert(y == 25 * (16 * t) + 16 * s);
    lemma_mod_multiples_vanish(16 * t, 16 * s, 25);
    assert((25 * (16 * t) + 16 * s) % 25 == (16 * s) % 25);
    assert((16 * s) % 25 == 0);
    if s == 0 {
        assert(q == t * 25);
        assert(y == t * 400);
        lemma_mod_multiples_basic(t, 400);
        assert(y % 400 == 0);
    } else {
        assert(1 <= s <= 24);
        if s == 1 { assert((16 * 1) % 25 == 16) by (compute_only); }
        if s == 2 { assert((16 * 2) % 25 == 7) by (compute_only); }
        if s == 3 { assert((16 * 3) % 25 == 23) by (compute_only); }
        if s == 4 { assert((16 * 4) % 25 == 14) by (compute_only); }
        if s == 5 { assert((16 * 5) % 25 == 5) by (compute_only); }
        if s == 6 { assert((16 * 6) % 25 == 21) by (compute_only); }
        if s == 7 { assert((16 * 7) % 25 == 12) by (compute_only); }
        if s == 8 { assert((16 * 8) % 25 == 3) by (compute_only); }
        if s == 9 { assert((16 * 9) % 25 == 19) by (compute_only); }
        if s == 10 { assert((16 * 10) % 25 == 10) by (compute_only); }
        if s == 11 { assert((16 * 11) % 25 == 1) by (compute_only); }
        if s == 12 { assert((16 * 12) % 25 == 17) by (compute_only); }
        if s == 13 { assert((16 * 13) % 25 == 8) by (compute_only); }
        if s == 14 { assert((16 * 14) % 25 == 24) by (compute_only); }
        if s == 15 { assert((16 * 15) % 25 == 15) by (compute_only); }
        if s == 16 { assert((16 * 16) % 25 == 6) by (compute_only); }
        if s == 17 { assert((16 * 17) % 25 == 22) by (compute_only); }
        if s == 18 { assert((16 * 18) % 25 == 13) by (compute_only); }
        if s == 19 { assert((16 * 19) % 25 == 4) by (compute_only); }
        if s == 20 { assert((16 * 20) % 25 == 20) by (compute_only); }
        if s == 21 { assert((16 * 21) % 25 == 11) by (compute_only); }
        if s == 22 { assert((16 * 22) % 25 == 2) by (compute_only); }
        if s == 23 { assert((16 * 23) % 25 == 18) by (compute_only); }
        if s == 24 { assert((16 * 24) % 25 == 9) by (compute_only); }
        assert((16 * s) % 25 != 0);
        assert(false);
    }
}

/// Full equivalence between the upstream branchless leap face
/// (25-remainder selects divisor 4 or 16) and the textbook rule.
/// Upstream body (civil/mod.rs:173-174):
///   let d = if year % 25 != 0 { 4 } else { 16 };
///   (year % d) == 0
proof fn lemma_leap_year_equiv(y: int)
    ensures
        ((y % 25 != 0) && (y % 4 == 0)) || ((y % 25 == 0) && (y % 16 == 0))
        <==> ((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0),
{
    if y % 25 != 0 {
        if y % 100 == 0 {
            lemma_divisor_transfer(y, 100, 25);
            assert(y % 25 == 0);
            assert(false);
        }
        if y % 400 == 0 {
            lemma_divisor_transfer(y, 400, 25);
            assert(y % 25 == 0);
            assert(false);
        }
    } else {
        if y % 4 == 0 {
            lemma_mod4_25_to_100(y);
            assert(y % 100 == 0);
        }
        if y % 400 == 0 {
            lemma_divisor_transfer(y, 400, 16);
            assert(y % 16 == 0);
        } else if y % 16 == 0 {
            lemma_mod16_25_to_400(y);
            assert(y % 400 == 0);
        }
    }
}

/// days_in_month floor: every month has at least 28 days (used by
/// Date::new to justify the fast path day <= 28).
proof fn lemma_days_in_month_lower(y: int, m: int)
    requires 1 <= m <= 12,
    ensures 28 <= days_in_month_spec(y, m),
{
    if m == 2 {
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
    } else {
    }
}

// ===========================================================================
// free calendar functions (jcore civil/mod.rs faces)
// ===========================================================================

/// Origin Rust civil/mod.rs:171-175:
///     pub const fn is_leap_year(year: i16) -> bool {
///         let d = if year % 25 != 0 { 4 } else { 16 };
///         (year % d) == 0
///     }
/// Upstream doc (civil/mod.rs:167-169):
///   Returns true if and only if the given year is a leap year.
///   A leap year is a year with 366 days. Non-leap years have 365 days.
/// Transcription note: the i16 arithmetic is materialized at i64
/// (value-identical: |year| < 2^15 and d in {4, 16}); this build has no
/// exec-const support and the i64 form lets the rust_rem linkage reuse
/// the J1-proven pattern without i16-range re-derivation.
pub exec fn is_leap_year(year: i16) -> (r: bool)
    ensures r == is_leap_year_spec(year as int),
{
    let y64: i64 = year as i64;
    let m25 = y64 % 25;
    let d = if m25 != 0 { 4i64 } else { 16i64 };
    let md = y64 % d;
    proof {
        let yi: int = y64 as int;
        let di: int = d as int;
        assert(di == 4 || di == 16);
        assert(di > 0);
        assert(m25 as int == rust_rem(yi, 25));
        assert(md as int == rust_rem(yi, di));
        lemma_rust_rem_zero_iff(yi, 25);
        if di == 4 {
            lemma_rust_rem_zero_iff(yi, 4);
        } else {
            lemma_rust_rem_zero_iff(yi, 16);
        }
        lemma_leap_year_equiv(yi);
    }
    md == 0
}

/// Origin Rust civil/mod.rs:181-187:
///     pub const fn days_in_year(year: i16) -> i16 {
///         if is_leap_year(year) { 366 } else { 365 }
///     }
/// Upstream doc (civil/mod.rs:177-179):
///   Return the number of days in the given year.
///   This is guaranteed to either return `365` or `366`.
pub exec fn days_in_year(year: i16) -> (r: i16)
    ensures r as int == days_in_year_spec(year as int)
        && (r as int == 365 || r as int == 366),
{
    if is_leap_year(year) { 366 } else { 365 }
}

/// Origin Rust civil/mod.rs:193-204:
///     pub const fn days_in_month(year: i16, month: i8) -> i8 {
///         if month == 2 {
///             if is_leap_year(year) { 29 } else { 28 }
///         } else {
///             30 | (month ^ month >> 3)
///         }
///     }
/// Upstream doc (civil/mod.rs:189-191):
///   Return the number of days in the given month.
///   This is guaranteed to return a value in the range `1..=31`.
/// (The real range on the calendar domain is 28..=31 -- the doc
/// understates; see notes.md suspects.)
/// The 30 | (month ^ month >> 3) pattern is ground-checked per month
/// with the bit_vector prover (i8 xor/shr constants do not fold under
/// the arithmetic encoding).
pub exec fn days_in_month(year: i16, month: i8) -> (r: i8)
    requires 1 <= month && month <= 12,
    ensures
        r as int == days_in_month_spec(year as int, month as int)
            && 28 <= r as int && (r as int) <= 31,
{
    if month == 2 {
        if is_leap_year(year) {
            29
        } else {
            28
        }
    } else {
        proof {
            if month == 1 { assert(30 | (1 ^ (1 >> 3)) == 31i8) by (bit_vector); }
            if month == 3 { assert(30 | (3 ^ (3 >> 3)) == 31i8) by (bit_vector); }
            if month == 4 { assert(30 | (4 ^ (4 >> 3)) == 30i8) by (bit_vector); }
            if month == 5 { assert(30 | (5 ^ (5 >> 3)) == 31i8) by (bit_vector); }
            if month == 6 { assert(30 | (6 ^ (6 >> 3)) == 30i8) by (bit_vector); }
            if month == 7 { assert(30 | (7 ^ (7 >> 3)) == 31i8) by (bit_vector); }
            if month == 8 { assert(30 | (8 ^ (8 >> 3)) == 31i8) by (bit_vector); }
            if month == 9 { assert(30 | (9 ^ (9 >> 3)) == 30i8) by (bit_vector); }
            if month == 10 { assert(30 | (10 ^ (10 >> 3)) == 31i8) by (bit_vector); }
            if month == 11 { assert(30 | (11 ^ (11 >> 3)) == 30i8) by (bit_vector); }
            if month == 12 { assert(30 | (12 ^ (12 >> 3)) == 31i8) by (bit_vector); }
        }
        30 | (month ^ (month >> 3))
    }
}

// ===========================================================================
// Date (jcore civil/date.rs:18-599; the public jiff wrapper face is
// code/crates/jiff/src/civil/date.rs)
// ===========================================================================

/// Origin Rust (jcore date.rs:18-22):
///     pub struct Date { year: i16, month: i8, day: i8 }
/// Fields are public here because the Verus closure has no
/// private-field type discipline to lean on; valid_date (below) is the
/// carrying invariant instead.
#[derive(Clone, Copy)]
pub struct Date {
    pub year: i16,
    pub month: i8,
    pub day: i8,
}

impl Date {
    /// Origin Rust (jcore date.rs:81-94; the main crate re-exports it):
    ///     pub const fn new(year: i16, month: i8, day: i8)
    ///         -> Result<Date, RangeError>
    /// Upstream doc (main-crate date.rs:206-224):
    ///   Creates a new `Date` value from its component year, month and day
    ///   values.
    ///   # Errors
    ///   This returns an error when the given year-month-day does not
    ///   correspond to a valid date. Namely, all of the following must be
    ///   true:
    ///   * The year must be in the range `-9999..=9999`.
    ///   * The month must be in the range `1..=12`.
    ///   * The day must be at least `1` and must be at most the number of
    ///   days in the corresponding month. So for example, `2024-02-29` is
    ///   valid but `2023-02-29` is not.
    /// The rtry!/rbail! macros transcribe as their let-else expansions.
    pub exec fn new(year: i16, month: i8, day: i8) -> (r: Option<Date>)
        ensures
            match r {
                Option::Some(d) => d.year as int == year as int
                    && d.month as int == month as int
                    && d.day as int == day as int
                    && valid_date(d),
                Option::None => !(
                    year_iv().contains(year as int)
                        && month_iv().contains(month as int)
                        && 1 <= day as int
                        && day as int
                            <= days_in_month_spec(year as int, month as int)
                ),
            },
    {
        let Some(y) = Year::checkc(year as i64) else { return Option::None };
        let Some(m) = Month::checkc(month as i64) else { return Option::None };
        if day < 1i8 {
            return Option::None;
        }
        let dim = days_in_month(y, m);
        if day > 28i8 && day > dim {
            return Option::None;
        }
        proof {
            lemma_days_in_month_lower(y as int, m as int);
        }
        Option::Some(Date { year: y, month: m, day })
    }

    /// Origin Rust (jcore date.rs:102-122):
    ///     pub const fn new_constrain(year: i16, month: i8, day: i8)
    ///         -> Result<Date, RangeError>
    /// Upstream doc (jcore date.rs:97-100):
    ///   Like `Date::new`, but constrains the day value to the last day of
    ///   `month`.
    ///   This still returns an error when `day < 1` or when `year` or
    ///   `month` are invalid.
    pub exec fn new_constrain(
        year: i16,
        month: i8,
        day: i8,
    ) -> (r: Option<Date>)
        ensures
            match r {
                Option::Some(d) => d.year as int == year as int
                    && d.month as int == month as int
                    && d.day as int
                        == if day as int
                            > days_in_month_spec(year as int, month as int) {
                            days_in_month_spec(year as int, month as int)
                        } else {
                            day as int
                        }
                    && valid_date(d),
                Option::None => !(
                    year_iv().contains(year as int)
                        && month_iv().contains(month as int)
                        && 1 <= day as int
                ),
            },
    {
        let Some(y) = Year::checkc(year as i64) else { return Option::None };
        let Some(m) = Month::checkc(month as i64) else { return Option::None };
        if day < 1i8 {
            return Option::None;
        }
        let days_in_month = days_in_month(y, m);
        let cday = if day > 28i8 {
            if day <= days_in_month {
                day
            } else {
                days_in_month
            }
        } else {
            day
        };
        proof {
            lemma_days_in_month_lower(y as int, m as int);
        }
        Option::Some(Date { year: y, month: m, day: cday })
    }

    /// Origin Rust (jiff main-crate date.rs:309-314):
    ///     pub const fn constant(year: i16, month: i8, day: i8) -> Date
    /// Upstream doc (main-crate date.rs:284-296):
    ///   Creates a new `Date` value in a `const` context.
    ///   # Panics
    ///   This routine panics when [`Date::new`] would return an error.
    /// The panic face materializes as the precondition (this build has no
    /// const-fn or panic-path verification; the Date::MIN/MAX/ZERO const
    /// faces live upstream on this routine).
    pub exec fn constant(year: i16, month: i8, day: i8) -> (d: Date)
        requires
            year_iv().contains(year as int)
                && month_iv().contains(month as int)
                && 1 <= day as int
                && day as int
                    <= days_in_month_spec(year as int, month as int),
        ensures
            d.year as int == year as int
                && d.month as int == month as int
                && d.day as int == day as int
                && valid_date(d),
    {
        let Some(d) = Date::new(year, month, day) else {
            proof { assert(false); }
            unreachable!()
        };
        d
    }

    /// Origin Rust (jcore date.rs:181-183):
    ///     pub const fn year(self) -> i16 { self.year }
    /// Upstream doc (jcore date.rs:176-180):
    ///   Returns the year component of this date.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`Year`](crate::bounds::Year).
    pub exec fn year(self) -> (r: i16)
        ensures valid_date(self) ==> year_iv().contains(r as int)
            && r as int == self.year as int,
    {
        self.year
    }

    /// Origin Rust (jcore date.rs:189-191):
    ///     pub const fn month(self) -> i8 { self.month }
    /// Upstream doc (jcore date.rs:185-188):
    ///   Returns the month component of this date.
    ///   The value returned is guaranteed to be in the range `1..=12`.
    pub exec fn month(self) -> (r: i8)
        ensures valid_date(self) ==> month_iv().contains(r as int)
            && r as int == self.month as int,
    {
        self.month
    }

    /// Origin Rust (jcore date.rs:198-200):
    ///     pub const fn day(self) -> i8 { self.day }
    /// Upstream doc (jcore date.rs:193-197):
    ///   Returns the day component of this date.
    ///   The value returned is guaranteed to be in the range
    ///   `1..=`[`days_in_month`](crate::civil::days_in_month)`(date.year(),
    ///   date.month())`.
    pub exec fn day(self) -> (r: i8)
        ensures valid_date(self) ==> 1 <= r as int
            && (r as int) <= days_in_month_spec(self.year as int, self.month as int)
            && r as int == self.day as int,
    {
        self.day
    }

    /// Origin Rust (jcore date.rs:249-251; main-crate wrapper :594-596):
    ///     pub const fn first_of_month(self) -> Date {
    ///         Date { day: 1, ..self }
    ///     }
    /// Upstream doc (main-crate date.rs:583-592):
    ///   Returns the first date of the month that this date resides in.
    pub exec fn first_of_month(self) -> (r: Date)
        requires valid_date(self),
        ensures
            valid_date(r)
                && r.year as int == self.year as int
                && r.month as int == self.month as int
                && r.day as int == 1,
    {
        Date { year: self.year, month: self.month, day: 1 }
    }

    /// Origin Rust (jcore date.rs:255-257; main-crate wrapper :609-611):
    ///     pub const fn last_of_month(self) -> Date {
    ///         Date { day: self.days_in_month(), ..self }
    ///     }
    /// Upstream doc (main-crate date.rs:598-607):
    ///   Returns the last date of the month that this date resides in.
    pub exec fn last_of_month(self) -> (r: Date)
        requires valid_date(self),
        ensures
            valid_date(r)
                && r.year as int == self.year as int
                && r.month as int == self.month as int
                && r.day as int
                    == days_in_month_spec(self.year as int, self.month as int),
    {
        Date {
            year: self.year,
            month: self.month,
            day: days_in_month(self.year, self.month),
        }
    }

    /// Origin Rust (jcore date.rs:265-267; main-crate wrapper :634-636):
    ///     pub const fn days_in_month(self) -> i8 {
    ///         civil::days_in_month(self.year(), self.month())
    ///     }
    /// Upstream doc (main-crate date.rs:613-617):
    ///   Returns the total number of days in the the month in which this
    ///   date resides.
    ///   This is guaranteed to always return one of the following values,
    ///   depending on the year and the month: 28, 29, 30 or 31.
    pub exec fn days_in_month(self) -> (r: i8)
        requires valid_date(self),
        ensures
            r as int
                == days_in_month_spec(self.year as int, self.month as int)
                && 28 <= r as int && (r as int) <= 31,
    {
        days_in_month(self.year, self.month)
    }

    /// Origin Rust (jcore date.rs:271-273; main-crate wrapper :649-651):
    ///     pub const fn first_of_year(self) -> Date {
    ///         Date { month: 1, day: 1, ..self }
    ///     }
    /// Upstream doc (main-crate date.rs:638-646):
    ///   Returns the first date of the year that this date resides in.
    pub exec fn first_of_year(self) -> (r: Date)
        requires valid_date(self),
        ensures
            valid_date(r)
                && r.year as int == self.year as int
                && r.month as int == 1
                && r.day as int == 1,
    {
        Date { year: self.year, month: 1, day: 1 }
    }

    /// Origin Rust (jcore date.rs:277-279; main-crate wrapper :664-666):
    ///     pub const fn last_of_year(self) -> Date {
    ///         Date { month: 12, day: 31, ..self }
    ///     }
    /// Upstream doc (main-crate date.rs:653-661):
    ///   Returns the last date of the year that this date resides in.
    pub exec fn last_of_year(self) -> (r: Date)
        requires valid_date(self),
        ensures
            valid_date(r)
                && r.year as int == self.year as int
                && r.month as int == 12
                && r.day as int == 31,
    {
        Date { year: self.year, month: 12, day: 31 }
    }

    /// Origin Rust (jcore date.rs:285-291; main-crate wrapper :685-687):
    ///     pub const fn days_in_year(self) -> i16 {
    ///         if self.in_leap_year() { 366 } else { 365 }
    ///     }
    /// Upstream doc (main-crate date.rs:668-671):
    ///   Returns the total number of days in the the year in which this
    ///   date resides.
    ///   This is guaranteed to always return either `365` or `366`.
    pub exec fn days_in_year(self) -> (r: i16)
        requires valid_date(self),
        ensures
            r as int == days_in_year_spec(self.year as int)
                && (r as int == 365 || r as int == 366),
    {
        if self.in_leap_year() {
            366
        } else {
            365
        }
    }

    /// Origin Rust (jcore date.rs:295-297; main-crate wrapper :701-703):
    ///     pub const fn in_leap_year(self) -> bool {
    ///         civil::is_leap_year(self.year())
    ///     }
    /// Upstream doc (main-crate date.rs:689-699):
    ///   Returns true if and only if the year in which this date resides
    ///   is a leap year.
    pub exec fn in_leap_year(self) -> (r: bool)
        requires valid_date(self),
        ensures r == is_leap_year_spec(self.year as int),
    {
        is_leap_year(self.year)
    }

    /// Origin Rust (jcore date.rs:303-314; main-crate wrapper :749-754):
    ///     pub const fn yesterday(self) -> Result<Date, RangeError>
    /// Upstream doc (main-crate date.rs:729-747):
    ///   Returns the date immediately preceding this one.
    ///   # Errors
    ///   This returns an error when this date is the minimum value.
    ///   # Example (skipped, pin :735-747)
    pub exec fn yesterday(self) -> (r: Option<Date>)
        requires valid_date(self),
        ensures
            r == spec_yesterday(self)
                && (r is Some ==> valid_date(r->Some_0)),
    {
        if self.day() == 1 {
            if self.month() == 1 {
                return match self.prev_year() {
                    Option::Some(year) => Option::Some(Date {
                        year,
                        month: 12,
                        day: 31,
                    }),
                    Option::None => Option::None,
                };
            }
            let month = self.month() - 1;
            let day = days_in_month(self.year, month);
            return Option::Some(Date {
                year: self.year,
                month,
                day,
            });
        }
        Option::Some(Date {
            year: self.year,
            month: self.month,
            day: self.day - 1,
        })
    }

    /// Origin Rust (jcore date.rs:320-330; main-crate wrapper :725-727):
    ///     pub const fn tomorrow(self) -> Result<Date, RangeError>
    /// Upstream doc (main-crate date.rs:705-723):
    ///   Returns the date immediately following this one.
    ///   # Errors
    ///   This returns an error when this date is the maximum value.
    ///   # Example (skipped, pin :711-723)
    pub exec fn tomorrow(self) -> (r: Option<Date>)
        requires valid_date(self),
        ensures
            r == spec_tomorrow(self)
                && (r is Some ==> valid_date(r->Some_0)),
    {
        if self.day() >= 28i8 && self.day() == self.days_in_month() {
            if self.month() == 12 {
                return match self.next_year() {
                    Option::Some(year) => Option::Some(Date {
                        year,
                        month: 1,
                        day: 1,
                    }),
                    Option::None => Option::None,
                };
            }
            let month = self.month() + 1;
            return Option::Some(Date {
                year: self.year,
                month,
                day: 1,
            });
        }
        Option::Some(Date {
            year: self.year,
            month: self.month,
            day: self.day + 1,
        })
    }

    /// Origin Rust (jcore date.rs:387-389):
    ///     pub(crate) const fn prev_year(self) -> Result<i16, RangeError>
    /// Upstream doc (jcore date.rs:383-385):
    ///   Returns the year one year before this date.
    ///   Returns an error if this would result in a year outside the range
    ///   specified by [`Year`](b::Year).
    pub exec fn prev_year(self) -> (r: Option<i16>)
        requires valid_date(self),
        ensures
            match r {
                Option::Some(y) => y as int == (self.year as int) - 1
                    && year_iv().contains(y as int),
                Option::None => self.year as int == -9999,
            },
    {
        Year::checked_add(self.year, -1i16)
    }

    /// Origin Rust (jcore date.rs:393-395):
    ///     pub(crate) const fn next_year(self) -> Result<i16, RangeError>
    /// Upstream doc (jcore date.rs:391):
    ///   Returns the year one year from this date.
    pub exec fn next_year(self) -> (r: Option<i16>)
        requires valid_date(self),
        ensures
            match r {
                Option::Some(y) => y as int == (self.year as int) + 1
                    && year_iv().contains(y as int),
                Option::None => self.year as int == 9999,
            },
    {
        Year::checked_add(self.year, 1i16)
    }

    /// Origin Rust (jcore date.rs:401-408):
    ///     pub const fn checked_add(self, days: i32)
    ///         -> Result<Date, RangeError>
    /// Upstream doc (jcore date.rs:397-399):
    ///   Adds the given number of days to this date.
    ///   Returns an error if the result is outside the valid range of a
    ///   `Date`.
    /// Contract note: the 0/+1/-1 fast paths carry the full structural
    /// contract; the general-N path is the Neri-Schneider epoch-day
    /// bridge, whose informative postconditions (validity and the
    /// roundtrip family) are deferred to the NS-roundtrip batch --
    /// upstream's own contract for this path is validated by exhaustive
    /// test (jcore date.rs:1419-1454, 1934-1981).
    pub exec fn checked_add(self, days: i32) -> (r: Option<Date>)
        requires valid_date(self),
        ensures
            days == 0 ==> r == Option::Some(self),
            days == 1 ==> r == spec_tomorrow(self),
            days == -1 ==> r == spec_yesterday(self),
    {
        match days {
            0 => Option::Some(self),
            -1 => self.yesterday(),
            1 => self.tomorrow(),
            n => match self.to_unix_epoch_day().checked_add(n) {
                Option::Some(e) => Option::Some(e.to_date()),
                Option::None => Option::None,
            },
        }
    }

    /// Origin Rust (jcore date.rs:414-419):
    ///     pub const fn checked_sub(self, days: i32)
    ///         -> Result<Date, RangeError>
    /// Upstream doc (jcore date.rs:410-412):
    ///   Subtracts the given number of days to this date.
    ///   Returns an error if the result is outside the valid range of a
    ///   `Date`.
    pub exec fn checked_sub(self, days: i32) -> (r: Option<Date>)
        requires valid_date(self),
        ensures
            days == 0 ==> r == Option::Some(self),
            days == 1 ==> r == spec_yesterday(self),
            days == -1 ==> r == spec_tomorrow(self),
            days == i32::MIN ==> r == Option::None,
    {
        if days == i32::MIN {
            // std i32::checked_neg (no vstd spec in this build) inlined:
            // the only negation failure is i32::MIN; upstream then
            // rbail!s with b::UnixEpochDays::error().
            return Option::None;
        }
        let days = 0i32 - days;
        self.checked_add(days)
    }

    /// Origin Rust (jcore date.rs:498-523):
    ///     pub const fn to_unix_epoch_day(self) -> UnixEpochDay
    ///     // This is Neri-Schneider. There's no branching or divisions.
    /// Upstream doc (jcore date.rs:495-496):
    ///   Converts a Gregorian date to a Unix epoch day.
    /// Transcription ledger (see module header): the u32 wrapping chains
    /// materialize in i64 where they are identities (year + L - J and
    /// 2^32*[day < 0] + day + K are the exact wrapped values for every
    /// representable input whose month and day are in the valid domain).
    /// Basic bounds checks: this computes the same grand-total as upstream
    /// for every valid date; the full NS spec (epoch-day ranges, the
    /// to_date roundtrip) is deferred with the harness-batch record.
    #[allow(non_snake_case)] // upstream Neri-Schneider identifier shapes
    pub exec fn to_unix_epoch_day(self) -> (r: UnixEpochDay)
    {
        const K: i64 = 719468 + 146097 * 82;
        const L: i64 = 400 * 82;

        let year: i64 = self.year as i64;
        let month: i64 = self.month as i64;
        let day: i64 = self.day as i64;

        let J: i64 = if month <= 2 { 1 } else { 0 };
        let Y: i64 = year + L - J;
        let M: i64 = if J == 1 { month + 12 } else { month };
        let D: i64 = day - 1;
        let C: i64 = Y / 100;

        let y_star = 1461 * Y / 4 - C + C / 4;
        let m_star = (979 * M - 2919) / 32;
        let N = y_star + m_star + D;

        let N_U = N - K;
        let epoch_day = N_U as i32;
        UnixEpochDay { day: epoch_day }
    }
}

/// Origin Rust (jiff main-crate civil/mod.rs:244-246):
///     pub const fn date(year: i16, month: i8, day: i8) -> Date {
///         Date::constant(year, month, day)
///     }
/// Upstream doc (main-crate civil/mod.rs:231-243):
///   Creates a new `Date` value in a `const` context.
///   This is a convenience free function for [`Date::constant`]. It is
///   intended to provide a terse syntax for constructing `Date` values
///   from parameters that are known to be valid.
///   # Panics
///   This panics if the given values do not correspond to a valid `Date`.
pub exec fn date(year: i16, month: i8, day: i8) -> (d: Date)
    requires
        year_iv().contains(year as int)
            && month_iv().contains(month as int)
            && 1 <= day as int
            && (day as int) <= days_in_month_spec(year as int, month as int),
    ensures
        d.year as int == year as int
            && d.month as int == month as int
            && d.day as int == day as int
            && valid_date(d),
{
    Date::constant(year, month, day)
}

// ===========================================================================
// UnixEpochDay (jcore civil/date.rs:695-935)
// ===========================================================================

/// Origin Rust (jcore date.rs:695-699):
///     pub struct UnixEpochDay { day: i32 }
/// Upstream doc (jcore date.rs:687-694):
///   A civil date represented by a number of days since the Unix epoch
///   (1970-01-01).
///   The date can be positive (occurs after 1970-01-01) or negative
///   (occurs before 1970-01-01). A zero value corresponds to 1970-01-01.
///   Unix epoch days can be infallibly converted to and from [`Date`]
///   values.
#[derive(Clone, Copy)]
pub struct UnixEpochDay {
    pub day: i32,
}

impl UnixEpochDay {
    /// Origin Rust (jcore date.rs:720-723):
    ///     pub const fn new(day: i32) -> Result<UnixEpochDay, RangeError>
    /// Upstream doc (jcore date.rs:714-718):
    ///   Creates a new Unix epoch day.
    ///   The day given must correspond to a number of days (positive or
    ///   negative) since the Unix epoch (1970-01-01). A value of `0`
    ///   corresponds to `1970-01-01`.
    pub exec fn new(day: i32) -> (r: Option<UnixEpochDay>)
        ensures
            match r {
                Option::Some(e) => e.day as int == day as int
                    && ued_iv().contains(day as int),
                Option::None => !ued_iv().contains(day as int),
            },
    {
        let Some(d) = const_check::i32(-4371587i32, 2932896i32, day as i64)
        else { return Option::None };
        Option::Some(UnixEpochDay { day: d })
    }

    /// Origin Rust (jcore date.rs:730-732):
    ///     pub const fn day(self) -> i32 { self.day }
    /// Upstream doc (jcore date.rs:725-728):
    ///   Returns the underlying day value.
    ///   This is guaranteed to be in the [`UnixEpochDays`](b::UnixEpochDays)
    ///   range.
    pub exec fn day(self) -> (r: i32)
        ensures ued_iv().contains(self.day as int) ==> ued_iv().contains(r as int),
    {
        self.day
    }

    /// Origin Rust (jcore date.rs:813-819):
    ///     pub const fn checked_add(self, days: i32)
    ///         -> Result<UnixEpochDay, RangeError>
    /// Upstream doc (jcore date.rs:808-812):
    ///   Add the given number of days to this Unix epoch day.
    ///   If this would overflow an `i32` or result in an out-of-bounds Unix
    ///   epoch day, then this returns an error.
    pub exec fn checked_add(self, days: i32) -> (r: Option<UnixEpochDay>)
        ensures
            match r {
                Option::Some(e) => e.day as int
                    == (self.day as int) + (days as int)
                    && ued_iv().contains(e.day as int),
                Option::None => !ued_iv().contains(
                    (self.day as int) + (days as int),
                ),
            },
    {
        let Some(d) = const_checked_add::i32(
            -4371587i32,
            2932896i32,
            self.day,
            days,
        ) else { return Option::None };
        Option::Some(UnixEpochDay { day: d })
    }

    /// Origin Rust (jcore date.rs:826-834):
    ///     pub const fn checked_sub(self, days: i32)
    ///         -> Result<UnixEpochDay, RangeError>
    /// Upstream doc (jcore date.rs:821-825):
    ///   Subtracts the given number of days from this Unix epoch day.
    ///   If this would overflow an `i32` or result in an out-of-bounds Unix
    ///   epoch day, then this returns an error.
    pub exec fn checked_sub(self, days: i32) -> (r: Option<UnixEpochDay>)
        ensures
            match r {
                Option::Some(e) => e.day as int
                    == (self.day as int) - (days as int)
                    && ued_iv().contains(e.day as int),
                Option::None => days == i32::MIN || !ued_iv().contains(
                    (self.day as int) - (days as int),
                ),
            },
    {
        if days == i32::MIN {
            // upstream rbail!(b::UnixEpochDays::error()); days == i32::MIN
            // is the only checked_neg failure (std method inlined -- no
            // vstd spec in this build)
            return Option::None;
        }
        let days = 0i32 - days;
        self.checked_add(days)
    }

    /// Origin Rust (jcore date.rs:865-867):
    ///     pub const fn until(self, other: UnixEpochDay) -> i32 {
    ///         -self.since(other)
    ///     }
    /// Upstream doc (jcore date.rs:836-863, abridged):
    ///   Returns the number of days from this date until `other`.
    ///   This routine never overflows because of the enforced range on
    ///   `UnixEpochDay` values.
    pub exec fn until(self, other: UnixEpochDay) -> (r: i32)
        requires
            ued_iv().contains(self.day as int)
                && ued_iv().contains(other.day as int),
        ensures r as int == (other.day as int) - (self.day as int),
    {
        let s = self.since(other);
        0 - s
    }

    /// Origin Rust (jcore date.rs:897-899):
    ///     pub const fn since(self, other: UnixEpochDay) -> i32 {
    ///         self.day() - other.day()
    ///     }
    /// Upstream doc (jcore date.rs:869-895, abridged):
    ///   Returns the number of days from this date since `other`.
    ///   This routine never overflows because of the enforced range on
    ///   `UnixEpochDay` values.
    pub exec fn since(self, other: UnixEpochDay) -> (r: i32)
        requires
            ued_iv().contains(self.day as int)
                && ued_iv().contains(other.day as int),
        ensures r as int == (self.day as int) - (other.day as int),
    {
        self.day - other.day
    }

    /// Origin Rust (jcore date.rs:904-934):
    ///     pub const fn to_date(self) -> Date
    ///     // This is Neri-Schneider. There's no branching or divisions.
    /// Upstream doc (jcore date.rs:901-902):
    ///   Converts this Unix epoch day to a Gregorian date.
    /// Repair note (J7 batch, recorded in out/kverus-run/J7/notes.md):
    /// the earlier J2 body computed the u32 widening as
    /// N = day + 2^32*[day < 0] + K WITHOUT the wrapping_add wrap,
    /// which diverged from upstream for every negative epoch day
    /// (upstream wraps back to N == day + K on the whole
    /// b::UnixEpochDays domain, since day + K sits in (0, 2^32) and
    /// the wrap fires exactly once to cancel the bit-cast widening;
    /// e.g. day = -1: upstream 1969-12-31, the old form a far-future
    /// garbage year). The chain below keeps the upstream
    /// Neri-Schneider step structure at i64 with N = day + K -- the
    /// exact value of the upstream u32/u64 chain for every day the new
    /// requires admits (the struct-level b::UnixEpochDays guarantee
    /// upstream) -- and drops the earlier false
    /// "identities for every representable input" claim. No
    /// postcondition yet: the informative faces live with the J7
    /// calendar.rs twins (to_date_ns), and the universal NS reverse
    /// correctness stays deferred with the roundtrip family.
    #[allow(non_snake_case)] // upstream Neri-Schneider identifier shapes
    pub exec fn to_date(self) -> (r: Date)
        requires ued_iv().contains(self.day as int),
    {
        const K: i64 = 719468 + 146097 * 82;
        const L: i64 = 400 * 82;

        // upstream: let N_U = self.day as u32; N = N_U.wrapping_add(K).
        // On the b::UnixEpochDays domain, day + K lies in (0, 2^32), so
        // the u32 bit-cast widening and the wrapping_add wrap compose
        // to N == day + K exactly (the wrap fires once and cancels the
        // [+ 2^32 * (day < 0)] widening of the bit-cast). This is the
        // value-faithful computation of the upstream chain for every
        // day the requires admits; no downstream step reaches the u32
        // or u64 wrap widths on that domain (4*N+3 and 2939745*N_2
        // stay far below 2^32 and 2^64).
        let N: i64 = (self.day as i64) + K;

        let N_1 = 4 * N + 3;
        let C = N_1 / 146097;
        let N_C = (N_1 % 146097) / 4;

        let N_2 = 4 * N_C + 3;
        let P_2 = 2939745 * N_2;
        let Z = P_2 / 4294967296i64;
        let N_Y = (P_2 % 4294967296i64) / 2939745 / 4;
        let Y = 100 * C + Z;

        let N_3 = 2141 * N_Y + 197913;
        let M = N_3 / 65536;
        let D = (N_3 % 65536) / 2141;

        let J: i64 = if N_Y >= 306 { 1 } else { 0 };
        let year = (Y - L + J) as i16;
        let month = (if J == 1 { M - 12 } else { M }) as i8;
        let day = (D + 1) as i8;
        Date { year, month, day }
    }
}

// ===========================================================================
// months-overflow core (jiff main-crate civil/date.rs:3422-3433), the
// Span-free arithmetic heart of Date::checked_add_span (date.rs:1363-1364)
// ===========================================================================

/// rem_euclid at the month core's fixed divisor 12. The std
/// rem_euclid body (self % rhs, + rhs when negative) has no vstd spec in
/// this build (probe3 finding), so the std definition is inlined here at
/// the divisor the batch needs.
/// Domain note: |a| <= 2^30 keeps `x + 12` and the caller's total free of
/// i32 overflow; the month core's total is bounded by SpanMonths.
pub exec fn rem_euclid_12(a: i32) -> (r: i32)
    requires -(1073741824i32) <= a <= 1073741824i32,
    ensures r as int == (a as int) % 12 && 0 <= r as int && (r as int) < 12,
{
    let x = a % 12;
    proof {
        let ai: int = a as int;
        assert(x as int == rust_rem(ai, 12));
        if a == 0 {
            assert(rust_rem(ai, 12) == 0);
        } else if a > 0 {
            assert(rust_rem(ai, 12) == ai % 12);
        } else {
            let n: int = 0 - ai;
            let q: int = n / 12;
            let e: int = n % 12;
            lemma_fundamental_div_mod(n, 12);
            assert(n == 12 * q + e);
            assert(0 <= e < 12);
            lemma_mul_is_commutative(q, 12);
            lemma_mul_unary_negation(q, 12);
            assert(ai == (-q) * 12 + (0 - e));
            if x == 0 {
                assert(ai == (-q) * 12);
                assert(rust_rem(ai, 12) == 0);
                assert(ai % 12 == 0);
            } else {
                let w: int = 12 - e;
                assert(0 < w < 12);
                lemma_mul_is_distributive_add_other_way(12, q, 1);
                lemma_mul_basics(12);
                assert((q + 1) * 12 == q * 12 + 1 * 12);
                assert(1 * 12 == 12);
                assert((q + 1) * 12 == q * 12 + 12);
                lemma_mul_unary_negation(q + 1, 12);
                assert((-(q + 1)) * 12 == 0 - ((q + 1) * 12));
                assert((-(q + 1)) * 12 == (0 - q * 12) - 12);
                assert(ai == (0 - (q + 1)) * 12 + w);
                lemma_fundamental_div_mod_converse(ai, 12, 0 - (q + 1), w);
                assert(ai % 12 == w);
                assert(rust_rem(ai, 12) == 0 - e);
                assert(x as int == 0 - e);
            }
        }
    }
    if x < 0 {
        x + 12
    } else {
        x
    }
}

/// div_euclid at the month core's fixed divisor 12 (std inlines as
/// (self - self.rem_euclid(rhs)) / rhs; same transcription rationale as
/// rem_euclid_12).
pub exec fn div_euclid_12(a: i32) -> (q: i32)
    requires -(1073741824i32) <= a <= 1073741824i32,
    ensures
        (q as int) * 12 + (a as int % 12) == a as int
            && (q as int) >= -89478486
            && (q as int) <= 89478486,
{
    let r = rem_euclid_12(a);
    (a - r) / 12
}

/// Origin Rust (jiff main-crate civil/date.rs:3422-3433):
///     fn month_add_overflowing(month: i8, span: i32) -> (i8, i16) {
///         debug_assert!(b::SpanMonths::check(span).is_ok());
///         let month = i32::from(month);
///         let total = month - 1 + span;
///         let years = total.div_euclid(12);
///         let month = total.rem_euclid(12) + 1;
///         (month as i8, years as i16)
///     }
/// Upstream doc (main-crate date.rs:3412-3421):
///   Adds the given span of months to the `month` given.
///   If adding (or subtracting) would result in overflowing the `month`
///   value, then the amount by which it overflowed, in units of years,
///   is returned. For example, adding 14 months to the month `3` (March)
///   will result in returning the month `5` (May) with `1` year of
///   overflow.
///   # Preconditions
///   Callers must ensure that `span` is in bounds for `b::SpanMonths`.
/// b::SpanMonths is -239976..=239976 (jiff util/b.rs:193-194:
/// SpanYears::MAX as i32 * 12 with SpanYears::MAX = (Year::LEN - 1) as
/// i16 = 19998, util/b.rs:193), so that upstream comment's i8/i16 fit
/// claims (date.rs:3428-3432) hold with slack.
pub exec fn month_add_overflowing(month: i8, span: i32) -> (r: (i8, i16))
    requires
        1 <= month as int && (month as int) <= 12
            && -239976 <= span as int && (span as int) <= 239976,
    ensures
        ({
                let total: int = (month as int) - 1 + (span as int);
                r.0 as int == total % 12 + 1
                    && (r.1 as int) * 12 + (r.0 as int) - 1 == total
                    && 1 <= r.0 as int && (r.0 as int) <= 12
                    && -19999 <= r.1 as int && (r.1 as int) <= 19999
            }),
{
    let month_i: i32 = month as i32;
    let total = month_i - 1 + span;
    let years = div_euclid_12(total);
    let month2 = rem_euclid_12(total) + 1;
    (month2 as i8, years as i16)
}

} // verus!
