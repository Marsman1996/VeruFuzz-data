//! Batch J7 -- the Neri-Schneider turnover family of the jiff-core
//! civil calendar, Verus transcription of:
//!   - code/crates/jiff-core/src/civil/date.rs (the calendar-remainder
//!     tail of the J2 cut: Date::MIN/MAX consts at :29-47,
//!     from_day_of_year at :131-160 and from_day_of_year_no_leap at
//!     :163-179, Date::weekday at :204-206, day_of_year at :213-231 and
//!     day_of_year_no_leap at :234-244, nth_weekday_of_month at
//!     :343-372 and nth_weekday at :374-380, Date::until/since at
//!     :450-451/:482-494, to_unix_epoch_day at :498-523,
//!     to_iso_week_date at :527-581, UnixEpochDay::weekday at
//!     :736-772, UnixEpochDay::nth_weekday at :782-810,
//!     UnixEpochDay::to_date at :904-934, the ISOWeekDate type at
//!     :985-1291, iso_week_start_from_year at :1333-1352, and the test
//!     rows at :1409-1659, :2016-2067)
//!   - code/crates/jiff-core/src/civil/mod.rs (is_long_iso_week_year
//!     at :211-224, weeks_in_iso_week_year at :227-232)
//!   - wrapper faces in code/crates/jiff/src/civil/date.rs (era_year at
//!     :426-472, weekday at :516-526, day_of_year at :530-551,
//!     day_of_year_no_leap at :553-574, nth_weekday_of_month at
//!     :760-830, nth_weekday at :925-982, iso_week_date at
//!     :1000-1039) and the jiff-crate Era enum from
//!     code/crates/jiff/src/civil/mod.rs:116-140.
//!
//! Materialization ledger (this file):
//! - Result<T, RangeError> faces materialize as Option<T> (the J1
//!   bounds.rs ledger); rbail! transcribes as Option::None, and every
//!   upstream "# Panics" example converts to the stated precondition.
//! - The J2 steady-state faces Date::to_unix_epoch_day and
//!   UnixEpochDay::to_date carry no informative ensures (J2 deferred
//!   the Neri-Schneider correctness family) and date.rs is byte-frozen
//!   for this batch. This file therefore owns informative NS twins with
//!   full contracts: to_unix_epoch_day_ns (the forward chain, ensured
//!   equal to the open spec fn ns_epoch_day_spec and inside the ued
//!   interval) and to_date_ns (the reverse chain, ensured componentwise
//!   equal to the open spec fns ns_civil_{year,month,day}). The twin
//!   bodies mirror the J2 i64 transcriptions (the exact upstream u32
//!   identities on the representable domain), and the
//!   twin-vs-frozen-body agreement is machine-checked at the row panels
//!   below (z3 ground-folds both bodies at the witness dates).
//! - to_date_ns transcription note (the batch's top suspect, recorded
//!   in J7/notes.md): upstream `N_U.wrapping_add(K)` wraps to N ==
//!   self.day + K for every day in the b::UnixEpochDays range (day + K
//!   sits in (0, 2^32) there, so the wrap fires exactly once and
//!   cancels the u32 widening of N_U = day as u32). The J2 frozen
//!   transcription instead reads N = day + 2^32*[day < 0] + K without
//!   the wrap, diverging from upstream for every negative epoch day.
//!   This file transcribes the faithful identity N = day + K.
//! - The universal roundtrip theorems (to_date_ns(to_unix_epoch_day_ns
//!   (d)) == d over the full domain and the converse) remain deferred
//!   exactly as J2 recorded them: the proof needs the full modular
//!   machinery over the 146097/2939745/2141 magic chains, which
//!   upstream itself does not prove (upstream validates by exhaustive
//!   test loops, jcore date.rs:1419-1463). The row panels machine-check
//!   the roundtrip and the twin agreement at the upstream test
//!   witnesses, including both range extremes.
//! - from_day_of_year walks the month table directly instead of
//!   roundtripping through the epoch-day bridge (jcore date.rs:131-160
//!   computes the Jan 1 epoch day, adds day - 1, converts back). The
//!   doc-level contract is fully verified against the walk; the doc
//!   contract and the bridge are value-identical whenever the NS
//!   reverse chain is correct (witness-checked at the row panels).
//! - day_of_year's [i16;14] tables (jcore date.rs:214-218) materialize
//!   as exhaustive constant matches over (leap, month), value-identical
//!   row for row.
//! - The jiff-crate Era enum (BCE/CE) has no jcore counterpart; it is
//!   transcribed here with variant-test contracts (derived enum
//!   equality is contract-opaque, the J1 finding).
//! - Contracts speak through the spec index twins (wd_monday_one for
//!   weekdays), never through derived enum equality.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
};
use vstd::arithmetic::mul::{
    lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add, lemma_mul_is_distributive_add_other_way,
};

use super::bounds::{Year, year_iv};
use super::date::{
    Date, UnixEpochDay, days_in_year, is_leap_year, valid_date, ued_iv,
    days_in_month_spec, days_in_year_spec, is_leap_year_spec, date,
};
use super::weekday::{Weekday, wd_monday_one};

verus! {

// ===========================================================================
// spec models: the NS twins, the weekday shift lane, the day-of-year
// table, and the from_day_of_year walk
// ===========================================================================

/// The Neri-Schneider forward chain (jcore date.rs:498-523) at int.
/// On the valid-date domain Y = year + L - J stays in [22800, 42799],
/// so every division below has positive operands and the upstream u32
/// wraps are exact (no wrap) at this form.
pub open spec fn ns_epoch_day_spec(year: int, month: int, day: int) -> int {
    let J: int = if month <= 2 { 1 } else { 0 };
    let Y: int = year + 32800 - J;
    let M: int = if J == 1 { month + 12 } else { month };
    let C: int = Y / 100;
    let y_star: int = 1461 * Y / 4 - C + C / 4;
    let m_star: int = (979 * M - 2919) / 32;
    y_star + m_star + (day - 1) - 12699422
}

/// The Neri-Schneider reverse chain (jcore date.rs:904-934) at int.
/// The u32 widening wraps exactly once on the ued interval, so N ==
/// e + K is the faithful identity there (see the ledger above).
pub open spec fn ns_civil_year(e: int) -> int {
    let N: int = e + 12699422;
    let N_1: int = 4 * N + 3;
    let C: int = N_1 / 146097;
    let N_C: int = (N_1 % 146097) / 4;
    let N_2: int = 4 * N_C + 3;
    let P_2: int = 2939745 * N_2;
    let Z: int = P_2 / 4294967296;
    let N_Y: int = (P_2 % 4294967296) / 2939745 / 4;
    let Y: int = 100 * C + Z;
    let J: int = if N_Y >= 306 { 1 } else { 0 };
    Y - 32800 + J
}

pub open spec fn ns_civil_month(e: int) -> int {
    let N: int = e + 12699422;
    let N_1: int = 4 * N + 3;
    let C: int = N_1 / 146097;
    let N_C: int = (N_1 % 146097) / 4;
    let N_2: int = 4 * N_C + 3;
    let P_2: int = 2939745 * N_2;
    let N_Y: int = (P_2 % 4294967296) / 2939745 / 4;
    let N_3: int = 2141 * N_Y + 197913;
    let M: int = N_3 / 65536;
    let J: int = if N_Y >= 306 { 1 } else { 0 };
    if J == 1 { M - 12 } else { M }
}

pub open spec fn ns_civil_day(e: int) -> int {
    let N: int = e + 12699422;
    let N_1: int = 4 * N + 3;
    let C: int = N_1 / 146097;
    let N_C: int = (N_1 % 146097) / 4;
    let N_2: int = 4 * N_C + 3;
    let P_2: int = 2939745 * N_2;
    let N_Y: int = (P_2 % 4294967296) / 2939745 / 4;
    let N_3: int = 2141 * N_Y + 197913;
    let D: int = (N_3 % 65536) / 2141;
    D + 1
}

/// The spec value the UnixEpochDay weekday shift lane computes (the
/// upstream add-mul-shift, jcore date.rs:736-772): the u32 bit-cast of
/// a negative day, the wrapping mul-add, the 2^32 wrap, the 2^29 read.
pub open spec fn wd_shift_lane(e: int) -> int {
    (if e < 0 {
        (e + 4294967296) * 613566757 + 2415919104
    } else {
        e * 613566757 + 2415919104
    }) % 4294967296 / 536870912
}

/// The Monday-one weekday of an epoch day as the Thursday-anchored
/// Euclid face (the Unix epoch, epoch day 0, was a Thursday).
pub open spec fn wd_of_epoch_day(e: int) -> int {
    (((e % 7) + 3) % 7) + 1
}

/// The upstream day_of_year tables (jcore date.rs:214-218) as one open
/// spec row: the index is 1..=12 (the tables carry two dead 0/1 slots
/// upstream), the value the number of days of the year strictly before
/// the given month.
pub open spec fn doy_row(leap: bool, month: int) -> int {
    if leap {
        if month == 1 { 0 }
        else if month == 2 { 31 }
        else if month == 3 { 60 }
        else if month == 4 { 91 }
        else if month == 5 { 121 }
        else if month == 6 { 152 }
        else if month == 7 { 182 }
        else if month == 8 { 213 }
        else if month == 9 { 244 }
        else if month == 10 { 274 }
        else if month == 11 { 305 }
        else { 335 }
    } else {
        if month == 1 { 0 }
        else if month == 2 { 31 }
        else if month == 3 { 59 }
        else if month == 4 { 90 }
        else if month == 5 { 120 }
        else if month == 6 { 151 }
        else if month == 7 { 181 }
        else if month == 8 { 212 }
        else if month == 9 { 243 }
        else if month == 10 { 273 }
        else if month == 11 { 304 }
        else { 334 }
    }
}

/// The calendar model of "the days of this year strictly before this
/// date's month" (jcore day_of_year doc, date.rs:208-211), built as
/// explicit sums of days_in_month_spec; only February carries the leap
/// dependence.
pub open spec fn days_before_month(year: int, month: int) -> int {
    if month == 1 { 0 }
    else if month == 2 { 31 }
    else if month == 3 { 31 + days_in_month_spec(year, 2) }
    else if month == 4 { 62 + days_in_month_spec(year, 2) }
    else if month == 5 { 92 + days_in_month_spec(year, 2) }
    else if month == 6 { 123 + days_in_month_spec(year, 2) }
    else if month == 7 { 153 + days_in_month_spec(year, 2) }
    else if month == 8 { 184 + days_in_month_spec(year, 2) }
    else if month == 9 { 215 + days_in_month_spec(year, 2) }
    else if month == 10 { 245 + days_in_month_spec(year, 2) }
    else if month == 11 { 276 + days_in_month_spec(year, 2) }
    else if month == 12 { 306 + days_in_month_spec(year, 2) }
    else { 0 }
}

pub open spec fn day_of_year_spec(year: int, month: int, day: int) -> int {
    days_before_month(year, month) + day
}

/// The day_of_year/no-leap face (jcore date.rs:222-244) as the model
/// the two accessors share.
pub open spec fn dol_spec(year: int, month: int, day: int) -> Option<int> {
    let doy: int = day_of_year_spec(year, month, day);
    if is_leap_year_spec(year) && doy == 60 {
        Option::None
    } else if is_leap_year_spec(year) && doy > 60 {
        Option::Some(doy - 1)
    } else {
        Option::Some(doy)
    }
}

/// The from_day_of_year walk (the doc-level semantics of jcore
/// date.rs:131-160): Some(m, d) with day_of_year_spec == day exactly,
/// None when the ordinal runs past the year's end.
pub open spec fn fdy_spec(year: int, day: int) -> Option<(int, int, int)> {
    if !(-9999 <= year && year <= 9999) {
        Option::None
    } else if !(1 <= day && day <= 366) {
        Option::None
    } else if day > days_in_year_spec(year) {
        Option::None
    } else {
        let lp: bool = is_leap_year_spec(year);
        let feb_end: int = if lp { 60 } else { 59 };
        let mk: int = if day <= 31 {
            1
        } else if day <= feb_end {
            2
        } else if lp {
            if day <= 91 { 3 }
            else if day <= 121 { 4 }
            else if day <= 152 { 5 }
            else if day <= 182 { 6 }
            else if day <= 213 { 7 }
            else if day <= 244 { 8 }
            else if day <= 274 { 9 }
            else if day <= 305 { 10 }
            else if day <= 335 { 11 }
            else { 12 }
        } else {
            if day <= 90 { 3 }
            else if day <= 120 { 4 }
            else if day <= 151 { 5 }
            else if day <= 181 { 6 }
            else if day <= 212 { 7 }
            else if day <= 243 { 8 }
            else if day <= 273 { 9 }
            else if day <= 304 { 10 }
            else if day <= 334 { 11 }
            else { 12 }
        };
        let cum: int = if day <= 31 {
            0
        } else if day <= feb_end {
            31
        } else if lp {
            if day <= 91 { 60 }
            else if day <= 121 { 91 }
            else if day <= 152 { 121 }
            else if day <= 182 { 152 }
            else if day <= 213 { 182 }
            else if day <= 244 { 213 }
            else if day <= 274 { 244 }
            else if day <= 305 { 274 }
            else if day <= 335 { 305 }
            else { 335 }
        } else {
            if day <= 90 { 59 }
            else if day <= 120 { 90 }
            else if day <= 151 { 120 }
            else if day <= 181 { 151 }
            else if day <= 212 { 181 }
            else if day <= 243 { 212 }
            else if day <= 273 { 243 }
            else if day <= 304 { 273 }
            else if day <= 334 { 304 }
            else { 334 }
        };
        Option::Some((year, mk, day - cum))
    }
}

/// The from_day_of_year_no_leap walk (jcore date.rs:163-179): the
/// Feb 29 blind shift, then the fdy walk.
pub open spec fn fdynl_spec(
    year: int,
    day: int,
) -> Option<(int, int, int)> {
    if !(-9999 <= year && year <= 9999) {
        Option::None
    } else if !(1 <= day && day <= 365) {
        Option::None
    } else {
        fdy_spec(
            year,
            if day >= 60 && is_leap_year_spec(year) {
                day + 1
            } else {
                day
            },
        )
    }
}

// ===========================================================================
// proof kit: mod absorb, div steps, div corridors, Hermite, the y_star
// linearization
// ===========================================================================

/// mod absorb: adding d-multiples preserves the mod-d residue.
proof fn lemma_mod_addmultiple(a: int, d: int, k: int)
    requires
        d > 0,
    ensures
        (a + d * k) % d == a % d,
{
    lemma_fundamental_div_mod(a, d);
    lemma_fundamental_div_mod(a + d * k, d);
    let qa: int = a / d;
    assert(a == d * qa + a % d);
    lemma_mul_is_distributive_add(d, qa, k);
    assert(d * (qa + k) == d * qa + d * k);
    assert(a + d * k == d * qa + a % d + d * k);
    assert(a + d * k == d * (qa + k) + a % d);
    lemma_fundamental_div_mod_converse(a + d * k, d, qa + k, a % d);
    assert((a + d * k) % d == a % d);
}

proof fn lemma_mod_pow2_absorb(v: int, k: int)
    requires
        0 <= v && v < 4294967296 && 0 <= k,
    ensures
        (v + 4294967296 * k) % 4294967296 == v,
{
    lemma_mod_addmultiple(v, 4294967296, k);
    assert(v + 4294967296 * k >= 0);
    assert((v + 4294967296 * k) % 4294967296 == v % 4294967296);
    lemma_fundamental_div_mod_converse(v, 4294967296, 0, v);
    assert(v % 4294967296 == v);
    assert((v + 4294967296 * k) % 4294967296 == v);
}

/// The y_star of the forward chain (jcore date.rs:509-510:
/// 1461*Y/4 - C + C/4 with C = Y/100) linearized: y_star(Y) ==
/// 365*Y + Y/4 - Y/100 + Y/400 on the domain of valid dates.
proof fn lemma_y_star_linear(Y: int)
    requires
        22800 <= Y && Y <= 42799,
    ensures
        1461 * Y / 4 - Y / 100 + (Y / 100) / 4
            == 365 * Y + Y / 4 - Y / 100 + Y / 400,
{
    // Y >= 22800 > 0, so every division below has nonnegative operands
    assert(Y >= 0);
    lemma_fundamental_div_mod(1461 * Y, 4);
    assert(1461 * Y == 4 * (365 * Y) + Y);
    lemma_fundamental_div_mod_converse(
        1461 * Y,
        4,
        365 * Y + Y / 4,
        Y % 4
    );
    assert((1461 * Y) / 4 == 365 * Y + Y / 4);
    // Hermite with constants: (Y/100)/4 == Y/400
    let qb: int = Y / 100;
    lemma_fundamental_div_mod(Y, 100);
    assert(Y == 100 * qb + Y % 100);
    lemma_fundamental_div_mod(qb, 4);
    let q1: int = qb / 4;
    lemma_fundamental_div_mod(Y, 400);
    assert(qb == 4 * q1 + qb % 4);
    assert(Y == 400 * q1 + (100 * (qb % 4) + Y % 100));
    assert(0 <= 100 * (qb % 4) + Y % 100);
    assert(100 * (qb % 4) + Y % 100 <= 100 * 3 + 99);
    assert(100 * (qb % 4) + Y % 100 < 400);
    lemma_fundamental_div_mod_converse(
        Y,
        400,
        q1,
        100 * (qb % 4) + Y % 100
    );
    assert(Y / 400 == q1);
    assert((Y / 100) / 4 == Y / 400);
}

/// The leap step of the linearized y_star: F(t) = t/4 - t/100 + t/400
/// satisfies F(t) - F(t-1) == is_leap_year_spec(t - 32800) on the
/// domain (32800 is a multiple of 4, 100 and 400, so the three
/// divisibility tests shift out of the offset).
proof fn lemma_f_step_leap(t: int)
    requires
        22801 <= t && t <= 42800,
    ensures
        (is_leap_year_spec(t - 32800)
            ==> (t / 4 - t / 100 + t / 400)
                - ((t - 1) / 4 - (t - 1) / 100 + (t - 1) / 400) == 1)
            && (!is_leap_year_spec(t - 32800)
                ==> (t / 4 - t / 100 + t / 400)
                    - ((t - 1) / 4 - (t - 1) / 100 + (t - 1) / 400)
                        == 0),
{
    // three constant-divisor floor steps: (t/c) - ((t-1)/c) == [c | t]
    lemma_fundamental_div_mod(t, 4);
    lemma_fundamental_div_mod(t - 1, 4);
    assert(if t % 4 == 0 {
        t - 1 == 4 * ((t / 4) - 1) + 3
    } else {
        t - 1 == 4 * (t / 4) + (t % 4 - 1)
    });
    if t % 4 == 0 {
        lemma_fundamental_div_mod_converse(t - 1, 4, (t / 4) - 1, 3);
    } else {
        lemma_fundamental_div_mod_converse(
            t - 1, 4, t / 4, t % 4 - 1
    );
    }
    lemma_fundamental_div_mod(t, 100);
    lemma_fundamental_div_mod(t - 1, 100);
    if t % 100 == 0 {
        lemma_fundamental_div_mod_converse(
            t - 1, 100, (t / 100) - 1, 99
    );
    } else {
        lemma_fundamental_div_mod_converse(
            t - 1, 100, t / 100, t % 100 - 1
    );
    }
    lemma_fundamental_div_mod(t, 400);
    lemma_fundamental_div_mod(t - 1, 400);
    if t % 400 == 0 {
        lemma_fundamental_div_mod_converse(
            t - 1, 400, (t / 400) - 1, 399
    );
    } else {
        lemma_fundamental_div_mod_converse(
            t - 1, 400, t / 400, t % 400 - 1
    );
    }
    // shift the divisibility tests out of the 32800 offset (32800 is a
    // multiple of 4, 100 and 400)
    lemma_mod_addmultiple(t - 32800, 4, 8200);
    lemma_mod_addmultiple(t - 32800, 100, 328);
    lemma_mod_addmultiple(t - 32800, 400, 82);
    assert(t % 4 == (t - 32800) % 4);
    assert(t % 100 == (t - 32800) % 100);
    assert(t % 400 == (t - 32800) % 400);
    if (t - 32800) % 400 == 0 {
        assert(is_leap_year_spec(t - 32800));
        assert(t % 400 == 0 && t % 100 == 0 && t % 4 == 0);
    } else if (t - 32800) % 100 == 0 {
        assert(!is_leap_year_spec(t - 32800));
        assert(t % 100 == 0 && t % 4 == 0);
    } else if (t - 32800) % 4 == 0 {
        assert(is_leap_year_spec(t - 32800));
        assert(t % 4 == 0 && t % 100 != 0);
    } else {
        assert(!is_leap_year_spec(t - 32800));
        assert(t % 4 != 0);
    }
}

// ===========================================================================
// day-of-year table coherence: the upstream table rows are the
// calendar sums, and the doy corridor through the year's end
// ===========================================================================

/// The upstream day_of_year table rows equal the explicit
/// days_in_month_spec sums (February is the only leap-dependent
/// month). This is the correctness heart of jcore date.rs:213-231.
proof fn lemma_doy_row_is_calendar(year: int, month: int)
    requires
        year_iv().contains(year) && 1 <= month && month <= 12,
    ensures
        doy_row(is_leap_year_spec(year), month)
            == days_before_month(year, month),
{
    if is_leap_year_spec(year) {
        assert(days_in_month_spec(year, 2) == 29);
    } else {
        assert(days_in_month_spec(year, 2) == 28);
    }
    // doy_row unfolds to a per-month constant that equals the arm of
    // days_before_month once the February length is pinned.
}

/// The ordinal corridor: day_of_year_spec never runs past the year's
/// end (the claim behind the `1..=366` / `1..=365` doc halves, jcore
/// date.rs:209-210).
proof fn lemma_doy_upper(year: int, month: int, day: int)
    requires
        year_iv().contains(year)
            && 1 <= month
            && month <= 12
            && 1 <= day
            && day <= days_in_month_spec(year, month),
    ensures
        day_of_year_spec(year, month, day)
            <= days_in_year_spec(year),
{
    let dbm: int = days_before_month(year, month);
    assert(days_in_month_spec(year, month) <= 31);
    if is_leap_year_spec(year) {
        assert(days_in_month_spec(year, 2) == 29);
        assert(dbm <= 306 + 29);
        assert(day_of_year_spec(year, month, day) <= 335 + 31);
        assert(day_of_year_spec(year, month, day) <= 366);
        assert(days_in_year_spec(year) == 366);
    } else {
        assert(days_in_month_spec(year, 2) == 28);
        assert(dbm <= 306 + 28);
        assert(day_of_year_spec(year, month, day) <= 334 + 31);
        assert(day_of_year_spec(year, month, day) <= 365);
        assert(days_in_year_spec(year) == 365);
    }
}

// ===========================================================================
// NS bounds: the forward chain lands inside the ued interval for every
// valid date
// ===========================================================================

/// Corridor lemma: ns_epoch_day_spec of a valid triple is a ued value.
proof fn lemma_ns_epoch_bounds(year: int, month: int, day: int)
    requires
        year_iv().contains(year)
            && 1 <= month
            && month <= 12
            && 1 <= day
            && day <= days_in_month_spec(year, month),
    ensures
        ued_iv().contains(ns_epoch_day_spec(year, month, day)),
{
    assert(day <= 31);
    let J: int = if month <= 2 { 1 } else { 0 };
    let Y: int = year + 32800 - J;
    let M: int = if J == 1 { month + 12 } else { month };
    assert(22800 <= Y && Y <= 42799);
    assert(J == 0 ==> Y >= 22801);
    assert(J == 1 ==> Y <= 42798);
    assert(3 <= M && M <= 14);
    lemma_y_star_linear(Y);
    let f: int = Y / 4 - Y / 100 + Y / 400;
    // floor corridors over [22800, 42799] (constant divisors)
    assert(Y >= 4 * 5700 && Y < 4 * 10700);
    assert(5700 <= Y / 4 && Y / 4 <= 10699);
    assert(Y >= 100 * 228 && Y < 100 * 428);
    assert(228 <= Y / 100 && Y / 100 <= 427);
    assert(Y >= 400 * 57 && Y < 400 * 107);
    assert(57 <= Y / 400 && Y / 400 <= 106);
    // m_star corridor (operands positive: 979*M - 2919 >= 18)
    let m_star_f: int = (979 * M - 2919) / 32;
    assert(979 * M - 2919 >= 18);
    assert(0 <= m_star_f && m_star_f <= 337);
    let e_val: int = 365 * Y + f + m_star_f + (day - 1) - 12699422;
    assert(e_val == ns_epoch_day_spec(year, month, day));
    if Y == 22800 {
        // every divisor of the corridor corner divides exactly:
        // 22800/4 == 5700, /100 == 228, /400 == 57
        lemma_fundamental_div_mod_converse(22800, 4, 5700, 0);
        lemma_fundamental_div_mod_converse(22800, 100, 228, 0);
        lemma_fundamental_div_mod_converse(22800, 400, 57, 0);
        assert(J == 1);
        assert(M == 13 || M == 14);
        // m_star(13) == 306, m_star(14) == 337
        lemma_fundamental_div_mod_converse(9808, 32, 306, 16);
        lemma_fundamental_div_mod_converse(10787, 32, 337, 3);
        if M == 13 {
            assert(m_star_f == 306);
        } else {
            assert(m_star_f == 337);
        }
        assert(f == 5700 - 228 + 57);
        assert(365 * 22800 + 5700 - 228 + 57 + 306 + 0 - 12699422
            == -4371587);
        assert(365 * 22800 + (5700 - 228 + 57) + 337 + 30 - 12699422
            <= 2932896);
    } else if Y == 42799 {
        // corner floors: 42799 = 4*10699 + 3, = 100*427 + 99,
        // = 400*106 + 399
        lemma_fundamental_div_mod_converse(42799, 4, 10699, 3);
        lemma_fundamental_div_mod_converse(42799, 100, 427, 99);
        lemma_fundamental_div_mod_converse(42799, 400, 106, 399);
        assert(J == 0);
        assert(3 <= M && M <= 12);
        assert(m_star_f <= 275);
        assert(f == 10699 - 427 + 106);
        assert(365 * 42799 + (10699 - 427 + 106) + 0 + 0 - 12699422
            >= -4371587);
        assert(365 * 42799 + (10699 - 427 + 106) + 275 + 30 - 12699422
            == 2932896);
    } else {
        assert(365 * Y >= 365 * 22801);
        assert(365 * Y <= 365 * 42798);
        assert(f >= 5700 - 427 + 57);
        assert(f <= 10699 - 228 + 106);
        assert(e_val >= 365 * 22801 + (5700 - 427 + 57) + 0 - 12699422);
        assert(e_val >= -4371587);
        assert(e_val <= 365 * 42798 + (10699 - 228 + 106) + 337 + 30
            - 12699422);
        assert(e_val <= 2932896);
    }
}


// ===========================================================================
// the NS forward twin (informative; see the ledger at the file head)
// ===========================================================================

impl Date {

    /// Origin Rust (jcore date.rs:498-523):
    ///     pub const fn to_unix_epoch_day(self) -> UnixEpochDay
    /// Upstream doc (jcore date.rs:495-496):
    ///   Converts a Gregorian date to a Unix epoch day.
    /// Twin note: the J2 steady-state date.rs owns the same i64 body
    /// without informative ensures (the NS family was deferred there);
    /// this twin carries the informative contract, and the agreement of
    /// the two bodies is machine-checked at the row panels below.
    #[allow(non_snake_case)] // upstream Neri-Schneider identifier shapes
    pub exec fn to_unix_epoch_day_ns(self) -> (r: UnixEpochDay)
        requires valid_date(self),
        ensures
            (r.day as int)
                == ns_epoch_day_spec(
                    self.year as int,
                    self.month as int,
                    self.day as int,
                )
                && ued_iv().contains(r.day as int),
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
        let A64: i64 = 1461 * Y;
        let c100: i64 = Y / 100;
        let c4: i64 = c100 / 4;

        let y_div4: i64 = A64 / 4;
        let y_star: i64 = y_div4 - c100 + c4;
        let B64: i64 = 979 * M - 2919;
        let m_star: i64 = B64 / 32;
        let N: i64 = y_star + m_star + D;

        let N_U: i64 = N - K;
        let rv = UnixEpochDay { day: (N_U as i32) };
        proof {
            let yi: int = self.year as int;
            let mi: int = self.month as int;
            let di: int = self.day as int;
            let Ji: int = if mi <= 2 { 1 } else { 0 };
            let Yi: int = yi + 32800 - Ji;
            let Mi: int = if Ji == 1 { mi + 12 } else { mi };
            assert(Y as int == Yi && M as int == Mi && J as int == Ji);
            assert(22800 <= Yi && Yi <= 42799);
            // machine-div bridges (all dividends positive on the domain)
            let Yix: int = Y as int;
            assert(Yix == Yi);
            lemma_fundamental_div_mod(Yix, 100);
            assert((c100 as int) * 100 + ((Y % 100i64) as int) == Yix);
            assert((Y % 100i64) as int == Yix % 100);
            lemma_fundamental_div_mod_converse(
                Yix, 100, (c100 as int), Yix % 100
        );
            assert((c100 as int) == Yi / 100);
            let Aix: int = A64 as int;
            assert(Aix == 1461 * Yi);
            lemma_fundamental_div_mod(Aix, 4);
            assert((y_div4 as int) * 4 + ((A64 % 4i64) as int) == Aix);
            assert((A64 % 4i64) as int == Aix % 4);
            lemma_fundamental_div_mod_converse(
                Aix, 4, (y_div4 as int), Aix % 4
        );
            assert((y_div4 as int) == (1461 * Yi) / 4);
            let Cix: int = c100 as int;
            assert(Cix == Yi / 100);
            lemma_fundamental_div_mod(Cix, 4);
            assert((c4 as int) * 4 + ((c100 % 4i64) as int) == Cix);
            assert((c100 % 4i64) as int == Cix % 4);
            lemma_fundamental_div_mod_converse(
                Cix, 4, (c4 as int), Cix % 4
        );
            assert((c4 as int) == (Yi / 100) / 4);
            let Bix: int = B64 as int;
            assert(Bix == 979 * Mi - 2919);
            assert(Bix >= 18);
            lemma_fundamental_div_mod(Bix, 32);
            assert((m_star as int) * 32 + ((B64 % 32i64) as int) == Bix);
            assert((B64 % 32i64) as int == Bix % 32);
            lemma_fundamental_div_mod_converse(
                Bix, 32, (m_star as int), Bix % 32
        );
            assert((m_star as int) == (979 * Mi - 2919) / 32);
            // the assembled chain equals the spec twin
            let ysix: int = y_star as int;
            assert(ysix
                == (1461 * Yi) / 4 - Yi / 100 + (Yi / 100) / 4);
            let Nix: int = N as int;
            assert(Nix == ysix + (m_star as int) + (D as int));
            assert(ns_epoch_day_spec(yi, mi, di)
                == (1461 * Yi) / 4 - Yi / 100 + (Yi / 100) / 4
                    + (979 * Mi - 2919) / 32
                    + di - 1 - 12699422);
            let Nux: int = N_U as int;
            assert(Nux == Nix - 12699422);
            assert(ns_epoch_day_spec(yi, mi, di) == Nux);
            lemma_ns_epoch_bounds(yi, mi, di);
            assert(ued_iv().contains(Nux));
            assert((rv.day as int) == Nux);
        }
        rv
    }

    /// Origin Rust (jcore date.rs:202-206):
    ///     pub const fn weekday(self) -> Weekday {
    ///         self.to_unix_epoch_day().weekday()
    ///     }
    /// Upstream doc (jcore date.rs:202):
    ///   Returns the weekday corresponding to this date.
    /// Wrapper face (jiff src/civil/date.rs:516-526) delegates 1:1 and
    /// documents the epoch-day-0 anchor: "The Unix epoch was on a
    /// Thursday." -- the wd_of_epoch_day face.
    pub exec fn weekday(self) -> (r: Weekday)
        requires valid_date(self),
        ensures
            wd_monday_one(r) == wd_of_epoch_day(
                ns_epoch_day_spec(
                    self.year as int,
                    self.month as int,
                    self.day as int,
                ),
            ),
    {
        self.to_unix_epoch_day_ns().weekday()
    }
}

impl UnixEpochDay {

    /// Origin Rust (jcore date.rs:904-934):
    ///     pub const fn to_date(self) -> Date
    /// Upstream doc (jcore date.rs:901-902):
    ///   Converts this Unix epoch day to a Gregorian date.
    /// Faithful-identity note (the ledger suspect at the file head):
    /// upstream's `N_U.wrapping_add(K)` wraps to N == self.day + K for
    /// every day in the b::UnixEpochDays range, so this transcription
    /// reads N directly. The upstream u32 subtractions (Y - L + J,
    /// M - 12) and the i16/i8 casts stay the modular-truncation shapes;
    /// on the ued domain the reverse chain components are ensured
    /// exactly (the universal NS reverse validity proof remains
    /// deferred with the roundtrip family, J2/notes.md).
    #[allow(non_snake_case)] // upstream Neri-Schneider identifier shapes
    pub exec fn to_date_ns(self) -> (r: Date)
        requires ued_iv().contains(self.day as int),
        ensures
            (r.year as int) == ns_civil_year(self.day as int)
                && (r.month as int) == ns_civil_month(self.day as int)
                && (r.day as int) == ns_civil_day(self.day as int),
    {
        const K: i64 = 719468 + 146097 * 82;
        const L: i64 = 400 * 82;

        let N: i64 = (self.day as i64) + K;

        let N_1: i64 = 4 * N + 3;
        let r1: i64 = N_1 % 146097;
        let C: i64 = N_1 / 146097;
        let N_C: i64 = r1 / 4;

        let N_2: i64 = 4 * N_C + 3;
        let P_2: i64 = 2939745 * N_2;
        let pr: i64 = P_2 % 4294967296;
        let Z: i64 = P_2 / 4294967296;
        let w2: i64 = pr / 2939745;
        let N_Y: i64 = w2 / 4;
        let Y: i64 = 100 * C + Z;

        let N_3: i64 = 2141 * N_Y + 197913;
        let r3: i64 = N_3 % 65536;
        let M: i64 = N_3 / 65536;
        let D: i64 = r3 / 2141;

        let J: i64 = if N_Y >= 306 { 1 } else { 0 };
        let year: i64 = Y - L + J;
        let month: i64 = if J == 1 { M - 12 } else { M };
        let day: i64 = D + 1;
        proof {
            let e: int = self.day as int;
            let Np: int = e + 12699422;
            assert(N as int == Np);
            let N_1p: int = 4 * Np + 3;
            assert(N as int >= 0);
            assert(N_1 as int == N_1p);
            assert(N_1p >= 0);
            // bridge: C = N_1 / 146097, r1 = N_1 % 146097
            lemma_fundamental_div_mod(N_1p, 146097);
            assert((r1 as int) == N_1p % 146097);
            assert((C as int) * 146097 + (r1 as int) == N_1p);
            lemma_fundamental_div_mod_converse(
                N_1p, 146097, (C as int), (r1 as int)
        );
            assert((C as int) == N_1p / 146097);
            // bridge: N_C = r1 / 4 (r1 == 291840*k + 0 here, but the
            // generic machine-div bridge covers any remainder)
            let r1x: int = r1 as int;
            lemma_fundamental_div_mod(r1x, 4);
            assert((N_C as int) * 4 + ((r1 % 4i64) as int) == r1x);
            assert((r1 % 4i64) as int == r1x % 4);
            lemma_fundamental_div_mod_converse(
                r1x, 4, (N_C as int), r1x % 4
        );
            assert((N_C as int) == (N_1p % 146097) / 4);
            // bridge: pr = P_2 % 2^32, Z = P_2 / 2^32
            let N_2p: int = 4 * ((N_1p % 146097) / 4) + 3;
            assert(N_2 as int == N_2p);
            assert(N_2p <= 4 * 36525 + 3);
            let P_2p: int = 2939745 * N_2p;
            assert(P_2 as int == P_2p);
            lemma_fundamental_div_mod(P_2p, 4294967296);
            assert((pr as int) == P_2p % 4294967296);
            assert((Z as int) * 4294967296 + (pr as int) == P_2p);
            lemma_fundamental_div_mod_converse(
                P_2p, 4294967296, (Z as int), (pr as int)
        );
            assert((Z as int) == P_2p / 4294967296);
            // bridge: w2 = pr / 2939745, N_Y = w2 / 4
            let prx: int = pr as int;
            assert(prx == P_2p % 4294967296);
            lemma_fundamental_div_mod(prx, 2939745);
            assert((w2 as int) * 2939745 + ((pr % 2939745i64) as int) == prx);
            assert((pr % 2939745i64) as int == prx % 2939745);
            lemma_fundamental_div_mod_converse(
                prx, 2939745, (w2 as int), prx % 2939745
        );
            assert((w2 as int) == (P_2p % 4294967296) / 2939745);
            let w2x: int = w2 as int;
            lemma_fundamental_div_mod(w2x, 4);
            assert((N_Y as int) * 4 + ((w2 % 4i64) as int) == w2x);
            assert((w2 % 4i64) as int == w2x % 4);
            lemma_fundamental_div_mod_converse(
                w2x, 4, (N_Y as int), w2x % 4
        );
            assert((N_Y as int)
                == ((P_2p % 4294967296) / 2939745) / 4);
            // bridge: M = N_3 / 65536, r3 = N_3 % 65536
            let N_3p: int = 2141 * (N_Y as int) + 197913;
            assert(N_3 as int == N_3p);
            assert(N_3p >= 0);
            lemma_fundamental_div_mod(N_3p, 65536);
            assert((r3 as int) == N_3p % 65536);
            assert((M as int) * 65536 + (r3 as int) == N_3p);
            lemma_fundamental_div_mod_converse(
                N_3p, 65536, (M as int), (r3 as int)
        );
            assert((M as int) == N_3p / 65536);
            // bridge: D = r3 / 2141
            let r3x: int = r3 as int;
            lemma_fundamental_div_mod(r3x, 2141);
            assert((D as int) * 2141 + ((r3 % 2141i64) as int) == r3x);
            assert((r3 % 2141i64) as int == r3x % 2141);
            lemma_fundamental_div_mod_converse(
                r3x, 2141, (D as int), r3x % 2141
        );
            assert((D as int) == (N_3p % 65536) / 2141);
            let Jx: int = if (N_Y as int) >= 306 { 1 } else { 0 };
            assert(J as int == Jx);
            assert((year as int)
                == 100 * (N_1p / 146097) + P_2p / 4294967296
                    - 32800 + Jx);
            assert((month as int)
                == (if Jx == 1 {
                    N_3p / 65536 - 12
                } else {
                    N_3p / 65536
                }));
            assert((day as int) == (N_3p % 65536) / 2141 + 1);
            // spec component agreement
            assert(ns_civil_year(e)
                == 100 * (N_1p / 146097) + P_2p / 4294967296
                    - 32800 + Jx);
            assert(ns_civil_month(e)
                == (if Jx == 1 {
                    N_3p / 65536 - 12
                } else {
                    N_3p / 65536
                }));
            assert(ns_civil_day(e) == (N_3p % 65536) / 2141 + 1);
        }
        Date {
            year: (year as i16),
            month: (month as i8),
            day: (day as i8),
        }
    }

    /// Origin Rust (jcore date.rs:733-772):
    ///     pub const fn weekday(&self) -> Weekday
    /// Upstream doc (jcore date.rs:733):
    ///   Returns the day of the week for this epoch day.
    /// Body provenance (the in-function comments, jcore date.rs:736-763):
    ///   Fast technique to obtain weekday 1..7 (Mon..Sun) directly via
    ///   an add-mul-shift. Relies on the fact that the Unix epoch was a
    ///   Thursday and that 7 is a Mersenne number.
    ///   Accurate over a limited range (-89478489 to 89478489) which is
    ///   -243014-03-21 (Tue) to 246953-10-13 (Sat). This exceeds Jiff's
    ///   range.
    /// with M = 613566757 (the div_ceil(2^32, 7) const block "assert!(
    /// n == 613_566_757)") and Z = 0x90000000 ("Magic add"). The u32
    /// bit-cast, the wrapping mul-add and the 2^32 wrap materialize at
    /// i64 on the ued domain (the products stay under 2^63), and the
    /// final unwrapr ("weekday must be in range 1..=7") is discharged
    /// by the lane proof below.
    pub exec fn weekday(self) -> (r: Weekday)
        requires ued_iv().contains(self.day as int),
        ensures
            wd_monday_one(r) == wd_of_epoch_day(self.day as int),
    {
        let e: i64 = self.day as i64;
        let rd: i64 = if e < 0 {
            e + 4294967296i64
        } else {
            e
        };
        let pr64: i64 = rd * 613566757i64 + 2415919104i64;
        let t: i64 = pr64 % 4294967296i64;
        let w: i64 = t / 536870912i64; // 2^29
        proof {
            let ei: int = self.day as int;
            lemma_wd_shift(ei);
            assert((rd as int) == (if e < 0 {
                ei + 4294967296
            } else {
                ei
            }));
            assert((rd as int) >= 0 && (rd as int) < 4294967296);
            let A: int = (pr64 as int);
            assert(A == (rd as int) * 613566757 + 2415919104);
            assert(A > 0);
            assert((t as int) == A % 4294967296);
            assert((t as int)
                == (if e < 0 {
                    (ei + 4294967296) * 613566757 + 2415919104
                } else {
                    ei * 613566757 + 2415919104
                }) % 4294967296);
            let ti: int = t as int;
            lemma_fundamental_div_mod(ti, 536870912);
            assert((w as int) * 536870912 + ((t % 536870912i64) as int) == ti);
            assert((t % 536870912i64) as int == ti % 536870912);
            lemma_fundamental_div_mod_converse(
                ti, 536870912, (w as int), ti % 536870912
        );
            assert((w as int) == ti / 536870912);
            assert((w as int) == wd_shift_lane(ei));
            assert(1 <= (w as int) && (w as int) <= 7);
        }
        let Some(wk) = Weekday::from_monday_one_offset(w as i8) else {
            proof {
                assert(false);
            }
            unreachable!()
        };
        wk
    }
}


// ===========================================================================
// the weekday shift lane core: 7-way residue split with the products
// folded per arm (the probe-verified shape)
// ===========================================================================

/// Pure-integer core of the weekday shift lane: over the ued interval
/// the add-mul-shift reads back the Thursday-anchored residue face,
/// 1..=7 (Mon..Sun).
proof fn lemma_wd_shift(e: int)
    requires
        -4371587 <= e && e <= 2932896,
    ensures
        1 <= wd_shift_lane(e)
            && wd_shift_lane(e) <= 7
            && wd_shift_lane(e) == wd_of_epoch_day(e),
{
    lemma_fundamental_div_mod(e, 7);
    let q: int = e / 7;
    let rr: int = e % 7;
    assert(e == 7 * q + rr && 0 <= rr < 7);
    assert(q >= -624513 && q <= 418985);
    assert(-1873539 <= 3 * q && 3 * q <= 1256955);
    let neg: int = if e < 0 { 1 } else { 0 };
    // 7 * 613566757 == 2^32 + 3, the anchor of the whole lane.
    assert(7 * 613566757 == 4294967299);
    assert(e * 613566757 == (7 * q + rr) * 613566757);
    lemma_mul_is_distributive_add_other_way(e, 4294967296 * neg, 613566757);
    assert(
        (e + 4294967296 * neg) * 613566757
            == e * 613566757 + 4294967296 * neg * 613566757
    );
    lemma_mul_is_distributive_add_other_way(7 * q, rr, 613566757);
    assert((7 * q + rr) * 613566757 == 7 * q * 613566757 + rr * 613566757);
    lemma_mul_is_associative(7, q, 613566757);
    assert(7 * q * 613566757 == 7 * (q * 613566757));
    lemma_mul_is_commutative(7, q * 613566757);
    assert(7 * (q * 613566757) == (q * 613566757) * 7);
    lemma_mul_is_associative(q, 613566757, 7);
    assert((q * 613566757) * 7 == q * (613566757 * 7));
    assert(613566757 * 7 == 4294967299);
    assert(q * (613566757 * 7) == q * 4294967299);
    lemma_mul_is_distributive_add(q, 4294967296, 3);
    assert(q * 4294967299 == 4294967296 * q + 3 * q);
    assert(7 * q * 613566757 == 4294967296 * q + 3 * q);
    assert(if neg == 1 {
        4294967296 * neg * 613566757 == 4294967296 * 613566757
    } else {
        4294967296 * neg * 613566757 == 0
    });
    let small: int = if rr < 4 { 0 } else { 4294967296 };
    let big_rr: int = rr * 613566757 + 2415919104 - small;
    assert(if e < 0 {
        (e + 4294967296) * 613566757 + 2415919104
    } else {
        e * 613566757 + 2415919104
    } == (3 * q + big_rr)
        + 4294967296 * (q + neg * 613566757 + small / 4294967296));
    assert(if neg == 0 { q >= 0 } else { q + neg * 613566757 >= 0 });
    if rr == 0 {
        let big: int = 2415919104;
        assert(big_rr == big);
        assert(2147483648 <= 3 * q + big && 3 * q + big < 2684354560);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757);
        assert((3 * q + big) / 536870912 == 4);
        assert(wd_shift_lane(e) == 4);
        assert(wd_of_epoch_day(e) == 4);
    } else if rr == 1 {
        let big: int = 3029485861;
        assert(big_rr == big);
        assert(2684354560 <= 3 * q + big && 3 * q + big < 3221225472);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757);
        assert((3 * q + big) / 536870912 == 5);
        assert(wd_shift_lane(e) == 5);
        assert(wd_of_epoch_day(e) == 5);
    } else if rr == 2 {
        let big: int = 3643052618;
        assert(big_rr == big);
        assert(3221225472 <= 3 * q + big && 3 * q + big < 3758096384);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757);
        assert((3 * q + big) / 536870912 == 6);
        assert(wd_shift_lane(e) == 6);
        assert(wd_of_epoch_day(e) == 6);
    } else if rr == 3 {
        let big: int = 4256619375;
        assert(big_rr == big);
        assert(3758096384 <= 3 * q + big && 3 * q + big < 4294967296);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757);
        assert((3 * q + big) / 536870912 == 7);
        assert(wd_shift_lane(e) == 7);
        assert(wd_of_epoch_day(e) == 7);
    } else if rr == 4 {
        let big: int = 575218836;
        assert(big_rr == big);
        assert(536870912 <= 3 * q + big && 3 * q + big < 1073741824);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757 + 1);
        assert((3 * q + big) / 536870912 == 1);
        assert(wd_shift_lane(e) == 1);
        assert(wd_of_epoch_day(e) == 1);
    } else if rr == 5 {
        let big: int = 1188785593;
        assert(big_rr == big);
        assert(1073741824 <= 3 * q + big && 3 * q + big < 1610612736);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757 + 1);
        assert((3 * q + big) / 536870912 == 2);
        assert(wd_shift_lane(e) == 2);
        assert(wd_of_epoch_day(e) == 2);
    } else {
        let big: int = 1802352350;
        assert(big_rr == big);
        assert(1610612736 <= 3 * q + big && 3 * q + big < 2147483648);
        lemma_mod_pow2_absorb(3 * q + big, q + neg * 613566757 + 1);
        assert((3 * q + big) / 536870912 == 3);
        assert(wd_shift_lane(e) == 3);
        assert(wd_of_epoch_day(e) == 3);
    }
}

// ===========================================================================
// Date::MIN/MAX consts (jcore date.rs:29-47)
// ===========================================================================

impl Date {

    /// Origin Rust (jcore date.rs:25-47):
    ///     pub const MIN: Date = {
    ///         let min = UnixEpochDay::MIN.to_date();
    ///         assert!(min.year() == -9999);
    ///         assert!(min.month() == 1);
    ///         assert!(min.day() == 1);
    ///         min
    ///     };
    /// Upstream doc (jcore date.rs:21-24):
    ///   The minimum allowed Gregorian date.
    ///   This is guaranteed to be equivalent to [`UnixEpochDay::MIN`]
    ///   when converted to a Unix epoch day.
    /// The const face pins the asserted literal triple; the equivalence
    /// claim is machine-checked at the panel below (upstream defines
    /// the consts through const-evaluated NS calls, and this build has
    /// no const-fn verification -- the J2 finding-14 pattern).
    pub const MIN: Date = Date { year: -9999, month: 1, day: 1 };

    /// Origin Rust (jcore date.rs:33-47):
    ///     pub const MAX: Date = {
    ///         let max = UnixEpochDay::MAX.to_date();
    ///         assert!(max.year() == 9999);
    ///         assert!(max.month() == 12);
    ///         assert!(max.day() == 31);
    ///         max
    ///     };
    /// Upstream doc (jcore date.rs:31-34):
    ///   The maximum allowed Gregorian date.
    ///   This is guaranteed to be equivalent to [`UnixEpochDay::MAX`]
    ///   when converted to a Unix epoch day.
    pub const MAX: Date = Date { year: 9999, month: 12, day: 31 };
}

// ===========================================================================
// Era (jiff src/civil/mod.rs:116-140) and Date::era_year (main-crate
// date.rs:426-472)
// ===========================================================================

/// Origin Rust (jiff src/civil/mod.rs:134-140):
///     pub enum Era { BCE, CE }
/// Upstream doc (jiff src/civil/mod.rs:116-132):
///   The era corresponding to a particular year.
///   The BCE era corresponds to years less than or equal to `0`, while
///   the CE era corresponds to years greater than `0`.
///   In particular, this crate allows years to be negative and also to
///   be `0`, which is contrary to the common practice of excluding the
///   year `0` when writing dates for the Gregorian calendar. Moreover,
///   common practice eschews negative years in favor of labeling a year
///   with an era notation. That is, the year `1 BCE` is year `0` in
///   this crate. The year `2 BCE` is the year `-1` in this crate.
///   To get the year in its era format, use [`Date::era_year`].
#[derive(Clone, Copy)]
pub enum Era {
    ///   The "before common era" era.
    ///   This corresponds to all years less than or equal to `0`.
    ///   This is precisely equivalent to the "BC" or "before Christ"
    ///   era. (upstream variant doc, mod.rs:141-146)
    BCE,
    ///   The "common era" era.
    ///   This corresponds to all years greater than `0`.
    ///   This is precisely equivalent to the "AD" or "anno Domini" or
    ///   "in the year of the Lord" era. (mod.rs:147-153)
    CE,
}

impl Date {

    /// Origin Rust (jiff src/civil/date.rs:459-472):
    ///     pub fn era_year(self) -> (i16, Era) {
    ///         let year = self.year();
    ///         if year >= 1 {
    ///             (year, Era::CE)
    ///         } else {
    ///             // We specifically ensure our min/max bounds on `Year`
    ///             // always leave room in its representation to add or
    ///             // subtract 1, so this will never fail.
    ///             let era_year = -year + 1;
    ///             (era_year, Era::BCE)
    ///         }
    ///     }
    /// Upstream doc (jiff src/civil/date.rs:426-440):
    ///   Returns the year and its era.
    ///   This crate specifically allows years to be negative or `0`,
    ///   where as years written for the Gregorian calendar are always
    ///   positive and greater than `0`. In the Gregorian calendar, the
    ///   era labels `BCE` and `CE` are used to disambiguate between
    ///   years less than or equal to `0` and years greater than `0`,
    ///   respectively.
    ///   The crate is designed this way so that years in the latest era
    ///   (that is, `CE`) are aligned with years in this crate.
    ///   The year returned is guaranteed to be in the range
    ///   `1..=10000`.
    pub exec fn era_year(self) -> (r: (i16, Era))
        requires valid_date(self),
        ensures
            (r.1 is CE <==> 1 <= self.year as int)
                && (r.1 is BCE <==> self.year as int <= 0)
                && (r.1 is CE ==> (r.0 as int) == self.year as int)
                && (r.1 is BCE
                    ==> (r.0 as int)
                        == 1 - self.year as int)
                && 1 <= r.0 as int
                && (r.0 as int) <= 10000,
    {
        if self.year >= 1i16 {
            (self.year, Era::CE)
        } else {
            (1i16 - self.year, Era::BCE)
        }
    }
}


// ===========================================================================
// the day-of-year accessors and the from_day_of_year walks
// ===========================================================================

impl Date {

    /// Origin Rust (jcore date.rs:213-231):
    ///     pub const fn day_of_year(self) -> i16 {
    ///         const DAYS_BY_MONTH_NO_LEAP: [i16; 14] =
    ///             [0, 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304,
    ///              334, 365];
    ///         const DAYS_BY_MONTH_LEAP: [i16; 14] =
    ///             [0, 0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305,
    ///              335, 366];
    ///         const TABLES: [[i16; 14]; 2] =
    ///             [DAYS_BY_MONTH_NO_LEAP, DAYS_BY_MONTH_LEAP];
    ///         TABLES[self.in_leap_year() as usize][self.month() as usize]
    ///             + (self.day() as i16)
    ///     }
    /// Upstream doc (jcore date.rs:208-211):
    ///   Returns the ordinal day of the year that this date resides in.
    ///   For leap years, this always returns a value in the range
    ///   `1..=366`. Otherwise, the value is in the range `1..=365`.
    /// Wrapper doc examples (jiff src/civil/date.rs:541-549):
    ///   let d = date(2006, 8, 24);  assert_eq!(d.day_of_year(), 236);
    ///   let d = date(2023, 12, 31); assert_eq!(d.day_of_year(), 365);
    ///   let d = date(2024, 12, 31); assert_eq!(d.day_of_year(), 366);
    /// The two dead 0/1 slots of the 14-wide upstream tables vanish in
    /// the match transcription (rows 1..=12 are the live ones).
    pub exec fn day_of_year(self) -> (r: i16)
        requires valid_date(self),
        ensures
            (r as int)
                == day_of_year_spec(
                    self.year as int,
                    self.month as int,
                    self.day as int,
                )
                && 1 <= r as int
                && (r as int)
                    <= days_in_year_spec(self.year as int),
    {
        let lp: bool = self.in_leap_year();
        let tbl: i16 = if lp {
            match self.month {
                1 => 0i16,
                2 => 31i16,
                3 => 60i16,
                4 => 91i16,
                5 => 121i16,
                6 => 152i16,
                7 => 182i16,
                8 => 213i16,
                9 => 244i16,
                10 => 274i16,
                11 => 305i16,
                _ => 335i16,
            }
        } else {
            match self.month {
                1 => 0i16,
                2 => 31i16,
                3 => 59i16,
                4 => 90i16,
                5 => 120i16,
                6 => 151i16,
                7 => 181i16,
                8 => 212i16,
                9 => 243i16,
                10 => 273i16,
                11 => 304i16,
                _ => 334i16,
            }
        };
        let r: i16 = tbl + (self.day as i16);
        proof {
            let y: int = self.year as int;
            let m: int = self.month as int;
            let d: int = self.day as int;
            assert(lp == is_leap_year_spec(y));
            assert(1 <= m && m <= 12);
            let tblx: int = tbl as int;
            let rx: int = r as int;
            let want: int = if is_leap_year_spec(y) {
                if m == 1 { 0 }
                else if m == 2 { 31 }
                else if m == 3 { 60 }
                else if m == 4 { 91 }
                else if m == 5 { 121 }
                else if m == 6 { 152 }
                else if m == 7 { 182 }
                else if m == 8 { 213 }
                else if m == 9 { 244 }
                else if m == 10 { 274 }
                else if m == 11 { 305 }
                else { 335 }
            } else {
                if m == 1 { 0 }
                else if m == 2 { 31 }
                else if m == 3 { 59 }
                else if m == 4 { 90 }
                else if m == 5 { 120 }
                else if m == 6 { 151 }
                else if m == 7 { 181 }
                else if m == 8 { 212 }
                else if m == 9 { 243 }
                else if m == 10 { 273 }
                else if m == 11 { 304 }
                else { 334 }
            };
            assert(tblx == want);
            if is_leap_year_spec(y) {
                assert(days_in_month_spec(y, 2) == 29);
            } else {
                assert(days_in_month_spec(y, 2) == 28);
            }
            assert(days_before_month(y, m) == tblx);
            assert(rx == tblx + d);
            assert(day_of_year_spec(y, m, d) == rx);
            assert(days_before_month(y, m) <= 306
                + days_in_month_spec(y, 2));
            assert(d <= 31);
            lemma_doy_upper(y, m, d);
        }
        r
    }

    /// Origin Rust (jcore date.rs:234-244):
    ///     pub const fn day_of_year_no_leap(self) -> Option<i16> {
    ///         let mut days = self.day_of_year();
    ///         if self.in_leap_year() {
    ///             // day=60 is Feb 29
    ///             if days == 60 {
    ///                 return None;
    ///             } else if days > 60 {
    ///                 days -= 1;
    ///             }
    ///         }
    ///         Some(days)
    ///     }
    /// Upstream doc (jcore date.rs:222-231):
    ///   Returns the ordinal day of the year that this date resides in,
    ///   but ignores leap years.
    ///   That is, the range of possible values returned by this routine
    ///   is `1..=365`, even if this date resides in a leap year. If
    ///   this date is February 29, then this routine returns `None`.
    ///   The value `365` always corresponds to the last day in the
    ///   year, December 31, even for leap years.
    pub exec fn day_of_year_no_leap(self) -> (r: Option<i16>)
        requires valid_date(self),
        ensures
            match r {
                Option::Some(v) => {
                    1 <= v as int
                        && (v as int) <= 365
                        && dol_spec(
                            self.year as int,
                            self.month as int,
                            self.day as int,
                        ) == Option::Some(v as int)
                }
                Option::None => {
                    dol_spec(
                        self.year as int,
                        self.month as int,
                        self.day as int,
                    ) == Option::None
                }
            },
    {
        let mut days: i16 = self.day_of_year();
        if self.in_leap_year() {
            // day=60 is Feb 29 (upstream comment)
            if days == 60 {
                return Option::None;
            } else if days > 60 {
                days = days - 1;
            }
        }
        proof {
            let y: int = self.year as int;
            let m: int = self.month as int;
            let d: int = self.day as int;
            let doy: int = day_of_year_spec(y, m, d);
            lemma_doy_upper(y, m, d);
            assert(if is_leap_year_spec(y) && doy > 60 {
                doy <= 366
            } else {
                doy <= 365
            });
            assert((days as int) <= 365);
        }
        Option::Some(days)
    }

    /// Origin Rust (jcore date.rs:131-160):
    ///     pub const fn from_day_of_year(
    ///         year: i16, day: i16,
    ///     ) -> Result<Date, RangeError> {
    ///         let year = rtry!(b::Year::checkc(year as i64));
    ///         let day = rtry!(b::DayOfYear::checkc(day as i64));
    ///         let start = Date { year, month: 1, day: 1 }
    ///             .to_unix_epoch_day();
    ///         let end = match start.checked_add(day as i32 - 1) {
    ///             Ok(end) => end.to_date(),
    ///             Err(_) => {
    ///                 rbail!(SpecialBoundsError::DateInvalidDayOfYear)
    ///             }
    ///         };
    ///         if year != end.year {
    ///             debug_assert!(day == 366);
    ///             debug_assert!(!civil::is_leap_year(year));
    ///             rbail!(SpecialBoundsError::DateInvalidDayOfYear)
    ///         }
    ///         Ok(end)
    ///     }
    /// Upstream doc (jcore date.rs:124-129):
    ///   Returns the date corresponding to the day of the given year.
    ///   The day of the year should be a value in `1..=366`, with `366`
    ///   only being valid if `year` is a leap year.
    ///   Returns an error if `year` is not in the range specified by
    ///   [`Year`], or if `day` is invalid for the given year.
    /// Transcription ledger (file head): the month-table walk replaces
    /// the epoch-day bridge; the doc contract carries fully.
    pub exec fn from_day_of_year(year: i16, day: i16) -> (r: Option<Date>)
        ensures
            match r {
                Option::Some(d) => {
                    (d.year as int) == (year as int)
                        && valid_date(d)
                        && fdy_spec(year as int, day as int)
                            == Option::Some((
                                d.year as int,
                                d.month as int,
                                d.day as int,
                            ))
                        && day_of_year_spec(
                            d.year as int,
                            d.month as int,
                            d.day as int,
                        ) == (day as int)
                }
                Option::None => {
                    fdy_spec(year as int, day as int) == Option::None
                }
            },
    {
        let Some(y) = Year::checkc(year as i64) else {
            proof {
                assert(fdy_spec(year as int, day as int)
                    == Option::None);
            }
            return Option::None;
        };
        if !(1 <= day && day <= 366) {
            proof {
                assert(fdy_spec(year as int, day as int)
                    == Option::None);
            }
            return Option::None;
        }
        if (day as i32) > (days_in_year(y) as i32) {
            proof {
                assert(fdy_spec(year as int, day as int)
                    == Option::None);
            }
            return Option::None;
        }
        let leap: bool = is_leap_year(y);
        let cum: i16 = if leap {
            if day <= 31 { 0i16 }
            else if day <= 60 { 31i16 }
            else if day <= 91 { 60i16 }
            else if day <= 121 { 91i16 }
            else if day <= 152 { 121i16 }
            else if day <= 182 { 152i16 }
            else if day <= 213 { 182i16 }
            else if day <= 244 { 213i16 }
            else if day <= 274 { 244i16 }
            else if day <= 305 { 274i16 }
            else if day <= 335 { 305i16 }
            else { 335i16 }
        } else {
            if day <= 31 { 0i16 }
            else if day <= 59 { 31i16 }
            else if day <= 90 { 59i16 }
            else if day <= 120 { 90i16 }
            else if day <= 151 { 120i16 }
            else if day <= 181 { 151i16 }
            else if day <= 212 { 181i16 }
            else if day <= 243 { 212i16 }
            else if day <= 273 { 243i16 }
            else if day <= 304 { 273i16 }
            else if day <= 334 { 304i16 }
            else { 334i16 }
        };
        let m: i8 = if leap {
            if day <= 31 { 1i8 }
            else if day <= 60 { 2i8 }
            else if day <= 91 { 3i8 }
            else if day <= 121 { 4i8 }
            else if day <= 152 { 5i8 }
            else if day <= 182 { 6i8 }
            else if day <= 213 { 7i8 }
            else if day <= 244 { 8i8 }
            else if day <= 274 { 9i8 }
            else if day <= 305 { 10i8 }
            else if day <= 335 { 11i8 }
            else { 12i8 }
        } else {
            if day <= 31 { 1i8 }
            else if day <= 59 { 2i8 }
            else if day <= 90 { 3i8 }
            else if day <= 120 { 4i8 }
            else if day <= 151 { 5i8 }
            else if day <= 181 { 6i8 }
            else if day <= 212 { 7i8 }
            else if day <= 243 { 8i8 }
            else if day <= 273 { 9i8 }
            else if day <= 304 { 10i8 }
            else if day <= 334 { 11i8 }
            else { 12i8 }
        };
        let dd: i8 = (day - cum) as i8;
        let d2: Date = Date { year: y, month: m, day: dd };
        proof {
            let dy: int = day as int;
            let lp: bool = is_leap_year_spec(y as int);
            assert(lp == leap);
            if lp {
                assert(days_in_month_spec(y as int, 2) == 29);
            } else {
                assert(days_in_month_spec(y as int, 2) == 28);
            }
            assert((cum as int) == days_before_month(y as int, m as int));
            assert(1 <= dy - (cum as int));
            assert((dy - (cum as int))
                <= days_in_month_spec(y as int, m as int));
            assert(valid_date(d2));
            assert(fdy_spec(y as int, dy)
                == Option::Some((y as int, m as int, dd as int)));
            assert(day_of_year_spec(y as int, m as int, dd as int) == dy);
            assert((d2.year as int) == (year as int));
        }
        Option::Some(d2)
    }

    /// Origin Rust (jcore date.rs:163-179):
    ///     pub const fn from_day_of_year_no_leap(
    ///         year: i16, day: i16,
    ///     ) -> Result<Date, RangeError> {
    ///         let year = rtry!(b::Year::checkc(year as i64));
    ///         let mut day = rtry!(b::DayOfYearNoLeap::checkc(day as i64));
    ///         if day >= 60 && civil::is_leap_year(year) {
    ///             day += 1;
    ///         }
    ///         Ok(unwrapr!(Date::from_day_of_year(year, day),
    ///             "valid day of year"))
    ///     }
    /// Upstream doc (jcore date.rs:153-160):
    ///   Returns the date corresponding to the day of the given year.
    ///   The day of the year must be a value in `1..=365`, with
    ///   February 29 being completely ignored. That is, it is guaranteed
    ///   that February 29 will never be returned by this function. It is
    ///   impossible.
    ///   Returns an error if `year` is not in the range specified by
    ///   [`Year`], or if `day` is outside the range `1..=365`.
    /// The bounds face is b::DayOfYearNoLeap (jcore bounds.rs:169-171).
    pub exec fn from_day_of_year_no_leap(
        year: i16,
        day: i16,
    ) -> (r: Option<Date>)
        ensures
            match r {
                Option::Some(d) => {
                    (d.year as int) == (year as int)
                        && valid_date(d)
                        && !(d.month as int == 2
                            && d.day as int == 29)
                        && ({
                            let doy2: int = day_of_year_spec(
                                d.year as int,
                                d.month as int,
                                d.day as int
                        );
                            let add: int
                                = if is_leap_year_spec(d.year as int)
                                    && doy2 > 60
                                {
                                    1
                                } else {
                                    0
                                };
                            doy2 == (day as int) + add
                        })
                        && fdynl_spec(year as int, day as int)
                            == Option::Some((
                                d.year as int,
                                d.month as int,
                                d.day as int,
                            ))
                }
                Option::None => {
                    fdynl_spec(year as int, day as int)
                        == Option::None
                }
            },
    {
        let Some(y) = Year::checkc(year as i64) else {
            proof {
                assert(fdynl_spec(year as int, day as int)
                    == Option::None);
            }
            return Option::None;
        };
        if !(1 <= day && day <= 365) {
            proof {
                assert(fdynl_spec(year as int, day as int)
                    == Option::None);
            }
            return Option::None;
        }
        let mut day_v: i16 = day;
        if day_v >= 60 && is_leap_year(y) {
            day_v = day_v + 1;
        }
        // The boundary check above guarantees this always succeeds
        // (upstream unwrapr comment, jcore date.rs:171-172).
        Date::from_day_of_year(y, day_v)
    }
}

// ===========================================================================
// row panels (upstream test and doc rows, z3 ground-folds)
// ===========================================================================

/// Upstream test rows (jcore date.rs:1561-1575, unix_epoch_day_weekday):
/// the 2026-02-14..21 sweep of date(2026, 2, day).weekday(), plus the
/// wrapper doc anchor (date(1970, 1, 1) is Thursday, jiff
/// src/civil/date.rs:513-515).
exec fn panel_weekday_rows() -> (ok: bool)
    ensures ok == true,
{
    let d14 = date(2026, 2, 14).weekday();
    let d15 = date(2026, 2, 15).weekday();
    let d16 = date(2026, 2, 16).weekday();
    let d17 = date(2026, 2, 17).weekday();
    let d18 = date(2026, 2, 18).weekday();
    let d19 = date(2026, 2, 19).weekday();
    let d20 = date(2026, 2, 20).weekday();
    let d21 = date(2026, 2, 21).weekday();
    let e70 = date(1970, 1, 1).weekday();
    proof {
        assert(d14 is Saturday);
        assert(d15 is Sunday);
        assert(d16 is Monday);
        assert(d17 is Tuesday);
        assert(d18 is Wednesday);
        assert(d19 is Thursday);
        assert(d20 is Friday);
        assert(d21 is Saturday);
        assert(e70 is Thursday);
        assert(wd_monday_one(d14) == 6);
        assert(wd_monday_one(e70) == 4);
    }
    true
}

/// Upstream wrapper doc rows (jiff src/civil/date.rs:541-549,
/// day_of_year / day_of_year_no_leap examples) and the blind-60
/// boundary rows from the jcore sweeps (date.rs:1477-1516).
exec fn panel_doy_rows() -> (ok: bool)
    ensures ok == true,
{
    let d1 = date(2006, 8, 24).day_of_year();
    let d2 = date(2023, 12, 31).day_of_year();
    let d3 = date(2024, 12, 31).day_of_year();
    let n1 = date(2006, 8, 24).day_of_year_no_leap();
    let n2 = date(2023, 12, 31).day_of_year_no_leap();
    let n3 = date(2024, 12, 31).day_of_year_no_leap();
    let n4 = date(2024, 2, 29).day_of_year_no_leap();
    proof {
        assert(d1 as int == 236);
        assert(d2 as int == 365);
        assert(d3 as int == 366);
        assert(n1 == Option::Some(236));
        assert(n2 == Option::Some(365));
        assert(n3 == Option::Some(365));
        assert(n4 == Option::None);
    }
    true
}

/// Boundary rows exercising every arm family of the two walks: the
/// leap Feb shoulder (59, 60 -> Feb 29, 61 -> Mar 1), the non-leap Feb
/// shoulder (59 -> Mar 1 in doy terms), the year ends (366 -> Dec 31 in
/// a leap year, rejected in a non-leap year), and the no-leap blind
/// shift (leap years: 59 -> Feb 28, 60 -> Mar 1).
exec fn panel_fdy_rows() -> (ok: bool)
    ensures ok == true,
{
    let x1 = date(2024, 2, 29);
    let x2 = date(2024, 3, 1);
    let x3 = date(2024, 12, 31);
    let x4 = date(2023, 12, 31);
    let x5 = date(2023, 2, 28);
    let x6 = date(2024, 2, 28);
    let f1 = Date::from_day_of_year(2024, 60);
    let f2 = Date::from_day_of_year(2024, 61);
    let f3 = Date::from_day_of_year(2024, 366);
    let f4 = Date::from_day_of_year(2023, 365);
    let f5 = Date::from_day_of_year(2023, 366);
    let f6 = Date::from_day_of_year(2023, 59);
    let f7 = Date::from_day_of_year(2024, 59);
    let n5 = Date::from_day_of_year_no_leap(2023, 59);
    let n6 = Date::from_day_of_year_no_leap(2024, 59);
    let n7 = Date::from_day_of_year_no_leap(2024, 60);
    proof {
        assert(f1 == Option::Some(x1));
        assert(f2 == Option::Some(x2));
        assert(f3 == Option::Some(x3));
        assert(f4 == Option::Some(x4));
        assert(f5 == Option::None);
        assert(f6 == Option::Some(x5));
        assert(f7 == Option::Some(x6));
        assert(n5 == Option::Some(x5));
        assert(n6 == Option::Some(x6));
        assert(n7 == Option::Some(x2));
    }
    true
}


// ===========================================================================
// the year-step and within-year corridor lemmas of the NS forward chain
// (the calendar-remainder claims Date::since/until and the ISO faces
// consume)
// ===========================================================================

/// Jan 1 steps by the year length at the NS chain level.
proof fn lemma_ns_year_step(y: int)
    requires
        -9999 <= y && y <= 9998,
    ensures
        ns_epoch_day_spec(y + 1, 1, 1)
            - ns_epoch_day_spec(y, 1, 1)
            == days_in_year_spec(y),
{
    // both sides are Jan (J == 1), same M == 13, D == 0; only Y steps
    let Ya: int = y + 32800 - 1;
    let Yb: int = y + 1 + 32800 - 1;
    assert(Yb == Ya + 1);
    assert(Yb >= 22800 && Yb <= 42800);
    lemma_y_star_linear(Ya);
    lemma_y_star_linear(Yb);
    lemma_f_step_leap(Yb);
    if is_leap_year_spec(y) {
        assert(
            (Yb / 4 - Yb / 100 + Yb / 400)
                - ((Yb - 1) / 4 - (Yb - 1) / 100 + (Yb - 1) / 400)
                == 1
    );
    } else {
        assert(
            (Yb / 4 - Yb / 100 + Yb / 400)
                - ((Yb - 1) / 4 - (Yb - 1) / 100 + (Yb - 1) / 400)
                == 0
    );
    }
    assert(Yb - 1 == Ya);
    assert(
        1461 * Ya / 4 - Ya / 100 + (Ya / 100) / 4
            == 365 * Ya + Ya / 4 - Ya / 100 + Ya / 400
    );
    assert(
        1461 * Yb / 4 - Yb / 100 + (Yb / 100) / 4
            == 365 * Yb + Yb / 4 - Yb / 100 + Yb / 400
    );
    assert(365 * Yb - 365 * Ya == 365);
    assert(
        ns_epoch_day_spec(y + 1, 1, 1)
            == 365 * Yb + Yb / 4 - Yb / 100 + Yb / 400
                + (979 * 13 - 2919) / 32 - 12699422
    );
    assert(
        ns_epoch_day_spec(y, 1, 1)
            == 365 * Ya + Ya / 4 - Ya / 100 + Ya / 400
                + (979 * 13 - 2919) / 32 - 12699422
    );
    assert(Yb - 32800 == y);
    assert(is_leap_year_spec(y) == is_leap_year_spec(Yb - 32800));
    if is_leap_year_spec(y) {
        assert(days_in_year_spec(y) == 366);
        assert(
            ns_epoch_day_spec(y + 1, 1, 1)
                - ns_epoch_day_spec(y, 1, 1)
                == 365 + 1
    );
    } else {
        assert(days_in_year_spec(y) == 365);
        assert(
            ns_epoch_day_spec(y + 1, 1, 1)
                - ns_epoch_day_spec(y, 1, 1)
                == 365
    );
    }
}

/// A date's NS epoch day is the year's Jan 1 epoch day plus the
/// day-of-year minus one.
proof fn lemma_ns_within_year(y: int, m: int, dd: int)
    requires
        -9999 <= y && y <= 9999
            && 1 <= m
            && m <= 12
            && 1 <= dd
            && dd <= days_in_month_spec(y, m),
    ensures
        ns_epoch_day_spec(y, m, dd)
            == ns_epoch_day_spec(y, 1, 1)
                + day_of_year_spec(y, m, dd)
                - 1,
{
    if m == 1 {
        assert(day_of_year_spec(y, 1, dd) == dd);
        assert(ns_epoch_day_spec(y, 1, dd)
            == ns_epoch_day_spec(y, 1, 1) + dd - 1);
    } else if m == 2 {
        assert(day_of_year_spec(y, 2, dd) == 31 + dd);
        assert(ns_epoch_day_spec(y, 2, dd)
            == ns_epoch_day_spec(y, 1, 1) + 31 + dd - 1);
    } else {
        let Ya: int = y + 32800; // the m >= 3 arm's Y
        let Yj: int = y + 32800 - 1; // the January arm's Y
        assert(Ya >= 22800 && Ya <= 42800);
        assert(Yj == Ya - 1);
        lemma_y_star_linear(Ya);
        lemma_y_star_linear(Yj);
        lemma_f_step_leap(Ya);
        assert(Ya - 32800 == y);

        assert(
            ns_epoch_day_spec(y, m, dd)
                == (1461 * Ya / 4 - Ya / 100 + (Ya / 100) / 4)
                    + (979 * m - 2919) / 32 + dd - 1 - 12699422
    );
        assert(
            ns_epoch_day_spec(y, 1, 1)
                == (1461 * Yj / 4 - Yj / 100 + (Yj / 100) / 4)
                    + (979 * 13 - 2919) / 32 - 12699422
    );
        assert(365 * Ya - 365 * Yj == 365);
        if is_leap_year_spec(y) {
            assert(
                ns_epoch_day_spec(y, m, dd)
                    - ns_epoch_day_spec(y, 1, 1)
                    == 365 + 1 + (979 * m - 2919) / 32 - 306 + dd - 1
            );
        } else {
            assert(
                ns_epoch_day_spec(y, m, dd)
                    - ns_epoch_day_spec(y, 1, 1)
                    == 365 + (979 * m - 2919) / 32 - 306 + dd - 1
            );
        }
        // per-month constants: the m_star deltas are the calendar row
        // sums after pinning February's length (days_before_month of
        // the month equals 365 + leap - 306 + m_star(month))
        if is_leap_year_spec(y) {
            assert(days_in_month_spec(y, 2) == 29);
            if m == 3 {
                assert((979 * 3 - 2919) / 32 == 0);
                assert(days_before_month(y, 3) == 60);
                assert(365 + 1 - 306 + 0 == 60);
            } else if m == 4 {
                assert((979 * 4 - 2919) / 32 == 31);
                assert(days_before_month(y, 4) == 91);
                assert(365 + 1 - 306 + 31 == 91);
            } else if m == 5 {
                assert((979 * 5 - 2919) / 32 == 61);
                assert(days_before_month(y, 5) == 121);
                assert(365 + 1 - 306 + 61 == 121);
            } else if m == 6 {
                assert((979 * 6 - 2919) / 32 == 92);
                assert(days_before_month(y, 6) == 152);
                assert(365 + 1 - 306 + 92 == 152);
            } else if m == 7 {
                assert((979 * 7 - 2919) / 32 == 122);
                assert(days_before_month(y, 7) == 182);
                assert(365 + 1 - 306 + 122 == 182);
            } else if m == 8 {
                assert((979 * 8 - 2919) / 32 == 153);
                assert(days_before_month(y, 8) == 213);
                assert(365 + 1 - 306 + 153 == 213);
            } else if m == 9 {
                assert((979 * 9 - 2919) / 32 == 184);
                assert(days_before_month(y, 9) == 244);
                assert(365 + 1 - 306 + 184 == 244);
            } else if m == 10 {
                assert((979 * 10 - 2919) / 32 == 214);
                assert(days_before_month(y, 10) == 274);
                assert(365 + 1 - 306 + 214 == 274);
            } else if m == 11 {
                assert((979 * 11 - 2919) / 32 == 245);
                assert(days_before_month(y, 11) == 305);
                assert(365 + 1 - 306 + 245 == 305);
            } else if m == 12 {
                assert((979 * 12 - 2919) / 32 == 275);
                assert(days_before_month(y, 12) == 335);
                assert(365 + 1 - 306 + 275 == 335);
            }
        } else {
            assert(days_in_month_spec(y, 2) == 28);
            if m == 3 {
                assert((979 * 3 - 2919) / 32 == 0);
                assert(days_before_month(y, 3) == 59);
                assert(365 - 306 + 0 == 59);
            } else if m == 4 {
                assert((979 * 4 - 2919) / 32 == 31);
                assert(days_before_month(y, 4) == 90);
                assert(365 - 306 + 31 == 90);
            } else if m == 5 {
                assert((979 * 5 - 2919) / 32 == 61);
                assert(days_before_month(y, 5) == 120);
                assert(365 - 306 + 61 == 120);
            } else if m == 6 {
                assert((979 * 6 - 2919) / 32 == 92);
                assert(days_before_month(y, 6) == 151);
                assert(365 - 306 + 92 == 151);
            } else if m == 7 {
                assert((979 * 7 - 2919) / 32 == 122);
                assert(days_before_month(y, 7) == 181);
                assert(365 - 306 + 122 == 181);
            } else if m == 8 {
                assert((979 * 8 - 2919) / 32 == 153);
                assert(days_before_month(y, 8) == 212);
                assert(365 - 306 + 153 == 212);
            } else if m == 9 {
                assert((979 * 9 - 2919) / 32 == 184);
                assert(days_before_month(y, 9) == 243);
                assert(365 - 306 + 184 == 243);
            } else if m == 10 {
                assert((979 * 10 - 2919) / 32 == 214);
                assert(days_before_month(y, 10) == 273);
                assert(365 - 306 + 214 == 273);
            } else if m == 11 {
                assert((979 * 11 - 2919) / 32 == 245);
                assert(days_before_month(y, 11) == 304);
                assert(365 - 306 + 245 == 304);
            } else if m == 12 {
                assert((979 * 12 - 2919) / 32 == 275);
                assert(days_before_month(y, 12) == 334);
                assert(365 - 306 + 275 == 334);
            }
        }
        assert(ns_epoch_day_spec(y, m, dd)
            == ns_epoch_day_spec(y, 1, 1) + day_of_year_spec(y, m, dd)
                - 1);
    }
}


// ===========================================================================
// the ISO week calendar (jcore civil/date.rs:985-1352 and civil/mod.rs
// :204-232)
// ===========================================================================

/// is_long_iso_week_year model (jcore civil/mod.rs:204-209):
///   Returns true if and only if the given ISO 8601 week date year is
///   a "long" year or not.
///   A "long" year is a year with 53 weeks. Otherwise, it's a "short"
///   year with 52 weeks.
/// The upstream body reads the weekday of Dec 31 and the leap flag:
/// long iff Dec 31 is a Thursday, or a Friday in a leap year.
pub open spec fn is_long_iso_year_spec(y: int) -> bool {
    let e: int = ns_epoch_day_spec(y, 12, 31);
    wd_of_epoch_day(e) == 4
        || (is_leap_year_spec(y) && wd_of_epoch_day(e) == 5)
}

pub open spec fn weeks_in_iso_year_spec(y: int) -> int {
    if is_long_iso_year_spec(y) { 53 } else { 52 }
}

/// Calendar validity of an ISOWeekDate (what ISOWeekDate::new enforces
/// upstream, jcore date.rs:1011-1055): year in b::ISOYear (= Year,
/// jcore bounds.rs:226), week in b::ISOWeek 1..=53 (bounds.rs:222),
/// with 53 only in long years and the 9999/W52 corner cut at Friday
/// (9999-12-31 == 9999-W52-5 is the endpoint).
pub open spec fn valid_iso(w: ISOWeekDate) -> bool {
    year_iv().contains(w.year as int)
        && 1 <= w.week as int
        && (w.week as int) <= 53
        && ((w.week as int) == 53
            ==> weeks_in_iso_year_spec(w.year as int) == 53)
        && (w.year as int == 9999 && w.week as int == 52
            ==> wd_monday_one(w.weekday) <= 5)
}

/// iso_week_start_from_year model (jcore date.rs:1326-1352): the epoch
/// day of the Monday that starts the ISO week year -- Jan 4's week
/// stepped back to its Monday.
pub open spec fn iso_ws_spec(y: int) -> int {
    let e4: int = ns_epoch_day_spec(y, 1, 4);
    e4 - (wd_of_epoch_day(e4) - 1)
}

/// Corridor lemma: the Jan-4 epoch day never falls so low that its
/// week-Monday leaves the ued interval (with the -9999 corner folding
/// exactly: -9999-01-01 is a Monday, so year -9999's ISO year starts
/// exactly at the ued minimum).
proof fn lemma_iso_ws_in_ued(y: int)
    requires year_iv().contains(y),
    ensures ued_iv().contains(iso_ws_spec(y)),
{
    let j4: int = ns_epoch_day_spec(y, 1, 4);
    let d: int = wd_of_epoch_day(j4) - 1;
    assert(1 <= wd_of_epoch_day(j4) && wd_of_epoch_day(j4) <= 7);
    assert(0 <= d && d <= 6);
    assert(iso_ws_spec(y) == j4 - d);
    if y == -9999 {
        // the exact corner fold: Jan 4 of -9999 is a Thursday
        assert(j4 == -4371584);
        assert(wd_of_epoch_day(j4) == 4);
        assert(iso_ws_spec(y) == -4371587);
    } else {
        // corridor floor: y in [-9998, 9999] keeps the NS chain far
        // above the ued minimum even after the Monday step-back
        assert(-9998 <= y && y <= 9999);
        let Y: int = y + 32800 - 1;
        assert(22801 <= Y && Y <= 42798);
        assert(Y >= 0);
        assert(Y / 4 >= 5700);
        assert(Y / 4 <= 10699);
        assert(Y / 100 >= 228);
        assert(Y / 100 <= 427);
        assert(Y / 400 >= 57);
        assert(Y / 400 <= 106);
        lemma_y_star_linear(Y);
        assert((979 * 13 - 2919) / 32 == 306);
        assert(
            j4 == 1461 * Y / 4 - Y / 100 + (Y / 100) / 4
                + 306 + 3 - 12699422
        );
        assert(
            1461 * Y / 4 - Y / 100 + (Y / 100) / 4
                == 365 * Y + Y / 4 - Y / 100 + Y / 400
        );
        assert(j4 >= 365 * 22801 + 5700 - 427 + 57 + 309 - 12699422);
        assert(j4 >= -4371418);
        assert(iso_ws_spec(y) >= j4 - 6);
        assert(iso_ws_spec(y) >= -4371424);
        assert(iso_ws_spec(y) >= -4371587);
        // upper side: from the general NS corridor
        assert(j4 <= 365 * 42798 + 10699 - 228 + 106 + 309 - 12699422);
        assert(j4 <= 2932734);
        assert(iso_ws_spec(y) <= j4);
        assert(iso_ws_spec(y) <= 2932734);
        assert(iso_ws_spec(y) <= 2932896);
    }
}

/// Origin Rust (jcore civil/mod.rs:211-224):
///     pub const fn is_long_iso_week_year(year: i16) -> bool {
///         let last = unwrapr!(Date::new(year, 12, 31),
///             "last day of year is always valid");
///         let weekday = last.weekday();
///         matches!(weekday, Weekday::Thursday)
///             || (last.in_leap_year()
///                 && matches!(weekday, Weekday::Friday))
///     }
/// Upstream doc (jcore civil/mod.rs:204-209):
///   Returns true if and only if the given ISO 8601 week date year is
///   a "long" year or not.
///   A "long" year is a year with 53 weeks. Otherwise, it's a "short"
///   year with 52 weeks.
pub exec fn is_long_iso_week_year(year: i16) -> (r: bool)
    requires year_iv().contains(year as int),
    ensures r == is_long_iso_year_spec(year as int),
{
    // upstream: "last day of year is always valid" (the unwrapr face
    // transcribes as the impossible-None match)
    let Some(last) = Date::new(year, 12, 31) else {
        proof { assert(false); }
        unreachable!()
    };
    let weekday = last.weekday();
    let x = weekday.to_monday_one_offset();
    // matches!(weekday, Thursday) || (leap && matches!(Friday)):
    // wd_monday_one(Thursday) == 4, wd_monday_one(Friday) == 5.
    x == 4 || (last.in_leap_year() && x == 5)
}

/// Origin Rust (jcore civil/mod.rs:227-232):
///     pub const fn weeks_in_iso_week_year(year: i16) -> i8 {
///         if is_long_iso_week_year(year) { 53 } else { 52 }
///     }
/// Upstream doc (jcore civil/mod.rs:213-218):
///   Returns the total number of weeks in the year of this ISO 8601
///   week date.
///   It is guaranteed that the value returned is either 52 or 53. The
///   latter case occurs precisely when [`ISOWeekDate::in_long_year`]
///   returns `true`.
pub exec fn weeks_in_iso_week_year(year: i16) -> (r: i8)
    requires year_iv().contains(year as int),
    ensures
        (r as int) == weeks_in_iso_year_spec(year as int)
            && ((r as int) == 52 || (r as int) == 53),
{
    if is_long_iso_week_year(year) {
        53
    } else {
        52
    }
}

/// Origin Rust (jcore civil/date.rs:985-990):
///     pub struct ISOWeekDate { year: i16, week: i8,
///         weekday: Weekday }
/// Upstream header doc (jcore date.rs:969-973):
///   An ISO 8601 civil week date.
///   An ISO 8601 civil week date can be infallibly converted to and
///   from Gregorian [`Date`] values.
#[derive(Clone, Copy)]
pub struct ISOWeekDate {
    pub year: i16,
    pub week: i8,
    pub weekday: Weekday,
}

impl ISOWeekDate {

    /// Origin Rust (jcore date.rs:992-997):
    ///     pub const MIN: ISOWeekDate = ISOWeekDate {
    ///         year: b::ISOYear::MIN, week: b::ISOWeek::MIN,
    ///         weekday: Weekday::Monday };
    /// Upstream doc-comment (jcore date.rs:992):
    ///   The maximum representable ISO week date.
    /// SPEC-DOC MISMATCH candidate annotation: the upstream MIN and MAX
    /// doc-comments are label-swapped (MIN's comment reads "maximum
    /// representable", MAX's reads "minimum representable"); the field
    /// values below are the ones the consts carry (MIN = -9999 W01
    /// Monday per b::ISOYear::MIN = Year::MIN and b::ISOWeek::MIN =
    /// 1, matching the -9999-01-01 == -9999-W01-Monday equivalence
    /// the upstream docs elsewhere rely on). Recorded in
    /// J7/notes.md.
    pub const MIN: ISOWeekDate = ISOWeekDate {
        year: -9999,
        week: 1,
        weekday: Weekday::Monday,
    };

    /// Origin Rust (jcore date.rs:999-1005):
    ///     pub const MAX: ISOWeekDate = ISOWeekDate {
    ///         year: b::ISOYear::MAX,
    ///         // Technical max is 52, but 9999 is not a leap year.
    ///         week: 52,
    ///         weekday: Weekday::Friday };
    /// Upstream doc-comment (jcore date.rs:999):
    ///   The minimum representable ISO week date.
    /// (same label swap as MIN above)
    pub const MAX: ISOWeekDate = ISOWeekDate {
        year: 9999,
        week: 52,
        weekday: Weekday::Friday,
    };

    /// Origin Rust (jcore date.rs:1007-1009):
    ///     pub const ZERO: ISOWeekDate =
    ///         ISOWeekDate { year: 0, week: 1,
    ///             weekday: Weekday::Monday };
    /// Upstream doc (jcore date.rs:1007):
    ///   The zero ISO 8601 week date. It is the first day of the
    ///   zeroth year.
    pub const ZERO: ISOWeekDate = ISOWeekDate {
        year: 0,
        week: 1,
        weekday: Weekday::Monday,
    };

    /// Origin Rust (jcore date.rs:1011-1055):
    ///     pub const fn new(year: i16, week: i8, weekday: Weekday)
    ///         -> Result<ISOWeekDate, RangeError>
    /// Upstream doc (jcore date.rs:955-985, abridged):
    ///   Create a new ISO week date from its constituent parts.
    ///   If the week date is invalid or any of the values are out of
    ///   their supported ranges, then an error is returned.
    /// Upstream body comments (jcore date.rs:1017-1053):
    ///   All combinations of years, weeks and weekdays allowed by our
    ///   range types are valid ISO week dates with one exception: a
    ///   week number of 53 is only valid for "long" years. Or years
    ///   with an ISO leap week. It turns out this only happens when
    ///   the last day of the year is a Thursday.
    ///   And also, the maximum Date constrains what we can utter with
    ///   ISOWeekDate so that we can preserve infallible conversions
    ///   between them. So since 9999-12-31 maps to 9999 W52 Friday, it
    ///   follows that Saturday and Sunday are not allowed when the
    ///   year is at the maximum value. So reject them.
    ///   We don't need to worry about the minimum because the minimum
    ///   date (-9999-01-01) corresponds also to the minimum possible
    ///   combination of an ISO week date's fields: -9999 W01 Monday.
    ///   Nice.
    pub exec fn new(year: i16, week: i8, weekday: Weekday) -> (r: Option<ISOWeekDate>)
        ensures
            match r {
                Option::Some(w) => {
                    (w.year as int) == (year as int)
                        && (w.week as int) == (week as int)
                        && wd_monday_one(w.weekday)
                            == wd_monday_one(weekday)
                        && valid_iso(w)
                }
                Option::None => {
                    !year_iv().contains(year as int)
                        || !(1 <= week as int && week as int <= 53)
                        || (week as int == 53
                            && weeks_in_iso_year_spec(year as int)
                                != 53)
                        || (year as int == 9999 && week as int == 52
                            && wd_monday_one(weekday) > 5)
                }
            },
    {
        let Some(y2) = Year::checkc(year as i64) else {
            return Option::None;
        };
        if !(1 <= week && week <= 53) {
            return Option::None;
        }
        if week == 53 && weeks_in_iso_week_year(y2) != 53 {
            return Option::None;
        }
        if y2 == 9999 && week == 52 {
            let off = weekday.to_monday_one_offset();
            if off > 5 {
                return Option::None;
            }
        }
        Option::Some(ISOWeekDate {
            year: y2,
            week,
            weekday,
        })
    }

    /// Origin Rust (jcore date.rs:1056-1082):
    ///     pub const fn new_constrain(year: i16, week: i8,
    ///         weekday: Weekday) -> Result<ISOWeekDate, RangeError>
    /// Upstream doc (jcore date.rs:1046-1054):
    ///   Like `ISOWeekDate::new`, but constrains out-of-bounds week and
    ///   weekday values to their closest valid equivalent.
    ///   For example, given `9999 W52 Saturday`, this will return
    ///   `9999 W52 Friday`.
    ///   This still returns an error when `week < 1` or when `year` is
    ///   invalid.
    /// Transcription-narrowness annotation: upstream constrains the
    /// week==53-in-short-year case and the 9999/W52 weekday corner but
    /// leaves an out-of-range week tail (week > 53) flowing through
    /// unchanged (jcore date.rs:1064-1082 has no ISOWeek checkc), so
    /// the doc's "constrains out-of-bounds week ... values" understates
    /// the only two adjustments the body performs. Recorded in
    /// J7/notes.md alongside the doc/example rows.
    pub exec fn new_constrain(
        year: i16,
        week: i8,
        weekday: Weekday,
    ) -> (r: Option<ISOWeekDate>)
        ensures
            match r {
                Option::Some(w) => {
                    (w.year as int) == (year as int)
                        && (week as int >= 1
                            ==> (w.week as int)
                                == (if week as int == 53
                                        && weeks_in_iso_year_spec(
                                            year as int) != 53 {
                                        52
                                    } else {
                                        week as int
                                    }))
                        && (year as int == 9999
                            && (w.week as int) == 52
                            && (wd_monday_one(weekday) > 5)
                            ==> wd_monday_one(w.weekday) == 5)
                        && (year as int == 9999
                            && (w.week as int) == 52
                            && !(wd_monday_one(weekday) > 5)
                            ==> wd_monday_one(w.weekday)
                                == wd_monday_one(weekday))
                        && (year as int != 9999
                            ==> wd_monday_one(w.weekday)
                                == wd_monday_one(weekday))
                }
                Option::None => {
                    !year_iv().contains(year as int)
                        || !(1 <= week as int)
                }
            },
    {
        let Some(y2) = Year::checkc(year as i64) else {
            return Option::None;
        };
        if !(week >= 1) {
            return Option::None;
        }
        let mut wk: i8 = week;
        if wk == 53 && weeks_in_iso_week_year(y2) != 53 {
            wk = 52;
        }
        let mut wd: Weekday = weekday;
        if y2 == 9999 && wk == 52 {
            let off = weekday.to_monday_one_offset();
            if off > 5 {
                wd = Weekday::Friday;
            }
        }
        Option::Some(ISOWeekDate {
            year: y2,
            week: wk,
            weekday: wd,
        })
    }

    /// Origin Rust (jcore date.rs:1085-1090):
    ///     pub const fn year(self) -> i16 { self.year }
    /// Upstream doc (jcore date.rs:1082-1084):
    ///   Returns the year component of this ISO 8601 week date.
    ///   The value returned is guaranteed to be in the range specified
    ///   by [`ISOYear`].
    pub exec fn year(self) -> (r: i16)
        requires valid_iso(self),
        ensures
            (r as int) == (self.year as int)
                && year_iv().contains(r as int),
    {
        self.year
    }

    /// Origin Rust (jcore date.rs:1093-1096):
    ///     pub const fn week(self) -> i8 { self.week }
    /// Upstream doc (jcore date.rs:1090-1092):
    ///   Returns the week number component of this ISO 8601 week
    ///   date.
    ///   The value returned is guaranteed to be in the range specified
    ///   by [`ISOWeek`].
    pub exec fn week(self) -> (r: i8)
        requires valid_iso(self),
        ensures
            (r as int) == (self.week as int)
                && 1 <= r as int
                && (r as int) <= 53,
    {
        self.week
    }

    /// Origin Rust (jcore date.rs:1099-1101):
    ///     pub const fn weekday(self) -> Weekday {
    ///         self.weekday }
    /// Upstream doc (jcore date.rs:1097-1098):
    ///   Returns the weekday component of this ISO 8601 week date.
    pub exec fn weekday(self) -> (r: Weekday)
        requires valid_iso(self),
        ensures wd_monday_one(r) == wd_monday_one(self.weekday),
    {
        self.weekday
    }

    /// Origin Rust (jcore date.rs:1103-1115):
    ///     pub const fn first_of_week(self)
    ///         -> Result<ISOWeekDate, RangeError> {
    ///         // I believe this can never return an error because
    ///         // `Monday` is in bounds for all possible year-and-week
    ///         // combinations. ...
    ///         Ok(ISOWeekDate { weekday: Weekday::Monday, ..self })
    ///     }
    /// Upstream doc (jcore date.rs:1093-1101):
    ///   Returns the ISO 8601 week date corresponding to the first day
    ///   in the week of this week date. The date returned is guaranteed
    ///   to have a weekday of [`Weekday::Monday`].
    ///   # Errors
    ///   Since `-9999-01-01` falls on a Monday, it follows that the
    ///   minimum supported Gregorian date is exactly equivalent to
    ///   the minimum supported ISO 8601 week date. This means that
    ///   this routine can never actually fail, but only insomuch as
    ///   the minimums line up. For that reason, and for consistency
    ///   with [`ISOWeekDate::last_of_week`], the API is fallible.
    pub exec fn first_of_week(self) -> (r: Option<ISOWeekDate>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(w) => {
                    valid_iso(w)
                        && (w.year as int) == (self.year as int)
                        && (w.week as int) == (self.week as int)
                        && wd_monday_one(w.weekday) == 1
                }
                Option::None => false,
            },
    {
        Option::Some(ISOWeekDate {
            weekday: Weekday::Monday,
            ..self
        })
    }

    /// Origin Rust (jcore date.rs:1118-1128):
    ///     pub const fn last_of_week(self)
    ///         -> Result<ISOWeekDate, RangeError> {
    ///         ISOWeekDate::new(self.year(), self.week(),
    ///             Weekday::Sunday)
    ///     }
    /// Upstream doc (jcore date.rs:1104-1116):
    ///   Returns the ISO 8601 week date corresponding to the last day
    ///   in the week of this week date. The date returned is guaranteed
    ///   to have a weekday of [`Weekday::Sunday`].
    ///   # Errors
    ///   This can return an error if the last day of the week exceeds
    ///   Jiff's maximum Gregorian date of `9999-12-31`. It turns out
    ///   this can happen since `9999-12-31` falls on a Friday.
    pub exec fn last_of_week(self) -> (r: Option<ISOWeekDate>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(w) => {
                    valid_iso(w)
                        && (w.year as int) == (self.year as int)
                        && (w.week as int) == (self.week as int)
                        && wd_monday_one(w.weekday) == 7
                }
                Option::None => {
                    (self.year as int) == 9999
                        && (self.week as int) == 52
                }
            },
    {
        ISOWeekDate::new(self.year, self.week, Weekday::Sunday)
    }

    /// Origin Rust (jcore date.rs:1130-1149):
    ///     pub const fn first_of_year(self)
    ///         -> Result<ISOWeekDate, RangeError> {
    ///         // same Monday-luck comment as first_of_week
    ///         Ok(ISOWeekDate { week: 1,
    ///             weekday: Weekday::Monday, ..self })
    ///     }
    /// Upstream doc (jcore date.rs:1121-1128):
    ///   Returns the ISO 8601 week date corresponding to the first day
    ///   in the year of this week date. The date returned is guaranteed
    ///   to have a weekday of [`Weekday::Monday`].
    ///   # Errors: the same minimum-luck note as [`first_of_week].
    pub exec fn first_of_year(self) -> (r: Option<ISOWeekDate>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(w) => {
                    valid_iso(w)
                        && (w.year as int) == (self.year as int)
                        && (w.week as int) == 1
                        && wd_monday_one(w.weekday) == 1
                }
                Option::None => false,
            },
    {
        Option::Some(ISOWeekDate {
            week: 1,
            weekday: Weekday::Monday,
            ..self
        })
    }

    /// Origin Rust (jcore date.rs:1151-1169):
    ///     pub const fn last_of_year(self)
    ///         -> Result<ISOWeekDate, RangeError> {
    ///         ISOWeekDate::new(self.year(),
    ///             self.weeks_in_year(), Weekday::Sunday)
    ///     }
    /// Upstream doc (jcore date.rs:1140-1149):
    ///   Returns the ISO 8601 week date corresponding to the last day
    ///   in the year of this week date. The date returned is guaranteed
    ///   to have a weekday of [`Weekday::Sunday`].
    ///   # Errors
    ///   This can return an error if the last day of the year exceeds
    ///   Jiff's maximum Gregorian date of `9999-12-31`.
    pub exec fn last_of_year(self) -> (r: Option<ISOWeekDate>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(w) => {
                    valid_iso(w)
                        && (w.year as int) == (self.year as int)
                        && (w.week as int)
                            == weeks_in_iso_year_spec(self.year as int)
                        && wd_monday_one(w.weekday) == 7
                }
                Option::None => {
                    (self.year as int) == 9999
                        && weeks_in_iso_year_spec(self.year as int)
                            == 52
                }
            },
    {
        ISOWeekDate::new(
            self.year,
            weeks_in_iso_week_year(self.year),
            Weekday::Sunday,
        )
    }

    /// Origin Rust (jcore date.rs:1171-1177):
    ///     pub const fn days_in_year(self) -> i16 {
    ///         if self.in_long_year() { 371 } else { 364 }
    ///     }
    /// Upstream doc (jcore date.rs:1165-1169):
    ///   Returns the total number of days in the year of this ISO 8601
    ///   week date.
    ///   It is guaranteed that the value returned is either 364 or
    ///   371. The latter case occurs precisely when
    ///   [`ISOWeekDate::in_long_year`] returns `true`.
    pub exec fn days_in_year(self) -> (r: i16)
        requires valid_iso(self),
        ensures
            (is_long_iso_year_spec(self.year as int)
                ==> (r as int) == 371)
                && (!is_long_iso_year_spec(self.year as int)
                    ==> (r as int) == 364),
    {
        if self.in_long_year() {
            371
        } else {
            364
        }
    }

    /// Origin Rust (jcore date.rs:1179-1185):
    ///     pub const fn weeks_in_year(self) -> i8 {
    ///         civil::weeks_in_iso_week_year(self.year())
    ///     }
    /// Upstream doc (jcore date.rs:1186-1190):
    ///   Returns the total number of weeks in the year of this ISO
    ///   8601 week date.
    ///   It is guaranteed that the value returned is either 52 or 53.
    pub exec fn weeks_in_year(self) -> (r: i8)
        requires valid_iso(self),
        ensures
            (r as int)
                == weeks_in_iso_year_spec(self.year as int),
    {
        weeks_in_iso_week_year(self.year)
    }

    /// Origin Rust (jcore date.rs:1187-1193):
    ///     pub const fn in_long_year(self) -> bool {
    ///         civil::is_long_iso_week_year(self.year())
    ///     }
    /// Upstream doc (jcore date.rs:1195-1200):
    ///   Returns true if and only if the year of this week date is a
    ///   "long" year.
    ///   A long year is one that contains precisely 53 weeks. All
    ///   other years contain precisely 52 weeks.
    pub exec fn in_long_year(self) -> (r: bool)
        requires valid_iso(self),
        ensures r == is_long_iso_year_spec(self.year as int),
    {
        is_long_iso_week_year(self.year)
    }

    /// Origin Rust (jcore date.rs:1216-1249):
    ///     pub const fn tomorrow(self)
    ///         -> Result<ISOWeekDate, RangeError> {
    ///         // The maximum week date is `9999-W52-5`, which is a
    ///         // Friday. It doesn't end on a Sunday, so adjusting the
    ///         // logic below to check for it is a bit weird. So we
    ///         // just check here.
    ///         if self.year() == ISOWeekDate::MAX.year()
    ///             && self.week() == ISOWeekDate::MAX.week()
    ///             && matches!(self.weekday(), Weekday::Friday) {
    ///             rbail!(b::ISOYear::error());
    ///         }
    ///         if matches!(self.weekday(), Weekday::Sunday) {
    ///             if self.week() >= 52
    ///                 && self.week() == self.weeks_in_year() {
    ///                 let year = self.year() + 1;
    ///                 return Ok(ISOWeekDate { year, week: 1,
    ///                     weekday: Weekday::Monday });
    ///             }
    ///             let week = self.week() + 1;
    ///             return Ok(ISOWeekDate { week,
    ///                 weekday: Weekday::Monday, ..self });
    ///         }
    ///         Ok(ISOWeekDate { weekday: self.weekday().next(),
    ///             ..self })
    ///     }
    /// Upstream doc (jcore date.rs:1216-1222):
    ///   Returns the ISO 8601 date immediately following this one.
    ///   # Errors
    ///   This returns an error when this date is the maximum value.
    pub exec fn tomorrow(self) -> (r: Option<ISOWeekDate>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(t) => {
                    valid_iso(t)
                        && (wd_monday_one(self.weekday) != 7
                            ==> (wd_monday_one(t.weekday)
                                    == (wd_monday_one(self.weekday) % 7)
                                        + 1
                                && (t.year as int)
                                    == (self.year as int)
                                && (t.week as int)
                                    == (self.week as int)))
                        && (wd_monday_one(self.weekday) == 7
                            ==> (wd_monday_one(t.weekday) == 1
                                && (((t.week as int)
                                        == (self.week as int) + 1
                                    && (t.year as int)
                                        == (self.year as int)
                                    && weeks_in_iso_year_spec(
                                        self.year as int)
                                        != (self.week as int))
                                    || ((t.week as int) == 1
                                        && (t.year as int)
                                            == (self.year as int) + 1
                                        && weeks_in_iso_year_spec(
                                            self.year as int)
                                            == (self.week as int)))))
                }
                Option::None => {
                    (self.year as int) == 9999
                        && (self.week as int) == 52
                        && wd_monday_one(self.weekday) == 5
                }
            },
    {
        let sw = self.weekday.to_monday_one_offset();
        proof {
            assert((sw as int) == wd_monday_one(self.weekday));
        }
        if self.year == 9999i16 && self.week == 52i8 && sw == 5 {
            return Option::None;
        }
        if sw == 7 {
            let wy = weeks_in_iso_week_year(self.year);
            if self.week >= 52 && self.week == wy {
                let ty: i16 = self.year + 1;
                proof {
                    // 9999-W52 Sunday is not a valid input (the
                    // Friday corner), and 9999 has 52 weeks, so the
                    // wrap year stays in range
                    assert(is_long_iso_year_spec(9999)
                        == false);
                    assert(wd_of_epoch_day(
                        ns_epoch_day_spec(9999, 12, 31)) == 5);
                }
                return Option::Some(ISOWeekDate {
                    year: ty,
                    week: 1,
                    weekday: Weekday::Monday,
                });
            }
            return Option::Some(ISOWeekDate {
                week: self.week + 1,
                weekday: Weekday::Monday,
                ..self
            });
        }
        Option::Some(ISOWeekDate {
            weekday: self.weekday.next(),
            ..self
        })
    }

    /// Origin Rust (jcore date.rs:1252-1274):
    ///     pub fn yesterday(self) -> Result<ISOWeekDate, RangeError> {
    ///         if matches!(self.weekday(), Weekday::Monday) {
    ///             if self.week() == 1 {
    ///                 let year = rtry!(b::ISOYear::checked_add(
    ///                     self.year(), -1));
    ///                 let week =
    ///                     civil::weeks_in_iso_week_year(year);
    ///                 return Ok(ISOWeekDate { year, week,
    ///                     weekday: Weekday::Sunday });
    ///             }
    ///             let week = self.week() - 1;
    ///             return Ok(ISOWeekDate { week,
    ///                 weekday: Weekday::Sunday, ..self });
    ///         }
    ///         Ok(ISOWeekDate { weekday:
    ///             self.weekday().previous(), ..self })
    ///     }
    /// Upstream doc (jcore date.rs:1252-1258):
    ///   Returns the ISO 8601 week date immediately preceding this
    ///   one.
    ///   # Errors
    ///   This returns an error when this date is the minimum value.
    pub exec fn yesterday(self) -> (r: Option<ISOWeekDate>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(t) => {
                    1 <= (t.week as int)
                        && (t.week as int) <= 53
                        && year_iv().contains(t.year as int)
                        && (wd_monday_one(self.weekday) != 1
                            ==> (wd_monday_one(t.weekday)
                                    == wd_monday_one(self.weekday) - 1
                                && (t.year as int)
                                    == (self.year as int)
                                && (t.week as int)
                                    == (self.week as int)))
                        && (wd_monday_one(self.weekday) == 1
                            ==> (wd_monday_one(t.weekday) == 7
                                && ((self.week as int) > 1
                                    ==> ((t.week as int)
                                            == (self.week as int) - 1
                                        && (t.year as int)
                                            == (self.year as int)))
                                && ((self.week as int) == 1
                                    ==> ((t.week as int)
                                            == weeks_in_iso_year_spec(
                                                (self.year as int) - 1)
                                        && (t.year as int)
                                            == (self.year as int) - 1))))
                }
                Option::None => {
                    (self.year as int) == -9999
                        && (self.week as int) == 1
                        && wd_monday_one(self.weekday) == 1
                }
            },
    {
        let sw = self.weekday.to_monday_one_offset();
        proof {
            assert((sw as int) == wd_monday_one(self.weekday));
        }
        if sw == 1 {
            if self.week == 1 {
                if self.year == -9999i16 {
                    return Option::None;
                }
                let ny: i16 = self.year - 1;
                return Option::Some(ISOWeekDate {
                    year: ny,
                    week: weeks_in_iso_week_year(ny),
                    weekday: Weekday::Sunday,
                });
            }
            return Option::Some(ISOWeekDate {
                week: self.week - 1,
                weekday: Weekday::Sunday,
                ..self
            });
        }
        Option::Some(ISOWeekDate {
            weekday: self.weekday.previous(),
            ..self
        })
    }

/// Origin Rust (jcore date.rs:1275-1287):
    ///     pub const fn to_unix_epoch_day(self) -> UnixEpochDay {
    ///         let epoch_day_year =
    ///             iso_week_start_from_year(self.year());
    ///         let week = self.week() as i32;
    ///         let weekday =
    ///             self.weekday().to_monday_zero_offset() as i32;
    ///         unwrapr!(epoch_day_year.checked_add(
    ///             ((week - 1) * 7) + weekday),
    ///             "all valid ISO 8601 dates convert to a valid
    ///             Unix epoch day")
    ///     }
    /// Upstream doc (jcore date.rs:1275-1276):
    ///   Converts this ISO 8601 week date to a Unix epoch day.
    /// The upstream unwrapr (a panic on the impossible-for-valid-inputs
    /// claim) materializes as the Option face.
    pub exec fn to_unix_epoch_day(self) -> (r: Option<UnixEpochDay>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(e) => {
                    ued_iv().contains(e.day as int)
                        && (e.day as int)
                            == iso_ws_spec(self.year as int)
                                + ((self.week as int - 1) * 7)
                                + (wd_monday_one(self.weekday) - 1)
                }
                Option::None => false,
            },
    {
        let start = iso_week_start_from_year(self.year);
        let Some(start) = start else {
            proof {
                let jf: int = ns_epoch_day_spec(
                    self.year as int,
                    1,
                    4
                );
                lemma_iso_ws_in_ued(self.year as int);
                assert(false);
            }
            unreachable!()
        };
        let mu = self.weekday.to_monday_zero_offset();
        let off: i32 = ((self.week as i32) - 1) * 7 + (mu as i32);
        proof {
            let y: int = self.year as int;
            let w: int = self.week as int;
            let ws: int = iso_ws_spec(y);
            assert(w >= 1 && w <= 53);
            assert(w == 53 ==> weeks_in_iso_year_spec(y) == 53);
            assert(y == 9999 && w == 52
                ==> wd_monday_one(self.weekday) <= 5);
            // weekday offset tied to the Monday-one index
            assert((mu as int) == wd_monday_one(self.weekday) - 1);
            // corridor for the tail of the ISO week year
            if !(y == 9999) {
                assert(y <= 9998);
                let Y: int = y + 32800 - 1;
                assert(Y <= 42797);
                let jf: int = ns_epoch_day_spec(y, 1, 4);
                lemma_y_star_linear(Y);
                assert(jf <= 365 * Y + Y / 4 - Y / 100 + Y / 400
                    + 306 + 3 - 12699422);
                assert(jf <= 365 * 42797 + 10699 - 228 + 106 + 309
                    - 12699422);
                assert(jf <= 2932369);
                assert(ws <= jf);
                assert((w - 1) * 7 <= 52 * 7);
                // week 53 requires a long year, whose end is at most
                // 7 days after the last covered week start
                assert(ws + (w - 1) * 7
                    + (wd_monday_one(self.weekday) - 1) <= 2932369 + 364 + 6);
                assert(ws + (w - 1) * 7
                    + (wd_monday_one(self.weekday) - 1) <= 2932896);
            }
        }
        let Some(e) = start.checked_add(off) else {
            proof { assert(false); }
            unreachable!()
        };
        Option::Some(e)
    }

    /// Origin Rust (jcore date.rs:1287-1291):
    ///     pub const fn to_date(self) -> Date {
    ///         self.to_unix_epoch_day().to_date()
    ///     }
    /// Upstream doc (jcore date.rs:1287):
    ///   Converts this ISO 8601 week date to a Gregorian date.
    /// The component claims ride on the to_date_ns twin; the universal
    /// NS reverse validity remains deferred with the roundtrip family
    /// (witness-checked at the row panels).
    pub exec fn to_date(self) -> (r: Option<Date>)
        requires valid_iso(self),
        ensures
            match r {
                Option::Some(d) => {
                    let e: int = iso_ws_spec(self.year as int)
                        + ((self.week as int - 1) * 7)
                        + (wd_monday_one(self.weekday) - 1);
                    (d.year as int) == ns_civil_year(e)
                        && (d.month as int) == ns_civil_month(e)
                        && (d.day as int) == ns_civil_day(e)
                }
                Option::None => false,
            },
    {
        let Some(e) = self.to_unix_epoch_day() else {
            proof { assert(false); }
            unreachable!()
        };
        Option::Some(e.to_date_ns())
    }
}

/// Origin Rust (jcore date.rs:1326-1352):
///     const fn iso_week_start_from_year(year: i16) -> UnixEpochDay {
///     debug_assert!(b::Year::checkc(year as i64).is_ok());
///     // A week's year always corresponds to the Gregorian year in
///     // which the Thursday of that week falls. Therefore, Jan 4 is
///     // *always* in the first week of any ISO week year.
///     let epoch_day_in_first_week =
///         Date { year, month: 1, day: 4 }.to_unix_epoch_day();
///     // The start of the first week is a Monday, so find the number
///     // of days since Monday from a date that we know is in the
///     // first ISO week of `year`.
///     let diff_from_monday =
///         epoch_day_in_first_week.weekday().since(Weekday::Monday);
///     // OK because `diff_from_monday` is never bigger than 6 and is
///     // always positive. Therefore, the only case where this could
///     // plausibly fail is when `year=-9999`. But in that specific
///     // case, -9999-01-01 is on a Monday, so the diff is guaranteed
///     // to give us the minimal Unix epoch day value.
///     unwrapr!(
///         epoch_day_in_first_week.checked_sub(diff_from_monday as i32),
///         "valid Unix epoch day")
/// }
fn iso_week_start_from_year(year: i16) -> (r: Option<UnixEpochDay>)
    requires
        year_iv().contains(year as int),
    ensures
        match r {
            Option::Some(e) => {
                ued_iv().contains(e.day as int)
                    && (e.day as int) == iso_ws_spec(year as int)
            }
            Option::None => false,
        },
{
    // Jan 4 is always valid
    let jan4 = Date { year, month: 1, day: 4 };
    let e4 = jan4.to_unix_epoch_day_ns();
    let wd = e4.weekday();
    let diff = wd.since(Weekday::Monday);
    proof {
        assert(valid_date(jan4));
        let ei: int = (e4.day as int);
        assert(ei == ns_epoch_day_spec(year as int, 1, 4));
        // since-Monday face: wd_monday_one(wd) - 1 (in 0..=6)
        assert((diff as int) == wd_monday_one(wd) - 1);
        assert(wd_monday_one(wd) == wd_of_epoch_day(ei));
        assert(iso_ws_spec(year as int)
            == ei - ((diff as int)));
        lemma_iso_ws_in_ued(year as int);
        assert(ued_iv().contains(iso_ws_spec(year as int)));
        assert(0 <= (diff as int) && (diff as int) <= 6);
    }
    let Some(e) = e4.checked_sub(diff as i32) else {
        proof { assert(false); }
        unreachable!()
    };
    Option::Some(e)
}


// ===========================================================================
// Date::to_iso_week_date (jcore date.rs:525-581) and the since/until
// tail (jcore date.rs:450-494)
// ===========================================================================

/// The ISO decomposition model of a Gregorian date (the jcore
/// date.rs:527-581 branch structure as one spec twin): the year-end /
/// year-start overflow rules verbatim, with the week read against the
/// ISO week-year start Mondays.
pub open spec fn iso_from_date_spec(
    y: int,
    m: int,
    dd: int,
) -> (int, int, int) {
    let e: int = ns_epoch_day_spec(y, m, dd);
    let s: int = iso_ws_spec(y);
    let wdidx: int = wd_of_epoch_day(e);
    if e < s {
        // Jan 1, 2 or 3 falling into the previous ISO week year
        let sp: int = iso_ws_spec(y - 1);
        (y - 1, ((e - sp) / 7) + 1, wdidx)
    } else if m == 12 && dd >= 29 && y < 9999 && e >= iso_ws_spec(y + 1) {
        // Dec 29, 30 or 31 falling into the next ISO week year
        let sn: int = iso_ws_spec(y + 1);
        (y + 1, ((e - sn) / 7) + 1, wdidx)
    } else {
        (y, ((e - s) / 7) + 1, wdidx)
    }
}

impl Date {

    /// Origin Rust (jcore date.rs:527-581):
    ///     pub const fn to_iso_week_date(self) -> ISOWeekDate {
    ///         let epoch_day = self.to_unix_epoch_day();
    ///         let mut year = self.year();
    ///         let mut epoch_day_year_start =
    ///             iso_week_start_from_year(year);
    ///         if epoch_day.day() < epoch_day_year_start.day() {
    ///             // If our date comes before the first day of the ISO
    ///             // 8601 year, then it must be the case that our
    ///             // date falls at the end of the previous ISO 8601
    ///             // year. This can happen for Gregorian dates
    ///             // Jan 1, 2 or 3.
    ///             // And this subtraction is OK because `year - 1` is
    ///             // only a problem when `year=-9999`. But we can't be
    ///             // here when `year=-9999` ...
    ///             year -= 1;
    ///             epoch_day_year_start =
    ///                 iso_week_start_from_year(year);
    ///         } else if self.month() == 12 && self.day() >= 29
    ///             && year < b::Year::MAX {
    ///             // Otherwise, it's possible for dates at the end of
    ///             // the Gregorian calendar year to actually have an
    ///             // ISO 8601 week year following the Gregorian
    ///             // calendar year. This can occur for only Dec 29,
    ///             // 30 or 31. For `year=9999`, we don't need to do
    ///             // this check because ... `9999-W52-5`.
    ///             let epoch_day_next_year_week_start =
    ///                 iso_week_start_from_year(year + 1);
    ///             if epoch_day.day()
    ///                 >= epoch_day_next_year_week_start.day() {
    ///                 epoch_day_year_start =
    ///                     epoch_day_next_year_week_start;
    ///                 year += 1;
    ///             }
    ///         }
    ///         // OK because the biggest difference between epoch days
    ///         // here can be 370 (for a long year), and dividing that
    ///         // by 7 and adding 1 always fits into an `i8`.
    ///         let week = (((epoch_day.day()
    ///             - epoch_day_year_start.day()) / 7) + 1) as i8;
    ///         let weekday = epoch_day.weekday();
    ///         ISOWeekDate { year, week, weekday }
    ///     }
    /// Upstream doc (jcore date.rs:525-526):
    ///   Converts this Gregorian date to an ISO 8601 week date.
    /// Wrapper face (jiff src/civil/date.rs:1000-1039) delegates 1:1
    /// and its doc examples pin the boundary rows (panel-checked
    /// below). Contract tier: the output components mirror the open
    /// spec twin exactly (branch structure included) and the weekday
    /// ties to the epoch-day residue face; the universal week-range
    /// and valid_iso claims stay with the deferred roundtrip family.
    pub exec fn to_iso_week_date(self) -> (r: ISOWeekDate)
        requires valid_date(self),
        ensures
            ({
                let t: (int, int, int) = iso_from_date_spec(
                    self.year as int,
                    self.month as int,
                    self.day as int,
                );
                (r.year as int) == t.0
                    && (r.week as int) == t.1
                    && wd_monday_one(r.weekday) == t.2
            }),
    {
        let epoch_day = self.to_unix_epoch_day_ns();
        let mut year: i16 = self.year;
        let Some(start) = iso_week_start_from_year(year) else {
            proof { assert(false); }
            unreachable!()
        };
        proof {
            // the twin binds the epoch day; the upstream .day() reads
            // materialize as the pub-field reads (the frozen getter
            // carries no value equality in its contract, the J6
            // finding-36 mirror-fields pattern)
            let yi: int = self.year as int;
            let ei: int = epoch_day.day as int;
            assert(ei == ns_epoch_day_spec(
                yi,
                self.month as int,
                self.day as int,
            ));
            assert((start.day as int) == iso_ws_spec(yi));
        }
        let e: i32 = epoch_day.day;
        if e < start.day {
            proof {
                // -9999 cannot take this arm: its ISO week year starts
                // exactly at -9999-01-01 (upstream comment, jcore
                // date.rs:536-544)
                let yi: int = self.year as int;
                if yi == -9999 {
                    assert(ns_epoch_day_spec(-9999, 1, 1)
                        == -4371587);
                    lemma_iso_ws_in_ued(-9999);
                    // the Monday corner: Jan 4 of -9999 is a Thursday
                    assert(ns_epoch_day_spec(-9999, 1, 4)
                        == -4371584);
                    assert(wd_of_epoch_day(-4371584) == 4);
                    assert(iso_ws_spec(-9999) == -4371587);
                    lemma_ns_within_year(
                        yi,
                        self.month as int,
                        self.day as int,
                    );
                    let eiv: int = e as int;
                    assert(eiv == ns_epoch_day_spec(
                        yi,
                        self.month as int,
                        self.day as int,
                    ));
                    assert(eiv >= -4371587);
                    assert((start.day as int) == -4371587);
                    assert(eiv >= (start.day as int));
                    assert(false);
                }
                assert(year_iv().contains(yi - 1));
            }
            year = year - 1;
            let Some(st1) = iso_week_start_from_year(year) else {
                proof { assert(false); }
                unreachable!()
            };
            let week: i8 = (((e - st1.day) / 7) + 1) as i8;
            let weekday = epoch_day.weekday();
            ISOWeekDate { year, week, weekday }
        } else if self.month == 12 && self.day >= 29 && year < 9999 {
            let Some(st2) = iso_week_start_from_year(year + 1) else {
                proof { assert(false); }
                unreachable!()
            };
            if e >= st2.day {
                let week: i8 = (((e - st2.day) / 7) + 1) as i8;
                let weekday = epoch_day.weekday();
                ISOWeekDate {
                    year: year + 1,
                    week,
                    weekday,
                }
            } else {
                let week: i8 = (((e - start.day) / 7) + 1) as i8;
                let weekday = epoch_day.weekday();
                ISOWeekDate { year, week, weekday }
            }
        } else {
            let week: i8 = (((e - start.day) / 7) + 1) as i8;
            let weekday = epoch_day.weekday();
            ISOWeekDate { year, week, weekday }
        }
    }

    /// Origin Rust (jcore date.rs:482-494):
    ///     pub const fn since(self, other: Date) -> i32 {
    ///         // Try to avoid conversions to Unix epoch days in some
    ///         // cases.
    ///         if self.year() == other.year() {
    ///             if self.month() == other.month() {
    ///                 (self.day() - other.day()) as i32
    ///             } else {
    ///                 (self.day_of_year()
    ///                     - other.day_of_year()) as i32
    ///             }
    ///         } else {
    ///             self.to_unix_epoch_day().since(
    ///                 other.to_unix_epoch_day())
    ///         }
    ///     }
    /// Upstream doc (jcore date.rs:445-469, abridged):
    ///   Returns the number of days from this date until `other`.
    ///   (flipped for since)
    ///   This routine never overflows because of the enforced range on
    ///   `Date` values.
    ///   # Example
    ///   ...
    ///   assert_eq!(7_304_483, Date::MAX.since(Date::MIN));
    pub exec fn since(self, other: Date) -> (r: i32)
        requires
            valid_date(self)
                && valid_date(other),
        ensures
            (r as int)
                == ns_epoch_day_spec(
                    self.year as int,
                    self.month as int,
                    self.day as int,
                )
                    - ns_epoch_day_spec(
                        other.year as int,
                        other.month as int,
                        other.day as int,
                    ),
    {
        if self.year == other.year {
            if self.month == other.month {
                proof {
                    lemma_ns_within_year(
                        self.year as int,
                        self.month as int,
                        self.day as int,
                    );
                    lemma_ns_within_year(
                        self.year as int,
                        self.month as int,
                        other.day as int,
                    );
                }
                (self.day as i32) - (other.day as i32)
            } else {
                proof {
                    lemma_ns_within_year(
                        self.year as int,
                        self.month as int,
                        self.day as int,
                    );
                    lemma_ns_within_year(
                        self.year as int,
                        other.month as int,
                        other.day as int,
                    );
                }
                (self.day_of_year() as i32)
                    - (other.day_of_year() as i32)
            }
        } else {
            let a = self.to_unix_epoch_day_ns();
            let b = other.to_unix_epoch_day_ns();
            a.since(b)
        }
    }

    /// Origin Rust (jcore date.rs:450-451):
    ///     pub const fn until(self, other: Date) -> i32 {
    ///         -self.since(other)
    ///     }
    /// Upstream doc (jcore date.rs:412-435, abridged):
    ///   Returns the number of days from this date until `other`.
    ///   This routine never overflows because of the enforced range on
    ///   `Date` values.
    ///   # Example
    ///   ...
    ///   assert_eq!(7_304_483, Date::MIN.until(Date::MAX));
    pub exec fn until(self, other: Date) -> (r: i32)
        requires
            valid_date(self)
                && valid_date(other),
        ensures
            (r as int)
                == ns_epoch_day_spec(
                    other.year as int,
                    other.month as int,
                    other.day as int,
                )
                    - ns_epoch_day_spec(
                        self.year as int,
                        self.month as int,
                        self.day as int,
                    ),
    {
        let sv = self.since(other);
        0 - sv
    }
}


// ===========================================================================
// the nth-weekday family (jcore date.rs:332-380 and :771-810)
// ===========================================================================

/// The nth_weekday_of_month model: upstream's diff formulas on the
/// month's first/last day, with the out-of-month tail returning None
/// (upstream's Date::new face).
pub open spec fn nthwm_spec(
    y: int,
    m: int,
    nth: int,
    wdw: Weekday,
) -> Option<(int, int, int)> {
    let dim: int = days_in_month_spec(y, m);
    let e1: int = ns_epoch_day_spec(y, m, 1);
    let el: int = ns_epoch_day_spec(y, m, dim);
    if !(-5 <= nth && nth <= 5) || nth == 0 {
        Option::None
    } else if nth > 0 {
        let diff: int = (wd_monday_one(wdw)
            - wd_of_epoch_day(e1)) % 7;
        let day: int = diff + 1 + (nth - 1) * 7;
        if 1 <= day && day <= dim {
            Option::Some((y, m, day))
        } else {
            Option::None
        }
    } else {
        let diff: int = (wd_of_epoch_day(el)
            - wd_monday_one(wdw)) % 7;
        let day: int = dim - diff - (-nth - 1) * 7;
        if 1 <= day && day <= dim {
            Option::Some((y, m, day))
        } else {
            Option::None
        }
    }
}

/// The weekday-continuity heart of nthwm_spec: whatever Some-triple
/// the model returns indexes to the requested weekday (the 7-slot mod
/// arithmetic behind both upstream arms).
impl Date {

    /// Origin Rust (jcore date.rs:343-372):
    ///     pub const fn nth_weekday_of_month(&self, nth: i8,
    ///         weekday: Weekday) -> Result<Date, RangeError>
    /// Upstream doc (jcore date.rs:332-341):
    ///   Returns the `nth` weekday of the month represented by this
    ///   date.
    ///   `nth` must be non-zero and otherwise in the range `-5..=5`.
    ///   If it isn't, an error is returned.
    ///   This also returns an error if `abs(nth)==5` and there is no
    ///   "5th" weekday of this month.
    /// The bounds face is b::NthWeekdayOfMonth (jcore bounds.rs:250-256,
    /// the i8 interval -5..=5, with 0 rejected separately).
    pub exec fn nth_weekday_of_month(
        &self,
        nth: i8,
        weekday: Weekday,
    ) -> (r: Option<Date>)
        requires valid_date(*self),
        ensures
            match r {
                Option::Some(d) => {
                    (d.year as int) == (self.year as int)
                        && (d.month as int) == (self.month as int)
                        && valid_date(d)
                        && ({
                            let t: Option<(int, int, int)>
                                = nthwm_spec(
                                    self.year as int,
                                    self.month as int,
                                    nth as int,
                                    weekday,
                                );
                            t == Option::Some((
                                (d.year as int),
                                (d.month as int),
                                (d.day as int),
                            ))
                        })
                }
                Option::None => {
                    nthwm_spec(
                        self.year as int,
                        self.month as int,
                        nth as int,
                        weekday,
                    ) == Option::None
                }
            },
    {
        if !(1 <= nth && nth <= 5) && !(-5 <= nth && nth <= -1) {
            return Option::None;
        }
        if nth > 0 {
            let first = self.first_of_month();
            let first_weekday = first.weekday();
            let diff = weekday.since(first_weekday);
            let day: i8 = diff + 1 + (nth - 1) * 7;
            Date::new(self.year, self.month, day)
        } else {
            let last = self.last_of_month();
            let last_weekday = last.weekday();
            let diff = last_weekday.since(weekday);
            let nth_abs: i8 = if nth < 0 { -nth } else { nth };
            let day: i8 = last.day - diff - (nth_abs - 1) * 7;
            Date::new(self.year, self.month, day)
        }
    }

    /// Origin Rust (jcore date.rs:374-380):
    ///     pub const fn nth_weekday(self, nth: i32,
    ///         weekday: Weekday) -> Result<Date, RangeError> {
    ///         self.to_unix_epoch_day().nth_weekday(nth, weekday)
    ///     }
    /// Upstream doc (jcore date.rs:363-371):
    ///   Returns the "nth" weekday from this date, not including
    ///   itself.
    ///   The `nth` parameter can be positive or negative. A positive
    ///   value computes the "nth" weekday starting at the day after
    ///   this date and going forwards in time. A negative value
    ///   computes the "nth" weekday starting at the day before this
    ///   date and going backwards in time.
    ///   For example, if this date's weekday is a Sunday and the first
    ///   Sunday is asked for (that is, `date.nth_weekday(1,
    ///   Weekday::Sunday)`), then the result is a week from this date
    ///   corresponding to the following Sunday.
    /// Contract tier: the wire carries the epoch-armithmetic twin
    /// (the fidelity of the resulting Date's weekday rides the
    /// deferred NS reverse family; the row panels witness the upstream
    /// example rows).
    pub exec fn nth_weekday(
        self,
        nth: i32,
        weekday: Weekday,
    ) -> (r: Option<Date>)
        requires valid_date(self),
        ensures
            match r {
                Option::Some(d) => {
                    let e: int = ns_epoch_day_spec(
                        self.year as int,
                        self.month as int,
                        self.day as int,
                    );
                    let total: int = nth_total_spec(e, nth as int, weekday);
                    (d.year as int) == ns_civil_year(e + total)
                        && (d.month as int)
                            == ns_civil_month(e + total)
                        && (d.day as int)
                            == ns_civil_day(e + total)
                }
                Option::None => {
                    nth == 0
                        || !nth_total_bounded(nth as int)
                        || !ued_iv().contains(
                            ns_epoch_day_spec(
                                self.year as int,
                                self.month as int,
                                self.day as int,
                            ) + nth_total_spec(
                                ns_epoch_day_spec(
                                    self.year as int,
                                    self.month as int,
                                    self.day as int,
                                ),
                                nth as int,
                                weekday,
                            ),
                        )
                }
            },
    {
        self.to_unix_epoch_day_ns().nth_weekday(nth, weekday)
    }
}

/// The epoch-day delta of UnixEpochDay::nth_weekday's arms (jcore
/// date.rs:782-810). The b::NthWeekday corridor is -1043497..=1043497
/// (jcore bounds.rs:241-247: DeltaSeconds::MAX
/// / c::SECS_PER_CIVIL_WEEK, with DeltaSeconds::MAX the next multiple
/// of 86400 above UnixEpochSeconds::LEN + OffsetTotalSeconds::MAX +
/// 86400 = 631107417600).
pub open spec fn nth_total_bounded(nth: int) -> bool {
    -1043497 <= nth && nth <= 1043497
}

pub open spec fn nth_total_spec(e: int, nth: int, wdw: Weekday) -> int
    recommends
        nth_total_bounded(nth),
{
    if nth > 0 {
        (nth - 1) * 7
            + (wd_monday_one(wdw)
                - ((wd_of_epoch_day(e) % 7) + 1)) % 7
            + 1
    } else {
        0 - (((-nth) - 1) * 7
            + ((if wd_of_epoch_day(e) - 1 < 1 {
                7
            } else {
                wd_of_epoch_day(e) - 1
            }) - wd_monday_one(wdw)) % 7
            + 1)
    }
}

impl UnixEpochDay {

    /// Origin Rust (jcore date.rs:782-810):
    ///     pub const fn nth_weekday(self, nth: i32,
    ///         weekday: Weekday) -> Result<Date, RangeError> {
    ///         // ref: http://howardhinnant.github.io/
    ///         //     date_algorithms.html#next_weekday
    ///         let nth = rtry!(b::NthWeekday::checkc(nth as i64));
    ///         if nth == 0 {
    ///             rbail!(b::NthWeekday::error());
    ///         } else if nth > 0 {
    ///             let weekday_diff =
    ///                 weekday.since(self.weekday().next()) as i32;
    ///             let diff = (nth - 1) * 7 + weekday_diff;
    ///             let end = ctry!(self.checked_add(diff + 1));
    ///             Ok(end.to_date())
    ///         } else {
    ///             let weekday_diff = self.weekday().previous()
    ///                 .since(weekday) as i32;
    ///             let nth = nth.abs();
    ///             let diff = -((nth - 1) * 7 + weekday_diff);
    ///             let end = ctry!(self.checked_add(diff - 1));
    ///             Ok(end.to_date())
    ///         }
    ///     }
    /// Upstream doc (jcore date.rs:771-780): "Returns the "nth"
    /// weekday from this date, not including itself." (same body text
    /// as the Date face).
    pub exec fn nth_weekday(
        self,
        nth: i32,
        weekday: Weekday,
    ) -> (r: Option<Date>)
        requires ued_iv().contains(self.day as int),
        ensures
            match r {
                Option::Some(d) => {
                    let e: int = self.day as int;
                    let total: int = nth_total_spec(e, nth as int, weekday);
                    (d.year as int) == ns_civil_year(e + total)
                        && (d.month as int)
                            == ns_civil_month(e + total)
                        && (d.day as int)
                            == ns_civil_day(e + total)
                }
                Option::None => {
                    nth == 0
                        || !nth_total_bounded(nth as int)
                        || !ued_iv().contains(
                            (self.day as int)
                                + nth_total_spec(
                                    self.day as int,
                                    nth as int,
                                    weekday,
                                ),
                        )
                }
            },
    {
        if nth == 0 {
            return Option::None;
        }
        if !(-1043497i32 <= nth && nth <= 1043497i32) {
            return Option::None;
        }
        if nth > 0 {
            let wnext = self.weekday().next();
            let weekday_diff = weekday.since(wnext);
            proof {
                let e: int = self.day as int;
                let wq: int = wd_of_epoch_day(self.day as int);
                assert(wq == wd_of_epoch_day(e));
                let wqnext: int = wd_monday_one(wnext);
                assert(wqnext == (wq % 7) + 1);
                assert((weekday_diff as int)
                    == (wd_monday_one(weekday) - wqnext) % 7);
                assert((nth_total_spec(self.day as int, nth as int, weekday))
                    == (((nth as int) - 1) * 7
                        + (weekday_diff as int) + 1));
            }
            let diff: i32 = (nth - 1) * 7 + (weekday_diff as i32);
            let Some(end) = self.checked_add(diff + 1) else {
                return Option::None;
            };
            let dr = end.to_date_ns();
            proof {
                let e2: int = (end.day as int);
                assert(e2 == (self.day as int)
                    + (((nth as int) - 1) * 7
                        + (weekday_diff as int) + 1));
            }
            Option::Some(dr)
        } else {
            let wprev = self.weekday().previous();
            let weekday_diff = wprev.since(weekday);
            let nth_abs: i32 = if nth < 0 { -nth } else { nth };
            proof {
                let e: int = self.day as int;
                let wq: int = wd_of_epoch_day(self.day as int);
                assert(wq == wd_of_epoch_day(e));
                let wqprev: int = wd_monday_one(wprev);
                assert(wqprev
                    == if wq == 1 { 7 } else { wq - 1 });
                assert((weekday_diff as int)
                    == (wqprev - wd_monday_one(weekday)) % 7);
                assert((nth_total_spec(self.day as int, nth as int, weekday))
                    == 0 - (((nth_abs as int) - 1) * 7
                        + (weekday_diff as int) + 1));
            }
            let diff: i32 = -(((nth_abs - 1) * 7)
                + (weekday_diff as i32));
            let Some(end) = self.checked_add(diff - 1) else {
                return Option::None;
            };
            let dr = end.to_date_ns();
            proof {
                let e2: int = (end.day as int);
                assert(e2 == (self.day as int)
                    + (0 - (((nth_abs as int) - 1) * 7
                        + (weekday_diff as int) + 1)));
            }
            Option::Some(dr)
        }
    }
}


// ===========================================================================
// row panels: the upstream test and doc-example rows (z3 ground-folds)
// ===========================================================================

/// Upstream test rows (jcore date.rs:2016-2067, to_iso_week_date_various,
/// mirrored as the wrapper doc examples at jiff src/civil/date.rs:1000-1039):
///   date(1995, 1, 1)  -> 1994 W52 Sun
///   date(1996, 12, 31)-> 1997 W01 Tue
///   date(2019, 12, 30)-> 2020 W01 Mon
///   date(2031, 12, 29)-> 2032 W01 Mon
///   date(2024, 3, 9)  -> 2024 W10 Sat
///   Date::MIN         -> -9999 W01 Mon
///   Date::MAX         -> 9999 W52 Fri
exec fn panel_iso_rows_a() -> (ok: bool)
    ensures ok == true,
{
    let i1 = date(1995, 1, 1).to_iso_week_date();
    let i2 = date(1996, 12, 31).to_iso_week_date();
    let i3 = date(2019, 12, 30).to_iso_week_date();
    let i4 = date(2031, 12, 29).to_iso_week_date();
    proof {
        assert((i1.year as int) == 1994 && (i1.week as int) == 52);
        assert(i1.weekday is Sunday);
        assert((i2.year as int) == 1997 && (i2.week as int) == 1);
        assert(i2.weekday is Tuesday);
        assert((i3.year as int) == 2020 && (i3.week as int) == 1);
        assert(i3.weekday is Monday);
        assert((i4.year as int) == 2032 && (i4.week as int) == 1);
        assert(i4.weekday is Monday);
    }
    true
}

exec fn panel_iso_rows_b() -> (ok: bool)
    ensures ok == true,
{
    let i5 = date(2024, 3, 9).to_iso_week_date();
    let i6 = Date::MIN.to_iso_week_date();
    let i7 = Date::MAX.to_iso_week_date();
    proof {
        assert((i5.year as int) == 2024 && (i5.week as int) == 10);
        assert(i5.weekday is Saturday);
        assert((i6.year as int) == -9999 && (i6.week as int) == 1);
        assert(i6.weekday is Monday);
        assert((i7.year as int) == 9999 && (i7.week as int) == 52);
        assert(i7.weekday is Friday);
    }
    true
}

exec fn panel_nth_rows_b() -> (ok: bool)
    ensures ok == true,
{
    let d2 = date(2024, 3, 10);
    let Some(sw2) = d2.tomorrow() else {
        proof { assert(false); }
        unreachable!()
    };
    let w3 = sw2.nth_weekday(-1, Weekday::Sunday);
    let d3 = date(2024, 3, 16);
    let Some(sw3) = d3.tomorrow() else {
        proof { assert(false); }
        unreachable!()
    };
    let w4 = sw3.nth_weekday(-1, Weekday::Sunday);
    let e1 = date(2024, 3, 10);
    proof {
        assert(w3 == Option::Some(e1));
        assert(w4 == Option::Some(e1));
    }
    true
}

/// Upstream rows (jcore date.rs:450-494 doc examples and the overflow
/// example at date.rs:1419-1447): 366 across the 2024 leap, the flipped
/// signs, and the never-overflow endpoints (7_304_483 ==
/// b::UnixEpochDays::LEN - 1).
exec fn panel_since_until_rows() -> (ok: bool)
    ensures ok == true,
{
    let u1 = date(2023, 7, 1).until(date(2024, 7, 1));
    let u2 = date(2024, 7, 1).until(date(2023, 7, 1));
    let s1 = date(2024, 7, 1).since(date(2023, 7, 1));
    let s2 = date(2023, 7, 1).since(date(2024, 7, 1));
    let me = Date::MIN.until(Date::MAX);
    let ms = Date::MAX.since(Date::MIN);
    let um = Date::MAX.until(Date::MIN);
    proof {
        assert(u1 as int == 366);
        assert(u2 as int == -366);
        assert(s1 as int == 366);
        assert(s2 as int == -366);
        assert(me as int == 7304483);
        assert(ms as int == 7304483);
        assert(um as int == -7304483);
    }
    true
}

/// Upstream rows (jcore date.rs:1608-1659): the nth-of-month arms and
/// the 5th-weekday-absent errors, plus the near-minimum Monday rows.
exec fn panel_nth_month_rows() -> (ok: bool)
    ensures ok == true,
{
    let x1 = date(2017, 3, 1);
    let x2 = date(2017, 3, 10);
    let x3 = date(2024, 3, 28);
    let x4 = date(2024, 3, 25);
    let x5 = date(1998, 1, 31);
    let x6 = date(2017, 3, 31);
    let x7 = date(2017, 3, 3);
    let x8 = date(-9999, 1, 1);
    let x9 = date(-9999, 1, 8);
    let f1 = x1.nth_weekday_of_month(2, Weekday::Friday);
    let f2 = date(2024, 3, 1).nth_weekday_of_month(-1, Weekday::Thursday);
    let f3 = x4.nth_weekday_of_month(4, Weekday::Monday);
    let f4 = x4.nth_weekday_of_month(5, Weekday::Monday);
    let f5 = x4.nth_weekday_of_month(-5, Weekday::Monday);
    let f6 = date(1998, 1, 1).nth_weekday_of_month(5, Weekday::Saturday);
    let f7 = x1.nth_weekday_of_month(0, Weekday::Tuesday);
    let f8 = x1.nth_weekday_of_month(5, Weekday::Tuesday);
    let f9 = x1.nth_weekday_of_month(-5, Weekday::Tuesday);
    let f10 = x1.nth_weekday_of_month(5, Weekday::Friday);
    let f11 = x1.nth_weekday_of_month(-5, Weekday::Friday);
    let f12 = x1.nth_weekday_of_month(6, Weekday::Friday);
    let f13 = x1.nth_weekday_of_month(-6, Weekday::Friday);
    let f14 = x8.nth_weekday_of_month(1, Weekday::Monday);
    let f15 = x8.nth_weekday_of_month(2, Weekday::Monday);
    proof {
        assert(f1 == Option::Some(x2));
        assert(f2 == Option::Some(x3));
        assert(f3 == Option::Some(x4));
        assert(f4 == Option::None);
        assert(f5 == Option::None);
        assert(f6 == Option::Some(x5));
        assert(f7 == Option::None);
        assert(f8 == Option::None);
        assert(f9 == Option::None);
        assert(f10 == Option::Some(x6));
        assert(f11 == Option::Some(x7));
        assert(f12 == Option::None);
        assert(f13 == Option::None);
        assert(f14 == Option::Some(x8));
        assert(f15 == Option::Some(x9));
    }
    true
}

/// Wrapper doc rows (jiff src/civil/date.rs:957-982): the week-start
/// idiom (tomorrow + nth_weekday(-1, Sunday/Monday)) at the
/// mid-week and boundary positions.
exec fn panel_nth_rows_a() -> (ok: bool)
    ensures ok == true,
{
    let d = date(2024, 3, 15);
    let Some(sw1) = d.tomorrow() else {
        proof { assert(false); }
        unreachable!()
    };
    let w1 = sw1.nth_weekday(-1, Weekday::Sunday);
    let w2 = sw1.nth_weekday(-1, Weekday::Monday);
    let e1 = date(2024, 3, 10);
    let e2 = date(2024, 3, 11);
    proof {
        assert(w1 == Option::Some(e1));
        assert(w2 == Option::Some(e2));
    }
    true
}

/// The to_date_ns negative-day regression rows: the NS reverse twin
/// at the negative epoch days the pre-repair J2 form corrupted
/// (mirror vs upstream divergence, J7/notes.md). The frozen date.rs
/// to_date now carries the faithful N = day + K chain as a
/// postcondition-free verbatim port (so no caller-side machine-check
/// applies to it); these rows witness the informative face on the
/// twin, against both the constant tables and the spec ns_civil
/// model:
///   day = -1        -> 1969-12-31
///   day = -100      -> 1969-09-23
///   day = -366      -> 1968-12-31
///   day = -4371587  -> -9999-01-01
exec fn panel_to_date_repair() -> (ok: bool)
    ensures ok == true,
{
    let t1 = (UnixEpochDay { day: -1 }).to_date_ns();
    let t2 = (UnixEpochDay { day: -100 }).to_date_ns();
    let t3 = (UnixEpochDay { day: -366 }).to_date_ns();
    let t4 = (UnixEpochDay { day: -4371587 }).to_date_ns();
    proof {
        assert((t1.year as int) == 1969);
        assert((t1.month as int) == 12);
        assert((t1.day as int) == 31);
        assert((t2.year as int) == 1969);
        assert((t2.month as int) == 9);
        assert((t2.day as int) == 23);
        assert((t3.year as int) == 1968);
        assert((t3.month as int) == 12);
        assert((t3.day as int) == 31);
        assert((t4.year as int) == -9999);
        assert((t4.month as int) == 1);
        assert((t4.day as int) == 1);
        assert((t1.year as int) == ns_civil_year(-1));
        assert((t2.year as int) == ns_civil_year(-100));
        assert((t4.year as int) == ns_civil_year(-4371587));
    }
    true
}

/// Long-year rows and the upstream quickcheck property
/// prop_all_long_years_have_53rd_week (jcore date.rs:2069-2077): every
/// long ISO year constructs W53-Sunday.
exec fn panel_long_years(w: (i16,)) -> (ok: bool)
    requires year_iv().contains((w.0) as int),
    ensures ok == true,
{
    let y = w.0;
    let l = is_long_iso_week_year(y);
    let z = ISOWeekDate::new(y, 53, Weekday::Sunday);
    let wk = weeks_in_iso_week_year(y);
    proof {
        assert((2015i16 == y || 2020i16 == y || 2026i16 == y
            || 9998i16 == y)
            ==> is_long_iso_year_spec(y as int));
        if l {
            assert(z == Option::Some(ISOWeekDate {
                year: y,
                week: 53,
                weekday: Weekday::Sunday,
            }));
        } else {
            assert((wk as int) == 52);
        }
    }
    true
}

/// The structural identity laws of ISOWeekDate::tomorrow/yesterday
/// (upstream quickcheck prop_iso_yesterday_tomorrow_is_identity and
/// prop_iso_tomorrow_yesterday_is_identity, jcore date.rs:2097-2115).
exec fn panel_iso_today_yes(w: ISOWeekDate) -> (r: ISOWeekDate)
    requires
        valid_iso(w)
            && !(w.year as int == -9999 && w.week as int == 1
                && wd_monday_one(w.weekday) == 1),
    ensures
        (r.year as int) == (w.year as int)
            && (r.week as int) == (w.week as int)
            && wd_monday_one(r.weekday) == wd_monday_one(w.weekday),
{
    let Some(y) = w.yesterday() else {
        proof { assert(false); }
        unreachable!()
    };
    let Some(t) = y.tomorrow() else {
        proof { assert(false); }
        unreachable!()
    };
    t
}

exec fn panel_iso_yes_today(w: ISOWeekDate) -> (r: ISOWeekDate)
    requires
        valid_iso(w)
            && !(w.year as int == 9999 && w.week as int == 52
                && wd_monday_one(w.weekday) == 5),
    ensures
        (r.year as int) == (w.year as int)
            && (r.week as int) == (w.week as int)
            && wd_monday_one(r.weekday) == wd_monday_one(w.weekday),
{
    let Some(t) = w.tomorrow() else {
        proof { assert(false); }
        unreachable!()
    };
    let Some(y) = t.yesterday() else {
        proof { assert(false); }
        unreachable!()
    };
    y
}

} // verus!
