//! Batch J6 -- the civil datetime core, Verus transcription of:
//!   - code/crates/jiff-core/src/civil/datetime.rs (the whole 273-line
//!     file at this pin: the DateTime struct :12-15, the MIN/MAX consts
//!     :18-22, DateTime::new :30-42, from_parts :44-48, date :52-54,
//!     time :58-60, checked_add_seconds :67-81,
//!     saturating_add_seconds :87-98, to_timestamp :113-118)
//!   - the public wrapper faces in code/crates/jiff/src/civil/datetime.rs
//!     that are pure Date/Time reassemblies: new :302, constant :375,
//!     from_parts :405, year :464, month :522, day :539, hour :556,
//!     minute :573, second :590, millisecond :607, microsecond :624,
//!     nanosecond :641, subsec_nanosecond :695, tomorrow :967,
//!     yesterday :993, date :1240, time :1255
//!   - the free constructor civil::datetime() (jiff main-crate civil/
//!     mod.rs:192-198)
//!
//! Cut declarations (recorded in J6/notes.md):
//! - DateTime::to_timestamp (jcore :113-118) and everything tz-flavored
//!   is the permanent out-of-scope tz surface (inventory trimming
//!   principle 3); the tz::tzif same-named DateTime is likewise
//!   another crate's face, untouched.
//! - The wrapper arithmetic checked_add/checked_sub/saturating_add/
//!   saturating_sub (wrapper :1680/:1777/:1802/:1832, DateTimeArithmetic
//!   :3050+) ride the Span surface -- J5 agent territory, deferred to
//!   the span batch. The jcore-internal checked_add_seconds /
//!   saturating_add_seconds (the Span-free seconds-reassembly hearts)
//!   ARE transcribed below.
//! - DateTime::weekday (wrapper :716) delegates to Date::weekday, whose
//!   face is the Neri-Schneider epoch-day mod-7 reduction of the J2
//!   deferred roundtrip family; recorded for the NS roundtrip batch.
//!
//! Materialization ledger (this file):
//! - Result<T, RangeError / Error> faces materialize as Option<T> (the
//!   J1 bounds.rs ledger); ctry!/unwrapr! transcribe as their let-else
//!   expansions, the None arm of the latter under an assert(false)
//!   proof + unreachable!() when the caller's invariants discharge it.
//! - Validity model: valid_datetime(dt) == valid_date(dt.date) &&
//!   valid_time(dt.time), standing in for upstream's private-field type
//!   discipline (jcore datetime.rs:12-15). from_parts preserves nothing
//!   upstream beyond the two components (any valid Date plus any valid
//!   Time is a valid DateTime, wrapper from_parts doc :399-401); the
//!   constructor faces ensure validity, from_parts passes it through.
//! - The MIN/MAX consts (jcore :19-22 upstream define them through
//!   Date::MIN/MAX + Time::MIN/MAX const evaluation, which this build
//!   cannot verify -- the J2 Date::MIN/MAX deferral): materialized with
//!   the literal field values those upstream consts denote
//!   (-9999-01-01T00:00:00 / 9999-12-31T23:59:59.999999999), tied to
//!   the validity model by the constants-panel proof fn (the J2 toolchain
//!   finding-14 pattern: pub const items carry no obligation of their
//!   own; the panel lemma is the honest face).
//! - checked_add_seconds' day-carry: upstream calls
//!   Time::to_second().overflowing_add(seconds) (the jcore TimeSecond
//!   face, jcore time.rs:346-356); the J3 transcription of
//!   TimeSecond::overflowing_add carries an |a| <= 2^30 domain guard
//!   (time.rs rem/div_euclid_86400 requires) that DateTime's full i32
//!   seconds parameter cannot honor, so the day-carry is re-materialized
//!   here at the full i32 domain (div_euclid_86400_full /
//!   rem_euclid_86400_full below, the same std-body inlines without the
//!   conservative guard -- the fix-up x + 86_400 and q - 1 cannot
//!   overflow at the i32 width for any a, since the trunc remainder
//!   sits in -86_399..=86_399).
//! - Time::with_subsec_nanosecond (jcore time.rs:140-154) is consumed by
//!   the checked_add_seconds body upstream; it is materialized here as
//!   the free fn time_with_subsec_nanosecond (the time.rs module is
//!   closed to this batch -- the append-only concurrency discipline).
//! - checked_add_seconds inherits the J2 contract tier of
//!   Date::checked_add for the date component: the informative
//!   general-N postcondition is the deferred Neri-Schneider roundtrip
//!   family, so the transcribed contract pins the time component
//!   exactly (the day-carry decomposition + the carried subsec) and the
//!   date component on the 0/+1/-1 carries (spec_tomorrow /
//!   spec_yesterday), with the full determinism faces for those
//!   carries -- the J2 Date::checked_add contract style.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_mod_multiples_basic, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add_other_way, lemma_mul_unary_negation,
};

use super::bounds::{const_check, month_iv, year_iv};
use super::date::{
    Date, days_in_month_spec, is_leap_year_spec, spec_tomorrow,
    spec_yesterday, valid_date,
};
use super::time::{
    Time, TimeSecond, hour_iv, minute_iv, second_iv,
    spec_time_from_second, subsec_iv, time_secs_spec, valid_time,
};

verus! {

// ===========================================================================
// spec models
// ===========================================================================

/// The private-field DateTime invariant upstream's type discipline
/// carries (jcore datetime.rs:12-15): a valid Date plus a valid Time
/// (wrapper from_parts doc, jiff civil/datetime.rs:398-401:
/// "Any combination of a valid `Date` and a valid `Time` results in a
/// valid `DateTime`.").
pub open spec fn valid_datetime(dt: DateTime) -> bool {
    valid_date(dt.date) && valid_time(dt.time)
}

/// The time component of DateTime::checked_add_seconds' result: the
/// seconds-of-day decomposition of the carried remainder with the
/// original subsecond preserved (upstream second.to_time()
/// .with_subsec_nanosecond(self.time().subsec_nanosecond()),
/// jcore datetime.rs:74-79).
pub open spec fn spec_dt_time_add(
    t: Time,
    rem: int,
) -> Time {
    let twin: Time = spec_time_from_second(rem);
    Time {
        hour: twin.hour,
        minute: twin.minute,
        second: twin.second,
        subsec_nanosecond: t.subsec_nanosecond,
    }
}

// ===========================================================================
// DateTime (jcore civil/datetime.rs:12-119; the wrapper faces live in the
// jiff main crate at code/crates/jiff/src/civil/datetime.rs)
// ===========================================================================

/// Origin Rust (jcore datetime.rs:12-15):
///     pub struct DateTime { date: Date, time: Time }
/// Upstream doc (jcore datetime.rs:9):
///   A civil time of a day on a particular Gregorian date.
/// Fields are public here (no private-field type discipline in the
/// closure); valid_datetime (above) is the carrying invariant.
#[derive(Clone, Copy)]
pub struct DateTime {
    pub date: Date,
    pub time: Time,
}

impl DateTime {
    /// Origin Rust (jcore datetime.rs:18-19):
    ///     /// The minimum allowed Gregorian date and clock time.
    ///     pub const MIN: DateTime = DateTime {
    ///         date: Date::MIN, time: Time::MIN,
    ///     };
    /// Date::MIN/MAX are -9999-01-01 / 9999-12-31 (jcore date.rs:29-47,
    /// const-evaluated Neri-Schneider at this pin) and Time::MIN/MAX are
    /// 00:00:00.000000000 / 23:59:59.999999999 (jcore time.rs:25-35,
    /// const-evaluated through Time::constant); const items carry no
    /// obligation in this build, so the literal field values they denote
    /// are spelled here and checked by the panel proof fn (J2 finding 14
    /// ledger; the J2 Date::MIN/MAX deferral note).
    pub const MIN: DateTime = DateTime {
        date: Date { year: -9999i16, month: 1i8, day: 1i8 },
        time: Time {
            hour: 0i8,
            minute: 0i8,
            second: 0i8,
            subsec_nanosecond: 0i32,
        },
    };

    /// Origin Rust (jcore datetime.rs:21-22):
    ///     /// The maximum allowed Gregorian date and clock time.
    ///     pub const MAX: DateTime = DateTime {
    ///         date: Date::MAX, time: Time::MAX,
    ///     };
    /// Date::MAX is 9999-12-31 and Time::MAX is 23:59:59.999999999.
    pub const MAX: DateTime = DateTime {
        date: Date { year: 9999i16, month: 12i8, day: 31i8 },
        time: Time {
            hour: 23i8,
            minute: 59i8,
            second: 59i8,
            subsec_nanosecond: 999_999_999i32,
        },
    };

    /// Origin Rust (jcore datetime.rs:24-42 / wrapper datetime.rs:302-310):
    ///     pub const fn new(year: i16, month: i8, day: i8,
    ///         hour: i8, minute: i8, second: i8, subsec_nanosecond: i32,
    ///     ) -> Result<DateTime, RangeError> {
    ///         let date = ctry!(Date::new(year, month, day));
    ///         let time = ctry!(Time::new(hour, minute, second,
    ///             subsec_nanosecond));
    ///         Ok(DateTime::from_parts(date, time))
    ///     }
    /// Upstream doc (jcore datetime.rs:26-29):
    ///   Creates a new civil datetime from its constituent components.
    ///   If any of the values are out of their supported ranges, then an
    ///   error is returned. Additionally, if `year`, `month` and `day` do not
    ///   correspond to a valid Gregorian date, then an error is returned.
    pub exec fn new(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> (r: Option<DateTime>)
        ensures
            match r {
                Option::Some(dt) => dt.date.year as int == year as int
                    && dt.date.month as int == month as int
                    && dt.date.day as int == day as int
                    && dt.time.hour as int == hour as int
                    && dt.time.minute as int == minute as int
                    && dt.time.second as int == second as int
                    && (dt.time.subsec_nanosecond as int)
                        == (subsec_nanosecond as int)
                    && valid_datetime(dt),
                Option::None => !(
                    year_iv().contains(year as int)
                        && month_iv().contains(month as int)
                        && 1 <= day as int
                        && (day as int)
                            <= days_in_month_spec(year as int, month as int)
                        && hour_iv().contains(hour as int)
                        && minute_iv().contains(minute as int)
                        && second_iv().contains(second as int)
                        && subsec_iv().contains(subsec_nanosecond as int)
                ),
            },
    {
        let Some(date) = Date::new(year, month, day) else {
            return Option::None;
        };
        let Some(time) = Time::new(
            hour,
            minute,
            second,
            subsec_nanosecond,
        ) else {
            return Option::None;
        };
        Option::Some(DateTime { date, time })
    }

    /// Origin Rust (jcore datetime.rs:44-48 / wrapper datetime.rs:405):
    ///     pub const fn from_parts(date: Date, time: Time) -> DateTime {
    ///         DateTime { date, time }
    ///     }
    /// Upstream doc (wrapper datetime.rs:398-401):
    ///   Creates a `DateTime` from its constituent parts.
    ///   Any combination of a valid `Date` and a valid `Time` results in a
    ///   valid `DateTime`.
    pub exec fn from_parts(date: Date, time: Time) -> (dt: DateTime)
        ensures
            dt.date == date && dt.time == time
                && (valid_date(date) && valid_time(time)
                    ==> valid_datetime(dt)),
    {
        DateTime { date, time }
    }

    /// Origin Rust (jcore datetime.rs:50-54 / wrapper datetime.rs:1240):
    ///     pub const fn date(&self) -> Date { self.date }
    /// Upstream doc (wrapper datetime.rs:1229-1237):
    ///   Returns the civil date component of this datetime.
    pub exec fn date(self) -> (r: Date)
        ensures
            r == self.date
                && (valid_datetime(self) ==> valid_date(r)),
    {
        self.date
    }

    /// Origin Rust (jcore datetime.rs:56-60 / wrapper datetime.rs:1255):
    ///     pub const fn time(&self) -> Time { self.time }
    /// Upstream doc (wrapper datetime.rs:1244-1252):
    ///   Returns the civil time component of this datetime.
    pub exec fn time(self) -> (r: Time)
        ensures
            r == self.time
                && (valid_datetime(self) ==> valid_time(r)),
    {
        self.time
    }

    /// Origin Rust (jcore datetime.rs:62-81):
    ///     pub const fn checked_add_seconds(
    ///         &self, seconds: i32,
    ///     ) -> Result<DateTime, RangeError> {
    ///         let (second, added_days) =
    ///             ctry!(self.time().to_second().overflowing_add(seconds));
    ///         let date = ctry!(self.date().checked_add(added_days));
    ///         let time = unwrapr!(
    ///             second
    ///                 .to_time()
    ///                 .with_subsec_nanosecond(self.time().subsec_nanosecond()),
    ///             "subsec we started from hasn't change and must be valid",
    ///         );
    ///         Ok(DateTime::from_parts(date, time))
    ///     }
    /// Upstream doc (jcore datetime.rs:62-65):
    ///   Adds the given number of seconds to this civil datetime.
    ///   This returns an error when the resulting datetime would exceed
    ///   either [`DateTime::MIN`] or [`DateTime::MAX`].
    /// Contract ledger: the time component is pinned exactly (the
    /// day-carry decomposition s = time_secs + seconds with the Euclid
    /// remainder / carry, the subsecond carried through); the date
    /// component inherits the J2 Date::checked_add contract tier, so its
    /// informative face is precise on the 0/+1/-1 carries (full
    /// determinism faces below) and otherwise only reachable through
    /// the caller (the deferred NS roundtrip family, J2/notes.md). The
    /// i32-overflow error direction (s outside i32) is upstream's
    /// TimeSecond::overflowing_add rbail face (jcore time.rs:347-349).
    pub exec fn checked_add_seconds(
        self,
        seconds: i32,
    ) -> (r: Option<DateTime>)
        requires valid_datetime(self),
        ensures
            ({
                let s: int =
                    time_secs_spec(self.time) + (seconds as int);
                let rem: int = s % 86_400;
                let days: int = s / 86_400;
                let tw: Time = spec_dt_time_add(self.time, rem);
                (r is Some ==> (i32::MIN as int) <= s
                    && s <= (i32::MAX as int)
                    && (r->Some_0).time == tw
                    && valid_time(tw))
                    && ((s < (i32::MIN as int)
                        || (i32::MAX as int) < s) ==> r is None)
                    && (days == 0 ==> r
                        == Option::Some(DateTime {
                            date: self.date,
                            time: tw,
                        }))
                    && (days == 1 ==> match spec_tomorrow(self.date) {
                        Option::Some(d) => r == Option::Some(DateTime {
                            date: d,
                            time: tw,
                        }),
                        Option::None => r is None,
                    })
                    && (days == -1 ==> match spec_yesterday(self.date) {
                        Option::Some(d) => r == Option::Some(DateTime {
                            date: d,
                            time: tw,
                        }),
                        Option::None => r is None,
                    })
            }),
    {
        let ts = self.time.to_second();
        let Some(sum) = ts.second.checked_add(seconds) else {
            proof {
                let s: int =
                    time_secs_spec(self.time) + (seconds as int);
                assert(!(
                    (i32::MIN as int) <= s && s <= (i32::MAX as int)
                ));
            }
            return Option::None;
        };
        let second = rem_euclid_86400_full(sum);
        let added_days = div_euclid_86400_full(sum);
        proof {
            let s: int = time_secs_spec(self.time) + (seconds as int);
            assert((ts.second as int) == time_secs_spec(self.time));
            assert((sum as int) == s);
            assert((second as int) == s % 86_400);
            assert((added_days as int) == s / 86_400);
        }
        let Some(date) = self.date.checked_add(added_days) else {
            proof {
                // the callee's J2-tier ensures decide the 0/±1 carries:
                // on those carries the None arm is unreachable here
                if added_days == 0 {
                    assert(false);
                } else if added_days == 1 {
                    if spec_tomorrow(self.date) is Some {
                        assert(false);
                    }
                } else if added_days == -1 {
                    if spec_yesterday(self.date) is Some {
                        assert(false);
                    }
                }
            }
            return Option::None;
        };
        proof {
            if added_days == 0 {
                assert(date == self.date);
            } else if added_days == 1 {
                if spec_tomorrow(self.date) is Some {
                    assert(date == spec_tomorrow(self.date)->Some_0);
                }
            } else if added_days == -1 {
                if spec_yesterday(self.date) is Some {
                    assert(date == spec_yesterday(self.date)->Some_0);
                }
            }
        }
        let t0 = TimeSecond { second }.to_time();
        let Some(time) =
            time_with_subsec_nanosecond(t0, self.time.subsec_nanosecond)
        else {
            proof { assert(false); }
            unreachable!()
        };
        proof {
            let s: int = time_secs_spec(self.time) + (seconds as int);
            let rem: int = s % 86_400;
            let twin: Time = spec_time_from_second(rem);
            assert(t0 == twin);
            assert(time.hour == twin.hour);
            assert(time.minute == twin.minute);
            assert(time.second == twin.second);
            assert(
                (time.subsec_nanosecond as int)
                    == (self.time.subsec_nanosecond as int)
            );
            assert(time == spec_dt_time_add(self.time, rem));
            assert(valid_time(time));
        }
        Option::Some(DateTime { date, time })
    }

    /// Origin Rust (jcore datetime.rs:83-98):
    ///     pub const fn saturating_add_seconds(
    ///         &self, seconds: i32,
    ///     ) -> DateTime {
    ///         match self.checked_add_seconds(seconds) {
    ///             Ok(dt) => dt,
    ///             Err(_) => {
    ///                 if seconds < 0 {
    ///                     DateTime::MIN
    ///                 } else {
    ///                     DateTime::MAX
    ///                 }
    ///             }
    ///         }
    ///     }
    /// Upstream doc (jcore datetime.rs:83-86):
    ///   Like `DateTime::checked_add_seconds`, but arithmetic saturates to
    ///   either [`DateTime::MIN`] (when `seconds < 0`) or [`DateTime::MAX`]
    ///   (when `seconds > 0`).
    pub exec fn saturating_add_seconds(
        self,
        seconds: i32,
    ) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            ({
                let s: int =
                    time_secs_spec(self.time) + (seconds as int);
                let rem: int = s % 86_400;
                let days: int = s / 86_400;
                let tw: Time = spec_dt_time_add(self.time, rem);
                let in_i32: bool = (i32::MIN as int) <= s
                    && s <= (i32::MAX as int);
                ((r.time == tw
                    && in_i32
                    && (days == 0 ==> r.date == self.date)
                    && (days == 1
                        ==> match spec_tomorrow(self.date) {
                            Option::Some(d) => r.date == d,
                            Option::None => false,
                        })
                    && (days == -1
                        ==> match spec_yesterday(self.date) {
                            Option::Some(d) => r.date == d,
                            Option::None => false,
                        }))
                    || (r.date == DateTime::MIN.date
                        && r.time == DateTime::MIN.time)
                    || (r.date == DateTime::MAX.date
                        && r.time == DateTime::MAX.time))
                    && (!in_i32
                        ==> if seconds < 0 {
                            r.date == DateTime::MIN.date
                                && r.time == DateTime::MIN.time
                        } else {
                            r.date == DateTime::MAX.date
                                && r.time == DateTime::MAX.time
                        })
            }),
    {
        let Some(dt) = self.checked_add_seconds(seconds) else {
            if seconds < 0 {
                return DateTime::MIN;
            } else {
                return DateTime::MAX;
            }
        };
        dt
    }
}

/// Origin Rust (jiff main-crate civil/mod.rs:192-198):
///     pub const fn datetime(year: i16, month: i8, day: i8,
///         hour: i8, minute: i8, second: i8, subsec_nanosecond: i32,
///     ) -> DateTime {
///         DateTime::constant(year, month, day, hour, minute, second,
///             subsec_nanosecond)
///     }
/// Upstream doc (main-crate civil/mod.rs:169-191, abridged):
///   Creates a new `DateTime` value in a `const` context.
///   This is a convenience free function for [`DateTime::constant`].
///   # Panics
///   This routine panics when [`DateTime::new`] would return an error.
///   [The seven component-bounds bullets of DateTime::constant's Panics
///   section, main-crate datetime.rs:312-326.]
pub exec fn datetime(
    year: i16,
    month: i8,
    day: i8,
    hour: i8,
    minute: i8,
    second: i8,
    subsec_nanosecond: i32,
) -> (dt: DateTime)
    requires
        year_iv().contains(year as int)
            && month_iv().contains(month as int)
            && 1 <= day as int
            && (day as int)
                <= days_in_month_spec(year as int, month as int)
            && hour_iv().contains(hour as int)
            && minute_iv().contains(minute as int)
            && second_iv().contains(second as int)
            && subsec_iv().contains(subsec_nanosecond as int),
    ensures
        dt.date.year as int == year as int
            && dt.date.month as int == month as int
            && dt.date.day as int == day as int
            && dt.time.hour as int == hour as int
            && dt.time.minute as int == minute as int
            && dt.time.second as int == second as int
            && (dt.time.subsec_nanosecond as int)
                == (subsec_nanosecond as int)
            && valid_datetime(dt),
{
    let Some(dt) = DateTime::new(
        year,
        month,
        day,
        hour,
        minute,
        second,
        subsec_nanosecond,
    ) else {
        proof { assert(false); }
        unreachable!()
    };
    dt
}

// ===========================================================================
// std rem_euclid / div_euclid inlines at the civil-day-second divisor
// (86_400), FULL i32 domain -- the finding-13 std-body inlines without
// the |a| <= 2^30 guard the J3 time.rs siblings carry: at the divisor
// head the trunc remainder lies in -86_399..=86_399, so neither the
// x + 86_400 fix-up nor the q - 1 adjust can overflow i32. This is the
// domain DateTime::checked_add_seconds' full i32 seconds parameter needs.
// ===========================================================================

/// std i32::rem_euclid body inlined at the SECS_PER_CIVIL_DAY divisor.
pub exec fn rem_euclid_86400_full(a: i32) -> (r: i32)
    ensures
        r as int == (a as int) % 86_400
            && 0 <= r as int
            && (r as int) < 86_400,
{
    let x = a % 86_400i32;
    proof {
        let ai: int = a as int;
        assert(x as int == rust_rem(ai, 86_400));
        if a == 0 {
            assert(rust_rem(ai, 86_400) == 0);
            assert(ai % 86_400 == 0);
        } else if a > 0 {
            assert(rust_rem(ai, 86_400) == ai % 86_400);
        } else {
            let n: int = 0 - ai;
            let q: int = n / 86_400;
            let e: int = n % 86_400;
            lemma_fundamental_div_mod(n, 86_400);
            assert(n == 86_400 * q + e);
            assert(0 <= e < 86_400);
            lemma_mul_is_commutative(q, 86_400);
            lemma_mul_unary_negation(q, 86_400);
            assert(ai == (0 - q) * 86_400 + (0 - e));
            if x == 0 {
                assert(ai == (0 - q) * 86_400);
                assert(rust_rem(ai, 86_400) == 0);
                lemma_mod_multiples_basic(0 - q, 86_400);
                assert(ai % 86_400 == 0);
            } else {
                let w: int = 86_400 - e;
                assert(0 < w < 86_400);
                lemma_mul_is_distributive_add_other_way(86_400, q, 1);
                lemma_mul_basics(86_400);
                assert((q + 1) * 86_400 == q * 86_400 + 1 * 86_400);
                assert(1 * 86_400 == 86_400);
                assert((q + 1) * 86_400 == q * 86_400 + 86_400);
                lemma_mul_unary_negation(q + 1, 86_400);
                assert((0 - (q + 1)) * 86_400 == (0 - q * 86_400) - 86_400);
                assert(ai == (0 - (q + 1)) * 86_400 + w);
                lemma_fundamental_div_mod_converse(
                    ai,
                    86_400,
                    0 - (q + 1),
                    w,
                );
                assert(ai % 86_400 == w);
                assert(rust_rem(ai, 86_400) == 0 - e);
                assert(x as int == 0 - e);
                assert(x as int + 86_400 == w);
            }
        }
    }
    if x < 0 {
        x + 86_400i32
    } else {
        x
    }
}

/// std i32::div_euclid (q-adjust form: q = a / rhs, minus 1 when the
/// trunc remainder is negative) inlined at the SECS_PER_CIVIL_DAY
/// divisor.
pub exec fn div_euclid_86400_full(a: i32) -> (q: i32)
    ensures (q as int) == (a as int) / 86_400,
{
    let q = a / 86_400i32;
    let x = a % 86_400i32;
    proof {
        let ai: int = a as int;
        assert(x as int == rust_rem(ai, 86_400));
        let tr: int = vstd::arithmetic::div_mod::rust_div(ai, 86_400);
        assert(q as int == tr);
        assert(ai == 86_400 * tr + (x as int));
        let e: int = ai % 86_400;
        if x >= 0 {
            assert(e == x as int);
            lemma_fundamental_div_mod_converse(ai, 86_400, tr, e);
        } else {
            let qm: int = tr - 1;
            assert(e == (x as int) + 86_400);
            lemma_mul_is_distributive_add_other_way(86_400, qm, 1);
            lemma_mul_basics(86_400);
            assert((qm + 1) * 86_400 == qm * 86_400 + 1 * 86_400);
            assert(1 * 86_400 == 86_400);
            assert((qm + 1) * 86_400 == qm * 86_400 + 86_400);
            lemma_mul_is_commutative(qm + 1, 86_400);
            assert(86_400 * tr == qm * 86_400 + 86_400);
            assert(ai == qm * 86_400 + ((x as int) + 86_400));
            lemma_fundamental_div_mod_converse(
                ai,
                86_400,
                qm,
                (x as int) + 86_400,
            );
        }
    }
    if x < 0 {
        q - 1
    } else {
        q
    }
}

// ===========================================================================
// Time::with_subsec_nanosecond (jcore civil/time.rs:140-154), materialized
// here as a free fn: the time.rs module is closed to this batch (the
// steady-state append-only discipline); the body is the upstream
// b::SubsecNanosecond checkc plus the struct field replacement.
// ===========================================================================

/// Origin Rust (jcore time.rs:146-153):
///     pub const fn with_subsec_nanosecond(
///         self, subsec_nanosecond: i32,
///     ) -> Result<Time, RangeError> {
///         let subsec_nanosecond =
///             rtry!(b::SubsecNanosecond::checkc(subsec_nanosecond as i64));
///         Ok(Time { subsec_nanosecond, ..self })
///     }
/// Upstream doc (jcore time.rs:141-145):
///   Returns this time with its subsecond component replaced with the
///   nanosecond component given.
///   If the number of nanoseconds is out of range (`0..=999_999_999`),
///   then an error is returned.
exec fn time_with_subsec_nanosecond(
    t: Time,
    subsec_nanosecond: i32,
) -> (r: Option<Time>)
    ensures
        match r {
            Option::Some(t2) =>
                t2.hour == t.hour
                    && t2.minute == t.minute
                    && t2.second == t.second
                    && t2.subsec_nanosecond == subsec_nanosecond
                    && (valid_time(t) ==> valid_time(t2)),
            Option::None => !subsec_iv().contains(subsec_nanosecond as int),
        },
{
    let Some(subsec) = const_check::i32(
        0i32,
        999_999_999i32,
        subsec_nanosecond as i64,
    ) else {
        return Option::None;
    };
    Option::Some(Time {
        hour: t.hour,
        minute: t.minute,
        second: t.second,
        subsec_nanosecond: subsec,
    })
}

// ===========================================================================
// constants panel (the J2 finding-14 pattern: the MIN/MAX consts carry
// no verification obligation; this proof fn is their honest face)
// ===========================================================================

proof fn lemma_datetime_panel()
    ensures
        valid_datetime(DateTime::MIN)
            && valid_datetime(DateTime::MAX)
            && valid_date(DateTime::MIN.date)
            && valid_time(DateTime::MIN.time)
            && valid_date(DateTime::MAX.date)
            && valid_time(DateTime::MAX.time),
{
    let dmin: Date = DateTime::MIN.date;
    let tmin: Time = DateTime::MIN.time;
    assert(dmin.year as int == -9999);
    assert(dmin.month as int == 1);
    assert(dmin.day as int == 1);
    assert(tmin.hour as int == 0 && tmin.minute as int == 0);
    assert(tmin.second as int == 0);
    assert(tmin.subsec_nanosecond as int == 0);
    assert(year_iv().contains(-9999));
    assert(month_iv().contains(1));
    assert(days_in_month_spec(-9999, 1) >= 1);
    assert(valid_date(dmin) && valid_time(tmin));
    let dmax: Date = DateTime::MAX.date;
    let tmax: Time = DateTime::MAX.time;
    assert(dmax.year as int == 9999);
    assert(dmax.month as int == 12);
    assert(dmax.day as int == 31);
    assert(tmax.hour as int == 23 && tmax.minute as int == 59);
    assert(tmax.second as int == 59);
    assert(tmax.subsec_nanosecond as int == 999_999_999);
    assert(year_iv().contains(9999));
    assert(month_iv().contains(12));
    assert(days_in_month_spec(9999, 12) == 31);
    assert(hour_iv().contains(23) && minute_iv().contains(59));
    assert(second_iv().contains(59));
    assert(subsec_iv().contains(999_999_999));
    assert(valid_date(dmax) && valid_time(tmax));
}

// ===========================================================================
// wrapper delegation faces (jiff main-crate civil/datetime.rs): the pure
// Date/Time reassembly getters, each one citing its wrapper position;
// the delegate callees are the J2/J3 verified faces
// ===========================================================================

impl DateTime {
    /// Origin Rust (wrapper datetime.rs:464-465):
    ///     pub fn year(self) -> i16 { self.date().year() }
    /// Upstream doc (wrapper datetime.rs:450-451):
    ///   Returns the year for this datetime.
    ///   The value returned is guaranteed to be in the range
    ///   `-9999..=9999`.
    pub exec fn year(self) -> (r: i16)
        ensures
            (r as int) == (self.date.year as int)
                && (valid_datetime(self)
                    ==> year_iv().contains(r as int)),
    {
        // the upstream one-line delegation self.date().year() is
        // inlined through the public mirror fields (value-identical)
        self.date.year
    }

    /// Origin Rust (wrapper datetime.rs:522-523):
    ///     pub fn month(self) -> i8 { self.date().month() }
    /// Upstream doc (wrapper datetime.rs:508-509):
    ///   Returns the month for this datetime.
    ///   The value returned is guaranteed to be in the range `1..=12`.
    pub exec fn month(self) -> (r: i8)
        ensures
            (r as int) == (self.date.month as int)
                && (valid_datetime(self)
                    ==> month_iv().contains(r as int)),
    {
        self.date.month
    }

    /// Origin Rust (wrapper datetime.rs:539-540):
    ///     pub fn day(self) -> i8 { self.date().day() }
    /// Upstream doc (wrapper datetime.rs:525-526):
    ///   Returns the day for this datetime.
    ///   The value returned is guaranteed to be in the range `1..=31`.
    /// (Like the J2 days_in_month doc note, 1..=31 understates the real
    /// conditional bound 1..=days_in_month(year, month); the contract
    /// below pins the tight bound and the doc claim is implied by it.)
    pub exec fn day(self) -> (r: i8)
        ensures
            (r as int) == (self.date.day as int)
                && (valid_datetime(self) ==> 1 <= r as int
                    && (r as int)
                        <= days_in_month_spec(
                            (self.date.year as int),
                            (self.date.month as int),
                        )),
    {
        self.date.day
    }

    /// Origin Rust (wrapper datetime.rs:556-557):
    ///     pub fn hour(self) -> i8 { self.time().hour() }
    /// Upstream doc (wrapper datetime.rs:542-543):
    ///   Returns the "hour" component of this datetime.
    ///   The value returned is guaranteed to be in the range `0..=23`.
    pub exec fn hour(self) -> (r: i8)
        ensures
            (r as int) == (self.time.hour as int)
                && (valid_datetime(self)
                    ==> hour_iv().contains(r as int)),
    {
        self.time().hour()
    }

    /// Origin Rust (wrapper datetime.rs:573-574):
    ///     pub fn minute(self) -> i8 { self.time().minute() }
    /// Upstream doc (wrapper datetime.rs:559-560):
    ///   Returns the "minute" component of this datetime.
    ///   The value returned is guaranteed to be in the range `0..=59`.
    pub exec fn minute(self) -> (r: i8)
        ensures
            (r as int) == (self.time.minute as int)
                && (valid_datetime(self)
                    ==> minute_iv().contains(r as int)),
    {
        self.time().minute()
    }

    /// Origin Rust (wrapper datetime.rs:590-591):
    ///     pub fn second(self) -> i8 { self.time().second() }
    /// Upstream doc (wrapper datetime.rs:576-577):
    ///   Returns the "second" component of this datetime.
    ///   The value returned is guaranteed to be in the range `0..=59`.
    pub exec fn second(self) -> (r: i8)
        ensures
            (r as int) == (self.time.second as int)
                && (valid_datetime(self)
                    ==> second_iv().contains(r as int)),
    {
        self.time().second()
    }

    /// Origin Rust (wrapper datetime.rs:607-608):
    ///     pub fn millisecond(self) -> i16 { self.time().millisecond() }
    /// Upstream doc (wrapper datetime.rs:582-585):
    ///   Returns the "millisecond" component of this datetime.
    ///   The value returned is guaranteed to be in the range `0..=999`.
    pub exec fn millisecond(self) -> (r: i16)
        requires valid_datetime(self),
        ensures
            0 <= r as int && (r as int) <= 999
                && r as int
                    == ((self.time.subsec_nanosecond as int)
                        / 1_000_000),
    {
        let t = self.time;
        t.millisecond()
    }

    /// Origin Rust (wrapper datetime.rs:624-625):
    ///     pub fn microsecond(self) -> i16 { self.time().microsecond() }
    /// Upstream doc (wrapper datetime.rs:599-602):
    ///   Returns the "microsecond" component of this datetime.
    ///   The value returned is guaranteed to be in the range `0..=999`.
    pub exec fn microsecond(self) -> (r: i16)
        requires valid_datetime(self),
        ensures
            0 <= r as int && (r as int) <= 999
                && r as int
                    == (((self.time.subsec_nanosecond as int)
                        / 1_000) % 1_000),
    {
        let t = self.time;
        t.microsecond()
    }

    /// Origin Rust (wrapper datetime.rs:641-642):
    ///     pub fn nanosecond(self) -> i16 { self.time().nanosecond() }
    /// Upstream doc (wrapper datetime.rs:616-619):
    ///   Returns the "nanosecond" component of this datetime.
    ///   The value returned is guaranteed to be in the range `0..=999`.
    pub exec fn nanosecond(self) -> (r: i16)
        requires valid_datetime(self),
        ensures
            0 <= r as int && (r as int) <= 999
                && r as int
                    == ((self.time.subsec_nanosecond as int) % 1_000),
    {
        let t = self.time;
        t.nanosecond()
    }

    /// Origin Rust (wrapper datetime.rs:695-696):
    ///     pub fn subsec_nanosecond(self) -> i32 {
    ///         self.time().subsec_nanosecond()
    ///     }
    /// Upstream doc (wrapper datetime.rs:683-685):
    ///   Returns the fractional nanosecond for this `DateTime` value.
    ///   The value returned is guaranteed to be in the range
    ///   `0..=999_999_999`.
    pub exec fn subsec_nanosecond(self) -> (r: i32)
        ensures
            (r as int) == (self.time.subsec_nanosecond as int)
                && (valid_datetime(self)
                    ==> subsec_iv().contains(r as int)),
    {
        self.time().subsec_nanosecond()
    }

    /// Origin Rust (jiff main-crate datetime.rs:375-380, wrapper face of
    /// the jcore const constructors; the panicking const face
    /// materializes as the precondition, the J2 Date::constant precedent):
    ///     pub const fn constant(year: i16, month: i8, day: i8,
    ///         hour: i8, minute: i8, second: i8, subsec_nanosecond: i32,
    ///     ) -> DateTime {
    ///         let date = Date::constant(year, month, day);
    ///         let time = Time::constant(hour, minute, second,
    ///             subsec_nanosecond);
    ///         DateTime { date, time }
    ///     }
    /// Upstream doc (wrapper datetime.rs:282-311):
    ///   Creates a new `DateTime` value in a `const` context.
    ///   # Panics
    ///   This routine panics when [`DateTime::new`] would return an error.
    ///   [The seven component-bounds bullets: year -9999..=9999, month
    ///   1..=12, day 1..=days_in_month(year, month), 0 <= hour <= 23,
    ///   0 <= minute <= 59, 0 <= second <= 59,
    ///   0 <= subsec_nanosecond <= 999,999,999.]
    pub exec fn constant(
        year: i16,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> (dt: DateTime)
        requires
            year_iv().contains(year as int)
                && month_iv().contains(month as int)
                && 1 <= day as int
                && (day as int)
                    <= days_in_month_spec(year as int, month as int)
                && hour_iv().contains(hour as int)
                && minute_iv().contains(minute as int)
                && second_iv().contains(second as int)
                && subsec_iv().contains(subsec_nanosecond as int),
        ensures
            dt.date.year as int == year as int
                && dt.date.month as int == month as int
                && dt.date.day as int == day as int
                && dt.time.hour as int == hour as int
                && dt.time.minute as int == minute as int
                && dt.time.second as int == second as int
                && (dt.time.subsec_nanosecond as int)
                    == (subsec_nanosecond as int)
                && valid_datetime(dt),
    {
        let Some(dt) = DateTime::new(
            year,
            month,
            day,
            hour,
            minute,
            second,
            subsec_nanosecond,
        ) else {
            proof { assert(false); }
            unreachable!()
        };
        dt
    }

    /// Origin Rust (wrapper datetime.rs:967-971):
    ///     pub fn tomorrow(self) -> Result<DateTime, Error> {
    ///         Ok(DateTime::from_parts(self.date().tomorrow()?, self.time()))
    ///     }
    /// Upstream doc (wrapper datetime.rs:943-958):
    ///   Returns the datetime with a date immediately following this one.
    ///   The time in the datetime returned remains unchanged.
    ///   # Errors
    ///   This returns an error when this datetime's date is the maximum
    ///   value.
    pub exec fn tomorrow(self) -> (r: Option<DateTime>)
        requires valid_datetime(self),
        ensures
            match r {
                Option::Some(dt) =>
                    match spec_tomorrow(self.date) {
                        Option::Some(d) => dt.date == d
                            && dt.time == self.time
                            && valid_datetime(dt),
                        Option::None => false,
                    },
                Option::None => spec_tomorrow(self.date) is None,
            },
    {
        let Some(date) = self.date().tomorrow() else {
            return Option::None;
        };
        Option::Some(DateTime { date, time: self.time })
    }

    /// Origin Rust (wrapper datetime.rs:993-997):
    ///     pub fn yesterday(self) -> Result<DateTime, Error> {
    ///         Ok(DateTime::from_parts(self.date().yesterday()?, self.time()))
    ///     }
    /// Upstream doc (wrapper datetime.rs:974-989):
    ///   Returns the datetime with a date immediately preceding this one.
    ///   The time in the datetime returned remains unchanged.
    ///   # Errors
    ///   This returns an error when this datetime's date is the minimum
    ///   value.
    pub exec fn yesterday(self) -> (r: Option<DateTime>)
        requires valid_datetime(self),
        ensures
            match r {
                Option::Some(dt) =>
                    match spec_yesterday(self.date) {
                        Option::Some(d) => dt.date == d
                            && dt.time == self.time
                            && valid_datetime(dt),
                        Option::None => false,
                    },
                Option::None => spec_yesterday(self.date) is None,
            },
    {
        let Some(date) = self.date().yesterday() else {
            return Option::None;
        };
        Option::Some(DateTime { date, time: self.time })
    }

    /// Origin Rust (wrapper datetime.rs:790-792):
    ///     pub fn start_of_day(&self) -> DateTime {
    ///         DateTime::from_parts(self.date(), Time::MIN)
    ///     }
    /// Upstream doc (wrapper datetime.rs:776-779):
    ///   Returns the beginning of the day that this datetime resides in.
    ///   That is, the datetime returned always keeps the same date, but its
    ///   time is always `00:00:00` (midnight).
    /// Time::MIN is the midnight literal (jcore time.rs:25-27); the
    /// from_parts call materializes as the direct construction.
    pub exec fn start_of_day(self) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            r.date == self.date
                && r.time.hour as int == 0
                && r.time.minute as int == 0
                && r.time.second as int == 0
                && r.time.subsec_nanosecond as int == 0
                && valid_datetime(r),
    {
        DateTime {
            date: self.date,
            time: Time {
                hour: 0i8,
                minute: 0i8,
                second: 0i8,
                subsec_nanosecond: 0i32,
            },
        }
    }

    /// Origin Rust (wrapper datetime.rs:811-813):
    ///     pub fn end_of_day(&self) -> DateTime {
    ///         DateTime::from_parts(self.date(), Time::MAX)
    ///     }
    /// Upstream doc (wrapper datetime.rs:797-800):
    ///   Returns the end of the day that this datetime resides in.
    ///   That is, the datetime returned always keeps the same date, but its
    ///   time is always `23:59:59.999999999`.
    /// Time::MAX is that literal (jcore time.rs:31-35).
    pub exec fn end_of_day(self) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            r.date == self.date
                && r.time.hour as int == 23
                && r.time.minute as int == 59
                && r.time.second as int == 59
                && r.time.subsec_nanosecond as int == 999_999_999
                && valid_datetime(r),
    {
        DateTime {
            date: self.date,
            time: Time {
                hour: 23i8,
                minute: 59i8,
                second: 59i8,
                subsec_nanosecond: 999_999_999i32,
            },
        }
    }

    /// Origin Rust (wrapper datetime.rs:828-830):
    ///     pub fn first_of_month(self) -> DateTime {
    ///         DateTime::from_parts(self.date().first_of_month(), self.time())
    ///     }
    /// Upstream doc (wrapper datetime.rs:813-815):
    ///   Returns the first date of the month that this datetime resides in.
    ///   The time in the datetime returned remains unchanged.
    pub exec fn first_of_month(self) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            r.date.year as int == self.date.year as int
                && r.date.month as int == self.date.month as int
                && r.date.day as int == 1
                && r.time == self.time
                && valid_datetime(r),
    {
        DateTime {
            date: self.date.first_of_month(),
            time: self.time,
        }
    }

    /// Origin Rust (wrapper datetime.rs:845-847):
    ///     pub fn last_of_month(self) -> DateTime {
    ///         DateTime::from_parts(self.date().last_of_month(), self.time())
    ///     }
    /// Upstream doc (wrapper datetime.rs:830-832):
    ///   Returns the last date of the month that this datetime resides in.
    ///   The time in the datetime returned remains unchanged.
    pub exec fn last_of_month(self) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            r.date.year as int == self.date.year as int
                && r.date.month as int == self.date.month as int
                && r.date.day as int
                    == days_in_month_spec(
                        (self.date.year as int),
                        (self.date.month as int),
                    )
                && r.time == self.time
                && valid_datetime(r),
    {
        DateTime {
            date: self.date.last_of_month(),
            time: self.time,
        }
    }

    /// Origin Rust (wrapper datetime.rs:870-872):
    ///     pub fn days_in_month(self) -> i8 {
    ///         self.date().days_in_month()
    ///     }
    /// Upstream doc (wrapper datetime.rs:849-853):
    ///   Returns the total number of days in the the month in which this
    ///   datetime resides.
    ///   This is guaranteed to always return one of the following values,
    ///   depending on the year and the month: 28, 29, 30 or 31.
    pub exec fn days_in_month(self) -> (r: i8)
        requires valid_datetime(self),
        ensures
            r as int
                == days_in_month_spec(
                    (self.date.year as int),
                    (self.date.month as int),
                )
                && 28 <= r as int
                && (r as int) <= 31,
    {
        self.date.days_in_month()
    }

    /// Origin Rust (wrapper datetime.rs:887-889):
    ///     pub fn first_of_year(self) -> DateTime {
    ///         DateTime::from_parts(self.date().first_of_year(), self.time())
    ///     }
    /// Upstream doc (wrapper datetime.rs:872-874):
    ///   Returns the first date of the year that this datetime resides in.
    ///   The time in the datetime returned remains unchanged.
    pub exec fn first_of_year(self) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            r.date.year as int == self.date.year as int
                && r.date.month as int == 1
                && r.date.day as int == 1
                && r.time == self.time
                && valid_datetime(r),
    {
        DateTime {
            date: self.date.first_of_year(),
            time: self.time,
        }
    }

    /// Origin Rust (wrapper datetime.rs:904-906):
    ///     pub fn last_of_year(self) -> DateTime {
    ///         DateTime::from_parts(self.date().last_of_year(), self.time())
    ///     }
    /// Upstream doc (wrapper datetime.rs:889-891):
    ///   Returns the last date of the year that this datetime resides in.
    ///   The time in the datetime returned remains unchanged.
    pub exec fn last_of_year(self) -> (r: DateTime)
        requires valid_datetime(self),
        ensures
            r.date.year as int == self.date.year as int
                && r.date.month as int == 12
                && r.date.day as int == 31
                && r.time == self.time
                && valid_datetime(r),
    {
        DateTime {
            date: self.date.last_of_year(),
            time: self.time,
        }
    }

    /// Origin Rust (wrapper datetime.rs:925-927):
    ///     pub fn days_in_year(self) -> i16 {
    ///         self.date().days_in_year()
    ///     }
    /// Upstream doc (wrapper datetime.rs:910-913):
    ///   Returns the total number of days in the the year in which this
    ///   datetime resides.
    ///   This is guaranteed to always return either `365` or `366`.
    pub exec fn days_in_year(self) -> (r: i16)
        requires valid_datetime(self),
        ensures
            r as int
                == if is_leap_year_spec(self.date.year as int) {
                    366int
                } else {
                    365int
                }
                && (r as int == 365 || r as int == 366),
    {
        self.date.days_in_year()
    }

    /// Origin Rust (wrapper datetime.rs:941-942):
    ///     pub fn in_leap_year(self) -> bool {
    ///         self.date().in_leap_year()
    ///     }
    /// Upstream doc (wrapper datetime.rs:926-933):
    ///   Returns true if and only if the year in which this datetime resides
    ///   is a leap year.
    ///   Every astronomical year has either 365 or 366 days [...]
    pub exec fn in_leap_year(self) -> (r: bool)
        requires valid_datetime(self),
        ensures r == is_leap_year_spec(self.date.year as int),
    {
        self.date.in_leap_year()
    }
}

} // verus!
