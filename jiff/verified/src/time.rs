//! Batch J3 -- the civil time core, Verus transcription of:
//!   - code/crates/jiff-core/src/civil/time.rs (Time, TimeSecond,
//!     TimeNanosecond; the implementation bodies at this pin:
//!     Time::new at time.rs:43-55, hour :62, minute :71, second :80,
//!     millisecond :88, microsecond :96, nanosecond :105,
//!     subsec_nanosecond :115, to_second :164, to_nanosecond :179,
//!     TimeSecond::new :310, TimeSecond::constant :320,
//!     TimeSecond::second :329, TimeSecond::overflowing_add :346,
//!     TimeSecond::to_time :363-384, TimeNanosecond::new :401,
//!     TimeNanosecond::nanosecond :412,
//!     TimeNanosecond::overflowing_add :429,
//!     TimeNanosecond::to_time :446)
//!   - the public wrapper faces in code/crates/jiff/src/civil/time.rs
//!     (Time::new :279, Time::constant :322, Time::midnight :353,
//!     hour :401, minute :418, second :435, millisecond :452,
//!     microsecond :469, nanosecond :486, subsec_nanosecond :538,
//!     wrapping_add :699, wrapping_add_span :705, wrapping_sub :786,
//!     checked_add :919, checked_add_duration :937, checked_sub :984,
//!     until_nanoseconds :1690, to_second :1722, from_second :1732,
//!     to_nanosecond :1745, from_nanosecond :1755)
//!   - the free constructor civil::time() (code/crates/jiff/src/civil/
//!     mod.rs:284-289; the J2 notes pass-down's mod.rs:155 pointer is
//!     stale at this pin -- lines 150-169 there are the datetime docs
//!     area; the measured position is recorded in J3/notes.md)
//! The J2 notes' "Time::new at jcore time.rs:~186-215" positional guess is
//! likewise superseded by the measured :43-55.
//!
//! Materialization ledger (this file):
//! - Result<T, RangeError / Error> faces materialize as Option<T> (J1
//!   bounds.rs ledger: the error value is a zero-sized witness).
//! - const fn materializes as exec fn (no const verification in this
//!   build); core::ops / Display / serde / strtime faces are out of the
//!   batch. The TimeArithmetic generic (`A: Into<TimeArithmetic>`)
//!   materializes through the canonical quickcheck instantiation, a
//!   bare-nanoseconds `Span::new().nanoseconds(n)`: every arm tours
//!   through the civil-day nanosecond accumulator, so the arithmetic faces
//!   below are `*_nanos` and the Span surface itself stays cut (inventory
//!   trimming principle 5). The SignedDuration/UnsignedDuration arms
//!   (wrapper time.rs:726/:738) are J4b territory (jcore_signed_duration
//!   .rs is another agent's file) and stay out of this closure.
//! - The u32/u64 "faster division" casts upstream uses inside
//!   TimeSecond/TimeNanosecond to_time (jcore time.rs:374, :449)
//!   materialize at i64: every operand there is non-negative and < 2^32,
//!   so i64 arithmetic is value-identical; J2's is_leap_year i16->i64
//!   precedent.
//! - `wrapping_add_nanos` keeps upstream's machine `wrapping_add` under a
//!   |nanos| <= 2^62 precondition: outside that window upstream's program
//!   wraps mod 2^64 before the civil-day reduction (a mod-2^64 face this
//!   batch defers); the quickcheck domain (nanos spans in
//!   b::CivilDayNanosecond 0..=86_399_999_999_999, jcore bounds.rs:141-146)
//!   is deep inside the window. Same for `wrapping_sub_nanos` (which goes
//!   through Span::negate upstream, wrapper time.rs:2212).
//! - checked_sub_nanos' i64::MIN None arm mirrors the upstream
//!   checked_neg failure (TimeArithmetic::checked_neg, wrapper
//!   time.rs:2239, errors when negating a nanos-only span exactly at
//!   i64::MIN), the same edge treatment as batch J2's Date::checked_sub
//!   i32::MIN face.
//! - first_of_hour / last_of_hour: absent from this pin entirely (a grep
//!   over both crates returns no hit); nothing to transcribe -- the
//!   batch-plan item is recorded as measured-out in notes.md.
//! - Validity model: valid_time(Time) is the exact bounds conjunction of
//!   the four J1 interval faces (Hour/Minute/Second/SubsecNanosecond,
//!   jcore bounds.rs:217/:232/:298/:301), standing in for upstream's
//!   private-field type discipline (jcore time.rs:14-19).
//! - The day-carry heart (item 3 of the batch plan) is
//!   TimeNanosecond::overflowing_add (jcore :429-439) plus its std
//!   div_euclid/rem_euclid inlines at the NANOS_PER_CIVIL_DAY divisor
//!   (toolchain finding 13: no vstd spec for the std methods; J2's
//!   rem_euclid_12 chain transplanted to the i64 civil-day divisor,
//!   pre-verified by the batch's capability probe).

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_mod_multiples_basic, lemma_mod_multiples_vanish, rust_div,
    rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add, lemma_mul_is_distributive_add_other_way,
    lemma_mul_unary_negation,
};

use super::bounds::{Interval, const_check};

verus! {

// ===========================================================================
// spec models (the J1 interval faces of the clock fields + the civil-day
// nanosecond space)
//
// Spec-mirror values are spelled as int literals with the upstream const
// factorization cited per item; the exec constants are tied to the mirrors
// in lemma_time_panel (constants have no verification obligation of their
// own -- J2 toolchain finding 14).
// ===========================================================================

/// spec mirror of the i64 NANOS_PER_CIVIL_DAY constant (jcore constants
/// .rs:20: HOURS_PER_CIVIL_DAY * NANOS_PER_HOUR = 86_400_000_000_000).
pub open spec fn nanos_per_civil_day() -> int { 86_400_000_000_000 }

/// The Hour interval (jcore bounds.rs:217: (Hour, i8, "hour", 0, 23)).
pub open spec fn hour_iv() -> Interval { Interval { min: 0, max: 23 } }

/// The Minute interval (jcore bounds.rs:232: (Minute, i8, 0, 59)).
pub open spec fn minute_iv() -> Interval { Interval { min: 0, max: 59 } }

/// The Second interval (jcore bounds.rs:298: (Second, i8, 0, 59)).
pub open spec fn second_iv() -> Interval { Interval { min: 0, max: 59 } }

/// The SubsecNanosecond interval (jcore bounds.rs:301: 0,
/// c::NANOS_PER_SEC_32 - 1, i.e. 0..=999_999_999).
pub open spec fn subsec_iv() -> Interval {
    Interval { min: 0, max: 999_999_999 }
}

/// The CivilDayNanosecond interval (jcore bounds.rs:141-146: 0,
/// c::NANOS_PER_CIVIL_DAY - 1, nanoseconds in one civil day).
pub open spec fn cdn_iv() -> Interval {
    Interval { min: 0, max: 86_399_999_999_999 }
}

/// The CivilDaySecond interval (jcore bounds.rs:150-155: 0,
/// c::SECS_PER_CIVIL_DAY_32 - 1, i.e. 0..=86_399).
pub open spec fn cds_iv() -> Interval { Interval { min: 0, max: 86_399 } }

/// Clock validity of a Time quadruple: the conjunction of the four J1
/// bounds checks Time::new performs (jcore time.rs:49-53), standing in
/// for upstream's private-field discipline.
pub open spec fn valid_time(t: Time) -> bool {
    hour_iv().contains(t.hour as int)
        && minute_iv().contains(t.minute as int)
        && second_iv().contains(t.second as int)
        && subsec_iv().contains(t.subsec_nanosecond as int)
}

/// Upstream doc (jcore time.rs:172-175):
///   Converts this civil time to a nanosecond value corresponding to the
///   number of nanoseconds that has elapsed since midnight until this time.
/// This is the exact accumulator of Time::to_nanosecond (jcore :180-184).
pub open spec fn time_nanos_spec(t: Time) -> int {
    (t.hour as int) * 3_600_000_000_000
        + (t.minute as int) * 60_000_000_000
        + (t.second as int) * 1_000_000_000
        + (t.subsec_nanosecond as int)
}

/// Upstream doc (jcore time.rs:155-156):
///   Converts this civil time to a second value corresponding to the
///   number of seconds that has elapsed since midnight until this time.
/// The exact accumulator of Time::to_second (jcore :165-168).
pub open spec fn time_secs_spec(t: Time) -> int {
    (t.hour as int) * 3600
        + (t.minute as int) * 60
        + (t.second as int)
}

/// Spec twin of TimeSecond::to_time (jcore :363-384): the true component
/// decomposition of a civil-day second value. The upstream
/// "power-complement-padding" body computes exactly these fields (proof on
/// the exec face below); the subsecond component is always 0 (jcore
/// :358-360).
pub open spec fn spec_time_from_second(s: int) -> Time {
    Time {
        hour: (s / 3600) as i8,
        minute: ((s % 3600) / 60) as i8,
        second: (s % 60) as i8,
        subsec_nanosecond: 0,
    }
}

/// Spec twin of TimeNanosecond::to_time (jcore :446-455): the
/// seconds-of-day decomposition of a civil-day nanosecond value plus the
/// nanosecond remainder.
pub open spec fn spec_time_from_nanosecond(n: int) -> Time {
    let s: int = n / 1_000_000_000;
    Time {
        hour: (s / 3600) as i8,
        minute: ((s % 3600) / 60) as i8,
        second: (s % 60) as i8,
        subsec_nanosecond: (n % 1_000_000_000) as i32,
    }
}

/// Spec twin of Time::checked_add_nanos (the Some arm is the in-day sum;
/// the None arm is any over- or underflow past the civil-day bounds --
/// upstream error face: any non-zero non-time unit in the overflowing
/// remainder, wrapper time.rs:928-934).
pub open spec fn spec_checked_add_nanos(t: Time, n: int) -> Option<Time> {
    let sum: int = time_nanos_spec(t) + n;
    if cdn_iv().contains(sum) {
        Option::Some(spec_time_from_nanosecond(sum))
    } else {
        Option::None
    }
}

/// Spec twin of Time::checked_sub_nanos (the duration-negated face).
pub open spec fn spec_checked_sub_nanos(t: Time, n: int) -> Option<Time> {
    let diff: int = time_nanos_spec(t) - n;
    if cdn_iv().contains(diff) {
        Option::Some(spec_time_from_nanosecond(diff))
    } else {
        Option::None
    }
}

/// Spec twin of Time::wrapping_add_nanos (the civil-day reduction of the
/// sum; wrapper time.rs:720 `sum.rem_euclid(c::NANOS_PER_CIVIL_DAY)`).
pub open spec fn spec_wrapping_add_nanos(t: Time, n: int) -> Time {
    spec_time_from_nanosecond(
        (time_nanos_spec(t) + n) % nanos_per_civil_day(),
    )
}

/// Spec twin of Time::wrapping_sub_nanos.
pub open spec fn spec_wrapping_sub_nanos(t: Time, n: int) -> Time {
    spec_time_from_nanosecond(
        (time_nanos_spec(t) - n) % nanos_per_civil_day(),
    )
}

/// Constant-layer panel (J2 finding 14): the mirrors equal the exec
/// constants the upstream bodies actually run.
proof fn lemma_time_panel() {
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(1, 1);
    assert(1 == 1 * 1);
    assert(super::constants::NANOS_PER_CIVIL_DAY as int
        == nanos_per_civil_day());
    assert(super::constants::NANOS_PER_SEC_32 as int == 1_000_000_000);
    assert(super::constants::NANOS_PER_MILLI_32 as int == 1_000_000);
    assert(super::constants::NANOS_PER_MICRO_32 as int == 1_000);
    assert(super::constants::MICROS_PER_MILLI_32 as int == 1_000);
    assert(super::constants::SECS_PER_CIVIL_DAY_32 as int == 86_400);
    assert(subsec_iv().max == (super::constants::NANOS_PER_SEC_32 as int) - 1);
    assert(cdn_iv().max
        == (super::constants::NANOS_PER_CIVIL_DAY as int) - 1);
    assert(cds_iv().max
        == (super::constants::SECS_PER_CIVIL_DAY_32 as int) - 1);
}

// ===========================================================================
// std div_euclid / rem_euclid inlines at the civil-day nanosecond divisor
// (the J2 finding-13 pattern: these std methods have no vstd spec in this
// build; the bodies are the stable std implementations, and jcore's
// overflow helpers run them at the fixed divisor NANOS_PER_CIVIL_DAY)
// ===========================================================================

/// std i64::rem_euclid body (self % rhs, + rhs when the remainder is
/// negative), inlined at the NANOS_PER_CIVIL_DAY divisor. Full i64 domain:
/// the trunc remainder sits in (-(D-1))..=(D-1) and the + D fix-up cannot
/// overflow, so no caller-side domain restriction is needed (contrast
/// J2's rem_euclid_12, whose i32 width forced the |a| <= 2^30 guard).
/// Probe-verified shape (no |a| domain restriction needed).
pub exec fn rem_euclid_civilday(a: i64) -> (r: i64)
    ensures
        r as int == (a as int) % nanos_per_civil_day()
            && 0 <= r as int
            && (r as int) < nanos_per_civil_day(),
{
    let x = a % 86_400_000_000_000i64;
    proof {
        let ai: int = a as int;
        let di: int = nanos_per_civil_day();
        assert(x as int == rust_rem(ai, di));
        if a == 0 {
            assert(rust_rem(ai, di) == 0);
            assert(ai % di == 0);
        } else if a > 0 {
            assert(rust_rem(ai, di) == ai % di);
        } else {
            let n: int = 0 - ai;
            let q: int = n / di;
            let e: int = n % di;
            lemma_fundamental_div_mod(n, di);
            assert(n == di * q + e);
            assert(0 <= e < di);
            lemma_mul_is_commutative(q, di);
            lemma_mul_unary_negation(q, di);
            assert(ai == (0 - q) * di + (0 - e));
            if x == 0 {
                assert(ai == (0 - q) * di);
                assert(rust_rem(ai, di) == 0);
                lemma_mod_multiples_basic(0 - q, di);
                assert(((0 - q) * di) % di == 0);
                assert(ai % di == 0);
            } else {
                let w: int = di - e;
                assert(0 < w < di);
                lemma_mul_is_distributive_add_other_way(di, q, 1);
                lemma_mul_basics(di);
                assert((q + 1) * di == q * di + 1 * di);
                assert(1 * di == di);
                assert((q + 1) * di == q * di + di);
                lemma_mul_unary_negation(q + 1, di);
                assert((0 - (q + 1)) * di == (0 - q * di) - di);
                assert(ai == (0 - (q + 1)) * di + w);
                lemma_fundamental_div_mod_converse(ai, di, 0 - (q + 1), w);
                assert(ai % di == w);
                assert(rust_rem(ai, di) == 0 - e);
                assert(x as int == 0 - e);
                assert(x as int + di == w);
            }
        }
    }
    if x < 0 {
        x + 86_400_000_000_000i64
    } else {
        x
    }
}

/// std i64::div_euclid (stable std source, core::num):
///     let q = self / rhs;
///     if self % rhs < 0 { q - 1 } else { q }   // for rhs > 0
/// inlined at the NANOS_PER_CIVIL_DAY divisor, with its Euclid-division
/// contract. No overflow: only a subtraction on the quotient.
pub exec fn div_euclid_civilday(a: i64) -> (q: i64)
    ensures
        (q as int) * nanos_per_civil_day()
            + ((a as int) % nanos_per_civil_day())
            == a as int
            && (q as int) == (a as int) / nanos_per_civil_day(),
{
    let q = a / 86_400_000_000_000i64;
    let x = a % 86_400_000_000_000i64;
    proof {
        let ai: int = a as int;
        let di: int = nanos_per_civil_day();
        assert(x as int == rust_rem(ai, di));
        let tr: int = rust_div(ai, di);
        assert(q as int == tr);
        assert(ai == di * tr + (x as int));
        let e: int = ai % di;
        if x >= 0 {
            assert(e == x as int);
            lemma_fundamental_div_mod_converse(ai, di, tr, e);
        } else {
            let qm: int = tr - 1;
            assert(e == (x as int) + di);
            lemma_mul_is_distributive_add_other_way(di, qm, 1);
            lemma_mul_basics(di);
            assert((qm + 1) * di == qm * di + 1 * di);
            assert(1 * di == di);
            assert((qm + 1) * di == qm * di + di);
            lemma_mul_is_commutative(qm + 1, di);
            // di * tr == tr * di == (qm + 1) * di == qm * di + di
            assert(di * tr == qm * di + di);
            assert(ai == qm * di + ((x as int) + di));
            lemma_fundamental_div_mod_converse(
                ai,
                di,
                qm,
                (x as int) + di,
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
// Time (jcore civil/time.rs:14-209; the wrapper faces live in the jiff
// main crate at code/crates/jiff/src/civil/time.rs:223+)
// ===========================================================================

/// Origin Rust (jcore time.rs:14-19):
///     pub struct Time {
///         hour: i8,
///         minute: i8,
///         second: i8,
///         subsec_nanosecond: i32,
///     }
/// Upstream doc (jcore time.rs:8-11):
///   The civil time of day.
///   This time's representation uses nanosecond precision. The full range
///   of clock values are `00:00:00.000000000` to `23:59:59.999999999`
///   inclusive.
/// Fields are public here (no private-field type discipline in the
/// closure); valid_time (above) is the carrying invariant instead.
#[derive(Clone, Copy)]
pub struct Time {
    pub hour: i8,
    pub minute: i8,
    pub second: i8,
    pub subsec_nanosecond: i32,
}

impl Time {
    /// Origin Rust (wrapper time.rs:279-288 / jcore time.rs:43-55):
    ///     pub const fn new(hour: i8, minute: i8, second: i8,
    ///         subsec_nanosecond: i32) -> Result<Time, RangeError>
    /// Upstream doc (wrapper time.rs:245-253):
    ///   # Errors
    ///   This returns an error unless *all* of the following conditions
    ///   are true:
    ///   * `0 <= hour <= 23`
    ///   * `0 <= minute <= 59`
    ///   * `0 <= second <= 59`
    ///   * `0 <= subsec_nanosecond <= 999,999,999`
    /// The rtry! macros transcribe as their let-else expansions; the four
    /// b::X::checkc calls materialize through J1's const_check core with
    /// each type's interval constants -- Hour/Minute/Second/SubsecNanosecond,
    /// jcore bounds.rs:217/:232/:298/:301, the exact parameterization the
    /// define_bounds! macro gives their checkc methods.
    pub exec fn new(
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> (r: Option<Time>)
        ensures
            match r {
                Option::Some(t) => t.hour as int == hour as int
                    && t.minute as int == minute as int
                    && t.second as int == second as int
                    && t.subsec_nanosecond as int
                        == subsec_nanosecond as int
                    && valid_time(t),
                Option::None => !(
                    hour_iv().contains(hour as int)
                        && minute_iv().contains(minute as int)
                        && second_iv().contains(second as int)
                        && subsec_iv().contains(subsec_nanosecond as int)
                ),
            },
    {
        let Some(hour) = const_check::i8(0i8, 23i8, hour as i64) else {
            return Option::None;
        };
        let Some(minute) = const_check::i8(0i8, 59i8, minute as i64) else {
            return Option::None;
        };
        let Some(second) = const_check::i8(0i8, 59i8, second as i64) else {
            return Option::None;
        };
        let Some(subsec_nanosecond) =
            const_check::i32(0i32, 999_999_999i32, subsec_nanosecond as i64)
        else {
            return Option::None;
        };
        Option::Some(Time {
            hour,
            minute,
            second,
            subsec_nanosecond,
        })
    }

    /// Origin Rust (wrapper time.rs:322-332):
    ///     pub const fn constant(hour: i8, minute: i8, second: i8,
    ///         subsec_nanosecond: i32) -> Time
    /// Upstream doc (wrapper time.rs:290-303):
    ///   Creates a new `Time` value in a `const` context.
    ///   # Panics
    ///   This panics if the given values do not correspond to a valid
    ///   `Time`. All of the following conditions must be true: [...]
    /// The panic face materializes as the precondition (J2's
    /// Date::constant precedent); the unwrapr/const machinery has no
    /// further runtime contract.
    pub exec fn constant(
        hour: i8,
        minute: i8,
        second: i8,
        subsec_nanosecond: i32,
    ) -> (t: Time)
        requires
            hour_iv().contains(hour as int)
                && minute_iv().contains(minute as int)
                && second_iv().contains(second as int)
                && subsec_iv().contains(subsec_nanosecond as int),
        ensures
            t.hour as int == hour as int
                && t.minute as int == minute as int
                && t.second as int == second as int
                && t.subsec_nanosecond as int
                    == subsec_nanosecond as int
                && valid_time(t),
    {
        let Some(t) = Time::new(hour, minute, second, subsec_nanosecond)
        else {
            proof { assert(false); }
            unreachable!()
        };
        t
    }

    /// Origin Rust (wrapper time.rs:353-355):
    ///     pub const fn midnight() -> Time {
    ///         Time::constant(0, 0, 0, 0)
    ///     }
    /// Upstream doc (wrapper time.rs:334-338):
    ///   Returns the first moment of time in a day.
    ///   Specifically, this has the `hour`, `minute`, `second`,
    ///   `millisecond`, `microsecond` and `nanosecond` fields all set to
    ///   `0`.
    /// (Time::MIN is this value via const context, wrapper time.rs:228-231;
    /// const items carry no obligation -- panel note only.)
    pub exec fn midnight() -> (t: Time)
        ensures
            t.hour as int == 0
                && t.minute as int == 0
                && t.second as int == 0
                && t.subsec_nanosecond as int == 0
                && valid_time(t),
    {
        Time::constant(0, 0, 0, 0)
    }

    /// Origin Rust (jcore time.rs:62-64):
    ///     pub const fn hour(self) -> i8 { self.hour }
    /// Upstream doc (jcore time.rs:57-60):
    ///   Returns the hour component of this civil time.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`Hour`](crate::bounds::Hour).
    pub exec fn hour(self) -> (r: i8)
        ensures
            r as int == self.hour as int
                && (valid_time(self) ==> hour_iv().contains(r as int)),
    {
        self.hour
    }

    /// Origin Rust (jcore time.rs:71-73):
    ///     pub const fn minute(self) -> i8 { self.minute }
    /// Upstream doc (jcore time.rs:66-69):
    ///   Returns the minute component of this civil time.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`Minute`](crate::bounds::Minute).
    pub exec fn minute(self) -> (r: i8)
        ensures
            r as int == self.minute as int
                && (valid_time(self) ==> minute_iv().contains(r as int)),
    {
        self.minute
    }

    /// Origin Rust (jcore time.rs:80-82):
    ///     pub const fn second(self) -> i8 { self.second }
    /// Upstream doc (jcore time.rs:75-78):
    ///   Returns the second component of this civil time.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`Second`](crate::bounds::Second).
    pub exec fn second(self) -> (r: i8)
        ensures
            r as int == self.second as int
                && (valid_time(self) ==> second_iv().contains(r as int)),
    {
        self.second
    }

    /// Origin Rust (jcore time.rs:88-90):
    ///     pub const fn millisecond(self) -> i16 {
    ///         (self.subsec_nanosecond() as u32
    ///             / c::NANOS_PER_MILLI_32 as u32) as i16
    ///     }
    /// Upstream doc (jcore time.rs:84-86):
    ///   Returns the "millisecond" component of this time.
    ///   The value returned is guaranteed to be in the range `0..=999`.
    /// NANOS_PER_MILLI_32 = 1_000_000 (jcore constants.rs:36-37,
    /// MICROS_PER_MILLI_32 * NANOS_PER_MICRO_32); the u32 division
    /// materializes at i64 (ledger: operands non-negative there).
    pub exec fn millisecond(self) -> (r: i16)
        requires valid_time(self),
        ensures
            0 <= r as int && (r as int) <= 999
                && r as int
                    == (self.subsec_nanosecond as int) / 1_000_000,
    {
        ((self.subsec_nanosecond as i64) / 1_000_000i64) as i16
    }

    /// Origin Rust (jcore time.rs:96-99):
    ///     pub const fn microsecond(self) -> i16 {
    ///         ((self.subsec_nanosecond() as u32
    ///             / c::NANOS_PER_MICRO_32 as u32)
    ///             % c::MICROS_PER_MILLI_32 as u32) as i16
    ///     }
    /// Upstream doc (jcore time.rs:92-94):
    ///   Returns the "microsecond" component of this time.
    ///   The value returned is guaranteed to be in the range `0..=999`.
    /// (NANOS_PER_MICRO_32 = MICROS_PER_MILLI_32 = 1_000, jcore
    /// constants.rs:34-35/:38-39.)
    pub exec fn microsecond(self) -> (r: i16)
        requires valid_time(self),
        ensures
            0 <= r as int && (r as int) <= 999
                && r as int
                    == ((self.subsec_nanosecond as int) / 1_000) % 1_000,
    {
        (((self.subsec_nanosecond as i64) / 1_000i64) % 1_000i64) as i16
    }

    /// Origin Rust (jcore time.rs:105-107):
    ///     pub const fn nanosecond(self) -> i16 {
    ///         (self.subsec_nanosecond() as u32
    ///             % c::NANOS_PER_MICRO_32 as u32) as i16
    ///     }
    /// Upstream doc (jcore time.rs:101-103):
    ///   Returns the "nanosecond" component of this time.
    ///   The value returned is guaranteed to be in the range `0..=999`.
    pub exec fn nanosecond(self) -> (r: i16)
        requires valid_time(self),
        ensures
            0 <= r as int && (r as int) <= 999
                && r as int
                    == (self.subsec_nanosecond as int) % 1_000,
    {
        ((self.subsec_nanosecond as i64) % 1_000i64) as i16
    }

    /// Origin Rust (jcore time.rs:115-117):
    ///     pub const fn subsec_nanosecond(self) -> i32 {
    ///         self.subsec_nanosecond
    ///     }
    /// Upstream doc (jcore time.rs:109-113):
    ///   Returns the fractional second (to nanosecond precision) component
    ///   of this civil time.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`SubsecNanosecond`](crate::bounds::SubsecNanosecond).
    pub exec fn subsec_nanosecond(self) -> (r: i32)
        ensures
            r as int == self.subsec_nanosecond as int
                && (valid_time(self) ==> subsec_iv().contains(r as int)),
    {
        self.subsec_nanosecond
    }

    /// Origin Rust (jcore time.rs:164-170):
    ///     pub const fn to_second(self) -> TimeSecond {
    ///         let mut second: i32 = 0;
    ///         second += (self.hour() as i32) * 3600;
    ///         second += (self.minute() as i32) * 60;
    ///         second += self.second() as i32;
    ///         TimeSecond { second }
    ///     }
    /// Upstream doc (jcore time.rs:155-162):
    ///   Converts this civil time to a second value corresponding to the
    ///   number of seconds that has elapsed since midnight until this
    ///   time. If this time is midnight, then the second value returned
    ///   is `0`.
    ///
    ///   Note that this drops any subsecond component on this civil time.
    ///
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`CivilDaySecond`](crate::bounds::CivilDaySecond).
    /// (the wrapper reads this struct back out at wrapper time.rs:1722-1724)
    pub exec fn to_second(self) -> (r: TimeSecond)
        requires valid_time(self),
        ensures
            r.second as int == time_secs_spec(self)
                && cds_iv().contains(r.second as int),
    {
        let mut second: i32 = 0;
        second += (self.hour as i32) * 3600;
        second += (self.minute as i32) * 60;
        second += self.second as i32;
        TimeSecond { second }
    }

    /// Origin Rust (jcore time.rs:179-186):
    ///     pub const fn to_nanosecond(self) -> TimeNanosecond {
    ///         let mut nanosecond: i64 = 0;
    ///         nanosecond += (self.hour() as i64) * 3_600_000_000_000;
    ///         nanosecond += (self.minute() as i64) * 60_000_000_000;
    ///         nanosecond += (self.second() as i64) * 1_000_000_000;
    ///         nanosecond += self.subsec_nanosecond() as i64;
    ///         TimeNanosecond { nanosecond }
    ///     }
    /// Upstream doc (jcore time.rs:172-177):
    ///   Converts this civil time to a nanosecond value corresponding to
    ///   the number of nanoseconds that has elapsed since midnight until
    ///   this time. If this time is midnight, then the nanosecond value
    ///   returned is `0`.
    ///
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`CivilDayNanosecond`](crate::bounds::CivilDayNanosecond).
    /// (wrapper face: the crate-private to_nanosecond at wrapper
    /// time.rs:1745-1747)
    pub exec fn to_nanosecond(self) -> (r: TimeNanosecond)
        requires valid_time(self),
        ensures
            r.nanosecond as int == time_nanos_spec(self)
                && cdn_iv().contains(r.nanosecond as int),
    {
        let mut nanosecond: i64 = 0;
        nanosecond += (self.hour as i64) * 3_600_000_000_000;
        nanosecond += (self.minute as i64) * 60_000_000_000;
        nanosecond += (self.second as i64) * 1_000_000_000;
        nanosecond += self.subsec_nanosecond as i64;
        TimeNanosecond { nanosecond }
    }

    /// Origin Rust (wrapper time.rs:1690-1692, crate internal):
    ///     pub(crate) fn until_nanoseconds(self, other: Time) -> i64 {
    ///         other.to_nanosecond() - self.to_nanosecond()
    ///     }
    /// Upstream doc: none (crate internal; the span-oriented until/since
    /// family that builds on it is cut with the Span surface -- inventory
    /// trimming principle 5 -- see notes.md defers).
    pub exec fn until_nanoseconds(self, other: Time) -> (r: i64)
        requires valid_time(self) && valid_time(other),
        ensures
            r as int
                == time_nanos_spec(other) - time_nanos_spec(self)
                && -(nanos_per_civil_day() as int) < r as int
                && (r as int) < nanos_per_civil_day() as int,
    {
        other.to_nanosecond().nanosecond - self.to_nanosecond().nanosecond
    }

    /// Origin Rust (wrapper time.rs:1732-1737, crate internal):
    ///     fn from_second(second: i32) -> Result<Time, Error> {
    ///         JTimeSecond::new(second)
    ///             .map(|second| second.to_time())
    ///             .map(Time::from_jcore)
    ///             .map_err(Error::jcore_range)
    ///     }
    /// Upstream doc (wrapper time.rs:1726-1730):
    ///   Converts the given second to a time value. The second should
    ///   correspond to the number of seconds that have elapsed since
    ///   `00:00:00`. The fractional second component of the `Time`
    ///   returned is always `0`.
    ///
    ///   This returns an error when the given `second` is invalid.
    pub exec fn from_second(second: i32) -> (r: Option<Time>)
        ensures
            match r {
                Option::Some(t) =>
                    cds_iv().contains(second as int)
                        && t == spec_time_from_second(second as int)
                        && valid_time(t),
                Option::None => !cds_iv().contains(second as int),
            },
    {
        let Some(ts) = TimeSecond::new(second) else {
            return Option::None;
        };
        Option::Some(ts.to_time())
    }

    /// Origin Rust (wrapper time.rs:1755-1760, crate internal):
    ///     fn from_nanosecond(nanosecond: i64) -> Result<Time, Error> {
    ///         JTimeNanosecond::new(nanosecond)
    ///             .map(|nano| nano.to_time())
    ///             .map(Time::from_jcore)
    ///             .map_err(Error::jcore_range)
    ///     }
    /// Upstream doc (wrapper time.rs:1749-1753):
    ///   Converts the given nanosecond to a time value. The nanosecond
    ///   should correspond to the number of nanoseconds that have elapsed
    ///   since `00:00:00.000000000`.
    ///
    ///   This returns an error when the given `nanosecond` is invalid.
    /// This is the civil-day-nanosecond -> Time core every wrapping face
    /// reduces through (the under-carry helper of the batch plan: the
    /// wrapping faces call it with a value already reduced into
    /// CivilDayNanosecond; wrapper time.rs:722 comment "OK because of the
    /// modulus by `NANOS_PER_CIVIL_DAY`").
    pub exec fn from_nanosecond(nanosecond: i64) -> (r: Option<Time>)
        ensures
            match r {
                Option::Some(t) =>
                    cdn_iv().contains(nanosecond as int)
                        && t == spec_time_from_nanosecond(nanosecond as int)
                        && valid_time(t),
                Option::None => !cdn_iv().contains(nanosecond as int),
            },
    {
        let Some(tn) = TimeNanosecond::new(nanosecond) else {
            return Option::None;
        };
        Option::Some(tn.to_time())
    }

    /// Origin Rust (wrapper time.rs:699-702 + TimeArithmetic::wrapping_add
    /// at wrapper :2199-2207 + wrapping_add_span at :705-723), restricted
    /// to the canonical bare-nanoseconds span `Span::new().nanoseconds(n)`:
    ///     pub fn wrapping_add<A: Into<TimeArithmetic>>(
    ///         self, duration: A) -> Time
    ///     // wrapping_add_span, nanos-only arm (span.get_hours() etc. are
    ///     // all zero; the .nanoseconds() term is the whole sum):
    ///     let sum = self.to_nanosecond().wrapping_add(
    ///         i64::from(span.get_hours()).wrapping_mul(c::NANOS_PER_HOUR) /
    ///         ... / .wrapping_add(span.get_nanoseconds()));
    ///     let civil_day_nanosecond = sum.rem_euclid(c::NANOS_PER_CIVIL_DAY);
    ///     // OK because of the modulus by `NANOS_PER_CIVIL_DAY`.
    ///     Time::from_nanosecond(civil_day_nanosecond).unwrap()
    /// Upstream doc (wrapper time.rs:605-618):
    ///   Add the given span to this time and wrap around on overflow.
    ///   # Properties
    ///   Given times `t1` and `t2`, and a span `s`, with `t2 = t1 + s`, it
    ///   follows then that `t1 = t2 - s` for all values of `t1` and `s`
    ///   that sum to `t2`.
    /// The machine wrapping_add keeps upstream's shape under the
    /// |nanos| <= 2^62 window (ledger; mod-2^64 face beyond it deferred).
    pub exec fn wrapping_add_nanos(self, nanos: i64) -> (r: Time)
        requires
            valid_time(self)
                && -(4611686018427387904i64) <= nanos
                && nanos <= 4611686018427387904i64,
        ensures
            r == spec_wrapping_add_nanos(self, nanos as int)
                && valid_time(r),
    {
        let start = self.to_nanosecond();
        let sum = start.nanosecond.wrapping_add(nanos);
        proof {
            assert((start.nanosecond as int) >= 0);
            assert((start.nanosecond as int) < nanos_per_civil_day());
            assert(
                (start.nanosecond as int) + (nanos as int)
                    >= 0 - 4611686018427387904
            );
            assert(
                (start.nanosecond as int) + (nanos as int)
                    <= 4611686018427387904 + 86_400_000_000_000
            );
        }
        let civil_day_nanosecond = rem_euclid_civilday(sum);
        let Some(t) = Time::from_nanosecond(civil_day_nanosecond) else {
            proof { assert(false); }
            unreachable!()
        };
        t
    }

    /// Origin Rust (wrapper time.rs:750-789 + TimeArithmetic::wrapping_sub
    /// at wrapper :2209-2228), nanos-only arm: identical to wrapping_add
    /// with the span negated (`time.wrapping_add_span(span.negate())`,
    /// wrapper :2212; negating a nanos-only span is the i64 negation,
    /// which cannot fail inside the |n| <= 2^62 window).
    /// Upstream doc (wrapper time.rs:750-751):
    ///   This routine is identical to [`Time::wrapping_add`] with the
    ///   duration negated.
    pub exec fn wrapping_sub_nanos(self, nanos: i64) -> (r: Time)
        requires
            valid_time(self)
                && -(4611686018427387904i64) <= nanos
                && nanos <= 4611686018427387904i64,
        ensures
            r == spec_wrapping_sub_nanos(self, nanos as int)
                && valid_time(r),
    {
        self.wrapping_add_nanos(0 - nanos)
    }

    /// Origin Rust (wrapper time.rs:919-925 + checked_add_span :928-934 +
    /// overflowing_add :1076-1094 + checked_add_duration :937-952),
    /// nanos-only arm:
    ///     pub fn checked_add<A: Into<TimeArithmetic>>(
    ///         self, duration: A) -> Result<Time, Error>
    ///     // for Span::new().nanoseconds(n):
    ///     //   overflowing_add computes the i128 sum, days = sum
    ///     //   .div_euclid(NANOS_PER_CIVIL_DAY), rem = sum.rem_euclid(...);
    ///     //   checked_add_span then errs on any non-zero non-time unit,
    ///     //   i.e. exactly when days != 0, i.e. when the sum left the
    ///     //   civil-day range.
    /// Upstream doc (wrapper time.rs:805-827):
    ///   Add the given span to this time and return an error if the result
    ///   would otherwise overflow.
    ///   # Errors
    ///   If the sum would overflow the minimum or maximum timestamp
    ///   values, then an error is returned.
    ///   If the given span has any non-zero units greater than hours,
    ///   then an error is returned.
    /// Ledger: upstream widens to i128 before the overflow checks, so
    /// machine-overflow is impossible there; at the i64 materialization the
    /// checked_add None face covers it, and every such input is far
    /// outside the civil-day range anyway, so the None condition is the
    /// same out-of-[0, NANOS_PER_CIVIL_DAY) fact (the two error routes
    /// coincide on all inputs).
    pub exec fn checked_add_nanos(self, nanos: i64) -> (r: Option<Time>)
        requires valid_time(self),
        ensures
            r == spec_checked_add_nanos(self, nanos as int)
                && (r is Some ==> valid_time(r->Some_0)),
    {
        let start = self.to_nanosecond();
        let Some(end) = start.nanosecond.checked_add(nanos) else {
            proof {
                let s: int = time_nanos_spec(self);
                // vstd's None face: the true sum left the i64 range, and
                // the civil-day interval is deep inside it.
                assert(!(
                    (i64::MIN as int) <= s + (nanos as int)
                        && s + (nanos as int) <= (i64::MAX as int)
                ));
                assert(!(cdn_iv().contains(s + (nanos as int))));
                assert(
                    spec_checked_add_nanos(self, nanos as int)
                        == Option::None
                );
            }
            return Option::None;
        };
        proof {
            let s: int = time_nanos_spec(self);
            assert((end as int) == s + (nanos as int));
        }
        let ret = Time::from_nanosecond(end);
        proof {
            let s: int = time_nanos_spec(self);
            assert(s + (nanos as int) == (end as int));
            match ret {
                Option::Some(t) => {
                    assert(cdn_iv().contains(end as int));
                    assert(t == spec_time_from_nanosecond(end as int));
                    assert(
                        spec_checked_add_nanos(self, nanos as int)
                            == Option::Some(t)
                    );
                }
                Option::None => {
                    assert(!(cdn_iv().contains(end as int)));
                    assert(
                        spec_checked_add_nanos(self, nanos as int)
                            == Option::None
                    );
                }
            }
        }
        ret
    }

    /// Origin Rust (wrapper time.rs:984-990 + TimeArithmetic::checked_
    /// add/checked_neg at wrapper :2231-2242):
    ///     pub fn checked_sub<A: Into<TimeArithmetic>>(
    ///         self, duration: A) -> Result<Time, Error> {
    ///         let duration: TimeArithmetic = duration.into();
    ///         duration.checked_neg().and_then(|ta| ta.checked_add(self))
    ///     }
    /// Upstream doc (wrapper time.rs:954-959):
    ///   This routine is identical to [`Time::checked_add`] with the
    ///   duration negated.
    ///   # Errors
    ///   This has the same error conditions as [`Time::checked_add`].
    /// The i64::MIN arm is the upstream span-negation failure
    /// (checked_neg, wrapper :2239); batch J2's Date::checked_sub i32::MIN
    /// face is the same edge treatment.
    pub exec fn checked_sub_nanos(self, nanos: i64) -> (r: Option<Time>)
        requires valid_time(self),
        ensures
            nanos == i64::MIN
                || (r == spec_checked_sub_nanos(self, nanos as int)
                    && (r is Some ==> valid_time(r->Some_0))),
    {
        if nanos == i64::MIN {
            // the negation failure face (checked_neg on a nanos-only span)
            return Option::None;
        }
        self.checked_add_nanos(0 - nanos)
    }
}

/// Origin Rust (jiff main-crate civil/mod.rs:284-289):
///     pub const fn time(hour: i8, minute: i8, second: i8,
///         subsec_nanosecond: i32) -> Time {
///         Time::constant(hour, minute, second, subsec_nanosecond)
///     }
/// Upstream doc (main-crate civil/mod.rs:248-273):
///   Creates a new `Time` value in a `const` context.
///   This is a convenience free function for [`Time::constant`]. It is
///   intended to provide a terse syntax for constructing `Time` values from
///   parameters that are known to be valid.
///   # Panics
///   This panics if the given values do not correspond to a valid
///   `Time`. All of the following conditions must be true:
///   * `0 <= hour <= 23`
///   * `0 <= minute <= 59`
///   * `0 <= second <= 59`
///   * `0 <= subsec_nanosecond <= 999,999,999`
pub exec fn time(
    hour: i8,
    minute: i8,
    second: i8,
    subsec_nanosecond: i32,
) -> (t: Time)
    requires
        hour_iv().contains(hour as int)
            && minute_iv().contains(minute as int)
            && second_iv().contains(second as int)
            && subsec_iv().contains(subsec_nanosecond as int),
    ensures
        t.hour as int == hour as int
            && t.minute as int == minute as int
            && t.second as int == second as int
            && t.subsec_nanosecond as int == subsec_nanosecond as int
            && valid_time(t),
{
    Time::constant(hour, minute, second, subsec_nanosecond)
}

// ===========================================================================
// TimeSecond (jcore civil/time.rs:296-385)
// ===========================================================================

/// Origin Rust (jcore time.rs:296-301):
///     pub struct TimeSecond { second: i32 }
/// Upstream doc (jcore time.rs:296):
///   Represents a single point in a civil day, to second precision.
#[derive(Clone, Copy)]
pub struct TimeSecond {
    pub second: i32,
}

impl TimeSecond {
    /// Origin Rust (jcore time.rs:310-313):
    ///     pub const fn new(second: i32) -> Result<TimeSecond, RangeError>
    /// Upstream doc (jcore time.rs:304-308):
    ///   Creates a new civil time from a given second value.
    ///   The value must correspond to the number of seconds elapsed since
    ///   the start of a civil day. It cannot exceed the length of a civil
    ///   day (in seconds).
    pub exec fn new(second: i32) -> (r: Option<TimeSecond>)
        ensures
            match r {
                Option::Some(ts) => ts.second as int == second as int
                    && cds_iv().contains(second as int),
                Option::None => !cds_iv().contains(second as int),
            },
    {
        let Some(second) =
            const_check::i32(0i32, 86_399i32, second as i64) else {
            return Option::None;
        };
        Option::Some(TimeSecond { second })
    }

    /// Origin Rust (jcore time.rs:320-322):
    ///     pub const fn constant(second: i32) -> TimeSecond {
    ///         unwrapr!(TimeSecond::new(second), "invalid civil day second")
    ///     }
    /// Upstream doc (jcore time.rs:315-318):
    ///   Creates a new civil time from a given second value.
    ///   This panics when `second` exceeds the maximum number of seconds
    ///   in a single civil day.
    pub exec fn constant(second: i32) -> (ts: TimeSecond)
        requires cds_iv().contains(second as int),
        ensures
            ts.second as int == second as int
                && cds_iv().contains(ts.second as int),
    {
        let Some(ts) = TimeSecond::new(second) else {
            proof { assert(false); }
            unreachable!()
        };
        ts
    }

    /// Origin Rust (jcore time.rs:329-331):
    ///     pub const fn second(self) -> i32 { self.second }
    /// Upstream doc (jcore time.rs:324-327):
    ///   Returns the second value.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`CivilDaySecond`](crate::bounds::CivilDaySecond).
    pub exec fn second(self) -> (r: i32)
        ensures
            r as int == self.second as int
                && (cds_iv().contains(self.second as int)
                    ==> cds_iv().contains(r as int)),
    {
        self.second
    }

    /// Origin Rust (jcore time.rs:346-356):
    ///     pub const fn overflowing_add(self, seconds: i32)
    ///         -> Result<(TimeSecond, i32), RangeError> {
    ///         let Some(sum) = self.second().checked_add(seconds) else {
    ///             rbail!(b::CivilDaySecond::error());
    ///         };
    ///         let days = sum.div_euclid(c::SECS_PER_CIVIL_DAY_32);
    ///         let rem = sum.rem_euclid(c::SECS_PER_CIVIL_DAY_32);
    ///         Ok((TimeSecond { second: rem }, days))
    ///     }
    /// Upstream doc (jcore time.rs:329-344):
    ///   Adds the given number of seconds to this civil time and returns
    ///   the resulting civil time with any overflowing amount in units of
    ///   civil days.
    ///   This returns an error when integer overflow occurs. [...]
    ///   Note that the number of days returned may exceed the range
    ///   supported by [`UnixEpochDay`]. Moreover, the number of days
    ///   returned may be negative.
    /// (The second-precision sibling of the nanosecond under-carry
    /// helper; the std pair inlines below at the fixed divisor
    /// SECS_PER_CIVIL_DAY -- finding 13. The i32 helpers keep J2's
    /// |a| <= 2^30 domain guard for the fix-up headroom, which this
    /// caller's checked i32 sum satisfies.)
    pub exec fn overflowing_add(
        self,
        seconds: i32,
    ) -> (r: Option<(TimeSecond, i32)>)
        requires
            cds_iv().contains(self.second as int)
                && -(1073741824i32) <= self.second + seconds
                && self.second + seconds <= 1073741824i32,
        ensures
            match r {
                Option::Some((ts, days)) =>
                    (days as int) * 86_400 + (ts.second as int)
                        == (self.second as int) + (seconds as int)
                        && 0 <= ts.second as int
                        && (ts.second as int) <= 86_399,
                Option::None =>
                    !(i32::MIN as int
                        <= (self.second as int) + (seconds as int))
                        || !((self.second as int) + (seconds as int)
                            <= i32::MAX as int),
            },
    {
        let Some(sum) = self.second.checked_add(seconds) else {
            return Option::None;
        };
        let days = div_euclid_86400(sum);
        let rem = rem_euclid_86400(sum);
        Option::Some((TimeSecond { second: rem }, days))
    }

    /// Origin Rust (jcore time.rs:363-384):
    ///     pub const fn to_time(&self) -> Time {
    ///         // Uses a non-obvious sequence to allow component extraction
    ///         // to have overlapping execution.
    ///         // Calculation of `minute` and `second` use an optimised
    ///         // "power-complement-padding" technique instead of standard
    ///         // mod. Relies on the identity: 60 + 2^2 = 2^6.
    ///         // Ref: https://www.benjoffe.com/fast-time-of-day
    ///         let secs: u32 = self.second as u32;
    ///         let hour: u32 = (secs / 3600) as u32;
    ///         let tmin: u32 = (secs / 60) as u32;
    ///         Time {
    ///             hour: hour as i8,
    ///             minute: ((tmin + 4 * hour) % 64) as i8,
    ///             second: ((secs + 4 * tmin) % 64) as i8,
    ///             subsec_nanosecond: 0,
    ///         }
    ///     }
    /// Upstream doc (jcore time.rs:358-361):
    ///   Converts this second representation of a civil time into the
    ///   components of a civil time.
    ///   The subsecond component on the `Time` returned is always `0`.
    /// The power-complement-padding arithmetic is proven equal to the
    /// true components via the 60+4=64 congruence: minute's term is
    /// 64h + minute, second's term is 64*tmin + second, so both mod-64
    /// reductions recover the true field (the mod_multiples_vanish chain
    /// in the proof block). u32 materializes at i64 (ledger).
    pub exec fn to_time(self) -> (r: Time)
        requires cds_iv().contains(self.second as int),
        ensures
            r == spec_time_from_second(self.second as int)
                && valid_time(r),
    {
        let secs: i64 = self.second as i64;
        let hour: i64 = secs / 3600;
        let tmin: i64 = secs / 60;
        proof {
            let s: int = secs as int;
            assert(hour as int == s / 3600);
            assert(tmin as int == s / 60);
            let h: int = s / 3600;
            let rr: int = s % 3600;
            lemma_fundamental_div_mod(s, 3600);
            assert(s == 3600 * h + rr);
            assert(0 <= rr < 3600);
            let m: int = rr / 60;
            let e: int = rr % 60;
            lemma_fundamental_div_mod(rr, 60);
            assert(rr == 60 * m + e);
            assert(0 <= m < 60);
            assert(0 <= e < 60);
            // tmin == 60*h + m, and s % 60 == e, both from the 60-side
            // decomposition of s:
            lemma_mul_is_distributive_add(60, 60 * h, m);
            lemma_mul_is_associative(60, 60, h);
            assert(60 * (60 * h) == 3600 * h);
            assert(s == 60 * (60 * h + m) + e);
            lemma_fundamental_div_mod_converse(s, 60, 60 * h + m, e);
            assert(s / 60 == 60 * h + m);
            assert(s % 60 == e);
            // minute: tmin + 4*hour = (60h + m) + 4h = 64h + m
            lemma_mul_is_distributive_add_other_way(h, 60, 4);
            assert((60 + 4) * h == 60 * h + 4 * h);
            lemma_mul_is_commutative(60, h);
            assert(60 * h == h * 60);
            lemma_mul_is_commutative(4, h);
            assert(4 * h == h * 4);
            assert(tmin as int + 4 * (hour as int) == 64 * h + m);
            lemma_mod_multiples_vanish(h, m, 64);
            assert((64 * h + m) % 64 == m % 64);
            lemma_fundamental_div_mod_converse(m, 64, 0, m);
            assert(m % 64 == m);
            assert((tmin as int + 4 * (hour as int)) % 64 == m);
            // second: secs + 4*tmin = s + 4*(60h + m) = 64*(60h + m) + e
            lemma_mul_is_distributive_add(4, 60 * h, m);
            lemma_mul_is_associative(4, 60, h);
            assert(4 * (60 * h) == 240 * h);
            lemma_mul_is_distributive_add(64, 60 * h, m);
            lemma_mul_is_associative(64, 60, h);
            assert(64 * (60 * h) == 3840 * h);
            assert(s + 4 * (s / 60) == 64 * (60 * h + m) + e);
            lemma_mod_multiples_vanish(60 * h + m, e, 64);
            assert((64 * (60 * h + m) + e) % 64 == e % 64);
            lemma_fundamental_div_mod_converse(e, 64, 0, e);
            assert(e % 64 == e);
            assert((s + 4 * (s / 60)) % 64 == e);
        }
        Time {
            hour: hour as i8,
            minute: ((tmin + 4 * hour) % 64) as i8,
            second: ((secs + 4 * tmin) % 64) as i8,
            subsec_nanosecond: 0,
        }
    }
}

// ===========================================================================
// TimeNanosecond (jcore civil/time.rs:387-456): the CivilDayNanosecond
// accumulator space of the batch plan
// ===========================================================================

/// Origin Rust (jcore time.rs:387-392):
///     pub struct TimeNanosecond { nanosecond: i64 }
/// Upstream doc (jcore time.rs:387):
///   Represents a single point in a civil day, to nanosecond precision.
#[derive(Clone, Copy)]
pub struct TimeNanosecond {
    pub nanosecond: i64,
}

impl TimeNanosecond {
    /// Origin Rust (jcore time.rs:401-405):
    ///     pub const fn new(nanosecond: i64)
    ///         -> Result<TimeNanosecond, RangeError> {
    ///         let nanosecond =
    ///             rtry!(b::CivilDayNanosecond::checkc(nanosecond as i64));
    ///         Ok(TimeNanosecond { nanosecond })
    ///     }
    /// Upstream doc (jcore time.rs:395-399):
    ///   Creates a new civil time from a given nanosecond value.
    ///   The value must correspond to the number of nanoseconds elapsed
    ///   since the start of a civil day. It cannot exceed the length of a
    ///   civil day (in nanoseconds).
    pub exec fn new(nanosecond: i64) -> (r: Option<TimeNanosecond>)
        ensures
            match r {
                Option::Some(tn) =>
                    tn.nanosecond as int == nanosecond as int
                        && cdn_iv().contains(nanosecond as int),
                Option::None => !cdn_iv().contains(nanosecond as int),
            },
    {
        let Some(nanosecond) = const_check::i64(
            0i64,
            86_399_999_999_999i64,
            nanosecond,
        ) else {
            return Option::None;
        };
        Option::Some(TimeNanosecond { nanosecond })
    }

    /// Origin Rust (jcore time.rs:412-414):
    ///     pub const fn nanosecond(self) -> i64 { self.nanosecond }
    /// Upstream doc (jcore time.rs:407-410):
    ///   Returns the nanosecond value.
    ///   The value returned is guaranteed to be in the range specified by
    ///   [`CivilDayNanosecond`](crate::bounds::CivilDayNanosecond).
    pub exec fn nanosecond(self) -> (r: i64)
        ensures
            r as int == self.nanosecond as int
                && (cdn_iv().contains(self.nanosecond as int)
                    ==> cdn_iv().contains(r as int)),
    {
        self.nanosecond
    }

    /// Origin Rust (jcore time.rs:429-439):
    ///     pub const fn overflowing_add(self, nanoseconds: i64)
    ///         -> Result<(TimeNanosecond, i64), RangeError> {
    ///         let Some(sum) = self.nanosecond().checked_add(nanoseconds)
    ///         else { rbail!(b::CivilDayNanosecond::error()); };
    ///         let days = sum.div_euclid(c::NANOS_PER_CIVIL_DAY);
    ///         let rem = sum.rem_euclid(c::NANOS_PER_CIVIL_DAY);
    ///         Ok((TimeNanosecond { nanosecond: rem }, days))
    ///     }
    /// Upstream doc (jcore time.rs:416-427):
    ///   Adds the given number of nanoseconds to this civil time and
    ///   returns the resulting civil time with any overflowing amount in
    ///   units of civil days.
    ///   This returns an error when integer overflow occurs. For example,
    ///   when `seconds` is `i64::MAX` and this civil time is any time other
    ///   than midnight.
    ///   Note that the number of days returned may exceed the range
    ///   supported by [`UnixEpochDay`]. Moreover, the number of days
    ///   returned may be negative. This occurs only when `nanoseconds` is
    ///   negative enough to result in the time wrapping around at `0`.
    /// This is the civil-day accumulator / under-carry helper core: every
    /// Time addition and subtraction reduces to a checked sum in this
    /// space and reads back through to_time.
    pub exec fn overflowing_add(
        self,
        nanoseconds: i64,
    ) -> (r: Option<(TimeNanosecond, i64)>)
        requires cdn_iv().contains(self.nanosecond as int),
        ensures
            match r {
                Option::Some((tn, days)) =>
                    (days as int) * nanos_per_civil_day()
                        + (tn.nanosecond as int)
                        == (self.nanosecond as int)
                            + (nanoseconds as int)
                        && 0 <= tn.nanosecond as int
                        && (tn.nanosecond as int)
                            < nanos_per_civil_day(),
                Option::None =>
                    !(i64::MIN as int
                        <= (self.nanosecond as int)
                            + (nanoseconds as int))
                        || !((self.nanosecond as int)
                            + (nanoseconds as int)
                            <= i64::MAX as int),
            },
    {
        let Some(sum) = self.nanosecond().checked_add(nanoseconds) else {
            return Option::None;
        };
        let days = div_euclid_civilday(sum);
        let rem = rem_euclid_civilday(sum);
        Option::Some((TimeNanosecond { nanosecond: rem }, days))
    }

    /// Origin Rust (jcore time.rs:446-455):
    ///     pub const fn to_time(&self) -> Time {
    ///         // Nanosecond is enforced as non-negative elsewhere
    ///         // as such, we can cast to unsigned for faster division:
    ///         let nanos: u64 = self.nanosecond as u64;
    ///         let mut time: Time =
    ///             TimeSecond { second: (nanos / 1_000_000_000) as i32 }
    ///                 .to_time();
    ///         time.subsec_nanosecond = (nanos % 1_000_000_000) as i32;
    ///         time
    ///     }
    /// Upstream doc (jcore time.rs:441-444):
    ///   Converts this second representation of a civil time into the
    ///   components of a civil time.
    ///   The subsecond component on the `Time` returned is always `0`.
    // SPEC-DOC MISMATCH (candidate, unfiled): the doc's "always `0`"
    // sentence is contradicted by the body's own field write
    //     time.subsec_nanosecond = (nanos % 1_000_000_000) as i32;
    // (jcore time.rs:453): the returned subsecond is `nanos % 1e9`,
    // nonzero for every civil-day nanosecond value not a multiple of
    // 1e9 (e.g. TimeNanosecond::new(1) -> subsec_nanosecond == 1); the
    // "second representation" phrasing is the copy-paste from the
    // seconds face, where both sentences are truthful. The contract
    // below carries the implementation shape.
    /// u64 materializes at i64 (non-negative ledger).
    pub exec fn to_time(self) -> (r: Time)
        requires cdn_iv().contains(self.nanosecond as int),
        ensures
            r == spec_time_from_nanosecond(self.nanosecond as int)
                && valid_time(r),
    {
        let nanos: i64 = self.nanosecond;
        let mut time: Time = TimeSecond {
            second: (nanos / 1_000_000_000) as i32,
        }.to_time();
        proof {
            let n: int = nanos as int;
            let s: int = n / 1_000_000_000;
            assert(((nanos / 1_000_000_000) as int)
                == n / 1_000_000_000);
            assert(((nanos % 1_000_000_000) as int)
                == n % 1_000_000_000);
            assert(time == spec_time_from_second(s));
            assert(time.hour as int == s / 3600);
            assert(time.minute as int == ((s % 3600) / 60));
            assert(time.second as int == s % 60);
        }
        time.subsec_nanosecond = (nanos % 1_000_000_000) as i32;
        proof {
            let n: int = nanos as int;
            let s: int = n / 1_000_000_000;
            assert(time == Time {
                hour: ((s / 3600) as i8),
                minute: (((s % 3600) / 60) as i8),
                second: ((s % 60) as i8),
                subsec_nanosecond: ((n % 1_000_000_000) as i32),
            });
            assert(spec_time_from_nanosecond(n) == Time {
                hour: ((s / 3600) as i8),
                minute: (((s % 3600) / 60) as i8),
                second: ((s % 60) as i8),
                subsec_nanosecond: ((n % 1_000_000_000) as i32),
            });
        }
        time
    }
}

// ===========================================================================
// std div_euclid / rem_euclid inlines at the civil-DAY-SECOND divisor
// (86_400), the i32 pair used by TimeSecond::overflowing_add
// ===========================================================================

/// std i32::rem_euclid inlined at the SECS_PER_CIVIL_DAY divisor (same
/// finding-13 treatment as rem_euclid_civilday; the i32 width keeps J2's
/// |a| <= 2^30 domain guard so the fix-up x + 86_400 cannot overflow).
pub exec fn rem_euclid_86400(a: i32) -> (r: i32)
    requires -(1073741824i32) <= a && a <= 1073741824i32,
    ensures
        r as int == (a as int) % 86_400
            && 0 <= r as int
            && (r as int) < 86_400,
{
    let x = a % 86_400i32;
    proof {
        let ai: int = a as int;
        let di: int = 86_400;
        assert(x as int == rust_rem(ai, di));
        if a == 0 {
            assert(rust_rem(ai, di) == 0);
            assert(ai % di == 0);
        } else if a > 0 {
            assert(rust_rem(ai, di) == ai % di);
        } else {
            let n: int = 0 - ai;
            let q: int = n / di;
            let e: int = n % di;
            lemma_fundamental_div_mod(n, di);
            assert(n == di * q + e);
            assert(0 <= e < di);
            lemma_mul_is_commutative(q, di);
            lemma_mul_unary_negation(q, di);
            assert(ai == (0 - q) * di + (0 - e));
            if x == 0 {
                assert(ai == (0 - q) * di);
                assert(rust_rem(ai, di) == 0);
                lemma_mod_multiples_basic(0 - q, di);
                assert(((0 - q) * di) % di == 0);
                assert(ai % di == 0);
            } else {
                let w: int = di - e;
                assert(0 < w < di);
                lemma_mul_is_distributive_add_other_way(di, q, 1);
                lemma_mul_basics(di);
                assert((q + 1) * di == q * di + 1 * di);
                assert(1 * di == di);
                assert((q + 1) * di == q * di + di);
                lemma_mul_unary_negation(q + 1, di);
                assert((0 - (q + 1)) * di == (0 - q * di) - di);
                assert(ai == (0 - (q + 1)) * di + w);
                lemma_fundamental_div_mod_converse(ai, di, 0 - (q + 1), w);
                assert(ai % di == w);
                assert(rust_rem(ai, di) == 0 - e);
                assert(x as int == 0 - e);
                assert(x as int + di == w);
            }
        }
    }
    if x < 0 {
        x + 86_400i32
    } else {
        x
    }
}

/// std i32::div_euclid (q-adjust form, as div_euclid_civilday) inlined at
/// the SECS_PER_CIVIL_DAY divisor, with the same |a| <= 2^30 guard.
pub exec fn div_euclid_86400(a: i32) -> (q: i32)
    requires -(1073741824i32) <= a && a <= 1073741824i32,
    ensures
        (q as int) * 86_400 + ((a as int) % 86_400) == a as int
            && (q as int) == (a as int) / 86_400,
{
    let q = a / 86_400i32;
    let x = a % 86_400i32;
    proof {
        let ai: int = a as int;
        let di: int = 86_400;
        assert(x as int == rust_rem(ai, di));
        let tr: int = rust_div(ai, di);
        assert(q as int == tr);
        assert(ai == di * tr + (x as int));
        let e: int = ai % di;
        if x >= 0 {
            assert(e == x as int);
            lemma_fundamental_div_mod_converse(ai, di, tr, e);
        } else {
            let qm: int = tr - 1;
            assert(e == (x as int) + di);
            lemma_mul_is_distributive_add_other_way(di, qm, 1);
            lemma_mul_basics(di);
            assert((qm + 1) * di == qm * di + 1 * di);
            assert(1 * di == di);
            assert((qm + 1) * di == qm * di + di);
            lemma_mul_is_commutative(qm + 1, di);
            assert(di * tr == qm * di + di);
            assert(ai == qm * di + ((x as int) + di));
            lemma_fundamental_div_mod_converse(
                ai,
                di,
                qm,
                (x as int) + di,
            );
        }
    }
    if x < 0 {
        q - 1
    } else {
        q
    }
}

} // verus!
