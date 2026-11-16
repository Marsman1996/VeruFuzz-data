//! Batch J3 harness -- the quickcheck time properties, transcribed from
//! upstream `#[cfg(test)]` quickcheck blocks into proof theorems (the J2
//! quickcheck_date.rs precedent: the quickcheck discard-at-extremes
//! discipline becomes the `is Some` / domain precondition, and the
//! TestResult::from_bool assertion becomes the ensures clause).
//!
//! Upstream sources of record (pin 627c7358):
//! crates/jiff-core/src/civil/time.rs quickcheck block (jcore
//! time.rs:667-676):
//!   quickcheck::quickcheck! {
//!       fn prop_time_to_second_roundtrip(t: Time) -> bool {
//!           let t = Time::new(t.hour(), t.minute(), t.second(), 0).unwrap();
//!           t == t.to_second().to_time()
//!       }
//!       fn prop_time_to_nanosecond_roundtrip(t: Time) -> bool {
//!           t == t.to_nanosecond().to_time()
//!       }
//!   }
//! crates/jiff/src/civil/time.rs quickcheck block (time.rs:3273-3371):
//!   prop_ordering_same_as_civil_nanosecond (:3274-3287),
//!   prop_checked_add_then_sub (:3289-3302),
//!   prop_wrapping_add_then_sub (:3304-3315),
//!   prop_checked_add_equals_wrapping_add (:3317-3330),
//!   prop_checked_sub_equals_wrapping_sub (:3332-3345),
//!   prop_until_then_add (:3347), prop_until_then_sub (:3352),
//!   prop_since_then_add (:3357), prop_since_then_sub (:3362),
//!   prop_until_is_since_negated (:3367 -- :3370).
//!
//! Landing record (this file):
//! - Transcribed: the two jcore roundtrip properties + the first five
//!   main-crate laws (7 of the 12 upstream time properties; 5 of the 10
//!   the inventory counts for the main crate).
//! - Deferred to the Span batch (inventory trimming principle 5):
//!   prop_until_then_add/until_then_sub/since_then_add/since_then_sub/
//!   until_is_since_negated -- each builds a Span (via `Time::until` /
//!   `Time::since`, wrapper time.rs:1223/:1257) whose construction lies in
//!   the Span surface this batch cut; the until_nanoseconds backbone they
//!   sit on is transcribed in src/time.rs.
//! - Equality/ordering materialization: Time's `#[derive(PartialEq,
//!   PartialOrd, Ord)]` upstream is opaque in Verus contracts (J1
//!   finding 2), so the equality assertions transcribe as spec-struct
//!   equality against the spec twins, and the ordering law is stated
//!   between the derived lexicographic field order (spec_lex_cmp below)
//!   and the nanosecond projection -- exactly the content of upstream's
//!   `t1.cmp(&t2) == ns1.cmp(&ns2)` once the derived impls are replaced
//!   by their intended semantics.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    lemma_mod_multiples_vanish,
};
use vstd::arithmetic::mul::{
    lemma_mul_is_distributive_add, lemma_mul_is_associative,
};

#[path = "../src/lib.rs"]
mod jiff_lib;

verus! {

use jiff_lib::time::{
    Time, nanos_per_civil_day, spec_checked_add_nanos,
    spec_checked_sub_nanos, spec_time_from_nanosecond,
    spec_time_from_second, spec_wrapping_add_nanos,
    spec_wrapping_sub_nanos, time_nanos_spec, time_secs_spec, valid_time,
};

/// Theorem form of jcore prop_time_to_second_roundtrip
/// (jcore time.rs:668-671): upstream rebuilds the time with subsec 0
/// first, so the discard is the `subsec_nanosecond == 0` precondition.
pub proof fn prop_time_to_second_roundtrip(t: Time)
    requires valid_time(t) && t.subsec_nanosecond == 0,
    ensures spec_time_from_second(time_secs_spec(t)) == t,
{
    let h: int = t.hour as int;
    let m: int = t.minute as int;
    let sec: int = t.second as int;
    let s: int = time_secs_spec(t);
    assert(s == (h * 3600) + (m * 60) + sec);
    // the true components are the quotient chain of s:
    lemma_fundamental_div_mod_converse(s, 3600, h, (m * 60) + sec);
    assert(s % 60 == sec) by {
        lemma_fundamental_div_mod_converse(s, 60, 60 * h + m, sec);
    }
    assert(((m * 60) + sec) / 60 == m) by {
        lemma_fundamental_div_mod_converse(((m * 60) + sec), 60, m, sec);
    }
    assert(spec_time_from_second(s) == Time {
        hour: (s / 3600) as i8,
        minute: ((s % 3600) / 60) as i8,
        second: (s % 60) as i8,
        subsec_nanosecond: 0,
    });
}

/// Theorem form of jcore prop_time_to_nanosecond_roundtrip
/// (jcore time.rs:673-675): the civil-day nanosecond projection is
/// injective on valid times, with from_nanosecond as its inverse.
pub proof fn prop_time_to_nanosecond_roundtrip(t: Time)
    requires valid_time(t),
    ensures spec_time_from_nanosecond(time_nanos_spec(t)) == t,
{
    let h: int = t.hour as int;
    let m: int = t.minute as int;
    let sec: int = t.second as int;
    let sub: int = t.subsec_nanosecond as int;
    let n: int = time_nanos_spec(t);
    // n == 1e9 * ((h*3600) + ((m*60) + sec)) + sub, by monomial folding:
    lemma_mul_is_associative(h, 3600, 1_000_000_000);
    lemma_mul_is_associative(m, 60, 1_000_000_000);
    assert(h * 3_600_000_000_000 == (h * 3600) * 1_000_000_000);
    assert(m * 60_000_000_000 == (m * 60) * 1_000_000_000);
    let q: int = (h * 3600) + ((m * 60) + sec);
    lemma_mul_is_distributive_add(
        1_000_000_000,
        h * 3600,
        (m * 60) + sec,
    );
    assert(
        (h * 3600 + (m * 60 + sec)) * 1_000_000_000
            == (h * 3600) * 1_000_000_000
                + ((m * 60) + sec) * 1_000_000_000
    );
    lemma_mul_is_distributive_add(1_000_000_000, m * 60, sec);
    assert(
        ((m * 60) + sec) * 1_000_000_000
            == ((m * 60) * 1_000_000_000)
                + (sec * 1_000_000_000)
    );
    assert(n == 1_000_000_000 * q + sub);
    // so the from-nanosecond re-decomposition lands back on the fields:
    lemma_fundamental_div_mod_converse(n, 1_000_000_000, q, sub);
    assert(n / 1_000_000_000 == q);
    assert(n % 1_000_000_000 == sub);
    lemma_fundamental_div_mod_converse(q, 3600, h, (m * 60) + sec);
    assert(q % 60 == sec) by {
        lemma_fundamental_div_mod_converse(q, 60, 60 * h + m, sec);
    }
    assert(((m * 60) + sec) / 60 == m) by {
        lemma_fundamental_div_mod_converse(((m * 60) + sec), 60, m, sec);
    }
    assert(spec_time_from_nanosecond(n) == Time {
        hour: ((q / 3600)) as i8,
        minute: (((q % 3600) / 60)) as i8,
        second: ((q % 60)) as i8,
        subsec_nanosecond: ((n % 1_000_000_000)) as i32,
    });
}

/// Helper law used by the add/sub identities: re-assembling the fields of
/// the from-nanosecond decomposition gives the nanosecond value back
/// (the converse direction of prop_time_to_nanosecond_roundtrip; not
/// itself a quickcheck property upstream -- it is the from-side glue).
pub proof fn lemma_nanos_of_from_nanosecond(n: int)
    requires
        0 <= n && n < nanos_per_civil_day(),
    ensures time_nanos_spec(spec_time_from_nanosecond(n)) == n,
{
    let s: int = n / 1_000_000_000;
    let h: int = s / 3600;
    let rr: int = s % 3600;
    let m: int = rr / 60;
    let e: int = rr % 60;
    let sub: int = n % 1_000_000_000;
    lemma_fundamental_div_mod(s, 3600);
    assert(s == 3600 * h + rr);
    assert(0 <= rr < 3600);
    lemma_fundamental_div_mod(s, 60);
    let sec: int = s % 60;
    assert(s == 60 * (60 * h + m) + sec);
    assert(sec == e) by {
        lemma_fundamental_div_mod_converse(rr, 60, m, e);
        assert(rr == 60 * m + e);
    }
    let tw: Time = spec_time_from_nanosecond(n);
    assert(tw.hour as int == h);
    assert(tw.minute as int == m);
    assert(tw.second as int == e);
    assert(tw.subsec_nanosecond as int == sub);
    lemma_mul_is_associative(h, 3600, 1_000_000_000);
    lemma_mul_is_associative(m, 60, 1_000_000_000);
    assert(h * 3_600_000_000_000 == (h * 3600) * 1_000_000_000);
    assert(m * 60_000_000_000 == (m * 60) * 1_000_000_000);
    let q: int = (h * 3600) + ((m * 60) + e);
    lemma_mul_is_distributive_add(
        1_000_000_000,
        h * 3600,
        (m * 60) + e,
    );
    assert(
        q * 1_000_000_000
            == (h * 3600) * 1_000_000_000
                + ((m * 60) + e) * 1_000_000_000
    );
    lemma_mul_is_distributive_add(1_000_000_000, m * 60, e);
    assert(
        ((m * 60) + e) * 1_000_000_000
            == ((m * 60) * 1_000_000_000)
                + (e * 1_000_000_000)
    );
    assert(time_nanos_spec(tw) == q * 1_000_000_000 + sub);
    assert(s == q);
    assert(n == s * 1_000_000_000 + sub);
}

/// Theorem form of main-crate prop_checked_add_then_sub
/// (wrapper time.rs:3289-3302): the quickcheck nanos span is a value of
/// b::CivilDayNanosecond (0..=86_399_999_999_999, discard otherwise) and
/// the checked_add Err is the `is Some` precondition:
///   let Ok(sum) = time.checked_add(span) else { discard };
///   let diff = sum.checked_sub(span).unwrap();
///   time == diff
pub proof fn prop_checked_add_then_sub(t: Time, n: int)
    requires
        valid_time(t)
            && 0 <= n && n < nanos_per_civil_day()
            && spec_checked_add_nanos(t, n) is Some,
    ensures
        spec_checked_sub_nanos(
            spec_time_from_nanosecond(time_nanos_spec(t) + n),
            n,
        ) == Option::Some(t),
{
    let sum: int = time_nanos_spec(t) + n;
    assert(jiff_lib::time::cdn_iv().contains(sum));
    lemma_nanos_of_from_nanosecond(sum);
    let tw: Time = spec_time_from_nanosecond(sum);
    // tw's projection is the sum, so subtracting n projects back to t:
    assert(time_nanos_spec(tw) - n == time_nanos_spec(t));
    assert(
        spec_checked_sub_nanos(tw, n)
            == Option::Some(
                spec_time_from_nanosecond(time_nanos_spec(t)))
    );
    prop_time_to_nanosecond_roundtrip(t);
}

/// Theorem form of main-crate prop_wrapping_add_then_sub
/// (wrapper time.rs:3304-3315):
///   let sum = time.wrapping_add(span);
///   let diff = sum.wrapping_sub(span);
///   time == diff
pub proof fn prop_wrapping_add_then_sub(t: Time, n: int)
    requires
        valid_time(t)
            && 0 <= n && n < nanos_per_civil_day(),
    ensures
        spec_wrapping_sub_nanos(spec_wrapping_add_nanos(t, n), n)
            == spec_time_from_nanosecond(time_nanos_spec(t)),
{
    let a: int = time_nanos_spec(t);
    let m: int = a + n;              // < 2 * D
    let w: Time = spec_wrapping_add_nanos(t, n);
    assert(w == spec_time_from_nanosecond(m % nanos_per_civil_day()));
    lemma_nanos_of_from_nanosecond(m % nanos_per_civil_day());
    assert(time_nanos_spec(w) == m % nanos_per_civil_day());
    // (m % D) - n == a - k*D where k is the day count of m:
    let k: int = m / nanos_per_civil_day();
    assert(m % nanos_per_civil_day() == m - k * nanos_per_civil_day());
    assert((m % nanos_per_civil_day()) - n
        == (nanos_per_civil_day() * (0 - k)) + a);
    lemma_mod_multiples_vanish(0 - k, a, nanos_per_civil_day());
    assert(
        ((m % nanos_per_civil_day()) - n)
            % nanos_per_civil_day()
        == a % nanos_per_civil_day()
    );
    assert(a % nanos_per_civil_day() == a) by {
        lemma_fundamental_div_mod_converse(
            a,
            nanos_per_civil_day(),
            0,
            a,
        );
    }
    assert(
        spec_wrapping_sub_nanos(w, n)
            == spec_time_from_nanosecond(time_nanos_spec(t))
    );
}

/// Theorem form of main-crate prop_checked_add_equals_wrapping_add
/// (wrapper time.rs:3317-3330): the checked arm agrees with wrapping
/// exactly when no day-carry occurred.
pub proof fn prop_checked_add_equals_wrapping_add(t: Time, n: int)
    requires
        valid_time(t)
            && 0 <= n && n < nanos_per_civil_day()
            && spec_checked_add_nanos(t, n) is Some,
    ensures
        spec_checked_add_nanos(t, n)
            == Option::Some(spec_wrapping_add_nanos(t, n)),
{
    let sum: int = time_nanos_spec(t) + n;
    assert(jiff_lib::time::cdn_iv().contains(sum));
    assert(sum % nanos_per_civil_day() == sum) by {
        lemma_fundamental_div_mod_converse(
            sum,
            nanos_per_civil_day(),
            0,
            sum,
        );
    }
}

/// Theorem form of main-crate prop_checked_sub_equals_wrapping_sub
/// (wrapper time.rs:3332-3345).
pub proof fn prop_checked_sub_equals_wrapping_sub(t: Time, n: int)
    requires
        valid_time(t)
            && 0 <= n && n < nanos_per_civil_day()
            && spec_checked_sub_nanos(t, n) is Some,
    ensures
        spec_checked_sub_nanos(t, n)
            == Option::Some(spec_wrapping_sub_nanos(t, n)),
{
    let diff: int = time_nanos_spec(t) - n;
    assert(jiff_lib::time::cdn_iv().contains(diff));
    assert(diff % nanos_per_civil_day() == diff) by {
        lemma_fundamental_div_mod_converse(
            diff,
            nanos_per_civil_day(),
            0,
            diff,
        );
    }
}

/// The lexicographic field order Time's derived Ord implementation
/// represents (hour, then minute, then second, then subsec_nanosecond,
/// jcore time.rs:14-19 declaration order).
pub open spec fn spec_lex_cmp(t1: Time, t2: Time) -> int {
    if (t1.hour as int) < (t2.hour as int) {
        -1
    } else if (t2.hour as int) < (t1.hour as int) {
        1
    } else if (t1.minute as int) < (t2.minute as int) {
        -1
    } else if (t2.minute as int) < (t1.minute as int) {
        1
    } else if (t1.second as int) < (t2.second as int) {
        -1
    } else if (t2.second as int) < (t1.second as int) {
        1
    } else if (t1.subsec_nanosecond as int)
        < (t2.subsec_nanosecond as int)
    {
        -1
    } else if (t2.subsec_nanosecond as int)
        < (t1.subsec_nanosecond as int)
    {
        1
    } else {
        0
    }
}

/// Theorem form of main-crate prop_ordering_same_as_civil_nanosecond
/// (wrapper time.rs:3274-3287):
///   let t1 = Time::from_nanosecond(ns1).unwrap();
///   let t2 = Time::from_nanosecond(ns2).unwrap();
///   t1.cmp(&t2) == ns1.cmp(&ns2)
/// Materialized between spec_lex_cmp and the nanosecond projection (the
/// derived Ord/PartialOrd impl is contract-opaque; J1 finding 2 -- the
/// from_nanosecond covers of the quickcheck's ns1/ns2 correspond to the
/// valid-time domain via prop_time_to_nanosecond_roundtrip).
pub proof fn prop_ordering_same_as_civil_nanosecond(t1: Time, t2: Time)
    requires valid_time(t1) && valid_time(t2),
    ensures
        (spec_lex_cmp(t1, t2) == -1
            <==> time_nanos_spec(t1) < time_nanos_spec(t2))
            && (spec_lex_cmp(t1, t2) == 0
                <==> time_nanos_spec(t1) == time_nanos_spec(t2))
            && (spec_lex_cmp(t1, t2) == 1
                <==> time_nanos_spec(t1) > time_nanos_spec(t2)),
{
    let h1: int = t1.hour as int;
    let h2: int = t2.hour as int;
    let m1: int = t1.minute as int;
    let m2: int = t2.minute as int;
    let s1: int = t1.second as int;
    let s2: int = t2.second as int;
    let b1: int = t1.subsec_nanosecond as int;
    let b2: int = t2.subsec_nanosecond as int;
    assert(time_nanos_spec(t1)
        == h1 * 3_600_000_000_000
            + m1 * 60_000_000_000
            + s1 * 1_000_000_000
            + b1);
    assert(time_nanos_spec(t2)
        == h2 * 3_600_000_000_000
            + m2 * 60_000_000_000
            + s2 * 1_000_000_000
            + b2);
    // each branch of the lexicographic chain decides the projection
    // difference's sign by linear dominance of the higher field:
    if h1 < h2 {
        assert(time_nanos_spec(t1) < time_nanos_spec(t2));
    } else if h2 < h1 {
        assert(time_nanos_spec(t1) > time_nanos_spec(t2));
    } else if m1 < m2 {
        assert(time_nanos_spec(t1) < time_nanos_spec(t2));
    } else if m2 < m1 {
        assert(time_nanos_spec(t1) > time_nanos_spec(t2));
    } else if s1 < s2 {
        assert(time_nanos_spec(t1) < time_nanos_spec(t2));
    } else if s2 < s1 {
        assert(time_nanos_spec(t1) > time_nanos_spec(t2));
    } else if b1 < b2 {
        assert(time_nanos_spec(t1) < time_nanos_spec(t2));
    } else if b2 < b1 {
        assert(time_nanos_spec(t1) > time_nanos_spec(t2));
    } else {
        // all four fields equal: the projections are equal
        assert(time_nanos_spec(t1) == time_nanos_spec(t2));
    }
    // conversely: the projection's sign pins each of the >= / == / <=
    // trichotomy arms of the lex chain (each decided by dominance:
    // the sums below are exact linear combinations with the same
    // bounded coefficients on both sides).
    assert(time_nanos_spec(t2) - time_nanos_spec(t1)
        == (h2 - h1) * 3_600_000_000_000
            + (m2 - m1) * 60_000_000_000
            + (s2 - s1) * 1_000_000_000
            + (b2 - b1));
}

} // verus!

// Standalone driver form (the src/ crate root carries its own main; this
// file's module mount does not include it).
fn main() {}
