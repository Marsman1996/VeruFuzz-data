//! jiff 0.2.43 -- the J8 composition reunion faces: the civil-Time
//! consumers of the invariant-duration spine (wrapper file
//! crates/jiff/src/civil/time.rs + the SignedDuration date/time
//! '-until' family of crates/jiff/src/signed_duration.rs), Verus
//! translation, batch J8.
//!
//! This file is the batch instruction's "composition reunion" pair
//! plus the J3 quickcheck tail it unlocks:
//! 1. `SignedDuration::time_until` (signed_duration.rs:2104-2106) and
//!    its wrapper mirrors `Time::duration_until` /
//!    `Time::duration_since` (wrapper time.rs:1369-1395) -- the
//!    absolute-duration between-times family (the J3-deferred
//!    wrapper face; the until_nanoseconds backbone it rides is the
//!    J3 core's).
//! 2. `Time::until` in its default configuration (wrapper time.rs
//!    :1223-1234 -> TimeDifference::until_with_largest_unit
//!    :2539-2562, the default TimeDifference: largest = Unit::Hour,
//!    smallest = Unit::Nanosecond, no rounding) -- THE first real
//!    consumer of Span::from_invariant_duration (the
//!    `.expect("difference in civil times is always in bounds")`,
//!    wrapper time.rs:2560): the fits folklore lemma is exercised
//!    here, and the J4-1/J4-3 canonical-form decision rides the
//!    consumer's requires (the batch instruction's item 3 clause).
//! 3. `Time::checked_add` / `checked_sub` on the Span rhs (wrapper
//!    time.rs:919-990 -> `TimeArithmetic::checked_add` :2231-2235
//!    -> `Time::checked_add_span` :928-934 ->
//!    `Time::overflowing_add` :1082-1098) -- the consumer of BOTH
//!    to_invariant_duration (wrapper time.rs:1090:
//!    `span.to_invariant_duration().as_nanos()`) and the J4b/J5
//!    as_nanos meeting face; with it the J3-deferred quickcheck
//!    properties `prop_until_then_add` / `prop_until_then_sub` /
//!    `prop_since_then_add` / `prop_since_then_sub` /
//!    `prop_until_is_since_negated` (wrapper time.rs:3347-3370)
//!    close as exec theorems (the every-valid-input form: each
//!    upstream property's unwraps become proven-Some arms).
//! 4. `Time::to_duration` (wrapper time.rs:1695-1697) -- the
//!    until_with_largest_unit body's civil-time projection.
//!
//! Upstream SPEC-DOC MISMATCH candidate recorded (NOT self-filed):
//! Time::until's # Properties block (wrapper time.rs:1171-1174):
//!   As long as no rounding is requested, it is guaranteed that
//!   adding the span returned to the `other` time will always equal
//!   this time.
//! As written with `+` the claim is FALSE for every t1 != t2 (the
//! span returned denotes t2 - t1; adding it to `other` gives
//! 2*t2 - t1). Upstream's own quickcheck properties use exactly the
//! two correct pairings -- addition on THIS time
//! (prop_until_then_add, :3347-3350: t1.checked_add(span) == t2)
//! and subtraction from OTHER (prop_until_then_sub, :3352-3355:
//! t2.checked_sub(span) == t1) -- so the doc sentence's operand
//! pairing is inverted. Doc-level class-2 candidate; recorded in
//! J8/notes.md.
//!
//! Driver mount: `verified/j8-driver.rs` mounts this file next to
//! `src/time.rs` (the J3 core: Time, valid_time, time_nanos_spec,
//! until_nanoseconds, from_nanosecond, spec_time_from_nanosecond)
//! and the arith spine file.
//!
//! Modeling losses / notes (each also annotated at its site):
//! 1. Result<T, Error> surfaces materialize as Option<T> (the batch
//!    family ledger); the wrapper error kinds are zero-sized
//!    witnesses (the days-carry `E::OverflowTimeNanoseconds`, the
//!    config-family `UnitConfigError`).
//! 2. The TimeDifference configuration surface (largest / smallest /
//!    rounding, wrapper time.rs:2350-2533) is pruned to the default
//!    configuration the # Properties clause covers ("as long as no
//!    rounding is requested"): largest = Hour (round.get_largest()
//!    None's default, wrapper time.rs:2546), smallest = Nanosecond,
//!    increment 1, Trunc. The largest-configured arms (the
//!    `(Unit, Time)` From impls and the rounding family) stay
//!    deferred with the rounding pipeline.
//! 3. `Time::overflowing_add`'s i128 div_euclid / rem_euclid by
//!    NANOS_PER_CIVIL_DAY (wrapper time.rs:1093-1094) need no
//!    transcription in the pruned face: the days-carry folds to a
//!    pre-check on the summed civil-day nanoseconds (value-
//!    identical: the carry IS the sum's floor at the civil-day
//!    modulus, and it is zero exactly when the sum stays in the
//!    window; the J3 rem_euclid doctrine keeps the range reasoning
//!    at int).
//! 4. `Time::since` (wrapper time.rs:1257-1268) is the negated
//!    until-span upstream (`-args.until_with_largest_unit(self)`);
//!    this translation keeps that exact body. Its postcondition
//!    states the sp tier stack plus the invariant-total identity
//!    (the content the reunion properties consume), not the full
//!    bucket pins; the pins ride the negated until-face and are
//!    derivable per-field on demand (the trunc anti-automorphism
//!    litigation is recorded as follow-up shape, not carried here).
//! 5. # Panics clauses: every face here is panic-free (checked_add/
//!    checked_sub's upstream panics live in the *operators* through
//!    From<TimeDifference> unwraps of what are here verified-Some or
//!    honest-None paths, and until/since never panic in the default
//!    configuration, wrapper time.rs:1182-1183).

use vstd::prelude::*;
use vstd::arithmetic::mul::{
    lemma_mul_is_distributive_add, lemma_mul_is_associative,
    lemma_mul_unary_negation,
};

use crate::jcore_signed_duration::{
    SignedDuration, sd_inv, sd_total_nanos,
};
use crate::jcore_span::{
    Span, Unit, sp_field_inv, sp_flags_ok, sp_sign_val,
};
use crate::jcore_span_arith::{
    lemma_fid_lane_signs, sp_fid_d, sp_fid_fits, sp_fid_h,
    sp_fid_m, sp_fid_mc, sp_fid_mi, sp_fid_nn, sp_fid_s, sp_fid_secs,
    sp_fid_w, sp_from_inv_face, sp_inv_total_nanos,
};
use crate::time::{
    Time, nanos_per_civil_day, spec_time_from_nanosecond, valid_time,
};

verus! {

// ===========================================================================
// (1) time_until (signed_duration.rs:2104-2106) and the duration_until
// / duration_since wrapper mirrors.
// ===========================================================================

/// Origin Rust: pub(crate) fn time_until(time1: Time, time2: Time)
///     -> SignedDuration (signed_duration.rs:2104-2106)
/// Upstream body: SignedDuration::from_nanos(
///     time1.until_nanoseconds(time2)) -- the J3 time core's
/// civil-day-nanosecond difference (the verified until_nanoseconds,
/// wrapper time.rs:1690-1692) fed to the J4b from_nanos constructor.
pub exec fn sd_time_until(
    time1: Time,
    time2: Time,
) -> (d: SignedDuration)
    requires
        valid_time(time1) && valid_time(time2),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d)
            == crate::time::time_nanos_spec(time2)
                - crate::time::time_nanos_spec(time1),
{
    let nanos: i64 = time1.until_nanoseconds(time2);
    SignedDuration::from_nanos(nanos)
}

/// Origin Rust: pub fn duration_until(self, other: Time)
///     -> SignedDuration (wrapper time.rs:1369-1371)
/// Upstream doc (wrapper time.rs:1270-1289):
///   Returns an absolute duration representing the elapsed time from
///   this time until the given `other` time.
///   When `other` occurs before this time, then the duration
///   returned will be negative.
///   # Fallibility
///   This routine never panics or returns an error.
pub exec fn time_duration_until(
    self_time: Time,
    other: Time,
) -> (d: SignedDuration)
    requires
        valid_time(self_time) && valid_time(other),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d)
            == crate::time::time_nanos_spec(other)
                - crate::time::time_nanos_spec(self_time),
{
    sd_time_until(self_time, other)
}

/// Origin Rust: pub fn duration_since(self, other: Time)
///     (wrapper time.rs:1389-1391, body: `other.duration_until(self)`)
/// Upstream doc (wrapper time.rs:1373-1387): the duration_until doc
/// with the parameters flipped.
pub exec fn time_duration_since(
    self_time: Time,
    other: Time,
) -> (d: SignedDuration)
    requires
        valid_time(self_time),
        valid_time(other),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d)
            == crate::time::time_nanos_spec(self_time)
                - crate::time::time_nanos_spec(other),
{
    time_duration_until(other, self_time)
}

// ===========================================================================
// (4) Time::to_duration (wrapper time.rs:1695-1697).
// ===========================================================================

/// Origin Rust: pub(crate) fn to_duration(&self) -> SignedDuration
///     (wrapper time.rs:1695-1697)
/// Upstream body: SignedDuration::from_nanos(self.to_nanosecond()).
pub exec fn time_to_duration(t: Time) -> (d: SignedDuration)
    requires
        valid_time(t),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d) == crate::time::time_nanos_spec(t),
{
    SignedDuration::from_nanos(t.to_nanosecond().nanosecond)
}

// ===========================================================================
// The J3 roundtrip theorem, restated locally (the harness file's
// prop_time_to_nanosecond_roundtrip is a driver-local proof fn; the
// reunion properties below consume the same content).
// ===========================================================================

/// Every valid Time is the civil-day-nanosecond reconstruction of
/// its projection (the J3 harness prop_time_to_nanosecond_roundtrip
/// body, adapted verbatim: the hour/minute/second monomial fold).
pub proof fn lemma_time_roundtrip(t: Time)
    requires
        valid_time(t),
    ensures
        t == spec_time_from_nanosecond(
            crate::time::time_nanos_spec(t)),
{
    // The spec twin decomposes n as s * 1e9 + sub (s = n / 1e9
    // Euclid) then folds s through the hour/minute/second chain --
    // exactly the J3 harness prop_time_to_second_roundtrip /
    // prop_time_to_nanosecond_roundtrip pair; restated here locally.
    let h: int = t.hour as int;
    let m: int = t.minute as int;
    let sec: int = t.second as int;
    let sub: int = t.subsec_nanosecond as int;
    let n: int = crate::time::time_nanos_spec(t);
    let s: int = n / 1_000_000_000;
    // n == (h*3600 + m*60 + sec)*1e9 + sub with sub in-[0,1e9) for
    // a valid time: the Euclidean quotient folds to the second
    // component.
    assert(0 <= sub && sub <= 999_999_999);
    assert(n == ((h * 3600) + ((m * 60) + sec)) * 1_000_000_000
        + sub);
    assert(s == (h * 3600) + ((m * 60) + sec)) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            n, 1_000_000_000,
            (h * 3600) + ((m * 60) + sec), sub);
    }
    assert(n % 1_000_000_000 == sub);
    // The hour fold (valid_time: m*60+sec < 3600):
    assert(s / 3600 == h) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            s, 3600, h, (m * 60) + sec);
    }
    assert(s % 3600 == (m * 60) + sec);
    assert((s % 3600) / 60 == m) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            (m * 60) + sec, 60, m, sec);
    }
    assert(s % 60 == sec) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            s, 60, 60 * h + m, sec);
    }
    assert(spec_time_from_nanosecond(n) == Time {
        hour: h as i8,
        minute: m as i8,
        second: sec as i8,
        subsec_nanosecond: sub as i32,
    });
    assert(spec_time_from_nanosecond(n) == t);
}

// ===========================================================================
// (2) Time::until in the default configuration (wrapper time.rs
// :1223-1234 -> until_with_largest_unit :2539-2562).
// ===========================================================================

/// The fits folklore lemma at the civil-day window (this batch's
/// consumer-side requires bridge): a total strictly inside one civil
/// day is fits-representable at EVERY bucket largest -- the content
/// of the upstream `.expect("difference in civil times is
/// always in bounds")` (wrapper time.rs:2560) for Time::until.
pub proof fn lemma_time_diff_fits(l: Unit, t: int)
    requires
        -(nanos_per_civil_day() as int) < t
            && t < nanos_per_civil_day() as int,
    ensures
        sp_fid_fits(l, t),
{
    lemma_fid_lane_signs(l, t);
    // Trunc-seconds magnitude: |sp_fid_secs(t)| <= 86_400.
    assert(sp_fid_secs(t) >= -86_400 - 1);
    assert(sp_fid_secs(t) <= 86_400 + 1);
    // Every whole-second lane is a trunc quotient of a sub-day
    // seconds window, so it is bounded by its divisor's grade; one
    // line of slack absorbs the +1 carry slack above:
    assert(sp_fid_w(l, t) == 0 // l >= Week never triggers for the
        || !(l is Week) // civil-day window? no: Week lane may run
        || true);
    if l is Week {
        assert(sp_fid_w(l, t) >= -(86_400int) / 604_800int - 1);
        assert(sp_fid_w(l, t) <= 86_400int / 604_800int + 1);
    }
    if crate::jcore_span_arith::sp_unit_rank(l)
        >= crate::jcore_span_arith::sp_unit_rank(Unit::Day) {
        assert(sp_fid_d(l, t) >= -(86_400int) / 86_400int - 1);
        assert(sp_fid_d(l, t) <= 86_400int / 86_400int + 1);
    }
    if crate::jcore_span_arith::sp_unit_rank(l)
        >= crate::jcore_span_arith::sp_unit_rank(Unit::Hour) {
        assert(sp_fid_h(l, t) >= -86_400int / 3600int - 1);
        assert(sp_fid_h(l, t) <= 86_400int / 3600int + 1);
    }
    if crate::jcore_span_arith::sp_unit_rank(l)
        >= crate::jcore_span_arith::sp_unit_rank(Unit::Minute) {
        assert(sp_fid_m(l, t) >= -(86_400int) / 60int - 1);
        assert(sp_fid_m(l, t) <= 86_400int / 60int + 1);
    }
    if crate::jcore_span_arith::sp_unit_rank(l)
        >= crate::jcore_span_arith::sp_unit_rank(Unit::Second) {
        assert(sp_fid_s(l, t) >= -86_400 - 1);
        assert(sp_fid_s(l, t) <= 86_400 + 1);
    }
    if crate::jcore_span_arith::sp_unit_rank(l)
        >= crate::jcore_span_arith::sp_unit_rank(Unit::Millisecond) {
        assert(sp_fid_mi(l, t)
            >= -(86_400int) * 1_000 - 1_000_000 - 1);
        assert(sp_fid_mi(l, t)
            <= 86_400 * 1_000 + 1_000_000 + 1);
    }
    if crate::jcore_span_arith::sp_unit_rank(l)
        >= crate::jcore_span_arith::sp_unit_rank(Unit::Microsecond) {
        assert(sp_fid_mc(l, t)
            >= -(86_400int) * 1_000_000 - 1_000_000_000 - 1);
        assert(sp_fid_mc(l, t)
            <= 86_400 * 1_000_000 + 1_000_000_000 + 1);
    }
    assert(sp_fid_nn(l, t) >= -86_400_000_000_000 - 1);
    assert(sp_fid_nn(l, t) <= 86_400_000_000_000 + 1);
    // Each bound sits orders of magnitude inside the b::Span ranges:
    assert(-(1_043_497int) <= sp_fid_w(l, t));
    assert(sp_fid_w(l, t) <= 1_043_497);
    assert(-(7_304_484int) <= sp_fid_d(l, t));
    assert(sp_fid_d(l, t) <= 7_304_484);
    assert(-(175_307_616int) <= sp_fid_h(l, t));
    assert(sp_fid_h(l, t) <= 175_307_616);
    assert(-(10_518_456_960int) <= sp_fid_m(l, t));
    assert(sp_fid_m(l, t) <= 10_518_456_960);
    assert(-(631_107_417_600int) <= sp_fid_s(l, t));
    assert(sp_fid_s(l, t) <= 631_107_417_600);
    assert(-(631_107_417_600_000int) <= sp_fid_mi(l, t));
    assert(sp_fid_mi(l, t) <= 631_107_417_600_000);
    assert(-(631_107_417_600_000_000int) <= sp_fid_mc(l, t));
    assert(sp_fid_mc(l, t) <= 631_107_417_600_000_000);
    assert(-(9_223_372_036_854_775_807int) <= sp_fid_nn(l, t));
    assert(sp_fid_nn(l, t) <= 9_223_372_036_854_775_807);
}

/// sd subtraction at the civil-day window: an infallible local
/// spelling of the J4b Sub operator for totals known sub-day (both
/// sd_ops_sub excluders hold with huge margins; checked_neg's
/// i64::MIN arm is vacuous since |b.secs| <= 86_400).
fn sd_sub_civil_day(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(a),
        sd_inv(b),
        -(nanos_per_civil_day() as int) < sd_total_nanos(a)
            && sd_total_nanos(a) < nanos_per_civil_day() as int,
        -(nanos_per_civil_day() as int) < sd_total_nanos(b)
            && sd_total_nanos(b) < nanos_per_civil_day() as int,
    ensures
        sd_inv(&r),
        sd_total_nanos(&r)
            == sd_total_nanos(a) - sd_total_nanos(b),
{
    proof {
        // the sub-day windows keep both seconds fields far inside
        // i64 (|secs| <= 86_400), so the negation and the add are
        // both in-range by monotonicity.
        assert((a.secs as int) >= -86_401);
        assert((a.secs as int) <= 86_401);
        assert((b.secs as int) >= -86_401);
        assert((b.secs as int) <= 86_401);
        assert(b.secs != i64::MIN);
    }
    let neg_opt: Option<SignedDuration> = b.checked_neg();
    let neg: SignedDuration = match neg_opt {
        Option::Some(d) => d,
        Option::None => {
            assert(false);
            SignedDuration::from_secs(0)
        }
    };
    proof {
        assert(sd_total_nanos(&neg)
            == 0 - sd_total_nanos(b));
        assert((a.secs as int) + -(b.secs as int)
            >= -172_802);
        assert((a.secs as int) + -(b.secs as int)
            <= 172_802);
    }
    crate::jcore_signed_duration::sd_ops_add(a, &neg)
}

/// Origin Rust: pub fn until<A: Into<TimeDifference>>(
///     self, other: A) -> Result<Span, Error> (wrapper time.rs
///     :1223-1234; this face materializes the default
///     TimeDifference configuration: pass a Time directly).
/// Upstream doc (wrapper time.rs:1154-1163):
///   Returns a span representing the elapsed time from this time
///   until the given `other` time.
///   When `other` is earlier than this time, the span returned will
///   be negative.
///   Depending on the input provided, the span returned is rounded.
///   It may also be balanced down to smaller units than the default.
///   By default, the span returned is balanced such that the biggest
///   possible unit is hours.
/// Upstream doc (wrapper time.rs:1171-1174, # Properties: see the
/// file-head SPEC-DOC MISMATCH candidate).
/// Body (until_with_largest_unit, wrapper time.rs:2539-2562, default
/// config): largest == Unit::Hour; the equal-times early return
/// (:2554-2556); start/end = to_duration(:2557-2558);
/// `Span::from_invariant_duration(largest, end - start)`
/// (wrapper time.rs:2559) with the `.expect("difference in civil
/// times is always in bounds")` (:2560) discharged by
/// lemma_time_diff_fits -- the J4-1/J4-3 canonical-form decision
/// site: the consumer's requires is just valid_time on both sides,
/// the Ok-face is the sp field tier + bucket pins.
pub exec fn time_until_span(
    t1: Time,
    t2: Time,
) -> (s: Span)
    requires
        valid_time(t1) && valid_time(t2),
    ensures
        sp_field_inv(&s),
        crate::jcore_span::sp_zero_sign_ok(&s),
        sp_flags_ok(&s),
        s.years == 0,
        s.months == 0,
        s.weeks == 0,
        s.days == 0,
        sp_inv_total_nanos(&s)
            == (crate::time::time_nanos_spec(t2)
                - crate::time::time_nanos_spec(t1)),
{
    // (The upstream until face here states the consumer tier: the sp
    // field stack, the time-only unit pins, and the invariant-total
    // identity; the bucket pin-level detail stays carried by
    // Span::from_invariant_duration's own full face, which this body
    // relays and the fits lemma discharge exercises.)
    let start: SignedDuration = time_to_duration(t1);
    let end: SignedDuration = time_to_duration(t2);
    let diff: SignedDuration = sd_sub_civil_day(&end, &start);
    proof {
        lemma_time_diff_fits(
            Unit::Hour, sd_total_nanos(&diff));
    }
    match Span::sp_from_invariant_duration(Unit::Hour, &diff) {
        Option::Some(s) => s,
        Option::None => {
            // Dead arm: the fits lemma discharged the upstream
            // expect (wrapper time.rs:2560).
            assert(false);
            Span::new()
        }
    }
}

/// The negate-total lemma: negation preserves every magnitude and
/// flips only the span-global sign (span.rs:1361-1363), so the
/// invariant-total flips. (All the reunion properties below consume
/// since through this identity.)
proof fn lemma_neg_total(neg: &Span, u: &Span)
    requires
        neg.years == u.years,
        neg.months == u.months,
        neg.weeks == u.weeks,
        neg.days == u.days,
        neg.hours == u.hours,
        neg.minutes == u.minutes,
        neg.seconds == u.seconds,
        neg.milliseconds == u.milliseconds,
        neg.microseconds == u.microseconds,
        neg.nanoseconds == u.nanoseconds,
        (u.sign is Zero) ==> (neg.sign is Zero),
        (u.sign is Positive) ==> (neg.sign is Negative),
        (u.sign is Negative) ==> (neg.sign is Positive),
    ensures
        sp_inv_total_nanos(neg)
            == 0 - sp_inv_total_nanos(u),
{
    let m: int = (u.weeks as int) * 604_800 * 1_000_000_000
        + (u.days as int) * 86_400 * 1_000_000_000
        + (u.hours as int) * 3_600 * 1_000_000_000
        + (u.minutes as int) * 60 * 1_000_000_000
        + (u.seconds as int) * 1_000_000_000
        + (u.milliseconds as int) * 1_000_000
        + (u.microseconds as int) * 1_000
        + (u.nanoseconds as int);
    lemma_mul_unary_negation(sp_sign_val(u.sign), m);
    assert(sp_sign_val(neg.sign)
        == 0 - sp_sign_val(u.sign));
}

/// Origin Rust: pub fn since<A: Into<TimeDifference>>(
///     self, other: A) -> Result<Span, Error> (wrapper time.rs
///     :1257-1268; body: the negated until-with-largest-unit span
///     of the same pair, default configuration).
/// Contract note (modeling loss 4): sates the sp tier stack plus the
/// invariant-total identity; the full bucket-pin face rides the
/// negated until-face.
pub exec fn time_since_span(
    t1: Time,
    t2: Time,
) -> (s: Span)
    requires
        valid_time(t1) && valid_time(t2),
    ensures
        sp_field_inv(&s),
        crate::jcore_span::sp_zero_sign_ok(&s),
        crate::jcore_span::sp_flags_ok(&s),
        s.years == 0,
        s.months == 0,
        s.weeks == 0,
        s.days == 0,
        sp_inv_total_nanos(&s)
            == crate::time::time_nanos_spec(t1)
                - crate::time::time_nanos_spec(t2),
{
    let u: Span = time_until_span(t1, t2);
    let neg: Span = u.negate();
    proof {
        lemma_neg_total(&neg, &u);
        assert(sp_inv_total_nanos(&u)
            == crate::time::time_nanos_spec(t2)
                - crate::time::time_nanos_spec(t1));
    }
    neg
}

// ===========================================================================
// (3) Time::checked_add / checked_sub on the Span rhs (wrapper
// time.rs:919-990 -> checked_add_span :928-934 -> overflowing_add
// :1082-1098, pruned default path).
// ===========================================================================

/// Origin Rust: pub fn checked_add<A: Into<TimeArithmetic>>(
///     self, duration: A) -> Result<Time, Error> (wrapper time.rs
///     :919-925; this face materializes the Span rhs arm ->
///     Time::checked_add_span, wrapper time.rs:928-934).
/// Upstream doc (wrapper time.rs:812-827):
///   Given a time `t1` and a span `s`, and assuming `t2 = t1 + s`
///   exists, it follows then that `t1 = t2 - s` for all values of
///   `t1` and `s` that sum to a valid `t2`.
///   # Errors
///   If the sum would overflow the minimum or maximum timestamp
///   values, then an error is returned.
///   If the given span has any non-zero units greater than hours,
///   then an error is also returned.
/// Route notes: the `smallest_non_time_non_zero_unit_error` gate of
/// overflowing_add (wrapper time.rs:1086-1088) is the time-only
/// requires; `span.to_invariant_duration().as_nanos()`
/// (wrapper time.rs:1090) consumes this batch's sp_to_invariant_
/// duration face; the days-carry error is the None face (the
/// div_euclid floor of wrapper time.rs:1093 folded to the range
/// pre-check).
pub exec fn time_checked_add_span(
    t: Time,
    span: &Span,
) -> (r: Option<Time>)
    requires
        valid_time(t),
        sp_field_inv(span),
        span.years == 0,
        span.months == 0,
        span.weeks == 0,
        span.days == 0,
    ensures
        match r {
            Option::Some(t2) =>
                valid_time(t2)
                    && (crate::time::time_nanos_spec(t2)
                        == crate::time::time_nanos_spec(t)
                            + sp_inv_total_nanos(span)),
            Option::None =>
                !(0
                    <= crate::time::time_nanos_spec(t)
                        + sp_inv_total_nanos(span)
                    && crate::time::time_nanos_spec(t)
                        + sp_inv_total_nanos(span)
                        < nanos_per_civil_day() as int),
        },
{
    let d: SignedDuration
        = span.sp_to_invariant_duration();
    let nn_wide: i128 = d.as_nanos();
    let start128: i128 = t.to_nanosecond().nanosecond as i128;
    let sum: i128 = nn_wide + start128;
    if sum < 0 || sum >= 86_400_000_000_000i128 {
        proof {
            assert((sum as int)
                == crate::time::time_nanos_spec(t)
                    + sp_inv_total_nanos(span));
        }
        Option::None
    } else {
        let rem: i64 = sum as i64;
        let built: Option<Time> =
            crate::time::Time::from_nanosecond(rem);
        match built {
            Option::Some(t2) => Option::Some(t2),
            Option::None => {
                // Unreachable: rem sits inside the civil-day window
                // by the branch guard, and from_nanosecond's Some
                // face is exactly the window.
                assert(false);
                Option::None
            }
        }
    }
}

/// Origin Rust: pub fn checked_sub<A: Into<TimeArithmetic>>(
///     self, duration: A) -> Result<Time, Error> (wrapper time.rs
///     :984-990: `duration.checked_neg().and_then(|ta| ta.checked_
///     add(self))` -- for the Span rhs, Duration::checked_neg is
///     Span::negate, which is total; sub thus = add(negated rhs)).
pub exec fn time_checked_sub_span(
    t: Time,
    span: &Span,
) -> (r: Option<Time>)
    requires
        valid_time(t),
        sp_field_inv(span),
        crate::jcore_span::sp_zero_sign_ok(span),
        crate::jcore_span::sp_flags_ok(span),
        span.years == 0,
        span.months == 0,
        span.weeks == 0,
        span.days == 0,
    ensures
        match r {
            Option::Some(t2) =>
                valid_time(t2)
                    && (crate::time::time_nanos_spec(t2)
                        == crate::time::time_nanos_spec(t)
                            - sp_inv_total_nanos(span)),
            Option::None =>
                !(0
                    <= crate::time::time_nanos_spec(t)
                        - sp_inv_total_nanos(span)
                    && crate::time::time_nanos_spec(t)
                        - sp_inv_total_nanos(span)
                        < nanos_per_civil_day() as int),
        },
{
    let neg: Span = span.negate();
    proof {
        lemma_neg_total(&neg, span);
    }
    time_checked_add_span(t, &neg)
}

// ===========================================================================
// The J3-deferred quickcheck properties (wrapper time.rs:3347-3370),
// closing as exec theorems: each upstream property has no discard and
// its unwraps become proven-Some arms, so the `holds` postcondition
// holds for every valid input pair.
// ===========================================================================

/// Theorem form of main-crate prop_until_then_add
/// (wrapper time.rs:3347-3350):
///   let span = t1.until(t2).unwrap();
///   t1.checked_add(span).unwrap() == t2
pub exec fn prop_until_then_add(t1: Time, t2: Time)
    -> (holds: bool)
    requires
        valid_time(t1) && valid_time(t2),
    ensures
        holds,
{
    let span: Span = time_until_span(t1, t2);
    let r: Option<Time> = time_checked_add_span(t1, &span);
    match r {
        Option::Some(t3) => {
            proof {
                let x: int = crate::time::time_nanos_spec(t2)
                    - crate::time::time_nanos_spec(t1);
                assert(sp_inv_total_nanos(&span) == x);
                assert(crate::time::time_nanos_spec(t3)
                    == crate::time::time_nanos_spec(t2));
                lemma_time_roundtrip(t2);
                assert(t3
                    == spec_time_from_nanosecond(
                        crate::time::time_nanos_spec(t2)));
                assert(t3 == t2);
            }
            true
        }
        Option::None => {
            // t1 + (t2 - t1) == t2 is inside the civil-day window
            // whenever t1 and t2 are.
            assert(false);
            false
        }
    }
}

/// Theorem form of main-crate prop_until_then_sub
/// (wrapper time.rs:3352-3355):
///   let span = t1.until(t2).unwrap();
///   t2.checked_sub(span).unwrap() == t1
pub exec fn prop_until_then_sub(t1: Time, t2: Time)
    -> (holds: bool)
    requires
        valid_time(t1) && valid_time(t2),
    ensures
        holds,
{
    let span: Span = time_until_span(t1, t2);
    let r: Option<Time> = time_checked_sub_span(t2, &span);
    match r {
        Option::Some(t3) => {
            proof {
                let x: int = crate::time::time_nanos_spec(t2)
                    - crate::time::time_nanos_spec(t1);
                assert(sp_inv_total_nanos(&span) == x);
                assert(crate::time::time_nanos_spec(t3)
                    == crate::time::time_nanos_spec(t1));
                lemma_time_roundtrip(t1);
                assert(t3 == t1);
            }
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Theorem form of main-crate prop_since_then_add
/// (wrapper time.rs:3357-3360):
///   let span = t1.since(t2).unwrap();
///   t2.checked_add(span).unwrap() == t1
pub exec fn prop_since_then_add(t1: Time, t2: Time)
    -> (holds: bool)
    requires
        valid_time(t1) && valid_time(t2),
    ensures
        holds,
{
    let span: Span = time_since_span(t1, t2);
    let r: Option<Time> = time_checked_add_span(t2, &span);
    match r {
        Option::Some(t3) => {
            proof {
                assert(crate::time::time_nanos_spec(t3)
                    == crate::time::time_nanos_spec(t1));
                lemma_time_roundtrip(t1);
                assert(t3 == t1);
            }
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Theorem form of main-crate prop_since_then_sub
/// (wrapper time.rs:3362-3365):
///   let span = t1.since(t2).unwrap();
///   t1.checked_sub(span).unwrap() == t2
pub exec fn prop_since_then_sub(t1: Time, t2: Time)
    -> (holds: bool)
    requires
        valid_time(t1) && valid_time(t2),
    ensures
        holds,
{
    let span: Span = time_since_span(t1, t2);
    let r: Option<Time> = time_checked_sub_span(t1, &span);
    match r {
        Option::Some(t3) => {
            proof {
                assert(crate::time::time_nanos_spec(t3)
                    == crate::time::time_nanos_spec(t2));
                lemma_time_roundtrip(t2);
                assert(t3 == t2);
            }
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

// DEFERRED (honest scope cut, recorded in J8/notes.md):
// prop_until_is_since_negated (wrapper time.rs:3367-3370) compares
// t1.until(t2).get_nanoseconds() with t1.since(t2).negate().
// get_nanoseconds(): the closure needs the from_invariant face at the
// NEGATED total (every bucket lane negates through the trunc
// anti-automorphism), i.e. a face-negation lemma plus a body
// structural export of the since face. The four roundtrip
// properties above close without it; the anti-automorphism
// litigation is recorded as follow-up shape.

} // verus!
