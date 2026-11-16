//! jiff 0.2.43 Span invariant-duration composition spine (crates/jiff/
//! src/span.rs + the SignedDuration internals it consumes) -- Verus
//! translation, batch J8 (the composition reunion batch).
//!
//! Scope (the J5/J4b-deferred tail the J5 notes prescribed for this
//! batch):
//! 1. `Span::from_invariant_duration` (span.rs:2679-2731) -- the
//!    8-stage bucketize chain over the
//!    `SignedDuration::as_*_with_remainder` family.
//! 2. `SignedDuration::as_civil_weeks_with_remainder` /
//!    `as_civil_days_with_remainder` / `as_hours_with_remainder` /
//!    `as_mins_with_remainder` / `as_secs_with_remainder` /
//!    `as_millis_with_remainder` / `as_micros_with_remainder`
//!    (signed_duration.rs:2362-2462, the J4b-deferred Span-interaction
//!    internals) plus the three infallible 32-bit constructors
//!    `from_civil_weeks32` / `from_civil_days32` / `from_hours32`
//!    (signed_duration.rs:2321-2352).
//! 3. `Span::to_invariant_duration` and
//!    `to_invariant_duration_time_only` (span.rs:2416-2490), with the
//!    upstream `_FITS_IN_U64` compile-time asserts (span.rs:2422-2442,
//!    :2465-2478) materialized as verified int facts (a const-eval
//!    assert is not itself a verus obligation; its content is restated
//!    at int and proved).
//! 4. `Span::checked_add_invariant` / `checked_add_invariant_duration`
//!    (span.rs:1817-1840) and the public `checked_add` / `checked_sub`
//!    entry faces (span.rs:1758-1764, :1871-1879) at the invariant
//!    (no-relative-date) path.
//!
//! Driver mount: `verified/j8-driver.rs` mounts this file via #[path]
//! next to `src/bounds.rs`, `src/jcore_signed_duration.rs` and
//! `src/jcore_span.rs` (the j5-driver precedent: the closed panels
//! re-verify in this driver's run). Mounting-decision record (batch
//! option a vs option b): option a (independent driver whose module
//! tree replicates the lib.rs shape) was taken because merging
//! `jcore_span.rs` / `jcore_signed_duration.rs` into `src/lib.rs` would
//! push the lib panel past the 600-obligation discipline (wall 45) and
//! re-risk every closed panel; this family only consumes closed faces.
//! src/lib.rs is therefore NOT touched by this batch (not even
//! append-only): the composition spine hangs entirely off the driver.
//!
//! List of modeling losses / prunes (each also annotated at its site):
//! 1. `Result<Span, Error>` surfaces materialize as `Option<Span>`
//!    (the J1/J5 ledger: the error value is a zero-sized kind witness;
//!    error-message text is not verified). The one place the error
//!    KIND attribution is load-bearing -- the
//!    `b::SignedDurationSeconds::error()` mapping inside
//!    checked_add_invariant_duration (span.rs:1836-1838) -- carries an
//!    AUDIT note at its site (the J5 notes' audit point, dispositioned
//!    machine-checked here; see that site).
//! 2. `SpanArithmetic` / `SpanRelativeTo` / `Duration` config plumbing
//!    (span.rs:4059-4390, duration.rs:22-108) is pruned per the batch's
//!    pipeline doctrine: the translated entries materialize the
//!    `relative == None` path of `checked_add_span` /
//!    `checked_add_duration` (span.rs:1767-1812), which upstream gates
//!    through `requires_relative_date_err(unit)` (span.rs:6730-6739);
//!    the civil/zoned/days-are-24-hours relative pipeline
//!    (`to_relative` -> `Date/DateTime/Zoned::checked_add` ->
//!    `start.until`) stays deferred with its calendar-arithmetic mass,
//!    as do the `std::time::Duration` rhs arms (their `to_signed`
//!    conversion collapses to the SignedDuration rhs already
//!    translated here).
//! 3. `assert!(unit <= Unit::Week)` (span.rs:1823, :1834) is an
//!    upstream internal contract, not a documented panic; it
//!    materializes as a requires at its transcription sites.
//! 4. `Unit`'s upstream PartialOrd/Ord (discriminants Year = 9 ..
//!    Nanosecond = 0, span.rs:3874-3901) materializes as the rank
//!    twins below (the J5 ledger recorded that the verus Unit enum
//!    carries no discriminants; every ordering test routes through
//!    the rank).
//!
//! File-wide contract doctrine (the J4-1/J4-3 canonical-form decision
//! exercised at its first real consumer, per the J5 notes pointer):
//! the Ok-face spec twin is the sp field tier (sp_field_inv +
//! sp_zero_sign_ok + sp_flags_ok) plus the exact per-field bucket pins
//! and the total-nanosecond identity -- NOT any global canonical form
//! beyond what the setters maintain; the None-face is the exact
//! negation of the representability (fits) predicate over the summed
//! total. The precondition tier consumers need (e.g. wrapper
//! `Time::until`'s `.expect("difference in civil times is always in
//! bounds")`, wrapper time.rs:2560) is carried by the consumer's
//! requires; the fits folklore lemma below is the discharge tool.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    rust_div, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_strictly_positive, lemma_mul_unary_negation,
};

use crate::bounds::Sign;
use crate::jcore_signed_duration::{
    SignedDuration, sd_inv, sd_max_total_nanos, sd_min_total_nanos,
    sd_nanos_ok, sd_total_nanos,
};
use crate::jcore_span::{
    Span, Unit, sp_all_zero, sp_field_inv, sp_flags_ok, sp_sign_val,
    sp_zero_sign_ok,
};

verus! {

// ===========================================================================
// Unit ordering twins (span.rs:3874-3901, the upstream discriminant
// ordering Year = 9 > ... > Nanosecond = 0 that from_invariant_
// duration's `largest >= Unit::X` stages consume).
// ===========================================================================

/// Spec twin of the upstream Unit discriminant (span.rs:3876-3901):
/// bigger units compare greater.
pub open spec fn sp_unit_rank(u: Unit) -> int {
    match u {
        Unit::Year => 9,
        Unit::Month => 8,
        Unit::Week => 7,
        Unit::Day => 6,
        Unit::Hour => 5,
        Unit::Minute => 4,
        Unit::Second => 3,
        Unit::Millisecond => 2,
        Unit::Microsecond => 1,
        Unit::Nanosecond => 0,
    }
}

/// Exec twin of the Unit discriminant (the enum-contract doctrine: no
/// derived Ord; every comparison routes through the rank).
pub exec fn sp_unit_rank_exec(u: Unit) -> (r: i64)
    ensures
        (r as int) == sp_unit_rank(u),
{
    match u {
        Unit::Year => 9,
        Unit::Month => 8,
        Unit::Week => 7,
        Unit::Day => 6,
        Unit::Hour => 5,
        Unit::Minute => 4,
        Unit::Second => 3,
        Unit::Millisecond => 2,
        Unit::Microsecond => 1,
        Unit::Nanosecond => 0,
    }
}

/// Exec twin of upstream `largest >= Unit::X` (for example span.rs:2690,
/// :2695, :2700, :2705, :2710, :2717, :2724).
pub exec fn sp_unit_ge(a: Unit, b: Unit) -> (r: bool)
    ensures
        r <==> sp_unit_rank(a) >= sp_unit_rank(b),
{
    sp_unit_rank_exec(a) >= sp_unit_rank_exec(b)
}

/// Spec twin of upstream `largest_unit().max(other)` (span.rs:1773 via
/// the Unit Ord; the composed span unit passed down the invariant
/// checked_add chain).
pub open spec fn sp_unit_max(a: Unit, b: Unit) -> Unit {
    if sp_unit_rank(a) >= sp_unit_rank(b) {
        a
    } else {
        b
    }
}

/// Exec twin of the Unit max.
pub exec fn sp_unit_max_exec(a: Unit, b: Unit) -> (r: Unit)
    ensures
        r == sp_unit_max(a, b),
{
    if sp_unit_ge(a, b) {
        a
    } else {
        b
    }
}

/// Spec twin of `Span::largest_unit` (span.rs:2899-2903: the largest
/// non-zero unit flag, Nanosecond when all components are zero). The
/// shape mirrors the J5 exec face's ensures table (jcore_span.rs
/// largest_unit) so the two bridge by flag equality.
pub open spec fn sp_span_largest(s: &Span) -> Unit {
    if s.units.year {
        Unit::Year
    } else if s.units.month {
        Unit::Month
    } else if s.units.week {
        Unit::Week
    } else if s.units.day {
        Unit::Day
    } else if s.units.hour {
        Unit::Hour
    } else if s.units.minute {
        Unit::Minute
    } else if s.units.second {
        Unit::Second
    } else if s.units.millisecond {
        Unit::Millisecond
    } else if s.units.microsecond {
        Unit::Microsecond
    } else {
        Unit::Nanosecond
    }
}

// ===========================================================================
// The bucket-chain spec twins (all int, all rust_div/rust_rem -- the
// J4 doctrine that spec-position machine / and % would be Euclidean).
//
// The chain is the exact int content of span.rs:2685-2728 walked over
// the CANONICAL SignedDuration pair {trunc(total/1e9),
// total - trunc(total/1e9)*1e9}, which is the pair sd_inv guarantees
// (lemma_sd_canonical_secs below is the bridge sd_inv consumers
// call). Stage table (upstream stage conditions verbatim):
//   weeks   iff matches!(largest, Unit::Week)    (span.rs:2685)
//   days    iff largest >= Unit::Day              (span.rs:2690)
//   hours   iff largest >= Unit::Hour             (span.rs:2695)
//   minutes iff largest >= Unit::Minute           (span.rs:2700)
//   seconds iff largest >= Unit::Second           (span.rs:2705)
//   millis  iff largest >= Unit::Millisecond      (span.rs:2710)
//   micros  iff largest >= Unit::Microsecond       (span.rs:2717)
//   nanos   always (span.rs:2724: `largest >= Unit::Nanosecond` is a
//                  tautology -- Nanosecond is the smallest unit)
// and the whole-second strips cascade to the millisecond stage input,
// while the millisecond stage itself zeroes the seconds for every
// later stage (as_millis_with_remainder keeps only the subsecond --
// signed_duration.rs:2446-2451). That zeroing (NOT the seconds-cascade
// remainder) is what the sp_fid_mc_secs / sp_fid_nn_secs twins below
// encode; spelling it wrong double-counts the residual seconds for
// largest in {Minute-less} ranks, so these two definitions are
// contract-bearing.
// ===========================================================================

pub open spec fn S_NANOS_PER_SEC() -> int { 1_000_000_000 }
pub open spec fn S_CIVIL_WEEK_SECS() -> int { 604_800 }
pub open spec fn S_CIVIL_DAY_SECS() -> int { 86_400 }
pub open spec fn S_HOUR_SECS() -> int { 3_600 }
pub open spec fn S_MIN_SECS() -> int { 60 }

/// Canonical whole-seconds component of a total nanosecond count.
pub open spec fn sp_fid_secs(t: int) -> int {
    rust_div(t, S_NANOS_PER_SEC())
}

/// Canonical subsecond nanoseconds component of a total.
pub open spec fn sp_fid_sub(t: int) -> int {
    rust_rem(t, S_NANOS_PER_SEC())
}

/// Weeks field of the bucket chain (span.rs:2686-2689).
pub open spec fn sp_fid_w(l: Unit, t: int) -> int {
    if l is Week {
        rust_div(sp_fid_secs(t), S_CIVIL_WEEK_SECS())
    } else {
        0
    }
}

/// Whole seconds after the weeks stage.
pub open spec fn sp_fid_r_w(l: Unit, t: int) -> int {
    if l is Week {
        rust_rem(sp_fid_secs(t), S_CIVIL_WEEK_SECS())
    } else {
        sp_fid_secs(t)
    }
}

/// Days field (span.rs:2691-2694).
pub open spec fn sp_fid_d(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
        rust_div(sp_fid_r_w(l, t), S_CIVIL_DAY_SECS())
    } else {
        0
    }
}

/// Whole seconds after the days stage.
pub open spec fn sp_fid_r_d(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
        rust_rem(sp_fid_r_w(l, t), S_CIVIL_DAY_SECS())
    } else {
        sp_fid_r_w(l, t)
    }
}

/// Hours field (span.rs:2696-2699).
pub open spec fn sp_fid_h(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
        rust_div(sp_fid_r_d(l, t), S_HOUR_SECS())
    } else {
        0
    }
}

/// Whole seconds after the hours stage.
pub open spec fn sp_fid_r_h(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
        rust_rem(sp_fid_r_d(l, t), S_HOUR_SECS())
    } else {
        sp_fid_r_d(l, t)
    }
}

/// Minutes field (span.rs:2701-2704).
pub open spec fn sp_fid_m(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
        rust_div(sp_fid_r_h(l, t), S_MIN_SECS())
    } else {
        0
    }
}

/// Whole seconds after the minutes stage.
pub open spec fn sp_fid_r_m(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
        rust_rem(sp_fid_r_h(l, t), S_MIN_SECS())
    } else {
        sp_fid_r_h(l, t)
    }
}

/// Seconds field (span.rs:2706-2709).
pub open spec fn sp_fid_s(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Second) {
        sp_fid_r_m(l, t)
    } else {
        0
    }
}

/// Whole seconds after the seconds stage (0 when it ran; the untouched
/// chain remainder otherwise).
pub open spec fn sp_fid_r_s(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Second) {
        0
    } else {
        sp_fid_r_m(l, t)
    }
}

/// Milliseconds field (span.rs:2711-2715: as_millis_with_remainder
/// over the carried duration).
pub open spec fn sp_fid_mi(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Millisecond) {
        sp_fid_r_s(l, t) * 1_000
            + rust_div(sp_fid_sub(t), 1_000_000)
    } else {
        0
    }
}

/// Subsecond nanos after the millis stage (span.rs:2448:
/// `self.subsec_nanos() % NANOS_PER_MILLI`; the untouched subsecond
/// when the millis stage did not run).
pub open spec fn sp_fid_n_am(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Millisecond) {
        rust_rem(sp_fid_sub(t), 1_000_000)
    } else {
        sp_fid_sub(t)
    }
}

/// Seconds at the micros stage input: the millis stage ran (zeroing
/// the seconds, signed_duration.rs:2449) or nothing below minute
/// ever ran (largest is Microsecond or Nanosecond -- ranks below
/// Millisecond also fall below Second, so no earlier stage stripped
/// anything either).
pub open spec fn sp_fid_mc_secs(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Millisecond) {
        0
    } else {
        sp_fid_secs(t)
    }
}

/// Microseconds field (span.rs:2718-2722).
pub open spec fn sp_fid_mc(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Microsecond) {
        sp_fid_mc_secs(l, t) * 1_000_000
            + rust_div(sp_fid_n_am(l, t), 1_000)
    } else {
        0
    }
}

/// Seconds at the final (nanos) stage input: zeroed by the micros
/// stage when it ran (rank >= Microsecond), else untouched
/// (largest == Nanosecond -- the only rank below Microsecond is
/// Nanosecond, which also sits below every earlier stage).
pub open spec fn sp_fid_nn_secs(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Microsecond) {
        0
    } else {
        sp_fid_secs(t)
    }
}

/// Subsecond nanos at the final stage input (span.rs:2459's
/// `% NANOS_PER_MICRO` when micros ran; the passed-through n_am
/// otherwise).
pub open spec fn sp_fid_nn_nanos(l: Unit, t: int) -> int {
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Microsecond) {
        rust_rem(sp_fid_n_am(l, t), 1_000)
    } else {
        sp_fid_n_am(l, t)
    }
}

/// Nanoseconds field (span.rs:2724-2728): the whole remaining
/// duration, `dur.as_nanos()` (secs * 1e9 + subsec at the stage
/// input).
pub open spec fn sp_fid_nn(l: Unit, t: int) -> int {
    sp_fid_nn_secs(l, t) * S_NANOS_PER_SEC()
        + sp_fid_nn_nanos(l, t)
}

/// The representability predicate: every bucket value inside its
/// b::Span* range (jiff src/util/b.rs:193-231, the sp_field_inv
/// bounds).
///
/// The i64::try_from gates of the three i128 stages (span.rs:2712-
/// 2713, :2719-2720, :2725-2726) are subsumed by the b ranges: the
/// millis and micros b ranges lie strictly inside the i64 range (so an
/// i64-overflow implies the b conjunct fails), and the SpanNanoseconds
/// range IS the i64 range. CONTRACT-BEARING: the None face of
/// from_invariant_duration below is exactly this predicate's negation,
/// so no upstream error path is dropped by the subsumption.
pub open spec fn sp_fid_fits(l: Unit, t: int) -> bool {
    &&& -(1_043_497int) <= sp_fid_w(l, t)
        && sp_fid_w(l, t) <= 1_043_497
    &&& -(7_304_484int) <= sp_fid_d(l, t)
        && sp_fid_d(l, t) <= 7_304_484
    &&& -(175_307_616int) <= sp_fid_h(l, t)
        && sp_fid_h(l, t) <= 175_307_616
    &&& -(10_518_456_960int) <= sp_fid_m(l, t)
        && sp_fid_m(l, t) <= 10_518_456_960
    &&& -(631_107_417_600int) <= sp_fid_s(l, t)
        && sp_fid_s(l, t) <= 631_107_417_600
    &&& -(631_107_417_600_000int) <= sp_fid_mi(l, t)
        && sp_fid_mi(l, t) <= 631_107_417_600_000
    &&& -(631_107_417_600_000_000int) <= sp_fid_mc(l, t)
        && sp_fid_mc(l, t) <= 631_107_417_600_000_000
    &&& -(9_223_372_036_854_775_807int) <= sp_fid_nn(l, t)
        && sp_fid_nn(l, t) <= 9_223_372_036_854_775_807
}

/// Uniqueness of the trunc div/mod split with the sign-coupled
/// remainder (the fact sd_inv's sign harmonization is what makes a
/// duration's field pair canonical). Used by lemma_sd_canonical_secs.
proof fn lemma_trunc_uniqueness(t: int, d: int, q: int, r: int)
    requires
        d > 0,
        t == q * d + r,
        -(d) < r && r < d,
        r == 0 || ((t > 0 && r > 0) || (t < 0 && r < 0)),
    ensures
        q == rust_div(t, d),
        r == rust_rem(t, d),
{
    if t > 0 {
        // 0 <= r < d here (r may be 0: the coupling premise allows
        // t == q*d exactly): the Euclidean converse applies directly,
        // and rust_div/rust_rem match Euclid on positive dividends.
        lemma_fundamental_div_mod_converse(t, d, q, r);
        assert(q == t / d);
        assert(r == t % d);
    } else if t < 0 {
        // Case split on r: the coupling premise gives r == 0 (then
        // the converse runs with r' == 0) or r < 0 (then -r in (0, d)).
        // Negation pushes through the product by the unary-negation
        // mul lemma (z3 does not negate q*d termwise on its own --
        // the J5 'variable-times-variable products are never
        // self-evident' rule).
        lemma_mul_unary_negation(q, d);
        assert((-q) * d == -(q * d));
        if r == 0 {
            assert(-t == (-q) * d + 0);
            lemma_fundamental_div_mod_converse(-t, d, -q, 0);
            assert((-t) / d == -q);
        } else {
            assert(r < 0);
            assert(0 < -r && -r < d);
            assert(-t == (-q) * d + (-r));
            lemma_fundamental_div_mod_converse(-t, d, -q, -r);
            assert((-t) / d == -q);
        }
        // rust_div(t,d) == -((-t)/d) and rust_rem likewise (the
        // definitions' a < 0 arms); the premise ranges give the
        // remainder's final equality in both r sub-cases.
        assert(q == -((-t) / d));
        if r == 0 {
            assert((-t) % d == 0);
            assert(r == -((-t) % d));
        } else {
            assert((-t) % d == -r);
            assert(r == -((-t) % d));
        }
    } else {
        // t == 0: the coupling premise gives r == 0; then q * d == 0
        // with d != 0 cancels (nonlinear -- spelled by sign cases).
        assert(r == 0);
        assert(q * d == 0);
        assert(q == 0) by {
            if q > 0 {
                lemma_mul_strictly_positive(q, d);
            } else if q < 0 {
                lemma_mul_unary_negation(-q, d);
                lemma_mul_strictly_positive(-q, d);
                assert((-q) * d > 0);
                assert(q * d == -((-q) * d));
                assert(q * d < 0);
            }
        }
        assert(rust_div(0, d) == 0);
        assert(rust_rem(0, d) == 0);
    }
}

/// The sd_inv-to-canonical bridge: a sign-harmonized duration's field
/// pair IS the {trunc-seconds, trunc-subsec} pair of its total
/// (signed_duration.rs:30-40 type doc + the new_unchecked debug tier
/// :472-478). Every consumer of the bucket twins over an sd_inv value
/// calls this first.
pub proof fn lemma_sd_canonical_secs(d: &SignedDuration)
    requires
        sd_inv(d),
    ensures
        (d.secs as int) == sp_fid_secs(sd_total_nanos(d)),
        (d.nanos as int) == sp_fid_sub(sd_total_nanos(d)),
{
    let t: int = sd_total_nanos(d);
    let s: int = d.secs as int;
    let n: int = d.nanos as int;
    assert(t == s * S_NANOS_PER_SEC() + n);
    assert(-(999_999_999int) <= n && n <= 999_999_999);
    // sign coupling: sd_inv says signs agree or a side is zero.
    if s > 0 {
        assert(n >= 0);
    } else if s < 0 {
        assert(n <= 0);
    }
    lemma_trunc_uniqueness(t, S_NANOS_PER_SEC(), s, n);
}

// ===========================================================================
// The chain identity: why the bucket chain preserves the duration.
// ===========================================================================

pub proof fn lemma_fid_identity(l: Unit, t: int)
    ensures
        ((sp_fid_w(l, t) * S_CIVIL_WEEK_SECS()
            + sp_fid_d(l, t) * S_CIVIL_DAY_SECS()
            + sp_fid_h(l, t) * S_HOUR_SECS()
            + sp_fid_m(l, t) * S_MIN_SECS()
            + sp_fid_s(l, t)) * S_NANOS_PER_SEC())
            + sp_fid_mi(l, t) * 1_000_000
            + sp_fid_mc(l, t) * 1_000
            + sp_fid_nn(l, t)
            == t,
{
    let secs: int = sp_fid_secs(t);
    let sub: int = sp_fid_sub(t);
    lemma_fundamental_div_mod(t, S_NANOS_PER_SEC());
    assert(t == secs * S_NANOS_PER_SEC() + sub);
    // Strip the >= minute bulk in every rank.
    assert(secs
        == sp_fid_w(l, t) * S_CIVIL_WEEK_SECS() + sp_fid_r_w(l, t)) by {
        if l is Week {
            lemma_fundamental_div_mod(secs, S_CIVIL_WEEK_SECS());
        }
    }
    assert(sp_fid_r_w(l, t)
        == sp_fid_d(l, t) * S_CIVIL_DAY_SECS() + sp_fid_r_d(l, t)) by {
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
            lemma_fundamental_div_mod(
                sp_fid_r_w(l, t), S_CIVIL_DAY_SECS());
        }
    }
    assert(sp_fid_r_d(l, t)
        == sp_fid_h(l, t) * S_HOUR_SECS() + sp_fid_r_h(l, t)) by {
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
            lemma_fundamental_div_mod(
                sp_fid_r_d(l, t), S_HOUR_SECS());
        }
    }
    assert(sp_fid_r_h(l, t)
        == sp_fid_m(l, t) * S_MIN_SECS() + sp_fid_r_m(l, t)) by {
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
            lemma_fundamental_div_mod(
                sp_fid_r_h(l, t), S_MIN_SECS());
        }
    }
    // The seconds lane splits cleanly in every rank:
    assert(sp_fid_r_m(l, t)
        == sp_fid_s(l, t) + sp_fid_r_s(l, t));
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Second) {
        // SEC took the whole minute-lane remainder; the subsecond
        // stages see r_s == 0.
        assert(sp_fid_r_s(l, t) == 0);
        assert(sp_fid_mc_secs(l, t) == 0);
        assert(sp_fid_nn_secs(l, t) == 0);
        // Millis over {0, sub}.
        assert(sp_fid_mi(l, t) == rust_div(sub, 1_000_000)) by {
            lemma_fundamental_div_mod(sub, 1_000_000);
        }
        assert(sp_fid_n_am(l, t) == rust_rem(sub, 1_000_000));
        // Micros over {0, n_am}.
        assert(sp_fid_mc(l, t)
            == rust_div(sp_fid_n_am(l, t), 1_000)) by {
            lemma_fundamental_div_mod(sp_fid_n_am(l, t), 1_000);
        }
        assert(sp_fid_nn_nanos(l, t)
            == rust_rem(sp_fid_n_am(l, t), 1_000));
        // Fold through the sub lanes.
        assert(sub == sp_fid_mi(l, t) * 1_000_000
            + sp_fid_n_am(l, t));
        assert(sp_fid_n_am(l, t) == sp_fid_mc(l, t) * 1_000
            + sp_fid_nn_nanos(l, t));
    } else if sp_unit_rank(l) == sp_unit_rank(Unit::Millisecond) {
        // rank == 2: no stage above ran, so r_s == secs; the millis
        // field absorbs the full seconds and the subsecond stages
        // then walk the remainder.
        assert(sp_fid_r_s(l, t) == secs);
        assert(sp_fid_mc_secs(l, t) == 0);
        assert(sp_fid_nn_secs(l, t) == 0);
        assert(sp_fid_mi(l, t)
            == secs * 1_000 + rust_div(sub, 1_000_000)) by {
            lemma_fundamental_div_mod(sub, 1_000_000);
        }
        assert(sp_fid_n_am(l, t) == rust_rem(sub, 1_000_000));
        assert(sp_fid_mc(l, t)
            == rust_div(sp_fid_n_am(l, t), 1_000)) by {
            lemma_fundamental_div_mod(sp_fid_n_am(l, t), 1_000);
        }
        assert(sp_fid_nn_nanos(l, t)
            == rust_rem(sp_fid_n_am(l, t), 1_000));
        assert(sub == (sp_fid_mi(l, t) * 1_000_000
            - secs * S_NANOS_PER_SEC()) + sp_fid_n_am(l, t));
        assert(sub - rust_div(sub, 1_000_000) * 1_000_000
            == sp_fid_n_am(l, t));
        assert(sp_fid_n_am(l, t) == sp_fid_mc(l, t) * 1_000
            + sp_fid_nn_nanos(l, t));
    } else if sp_unit_rank(l) == sp_unit_rank(Unit::Microsecond) {
        // rank == 1: only micros and the final nanos ran; the micros
        // field absorbs the full seconds.
        assert(sp_fid_r_s(l, t) == secs);
        assert(sp_fid_mc_secs(l, t) == secs);
        assert(sp_fid_nn_secs(l, t) == 0);
        assert(sp_fid_mi(l, t) == 0);
        assert(sp_fid_n_am(l, t) == sub);
        assert(sp_fid_mc(l, t) == secs * 1_000_000
            + rust_div(sub, 1_000)) by {
            lemma_fundamental_div_mod(sub, 1_000);
        }
        assert(sp_fid_nn_nanos(l, t) == rust_rem(sub, 1_000));
        assert(sub == sp_fid_mc(l, t) * 1_000 - secs
            * S_NANOS_PER_SEC() + sp_fid_nn_nanos(l, t));
    } else {
        // rank == 0 (Nanosecond): nothing before the final stage ever
        // ran; the nanos field is the whole total.
        assert(sp_fid_r_s(l, t) == secs);
        assert(sp_fid_mi(l, t) == 0);
        assert(sp_fid_mc(l, t) == 0);
        assert(sp_fid_nn_secs(l, t) == secs);
        assert(sp_fid_nn_nanos(l, t) == sub);
        assert(sp_fid_nn(l, t) == t);
    }
}

/// Lane sign folklore: for a nonnegative total every bucket value is
/// nonnegative, dually for nonpositive (the trunc quotients of a
/// sign-agreeing pair). Used by the entry faces to pin the final
/// span sign, and by the as_*_with_remainder proof blocks.
pub proof fn lemma_fid_lane_signs(l: Unit, t: int)
    requires
        true,
    ensures
        (t >= 0)
            ==> (sp_fid_secs(t) >= 0 && sp_fid_sub(t) >= 0
                && sp_fid_w(l, t) >= 0 && sp_fid_r_w(l, t) >= 0
                && sp_fid_d(l, t) >= 0 && sp_fid_r_d(l, t) >= 0
                && sp_fid_h(l, t) >= 0 && sp_fid_r_h(l, t) >= 0
                && sp_fid_m(l, t) >= 0 && sp_fid_r_m(l, t) >= 0
                && sp_fid_s(l, t) >= 0 && sp_fid_r_s(l, t) >= 0
                && sp_fid_mi(l, t) >= 0 && sp_fid_n_am(l, t) >= 0
                && sp_fid_mc(l, t) >= 0 && sp_fid_nn(l, t) >= 0
                && sp_fid_mc_secs(l, t) >= 0
                && sp_fid_nn_secs(l, t) >= 0),
        (t <= 0)
            ==> (sp_fid_secs(t) <= 0 && sp_fid_sub(t) <= 0
                && sp_fid_w(l, t) <= 0 && sp_fid_r_w(l, t) <= 0
                && sp_fid_d(l, t) <= 0 && sp_fid_r_d(l, t) <= 0
                && sp_fid_h(l, t) <= 0 && sp_fid_r_h(l, t) <= 0
                && sp_fid_m(l, t) <= 0 && sp_fid_r_m(l, t) <= 0
                && sp_fid_s(l, t) <= 0 && sp_fid_r_s(l, t) <= 0
                && sp_fid_mi(l, t) <= 0 && sp_fid_n_am(l, t) <= 0
                && sp_fid_mc(l, t) <= 0 && sp_fid_nn(l, t) <= 0
                && sp_fid_mc_secs(l, t) <= 0
                && sp_fid_nn_secs(l, t) <= 0),
{
    if t == 0 {
        // The trunc quotient/rem of 0 are 0; every lane collapses.
        assert(sp_fid_secs(0) == 0);
        assert(sp_fid_sub(0) == 0);
        assert(sp_fid_w(l, 0) == 0);
        assert(sp_fid_r_w(l, 0) == 0);
        assert(sp_fid_d(l, 0) == 0);
        assert(sp_fid_r_d(l, 0) == 0);
        assert(sp_fid_h(l, 0) == 0);
        assert(sp_fid_r_h(l, 0) == 0);
        assert(sp_fid_m(l, 0) == 0);
        assert(sp_fid_r_m(l, 0) == 0);
        assert(sp_fid_s(l, 0) == 0);
        assert(sp_fid_r_s(l, 0) == 0);
        assert(sp_fid_n_am(l, 0) == 0);
        assert(sp_fid_mc_secs(l, 0) == 0);
        assert(sp_fid_nn_secs(l, 0) == 0);
    } else if t > 0 {
        // Positives: trunc preserve nonnegativity step by step.
        assert(sp_fid_secs(t) >= 0) by {
            let q = rust_div(t, S_NANOS_PER_SEC());
            let r = rust_rem(t, S_NANOS_PER_SEC());
            lemma_fundamental_div_mod(t, S_NANOS_PER_SEC());
            assert(t == q * S_NANOS_PER_SEC() + r);
            // rust_rem matches Euclid on positives: 0 <= r.
            assert(0 <= (t % S_NANOS_PER_SEC())
                < S_NANOS_PER_SEC());
            assert(r == t % S_NANOS_PER_SEC());
            if q < 0 {
                assert(q * S_NANOS_PER_SEC() + r
                    <= -S_NANOS_PER_SEC() + (S_NANOS_PER_SEC() - 1));
                assert(t < 0);
            }
        }
        assert(sp_fid_sub(t) >= 0) by {
            assert(sp_fid_sub(t)
                == t - sp_fid_secs(t) * S_NANOS_PER_SEC());
        }
        let secs: int = sp_fid_secs(t);
        let sub: int = sp_fid_sub(t);
        if l is Week {
            assert(sp_fid_w(l, t) >= 0) by {
                let q = rust_div(secs, S_CIVIL_WEEK_SECS());
                let r = rust_rem(secs, S_CIVIL_WEEK_SECS());
                lemma_fundamental_div_mod(secs, S_CIVIL_WEEK_SECS());
                assert(secs == q * S_CIVIL_WEEK_SECS() + r);
                assert(r == secs % S_CIVIL_WEEK_SECS());
                assert(0 <= r < S_CIVIL_WEEK_SECS());
                if q < 0 {
                    assert(secs < 0);
                }
            }
            assert(sp_fid_r_w(l, t) >= 0) by {
                assert(sp_fid_r_w(l, t)
                    == secs - sp_fid_w(l, t) * S_CIVIL_WEEK_SECS());
            }
        } else {
            assert(sp_fid_w(l, t) == 0);
            assert(sp_fid_r_w(l, t) == secs);
        }
        let rw: int = sp_fid_r_w(l, t);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
            assert(sp_fid_d(l, t) >= 0) by {
                let q = rust_div(rw, S_CIVIL_DAY_SECS());
                let r = rust_rem(rw, S_CIVIL_DAY_SECS());
                lemma_fundamental_div_mod(rw, S_CIVIL_DAY_SECS());
                assert(rw == q * S_CIVIL_DAY_SECS() + r);
                assert(r == rw % S_CIVIL_DAY_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(rw < 0);
                }
            }
            assert(sp_fid_r_d(l, t) >= 0) by {
                assert(sp_fid_r_d(l, t)
                    == rw - sp_fid_d(l, t) * S_CIVIL_DAY_SECS());
            }
        } else {
            assert(sp_fid_d(l, t) == 0);
            assert(sp_fid_r_d(l, t) == rw);
        }
        let rd: int = sp_fid_r_d(l, t);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
            assert(sp_fid_h(l, t) >= 0) by {
                let q = rust_div(rd, S_HOUR_SECS());
                let r = rust_rem(rd, S_HOUR_SECS());
                lemma_fundamental_div_mod(rd, S_HOUR_SECS());
                assert(rd == q * S_HOUR_SECS() + r);
                assert(r == rd % S_HOUR_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(rd < 0);
                }
            }
            assert(sp_fid_r_h(l, t) >= 0) by {
                assert(sp_fid_r_h(l, t)
                    == rd - sp_fid_h(l, t) * S_HOUR_SECS());
            }
        } else {
            assert(sp_fid_h(l, t) == 0);
            assert(sp_fid_r_h(l, t) == rd);
        }
        let rh: int = sp_fid_r_h(l, t);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
            assert(sp_fid_m(l, t) >= 0) by {
                let q = rust_div(rh, S_MIN_SECS());
                let r = rust_rem(rh, S_MIN_SECS());
                lemma_fundamental_div_mod(rh, S_MIN_SECS());
                assert(rh == q * S_MIN_SECS() + r);
                assert(r == rh % S_MIN_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(rh < 0);
                }
            }
            assert(sp_fid_r_m(l, t) >= 0) by {
                assert(sp_fid_r_m(l, t)
                    == rh - sp_fid_m(l, t) * S_MIN_SECS());
            }
        } else {
            assert(sp_fid_m(l, t) == 0);
            assert(sp_fid_r_m(l, t) == rh);
        }
        let rm: int = sp_fid_r_m(l, t);
        assert(sp_fid_s(l, t) >= 0);
        assert(sp_fid_r_s(l, t) >= 0);
        assert(sp_fid_mc_secs(l, t) >= 0);
        assert(sp_fid_nn_secs(l, t) >= 0);
        // r_s sub-lane: the div/mod over nonnegatives stays nonneg.
        assert(sp_fid_mi(l, t) >= 0) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Millisecond) {
                let q = rust_div(sub, 1_000_000);
                let r = rust_rem(sub, 1_000_000);
                lemma_fundamental_div_mod(sub, 1_000_000);
                assert(sub == q * 1_000_000 + r);
                assert(r == sub % 1_000_000);
                assert(0 <= r);
                if q < 0 {
                    assert(sub < 0);
                }
            }
        }
        assert(sp_fid_n_am(l, t) >= 0) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Millisecond) {
                assert(sp_fid_n_am(l, t)
                    == sub - rust_div(sub, 1_000_000) * 1_000_000);
            } else {
                assert(sp_fid_n_am(l, t) == sub);
            }
        }
        let nam: int = sp_fid_n_am(l, t);
        assert(sp_fid_mc(l, t) >= 0) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Microsecond) {
                let q = rust_div(nam, 1_000);
                let r = rust_rem(nam, 1_000);
                lemma_fundamental_div_mod(nam, 1_000);
                assert(nam == q * 1_000 + r);
                assert(r == nam % 1_000);
                assert(0 <= r);
                if q < 0 {
                    assert(nam < 0);
                }
            }
        }
        assert(sp_fid_nn(l, t) >= 0) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Microsecond) {
                assert(sp_fid_nn_nanos(l, t)
                    == nam - rust_div(nam, 1_000) * 1_000);
                assert(sp_fid_nn_nanos(l, t) >= 0);
                assert(sp_fid_nn_secs(l, t) == 0);
            } else {
                assert(sp_fid_nn_secs(l, t)
                    == sp_fid_mc_secs(l, t));
                assert(sp_fid_nn(l, t)
                    == sp_fid_secs(t) * S_NANOS_PER_SEC()
                        + sp_fid_n_am(l, t));
            }
        }
    } else {
        // t < 0: mirror of the t > 0 arm via negation.
        let u: int = -t;
        assert(sp_fid_secs(u) == -(sp_fid_secs(t))) by {
            let qa = rust_div(u, S_NANOS_PER_SEC());
            let ra = rust_rem(u, S_NANOS_PER_SEC());
            let qb = rust_div(t, S_NANOS_PER_SEC());
            let rb = rust_rem(t, S_NANOS_PER_SEC());
            lemma_fundamental_div_mod(u, S_NANOS_PER_SEC());
            lemma_fundamental_div_mod(t, S_NANOS_PER_SEC());
            assert(u == qa * S_NANOS_PER_SEC() + ra);
            assert(t == qb * S_NANOS_PER_SEC() + rb);
            // negation is an anti-automorphism of the trunc pair.
            lemma_trunc_uniqueness(u, S_NANOS_PER_SEC(),
                -(qb), -(rb));
            assert(qa == -(qb));
            assert(ra == -(rb));
        }
        assert(sp_fid_w(l, u) == -(sp_fid_w(l, t))) by {
            if l is Week {
                let qa = rust_div(sp_fid_secs(u), S_CIVIL_WEEK_SECS());
                let ra = rust_rem(sp_fid_secs(u), S_CIVIL_WEEK_SECS());
                lemma_trunc_uniqueness(sp_fid_secs(u),
                    S_CIVIL_WEEK_SECS(),
                    -(sp_fid_w(l, t)), -(sp_fid_r_w(l, t)));
                assert(sp_fid_secs(u)
                    == -(sp_fid_w(l, t)) * S_CIVIL_WEEK_SECS()
                        + -(sp_fid_r_w(l, t)));
                assert(sp_fid_secs(t)
                    == sp_fid_w(l, t) * S_CIVIL_WEEK_SECS()
                        + sp_fid_r_w(l, t));
                assert(sp_fid_secs(u) == -(sp_fid_secs(t)));
            }
        }
        assert(sp_fid_r_w(l, u) == -(sp_fid_r_w(l, t))) by {
            if l is Week {
                assert(sp_fid_secs(u)
                    == -(sp_fid_w(l, t)) * S_CIVIL_WEEK_SECS()
                        + -(sp_fid_r_w(l, t)));
                assert(sp_fid_secs(u)
                    == sp_fid_w(l, u) * S_CIVIL_WEEK_SECS()
                        + sp_fid_r_w(l, u));
                assert(sp_fid_w(l, u) == -(sp_fid_w(l, t)));
            } else {
                assert(sp_fid_secs(u) == -(sp_fid_secs(t)));
            }
        }
        // The days arm.
        assert(sp_fid_d(l, u) == -(sp_fid_d(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
                lemma_trunc_uniqueness(sp_fid_r_w(l, u),
                    S_CIVIL_DAY_SECS(),
                    -(sp_fid_d(l, t)), -(sp_fid_r_d(l, t)));
                assert(sp_fid_r_w(l, u)
                    == -(sp_fid_r_w(l, t)));
            }
        }
        assert(sp_fid_r_d(l, u) == -(sp_fid_r_d(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
                assert(sp_fid_r_w(l, u)
                    == -(sp_fid_d(l, t)) * S_CIVIL_DAY_SECS()
                        + -(sp_fid_r_d(l, t)));
                assert(sp_fid_r_w(l, u)
                    == sp_fid_d(l, u) * S_CIVIL_DAY_SECS()
                        + sp_fid_r_d(l, u));
                assert(sp_fid_d(l, u) == -(sp_fid_d(l, t)));
            } else {
                assert(sp_fid_r_w(l, u) == -(sp_fid_r_w(l, t)));
            }
        }
        assert(sp_fid_h(l, u) == -(sp_fid_h(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
                lemma_trunc_uniqueness(sp_fid_r_d(l, u),
                    S_HOUR_SECS(),
                    -(sp_fid_h(l, t)), -(sp_fid_r_h(l, t)));
                assert(sp_fid_r_d(l, u)
                    == -(sp_fid_r_d(l, t)));
            }
        }
        assert(sp_fid_r_h(l, u) == -(sp_fid_r_h(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
                assert(sp_fid_h(l, u) == -(sp_fid_h(l, t)));
            } else {
                assert(sp_fid_r_d(l, u) == -(sp_fid_r_d(l, t)));
            }
        }
        assert(sp_fid_m(l, u) == -(sp_fid_m(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
                lemma_trunc_uniqueness(sp_fid_r_h(l, u),
                    S_MIN_SECS(),
                    -(sp_fid_m(l, t)), -(sp_fid_r_m(l, t)));
                assert(sp_fid_r_h(l, u)
                    == -(sp_fid_r_h(l, t)));
            }
        }
        assert(sp_fid_r_m(l, u) == -(sp_fid_r_m(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
                assert(sp_fid_m(l, u) == -(sp_fid_m(l, t)));
            } else {
                assert(sp_fid_r_h(l, u) == -(sp_fid_r_h(l, t)));
            }
        }
        assert(sp_fid_sub(u) == -(sp_fid_sub(t))) by {
            lemma_trunc_uniqueness(u, S_NANOS_PER_SEC(),
                sp_fid_secs(u), sp_fid_sub(u));
            assert(sp_fid_secs(u)
                == -(sp_fid_secs(t)));
        }
        assert(sp_fid_s(l, u) == -(sp_fid_s(l, t))) by {
            assert(sp_fid_r_m(l, u)
                == -(sp_fid_r_m(l, t)));
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Second) {
                assert(sp_fid_s(l, u) == sp_fid_r_m(l, u));
                assert(sp_fid_s(l, u)
                    == -(sp_fid_s(l, t)));
            }
        }
        assert(sp_fid_r_s(l, u) == -(sp_fid_r_s(l, t))) by {
            if sp_unit_rank(l) >= sp_unit_rank(Unit::Second) {
                assert(sp_fid_r_s(l, u) == 0);
                assert(sp_fid_r_s(l, t) == 0);
            } else {
                assert(sp_fid_r_s(l, u) == sp_fid_r_m(l, u));
            }
        }
        assert(sp_fid_mi(l, u) == -(sp_fid_mi(l, t))) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Millisecond) {
                assert(sp_fid_r_s(l, u)
                    == -(sp_fid_r_s(l, t)));
                lemma_trunc_uniqueness(sp_fid_sub(u), 1_000_000,
                    -(rust_div(sp_fid_sub(t), 1_000_000)),
                    -(rust_rem(sp_fid_sub(t), 1_000_000)));
                assert(sp_fid_sub(u)
                    == -(rust_div(sp_fid_sub(t), 1_000_000))
                        * 1_000_000
                        + -(rust_rem(sp_fid_sub(t), 1_000_000)));
            }
        }
        assert(sp_fid_n_am(l, u) == -(sp_fid_n_am(l, t))) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Millisecond) {
                assert(sp_fid_sub(u)
                    == -(rust_div(sp_fid_sub(t), 1_000_000))
                        * 1_000_000
                        + -(rust_rem(sp_fid_sub(t), 1_000_000)));
                assert(sp_fid_n_am(l, u) == sp_fid_sub(u)
                    - rust_div(sp_fid_sub(u), 1_000_000)
                        * 1_000_000);
                assert(sp_fid_n_am(l, t) == sp_fid_sub(t)
                    - rust_div(sp_fid_sub(t), 1_000_000)
                        * 1_000_000);
            } else {
                assert(sp_fid_n_am(l, u) == sp_fid_sub(u));
                assert(sp_fid_n_am(l, t) == sp_fid_sub(t));
            }
        }
        assert(sp_fid_mc_secs(l, u) == -(sp_fid_mc_secs(l, t))) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Millisecond) {
                assert(sp_fid_mc_secs(l, u) == 0);
                assert(sp_fid_mc_secs(l, t) == 0);
            } else {
                assert(sp_fid_secs(u) == -(sp_fid_secs(t)));
            }
        }
        assert(sp_fid_mc(l, u) == -(sp_fid_mc(l, t))) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Microsecond) {
                assert(sp_fid_n_am(l, u)
                    == -(sp_fid_n_am(l, t)));
                assert(sp_fid_mc_secs(l, u)
                    == -(sp_fid_mc_secs(l, t)));
                lemma_trunc_uniqueness(sp_fid_n_am(l, u), 1_000,
                    -(rust_div(sp_fid_n_am(l, t), 1_000)),
                    -(rust_rem(sp_fid_n_am(l, t), 1_000)));
            }
        }
        assert(sp_fid_nn_secs(l, u) == -(sp_fid_nn_secs(l, t))) by {
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Microsecond) {
                assert(sp_fid_nn_secs(l, u) == 0);
                assert(sp_fid_nn_secs(l, t) == 0);
            } else {
                assert(sp_fid_secs(u) == -(sp_fid_secs(t)));
            }
        }
        assert(sp_fid_nn(l, u) == -(sp_fid_nn(l, t))) by {
            assert(sp_fid_nn_secs(l, u)
                == -(sp_fid_nn_secs(l, t)));
            if sp_unit_rank(l)
                >= sp_unit_rank(Unit::Microsecond) {
                assert(sp_fid_n_am(l, u)
                    == -(sp_fid_n_am(l, t)));
                assert(sp_fid_nn_nanos(l, u) == sp_fid_n_am(l, u)
                    - rust_div(sp_fid_n_am(l, u), 1_000) * 1_000);
                assert(sp_fid_nn_nanos(l, t) == sp_fid_n_am(l, t)
                    - rust_div(sp_fid_n_am(l, t), 1_000) * 1_000);
            } else {
                assert(sp_fid_nn_nanos(l, u)
                    == sp_fid_n_am(l, u));
                assert(sp_fid_nn_nanos(l, t)
                    == sp_fid_n_am(l, t));
            }
        }
        // u > 0 arm now carries the nonneg personalities.
        if u > 0 {
            // (reuse of the positive arm's content over u; the
            // negation equations above transfer it to t)
            assert(sp_fid_secs(u) >= 0) by {
                let q = rust_div(u, S_NANOS_PER_SEC());
                let r = rust_rem(u, S_NANOS_PER_SEC());
                lemma_fundamental_div_mod(u, S_NANOS_PER_SEC());
                assert(u == q * S_NANOS_PER_SEC() + r);
                assert(r == u % S_NANOS_PER_SEC());
                assert(0 <= r);
                if q < 0 {
                    assert(u < 0);
                }
            }
            assert(sp_fid_sub(u) >= 0) by {
                assert(sp_fid_sub(u)
                    == u - sp_fid_secs(u) * S_NANOS_PER_SEC());
            }
        } else {
            // t < 0 gives u > 0 always here; u == 0 impossible.
            assert(u > 0);
        }
        // Transfer through the negation equations.
        assert(sp_fid_secs(t) == -(sp_fid_secs(u)));
        assert(sp_fid_sub(t) == -(sp_fid_sub(u)));
        let rwu: int = sp_fid_r_w(l, u);
        if l is Week {
            assert(sp_fid_w(l, u) >= 0) by {
                let q = rust_div(sp_fid_secs(u), S_CIVIL_WEEK_SECS());
                let r = rust_rem(sp_fid_secs(u), S_CIVIL_WEEK_SECS());
                lemma_fundamental_div_mod(sp_fid_secs(u),
                    S_CIVIL_WEEK_SECS());
                assert(sp_fid_secs(u) == q * S_CIVIL_WEEK_SECS() + r);
                assert(r == sp_fid_secs(u) % S_CIVIL_WEEK_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(sp_fid_secs(u) < 0);
                }
            }
            assert(rwu >= 0) by {
                assert(rwu == sp_fid_secs(u)
                    - sp_fid_w(l, u) * S_CIVIL_WEEK_SECS());
            }
        }
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
            assert(sp_fid_d(l, u) >= 0) by {
                let q = rust_div(rwu, S_CIVIL_DAY_SECS());
                let r = rust_rem(rwu, S_CIVIL_DAY_SECS());
                lemma_fundamental_div_mod(rwu, S_CIVIL_DAY_SECS());
                assert(rwu == q * S_CIVIL_DAY_SECS() + r);
                assert(r == rwu % S_CIVIL_DAY_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(rwu < 0);
                }
            }
            assert(sp_fid_r_d(l, u) >= 0) by {
                assert(sp_fid_r_d(l, u) == rwu
                    - sp_fid_d(l, u) * S_CIVIL_DAY_SECS());
            }
        }
        let rdu: int = sp_fid_r_d(l, u);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
            assert(sp_fid_h(l, u) >= 0) by {
                let q = rust_div(rdu, S_HOUR_SECS());
                let r = rust_rem(rdu, S_HOUR_SECS());
                lemma_fundamental_div_mod(rdu, S_HOUR_SECS());
                assert(rdu == q * S_HOUR_SECS() + r);
                assert(r == rdu % S_HOUR_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(rdu < 0);
                }
            }
            assert(sp_fid_r_h(l, u) >= 0) by {
                assert(sp_fid_r_h(l, u) == rdu
                    - sp_fid_h(l, u) * S_HOUR_SECS());
            }
        }
        let rhu: int = sp_fid_r_h(l, u);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
            assert(sp_fid_m(l, u) >= 0) by {
                let q = rust_div(rhu, S_MIN_SECS());
                let r = rust_rem(rhu, S_MIN_SECS());
                lemma_fundamental_div_mod(rhu, S_MIN_SECS());
                assert(rhu == q * S_MIN_SECS() + r);
                assert(r == rhu % S_MIN_SECS());
                assert(0 <= r);
                if q < 0 {
                    assert(rhu < 0);
                }
            }
            assert(sp_fid_r_m(l, u) >= 0) by {
                assert(sp_fid_r_m(l, u) == rhu
                    - sp_fid_m(l, u) * S_MIN_SECS());
            }
        }
        assert(sp_fid_s(l, u) >= 0);
        assert(sp_fid_r_s(l, u) >= 0);
        assert(sp_fid_mc_secs(l, u) >= 0);
        assert(sp_fid_nn_secs(l, u) >= 0);
        let subu: int = sp_fid_sub(u);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Millisecond) {
            assert(sp_fid_mi(l, u) >= 0) by {
                let q = rust_div(subu, 1_000_000);
                let r = rust_rem(subu, 1_000_000);
                lemma_fundamental_div_mod(subu, 1_000_000);
                assert(subu == q * 1_000_000 + r);
                assert(r == subu % 1_000_000);
                assert(0 <= r);
                if q < 0 {
                    assert(subu < 0);
                }
            }
            assert(sp_fid_n_am(l, u) >= 0) by {
                assert(sp_fid_n_am(l, u) == subu
                    - rust_div(subu, 1_000_000) * 1_000_000);
            }
        } else {
            assert(sp_fid_sub(u) == sp_fid_n_am(l, u));
            assert(sp_fid_mi(l, u) == 0);
        }
        let namu: int = sp_fid_n_am(l, u);
        if sp_unit_rank(l) >= sp_unit_rank(Unit::Microsecond) {
            assert(sp_fid_mc(l, u) >= 0) by {
                let q = rust_div(namu, 1_000);
                let r = rust_rem(namu, 1_000);
                lemma_fundamental_div_mod(namu, 1_000);
                assert(namu == q * 1_000 + r);
                assert(r == namu % 1_000);
                assert(0 <= r);
                if q < 0 {
                    assert(namu < 0);
                }
            }
            assert(sp_fid_nn(l, u) >= 0) by {
                assert(sp_fid_nn(l, u)
                    == namu - rust_div(namu, 1_000) * 1_000);
            }
        }
        // Final transfer: each lane of t is the negated u lane.
        assert(sp_fid_secs(t) == -(sp_fid_secs(u)));
        assert(sp_fid_sub(t) == -(sp_fid_sub(u)));
        assert(sp_fid_w(l, t) == -(sp_fid_w(l, u)));
        assert(sp_fid_r_w(l, t) == -(sp_fid_r_w(l, u)));
        assert(sp_fid_d(l, t) == -(sp_fid_d(l, u)));
        assert(sp_fid_r_d(l, t) == -(sp_fid_r_d(l, u)));
        assert(sp_fid_h(l, t) == -(sp_fid_h(l, u)));
        assert(sp_fid_r_h(l, t) == -(sp_fid_r_h(l, u)));
        assert(sp_fid_m(l, t) == -(sp_fid_m(l, u)));
        assert(sp_fid_r_m(l, t) == -(sp_fid_r_m(l, u)));
        assert(sp_fid_s(l, t) == -(sp_fid_s(l, u)));
        assert(sp_fid_r_s(l, t) == -(sp_fid_r_s(l, u)));
        assert(sp_fid_mi(l, t) == -(sp_fid_mi(l, u)));
        assert(sp_fid_n_am(l, t) == -(sp_fid_n_am(l, u)));
        assert(sp_fid_mc(l, t) == -(sp_fid_mc(l, u)));
        assert(sp_fid_mc_secs(l, t) == -(sp_fid_mc_secs(l, u)));
        assert(sp_fid_nn_secs(l, t) == -(sp_fid_nn_secs(l, u)));
        assert(sp_fid_nn(l, t) == -(sp_fid_nn(l, u)));
    }
}

// ===========================================================================
// The infallible 32-bit SignedDuration constructors
// (signed_duration.rs:2321-2352). J4b cut them (no in-batch consumer);
// to_invariant_duration (span.rs:2446-2453) is their first consumer,
// so they live here next to it (jcore_signed_duration.rs is a closed
// panel file).
// ===========================================================================

/// Origin Rust: pub(crate) const fn from_civil_weeks32(weeks: i32)
///     (signed_duration.rs:2321-2329)
/// Upstream doc (signed_duration.rs:2316-2319):
///   Creates a signed duration from a 32-bit number of civil weeks.
///   (That is, every day is exactly 24 hours long and every week is 7
///   such days.)
///   This is infallible. It can never panic.
/// (Body: from_secs((weeks as i64) * DAYS_PER_CIVIL_WEEK *
/// HOURS_PER_CIVIL_DAY * MINS_PER_HOUR * SECS_PER_MINUTE); the
/// product constant is 604_800.)
pub exec fn sd_from_civil_weeks32(weeks: i32) -> (d: SignedDuration)
    ensures
        sd_inv(&d),
        (d.secs as int) == (weeks as int) * 604_800,
        d.nanos == 0,
        sd_total_nanos(&d)
            == (weeks as int) * 604_800 * 1_000_000_000,
{
    SignedDuration::from_secs((weeks as i64) * 604_800)
}

/// Origin Rust: pub(crate) const fn from_civil_days32(days: i32)
///     (signed_duration.rs:2336-2343)
/// Upstream doc (signed_duration.rs:2331-2334): the from_civil_weeks32
/// doc with day/days substituted (every day is exactly 24 hours long).
pub exec fn sd_from_civil_days32(days: i32) -> (d: SignedDuration)
    ensures
        sd_inv(&d),
        (d.secs as int) == (days as int) * 86_400,
        d.nanos == 0,
        sd_total_nanos(&d)
            == (days as int) * 86_400 * 1_000_000_000,
{
    SignedDuration::from_secs((days as i64) * 86_400)
}

/// Origin Rust: pub(crate) const fn from_hours32(hours: i32)
///     (signed_duration.rs:2348-2352)
/// Upstream doc (signed_duration.rs:2345-2347):
///   Like `SignedDuration::from_hours`, but for 32-bit integers
///   and thus infallible (including never panicking).
pub exec fn sd_from_hours32(hours: i32) -> (d: SignedDuration)
    ensures
        sd_inv(&d),
        (d.secs as int) == (hours as int) * 3_600,
        d.nanos == 0,
        sd_total_nanos(&d)
            == (hours as int) * 3_600 * 1_000_000_000,
{
    SignedDuration::from_secs((hours as i64) * 3_600)
}

// ===========================================================================
// The as_*_with_remainder family (signed_duration.rs:2362-2462, the
// J4b-deferred Span-interaction internals; every function the bucket
// chain consumes). Each returns the trunc quotient and the remainder
// duration upstream builds through new_unchecked (whose debug tier
// discharges as the sd_inv(&rem) postcondition).
// ===========================================================================

// The impl blocks re-open the J4b/J5 types cross-file (same crate:
// inherent impls are allowed wherever the type is in scope; the
// J5 as_nanos64-in-jcore_span precedent).

impl SignedDuration {

/// Origin Rust: pub(crate) fn as_civil_weeks_with_remainder(&self)
///     -> (i64, SignedDuration) (signed_duration.rs:2383-2394)
/// Upstream doc (signed_duration.rs:2379-2381):
///   Returns the number of whole civil weeks in this duration
///   (equivalent to `SignedDuration::as_civil_weeks`) along with a
///   duration equivalent to the fractional remainder.
pub exec fn sd_as_civil_weeks_with_remainder(&self)
    -> (r: (i64, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int) == rust_div(self.secs as int, 604_800),
        sd_inv(&r.1),
        (r.1.secs as int) == rust_rem(self.secs as int, 604_800),
        r.1.nanos == self.nanos,
        sd_total_nanos(&r.1)
            == sd_total_nanos(self)
                - (r.0 as int) * 604_800 * 1_000_000_000,
{
    // Upstream: weeks = self.as_civil_weeks() (signed_duration.rs
    // :2364-2370: as_secs() / 604_800; the J4b panel cut as_civil_
    // weeks, so the division is inlined verbatim).
    let weeks: i64 = self.as_secs() / 604_800;
    let secs: i64 = self.as_secs() % 604_800;
    proof {
        let q: int = rust_div(self.secs as int, 604_800);
        let r: int = rust_rem(self.secs as int, 604_800);
        lemma_fundamental_div_mod(self.secs as int, 604_800);
        assert((self.secs as int) == q * 604_800 + r);
        assert((weeks as int) == q);
        assert((secs as int) == r);
        // sd_inv of the remainder: the trunc remainder keeps the
        // dividend's sign, and sd_inv(self) couples the nanos sign.
        lemma_fid_lane_signs(Unit::Week, sd_total_nanos(self));
        if r > 0 {
            assert((self.nanos as int) >= 0);
        } else if r < 0 {
            assert((self.nanos as int) <= 0);
        } else {
            assert(secs == 0);
        }
    }
    let rem: SignedDuration =
        SignedDuration::new_unchecked(secs, self.nanos);
    (weeks, rem)
}

/// Origin Rust: pub(crate) fn as_civil_days_with_remainder(&self)
///     -> (i64, SignedDuration) (signed_duration.rs:2400-2408)
/// Upstream doc (signed_duration.rs:2396-2398): the weeks doc with
/// civil days substituted (as_civil_days, :2374-2377).
pub exec fn sd_as_civil_days_with_remainder(&self)
    -> (r: (i64, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int) == rust_div(self.secs as int, 86_400),
        sd_inv(&r.1),
        (r.1.secs as int) == rust_rem(self.secs as int, 86_400),
        r.1.nanos == self.nanos,
        sd_total_nanos(&r.1)
            == sd_total_nanos(self)
                - (r.0 as int) * 86_400 * 1_000_000_000,
{
    let days: i64 = self.as_secs() / 86_400;
    let secs: i64 = self.as_secs() % 86_400;
    proof {
        let q: int = rust_div(self.secs as int, 86_400);
        let r: int = rust_rem(self.secs as int, 86_400);
        lemma_fundamental_div_mod(self.secs as int, 86_400);
        assert((self.secs as int) == q * 86_400 + r);
        assert((days as int) == q);
        assert((secs as int) == r);
        lemma_fid_lane_signs(Unit::Week, sd_total_nanos(self));
        if r > 0 {
            assert((self.nanos as int) >= 0);
        } else if r < 0 {
            assert((self.nanos as int) <= 0);
        }
    }
    let rem: SignedDuration =
        SignedDuration::new_unchecked(secs, self.nanos);
    (days, rem)
}

/// Origin Rust: pub(crate) fn as_hours_with_remainder(&self)
///     -> (i64, SignedDuration) (signed_duration.rs:2414-2419)
/// Upstream doc (signed_duration.rs:2410-2412):
///   Returns the number of whole hours in this duration (equivalent to
///   `SignedDuration::as_hours`) along with a duration equivalent to
///   the fractional remainder.
pub exec fn sd_as_hours_with_remainder(&self)
    -> (r: (i64, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int) == rust_div(self.secs as int, 3_600),
        sd_inv(&r.1),
        (r.1.secs as int) == rust_rem(self.secs as int, 3_600),
        r.1.nanos == self.nanos,
        sd_total_nanos(&r.1)
            == sd_total_nanos(self)
                - (r.0 as int) * 3_600 * 1_000_000_000,
{
    let hours: i64 = self.as_secs() / 3_600;
    let secs: i64 = self.as_secs() % 3_600;
    proof {
        let q: int = rust_div(self.secs as int, 3_600);
        let r: int = rust_rem(self.secs as int, 3_600);
        lemma_fundamental_div_mod(self.secs as int, 3_600);
        assert((self.secs as int) == q * 3_600 + r);
        assert((hours as int) == q);
        assert((secs as int) == r);
        lemma_fid_lane_signs(Unit::Week, sd_total_nanos(self));
        if r > 0 {
            assert((self.nanos as int) >= 0);
        } else if r < 0 {
            assert((self.nanos as int) <= 0);
        }
    }
    let rem: SignedDuration =
        SignedDuration::new_unchecked(secs, self.nanos);
    (hours, rem)
}

/// Origin Rust: pub(crate) fn as_mins_with_remainder(&self)
///     -> (i64, SignedDuration) (signed_duration.rs:2425-2430)
/// Upstream doc (signed_duration.rs:2421-2423): the hours doc with
/// minutes substituted (as_mins).
pub exec fn sd_as_mins_with_remainder(&self)
    -> (r: (i64, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int) == rust_div(self.secs as int, 60),
        sd_inv(&r.1),
        (r.1.secs as int) == rust_rem(self.secs as int, 60),
        r.1.nanos == self.nanos,
        sd_total_nanos(&r.1)
            == sd_total_nanos(self)
                - (r.0 as int) * 60 * 1_000_000_000,
{
    let mins: i64 = self.as_secs() / 60;
    let secs: i64 = self.as_secs() % 60;
    proof {
        let q: int = rust_div(self.secs as int, 60);
        let r: int = rust_rem(self.secs as int, 60);
        lemma_fundamental_div_mod(self.secs as int, 60);
        assert((self.secs as int) == q * 60 + r);
        assert((mins as int) == q);
        assert((secs as int) == r);
        lemma_fid_lane_signs(Unit::Week, sd_total_nanos(self));
        if r > 0 {
            assert((self.nanos as int) >= 0);
        } else if r < 0 {
            assert((self.nanos as int) <= 0);
        }
    }
    let rem: SignedDuration =
        SignedDuration::new_unchecked(secs, self.nanos);
    (mins, rem)
}

/// Origin Rust: pub(crate) fn as_secs_with_remainder(&self)
///     -> (i64, SignedDuration) (signed_duration.rs:2436-2440)
/// Upstream doc (signed_duration.rs:2432-2434):
///   Returns the number of whole seconds in this duration (equivalent
///   to `SignedDuration::as_secs`) along with a duration equivalent to
///   the fractional remainder.
pub exec fn sd_as_secs_with_remainder(&self)
    -> (r: (i64, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int) == (self.secs as int),
        sd_inv(&r.1),
        r.1.secs == 0,
        r.1.nanos == self.nanos,
        sd_total_nanos(&r.1)
            == sd_total_nanos(self)
                - (r.0 as int) * 1_000_000_000,
{
    let secs: i64 = self.as_secs();
    let rem: SignedDuration =
        SignedDuration::new_unchecked(0, self.nanos);
    (secs, rem)
}

/// Origin Rust: pub(crate) fn as_millis_with_remainder(&self)
///     -> (i128, SignedDuration) (signed_duration.rs:2446-2451)
/// Upstream doc (signed_duration.rs:2442-2445):
///   Returns the number of whole milliseconds in this duration
///   (equivalent to `SignedDuration::as_millis`) along with a duration
///   equivalent to the fractional remainder.
pub exec fn sd_as_millis_with_remainder(&self)
    -> (r: (i128, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int)
            == (self.secs as int) * 1_000
                + rust_div(self.nanos as int, 1_000_000),
        sd_inv(&r.1),
        r.1.secs == 0,
        (r.1.nanos as int)
            == rust_rem(self.nanos as int, 1_000_000),
        sd_total_nanos(&r.1)
            == sd_total_nanos(self) - (r.0 as int) * 1_000_000,
{
    let millis: i128 = self.as_millis();
    let nanos: i32 = self.nanos % 1_000_000;
    proof {
        let q: int = rust_div(self.nanos as int, 1_000_000);
        let r: int = rust_rem(self.nanos as int, 1_000_000);
        lemma_fundamental_div_mod(self.nanos as int, 1_000_000);
        assert((self.nanos as int) == q * 1_000_000 + r);
        assert((nanos as int) == r);
        // fold: total(self) - millis*1e6 == r.
        assert(sd_total_nanos(self)
            - (millis as int) * 1_000_000
            == (self.nanos as int) - q * 1_000_000);
    }
    let rem: SignedDuration = SignedDuration::new_unchecked(0, nanos);
    (millis, rem)
}

/// Origin Rust: pub(crate) fn as_micros_with_remainder(&self)
///     -> (i128, SignedDuration) (signed_duration.rs:2457-2462)
/// Upstream doc (signed_duration.rs:2453-2456): the millis doc with
/// microseconds substituted (as_micros).
pub exec fn sd_as_micros_with_remainder(&self)
    -> (r: (i128, SignedDuration))
    requires
        sd_inv(self),
    ensures
        (r.0 as int)
            == (self.secs as int) * 1_000_000
                + rust_div(self.nanos as int, 1_000),
        sd_inv(&r.1),
        r.1.secs == 0,
        (r.1.nanos as int) == rust_rem(self.nanos as int, 1_000),
        sd_total_nanos(&r.1)
            == sd_total_nanos(self) - (r.0 as int) * 1_000,
{
    let micros: i128 = self.as_micros();
    let nanos: i32 = self.nanos % 1_000;
    proof {
        let q: int = rust_div(self.nanos as int, 1_000);
        let r: int = rust_rem(self.nanos as int, 1_000);
        lemma_fundamental_div_mod(self.nanos as int, 1_000);
        assert((self.nanos as int) == q * 1_000 + r);
        assert((nanos as int) == r);
        assert(sd_total_nanos(self)
            - (micros as int) * 1_000
            == (self.nanos as int) - q * 1_000);
    }
    let rem: SignedDuration = SignedDuration::new_unchecked(0, nanos);
    (micros, rem)
}

} // impl SignedDuration

// ===========================================================================
// Span::to_invariant_duration (span.rs:2416-2454) and its time-only
// twin (span.rs:2459-2490).
// ===========================================================================

/// Spec twin of the 8-term operator sum: the total nanoseconds the
/// invariant conversion of a span denotes. (The sign applies to the
/// whole span -- span.rs:122-130: "When a span is negative, then all
/// of its units are negative" -- which is exactly what the get_*()
/// sign multiplication in the upstream body applies termwise.)
pub open spec fn sp_inv_total_nanos(s: &Span) -> int {
    (sp_sign_val(s.sign)) * (
        (s.weeks as int) * 604_800 * 1_000_000_000
        + (s.days as int) * 86_400 * 1_000_000_000
        + (s.hours as int) * 3_600 * 1_000_000_000
        + (s.minutes as int) * 60 * 1_000_000_000
        + (s.seconds as int) * 1_000_000_000
        + (s.milliseconds as int) * 1_000_000
        + (s.microseconds as int) * 1_000
        + (s.nanoseconds as int)
    )
}

/// Origin Rust: pub(crate) fn to_invariant_duration(&self)
///     -> SignedDuration (span.rs:2416-2454)
/// Upstream doc (span.rs:2408-2414):
///   Converts the non-variable units of this `Span` to a
///   `SignedDuration`.
///   This includes days and weeks, even though they can be of varying
///   length during time zone transitions. If this applies, then
///   callers should set the days and weeks to `0` before calling this
///   routine.
///   All units above weeks are always ignored.
/// Upstream `_FITS_IN_U64` compile-time assert (span.rs:2422-2442,
/// comment :2417-2421):
///   This guarantees, at compile time, that a maximal invariant Span
///   (that is, all units are weeks or lower and all units are set to
///   their maximum values) will still balance out to a number of
///   seconds that fits into a `i64`.
/// -- materialized as lemma_fits_in_u64_ledger below. The 8-term body
/// sums through the Add operator (signed_duration.rs:2616-2618; the
/// upstream .expect panic text "overflow when adding signed
/// durations"); the excluder tier of sd_ops_add discharges from the
/// required sp_field_inv magnitudes -- see the in-body bound asserts.
impl Span {

pub exec fn sp_to_invariant_duration(&self) -> (r: SignedDuration)
    requires
        sp_field_inv(self),
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sp_inv_total_nanos(self),
        // Every invariant (week-or-lower) span sits deep inside the
        // SignedDuration range -- the _FITS_IN_U64 claim, restated as
        // a checked half-open bound for consumers.
        -(9_223_372_036_854_775_807int) * 1_000_000_000
            <= sd_total_nanos(&r),
        sd_total_nanos(&r)
            <= 9_223_372_036_854_775_807int * 1_000_000_000,
{
    // Upstream chain (span.rs:2446-2453):
    //   from_civil_weeks32(get_weeks()) + from_civil_days32(get_days())
    //   + from_hours32(get_hours()) + from_mins(get_minutes())
    //   + from_secs(get_seconds()) + from_millis(get_milliseconds())
    //   + from_micros(get_microseconds()) + from_nanos(get_nanos()).
    // get_*() applies the span-global sign (span.rs:1101-1303).
    let w: SignedDuration =
        sd_from_civil_weeks32(self.get_weeks());
    let d: SignedDuration =
        sd_from_civil_days32(self.get_days());
    let h: SignedDuration = sd_from_hours32(self.get_hours());
    // from_mins carries a genuine upstream panic face (signed_duration
    // .rs:783-793, "minutes overflowed an `i64` number of seconds
    // ..."); the magnitude tier keeps |get_minutes()| inside the
    // try_from_mins window, so the Some arm below is the only
    // reachable one (the panic-site fidelity note: this translation
    // states the no-panic domain as the checked bound assert).
    let mins_val: i64 = self.get_minutes();
    proof {
        assert((mins_val as int)
            == sp_sign_val(self.sign) * ((self.minutes as int)));
        assert(-(10_518_456_960int) <= (mins_val as int));
        assert((mins_val as int) <= 10_518_456_960);
    }
    let m: SignedDuration =
        crate::jcore_signed_duration::SignedDuration::from_mins(
            mins_val);
    let secs_val: i64 = self.get_seconds();
    let s: SignedDuration = SignedDuration::from_secs(secs_val);
    let mil_val: i64 = self.get_milliseconds();
    let mi: SignedDuration = SignedDuration::from_millis(mil_val);
    let mc_val: i64 = self.get_microseconds();
    let mc: SignedDuration = SignedDuration::from_micros(mc_val);
    let nn_val: i64 = self.get_nanoseconds();
    let nn: SignedDuration = SignedDuration::from_nanos(nn_val);
    proof {
        assert((secs_val as int)
            == sp_sign_val(self.sign) * ((self.seconds as int)));
        assert((mil_val as int)
            == sp_sign_val(self.sign)
                * ((self.milliseconds as int)));
        assert((mc_val as int)
            == sp_sign_val(self.sign)
                * ((self.microseconds as int)));
        assert((nn_val as int)
            == sp_sign_val(self.sign)
                * ((self.nanoseconds as int)));
    }
    proof {
        // Termwise magnitude ceilings (sp_field_inv), in whole
        // seconds; the partial sums stay far inside the sd_ops_add
        // excluder window.
        assert((self.weeks as int) * 604_800
            <= 1_043_497 * 604_800);
        assert(1_043_497 * 604_800 == 631_106_985_600);
        assert((self.days as int) * 86_400
            <= 7_304_484 * 86_400);
        assert(7_304_484 * 86_400 == 631_107_417_600);
        assert((self.hours as int) * 3_600
            <= 175_307_616 * 3_600);
        assert(175_307_616 * 3_600 == 631_107_417_600);
        assert((self.minutes as int) * 60
            <= 10_518_456_960 * 60);
        assert(10_518_456_960 * 60 == 631_107_417_600);
        assert((self.seconds as int) <= 631_107_417_600);
        assert((self.milliseconds as int) <= 631_107_417_600_000);
        assert((self.microseconds as int)
            <= 631_107_417_600_000_000);
        assert((self.nanoseconds as int)
            <= 9_223_372_036_854_775_807);
        assert((d.secs as int) <= 631_107_417_600);
        assert((h.secs as int) <= 631_107_417_600);
        assert((m.secs as int) <= 631_107_417_600);
        assert((s.secs as int) <= 631_107_417_600);
        assert((mi.secs as int) <= 631_107_417_600);
        assert((mc.secs as int) <= 631_107_417_600);
        assert((nn.secs as int) <= 9_223_372_036);
    }
    let a1: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&w, &d);
    let a2: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a1, &h);
    let a3: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a2, &m);
    let a4: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a3, &s);
    let a5: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a4, &mi);
    let a6: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a5, &mc);
    let a7: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a6, &nn);
    proof {
        let vx: int = sp_sign_val(self.sign);
        assert(sd_total_nanos(&w)
            == vx * ((self.weeks as int)) * 604_800 * 1_000_000_000);
        assert(sd_total_nanos(&d)
            == vx * ((self.days as int)) * 86_400 * 1_000_000_000);
        assert(sd_total_nanos(&h)
            == vx * ((self.hours as int)) * 3_600 * 1_000_000_000);
        assert(sd_total_nanos(&m)
            == vx * ((self.minutes as int)) * 60 * 1_000_000_000);
        assert(sd_total_nanos(&s)
            == vx * ((self.seconds as int)) * 1_000_000_000);
        assert(sd_total_nanos(&mi)
            == vx * ((self.milliseconds as int)) * 1_000_000);
        assert(sd_total_nanos(&mc)
            == vx * ((self.microseconds as int)) * 1_000);
        assert(sd_total_nanos(&nn)
            == vx * ((self.nanoseconds as int)));
    }
    a7
}

/// The `_FITS_IN_U64` compile-time assert's content (span.rs:2417-
/// 2442), as a verified int fact: the MAXIMAL invariant span (every
/// week-or-lower unit at its b::Span* maximum; years and months are
/// ignored by the conversion) balances to a number of whole seconds
/// well inside i64. The upstream const block's inequality, with the
/// upstream i128 casts spelled at int.
pub proof fn lemma_fits_in_u64_ledger()
    ensures
        9_223_372_036_854_775_807int
            > ((1_043_497int * 604_800)
                + (7_304_484int * 86_400)
                + (175_307_616int * 3_600)
                + (10_518_456_960int * 60)
                + 631_107_417_600int
                + (631_107_417_600_000int / 1_000)
                + (631_107_417_600_000_000int / 1_000_000)
                + (9_223_372_036_854_775_807int
                    / 1_000_000_000)),
{
    // Ground products fold (the wall-39 doctrine: shallow literals).
    assert(1_043_497 * 604_800 == 631_106_985_600);
    assert(7_304_484 * 86_400 == 631_107_417_600);
    assert(175_307_616 * 3_600 == 631_107_417_600);
    assert(10_518_456_960 * 60 == 631_107_417_600);
    // Six terms at the SpanSeconds::MAX grade plus the (smaller)
    // weeks term plus the nanos quotient:
    assert(631_107_417_600 * 6 + 631_106_985_600
        + 9_223_372_036 < 9_223_372_036_854_775_807);
}

/// Origin Rust: pub(crate) fn to_invariant_duration_time_only(&self)
///     -> SignedDuration (span.rs:2459-2490)
/// Upstream doc (span.rs:2456-2457):
///   Like `Span::to_invariant_duration`, except only considers units
///   of hours and lower. All bigger units are ignored.
/// (The upstream `_FITS_IN_U64` twin at span.rs:2465-2478 is carried
/// by lemma_fits_in_u64_time_only below.)
pub exec fn sp_to_invariant_duration_time_only(&self)
    -> (r: SignedDuration)
    requires
        sp_field_inv(self),
    ensures
        sd_inv(&r),
        sd_total_nanos(&r)
            == (sp_sign_val(self.sign)) * (
                (self.hours as int) * 3_600 * 1_000_000_000
                + (self.minutes as int) * 60 * 1_000_000_000
                + (self.seconds as int) * 1_000_000_000
                + (self.milliseconds as int) * 1_000_000
                + (self.microseconds as int) * 1_000
                + (self.nanoseconds as int)),
{
    let hrs_val_i32: i32 = self.get_hours();
    let h: SignedDuration = sd_from_hours32(hrs_val_i32);
    let mins_val: i64 = self.get_minutes();
    proof {
        assert((mins_val as int)
            == sp_sign_val(self.sign) * ((self.minutes as int)));
    }
    let m: SignedDuration =
        crate::jcore_signed_duration::SignedDuration::from_mins(
            mins_val);
    let secs_val: i64 = self.get_seconds();
    let s: SignedDuration = SignedDuration::from_secs(secs_val);
    let mil_val: i64 = self.get_milliseconds();
    let mi: SignedDuration = SignedDuration::from_millis(mil_val);
    let mc_val: i64 = self.get_microseconds();
    let mc: SignedDuration = SignedDuration::from_micros(mc_val);
    let nn_val: i64 = self.get_nanoseconds();
    let nn: SignedDuration = SignedDuration::from_nanos(nn_val);
    proof {
        assert((hrs_val_i32 as int)
            == sp_sign_val(self.sign) * ((self.hours as int)));
        assert((secs_val as int)
            == sp_sign_val(self.sign) * ((self.seconds as int)));
        assert((mil_val as int)
            == sp_sign_val(self.sign)
                * ((self.milliseconds as int)));
        assert((mc_val as int)
            == sp_sign_val(self.sign)
                * ((self.microseconds as int)));
        assert((nn_val as int)
            == sp_sign_val(self.sign)
                * ((self.nanoseconds as int)));
    }
    let a1: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&h, &m);
    let a2: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a1, &s);
    let a3: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a2, &mi);
    let a4: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a3, &mc);
    let a5: SignedDuration =
        crate::jcore_signed_duration::sd_ops_add(&a4, &nn);
    proof {
        let vx: int = sp_sign_val(self.sign);
        assert(sd_total_nanos(&h)
            == vx * ((self.hours as int)) * 3_600 * 1_000_000_000);
        assert(sd_total_nanos(&m)
            == vx * ((self.minutes as int)) * 60 * 1_000_000_000);
        assert(sd_total_nanos(&s)
            == vx * ((self.seconds as int)) * 1_000_000_000);
        assert(sd_total_nanos(&mi)
            == vx * ((self.milliseconds as int)) * 1_000_000);
        assert(sd_total_nanos(&mc)
            == vx * ((self.microseconds as int)) * 1_000);
        assert(sd_total_nanos(&nn)
            == vx * ((self.nanoseconds as int)));
    }
    a5
}

/// The time-only `_FITS_IN_U64` twin's content (span.rs:2460-2478).
pub proof fn lemma_fits_in_u64_time_only()
    ensures
        9_223_372_036_854_775_807int
            > ((175_307_616int * 3_600)
                + (10_518_456_960int * 60)
                + 631_107_417_600int
                + (631_107_417_600_000int / 1_000)
                + (631_107_417_600_000_000int / 1_000_000)
                + (9_223_372_036_854_775_807int
                    / 1_000_000_000)),
{
    assert(175_307_616 * 3_600 == 631_107_417_600);
    assert(10_518_456_960 * 60 == 631_107_417_600);
    assert(631_107_417_600 * 5 + 9_223_372_036
        < 9_223_372_036_854_775_807);
}

// ===========================================================================
// Span::from_invariant_duration (span.rs:2679-2731) -- the 8-stage
// bucketize chain. The contract carries: the sp tier stack, the
// per-field bucket pins (sign-applied magnitudes), the span-global
// sign pinned to the duration's sign, the years/months and bucket-
// dead fields structurally zero, the duration identity (the chain
// lemma), and the exact None-face `!fits`. This is the J4-1/J4-3
// canonical-form decision's first real consumer site (the batch
// instruction's item 3 clause): the Ok-face spec twin states the
// field tier + pins, not a global canonical form beyond the setters'
// own bookkeeping.
// ===========================================================================

/// Origin Rust: pub(crate) fn from_invariant_duration(
///     largest: Unit, mut dur: SignedDuration) -> Result<Span, Error>
///     (span.rs:2679-2731)
/// Upstream doc (span.rs:2666-2678):
///   Converts the given duration to a `Span` whose units do not
///   exceed `largest`.
///   Note that `largest` is capped at `Unit::Week`. Note though that
///   if any unit greater than `Unit::Week` is given, then it is
///   treated as `Unit::Day`. The only way to get weeks in the `Span`
///   returned is to specifically request `Unit::Week`.
///   And also note that days in this context are civil days. That is,
///   they are always 24 hours long. Callers needing to deal with
///   variable length days should do so outside of this routine and
///   should not provide a `largest` unit bigger than `Unit::Hour`.
/// (The Month/Year-as-Day clause is carried by the rank twins: ranks
///  8 and 9 satisfy every `>= Day..>= Second` gate but fail the
///  `matches!(largest, Unit::Week)` gate, exactly the upstream
///  behavior. The nanos stage runs unconditionally, span.rs:2724.)
pub exec fn sp_from_invariant_duration(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
    ensures
        sp_from_inv_face(
            largest,
            sd_total_nanos(dur0),
            &r,
        ),
{
    // The eight-arm dispatch: Year/Month/Day share the day-family
    // helper (exactly upstream's own `largest >= Unit::Day` note --
    // all three ranks satisfy every bucket gate except the
    // week-specific one); the helpers state the same sp_from_inv_face
    // contract, so this fn is a pure relay.
    match largest {
        Unit::Year | Unit::Month | Unit::Day =>
            sp_fid_arm_day_family(largest, dur0),
        Unit::Week => sp_fid_arm_week(largest, dur0),
        Unit::Hour => sp_fid_arm_hour(largest, dur0),
        Unit::Minute => sp_fid_arm_minute(largest, dur0),
        Unit::Second => sp_fid_arm_second(largest, dur0),
        Unit::Millisecond => sp_fid_arm_milli(largest, dur0),
        Unit::Microsecond => sp_fid_arm_micro(largest, dur0),
        Unit::Nanosecond => sp_fid_arm_nano(largest, dur0),
    }
}

} // impl Span

/// The shared result face of the from_invariant_duration bucket
/// chain: the sp tier stack + per-field bucket pins + the span-global
/// sign cases on Some, the exact `!fits` negation on None (every
/// per-arm helper below and the dispatch fn itself state this same
/// face, byte-equivalent, so their contracts compose exactly).
pub open spec fn sp_from_inv_face(
    l: Unit,
    tt: int,
    r: &Option<Span>,
) -> bool {
    ({
            let tt: int = tt;
            match r {
                Option::Some(sp) =>
                    sp_field_inv(&sp)
                        && sp_zero_sign_ok(&sp) && sp_flags_ok(&sp)
                        && ((tt > 0)
                            ==> ((sp.sign is Positive)
                                && (sp.years == 0) && (sp.months == 0)
                                && (sp.weeks as int)
                                    == sp_fid_w(l, tt)
                                && (sp.days as int)
                                    == sp_fid_d(l, tt)
                                && (sp.hours as int)
                                    == sp_fid_h(l, tt)
                                && (sp.minutes as int)
                                    == sp_fid_m(l, tt)
                                && (sp.seconds as int)
                                    == sp_fid_s(l, tt)
                                && (sp.milliseconds as int)
                                    == sp_fid_mi(l, tt)
                                && (sp.microseconds as int)
                                    == sp_fid_mc(l, tt)
                                && (sp.nanoseconds as int)
                                    == sp_fid_nn(l, tt)))
                        && ((tt < 0)
                            ==> ((sp.sign is Negative)
                                && (sp.years == 0) && (sp.months == 0)
                                && (sp.weeks as int)
                                    == 0 - sp_fid_w(l, tt)
                                && (sp.days as int)
                                    == 0 - sp_fid_d(l, tt)
                                && (sp.hours as int)
                                    == 0 - sp_fid_h(l, tt)
                                && (sp.minutes as int)
                                    == 0 - sp_fid_m(l, tt)
                                && (sp.seconds as int)
                                    == 0 - sp_fid_s(l, tt)
                                && (sp.milliseconds as int)
                                    == 0 - sp_fid_mi(l, tt)
                                && (sp.microseconds as int)
                                    == 0 - sp_fid_mc(l, tt)
                                && (sp.nanoseconds as int)
                                    == 0 - sp_fid_nn(l, tt)))
                        && ((tt == 0)
                            ==> ((sp.sign is Zero)
                                && sp.years == 0 && sp.months == 0
                                && sp.weeks == 0 && sp.days == 0
                                && sp.hours == 0 && sp.minutes == 0
                                && sp.seconds == 0
                                && sp.milliseconds == 0
                                && sp.microseconds == 0
                                && sp.nanoseconds == 0))
                        && sp_inv_total_nanos(&sp) == tt,
                Option::None => !sp_fid_fits(l, tt),
            }
        })
}

/// Translation-only per-arm bucket-runner (the `Unit::Year | Unit::Month | Unit::Day` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_day_family(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        (largest is Year) || (largest is Month) || (largest is Day),
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 2: days (span.rs:2690-2694) ----
    let stage2 = dur.sd_as_civil_days_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage2.0 as int) == sp_fid_d(largest, tt)) by {
            if matches!(largest, Unit::Week) {
                assert((dur.secs as int)
                    == sp_fid_r_w(largest, tt));
            } else {
                assert((dur.secs as int) == sp_fid_secs(tt));
            }
        }
        assert((stage2.1.secs as int)
            == sp_fid_r_d(largest, tt));
        assert((stage2.1.nanos as int) == sp_fid_sub(tt));
    }
    match span.try_days(stage2.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage2.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage2.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage2.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.days) as int == (stage2.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.days) as int == 0 - (stage2.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.days == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage2.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage2.0 as int)
                    == sp_fid_d(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage2.1;
// ---- stage 3: hours (span.rs:2695-2699) ----
    let stage3 = dur.sd_as_hours_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage3.0 as int) == sp_fid_h(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Day) {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            } else if matches!(largest, Unit::Week) {
                // unreachable: a Week largest always satisfies
                // the Day gate; kept for spec totality.
                assert(false);
            } else {
                assert((dur.secs as int) == sp_fid_secs(tt));
            }
        }
        assert((stage3.1.secs as int)
            == sp_fid_r_h(largest, tt));
    }
    match span.try_hours(stage3.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage3.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage3.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage3.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.hours) as int == (stage3.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.hours) as int == 0 - (stage3.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.hours == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage3.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage3.0 as int)
                    == sp_fid_h(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage3.1;
// ---- stage 4: minutes (span.rs:2700-2704) ----
    let stage4 = dur.sd_as_mins_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage4.0 as int) == sp_fid_m(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
        assert((stage4.1.secs as int)
            == sp_fid_r_m(largest, tt));
    }
    match span.try_minutes(stage4.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage4.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage4.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.minutes) as int == (stage4.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.minutes) as int == 0 - (stage4.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.minutes == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage4.0 as int)
                    == sp_fid_m(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage4.1;
// ---- stage 5: seconds (span.rs:2705-2709) ----
    let stage5 = dur.sd_as_secs_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage5.0 as int) == sp_fid_s(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Minute) {
                assert((dur.secs as int)
                    == sp_fid_r_m(largest, tt));
            } else if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
    }
    match span.try_seconds(stage5.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage5.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage5.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.seconds) as int == (stage5.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.seconds) as int == 0 - (stage5.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.seconds == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage5.0 as int)
                    == sp_fid_s(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage5.1;
// ---- stage 6: millis (span.rs:2710-2716): the i64::try_from
// (span.rs:2712-2713) spells as a range gate; its failure
// implies the b::SpanMilliseconds conjunct of fits fails (the
// range lies strictly inside i64). ----
    let stage6 = dur.sd_as_millis_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage6.0 as int) == sp_fid_mi(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_r_s(largest, tt));
            assert((dur.nanos as int) == sp_fid_sub(tt));
        }
        assert((stage6.1.secs as int)
            == sp_fid_mc_secs(largest, tt));
        assert((stage6.1.nanos as int)
            == sp_fid_n_am(largest, tt));
    }
    let wide: i128 = stage6.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_milliseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.milliseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.milliseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.milliseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mi(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                        // the Sub millisecond range sits strictly
                        // inside the i64 range, so a gate failure
                        // also violates fits:
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000int)
                    <= sp_fid_mi(largest, tt)
                    && sp_fid_mi(largest, tt)
                        <= 631_107_417_600_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage6.1;
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Week` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_week(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Week,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 1: weeks (span.rs:2685-2689) ----
    let stage1 = dur.sd_as_civil_weeks_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage1.0 as int)
            == sp_fid_w(largest, tt));
        assert((dur.secs as int) == sp_fid_secs(tt));
        assert((stage1.1.secs as int)
            == sp_fid_r_w(largest, tt));
        assert((stage1.1.nanos as int) == sp_fid_sub(tt));
    }
    match span.try_weeks(stage1.0) {
        Option::Some(s2) => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                if tt > 0 {
                    assert((stage1.0 as int)
                        == sp_fid_w(largest, tt));
                    assert((stage1.0 as int) >= 0);
                    assert(span.sign is Zero);
                    assert(s2.sign is Positive
                        || s2.sign is Zero);
                    assert((s2.weeks as int)
                        == (stage1.0 as int));
                } else if tt < 0 {
                    assert((stage1.0 as int)
                        == sp_fid_w(largest, tt));
                    assert((stage1.0 as int) <= 0);
                    assert(span.sign is Zero);
                    if stage1.0 < 0 {
                        assert(s2.sign is Negative);
                    } else {
                        assert(s2.sign is Zero);
                    }
                    assert((s2.weeks as int)
                        == 0 - (stage1.0 as int));
                } else {
                    assert(sp_fid_w(largest, 0) == 0);
                    assert((stage1.0 as int) == 0);
                    assert(span.sign is Zero);
                    assert(s2.sign is Zero);
                    assert(s2.weeks == 0);
                }
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage1.0 as int)
                    == sp_fid_w(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage1.1;
// ---- stage 2: days (span.rs:2690-2694) ----
    let stage2 = dur.sd_as_civil_days_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage2.0 as int) == sp_fid_d(largest, tt)) by {
            if matches!(largest, Unit::Week) {
                assert((dur.secs as int)
                    == sp_fid_r_w(largest, tt));
            } else {
                assert((dur.secs as int) == sp_fid_secs(tt));
            }
        }
        assert((stage2.1.secs as int)
            == sp_fid_r_d(largest, tt));
        assert((stage2.1.nanos as int) == sp_fid_sub(tt));
    }
    match span.try_days(stage2.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage2.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage2.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage2.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.days) as int == (stage2.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.days) as int == 0 - (stage2.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.days == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage2.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage2.0 as int)
                    == sp_fid_d(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage2.1;
// ---- stage 3: hours (span.rs:2695-2699) ----
    let stage3 = dur.sd_as_hours_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage3.0 as int) == sp_fid_h(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Day) {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            } else if matches!(largest, Unit::Week) {
                // unreachable: a Week largest always satisfies
                // the Day gate; kept for spec totality.
                assert(false);
            } else {
                assert((dur.secs as int) == sp_fid_secs(tt));
            }
        }
        assert((stage3.1.secs as int)
            == sp_fid_r_h(largest, tt));
    }
    match span.try_hours(stage3.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage3.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage3.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage3.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.hours) as int == (stage3.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.hours) as int == 0 - (stage3.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.hours == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage3.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage3.0 as int)
                    == sp_fid_h(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage3.1;
// ---- stage 4: minutes (span.rs:2700-2704) ----
    let stage4 = dur.sd_as_mins_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage4.0 as int) == sp_fid_m(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
        assert((stage4.1.secs as int)
            == sp_fid_r_m(largest, tt));
    }
    match span.try_minutes(stage4.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage4.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage4.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.minutes) as int == (stage4.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.minutes) as int == 0 - (stage4.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.minutes == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage4.0 as int)
                    == sp_fid_m(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage4.1;
// ---- stage 5: seconds (span.rs:2705-2709) ----
    let stage5 = dur.sd_as_secs_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage5.0 as int) == sp_fid_s(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Minute) {
                assert((dur.secs as int)
                    == sp_fid_r_m(largest, tt));
            } else if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
    }
    match span.try_seconds(stage5.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage5.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage5.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.seconds) as int == (stage5.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.seconds) as int == 0 - (stage5.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.seconds == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage5.0 as int)
                    == sp_fid_s(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage5.1;
// ---- stage 6: millis (span.rs:2710-2716): the i64::try_from
// (span.rs:2712-2713) spells as a range gate; its failure
// implies the b::SpanMilliseconds conjunct of fits fails (the
// range lies strictly inside i64). ----
    let stage6 = dur.sd_as_millis_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage6.0 as int) == sp_fid_mi(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_r_s(largest, tt));
            assert((dur.nanos as int) == sp_fid_sub(tt));
        }
        assert((stage6.1.secs as int)
            == sp_fid_mc_secs(largest, tt));
        assert((stage6.1.nanos as int)
            == sp_fid_n_am(largest, tt));
    }
    let wide: i128 = stage6.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_milliseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.milliseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.milliseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.milliseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mi(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                        // the Sub millisecond range sits strictly
                        // inside the i64 range, so a gate failure
                        // also violates fits:
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000int)
                    <= sp_fid_mi(largest, tt)
                    && sp_fid_mi(largest, tt)
                        <= 631_107_417_600_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage6.1;
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Hour` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_hour(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Hour,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 3: hours (span.rs:2695-2699) ----
    let stage3 = dur.sd_as_hours_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage3.0 as int) == sp_fid_h(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Day) {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            } else if matches!(largest, Unit::Week) {
                // unreachable: a Week largest always satisfies
                // the Day gate; kept for spec totality.
                assert(false);
            } else {
                assert((dur.secs as int) == sp_fid_secs(tt));
            }
        }
        assert((stage3.1.secs as int)
            == sp_fid_r_h(largest, tt));
    }
    match span.try_hours(stage3.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage3.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage3.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage3.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.hours) as int == (stage3.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.hours) as int == 0 - (stage3.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.hours == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage3.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage3.0 as int)
                    == sp_fid_h(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage3.1;
// ---- stage 4: minutes (span.rs:2700-2704) ----
    let stage4 = dur.sd_as_mins_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage4.0 as int) == sp_fid_m(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
        assert((stage4.1.secs as int)
            == sp_fid_r_m(largest, tt));
    }
    match span.try_minutes(stage4.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage4.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage4.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.minutes) as int == (stage4.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.minutes) as int == 0 - (stage4.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.minutes == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage4.0 as int)
                    == sp_fid_m(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage4.1;
// ---- stage 5: seconds (span.rs:2705-2709) ----
    let stage5 = dur.sd_as_secs_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage5.0 as int) == sp_fid_s(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Minute) {
                assert((dur.secs as int)
                    == sp_fid_r_m(largest, tt));
            } else if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
    }
    match span.try_seconds(stage5.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage5.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage5.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.seconds) as int == (stage5.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.seconds) as int == 0 - (stage5.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.seconds == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage5.0 as int)
                    == sp_fid_s(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage5.1;
// ---- stage 6: millis (span.rs:2710-2716): the i64::try_from
// (span.rs:2712-2713) spells as a range gate; its failure
// implies the b::SpanMilliseconds conjunct of fits fails (the
// range lies strictly inside i64). ----
    let stage6 = dur.sd_as_millis_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage6.0 as int) == sp_fid_mi(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_r_s(largest, tt));
            assert((dur.nanos as int) == sp_fid_sub(tt));
        }
        assert((stage6.1.secs as int)
            == sp_fid_mc_secs(largest, tt));
        assert((stage6.1.nanos as int)
            == sp_fid_n_am(largest, tt));
    }
    let wide: i128 = stage6.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_milliseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.milliseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.milliseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.milliseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mi(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                        // the Sub millisecond range sits strictly
                        // inside the i64 range, so a gate failure
                        // also violates fits:
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000int)
                    <= sp_fid_mi(largest, tt)
                    && sp_fid_mi(largest, tt)
                        <= 631_107_417_600_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage6.1;
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Minute` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_minute(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Minute,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 4: minutes (span.rs:2700-2704) ----
    let stage4 = dur.sd_as_mins_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage4.0 as int) == sp_fid_m(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
        assert((stage4.1.secs as int)
            == sp_fid_r_m(largest, tt));
    }
    match span.try_minutes(stage4.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage4.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage4.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.minutes) as int == (stage4.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.minutes) as int == 0 - (stage4.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.minutes == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage4.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage4.0 as int)
                    == sp_fid_m(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage4.1;
// ---- stage 5: seconds (span.rs:2705-2709) ----
    let stage5 = dur.sd_as_secs_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage5.0 as int) == sp_fid_s(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Minute) {
                assert((dur.secs as int)
                    == sp_fid_r_m(largest, tt));
            } else if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
    }
    match span.try_seconds(stage5.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage5.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage5.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.seconds) as int == (stage5.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.seconds) as int == 0 - (stage5.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.seconds == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage5.0 as int)
                    == sp_fid_s(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage5.1;
// ---- stage 6: millis (span.rs:2710-2716): the i64::try_from
// (span.rs:2712-2713) spells as a range gate; its failure
// implies the b::SpanMilliseconds conjunct of fits fails (the
// range lies strictly inside i64). ----
    let stage6 = dur.sd_as_millis_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage6.0 as int) == sp_fid_mi(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_r_s(largest, tt));
            assert((dur.nanos as int) == sp_fid_sub(tt));
        }
        assert((stage6.1.secs as int)
            == sp_fid_mc_secs(largest, tt));
        assert((stage6.1.nanos as int)
            == sp_fid_n_am(largest, tt));
    }
    let wide: i128 = stage6.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_milliseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.milliseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.milliseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.milliseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mi(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                        // the Sub millisecond range sits strictly
                        // inside the i64 range, so a gate failure
                        // also violates fits:
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000int)
                    <= sp_fid_mi(largest, tt)
                    && sp_fid_mi(largest, tt)
                        <= 631_107_417_600_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage6.1;
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Second` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_second(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Second,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 5: seconds (span.rs:2705-2709) ----
    let stage5 = dur.sd_as_secs_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage5.0 as int) == sp_fid_s(largest, tt)) by {
            if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Minute) {
                assert((dur.secs as int)
                    == sp_fid_r_m(largest, tt));
            } else if sp_unit_rank(largest)
                >= sp_unit_rank(Unit::Hour) {
                assert((dur.secs as int)
                    == sp_fid_r_h(largest, tt));
            } else {
                assert((dur.secs as int)
                    == sp_fid_r_d(largest, tt));
            }
        }
    }
    match span.try_seconds(stage5.0) {
        Option::Some(s2) => {
            proof {
                // Conditional (lazy) sign/magnitude facts -- the eager
                // three-way if-blocks multiplied the end-of-body query
                // into 10-unit x 8-stage case paths; implications keep
                // the query DAG branch-free (the lane facts ride the
                // lemma_fid_lane_signs call hoisted at the fn top).
                assert((sd_total_nanos(dur0) > 0) ==> ((stage5.0 as int) >= 0));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 as int) <= 0));
                assert((sd_total_nanos(dur0) == 0) ==> (stage5.0 == 0));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.seconds) as int == (stage5.0 as int));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.seconds) as int == 0 - (stage5.0 as int));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.seconds == 0));
                assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                    || span.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                assert((sd_total_nanos(dur0) > 0)
                    ==> (s2.sign is Positive || s2.sign is Zero));
                assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                assert((sd_total_nanos(dur0) < 0) ==> ((stage5.0 < 0)
                    ==> (s2.sign is Negative)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> ((span.sign is Negative || span.sign is Zero)));
                assert((sd_total_nanos(dur0) < 0)
                    ==> (s2.sign is Negative || s2.sign is Zero));
            }
            span = s2;
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert((stage5.0 as int)
                    == sp_fid_s(largest, tt));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage5.1;
// ---- stage 6: millis (span.rs:2710-2716): the i64::try_from
// (span.rs:2712-2713) spells as a range gate; its failure
// implies the b::SpanMilliseconds conjunct of fits fails (the
// range lies strictly inside i64). ----
    let stage6 = dur.sd_as_millis_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage6.0 as int) == sp_fid_mi(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_r_s(largest, tt));
            assert((dur.nanos as int) == sp_fid_sub(tt));
        }
        assert((stage6.1.secs as int)
            == sp_fid_mc_secs(largest, tt));
        assert((stage6.1.nanos as int)
            == sp_fid_n_am(largest, tt));
    }
    let wide: i128 = stage6.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_milliseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.milliseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.milliseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.milliseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mi(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                        // the Sub millisecond range sits strictly
                        // inside the i64 range, so a gate failure
                        // also violates fits:
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000int)
                    <= sp_fid_mi(largest, tt)
                    && sp_fid_mi(largest, tt)
                        <= 631_107_417_600_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage6.1;
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Millisecond` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_milli(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Millisecond,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 6: millis (span.rs:2710-2716): the i64::try_from
// (span.rs:2712-2713) spells as a range gate; its failure
// implies the b::SpanMilliseconds conjunct of fits fails (the
// range lies strictly inside i64). ----
    let stage6 = dur.sd_as_millis_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage6.0 as int) == sp_fid_mi(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_r_s(largest, tt));
            assert((dur.nanos as int) == sp_fid_sub(tt));
        }
        assert((stage6.1.secs as int)
            == sp_fid_mc_secs(largest, tt));
        assert((stage6.1.nanos as int)
            == sp_fid_n_am(largest, tt));
    }
    let wide: i128 = stage6.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_milliseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.milliseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.milliseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.milliseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mi(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                        // the Sub millisecond range sits strictly
                        // inside the i64 range, so a gate failure
                        // also violates fits:
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000int)
                    <= sp_fid_mi(largest, tt)
                    && sp_fid_mi(largest, tt)
                        <= 631_107_417_600_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage6.1;
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    proof {
        // Exit invariants for the minimal lane-set arm (the week/
        // days/hours/minutes buckets are structural zeros here): the
        // granular asserts are kept as derivation stepping stones
        // (the J5 per-atomic-obligation bisect doctrine -- this arm's
        // postcondition query needs the final re-proof below).
        let tt: int = sd_total_nanos(dur0);
        assert(sp_field_inv(&span));
        assert(sp_zero_sign_ok(&span));
        assert(sp_flags_ok(&span));
        assert(span.years == 0);
        assert(span.months == 0);
        assert(span.weeks == 0);
        assert(span.days == 0);
        if tt > 0 {
            assert(span.sign is Positive);
            assert((span.weeks as int) == sp_fid_w(largest, tt));
        } else if tt < 0 {
            assert(span.sign is Negative);
        } else {
            assert(span.sign is Zero);
        }
        assert(sp_inv_total_nanos(&span) == tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Microsecond` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_micro(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Microsecond,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 7: micros (span.rs:2717-2723) ----
    let stage7 = dur.sd_as_micros_with_remainder();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert((stage7.0 as int) == sp_fid_mc(largest, tt)) by {
            assert((dur.secs as int)
                == sp_fid_mc_secs(largest, tt));
            assert((dur.nanos as int)
                == sp_fid_n_am(largest, tt));
        }
        assert((stage7.1.secs as int)
            == sp_fid_nn_secs(largest, tt));
        assert((stage7.1.nanos as int)
            == sp_fid_nn_nanos(largest, tt));
    }
    let wide: i128 = stage7.0;
    let gate: Option<i64> = if wide
        > 9_223_372_036_854_775_807i128 || wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_microseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.microseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.microseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.microseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_mc(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(631_107_417_600_000_000int)
                    <= sp_fid_mc(largest, tt)
                    && sp_fid_mc(largest, tt)
                        <= 631_107_417_600_000_000));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    dur = stage7.1;
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }
    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}


/// Translation-only per-arm bucket-runner (the `Unit::Nanosecond` arm of the
/// sp_from_invariant_duration stage chain; a separate fn so verus
/// checks each arm as its own obligation family -- the monolithic
/// body exceeded the rlimit wall on its end-of-function query even
/// with a postcondition of true, and the 10-arm in-body match alone
/// did not split the query).
pub(crate) exec fn sp_fid_arm_nano(
    largest: Unit,
    dur0: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sd_inv(dur0),
        largest is Nanosecond,
    ensures
        sp_from_inv_face(largest, sd_total_nanos(dur0), &r),
{
    proof { lemma_fid_lane_signs(largest, sd_total_nanos(dur0)); }
    let mut span: Span = Span::new();
    let mut dur: SignedDuration = SignedDuration {
        secs: dur0.secs,
        nanos: dur0.nanos,
    };
    proof {
        lemma_sd_canonical_secs(&dur);
        assert(sd_total_nanos(&dur) == sd_total_nanos(dur0));
    }
// ---- stage 8: nanos (span.rs:2724-2728; the gate
// `largest >= Unit::Nanosecond` is upstream's own tautology) ----
    let nn_wide: i128 = dur.as_nanos();
    proof {
        let tt: int = sd_total_nanos(dur0);
        assert(sd_total_nanos(&dur)
            == sp_fid_nn_secs(largest, tt)
                * S_NANOS_PER_SEC()
            + sp_fid_nn_nanos(largest, tt));
        assert((nn_wide as int)
            == sp_fid_nn(largest, tt));
    }

    let gate: Option<i64> = if nn_wide
        > 9_223_372_036_854_775_807i128 || nn_wide
        < -9_223_372_036_854_775_808i128 {
        Option::None
    } else {
        Option::Some(nn_wide as i64)
    };
    match gate {
        Option::Some(n) => {
            match span.try_nanoseconds(n) {
                Option::Some(s2) => {
                    proof {
                        // Conditional (lazy) sign/magnitude facts -- the eager
                        // three-way if-blocks multiplied the end-of-body query
                        // into 10-unit x 8-stage case paths; implications keep
                        // the query DAG branch-free (the lane facts ride the
                        // lemma_fid_lane_signs call hoisted at the fn top).
                        assert((sd_total_nanos(dur0) > 0) ==> ((n as int) >= 0));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n as int) <= 0));
                        assert((sd_total_nanos(dur0) == 0) ==> (n == 0));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.nanoseconds) as int == (n as int));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.nanoseconds) as int == 0 - (n as int));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.nanoseconds == 0));
                        assert((sd_total_nanos(dur0) > 0) ==> (span.sign is Positive
                            || span.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (span.sign is Zero));
                        assert((sd_total_nanos(dur0) > 0)
                            ==> (s2.sign is Positive || s2.sign is Zero));
                        assert((sd_total_nanos(dur0) == 0) ==> (s2.sign is Zero));
                        assert((sd_total_nanos(dur0) < 0) ==> ((n < 0)
                            ==> (s2.sign is Negative)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> ((span.sign is Negative || span.sign is Zero)));
                        assert((sd_total_nanos(dur0) < 0)
                            ==> (s2.sign is Negative || s2.sign is Zero));
                    }
                    span = s2;
                }
                Option::None => {
                    proof {
                        let tt: int = sd_total_nanos(dur0);
                        assert((n as int)
                            == sp_fid_nn(largest, tt));
                        assert(!sp_fid_fits(largest, tt));
                    }
                    return Option::None;
                }
            }
        }
        Option::None => {
            proof {
                let tt: int = sd_total_nanos(dur0);
                assert(!(-(9_223_372_036_854_775_807int)
                    <= sp_fid_nn(largest, tt)
                    && sp_fid_nn(largest, tt)
                        <= 9_223_372_036_854_775_807));
                assert(!sp_fid_fits(largest, tt));
            }
            return Option::None;
        }
    }
    proof {
        // Final sign + pin assembly (the single eager case split --
        // every stage Some-arm above contributed lazy conditional
        // facts, so this block is the only branching site in the
        // end-of-body query).
        let tt: int = sd_total_nanos(dur0);
        if tt > 0 {
            assert(span.sign is Positive || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) > 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) > 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) > 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) > 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) > 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) > 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) > 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) > 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) > 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) > 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) > 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) > 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) > 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) > 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) > 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) > 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            // sp_zero_sign_ok: a Zero sign would force sp_all_zero.
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
            // sign resolved; the stored magnitude pins of the stages
            // discharge the ensures' lane equalities.
        } else if tt < 0 {
            assert(span.sign is Negative || span.sign is Zero);
            assert(!sp_all_zero(&span)) by {
                if sp_all_zero(&span) {
                    if sp_fid_w(largest, tt) < 0 {
                        assert((span.weeks as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_w(largest, tt) < 0 || span.weeks as int == 0);
                    if sp_fid_d(largest, tt) < 0 {
                        assert((span.days as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_d(largest, tt) < 0 || span.days as int == 0);
                    if sp_fid_h(largest, tt) < 0 {
                        assert((span.hours as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_h(largest, tt) < 0 || span.hours as int == 0);
                    if sp_fid_m(largest, tt) < 0 {
                        assert((span.minutes as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_m(largest, tt) < 0 || span.minutes as int == 0);
                    if sp_fid_s(largest, tt) < 0 {
                        assert((span.seconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_s(largest, tt) < 0 || span.seconds as int == 0);
                    if sp_fid_mi(largest, tt) < 0 {
                        assert((span.milliseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mi(largest, tt) < 0 || span.milliseconds as int == 0);
                    if sp_fid_mc(largest, tt) < 0 {
                        assert((span.microseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_mc(largest, tt) < 0 || span.microseconds as int == 0);
                    if sp_fid_nn(largest, tt) < 0 {
                        assert((span.nanoseconds as int) != 0);
                        assert(!sp_all_zero(&span));
                        assert(false);
                    }
                    assert(sp_fid_nn(largest, tt) < 0 || span.nanoseconds as int == 0);
                    lemma_fid_identity(largest, tt);
                    assert(tt == 0);
                    assert(false);
                }
            }
            if span.sign is Zero {
                assert(sp_all_zero(&span));
                assert(false);
            }
        } else {
            // tt == 0: every stage ran with a zero value, so the span
            // stayed the zero span (the conditional sign facts chain
            // Zero through every executed setter's v == 0 arm).
            assert(span.sign is Zero);
            assert(sp_all_zero(&span));
        }
        lemma_fid_identity(largest, tt);
    }
    Option::Some(span)
}

// ===========================================================================
// The checked_add invariant chain (span.rs:1814-1879) and the public
// entry faces (span.rs:1758-1764, :1871-1879, the relative==None
// paths; see the file-head prune ledger for the SpanArithmetic
// config surface).
// ===========================================================================

/// Translation-only INFORMATIVE re-derivation of
/// `SignedDuration::checked_add` (signed_duration.rs:1037-1092, whose
/// J4b transcription -- jcore_signed_duration.rs:1339-1465 -- states
/// the full Some-face but leaves the None-face at `true`; the J4b
/// file is a closed panel, so the body is mirrored here with the
/// REGARD-NOTING upgrade the upstream structure carries: None happens
/// precisely when the summed total falls outside the SignedDuration
/// range, which is what the b::SignedDurationSeconds error of
/// span.rs:1836-1838 reports).
pub(crate) exec fn sd_checked_add_info(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: Option<SignedDuration>)
    requires
        sd_inv(a),
        sd_inv(b),
    ensures
        match r {
            Option::Some(d) => sd_inv(&d)
                && sd_total_nanos(&d)
                    == sd_total_nanos(a) + sd_total_nanos(b),
            Option::None =>
                !(sd_min_total_nanos()
                    <= sd_total_nanos(a) + sd_total_nanos(b)
                    && sd_total_nanos(a) + sd_total_nanos(b)
                        <= sd_max_total_nanos()),
        },
{
    // Body: the J4b transcription, branch for branch
    // (jcore_signed_duration.rs:1365-1464); every safety comment
    // cited there applies unchanged.
    let opt = a.secs.checked_add(b.secs);
    let mut secs: i64 = match opt {
        Option::Some(v) => v,
        Option::None => return Option::None,
    };
    let mut nanos: i32 = a.nanos + b.nanos;
    if nanos != 0 {
        if nanos >= NANOS_PER_SEC_I32() {
            nanos = nanos - NANOS_PER_SEC_I32();
            let opt2 = secs.checked_add(1);
            secs = match opt2 {
                Option::Some(v) => v,
                Option::None => return Option::None,
            };
        } else if nanos <= -NANOS_PER_SEC_I32() {
            nanos = nanos + NANOS_PER_SEC_I32();
            let opt2 = secs.checked_sub(1);
            secs = match opt2 {
                Option::Some(v) => v,
                Option::None => return Option::None,
            };
        }
        if secs != 0 && nanos != 0 && !((secs > 0) == (nanos > 0)) {
            if secs < 0 {
                proof {
                    assert((secs as int) < 0);
                    assert((nanos as int) > 0);
                }
                let secs_new: i64 = secs + 1;
                let nanos_new: i32 = nanos - NANOS_PER_SEC_I32();
                proof {
                    assert(-(999_999_999int) <= nanos_new as int);
                    assert((secs_new as int) * 1_000_000_000
                        + (nanos_new as int)
                        == (secs as int) * 1_000_000_000
                            + (nanos as int));
                    if secs_new < 0 {
                        assert(nanos_new < 0);
                    } else {
                        assert(secs_new == 0);
                    }
                }
                secs = secs_new;
                nanos = nanos_new;
            } else {
                proof {
                    assert((secs as int) > 0);
                    assert((nanos as int) < 0);
                }
                let secs_new: i64 = secs - 1;
                let nanos_new: i32 = nanos + NANOS_PER_SEC_I32();
                proof {
                    assert((nanos_new as int) <= 999_999_999);
                    assert((secs_new as int) * 1_000_000_000
                        + (nanos_new as int)
                        == (secs as int) * 1_000_000_000
                            + (nanos as int));
                    if secs_new > 0 {
                        assert(nanos_new > 0);
                    } else {
                        assert(secs_new == 0);
                    }
                }
                secs = secs_new;
                nanos = nanos_new;
            }
        }
    }
    proof {
        assert(sd_nanos_ok(nanos));
        if nanos != 0 && secs != 0 {
            if nanos > 0 {
                assert(secs > 0);
            } else {
                assert(nanos < 0);
                assert(secs < 0);
            }
        }
        assert((nanos as int) > -(1_000_000_000int));
        assert((nanos as int) < 1_000_000_000int);
    }
    Option::Some(SignedDuration::new_unchecked(secs, nanos))
}

/// The i32 nanos-per-second constant the mirrored body spells with.
pub(crate) exec fn NANOS_PER_SEC_I32() -> (r: i32)
    ensures
        r == 1_000_000_000i32,
{
    1_000_000_000
}


/// fits implies the total sits inside the SignedDuration range (so a
/// checked_add whose sd-replica fires None -- the summed total out of
/// the sd range -- can never have a fits-representable total; the
/// None faces below inherit the exact `!fits` negation through this
/// lemma's contrapositive). Ground-bounds mirror the sp_field_inv
/// magnitudes * unit factors.
pub proof fn lemma_fits_implies_sd_range(l: Unit, tt: int)
    requires
        sp_fid_fits(l, tt),
    ensures
        sd_min_total_nanos() <= tt && tt <= sd_max_total_nanos(),
{
    // |tt| <= sum |lane| * factor <= (7 grade-terms at 631_107_417_600
    // seconds) + (nanos at i64) -- the _FITS_IN_U64 ledger shape.
    assert(sp_fid_w(l, tt) * 604_800 >= -(631_106_985_600int));
    assert(sp_fid_d(l, tt) * 86_400 >= -(631_107_417_600int));
    assert(sp_fid_h(l, tt) * 3_600 >= -(631_107_417_600int));
    assert(sp_fid_m(l, tt) * 60 >= -(631_107_417_600int));
    assert(sp_fid_s(l, tt) >= -(631_107_417_600int));
    assert(sp_fid_mi(l, tt) * 1_000_000
        >= -(631_107_417_600_000_000_000int));
    assert(sp_fid_mc(l, tt) * 1_000
        >= -(631_107_417_600_000_000_000int));
    assert(sp_fid_nn(l, tt)
        >= -(9_223_372_036_854_775_807int));
    assert(sp_fid_w(l, tt) * 604_800 <= 631_106_985_600);
    assert(sp_fid_d(l, tt) * 86_400 <= 631_107_417_600);
    assert(sp_fid_h(l, tt) * 3_600 <= 631_107_417_600);
    assert(sp_fid_m(l, tt) * 60 <= 631_107_417_600);
    assert(sp_fid_s(l, tt) <= 631_107_417_600);
    assert(sp_fid_mi(l, tt) * 1_000_000
        <= 631_107_417_600_000_000_000);
    assert(sp_fid_mc(l, tt) * 1_000
        <= 631_107_417_600_000_000_000);
    assert(sp_fid_nn(l, tt) <= 9_223_372_036_854_775_807);
    lemma_fid_identity(l, tt);
    // Sum bound: 4*631_107_417_600 (w Grade smaller) + ... all terms:
    // grand bound: 4*6.31e11-grade + the weeks grade + the two
    // 6.31e20-grade subsecond products + the nanos i64 grade:
    assert(631_107_417_600int * 4 + 631_106_985_600
        + 631_107_417_600_000_000_000
        + 631_107_417_600_000_000_000
        + 9_223_372_036_854_775_807
        < 9_223_372_036_854_775_807_000_000_000);
    // The sd extremes in nanoseconds:
    assert(sd_min_total_nanos()
        == -(9_223_372_036_854_775_808int) * 1_000_000_000
            - 999_999_999);
    assert(sd_max_total_nanos()
        == 9_223_372_036_854_775_807int * 1_000_000_000
            + 999_999_999);
}

impl Span {

/// Origin Rust: fn checked_add_invariant_duration(
///     &self, unit: Unit, rhs_duration: SignedDuration) -> Result<Span, Error>
///     (span.rs:1829-1840)
/// Upstream body (span.rs:1834-1839):
///     assert!(unit <= Unit::Week);
///     let self_duration = self.to_invariant_duration();
///     let sum = self_duration.checked_add(rhs_duration)
///         .ok_or_else(|| b::SignedDurationSeconds::error())?;
///     Span::from_invariant_duration(unit, sum)
/// AUDIT DISPOSITION (the J5 notes' audit point; see
/// signed_duration span.rs:1836-1838): the
/// `b::SignedDurationSeconds::error()` ok_or_else arm adds NO range
/// check -- b::SignedDurationSeconds' range is the full i64 second
/// range (jiff src/util/b.rs:192 and the user-facing error text of
/// MAX.round(Unit::Hour), signed_duration.rs:2273-2276) -- it merely
/// re-labels SignedDuration::checked_add's own overflow, which IS
/// reachable through the checked_add(SignedDuration) route (rhs near
/// SignedDuration::MAX: summed seconds overflow i64) and is dead
/// code through the invariant-Span-only route (both span totals are
/// bounded by the _FITS_IN_U64 ledger far inside the sd range). The
/// informative replica above carries the exact None-face, so both
/// dispositions are machine-checked here.
/// (The assert! materializes as the rank requires below.)
pub exec fn sp_checked_add_invariant_duration(
    &self,
    unit: Unit,
    rhs: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sp_field_inv(self),
        sp_zero_sign_ok(self),
        sp_flags_ok(self),
        self.years == 0 && self.months == 0
            && self.weeks == 0 && self.days == 0,
        sd_inv(rhs),
        sp_unit_rank(unit) <= sp_unit_rank(Unit::Week),
    ensures
        sp_from_inv_face(
            unit,
            sp_inv_total_nanos(self) + sd_total_nanos(rhs),
            &r,
        ),
{
    let self_duration: SignedDuration =
        self.sp_to_invariant_duration();
    proof {
        assert(sd_total_nanos(&self_duration)
            == sp_inv_total_nanos(self));
    }
    let sum: Option<SignedDuration> =
        sd_checked_add_info(&self_duration, rhs);
    match sum {
        Option::Some(d2) => {
            Span::sp_from_invariant_duration(unit, &d2)
        }
        Option::None => {
            proof {
                let tt: int = sp_inv_total_nanos(self)
                    + sd_total_nanos(rhs);
                assert(!(sd_min_total_nanos() <= tt
                    && tt <= sd_max_total_nanos()));
                if sp_fid_fits(unit, tt) {
                    lemma_fits_implies_sd_range(unit, tt);
                    assert(false);
                }
                assert(!sp_fid_fits(unit, tt));
            }
            Option::None
        }
    }
}

/// Origin Rust: fn checked_add_invariant(
///     &self, unit: Unit, span: &Span) -> Result<Span, Error>
///     (span.rs:1818-1825)
/// Upstream doc (span.rs:1814-1816):
///   Like `checked_add`, but only applies for invariant units. That
///   is, when *both spans* whose non-zero units are all hours or
///   smaller (or weeks or smaller with the "days are 24 hours"
///   marker).
/// Upstream body: assert!(unit <= Unit::Week);
///   self.checked_add_invariant_duration(
///       unit, span.to_invariant_duration()).
pub(crate) exec fn sp_checked_add_invariant(
    &self,
    unit: Unit,
    span2: &Span,
) -> (r: Option<Span>)
    requires
        sp_field_inv(self),
        sp_zero_sign_ok(self),
        sp_flags_ok(self),
        self.years == 0 && self.months == 0
            && self.weeks == 0 && self.days == 0,
        sp_field_inv(span2),
        sp_zero_sign_ok(span2),
        sp_flags_ok(span2),
        span2.years == 0 && span2.months == 0
            && span2.weeks == 0 && span2.days == 0,
        sp_unit_rank(unit) <= sp_unit_rank(Unit::Week),
    ensures
        sp_from_inv_face(
            unit,
            sp_inv_total_nanos(self)
                + sp_inv_total_nanos(span2),
            &r,
        ),
{
    let d2: SignedDuration =
        span2.sp_to_invariant_duration();
    self.sp_checked_add_invariant_duration(unit, &d2)
}

/// Origin Rust: pub fn checked_add<'a, A: Into<SpanArithmetic<'a>>>(
///     &self, options: A) -> Result<Span, Error>
///     (span.rs:1758-1764; the doc block span.rs:1600-1611)
/// Upstream doc (span.rs:1600-1602):
///   The sum returned is automatically re-balanced so that the span
///   is not "bottom heavy."
/// Upstream doc (span.rs:1606-1611, # Errors):
///   This returns an error when adding the two spans would overflow
///   any individual field of a span. This will also return an error
///   if either of the spans have non-zero units of days or greater
///   and no relative reference time is provided.
/// (The second error clause is the relative==None gate: this
///  translation materializes exactly that path, so the "non-zero
///  units of days or greater" state is the requires. The SpanArithmetic
///  `From<Span>` arm + checked_add_span's relative==None branch,
///  span.rs:4204-4207 + :1779-1782 with requires_relative_date_err,
///  span.rs:6730-6739.)
pub exec fn sp_checked_add_span(
    &self,
    span2: &Span,
) -> (r: Option<Span>)
    requires
        sp_field_inv(self),
        sp_zero_sign_ok(self),
        sp_flags_ok(self),
        self.years == 0 && self.months == 0
            && self.weeks == 0 && self.days == 0,
        sp_field_inv(span2),
        sp_zero_sign_ok(span2),
        sp_flags_ok(span2),
        span2.years == 0 && span2.months == 0
            && span2.weeks == 0 && span2.days == 0,
    ensures
        sp_from_inv_face(
            sp_unit_max(
                sp_span_largest(self),
                sp_span_largest(span2),
            ),
            sp_inv_total_nanos(self)
                + sp_inv_total_nanos(span2),
            &r,
        ),
{
    // unit = span1.largest_unit().max(span2.largest_unit())
    // (span.rs:1773); the J5 largest_unit table + sp_flags_ok place
    // both values inside {Hour..Nanosecond} on the time-only domain.
    let u1: Unit = self.largest_unit();
    let u2: Unit = span2.largest_unit();
    proof {
        assert(u1 == sp_span_largest(self));
        assert(u2 == sp_span_largest(span2));
        assert(sp_unit_rank(u1) <= sp_unit_rank(Unit::Hour));
        assert(sp_unit_rank(u2) <= sp_unit_rank(Unit::Hour));
    }
    let u: Unit = sp_unit_max_exec(u1, u2);
    proof {
        assert(u == sp_unit_max(u1, u2));
        assert(u
            == sp_unit_max(
                sp_span_largest(self),
                sp_span_largest(span2),
            ));
    }
    self.sp_checked_add_invariant(u, span2)
}

/// Origin Rust: pub fn checked_add(SignedDuration) -- the
/// SpanArithmetic `From<SignedDuration>` arm feeding
/// checked_add_duration (span.rs:1790-1812 at relative == None):
///   unit = span1.largest_unit();
///   ... requires_relative_date_err(unit)?;
///   span1.checked_add_invariant_duration(unit, dur2).
pub exec fn sp_checked_add_duration(
    &self,
    dur2: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sp_field_inv(self),
        sp_zero_sign_ok(self),
        sp_flags_ok(self),
        self.years == 0 && self.months == 0
            && self.weeks == 0 && self.days == 0,
        sd_inv(dur2),
    ensures
        sp_from_inv_face(
            sp_span_largest(self),
            sp_inv_total_nanos(self) + sd_total_nanos(dur2),
            &r,
        ),
{
    let u: Unit = self.largest_unit();
    proof {
        assert(u == sp_span_largest(self));
        assert(sp_unit_rank(u) <= sp_unit_rank(Unit::Week));
    }
    self.sp_checked_add_invariant_duration(u, dur2)
}

/// Origin Rust: pub fn checked_sub<'a, A: Into<SpanArithmetic<'a>>>(
///     &self, options: A) -> Result<Span, Error>
///     (span.rs:1871-1879)
/// Upstream doc (span.rs:1842-1847):
///   This routine is identical to [`Span::checked_add`] with the
///   given duration negated.
///   # Errors
///   This has the same error conditions as [`Span::checked_add`].
/// Upstream body (span.rs:1876-1878): the options duration checked-
/// negated, then the add. For the Span rhs the Duration::checked_neg
/// arm is Span::negate (infallible); sub thus = add(negated rhs).
pub exec fn sp_checked_sub_span(
    &self,
    span2: &Span,
) -> (r: Option<Span>)
    requires
        sp_field_inv(self),
        sp_zero_sign_ok(self),
        sp_flags_ok(self),
        self.years == 0 && self.months == 0
            && self.weeks == 0 && self.days == 0,
        sp_field_inv(span2),
        sp_zero_sign_ok(span2),
        sp_flags_ok(span2),
        span2.years == 0 && span2.months == 0
            && span2.weeks == 0 && span2.days == 0,
    ensures
        sp_from_inv_face(
            sp_unit_max(
                sp_span_largest(self),
                sp_span_largest(span2),
            ),
            sp_inv_total_nanos(self)
                - sp_inv_total_nanos(span2),
            &r,
        ),
{
    let neg: Span = span2.negate();
    proof {
        // negate preserves every magnitude and flips only the
        // span-global sign (span.rs:1361-1363), so the invariant
        // total flips sign (the sp_sign_val factor), and the unit
        // flags -- hence sp_span_largest -- pass through unchanged.
        assert(sp_sign_val(neg.sign)
            == 0 - sp_sign_val(span2.sign));
        lemma_mul_unary_negation(
            sp_sign_val(span2.sign),
            (span2.weeks as int) * 604_800 * 1_000_000_000
                + (span2.days as int) * 86_400 * 1_000_000_000
                + (span2.hours as int) * 3_600 * 1_000_000_000
                + (span2.minutes as int) * 60 * 1_000_000_000
                + (span2.seconds as int) * 1_000_000_000
                + (span2.milliseconds as int) * 1_000_000
                + (span2.microseconds as int) * 1_000
                + (span2.nanoseconds as int),
        );
        assert(sp_inv_total_nanos(&neg)
            == 0 - sp_inv_total_nanos(span2));
        assert(sp_span_largest(&neg)
            == sp_span_largest(span2));
    }
    self.sp_checked_add_span(&neg)
}

/// Origin Rust: pub fn checked_sub(SignedDuration) -- the duration
/// rhs arm of span.rs:1871-1879: the Duration::checked_neg for the
/// Absolute variant is SignedDuration::checked_neg, which returns
/// None precisely when as_secs == i64::MIN (signed_duration.rs:1975).
pub exec fn sp_checked_sub_duration(
    &self,
    dur2: &SignedDuration,
) -> (r: Option<Span>)
    requires
        sp_field_inv(self),
        sp_zero_sign_ok(self),
        sp_flags_ok(self),
        self.years == 0 && self.months == 0
            && self.weeks == 0 && self.days == 0,
        sd_inv(dur2),
    ensures
        match r {
            Option::Some(_) => sp_from_inv_face(
                sp_span_largest(self),
                sp_inv_total_nanos(self)
                    - sd_total_nanos(dur2),
                &r,
            ),
            Option::None => (dur2.secs == i64::MIN)
                || !(sp_fid_fits(
                    sp_span_largest(self),
                    sp_inv_total_nanos(self)
                        - sd_total_nanos(dur2),
                )),
        },
{
    let negopt: Option<SignedDuration> = dur2.checked_neg();
    match negopt {
        Option::Some(d2) => {
            proof {
                assert(sd_total_nanos(&d2)
                    == 0 - sd_total_nanos(dur2));
            }
            self.sp_checked_add_duration(&d2)
        }
        Option::None => {
            proof {
                assert(dur2.secs == i64::MIN);
            }
            Option::None
        }
    }
}

} // impl Span

// ===========================================================================
// Panels: the checked_add doc rows this batch's domain can state
// (the year-grade doc rows span.rs:1706-1708 ride the deferred
// relative-date pipeline; the time-unit twins below carry the same
// overflow doctrine), plus the audit-disposition witness for the
// b::SignedDurationSeconds arm.
// ===========================================================================

/// Doc row (span.rs:1631-1644, the re-balancing example):
///   span1 = 2.hours().minutes(59); span2 = 2.minutes();
///   span1.checked_add(span2) == 3.hours().minutes(1)
/// executed through this translation's layout.
pub exec fn sp_panel_checked_add_rebalance() -> (ok_face: bool)
    ensures
        ok_face,
{
    let span1: Span = Span::new().hours(2);
    let span1: Span = span1.minutes(59);
    let span2: Span = Span::new().minutes(2);
    let r: Option<Span> = span1.sp_checked_add_span(&span2);
    match r {
        Option::Some(sp) => {
            let hh: i32 = sp.get_hours();
            let mm: i64 = sp.get_minutes();
            let ss: i64 = sp.get_seconds();
            let mi: i64 = sp.get_milliseconds();
            let mc: i64 = sp.get_microseconds();
            let nn: i64 = sp.get_nanoseconds();
            assert(hh as int == 3);
            assert(mm as int == 1);
            assert(ss as int == 0);
            assert(mi as int == 0);
            assert(mc as int == 0);
            assert(nn as int == 0);
            assert(sp.sign is Positive);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Overflow row (span.rs:1701-1708, "error on overflow" -- the doc's
/// 19_998.years()+1.year example rides the pruned calendar pipeline;
/// the matched-unit twin of the same overflow doctrine, at the hours
/// magnitude: two maximal-hour spans do not fit a single SpanHours
/// bucket).
pub exec fn sp_panel_checked_add_overflow() -> (overflows: bool)
    ensures
        overflows == true,
{
    let span1: Span = Span::new().hours(175_307_616);
    let span2: Span = Span::new().hours(175_307_616);
    let r: Option<Span> = span1.sp_checked_add_span(&span2);
    match r {
        Option::Some(_) => {
            assert(false);
            true
        }
        Option::None => true,
    }
}

/// The audit-disposition witness for the b::SignedDurationSeconds arm
/// (span.rs:1836-1838): through the checked_add(SignedDuration)
/// route the sd-add None is REACHABLE (rhs near SignedDuration::MAX:
/// the summed seconds leave the i64 range), so the ok_or_else arm is
/// genuine error-mapping on this route -- the None face below is
/// machine-checked to be the exact `!fits` negation (the summed
/// total exceeds every bucket's b range by orders of magnitude).
pub exec fn sp_panel_checked_add_sd_max_witness() -> (none_face: bool)
    ensures
        none_face,
{
    let span1: Span = Span::new().hours(1);
    let sdmax: SignedDuration = SignedDuration::max_value();
    let r: Option<Span> =
        span1.sp_checked_add_duration(&sdmax);
    match r {
        Option::Some(_) => {
            assert(false);
            false
        }
        Option::None => true,
    }
}


} // verus!
