//! jiff 0.2.43 rounding family (crates/jiff/src/util/round.rs, the
//! Increment constructors and the RoundMode decision core, plus the
//! SpanRound consumer face of crates/jiff/src/span.rs) -- Verus
//! translation, batch J10.
//!
//! Upstream scope (pin tree, read-only):
//! 1. util/round.rs:31-198 `Increment` (the struct, the six
//!    constructors for_span/for_signed_duration/for_offset/
//!    for_datetime/for_time/for_timestamp, the low-level
//!    for_limits/for_maximums validators, and the getters
//!    unit()/value()), round.rs:168-179 `Increment::round`, and
//!    round.rs:292-341 `RoundMode` with the Temporal decision table
//!    (round.rs:401-462 round_by_i128, reached through
//!    round.rs:357-384 round_by_duration).
//! 2. span.rs:4952-4960 `SpanRound` (the config struct; the
//!    `relative` field is clipped with the relative pipeline, see
//!    below), span.rs:4961-4976 new, the setters smallest/largest/
//!    mode/increment (span.rs:5004-5211), the crate-internal getters
//!    get_smallest/get_largest (span.rs:5321-5333), the may-change
//!    predicates (span.rs:5340-5352), span.rs:6730-6739
//!    requires_relative_date_err, and span.rs:6638-6645
//!    round_span_invariant -- the invariant (no-relative-date) arm
//!    of SpanRound::round (span.rs:5354-5400) that consumes the
//!    batch-J8 arith spine (Span::to_invariant_duration ->
//!    Increment::round -> Span::from_invariant_duration).
//! 3. The upstream doc examples on RoundMode / SpanRound::smallest
//!    / SpanRound::increment / Span::round are carried as witness
//!    panels (doc annotations -> exec asserts), together with the
//!    upstream unit-test rows for the decision table (round.rs:855-
//!    1010, the Temporal rows, the saturation-domain rows and the
//!    maximum-increment ground check).
//!
//! Driver mount: `verified/j10-driver.rs` mounts this file via
//! #[path] next to `src/bounds.rs`, `src/jcore_signed_duration.rs`,
//! `src/jcore_span.rs` and `src/jcore_span_arith.rs` (the J8 driver
//! precedent: the closed panels re-verify in this driver's run;
//! src/lib.rs is NOT touched by this batch).
//!
//! List of modeling losses / prunes (each also annotated at its
//! site; the family ledger applies throughout):
//! 1. Result<T, Error> surfaces materialize as Option<T> (the J1/J5
//!    ledger: error kinds are zero-sized witnesses, error-message
//!    text is not verified). The six Increment constructors each get
//!    an exact Ok/None predicate twin -- the None arm is always the
//!    negation of the Ok predicate, never a vacuous `true` face.
//! 2. The `limits.get(unit as usize)` table lookup of
//!    for_limits/for_maximums (round.rs:213/:240) materializes as
//!    Unit-rank-bound predicates plus a per-unit value spec (the J5
//!    ledger: the verus Unit enum carries no discriminants; upstream
//!    table indexes ARE the discriminants). The Day-arm subtlety is
//!    preserved: for_datetime's table carries one more entry
//!    (MustDivide::Days == 1) than for_time's, so Day (and above)
//!    is always rejected there (upstream tests round.rs:652-659
//!    pin both shapes).
//! 3. `Increment::round`'s increment-in-nanoseconds product and the
//!    round_by_duration as_nanos/try_from_nanos_i128 pair are
//!    transplanted to int arithmetic with machine i128 at the two
//!    edges (the J4b/J8 widening doctrine); try_from_nanos_i128
//!    (signed_duration.rs:1845-1859) is transcribed here as
//!    sd_try_from_nanos_i128 because the J4b core does not carry it.
//! 4. The saturation lane of round_by_i128 (round.rs:456-461,
//!    quotient.saturating_mul) is transcribed with EXACT saturation
//!    semantics (rm_sat_mul / rm_sat_mul_exec; the exec ladder
//!    computes the same values through division bounds), and the
//!    saturation witness panel exercises the upstream i128::MAX rows
//!    plus one genuine clamp-hitting row.
//! 5. The upstream tie/nearer lanes spell `(remainder * 2).abs()` at
//!    machine i128 (round.rs:411-413) -- a lane that OVERFLOWS when
//!    the remainder magnitude exceeds 2**126 (e.g. quantity at
//!    i128::MAX - 1 with increment at i128::MAX), a corner upstream
//!    itself flags as an open overflow question at round.rs:891-904.
//!    The exec here computes the IDENTICAL decision via the
//!    subtractive form (2*mag OP increment <=> mag OP increment -
//!    mag; the subtraction stays positive in-domain), keeping every
//!    lane overflow-free; the doubling form lives on in the spec,
//!    where arithmetic is unbounded. Recorded as a suspected
//!    internal-invariant slip in the batch notes (likely
//!    unreachable through the public rounding API, whose increments
//!    cap at 1_000_000_000 * week-nanos and whose quantities sit in
//!    the SignedDuration range).
//! 6. `SpanRound::relative` / `days_are_24_hours` (span.rs:5274-5321)
//!    and with them the Some(relative) arms of SpanRound::round
//!    (span.rs:5366-5384, relative.round) stay clipped: the relative
//!    pipeline (SpanRelativeTo / to_relative / calendar arithmetic)
//!    is the concurrent batch's scope, and this file translates the
//!    relative==None arm only -- the arm upstream itself routes
//!    through round_span_invariant. DateTimeRound/TimeRound (the
//!    J6-deferred wrappers) ride the same relative surface and stay
//!    deferred with it.
//! 7. `Unit::duration()`'s `unit => unreachable!(...)` on Year/Month
//!    (span.rs:3936-3944) materializes as requires at the exec twin
//!    (a crate-internal contract, not a documented panic).
//! 8. The upstream debug_asserts of round_span_invariant (span.rs:
//!    6639-6640) materialize as requires (the J8 ledger).

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    rust_div, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add_other_way,
    lemma_mul_is_distributive_sub_other_way, lemma_mul_ordering,
    lemma_mul_strictly_positive, lemma_mul_unary_negation,
    lemma_mul_upper_bound,
};

use crate::jcore_signed_duration::{
    SignedDuration, sd_inv, sd_max_total_nanos, sd_min_total_nanos,
    sd_total_nanos,
};
use crate::jcore_span::{
    Span, Unit, sp_field_inv, sp_flags_ok, sp_zero_sign_ok,
};
use crate::jcore_span_arith::{
    sp_fid_fits, sp_fid_secs, sp_from_inv_face, sp_inv_total_nanos,
    sp_unit_max, sp_unit_max_exec, sp_unit_rank, sp_unit_rank_exec,
    sp_span_largest,
};

verus! {

// ===========================================================================
// (0) i128 ground constants (computed by script, never by head --
// the J8 wall-48 discipline; the machine-type bounds as int).
// ===========================================================================

/// 2**127 - 1 == i128::MAX.
pub open spec fn rm_i128_max() -> int {
    170141183460469231731687303715884105727
}

/// -(2**127) == i128::MIN.
pub open spec fn rm_i128_min() -> int {
    -(170141183460469231731687303715884105728int)
}

// ===========================================================================
// (1) Shared spec helpers: the magnitude form of truncated division.
//
// Upstream round_by_i128 (round.rs:401-462) computes on machine i128:
//   quotient = quantity / increment;  remainder = quantity % increment
// (Rust truncated division), then decides on |remainder| against the
// increment. The twins below restate the same arithmetic with
// nonnegative magnitudes (Euclidean division by a positive divisor),
// which keeps every downstream contract linear in the remainder.
// ===========================================================================

pub open spec fn rm_mag(t: int) -> int {
    if t < 0 { -t } else { t }
}

/// The truncated (toward zero) quotient by a positive divisor.
pub open spec fn rm_trunc_q(t: int, i: int) -> int {
    if t < 0 { -(rm_mag(t) / i) } else { rm_mag(t) / i }
}

/// The truncated remainder by a positive divisor (sign of t).
pub open spec fn rm_trunc_rem(t: int, i: int) -> int {
    if t < 0 { -(rm_mag(t) % i) } else { rm_mag(t) % i }
}

/// The saturating product at i128 width (round.rs:456-461,
/// quotient.saturating_mul, restated at int).
pub open spec fn rm_sat_mul(q: int, i: int) -> int {
    if q * i > rm_i128_max() {
        rm_i128_max()
    } else if q * i < rm_i128_min() {
        rm_i128_min()
    } else {
        q * i
    }
}

// ===========================================================================
// (2) RoundMode (round.rs:292-341) and the decision-table spec.
// ===========================================================================

/// Origin Rust: pub enum RoundMode { ... } (round.rs:295-341; the
/// upstream #[non_exhaustive] is a semver surface with no behavior,
/// and the upstream derives -- Clone, Copy, Debug, Eq, Hash,
/// PartialEq (round.rs:293) -- materialize as Copy/Clone below; the
/// derived Eq/Hash traits stay unverified surfaces and every
/// translated contract uses the variant tests).
#[derive(Copy, Clone)]
pub enum RoundMode {
    /// Rounds toward positive infinity (round.rs:296-300).
    Ceil,
    /// Rounds toward negative infinity (round.rs:301-306).
    Floor,
    /// Rounds away from zero (round.rs:307-309).
    Expand,
    /// Rounds toward zero (round.rs:310-315).
    Trunc,
    /// Half-nearest; ties toward positive infinity (round.rs:317-319).
    HalfCeil,
    /// Half-nearest; ties toward negative infinity (round.rs:320-322).
    HalfFloor,
    /// Half-nearest; ties away from zero (round.rs:323-331). The
    /// upstream default for rounding spans and datetimes.
    HalfExpand,
    /// Half-nearest; ties toward zero (round.rs:332-334).
    HalfTrunc,
    /// Half-nearest; ties to the even multiple (round.rs:335-340).
    HalfEven,
}

/// The per-mode bump decision (round.rs:415-455, each match arm's
/// condition): does the mode bump the truncated quotient by the
/// sign of the quantity?
pub open spec fn rm_bumps(
    m: RoundMode,
    sgn: int,
    tie: bool,
    nearer: bool,
    q_odd: bool,
) -> bool {
    match m {
        RoundMode::Ceil => sgn > 0,
        RoundMode::Floor => sgn < 0,
        RoundMode::Expand => true,
        RoundMode::Trunc => false,
        RoundMode::HalfCeil => nearer || (tie && sgn > 0),
        RoundMode::HalfFloor => nearer || (tie && sgn < 0),
        RoundMode::HalfExpand => nearer || tie,
        RoundMode::HalfTrunc => nearer,
        RoundMode::HalfEven => nearer || (tie && q_odd),
    }
}

/// The full decision-table spec of round_by_i128 (round.rs:401-462)
/// at int. The notch `i < 1` arm pins the upstream # Panics entry
/// contract (round.rs:399-400) as the callers' requires instead of
/// an assert; out-of-domain divisors return the quantity.
pub open spec fn rm_round_spec(m: RoundMode, t: int, i: int) -> int {
    if !(i >= 1) || t == 0 {
        t
    } else {
        let rmag: int = rm_mag(t) % i;
        if rmag == 0 {
            t
        } else {
            let sgn: int = if t < 0 { -1 } else { 1 };
            let tie: bool = 2 * rmag == i;
            let nearer: bool = 2 * rmag > i;
            let mq: int = rm_mag(t) / i;
            let q_odd: bool = mq % 2 == 1;
            let trunc_q: int = if t < 0 { -mq } else { mq };
            let adj: int = if rm_bumps(m, sgn, tie, nearer, q_odd) {
                trunc_q + sgn
            } else {
                trunc_q
            };
            rm_sat_mul(adj, i)
        }
    }
}

// ===========================================================================
// (3) The div/rem bridge: machine truncated division <-> the
// magnitude form, plus the bump-lane overflow corridor. One shared
// proof helper every decision-table lane calls.
// ===========================================================================

proof fn lemma_mag_facts(t: int, i: int)
    requires
        i >= 1,
    ensures
        i * (rm_mag(t) / i) + (rm_mag(t) % i) == rm_mag(t),
        0 <= rm_mag(t) % i,
        rm_mag(t) % i < i,
{
    lemma_fundamental_div_mod(rm_mag(t), i);
    assert(rm_mag(t) == i * (rm_mag(t) / i) + (rm_mag(t) % i));
}

/// The magnitude decomposition of the truncated pair: trunc_q * i
/// + trunc_rem == t (the caller-facing restatement of the Euclid
/// identity, spelled so downstream sign reasoning stays linear).
proof fn lemma_trunc_identity(t: int, i: int)
    requires
        i >= 1,
    ensures
        rm_trunc_q(t, i) * i + rm_trunc_rem(t, i) == t,
{
    lemma_mag_facts(t, i);
    let mq: int = rm_mag(t) / i;
    let mr: int = rm_mag(t) % i;
    assert(i * mq + mr == rm_mag(t));
    if t < 0 {
        lemma_mul_is_commutative(mq, i);
        assert(mq * i == i * mq);
        lemma_mul_unary_negation(mq, i);
        assert((-(mq)) * i == -(mq * i));
        assert(rm_trunc_q(t, i) == -(mq));
        assert(rm_trunc_rem(t, i) == -(mr));
        assert(t == -(rm_mag(t)));
        assert(t == -(mq * i + mr));
        assert(rm_trunc_q(t, i) * i + rm_trunc_rem(t, i)
            == -(mq * i) - mr);
        assert(-(mq * i) - mr == -(mq * i + mr));
    } else {
        lemma_mul_is_commutative(mq, i);
        assert(mq * i == i * mq);
        assert(rm_trunc_q(t, i) == mq);
        assert(rm_trunc_rem(t, i) == mr);
        assert(rm_trunc_q(t, i) * i + rm_trunc_rem(t, i)
            == mq * i + mr);
        assert(mq * i + mr == rm_mag(t));
    }
}

/// The bridge: rust_div/rust_rem (the spec of Rust's machine `/` and
/// `%`) fold to the magnitude form; and in the non-exact lane the
/// tensioned quotient+sign bump cannot wrap machine i128.
proof fn lemma_bridge_facts(t: int, i: int)
    requires
        i >= 1,
        rm_i128_min() <= t,
        t <= rm_i128_max(),
    ensures
        rust_div(t, i) == rm_trunc_q(t, i),
        rust_rem(t, i) == rm_trunc_rem(t, i),
        (rust_rem(t, i) == 0) <==> (rm_mag(t) % i == 0),
        (rust_rem(t, i) != 0) ==> (
            (rust_rem(t, i) < 0) <==> (t < 0)
        ),
        (rust_rem(t, i) != 0) ==>
            (rust_rem(t, i) != 0),
        (rust_rem(t, i) != 0) ==> (
            rm_trunc_q(t, i) > rm_i128_min()
                && rm_trunc_q(t, i) < rm_i128_max()
        ),
{
    if t == 0 {
        assert(rm_mag(t) == 0);
        assert(rm_mag(t) / i == 0);
        assert(rm_mag(t) % i == 0);
        assert(rust_div(t, i) == 0);
        assert(rust_rem(t, i) == 0);
    } else {
        lemma_mag_facts(t, i);
        let mq: int = rm_mag(t) / i;
        let mr: int = rm_mag(t) % i;
        lemma_mul_is_commutative(mq, i);
        assert(mq * i == i * mq);
        assert(rm_mag(t) == i * mq + mr);
        assert(rm_mag(t) == mq * i + mr);
        if t < 0 {
            // rust_div/rust_rem's negative arms: -(mag/i), -(mag%i)
            assert(rust_div(t, i) == -(mq));
            assert(rust_rem(t, i) == -(mr));
            lemma_mul_unary_negation(mq, i);
            assert((-(mq)) * i == -(mq * i));
            assert(i * mq == mq * i);
            // t == -(mag) == -(mq*i + mr)
            assert(rm_mag(t) == mq * i + mr);
            assert(t == -(rm_mag(t)));
            assert(t == -(mq * i + mr));
            assert(t + mr == -(mq * i));
            assert(rm_trunc_q(t, i) * i + rm_trunc_rem(t, i)
                == t);
        } else {
            assert(rust_div(t, i) == mq);
            assert(rust_rem(t, i) == mr);
            assert(rm_mag(t) == i * mq + mr);
            assert(i * mq == mq * i);
            assert(t == mq * i + mr);
        }
        if mr != 0 && i >= 2 {
            let q: int = rust_div(t, i);
            let r: int = rust_rem(t, i);
            assert(r != 0);
            assert(q * i + r == t);
            // |q*i| == |t - r| <= rm_i128_max() (both summands are
            // machine-bounded), and a quotient pinned at a machine
            // bound with divisor >= 2 contradicts that.
            if q >= rm_i128_max() {
                assert(q == rm_i128_max());
                lemma_mul_inequality(2, i, q);
                assert(2 * q <= i * q);
                assert(q * i == i * q);
                assert(2 * rm_i128_max() <= i * q == q * i);
                assert(r > -i);
                assert(t < rm_i128_max() + i);
                assert(q * i == t - r < rm_i128_max() + i <= 2 * rm_i128_max());
                assert(false);
            }
            if q <= rm_i128_min() {
                assert(q == rm_i128_min());
                let mm: int = -rm_i128_min();
                assert(q == -(mm));
                lemma_mul_unary_negation(mm, i);
                lemma_mul_inequality(2, i, mm);
                assert(2 * mm <= mm * i);
                assert(q * i == -(mm * i) <= -(2 * mm));
                assert(-(2 * mm) == 2 * rm_i128_min());
                assert(r < i);
                assert(t > rm_i128_min() - i);
                assert(q * i == t - r > rm_i128_min() - i >= 2 * rm_i128_min());
                assert(false);
            }
        }
    }
}

// ===========================================================================
// (4) The saturating-product ladder (round.rs:461). The upper and
// lower quotient bounds ARE the exact product thresholds for a
// positive divisor, so the ladder returns product values identical
// to saturating_mul.
// ===========================================================================

proof fn lemma_sat_hi_prefix(i: int)
    requires
        i >= 1,
    ensures
        rm_i128_max()
            == i * rust_div(rm_i128_max(), i)
                + rust_rem(rm_i128_max(), i),
        0 <= rust_rem(rm_i128_max(), i),
        rust_rem(rm_i128_max(), i) < i,
{
    lemma_fundamental_div_mod(rm_i128_max(), i);
}

proof fn lemma_sat_lo_prefix(i: int)
    requires
        i >= 1,
    ensures
        rust_div(rm_i128_min(), i) * i == rm_i128_min() + mmr(i),
        0 <= mmr(i),
        mmr(i) < i,
{
    let mm: int = -(rm_i128_min());
    lemma_fundamental_div_mod(mm, i);
    let md: int = mm / i;
    let mr: int = mm % i;
    assert(mm == i * md + mr);
    lemma_mul_is_commutative(i, md);
    assert(mm == md * i + mr);
    // rust_div's negative arm: -(mm / i)
    assert(rust_div(rm_i128_min(), i) == -(md));
    lemma_mul_unary_negation(md, i);
    assert(rm_i128_min() == -(mm));
    assert((-(md)) * i == -(md * i));
    assert(rust_div(rm_i128_min(), i) * i == -(md * i));
    assert(-(md * i) == -(mm - mr));
    assert(mmr(i) == mr);
}

/// Origin Rust: quotient.saturating_mul(increment)
///     (round.rs:461, the ladder's exact saturation arithmetic).
pub(crate) exec fn rm_sat_mul_exec(q: i128, i: i128) -> (r: i128)
    requires
        (i as int) >= 1,
    ensures
        (r as int) == rm_sat_mul((q as int), (i as int)),
{
    if q > 0 {
        // q <= rm_i128_max() / i  <=>  q * i inside the range
        let bound_hi: i128 = i128::MAX / i;
        if q <= bound_hi {
            proof {
                let ii: int = (i as int);
                let qi: int = (q as int);
                assert((bound_hi as int) == rust_div(rm_i128_max(), ii));
                lemma_sat_hi_prefix(ii);
                assert(rm_i128_max() == ii * (bound_hi as int)
                    + rust_rem(rm_i128_max(), ii));
                lemma_mul_inequality(qi, (bound_hi as int), ii);
                lemma_mul_is_commutative((bound_hi as int), ii);
                lemma_mul_strictly_positive(qi, ii);
                assert(qi * ii <= (bound_hi as int) * ii);
                assert((bound_hi as int) * ii <= rm_i128_max());
                assert(qi * ii <= rm_i128_max());
                lemma_mul_ordering(qi, ii);
                assert(qi * ii >= qi && qi * ii >= ii);
                assert(qi > 0);
            }
            q * i
        } else {
            proof {
                let ii: int = (i as int);
                let qi: int = (q as int);
                assert((bound_hi as int) == rust_div(rm_i128_max(), ii));
                lemma_sat_hi_prefix(ii);
                assert(qi >= (bound_hi as int) + 1);
                lemma_mul_inequality((bound_hi as int) + 1, qi, ii);
                lemma_mul_is_distributive_add_other_way(
                    ii, (bound_hi as int), 1,
                );
                assert(((bound_hi as int) + 1) * ii
                    == (bound_hi as int) * ii + 1 * ii);
                assert((bound_hi as int) * ii
                    == rm_i128_max() - rust_rem(rm_i128_max(), ii));
                assert((bound_hi as int) * ii + 1 * ii
                    == (bound_hi as int) * ii + ii);
                assert(ii - rust_rem(rm_i128_max(), ii) >= 1);
                assert(((bound_hi as int) + 1) * ii
                    == rm_i128_max()
                        + (ii - rust_rem(rm_i128_max(), ii)));
                assert(((bound_hi as int) + 1) * ii > rm_i128_max());
                assert(qi * ii >= ((bound_hi as int) + 1) * ii);
            }
            i128::MAX
        }
    } else {
        let bound_lo: i128 = i128::MIN / i;
        if q >= bound_lo {
            proof {
                let ii: int = (i as int);
                let qi: int = (q as int);
                assert((bound_lo as int) == rust_div(rm_i128_min(), ii));
                lemma_sat_lo_prefix(ii);
                assert((bound_lo as int) * ii == rm_i128_min() + mmr(ii));
                assert(mmr(ii) >= 0);
                lemma_mul_inequality((bound_lo as int), qi, ii);
                assert((bound_lo as int) * ii <= qi * ii);
                lemma_mul_inequality(qi, 0, ii);
                assert(qi * ii <= 0 <= rm_i128_max());
            }
            q * i
        } else {
            proof {
                let ii: int = (i as int);
                let qi: int = (q as int);
                assert((bound_lo as int) == rust_div(rm_i128_min(), ii));
                lemma_sat_lo_prefix(ii);
                assert((bound_lo as int) * ii == rm_i128_min() + mmr(ii));
                assert(mmr(ii) < ii);
                assert(qi <= (bound_lo as int) - 1);
                lemma_mul_inequality(qi, (bound_lo as int) - 1, ii);
                assert(qi * ii <= ((bound_lo as int) - 1) * ii);
                lemma_mul_is_distributive_sub_other_way(
                    ii, (bound_lo as int), 1,
                );
                assert(((bound_lo as int) - 1) * ii
                    == (bound_lo as int) * ii - 1 * ii);
                assert((bound_lo as int) * ii
                    == rm_i128_min() + mmr(ii));
                assert(mmr(ii) < ii);
                assert(((bound_lo as int) - 1) * ii
                    < rm_i128_min());
                assert(mmr(ii) - ii <= -1);
                assert(qi * ii < rm_i128_min());
            }
            i128::MIN
        }
    }
}

spec fn mmr(i: int) -> int {
    (-(rm_i128_min())) % i
}

// ===========================================================================
// (5) The eight decision-table arms, one exec fn per mode (a
// monolithic body exceeds the rlimit wall on its end-of-function
// query even with a `true` postcondition -- per-mode helper fns are
// the standard cure). Each arm restates the upstream ladder
// (round.rs:405-455) and pins the spec twin for its own mode.
// ===========================================================================

/// The shared non-exact lane: quotient/remainder (already computed
/// by the caller), their magnitude, and the subtractive
/// tie/nearer form (prune note 5: overflow-free where upstream's
/// (remainder * 2).abs() is not).
exec fn rm_arm_lane(
    quantity: i128,
    increment: i128,
    quotient: i128,
    remainder: i128,
) -> (r: (i128, i128))
    requires
        (increment as int) >= 1,
        (quotient as int) == rust_div((quantity as int), (increment as int)),
        (remainder as int) == rust_rem((quantity as int), (increment as int)),
        (remainder as int) != 0,
    ensures
        0 < (r.0 as int),
        (r.0 as int) < (increment as int),
        (r.0 as int) == rm_mag((quantity as int)) % (increment as int),
        (r.1 as int) == (increment as int) - (r.0 as int),
        0 < (r.1 as int),
        // (2*mag OP increment) <=> (mag OP half_gap) on these inputs.
        ((r.0 as int) == (r.1 as int))
            <==> (2 * (r.0 as int) == (increment as int)),
        ((r.0 as int) > (r.1 as int))
            <==> (2 * (r.0 as int) > (increment as int)),
{
    let mag: i128 = if remainder < 0 { 0 - remainder } else { remainder };
    let half_gap: i128 = increment - mag;
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let mi: int = (mag as int);
        assert(mi == rm_mag(ti) % ii);
        assert(1 <= mi);
        assert(mi < ii);
        assert((half_gap as int) == ii - mi);
        assert(2 * mi == ii <==> mi == ii - mi);
        assert(2 * mi > ii <==> mi > ii - mi);
    }
    (mag, half_gap)
}

// Each mode arm mirrors upstream's exact match arm. The proof blocks
// fold the exec decisions (subtractive form) into the spec's bump
// table (doubling form); the correspondence facts come from the
// lane helper and the bridge above.

pub(crate) exec fn rm_round_arm_ceil(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::Ceil, (quantity as int), (increment as int)),
{
    // round.rs:405-409
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // Ceil (round.rs:416-419): bump only toward positive infinity.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let _ = (mag, half_gap);
    let adj: i128 = if sgn > 0 { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        assert((sgn as int) == sgni);
        assert(rm_bumps(RoundMode::Ceil, sgni, false, false, false)
            == (sgni > 0));
        assert((adj as int)
            == (if sgni > 0 {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_floor(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::Floor, (quantity as int), (increment as int)),
{
    // round.rs:405-409
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // Floor (round.rs:421-424): bump only toward negative infinity.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let _ = (mag, half_gap);
    let adj: i128 = if sgn < 0 { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        assert((sgn as int) == sgni);
        assert(rm_bumps(RoundMode::Floor, sgni, false, false, false)
            == (sgni < 0));
        assert((adj as int)
            == (if sgni < 0 {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_expand(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::Expand, (quantity as int), (increment as int)),
{
    // round.rs:405-409
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // Expand (round.rs:426-428): always away from zero.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let _ = (mag, half_gap);
    let adj: i128 = quotient + sgn;
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        assert((sgn as int) == sgni);
        assert(rm_bumps(RoundMode::Expand, sgni, false, false, false));
        assert((adj as int) == rm_trunc_q(ti, ii) + sgni);
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_trunc(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::Trunc, (quantity as int), (increment as int)),
{
    // round.rs:405-409
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // Trunc (round.rs:429): never bumps.
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let _ = (mag, half_gap);
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        assert(!rm_bumps(RoundMode::Trunc, sgni, false, false, false));
        assert((quotient as int) == rm_trunc_q(ti, ii));
    }
    rm_sat_mul_exec(quotient, increment)
}

pub(crate) exec fn rm_round_arm_halfceil(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::HalfCeil, (quantity as int), (increment as int)),
{
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // HalfCeil (round.rs:430-433): bump when nearer, or on a tie
    // toward positive infinity.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let bump: bool = mag > half_gap || (mag == half_gap && sgn > 0);
    let adj: i128 = if bump { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        let tie: bool = 2 * (mag as int) == ii;
        let nearer: bool = 2 * (mag as int) > ii;
        assert(rm_bumps(RoundMode::HalfCeil, sgni, tie, nearer, false)
            == (nearer || (tie && sgni > 0)));
        assert(bump == (nearer || (tie && sgni > 0)));
        assert((adj as int)
            == (if rm_bumps(RoundMode::HalfCeil, sgni, tie, nearer, false) {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_halffloor(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::HalfFloor, (quantity as int), (increment as int)),
{
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // HalfFloor (round.rs:435-438): bump when nearer, or on a tie
    // toward negative infinity.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let bump: bool = mag > half_gap || (mag == half_gap && sgn < 0);
    let adj: i128 = if bump { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        let tie: bool = 2 * (mag as int) == ii;
        let nearer: bool = 2 * (mag as int) > ii;
        assert(rm_bumps(RoundMode::HalfFloor, sgni, tie, nearer, false)
            == (nearer || (tie && sgni < 0)));
        assert(bump == (nearer || (tie && sgni < 0)));
        assert((adj as int)
            == (if rm_bumps(RoundMode::HalfFloor, sgni, tie, nearer, false) {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_halfexpand(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::HalfExpand, (quantity as int), (increment as int)),
{
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // HalfExpand (round.rs:440-443): bump when nearer, or on any tie.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let bump: bool = mag > half_gap || mag == half_gap;
    let adj: i128 = if bump { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        let tie: bool = 2 * (mag as int) == ii;
        let nearer: bool = 2 * (mag as int) > ii;
        assert(rm_bumps(RoundMode::HalfExpand, sgni, tie, nearer, false)
            == (nearer || tie));
        assert(bump == (nearer || tie));
        assert((adj as int)
            == (if rm_bumps(RoundMode::HalfExpand, sgni, tie, nearer, false) {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_halftrunc(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::HalfTrunc, (quantity as int), (increment as int)),
{
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // HalfTrunc (round.rs:445-448): bump only when nearer; ties stay
    // toward zero.
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let bump: bool = mag > half_gap;
    let adj: i128 = if bump { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        let tie: bool = 2 * (mag as int) == ii;
        let nearer: bool = 2 * (mag as int) > ii;
        assert(rm_bumps(RoundMode::HalfTrunc, sgni, tie, nearer, false)
            == nearer);
        assert(bump == nearer);
        assert((adj as int)
            == (if rm_bumps(RoundMode::HalfTrunc, sgni, tie, nearer, false) {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

pub(crate) exec fn rm_round_arm_halfeven(
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(RoundMode::HalfEven, (quantity as int), (increment as int)),
{
    let quotient: i128 = quantity / increment;
    let remainder: i128 = quantity % increment;
    proof {
        lemma_bridge_facts((quantity as int), (increment as int));
    }
    if remainder == 0 {
        return quantity;
    }
    // HalfEven (round.rs:450-453): bump when nearer, or on a tie to
    // the even multiple. Upstream spells quotient.rem_euclid(2) ==
    // 1; a truncated remainder by 2 is nonzero exactly on odd
    // quotients (sign-independent), so `q % 2 != 0` is the same
    // predicate without the negation lane (the MIN-quotient corner
    // never reaches here: it demands divisor 1, whose remainder is
    // always 0).
    let sgn: i128 = if remainder < 0 { -1i128 } else { 1i128 };
    let lane = rm_arm_lane(quantity, increment, quotient, remainder);
    let mag: i128 = lane.0;
    let half_gap: i128 = lane.1;
    let parodd: bool = quotient % 2 != 0;
    let bump: bool = mag > half_gap || (mag == half_gap && parodd);
    let adj: i128 = if bump { quotient + sgn } else { quotient };
    proof {
        let ti: int = (quantity as int);
        let ii: int = (increment as int);
        let sgni: int = if ti < 0 { -1 } else { 1 };
        let tie: bool = 2 * (mag as int) == ii;
        let nearer: bool = 2 * (mag as int) > ii;
        let mq: int = rm_mag(ti) / ii;
        let q_odd: bool = mq % 2 == 1;
        // parity: |trunc quotient| odd <=> truncated remainder by 2
        // nonzero (both division flavors agree on oddness).
        let tq: int = if ti < 0 { -mq } else { mq };
        if mq % 2 == 1 {
            if tq > 0 {
                assert(rust_rem(tq, 2) == 1);
            } else {
                assert(rust_rem(tq, 2) == -1);
            }
        } else {
            if tq > 0 {
                assert(rust_rem(tq, 2) == 0);
            } else {
                assert(rust_rem(tq, 2) == 0);
            }
        }
        assert(parodd <==> q_odd);
        assert(rm_bumps(RoundMode::HalfEven, sgni, tie, nearer, q_odd)
            == (nearer || (tie && q_odd)));
        assert(bump == (nearer || (tie && q_odd)));
        assert((adj as int)
            == (if rm_bumps(RoundMode::HalfEven, sgni, tie, nearer, q_odd) {
                    rm_trunc_q(ti, ii) + sgni
                } else {
                    rm_trunc_q(ti, ii)
                }));
    }
    rm_sat_mul_exec(adj, increment)
}

/// Origin Rust: fn round_by_i128(self, quantity: i128, increment:
///     i128) -> i128 (round.rs:401-462). The # Panics entry contract
///     (round.rs:399-400, `assert!(increment >= 1)`) is this fn's
///     requires.
pub exec fn rm_round_by_i128(
    mode: RoundMode,
    quantity: i128,
    increment: i128,
) -> (r: i128)
    requires
        (increment as int) >= 1,
    ensures
        (r as int)
            == rm_round_spec(mode, (quantity as int), (increment as int)),
{
    match mode {
        RoundMode::Ceil => rm_round_arm_ceil(quantity, increment),
        RoundMode::Floor => rm_round_arm_floor(quantity, increment),
        RoundMode::Expand => rm_round_arm_expand(quantity, increment),
        RoundMode::Trunc => rm_round_arm_trunc(quantity, increment),
        RoundMode::HalfCeil => rm_round_arm_halfceil(quantity, increment),
        RoundMode::HalfFloor => rm_round_arm_halffloor(quantity, increment),
        RoundMode::HalfExpand => {
            rm_round_arm_halfexpand(quantity, increment)
        }
        RoundMode::HalfTrunc => rm_round_arm_halftrunc(quantity, increment),
        RoundMode::HalfEven => rm_round_arm_halfeven(quantity, increment),
    }
}


// ===========================================================================
// (6) The classical contracts of the integer voting core: Ceil,
// Floor and HalfExpand, stated over rm_round_spec (the semantic
// reading of the decision table). All three are proved for every
// quantity inside the i128 window (the decision core's own domain)
// including the saturation-clamp corners, where the clamped result
// still satisfies the contract because a clamp fires only within a
// half/full increment of the machine bound.
// ===========================================================================

/// Ceil (round.rs:296-300, "rounds toward positive infinity"): the
/// least product of the increment at or above t, strictly below
/// t + i.
pub open spec fn rm_ceil_c(t: int, i: int) -> bool {
    let r: int = rm_round_spec(RoundMode::Ceil, t, i);
    t <= r && r - i < t
}

pub open spec fn rm_floor_c(t: int, i: int) -> bool {
    let r: int = rm_round_spec(RoundMode::Floor, t, i);
    t - i < r && r <= t
}

pub open spec fn rm_halfexpand_c(t: int, i: int) -> bool {
    let r: int = rm_round_spec(RoundMode::HalfExpand, t, i);
    let d: int = r - t;
    (-(i)) <= 2 * d && 2 * d <= i
        && (2 * d == i ==> t > 0)
        && (2 * d == -(i) ==> t < 0)
}

proof fn lemma_ceil_contract(t: int, i: int)
    requires
        i >= 1,
        rm_i128_min() <= t,
        t <= rm_i128_max(),
    ensures
        rm_ceil_c(t, i),
{
    if t == 0 {
        assert(rm_round_spec(RoundMode::Ceil, t, i) == 0);
    } else if rm_mag(t) % i == 0 {
        assert(rm_round_spec(RoundMode::Ceil, t, i) == t);
    } else {
        lemma_mag_facts(t, i);
        let mq: int = rm_mag(t) / i;
        let mr: int = rm_mag(t) % i;
        assert(1 <= mr && mr < i);
        assert(i * mq + mr == rm_mag(t));
        lemma_mul_is_commutative(mq, i);
        if t > 0 {
            let adj: int = mq + 1;
            lemma_mul_is_distributive_add_other_way(i, mq, 1);
            assert((mq + 1) * i == mq * i + 1 * i);
            assert(mq * i == t - mr);
            assert(adj * i == t + (i - mr));
            assert(1 <= i - mr && i - mr <= i - 1);
            let r: int = rm_sat_mul(adj, i);
            assert(r == rm_round_spec(RoundMode::Ceil, t, i));
            if r == adj * i {
                assert(t <= r);
                assert(r - i == t - mr);
                assert(r - i < t);
            } else {
                assert(r == rm_i128_max());
                assert(adj * i > rm_i128_max());
                assert(adj * i == t + (i - mr));
                assert(t <= rm_i128_max());
                assert(t - mr > rm_i128_max() - i);
                assert(r - i < t);
            }
        } else {
            // t < 0: Ceil does not bump.
            let adj: int = -(mq);
            lemma_mul_unary_negation(mq, i);
            assert((-(mq)) * i == -(mq * i));
            assert(t == -(rm_mag(t)));
            assert(t + mr == -(mq * i));
            assert(adj * i == t + mr);
            assert(1 <= mr && mr < i);
            let r: int = rm_sat_mul(adj, i);
            assert(r == adj * i);
            assert(r == rm_round_spec(RoundMode::Ceil, t, i));
            assert(t <= r);
            assert(r == t + mr);
            assert(r - i == t + mr - i);
            assert(r - i < t);
        }
    }
}

proof fn lemma_floor_contract(t: int, i: int)
    requires
        i >= 1,
        rm_i128_min() <= t,
        t <= rm_i128_max(),
    ensures
        rm_floor_c(t, i),
{
    if t == 0 {
        assert(rm_round_spec(RoundMode::Floor, t, i) == 0);
    } else if rm_mag(t) % i == 0 {
        assert(rm_round_spec(RoundMode::Floor, t, i) == t);
    } else {
        lemma_mag_facts(t, i);
        let mq: int = rm_mag(t) / i;
        let mr: int = rm_mag(t) % i;
        assert(1 <= mr && mr < i);
        assert(i * mq + mr == rm_mag(t));
        lemma_mul_is_commutative(mq, i);
        if t < 0 {
            let adj: int = -(mq + 1);
            lemma_mul_is_distributive_add_other_way(i, mq, 1);
            assert((mq + 1) * i == mq * i + 1 * i);
            lemma_mul_unary_negation(mq + 1, i);
            assert((-(mq + 1)) * i == -((mq + 1) * i));
            assert(t == -(rm_mag(t)));
            assert(t == -(mq * i + mr));
            assert(adj * i == -(mq * i) - i);
            assert(t - (i - mr) == -(mq * i) - i);
            assert(adj * i == t - (i - mr));
            let r: int = rm_sat_mul(adj, i);
            assert(r == rm_round_spec(RoundMode::Floor, t, i));
            if r == adj * i {
                assert(r == t - (i - mr));
                assert(r <= t);
                assert(1 <= i - mr);
                assert(t - i == t - i);
                assert(t - i < t - i + mr);
                assert(t - i < r);
            } else {
                assert(r == rm_i128_min());
                assert(adj * i < rm_i128_min());
                assert(adj * i == t - (i - mr));
                assert(t <= rm_i128_max());
                assert(t - i + mr < rm_i128_min());
                assert(1 <= mr);
                assert(t - i < rm_i128_min());
                assert(t - i < r);
            }
        } else {
            // t > 0: Floor does not bump.
            let adj: int = mq;
            assert(mq * i == t - mr);
            let r: int = rm_sat_mul(adj, i);
            assert(r == adj * i);
            assert(r == rm_round_spec(RoundMode::Floor, t, i));
            assert(r <= t);
            assert(r == t - mr);
            assert(mr < i);
            assert(t - i < t - mr);
            assert(t - i < r);
        }
    }
}

proof fn lemma_halfexpand_contract(t: int, i: int)
    requires
        i >= 1,
        rm_i128_min() <= t,
        t <= rm_i128_max(),
    ensures
        rm_halfexpand_c(t, i),
{
    if t == 0 {
        assert(rm_round_spec(RoundMode::HalfExpand, t, i) == 0);
    } else if rm_mag(t) % i == 0 {
        assert(rm_round_spec(RoundMode::HalfExpand, t, i) == t);
    } else {
        lemma_mag_facts(t, i);
        let mq: int = rm_mag(t) / i;
        let mr: int = rm_mag(t) % i;
        assert(1 <= mr && mr < i);
        assert(i * mq + mr == rm_mag(t));
        lemma_mul_is_commutative(mq, i);
        let bumps: bool = 2 * mr > i || 2 * mr == i;
        if !bumps {
            // toward zero: distance mr, strictly inside a half step
            let adj: int = if t < 0 { -mq } else { mq };
            let d: int = if t < 0 { mr } else { -(mr) };
            if t < 0 {
                lemma_mul_unary_negation(mq, i);
                assert((-(mq)) * i == -(mq * i));
                assert(t == -(rm_mag(t)));
                assert(t + mr == -(mq * i));
            } else {
                assert(mq * i == t - mr);
            }
            assert(adj * i == t + d);
            let r: int = rm_sat_mul(adj, i);
            assert(r == adj * i);
            assert(r == rm_round_spec(RoundMode::HalfExpand, t, i));
            assert(r - t == d);
            assert(2 * mr < i);
            if t > 0 {
                assert(d == -(mr));
                assert(2 * d == -(2 * mr));
                assert(2 * mr < i);
                assert(-(i) <= 2 * d);
                assert(2 * d <= i);
            } else {
                assert(d == mr);
                assert(2 * d == 2 * mr);
                assert(2 * mr < i);
                assert(2 * d <= i - 1);
                assert(-(i) <= 2 * d);
            }
        } else {
            let sgn: int = if t < 0 { -1 } else { 1 };
            if t > 0 {
                let adj: int = mq + 1;
                let d: int = i - mr;
                lemma_mul_is_distributive_add_other_way(i, mq, 1);
                assert((mq + 1) * i == mq * i + 1 * i);
                assert(mq * i == t - mr);
                assert(adj * i == t + d);
                assert(2 * mr >= i);
                assert(d == i - mr);
                assert(2 * d == 2 * (i - mr));
                assert(2 * (i - mr) == 2 * i - 2 * mr);
                assert(2 * i - 2 * mr <= i);
                assert(2 * d <= i);
                assert(0 <= 2 * d);
                let r: int = rm_sat_mul(adj, i);
                if r == adj * i {
                    assert(r == rm_round_spec(RoundMode::HalfExpand, t, i));
                    assert(r - t == d);
                    assert(0 <= 2 * d);
                    assert(2 * d <= i);
                    if 2 * d == i {
                        assert(2 * mr == i);
                        assert(t > 0);
                    }
                } else {
                    assert(r == rm_i128_max());
                    assert(adj * i == t + d > rm_i128_max());
                    assert(t > rm_i128_max() - d);
                    let dd: int = r - t;
                    assert(dd < d);
                    assert(0 <= dd);
                    assert(2 * d == 2 * (i - mr));
                    assert(2 * (i - mr) <= i);
                    assert(2 * dd < 2 * d <= i);
                    assert(r == rm_round_spec(RoundMode::HalfExpand, t, i));
                    assert(r - t == dd);
                }
            } else {
                let adj: int = -(mq + 1);
                let d: int = -(i - mr);
                lemma_mul_is_distributive_add_other_way(i, mq, 1);
                assert((mq + 1) * i == mq * i + 1 * i);
                lemma_mul_unary_negation(mq + 1, i);
                assert((-(mq + 1)) * i == -((mq + 1) * i));
                assert(t == -(rm_mag(t)));
                assert(t == -(mq * i + mr));
                assert(adj * i == -(mq * i) - i);
                assert(t - i + mr == -(mq * i) - i);
                assert(d == -(i - mr));
                assert(adj * i == t + d);
                assert(2 * mr >= i);
                assert(2 * (i - mr) <= i);
                assert(2 * d == -(2 * (i - mr)));
                assert(2 * d >= -(i));
                let r: int = rm_sat_mul(adj, i);
                if r == adj * i {
                    assert(r == rm_round_spec(RoundMode::HalfExpand, t, i));
                    assert(r - t == d);
                    assert(-(i) <= 2 * d);
                    if -(2 * d) == i {
                        assert(2 * (i - mr) == i);
                        assert(2 * mr == i);
                    }
                } else {
                    assert(r == rm_i128_min());
                    assert(adj * i == t + d < rm_i128_min());
                    assert(t < rm_i128_min() - d);
                    let dd: int = r - t;
                    assert(dd > d);
                    assert(dd <= 0);
                    assert(2 * dd > 2 * d >= -(i));
                    assert(r == rm_round_spec(RoundMode::HalfExpand, t, i));
                    assert(r - t == dd);
                }
            }
        }
    }
}

// ===========================================================================
// (7) Increment (round.rs:31-256): the struct, the increment range
// twin (b::Increment32::check, util/b.rs:178 -- ranged 1..=
// 1_000_000_000 over an i64 input), the two validator tables and the
// six constructors with exact two-sided faces.
// ===========================================================================

/// Origin Rust: pub(crate) struct Increment { unit: Unit, value: i32 }
///     (round.rs:31-35).
#[derive(Copy, Clone)]
pub struct Increment {
    pub unit: Unit,
    pub value: i32,
}

/// The increment-range invariant every constructor enforces
/// (round.rs:193-194: "guaranteed to be in the range
/// 1..=1_000_000_000"); the constructors reject everything else
/// (negatives, zero, and out-of-range i64s, round.rs:475-589).
pub open spec fn inc_value_ok(v: i64) -> bool {
    1 <= (v as int) && (v as int) <= 1_000_000_000
}

pub open spec fn inc_inv(i: &Increment) -> bool {
    inc_value_ok(i.value as i64)
}

/// The LIMITS table over the time units (round.rs:44-51, :134-141):
/// the must-divide entry per unit.
pub open spec fn rm_must_divide_time(u: Unit) -> int {
    match u {
        Unit::Nanosecond => 1_000,
        Unit::Microsecond => 1_000,
        Unit::Millisecond => 1_000,
        Unit::Second => 60,
        Unit::Minute => 60,
        Unit::Hour => 24,
        _ => 0, // table entries exist for the time units only
    }
}

/// The MAXIMUMS table of for_timestamp (round.rs:153-160): the
/// per-unit civil-day budget.
pub open spec fn rm_maximums_time(u: Unit) -> int {
    match u {
        Unit::Nanosecond => 86_400_000_000_000,
        Unit::Microsecond => 86_400_000_000,
        Unit::Millisecond => 86_400_000,
        Unit::Second => 86_400,
        Unit::Minute => 1_440,
        Unit::Hour => 24,
        _ => 0,
    }
}

/// for_span (round.rs:39-69): calendar units (Day and above) accept
/// any in-range inline increment; time units must divide the next
/// unit up and be smaller than it (for_limits, round.rs:208-228).
pub open spec fn inc_for_span_ok(u: Unit, v: i64) -> bool {
    inc_value_ok(v)
        && (sp_unit_rank(u) >= sp_unit_rank(Unit::Day)
            || ((v as int) < rm_must_divide_time(u)
                && rm_must_divide_time(u) % (v as int) == 0))
}

/// for_datetime (round.rs:109-125) and for_time (round.rs:129-144):
/// the LIMITS table over the time units only (for_datetime's extra
/// Days == 1 entry at Unit::Day makes Day-and-above always-rejected
/// there too, round.rs:652-659).
pub open spec fn inc_for_time_like_ok(u: Unit, v: i64) -> bool {
    inc_value_ok(v)
        && sp_unit_rank(u) <= sp_unit_rank(Unit::Hour)
        && ((v as int) < rm_must_divide_time(u)
            && rm_must_divide_time(u) % (v as int) == 0)
}

/// for_timestamp (round.rs:148-163): the MAXIMUMS table, where the
/// value may equal the entry (round.rs:248: `value <= must_divide`).
pub open spec fn inc_for_timestamp_ok(u: Unit, v: i64) -> bool {
    inc_value_ok(v)
        && sp_unit_rank(u) <= sp_unit_rank(Unit::Hour)
        && ((v as int) <= rm_maximums_time(u)
            && rm_maximums_time(u) % (v as int) == 0)
}

/// for_signed_duration (round.rs:73-87): units up to Hour, any
/// in-range value.
pub open spec fn inc_for_signed_duration_ok(u: Unit, v: i64) -> bool {
    inc_value_ok(v) && sp_unit_rank(u) <= sp_unit_rank(Unit::Hour)
}

/// for_offset (round.rs:91-105): Second..=Hour, any in-range value.
pub open spec fn inc_for_offset_ok(u: Unit, v: i64) -> bool {
    inc_value_ok(v)
        && sp_unit_rank(Unit::Second) <= sp_unit_rank(u)
        && sp_unit_rank(u) <= sp_unit_rank(Unit::Hour)
}

impl Increment {
    exec fn try_new32(u: Unit, v: i64) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (i.unit == u
                        && (i.value as int) == (v as int)
                        && inc_value_ok(v)),
                Option::None => !inc_value_ok(v),
            },
    {
        if inc_value_ok_exec(v) {
            proof {
                assert(1 <= (v as int));
                assert((v as int) <= 1_000_000_000);
                assert((v as int) <= 2_147_483_647);
                assert((v as int) >= -(2147483648int));
            }
            Option::Some(Increment { unit: u, value: v as i32 })
        } else {
            Option::None
        }
    }

    /// Origin Rust: pub(crate) fn for_span(unit: Unit, value: i64)
    ///     -> Result<Increment, Error> (round.rs:39-69).
    pub exec fn for_span(u: Unit, v: i64) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (inc_for_span_ok(u, v) && i.unit == u
                        && (i.value as int) == (v as int)),
                Option::None => !inc_for_span_ok(u, v),
            },
    {
        if sp_unit_rank_exec(u) >= sp_unit_rank_exec(Unit::Day) {
            // Calendar units (round.rs:62-67): range gate only.
            Increment::try_new32(u, v)
        } else {
            // Time units (round.rs:59-61): the must-divide window.
            if inc_value_ok_exec(v) {
                proof {
                    assert((v as int) >= 1);
                    assert(sp_unit_rank(u) < sp_unit_rank(Unit::Day));
                }
                let limit: i64 = must_divide_time_exec(u);
                if v < limit && limit % v == 0 {
                    Increment::try_new32(u, v)
                } else {
                    proof {
                        assert(sp_unit_rank(u) <= sp_unit_rank(Unit::Hour));
                        assert((limit as int)
                            == rm_must_divide_time(u));
                        assert(!((v as int) < rm_must_divide_time(u)
                            && rm_must_divide_time(u) % (v as int) == 0));
                        assert(!inc_for_span_ok(u, v));
                    }
                    Option::None
                }
            } else {
                proof {
                    assert(!inc_for_span_ok(u, v));
                }
                Option::None
            }
        }
    }

    /// Origin Rust: pub(crate) fn for_signed_duration(unit: Unit,
    ///     value: i64) -> Result<Increment, Error> (round.rs:73-87).
    pub exec fn for_signed_duration(
        u: Unit,
        v: i64,
    ) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (inc_for_signed_duration_ok(u, v)
                        && i.unit == u
                        && (i.value as int) == (v as int)),
                Option::None => !inc_for_signed_duration_ok(u, v),
            },
    {
        if sp_unit_rank_exec(u) <= sp_unit_rank_exec(Unit::Hour) {
            Increment::try_new32(u, v)
        } else {
            proof {
                assert(!inc_for_signed_duration_ok(u, v));
            }
            Option::None
        }
    }

    /// Origin Rust: pub(crate) fn for_offset(unit: Unit, value: i64)
    ///     -> Result<Increment, Error> (round.rs:91-105).
    pub exec fn for_offset(u: Unit, v: i64) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (inc_for_offset_ok(u, v) && i.unit == u
                        && (i.value as int) == (v as int)),
                Option::None => !inc_for_offset_ok(u, v),
            },
    {
        if sp_unit_rank_exec(Unit::Second) <= sp_unit_rank_exec(u)
            && sp_unit_rank_exec(u) <= sp_unit_rank_exec(Unit::Hour)
        {
            Increment::try_new32(u, v)
        } else {
            proof {
                assert(!inc_for_offset_ok(u, v));
            }
            Option::None
        }
    }

    /// Origin Rust: pub(crate) fn for_datetime(unit: Unit,
    ///     value: i64) -> Result<Increment, Error> (round.rs:109-125).
    pub exec fn for_datetime(u: Unit, v: i64) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (inc_for_time_like_ok(u, v) && i.unit == u
                        && (i.value as int) == (v as int)),
                Option::None => !inc_for_time_like_ok(u, v),
            },
    {
        if sp_unit_rank_exec(u) <= sp_unit_rank_exec(Unit::Hour) {
            if inc_value_ok_exec(v) {
                proof {
                    assert((v as int) >= 1);
                }
                let limit: i64 = must_divide_time_exec(u);
                if v < limit && limit % v == 0 {
                    Increment::try_new32(u, v)
                } else {
                    proof {
                        assert((limit as int)
                            == rm_must_divide_time(u));
                        assert(!inc_for_time_like_ok(u, v));
                    }
                    Option::None
                }
            } else {
                proof {
                    assert(!inc_for_time_like_ok(u, v));
                }
                Option::None
            }
        } else {
            proof {
                assert(!inc_for_time_like_ok(u, v));
            }
            Option::None
        }
    }

    /// Origin Rust: pub(crate) fn for_time(unit: Unit, value: i64)
    ///     -> Result<Increment, Error> (round.rs:129-144; same
    ///     LIMITS surface as for_datetime minus the Days entry --
    ///     for the time units the two constructors agree exactly,
    ///     Day-and-above being rejected by both).
    pub exec fn for_time(u: Unit, v: i64) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (inc_for_time_like_ok(u, v) && i.unit == u
                        && (i.value as int) == (v as int)),
                Option::None => !inc_for_time_like_ok(u, v),
            },
    {
        Increment::for_datetime(u, v)
    }

    /// Origin Rust: pub(crate) fn for_timestamp(unit: Unit,
    ///     value: i64) -> Result<Increment, Error>
    ///     (round.rs:148-163).
    pub exec fn for_timestamp(u: Unit, v: i64) -> (r: Option<Increment>)
        ensures
            match r {
                Option::Some(i) =>
                    (inc_for_timestamp_ok(u, v) && i.unit == u
                        && (i.value as int) == (v as int)),
                Option::None => !inc_for_timestamp_ok(u, v),
            },
    {
        if sp_unit_rank_exec(u) <= sp_unit_rank_exec(Unit::Hour) {
            if inc_value_ok_exec(v) {
                proof {
                    assert((v as int) >= 1);
                }
                let maxv: i64 = maximums_time_exec(u);
                if v <= maxv && maxv % v == 0 {
                    Increment::try_new32(u, v)
                } else {
                    proof {
                        assert((maxv as int) == rm_maximums_time(u));
                        assert(!inc_for_timestamp_ok(u, v));
                    }
                    Option::None
                }
            } else {
                proof {
                    assert(!inc_for_timestamp_ok(u, v));
                }
                Option::None
            }
        } else {
            proof {
                assert(!inc_for_timestamp_ok(u, v));
            }
            Option::None
        }
    }

    /// Origin Rust: pub(crate) fn unit(&self) -> Unit
    ///     (round.rs:184-186).
    pub(crate) exec fn unit(&self) -> (r: Unit)
        ensures
            r == self.unit,
    {
        self.unit
    }

    /// Origin Rust: pub(crate) fn value(&self) -> i32
    ///     (round.rs:195-197; the doc's range guarantee rides the
    ///     caller's inc_inv).
    pub(crate) exec fn value(&self) -> (r: i32)
        requires
            inc_inv(self),
        ensures
            (r as int) == (self.value as int),
            1 <= (r as int),
            (r as int) <= 1_000_000_000,
    {
        self.value
    }
}

exec fn must_divide_time_exec(u: Unit) -> (r: i64)
    requires
        sp_unit_rank(u) <= sp_unit_rank(Unit::Hour),
    ensures
        (r as int) == rm_must_divide_time(u),
{
    match u {
        Unit::Nanosecond => 1_000,
        Unit::Microsecond => 1_000,
        Unit::Millisecond => 1_000,
        Unit::Second => 60,
        Unit::Minute => 60,
        _ => 24, // Unit::Hour (the requires keeps the arm)
    }
}

exec fn maximums_time_exec(u: Unit) -> (r: i64)
    requires
        sp_unit_rank(u) <= sp_unit_rank(Unit::Hour),
    ensures
        (r as int) == rm_maximums_time(u),
{
    match u {
        Unit::Nanosecond => 86_400_000_000_000,
        Unit::Microsecond => 86_400_000_000,
        Unit::Millisecond => 86_400_000,
        Unit::Second => 86_400,
        Unit::Minute => 1_440,
        _ => 24, // Unit::Hour (the requires keeps the arm)
    }
}

// ===========================================================================
// (8) Increment::round and the round_by_duration pair
// (round.rs:168-179 and :357-384), with the i128 nanosecond
// constructor the latter consumes (signed_duration.rs:1845-1859).
// ===========================================================================

/// Unit::duration() (span.rs:3928-3944): the invariant nanosecond
/// budget per unit; the Year/Month entries carry upstream's
/// unreachable! contract as the caller's requires (prune 7).
pub open spec fn rm_unit_nanos(u: Unit) -> int {
    match u {
        Unit::Nanosecond => 1,
        Unit::Microsecond => 1_000,
        Unit::Millisecond => 1_000_000,
        Unit::Second => 1_000_000_000,
        Unit::Minute => 60_000_000_000,
        Unit::Hour => 3_600_000_000_000,
        Unit::Day => 86_400_000_000_000,
        Unit::Week => 604_800_000_000_000,
        _ => 0, // Unit::Year | Unit::Month: unreachable-upstream
    }
}

exec fn rm_unit_nanos_exec(u: Unit) -> (r: i64)
    requires
        !(u is Year),
        !(u is Month),
    ensures
        (r as int) == rm_unit_nanos(u),
{
    match u {
        Unit::Nanosecond => 1,
        Unit::Microsecond => 1_000,
        Unit::Millisecond => 1_000_000,
        Unit::Second => 1_000_000_000,
        Unit::Minute => 60_000_000_000,
        Unit::Hour => 3_600_000_000_000,
        Unit::Day => 86_400_000_000_000,
        _ => 604_800_000_000_000, // Unit::Week (requires keeps it)
    }
}

/// Increment::round's increment-in-nanoseconds product
/// (round.rs:173-178: self.value() * self.unit().duration(); the
/// upstream safety comment's ground: the maximum is the week budget
/// times 1_000_000_000, round.rs:1015-1022).
pub open spec fn inc_increment_nanos(i: &Increment) -> int {
    (i.value as int) * rm_unit_nanos(i.unit)
}

/// Origin Rust: pub const fn try_from_nanos_i128(nanos: i128)
///     -> Option<SignedDuration> (signed_duration.rs:1845-1859;
///     transcribed here because the J4b core does not carry it).
/// The None face is exact: the i64-second window IS the
/// SignedDuration total range (its edges sd_min/sd_max_total_nanos,
/// from the trunc-division shape of the upstream body).
pub exec fn sd_try_from_nanos_i128(n: i128) -> (r: Option<SignedDuration>)
    ensures
        match r {
            Option::Some(d) =>
                sd_inv(&d) && sd_total_nanos(&d) == (n as int),
            Option::None =>
                ((n as int) < sd_min_total_nanos()
                    || (n as int) > sd_max_total_nanos()),
        },
{
    // upstream body: secs = nanos / NANOS_PER_SEC (trunc; the
    // constant is upstream-stated as safe because it is not
    // {-1, 0), the window check, then subsec = nanos % NANOS_PER_SEC.
    let secs: i128 = n / 1_000_000_000;
    proof {
        lemma_bridge_facts((n as int), 1_000_000_000int);
        lemma_trunc_identity((n as int), 1_000_000_000int);
        assert((secs as int)
            == rm_trunc_q((n as int), 1_000_000_000int));
    }
    if !(-(9_223_372_036_854_775_808i128) <= secs
        && secs <= 9_223_372_036_854_775_807i128)
    {
        proof {
            let ni: int = (n as int);
            let s: int = (secs as int);
            lemma_trunc_identity(ni, 1_000_000_000int);
            assert(s == rust_div(ni, 1_000_000_000int));
            assert(rust_div(ni, 1_000_000_000int) * 1_000_000_000int
                + rust_rem(ni, 1_000_000_000int) == ni);
            let sub: int = rust_rem(ni, 1_000_000_000int);
            assert(ni == s * 1_000_000_000int + sub);
            if s > 9_223_372_036_854_775_807int {
                // positive lane: the trunc remainder is nonnegative,
                // so ni >= s*1e9, one full second past sd_max.
                assert(sub >= 0);
                assert(s >= 9_223_372_036_854_775_808int);
                assert(s * 1_000_000_000int
                    >= 9_223_372_036_854_775_808_000_000_000int);
                assert(9_223_372_036_854_775_808_000_000_000int
                    == sd_max_total_nanos() + 1int);
                assert(ni >= sd_max_total_nanos() + 1int);
                assert(ni > sd_max_total_nanos());
            } else {
                // negative lane: s <= MIN - 1 and the trunc remainder
                // is nonpositive, so ni <= s*1e9, one full second
                // past sd_min.
                assert(s <= -(9_223_372_036_854_775_809int));
                assert(sub <= 0);
                assert(s * 1_000_000_000int
                    <= -(9_223_372_036_854_775_809_000_000_000int));
                assert(-(9_223_372_036_854_775_809_000_000_000int)
                    == sd_min_total_nanos() - 1int);
                assert(ni <= sd_min_total_nanos() - 1int);
                assert(ni < sd_min_total_nanos());
            }
        }
        return Option::None;
    }
    let nanos: i128 = n % 1_000_000_000;
    proof {
        let ni: int = (n as int);
        assert((nanos as int) == rm_trunc_rem(ni, 1_000_000_000int));
        assert(rm_mag(ni) % 1_000_000_000int < 1_000_000_000int);
        assert((nanos as int) < 1_000_000_000);
        assert((nanos as int) > -(1_000_000_000));
    }
    let nanos32: i32 = nanos as i32;
    let out = SignedDuration { secs: secs as i64, nanos: nanos32 };
    proof {
        let ni: int = (n as int);
        let s: int = (secs as int);
        let sub: int = (nanos32 as int);
        lemma_trunc_identity(ni, 1_000_000_000int);
        assert(s == rm_trunc_q(ni, 1_000_000_000int));
        assert(sub == rm_trunc_rem(ni, 1_000_000_000int));
        // sd_inv: the trunc pair shares ni's sign (both components
        // are the magnitude components), and the subsecond is
        // canonical by the remainder range.
        if ni > 0 {
            assert(s == rm_mag(ni) / 1_000_000_000int);
            if sub != 0 {
                assert(sub == rm_mag(ni) % 1_000_000_000int);
                assert(1 <= sub);
                assert(sub <= 999_999_999);
            }
        }
        if ni < 0 {
            assert(s == -(rm_mag(ni) / 1_000_000_000int));
            if sub != 0 {
                assert(
                    sub == -(rm_mag(ni) % 1_000_000_000int)
                );
                assert(-(999_999_999int) <= sub);
                assert(sub < 0);
            }
        }
    }
    Option::Some(out)
}

/// Origin Rust: pub(crate) fn round(&self, mode: RoundMode,
///     quantity: SignedDuration) -> Result<SignedDuration, Error>
///     (round.rs:168-179; the body delegates to
///     round_by_duration, round.rs:357-384, whose comment
///     round.rs:366-381 argues the error is practically
///     unreachable -- here the None arm says exactly when it fires).
impl Increment {
    pub(crate) exec fn inc_round(
        &self,
        mode: RoundMode,
        quantity: &SignedDuration,
    ) -> (r: Option<SignedDuration>)
        requires
            inc_inv(self),
            !(self.unit is Year),
            !(self.unit is Month),
            sd_inv(quantity),
        ensures
            match r {
                Option::Some(d) =>
                    (sd_inv(&d)
                        && (sd_total_nanos(&d)
                            == rm_round_spec(
                                mode,
                                sd_total_nanos(quantity),
                                inc_increment_nanos(self),
                            ))),
                Option::None =>
                    rm_round_spec(
                        mode,
                        sd_total_nanos(quantity),
                        inc_increment_nanos(self),
                    ) < sd_min_total_nanos()
                    || rm_round_spec(
                        mode,
                        sd_total_nanos(quantity),
                        inc_increment_nanos(self),
                    ) > sd_max_total_nanos(),
            },
    {
        // Upstream safety comment (round.rs:173-176): the product
        // value * unit duration cannot exceed the week budget times
        // 1_000_000_000 (the maximum_increment_nanos ground,
        // round.rs:1015-1022); pinned here so the machine i128
        // product carries a proof-checked bound.
        let u_nanos: i64 = rm_unit_nanos_exec(self.unit);
        proof {
            assert(1 <= (self.value as int));
            assert((self.value as int) <= 1_000_000_000);
            assert((u_nanos as int) == rm_unit_nanos(self.unit));
            assert(rm_unit_nanos(self.unit)
                <= 604_800_000_000_000int);
            lemma_mul_upper_bound((self.value as int),
                1_000_000_000int,
                rm_unit_nanos(self.unit), 604_800_000_000_000int);
            assert((self.value as int) * rm_unit_nanos(self.unit)
                <= 604_800_000_000_000_000_000_000int);
            assert((self.value as int) * rm_unit_nanos(self.unit)
                >= 1int);
        }
        let inc_nanos: i128 = (self.value as i128) * (u_nanos as i128);
        proof {
            assert((inc_nanos as int)
                == (self.value as i128 as int) * (u_nanos as i128 as int));
            assert((self.value as i128 as int)
                == (self.value as int));
            assert((u_nanos as i128 as int) == rm_unit_nanos(self.unit));
            assert((inc_nanos as int)
                == (self.value as int) * rm_unit_nanos(self.unit));
            assert(inc_nanos >= 1i128);
        }
        let qn: i128 = quantity.as_nanos();
        let rounded: i128 = rm_round_by_i128(mode, qn, inc_nanos);
        sd_try_from_nanos_i128(rounded)
    }
}


// ===========================================================================
// (9) SpanRound (span.rs:4952-5352): the config struct, new, the
// setters, the getters and the may-change predicates.
// ===========================================================================

/// Origin Rust: pub struct SpanRound<'a> (span.rs:4952-4960). The
/// `relative` field (Option<SpanRelativeTo<'a>>) is clipped with
/// the relative pipeline (prune 6, the concurrent batch's scope), so
/// the translated config covers the relative==None arm -- the arm
/// whose body upstream routes through round_span_invariant.
/// days_are_24_hours is clipped with it.
#[derive(Copy, Clone)]
pub struct SpanRound {
    pub largest: Option<Unit>,
    pub smallest: Unit,
    pub mode: RoundMode,
    pub increment: i64,
}

/// The may-change predicate twin (span.rs:5340-5347).
pub open spec fn sr_may_change_spec(cfg: &SpanRound) -> bool {
    (!(cfg.smallest is Nanosecond)) || cfg.increment != 1
}

/// The calendar-only twin (span.rs:5349-5352).
pub open spec fn sr_calendar_may_change_spec(cfg: &SpanRound) -> bool {
    (!(cfg.smallest is Day)) || cfg.increment != 1
}

/// requires_relative_date_err's predicate face (span.rs:6730-6739):
/// a variable unit (Year/Month/Week/Day, span.rs:3947-3950) demands a
/// relative datetime. The upstream error-kind split
/// (RelativeWeekOrDay vs RelativeYearOrMonth) is clipped per the
/// Option doctrine.
pub open spec fn sr_requires_relative_err(u: Unit) -> bool {
    sp_unit_rank(u) >= sp_unit_rank(Unit::Day)
}

impl SpanRound {
    /// Origin Rust: pub fn new() -> SpanRound<'static>
    ///     (span.rs:4968-4976). Upstream doc (span.rs:4965-4967):
    ///     "The default configuration does no rounding."
    pub exec fn new() -> (r: SpanRound)
        ensures
            r.largest is None,
            r.smallest is Nanosecond,
            r.mode is HalfExpand,
            r.increment == 1,
    {
        SpanRound {
            largest: Option::None,
            smallest: Unit::Nanosecond,
            mode: RoundMode::HalfExpand,
            increment: 1,
        }
    }

    /// Origin Rust: pub fn smallest(self, unit: Unit) -> SpanRound
    ///     (span.rs:5004-5008).
    pub exec fn smallest(self, unit: Unit) -> (r: SpanRound)
        ensures
            r.smallest == unit,
            r.largest == self.largest,
            r.mode == self.mode,
            r.increment == self.increment,
    {
        SpanRound {
            largest: self.largest,
            smallest: unit,
            mode: self.mode,
            increment: self.increment,
        }
    }

    /// Origin Rust: pub fn largest(self, unit: Unit) -> SpanRound
    ///     (span.rs:5129-5133).
    pub exec fn largest(self, unit: Unit) -> (r: SpanRound)
        ensures
            r.largest is Some,
            match r.largest {
                Option::Some(u) => u == unit,
                Option::None => false,
            },
            r.smallest == self.smallest,
            r.mode == self.mode,
            r.increment == self.increment,
    {
        SpanRound {
            largest: Option::Some(unit),
            smallest: self.smallest,
            mode: self.mode,
            increment: self.increment,
        }
    }

    /// Origin Rust: pub fn mode(self, mode: RoundMode) -> SpanRound
    ///     (span.rs:5163-5167).
    pub exec fn mode(self, mode: RoundMode) -> (r: SpanRound)
        ensures
            r.mode == mode,
            r.largest == self.largest,
            r.smallest == self.smallest,
            r.increment == self.increment,
    {
        SpanRound {
            largest: self.largest,
            smallest: self.smallest,
            mode,
            increment: self.increment,
        }
    }

    /// Origin Rust: pub fn increment(self, increment: i64)
    ///     -> SpanRound (span.rs:5207-5211; the doc's deferral note,
    ///     span.rs:5208: "The error will occur when computing the
    ///     span, and not when setting the increment" -- this setter
    ///     accepts every i64 exactly as upstream).
    pub exec fn increment(self, increment: i64) -> (r: SpanRound)
        ensures
            r.increment == increment,
            r.largest == self.largest,
            r.smallest == self.smallest,
            r.mode == self.mode,
    {
        SpanRound {
            largest: self.largest,
            smallest: self.smallest,
            mode: self.mode,
            increment,
        }
    }

    /// Origin Rust: pub(crate) fn get_smallest(&self) -> Unit
    ///     (span.rs:5321-5324).
    pub(crate) exec fn get_smallest(&self) -> (r: Unit)
        ensures
            r == self.smallest,
    {
        self.smallest
    }

    /// Origin Rust: pub(crate) fn get_largest(&self) -> Option<Unit>
    ///     (span.rs:5328-5331).
    pub(crate) exec fn get_largest(&self) -> (r: Option<Unit>)
        ensures
            r == self.largest,
    {
        self.largest
    }

    /// Origin Rust: pub(crate) fn rounding_may_change_span(&self)
    ///     -> bool (span.rs:5340-5347; "Returns true only when
    ///     rounding a span *may* change it").
    pub(crate) exec fn rounding_may_change_span(&self) -> (r: bool)
        ensures
            r == sr_may_change_spec(self),
    {
        sr_unit_is_nano(self.smallest) == false || self.increment != 1
    }

    /// Origin Rust: pub(crate) fn
    ///     rounding_calendar_only_may_change_span(&self) -> bool
    ///     (span.rs:5349-5352; the upstream note lands this on
    ///     civil::Date).
    pub(crate) exec fn rounding_calendar_only_may_change_span(&self)
        -> (r: bool)
        ensures
            r == sr_calendar_may_change_spec(self),
    {
        sr_unit_is_day(self.smallest) == false || self.increment != 1
    }
}

// ===========================================================================
// (10) round_span_invariant (span.rs:6638-6645) and the
// relative==None arm of SpanRound::round (span.rs:5354-5400): the
// skeleton consumers of the arith spine.
// ===========================================================================

/// The round_span_invariant result face: Some carries the full
/// from-invariant face at the rounded total; None is the exact
/// disjunction of the two upstream error arms -- the round-over
/// (round.rs:366-383, the practically unreachable label upstream
/// argues for, kept honest here) or the from-invariant non-fit
/// (span.rs:6643-6644).
pub open spec fn sr_round_inv_face(
    span: &Span,
    largest: Unit,
    increment: &Increment,
    mode: RoundMode,
    r: &Option<Span>,
) -> bool {
    let tot: int = sp_inv_total_nanos(span);
    let rt: int = rm_round_spec(mode, tot, inc_increment_nanos(increment));
    match r {
        Option::Some(sp2) => sp_from_inv_face(largest, rt, r),
        Option::None => (rt < sd_min_total_nanos() || rt > sd_max_total_nanos())
            || !sp_fid_fits(largest, rt),
    }
}

/// Origin Rust: fn round_span_invariant(span, largest, increment,
///     mode) -> Result<Span, Error> (span.rs:6638-6645; the two
///     debug_asserts are this fn's requires, prune 8).
pub(crate) exec fn sp_round_span_invariant(
    span: &Span,
    largest: Unit,
    increment: &Increment,
    mode: RoundMode,
) -> (r: Option<Span>)
    requires
        sp_field_inv(span),
        sp_unit_rank(largest) <= sp_unit_rank(Unit::Week),
        inc_inv(increment),
        sp_unit_rank(increment.unit) <= sp_unit_rank(Unit::Week),
        !(increment.unit is Year),
        !(increment.unit is Month),
    ensures
        sr_round_inv_face(span, largest, increment, mode, &r),
{
    // span.rs:6641: let dur = span.to_invariant_duration();
    let dur: SignedDuration = span.sp_to_invariant_duration();
    // span.rs:6642: let rounded = increment.round(mode, dur)?;
    let rounded: Option<SignedDuration> =
        increment.inc_round(mode, &dur);
    match rounded {
        Option::Some(d2) =>
            // span.rs:6643-6644: Span::from_invariant_duration(
            //     largest, rounded)
            Span::sp_from_invariant_duration(largest, &d2),
        Option::None => Option::None,
    }
}

/// The config face of the relative==None arm of SpanRound::round
/// (span.rs:5358-5391: the eff-largest ladder, Increment::for_span,
/// the largest<smallest check, the three
/// requires_relative_date_err checks, then round_span_invariant).
pub open spec fn sr_config_ok(cfg: &SpanRound, span: &Span) -> bool {
    let existing: Unit = sp_span_largest(span);
    let eff_largest: Unit = match cfg.largest {
        Option::Some(u) => u,
        Option::None => sp_unit_max(cfg.smallest, existing),
    };
    inc_for_span_ok(cfg.smallest, cfg.increment)
        && sp_unit_rank(eff_largest) >= sp_unit_rank(cfg.smallest)
        && !(sr_requires_relative_err(cfg.smallest))
        && (cfg.largest is None
            || !(sr_requires_relative_err(eff_largest)))
        && !(sr_requires_relative_err(existing))
}

/// The effective largest unit (span.rs:5358-5360: configured, else
/// the max of smallest and the span's own largest).
pub open spec fn sr_eff_largest(cfg: &SpanRound, span: &Span) -> Unit {
    match cfg.largest {
        Option::Some(u) => u,
        Option::None =>
            sp_unit_max(cfg.smallest, sp_span_largest(span)),
    }
}

/// The rounded total of the arm (the decision core evaluated on the
/// span's invariant total against the smallest-unit increment).
pub open spec fn sr_rt_total(cfg: &SpanRound, span: &Span) -> int {
    rm_round_spec(
        cfg.mode,
        sp_inv_total_nanos(span),
        (cfg.increment as int) * rm_unit_nanos(cfg.smallest),
    )
}

/// The full relative==None-arm result face.
pub open spec fn sr_round_none_face(
    cfg: &SpanRound,
    span: &Span,
    r: &Option<Span>,
) -> bool {
    let rt: int = sr_rt_total(cfg, span);
    match r {
        Option::Some(sp2) =>
            sr_config_ok(cfg, span)
                && sp_from_inv_face(sr_eff_largest(cfg, span), rt, r),
        Option::None =>
            !(sr_config_ok(cfg, span))
                || (rt < sd_min_total_nanos()
                    || rt > sd_max_total_nanos())
                || !sp_fid_fits(sr_eff_largest(cfg, span), rt),
    }
}

impl SpanRound {
    /// Origin Rust: fn round(&self, span: Span) -> Result<Span,
    ///     Error> (span.rs:5354-5400), translated at the
    ///     relative==None arm (the Some(relative) arms,
    ///     span.rs:5366-5384 relative.round, ride the clipped
    ///     relative pipeline; prune 6).
    pub(crate) exec fn round_no_relative(
        &self,
        span: &Span,
    ) -> (r: Option<Span>)
        requires
            sp_field_inv(span),
            sp_zero_sign_ok(span),
            sp_flags_ok(span),
        ensures
            sr_round_none_face(self, span, &r),
    {
        // span.rs:5358-5360
        let existing_largest: Unit = span.largest_unit();
        proof {
            // bridge the exec/unit-flag spelling to the spec twin
            let u1: Unit = existing_largest;
            assert(u1 == sp_span_largest(span));
        }
        let largest: Unit = match self.largest {
            Option::Some(u) => u,
            Option::None => sp_unit_max_exec(self.smallest, existing_largest),
        };
        // span.rs:5361: Increment::for_span(smallest, increment)?
        match Increment::for_span(self.smallest, self.increment) {
            Option::None => Option::None,
            Option::Some(inc) => {
                // span.rs:5362-5366: largest < smallest config error
                if sp_unit_rank_exec(self.smallest)
                    > sp_unit_rank_exec(largest)
                {
                    return Option::None;
                }
                // span.rs:5370-5378: the three relative guards
                if sp_unit_rank_exec(self.smallest)
                    >= sp_unit_rank_exec(Unit::Day)
                {
                    return Option::None;
                }
                if sr_largest_is_some(self.largest)
                    && sp_unit_rank_exec(largest)
                        >= sp_unit_rank_exec(Unit::Day)
                {
                    return Option::None;
                }
                if sp_unit_rank_exec(existing_largest)
                    >= sp_unit_rank_exec(Unit::Day)
                {
                    return Option::None;
                }
                proof {
                    // the assert!(max <= Unit::Week) lane
                    // (span.rs:5380): all three guards passed keep
                    // every unit at Hour or below.
                    assert(sp_unit_rank(largest) <= sp_unit_rank(Unit::Hour));
                    assert(sp_unit_rank(largest)
                        <= sp_unit_rank(Unit::Week));
                    assert(!(inc.unit is Year));
                    assert(!(inc.unit is Month));
                    assert(sp_unit_rank(inc.unit)
                        <= sp_unit_rank(Unit::Week));
                }
                sp_round_span_invariant(span, largest, &inc, self.mode)
            }
        }
    }

    /// The Some-only checked variant: on the configuration inputs
    /// the panels pin, the arm returns a span (each None lane of
    /// the ladder is refuted by the requires conjunction, so the
    /// unwraps are proven-Some arms rather than panic sites).
    pub(crate) exec fn round_no_relative_some(
        &self,
        span: &Span,
    ) -> (r: Span)
        requires
            sp_field_inv(span),
            sp_zero_sign_ok(span),
            sp_flags_ok(span),
            sr_config_ok(self, span),
            sp_unit_rank(self.smallest) <= sp_unit_rank(Unit::Hour),
            sd_min_total_nanos() <= sr_rt_total(self, span),
            sr_rt_total(self, span) <= sd_max_total_nanos(),
            sp_fid_fits(sr_eff_largest(self, span), sr_rt_total(self, span)),
        ensures
            sp_from_inv_face(
                sr_eff_largest(self, span),
                sr_rt_total(self, span),
                &Option::Some(r),
            ),
    {
        let existing_largest: Unit = span.largest_unit();
        proof {
            assert(existing_largest == sp_span_largest(span));
            let inc_ok: bool =
                inc_for_span_ok(self.smallest, self.increment);
            assert(inc_ok);
            assert(!(sr_requires_relative_err(self.smallest)));
            assert(sp_unit_rank(self.smallest) < sp_unit_rank(Unit::Day));
            assert(!(self.smallest is Year));
            assert(!(self.smallest is Month));
            let rt: int = sr_rt_total(self, span);
            assert(rt == rm_round_spec(
                self.mode,
                sp_inv_total_nanos(span),
                (self.increment as int) * rm_unit_nanos(self.smallest),
            ));
            assert(sd_min_total_nanos() <= rt && rt <= sd_max_total_nanos());
        }
        let largest: Unit = match self.largest {
            Option::Some(u) => u,
            Option::None => sp_unit_max_exec(self.smallest, existing_largest),
        };
        proof {
            assert(largest == sr_eff_largest(self, span));
            assert(sp_unit_rank(largest)
                >= sp_unit_rank(self.smallest));
            if self.largest is Some {
                assert(!(sr_requires_relative_err(largest)));
            }
        }
        let inc: Increment =
            match Increment::for_span(self.smallest, self.increment) {
                Option::Some(i) => i,
                Option::None => {
                    proof {
                        assert(false);
                    }
                    Increment {
                        unit: Unit::Nanosecond,
                        value: 1,
                    }
                }
            };
        proof {
            assert(inc.unit == self.smallest);
            assert(inc_inv(&inc));
            assert(sp_unit_rank(sr_eff_largest(self, span))
                >= sp_unit_rank(self.smallest));
        }
        if sp_unit_rank_exec(self.smallest)
            > sp_unit_rank_exec(largest)
        {
            proof {
                assert(false);
            }
            return Span::new();
        }
        if sp_unit_rank_exec(self.smallest)
            >= sp_unit_rank_exec(Unit::Day)
        {
            proof {
                assert(false);
            }
            return Span::new();
        }
        if sr_largest_is_some(self.largest)
            && sp_unit_rank_exec(largest)
                >= sp_unit_rank_exec(Unit::Day)
        {
            proof {
                assert(false);
            }
            return Span::new();
        }
        if sp_unit_rank_exec(existing_largest)
            >= sp_unit_rank_exec(Unit::Day)
        {
            proof {
                assert(false);
            }
            return Span::new();
        }
        proof {
            assert(sp_unit_rank(largest) <= sp_unit_rank(Unit::Hour));
            assert(!(largest is Year));
            assert(!(largest is Month));
            assert(sp_unit_rank(inc.unit) <= sp_unit_rank(Unit::Week));
        }
        match sp_round_span_invariant(span, largest, &inc, self.mode) {
            Option::Some(sp2) => sp2,
            Option::None => {
                proof {
                    assert(false);
                }
                Span::new()
            }
        }
    }
}


// Exec twins for the panel guards (exec mode cannot call spec fns,
// and enum pattern tests are spec-only in exec position).
exec fn inc_value_ok_exec(v: i64) -> (r: bool)
    ensures
        r <==> inc_value_ok(v),
{
    1 <= v && v <= 1_000_000_000
}

exec fn sr_unit_is_nano(u: Unit) -> (r: bool)
    ensures
        r <==> (u is Nanosecond),
{
    match u {
        Unit::Nanosecond => true,
        _ => false,
    }
}

exec fn sr_unit_is_day(u: Unit) -> (r: bool)
    ensures
        r <==> (u is Day),
{
    match u {
        Unit::Day => true,
        _ => false,
    }
}

exec fn sr_largest_is_some(o: Option<Unit>) -> (r: bool)
    ensures
        r <==> (o is Some),
{
    match o {
        Option::Some(_) => true,
        Option::None => false,
    }
}

// ===========================================================================
// (11) Witness panels: upstream doc examples and unit-test rows
// carried to exec asserts.
// ===========================================================================

/// The upstream Temporal decision-table rows (round.rs:877-1010,
/// a representative row set per mode) plus the ad-hoc HalfExpand
/// rows (round.rs:856-868).
exec fn rm_panel_decision_table()
{
    // Ceil (round.rs:877-889)
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, -15i128, 10);
    assert(v == -10);
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, -5i128, 10);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, 4, 10);
    assert(v == 10);
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, 5, 10);
    assert(v == 10);
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, 15, 10);
    assert(v == 20);
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, i128::MAX, 1);
    assert(v == i128::MAX);
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, i128::MAX, i128::MAX);
    assert(v == i128::MAX);
    // Floor (round.rs:908-919)
    let v: i128 = rm_round_by_i128(RoundMode::Floor, -15i128, 10);
    assert(v == -20);
    let v: i128 = rm_round_by_i128(RoundMode::Floor, -5i128, 10);
    assert(v == -10);
    let v: i128 = rm_round_by_i128(RoundMode::Floor, 4, 10);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::Floor, 15, 10);
    assert(v == 10);
    // Expand (round.rs:921-932)
    let v: i128 = rm_round_by_i128(RoundMode::Expand, -15i128, 10);
    assert(v == -20);
    let v: i128 = rm_round_by_i128(RoundMode::Expand, 4, 10);
    assert(v == 10);
    let v: i128 = rm_round_by_i128(RoundMode::Expand, 15, 10);
    assert(v == 20);
    // Trunc (round.rs:934-945)
    let v: i128 = rm_round_by_i128(RoundMode::Trunc, -15i128, 10);
    assert(v == -10);
    let v: i128 = rm_round_by_i128(RoundMode::Trunc, -5i128, 10);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::Trunc, 15, 10);
    assert(v == 10);
    // HalfCeil (round.rs:947-958)
    let v: i128 = rm_round_by_i128(RoundMode::HalfCeil, -15i128, 10);
    assert(v == -10);
    let v: i128 = rm_round_by_i128(RoundMode::HalfCeil, 5, 10);
    assert(v == 10);
    let v: i128 = rm_round_by_i128(RoundMode::HalfCeil, 15, 10);
    assert(v == 20);
    // HalfFloor (round.rs:960-971)
    let v: i128 = rm_round_by_i128(RoundMode::HalfFloor, -15i128, 10);
    assert(v == -20);
    let v: i128 = rm_round_by_i128(RoundMode::HalfFloor, 5, 10);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::HalfFloor, 15, 10);
    assert(v == 10);
    // HalfExpand (round.rs:973-984 + the ad-hoc rows :856-868)
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, -15i128, 10);
    assert(v == -20);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 5, 10);
    assert(v == 10);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 15, 10);
    assert(v == 20);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 20, 13);
    assert(v == 26);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 29, 60);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 30, 60);
    assert(v == 60);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 3, 7);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::HalfExpand, 4, 7);
    assert(v == 7);
    // HalfTrunc (round.rs:986-997)
    let v: i128 = rm_round_by_i128(RoundMode::HalfTrunc, -15i128, 10);
    assert(v == -10);
    let v: i128 = rm_round_by_i128(RoundMode::HalfTrunc, 5, 10);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::HalfTrunc, 15, 10);
    assert(v == 10);
    // HalfEven (round.rs:999-1010)
    let v: i128 = rm_round_by_i128(RoundMode::HalfEven, 5, 10);
    assert(v == 0);
    let v: i128 = rm_round_by_i128(RoundMode::HalfEven, 15, 10);
    assert(v == 20);
}

/// The saturation-clamp lane (round.rs:456-461): upstream's own
/// saturation-domain rows (round.rs:888-889, the two i128::MAX
/// ceil rows are already on the decision panel) plus one genuine
/// clamp-hitting row: a quantity a full step below the bound with a
/// half-width increment bumps the quotient to 2 and 2 * 2**126 ==
/// 2**127 leaves the range, so the ladder clamps at i128::MAX.
exec fn rm_panel_saturation_lane()
{
    let big: i128 = 170141183460469231731687303715884105727i128 - 3i128;
    let half_big: i128 = 85070591730234615865843651857942052864i128;
    let v: i128 = rm_round_by_i128(RoundMode::Ceil, big, half_big);
    assert(v == 170141183460469231731687303715884105727i128);
    proof {
        // the spec value at this corner: the decision core leaves
        // the machine range and rm_sat_mul picks the upper clamp
        // (2 * 2**126 == 2**127 > rm_i128_max())
        assert(2 * 85070591730234615865843651857942052864
            == 170141183460469231731687303715884105728);
        assert(rm_sat_mul_helper());
    }
}

spec fn rm_sat_mul_helper() -> bool {
    rm_sat_mul(2, 85070591730234615865843651857942052864)
        == 170141183460469231731687303715884105727
}

/// The Increment constructor rows (round.rs:470-852, representative
/// row set) plus the maximum-increment ground check
/// (round.rs:1015-1022).
exec fn inc_panel_ctor_rows()
{
    // for_span, Nanosecond arm (round.rs:473-480)
    let o: _ = Increment::for_span(Unit::Nanosecond, 500);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Nanosecond, 1);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Nanosecond, -1i64);
    assert(o is None);
    let o: _ = Increment::for_span(Unit::Nanosecond, 0);
    assert(o is None);
    let o: _ = Increment::for_span(Unit::Nanosecond, 7);
    assert(o is None);
    let o: _ = Increment::for_span(Unit::Nanosecond, 1_000);
    assert(o is None);
    let o: _ =
        Increment::for_span(Unit::Nanosecond, 9_223_372_036_854_775_807);
    assert(o is None);
    // for_span, Hour arm (round.rs:518-528)
    let o: _ = Increment::for_span(Unit::Hour, 6);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Hour, 12);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Hour, 15);
    assert(o is None);
    let o: _ = Increment::for_span(Unit::Hour, 24);
    assert(o is None);
    // for_span, calendar arms (round.rs:530-588)
    let o: _ = Increment::for_span(Unit::Day, 1);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Day, 100);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Week, 2_000_000);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Week, 1_000_000_000);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Week, 1_000_000_001);
    assert(o is None);
    let o: _ = Increment::for_span(Unit::Month, 300_000);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Year, 50_000);
    assert(o is Some);
    let o: _ = Increment::for_span(Unit::Year, 1_000_000_000);
    assert(o is Some);
    // for_datetime (round.rs:591-660): the Days == 1 dead arm
    let o: _ = Increment::for_datetime(Unit::Second, 15);
    assert(o is Some);
    let o: _ = Increment::for_datetime(Unit::Hour, 12);
    assert(o is Some);
    let o: _ = Increment::for_datetime(Unit::Day, 1);
    assert(o is None);
    let o: _ = Increment::for_datetime(Unit::Day, 7);
    assert(o is None);
    let o: _ = Increment::for_datetime(Unit::Week, 1);
    assert(o is None);
    // for_time (round.rs:662-731)
    let o: _ = Increment::for_time(Unit::Minute, 15);
    assert(o is Some);
    let o: _ = Increment::for_time(Unit::Day, 1);
    assert(o is None);
    // for_timestamp (round.rs:733-852)
    let o: _ = Increment::for_timestamp(Unit::Nanosecond, 500);
    assert(o is Some);
    let o: _ = Increment::for_timestamp(Unit::Nanosecond, 1_000);
    assert(o is Some);
    let o: _ = Increment::for_timestamp(Unit::Second, 3_600);
    assert(o is Some);
    let o: _ = Increment::for_timestamp(Unit::Second, 86_400);
    assert(o is Some);
    let o: _ = Increment::for_timestamp(Unit::Second, 1_000);
    assert(o is None);
    let o: _ = Increment::for_timestamp(Unit::Second, 86_401);
    assert(o is None);
    let o: _ = Increment::for_timestamp(Unit::Hour, 24);
    assert(o is Some);
    let o: _ = Increment::for_timestamp(Unit::Hour, 25);
    assert(o is None);
    let o: _ = Increment::for_timestamp(Unit::Day, 1);
    assert(o is None);
    // for_signed_duration (round.rs:73-87)
    let o: _ = Increment::for_signed_duration(Unit::Minute, 30);
    assert(o is Some);
    let o: _ = Increment::for_signed_duration(Unit::Day, 1);
    assert(o is None);
    // for_offset (round.rs:91-105)
    let o: _ = Increment::for_offset(Unit::Second, 30);
    assert(o is Some);
    let o: _ = Increment::for_offset(Unit::Minute, 15);
    assert(o is Some);
    let o: _ = Increment::for_offset(Unit::Hour, 12);
    assert(o is Some);
    let o: _ = Increment::for_offset(Unit::Day, 1);
    assert(o is None);
    // the maximum-increment ground (round.rs:1015-1022): week budget
    // times 1_000_000_000, computed by script (wall-48 discipline)
    let incw: Increment = Increment {
        unit: Unit::Week,
        value: 1_000_000_000,
    };
    assert(inc_inv(&incw));
    assert(
        inc_increment_nanos(&incw)
            == 604_800_000_000_000_000_000_000
    );
}

/// try_from_nanos_i128 rows (signed_duration.rs:1836-1844: the doc
/// example and the i128::MAX rejection).
exec fn sd_panel_try_from_nanos_rows()
{
    let o: _ = sd_try_from_nanos_i128(12_000_000_456);
    assert(o is Some);
    let o: _ =
        sd_try_from_nanos_i128(170141183460469231731687303715884105727i128);
    assert(o is None);
    // the exact i64-window edges: sd_min/sd_max_total_nanos convert
    // (both Some), one nanosecond beyond the upper edge does not
    let o: _ = sd_try_from_nanos_i128(-9223372036854775808999999999i128);
    assert(o is Some);
    let o: _ = sd_try_from_nanos_i128(9223372036854775807999999999i128);
    assert(o is Some);
    let edge: i128 = 9223372036854775807999999999i128 + 1i128;
    let o: _ = sd_try_from_nanos_i128(edge);
    assert(o is None);
}

/// The RoundMode doc example (round.rs:275-291): 1h59m rounds to 2h
/// under the default, and to 1h under Trunc.
exec fn sr_panel_doc_round_mode()
{
    let span1: Span = Span::new().hours(1).minutes(59);
    let cfgd: SpanRound = SpanRound::new().smallest(Unit::Hour);
    proof {
        assert(sp_inv_total_nanos(&span1) == 7_140_000_000_000int);
        assert(sr_eff_largest(&cfgd, &span1) is Hour);
        assert((cfgd.increment as int) * rm_unit_nanos(cfgd.smallest)
            == 3_600_000_000_000int);
        let rt: int = sr_rt_total(&cfgd, &span1);
        // decision core: 7140 = 1 x 3600 + 3540; tie/nearer: 2*3540 >
        // 3600, so HalfExpand bumps to 2 hours
        assert(2 * 3_540_000_000_000int > 3_600_000_000_000int);
        assert(sr_rt_total(&cfgd, &span1) == 7_200_000_000_000int);
        // config_ok: for_span(Hour, 1) -- 1 < 24, 24 % 1 == 0
        assert(inc_for_span_ok(Unit::Hour, 1));
        assert(sr_config_ok(&cfgd, &span1));
        assert(sd_min_total_nanos() <= 7_200_000_000_000int);
        assert(7_200_000_000_000int <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Hour, 7_200_000_000_000int));
    }
    let out1: Span = cfgd.round_no_relative_some(&span1);
    proof {
        // from-invariant face at 7200s: 2 hours, everything else 0
        assert(sp_fid_secs(7_200_000_000_000int) == 7_200int);
    }
    assert((out1.hours as int) == 2);
    assert(out1.minutes == 0);
    assert(out1.seconds == 0);
    assert(out1.sign is Positive);

    // The Trunc contrast (round.rs:283-288)
    let cfgt: SpanRound = cfgd.mode(RoundMode::Trunc);
    proof {
        assert(sp_inv_total_nanos(&span1) == 7_140_000_000_000int);
        assert(sr_rt_total(&cfgt, &span1) == 3_600_000_000_000int);
        assert(sr_config_ok(&cfgt, &span1));
        assert(sd_min_total_nanos() <= 3_600_000_000_000int);
        assert(3_600_000_000_000int <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Hour, 3_600_000_000_000int));
    }
    let out2: Span = cfgt.round_no_relative_some(&span1);
    assert((out2.hours as int) == 1);
    assert(out2.sign is Positive);
    // the config predicates (span.rs:5340-5352) on the same cfgs
let b1: bool = cfgd.rounding_may_change_span();
    assert(b1);
let b2: bool = SpanRound::new().rounding_may_change_span();
    assert(!b2);
let b3: bool = cfgd.rounding_calendar_only_may_change_span();
    assert(b3);
}

/// The SpanRound::smallest doc example (span.rs:4997-5001):
/// 15m46s rounds to 16 minutes.
exec fn sr_panel_doc_smallest()
{
    let span: Span = Span::new().minutes(15).seconds(46);
    let cfg: SpanRound = SpanRound::new().smallest(Unit::Minute);
    proof {
        assert(sp_inv_total_nanos(&span) == 946_000_000_000int);
        assert(sr_eff_largest(&cfg, &span) is Minute);
        assert((cfg.increment as int) * rm_unit_nanos(cfg.smallest)
            == 60_000_000_000int);
        // 946 = 15 x 60 + 46; 2*46 > 60: HalfExpand bumps to 16
        assert(sr_rt_total(&cfg, &span) == 960_000_000_000int);
        assert(inc_for_span_ok(Unit::Minute, 1));
        assert(sr_config_ok(&cfg, &span));
        assert(sd_min_total_nanos() <= 960_000_000_000int);
        assert(960_000_000_000int <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Minute, 960_000_000_000int));
    }
    let out: Span = cfg.round_no_relative_some(&span);
    assert((out.minutes as int) == 16);
    assert(out.sign is Positive);
}

/// The SpanRound::increment doc example (span.rs:5196-5211 in the
/// setter doc block; the row itself at the increment # Example:
/// span.rs:5218-5224): 4h2m30s with smallest Minute and increment 5
/// rounds the minutes to the nearest half-hour boundary.
exec fn sr_panel_doc_increment()
{
    let span: Span = Span::new()
        .hours(4)
        .minutes(2)
        .seconds(30);
    let cfg: SpanRound = SpanRound::new()
        .smallest(Unit::Minute)
        .increment(5);
    proof {
        assert(sp_inv_total_nanos(&span) == 14_550_000_000_000int);
        assert(sr_eff_largest(&cfg, &span) is Hour);
        assert((cfg.increment as int) * rm_unit_nanos(cfg.smallest)
            == 300_000_000_000int);
        // 14550 = 48 x 300 + 150; 2*150 == 300: the tie bumps to 49
        assert(sr_rt_total(&cfg, &span) == 14_700_000_000_000int);
        assert(inc_for_span_ok(Unit::Minute, 5));
        assert(sr_config_ok(&cfg, &span));
        assert(sd_min_total_nanos() <= 14_700_000_000_000int);
        assert(14_700_000_000_000int <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Hour, 14_700_000_000_000int));
    }
    let out: Span = cfg.round_no_relative_some(&span);
    assert((out.hours as int) == 4);
    assert((out.minutes as int) == 5);
    assert(out.seconds == 0);
    assert(out.sign is Positive);
}

/// The Span::round doc examples (span.rs:2183-2225):
/// 123_456_789_123_456_789 ns rounds to 34_294 hours by
/// Unit::Hour, and -- smallest Second, largest Hour --
/// re-balances-and-rounds to 34_293 hours 33 minutes 9 seconds.
exec fn sr_panel_doc_span_round()
{
    let span: Span = Span::new().nanoseconds(123_456_789_123_456_789);
    proof {
        assert(sp_inv_total_nanos(&span) == 123_456_789_123_456_789int);
    }
    // Row 1 (span.rs:2222-2225): round(Unit::Hour) == 34_294 hours
    let cfg: SpanRound = SpanRound::new().smallest(Unit::Hour);
    proof {
        // largest ladder: configured None, so max(Hour, span's own
        // largest) -- a pure-nanoseconds span carries Nanosecond.
        assert(sp_span_largest(&span) == Unit::Nanosecond);
        assert(sr_eff_largest(&cfg, &span) is Hour);
        assert((cfg.increment as int) * rm_unit_nanos(cfg.smallest)
            == 3_600_000_000_000int);
        // decision core at Hour: quotient 34293, remainder
        // 1_989_123_456_789; 2*rem > increment, so HalfExpand bumps
        lemma_fundamental_div_mod_converse(
            123_456_789_123_456_789int,
            3_600_000_000_000int,
            34293int,
            1_989_123_456_789int,
        );
        assert(2 * 1_989_123_456_789int > 3_600_000_000_000int);
        assert(sr_rt_total(&cfg, &span)
            == 123_458_400_000_000_000int);
        assert(inc_for_span_ok(Unit::Hour, 1));
        assert(sr_config_ok(&cfg, &span));
        assert(sd_min_total_nanos() <= 123_458_400_000_000_000int);
        assert(123_458_400_000_000_000int <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Hour, 123_458_400_000_000_000int));
    }
    let out: Span = cfg.round_no_relative_some(&span);
    assert((out.hours as int) == 34294);
    assert((out.minutes as int) == 0);
    assert(out.seconds == 0);
    assert(out.sign is Positive);

    // Row 2 (span.rs:2209-2217): largest Hour, smallest Second ->
    // 34_293 hours 33 minutes 9 seconds (the 789 ns remainder rounds
    // off toward zero).
    let cfg2: SpanRound =
        SpanRound::new().largest(Unit::Hour).smallest(Unit::Second);
    proof {
        assert(sr_eff_largest(&cfg2, &span) is Hour);
        assert((cfg2.increment as int) == 1int);
        assert(cfg2.smallest is Second);
        assert(cfg2.smallest == Unit::Second);
        assert(rm_unit_nanos(cfg2.smallest)
            == rm_unit_nanos(Unit::Second));
        assert(rm_unit_nanos(Unit::Second) == 1_000_000_000int);
        assert((cfg2.increment as int) * rm_unit_nanos(cfg2.smallest)
            == 1_000_000_000int);
        // decision core at Second: quotient 123_456_789, remainder
        // 123_456_789; 2*rem < increment, so no bump (the subsecond
        // remainder drops toward zero)
        lemma_fundamental_div_mod_converse(
            123_456_789_123_456_789int,
            1_000_000_000int,
            123_456_789int,
            123_456_789int,
        );
        assert(2 * 123_456_789int < 1_000_000_000int);
        assert(rm_mag(123_456_789_123_456_789int)
            == 123_456_789_123_456_789int);
        assert(rm_mag(123_456_789_123_456_789int)
            % 1_000_000_000int
            == 123_456_789int);
        assert(123_456_789int * 1_000_000_000int
            == 123_456_789_000_000_000int);
        assert(sr_rt_total(&cfg2, &span)
            == 123_456_789_000_000_000int);
        assert(inc_for_span_ok(Unit::Second, 1));
        assert(sr_config_ok(&cfg2, &span));
        assert(sd_min_total_nanos() <= 123_456_789_000_000_000int);
        assert(123_456_789_000_000_000int <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Hour, 123_456_789_000_000_000int));
    }
    let out2: Span = cfg2.round_no_relative_some(&span);
    assert((out2.hours as int) == 34293);
    assert((out2.minutes as int) == 33);
    assert((out2.seconds as int) == 9);
    assert(out2.sign is Positive);
}

} // verus!
