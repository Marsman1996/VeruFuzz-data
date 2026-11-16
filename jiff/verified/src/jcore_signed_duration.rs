//! jiff 0.2.43 SignedDuration arithmetic core
//! (crates/jiff/src/signed_duration.rs, 3409 lines, pin tree read-only) --
//! Verus translation, batch J4b.
//!
//! Scope: the arithmetic heart of `SignedDuration` -- the `new`
//! seconds/nanosecond carry normalization (with its sign harmonization),
//! the from_* constructors and their as_* inverses, the subsec accessors,
//! sign predicates, abs/checked_neg, the checked_add/checked_sub/
//! checked_mul family, the saturating_* variants, and the core::ops
//! faces (Neg/Add/Sub/AddAssign/SubAssign/Mul<i32>/MulAssign<i32>,
//! all as free functions -- the J4 ops precedent).
//!
//! Driver mount: `verified/j4b-driver.rs` mounts this file via #[path].
//! This file is fully self-contained (the J4 inline-materialization
//! precedent): the upstream time-unit constants (signed_duration.rs:20-28)
//! are re-declared here; it needs nothing from J1's bounds.rs / lib.rs,
//! J2's date.rs, or J4's jcore_timestamp.rs (SignedDuration and Timestamp
//! do not interact inside this file's translated surface), so the driver
//! mounts this file alone.
//!
//! Canonical form doctrine (file-wide):
//! - Upstream's struct invariant (signed_duration.rs:30-40, the type doc:
//!   "it is guaranteed that the signs of as_secs and subsec_nanos are
//!   always the same, or one component is zero") is codified as sd_inv
//!   below and -- unlike the J4 Timestamp case -- is FULLY preservable
//!   here: MIN = {i64::MIN, -999_999_999} is itself canonical (negative
//!   nanos on the minimal second are allowed), so there is no
//!   min-second exception tier. Every translated constructor establishes
//!   sd_inv, and every checked_* -> Some result keeps it.
//!
//! Panic face model (file-wide):
//! - The upstream reachable panic inside the carry branch of
//!   SignedDuration::new (signed_duration.rs:410-414,
//!   "nanoseconds overflowed seconds in SignedDuration::new") is
//!   transcribed faithfully as a panic via an external-body helper
//!   (the verus core panic spec assumes non-reachability; `-> !` gives
//!   callers honest divergence). Its reachability domain is carried by
//!   the spec fn sd_new_panic_face and proven nonempty by
//!   sd_audit_point_a_witness below (AUDIT POINT A).
//! - Same treatment (external body, real upstream panic site) for
//!   SignedDuration::abs on i64::MIN (signed_duration.rs:1925, the
//!   doc's own # Panics) and for the from_hours/from_mins # Panics
//!   faces (signed_duration.rs:749-759, :783-793).
//! - The core::ops impls upstream panic via .expect on the checked
//!   variants (signed_duration.rs:2603-2653); their translated faces add
//!   domain excluder requires and route the (now unreachable) failure
//!   arms through the dead-arm helper -- the honest note is that verus
//!   does not itself prove the excluder's sufficiency; the upstream
//!   panic text is preserved in the excluder documentation.
//!
//! Translation faces (toolchain doctrine, J1/J4 notes):
//! - exec machine `/` and `%` are Rust trunc; they lower to
//!   vstd::arithmetic::div_mod::rust_div/rust_rem, reasoned in proof
//!   blocks against those fns. Spec-position machine `/`/`%` would be
//!   Euclidean, so spec clauses only ever use rust_div/rust_rem.
//! - Variable-times-variable products are never self-evident; the
//!   product bound in checked_mul is discharged with explicit ground
//!   asserts (with the vstd::arithmetic::mul lemma family when the
//!   solver does not reduce ground products on its own).
//! - checked_add/checked_mul/checked_neg builtin specs carry the full
//!   None negative-information face; verbatim match arms verify.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{rust_div, rust_rem};
use vstd::arithmetic::mul::{
    lemma_mul_by_zero_is_zero, lemma_mul_cancels_negatives,
    lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add_other_way, lemma_mul_nonzero,
    lemma_mul_nonnegative, lemma_mul_strictly_positive,
    lemma_mul_unary_negation, lemma_mul_upper_bound,
};

verus! {

// ===========================================================================
// Time-unit constants (Origin signed_duration.rs:20-28, "We define our own
// constants here instead of using `jcore` to try and make things a little
// more self-contained here.")
// ===========================================================================

pub const NANOS_PER_SEC: i32 = 1_000_000_000;
pub const NANOS_PER_MILLI: i32 = 1_000_000;
pub const NANOS_PER_MICRO: i32 = 1_000;
pub const MILLIS_PER_SEC: i64 = 1_000;
pub const MICROS_PER_SEC: i64 = 1_000_000;
pub const SECS_PER_MINUTE: i64 = 60;
pub const MINS_PER_HOUR: i64 = 60;

// ===========================================================================
// Origin Rust: pub struct SignedDuration { secs: i64, nanos: i32 }
//     (signed_duration.rs:324-328)
// (Fields pub: harness-facing translation, the J4 Timestamp precedent;
//  upstream keeps them private.)
// ===========================================================================

pub struct SignedDuration {
    pub secs: i64,
    pub nanos: i32,
}

// ---------------------------------------------------------------------------
// Spec predicates. Comparisons live on int; machine values are cast at the
// boundary (the spec-side promotion doctrine).
// ---------------------------------------------------------------------------

/// The sub-second nanosecond domain: |nanos| <= 999_999_999 (the
/// new_unchecked debug tier, signed_duration.rs:472-473).
pub open spec fn sd_nanos_ok(n: i32) -> bool {
    -999_999_999 <= n && n <= 999_999_999
}

/// The total nanoseconds denoted by a duration (unbounded int).
pub open spec fn sd_total_nanos(d: &SignedDuration) -> int {
    (d.secs as int) * 1_000_000_000 + (d.nanos as int)
}

/// Sign harmonization (type doc, signed_duration.rs:30-40; the
/// new_unchecked debug_assert, signed_duration.rs:474-478): secs and
/// nanos signs agree, or one component is zero.
pub open spec fn sd_signs_agree(d: &SignedDuration) -> bool {
    d.nanos == 0
        || d.secs == 0
        || (d.secs > 0 && d.nanos > 0)
        || (d.secs < 0 && d.nanos < 0)
}

/// The full upstream canonical form (there is no min-second exception:
/// MIN itself is canonical -- see the file-head note).
pub open spec fn sd_inv(d: &SignedDuration) -> bool {
    sd_nanos_ok(d.nanos) && sd_signs_agree(d)
}

/// sd_total_nanos(MIN), as a spec fn (exec min_value()'s twin for use
/// inside contracts).
pub open spec fn sd_min_total_nanos() -> int {
    -(9223372036854775808int) * 1_000_000_000 - 999_999_999
}

/// sd_total_nanos(MAX), as a spec fn.
pub open spec fn sd_max_total_nanos() -> int {
    9223372036854775807int * 1_000_000_000 + 999_999_999
}

/// Spec twin of SignedDuration::signum (int face; the exec method
/// returns i8) -- only used inside contracts.
pub open spec fn sd_signum_spec(d: &SignedDuration) -> int {
    if d.secs == 0 && d.nanos == 0 {
        0
    } else if d.secs > 0 || d.nanos > 0 {
        1
    } else {
        -1
    }
}

/// Spec twin of i32::signum (for the saturating_mul selector face).
pub open spec fn sd_i32_signum_spec(v: i32) -> int {
    if v > 0 {
        1
    } else if v == 0 {
        0
    } else {
        -1
    }
}

// ===========================================================================
// Panic faces (external bodies; see the file-head model note).
// ===========================================================================

/// Faithful transcription of the upstream reachable panic inside the
/// carry branch of SignedDuration::new (signed_duration.rs:410-414):
/// `secs.checked_add(addsecs as i64)` on None panics
/// "nanoseconds overflowed seconds in SignedDuration::new".
/// Reachable domain proven by sd_audit_point_a_witness below
/// (AUDIT POINT A: the doc claim "This never panics when `nanos` is
/// less than `1_000_000_000`" (signed_duration.rs:385) is FALSE --
/// nanos <= -1_000_000_000 also carries, e.g. nanos = i32::MIN).
#[verifier::external_body]
pub fn upstream_new_carry_panic() -> ! {
    panic!("nanoseconds overflowed seconds in SignedDuration::new");
}

/// Faithful transcription of the upstream panic site of abs
/// (signed_duration.rs:1925, `self.secs.abs()` on i64::MIN -- the
/// Rust core overflow panic; the doc's own # Panics,
/// signed_duration.rs:1910-1913).
#[verifier::external_body]
pub fn upstream_abs_min_secs_panic() -> ! {
    panic!("attempt to negate with overflow");
}

/// Faithful transcription of the from_hours panic face
/// (signed_duration.rs:749-759, # Panics + message "hours overflowed
/// an `i64` number of seconds in `SignedDuration::from_hours`").
#[verifier::external_body]
pub fn upstream_from_hours_panic() -> ! {
    panic!(
        "hours overflowed an `i64` number of seconds \
         in `SignedDuration::from_hours`"
    );
}

/// Faithful transcription of the from_mins panic face
/// (signed_duration.rs:783-793, # Panics mirrors from_hours; message
/// "minutes overflowed an `i64` number of seconds in
/// `SignedDuration::from_mins`").
#[verifier::external_body]
pub fn upstream_from_mins_panic() -> ! {
    panic!(
        "minutes overflowed an `i64` number of seconds \
         in `SignedDuration::from_mins`"
    );
}

/// Translation-only filler for match arms the enclosing requires has
/// killed (the J4 j4_dead_arm_unreachable precedent; the
/// upstream_*_panic helpers above transcribe panics that CAN execute).
#[verifier::external_body]
pub fn j4b_dead_arm_unreachable() -> ! {
    panic!("jiff J4b translation: dead match arm reached (contradiction with requires)");
}

// ===========================================================================
// AUDIT POINT A -- the doc face of SignedDuration::new (signed_duration.rs
// :379-385):
///   # Panics
///   When the absolute value of the nanoseconds is greater than or equal
///   to 1 second and the excess that carries over to the number of whole
///   seconds overflows `i64`.
///   This never panics when `nanos` is less than `1_000_000_000`.
///
/// The second sentence is the audited claim. Its truth would be
///
///     nanos < 1_000_000_000  ==>  !sd_new_panic_face(secs, nanos)
///
/// which is FALSE: the carry branch fires for nanos <= -1_000_000_000
/// too (the negated guard is !(nanos > -1e9 && nanos < 1e9)), and there
/// addsecs = trunc(nanos/1e9) can be -2, pushing secs + addsecs below
/// i64::MIN.
// ===========================================================================

/// The exact reachability domain of the translated carry-branch panic:
/// |nanos| >= 1 second AND secs + trunc(nanos/1e9) does not fit in i64.
pub open spec fn sd_new_panic_face(secs: int, nanos: int) -> bool {
    (nanos <= -(1_000_000_000int) || nanos >= 1_000_000_000int)
        && !((-(9223372036854775808int))
            <= secs + rust_div(nanos, 1_000_000_000)
            && secs + rust_div(nanos, 1_000_000_000)
                <= 9223372036854775807int)
}

/// Verus-verified witness that the panic face is reachable on an input
/// with nanos < 1_000_000_000 -- i.e. the doc sentence
/// "This never panics when nanos is less than 1_000_000_000"
/// (signed_duration.rs:385) is falsified. Concrete runtime transcription
/// for a PoC, exactly these arguments:
///     SignedDuration::new(-9_223_372_036_854_775_807, -2_147_483_648)
///         // secs = i64::MIN + 1, nanos = i32::MIN
///         // carry on |nanos| >= 1e9:
///         //   addsecs = i32::MIN / 1_000_000_000 = -2 (trunc)
///         //   secs + addsecs = i64::MIN + 1 - 2 < i64::MIN -> panic!()
pub exec fn sd_audit_point_a_witness() -> (doc_claim_falsified: bool)
    ensures
        doc_claim_falsified,
        // The falsifying input, as spec facts:
        sd_new_panic_face(
            -(9223372036854775808int) + 1,
            -(2147483648int),
        ),
        -(2147483648int) < 1_000_000_000int,
{
    let secs: i64 = i64::MIN + 1;
    let nanos: i32 = i32::MIN;
    // The carry branch is taken (exec trunc division reproduces
    // upstream's addsecs verbatim).
    let addsecs: i32 = nanos / NANOS_PER_SEC;
    assert(addsecs == -2);
    let opt = secs.checked_add(addsecs as i64);
    let none: bool = match opt {
        Option::None => true,
        Option::Some(_) => false,
    };
    assert(none);
    assert(sd_new_panic_face(
        (secs as int),
        (nanos as int),
    ));
    assert((nanos as int) < 1_000_000_000);
    true
}

// ---------------------------------------------------------------------------
// Translation-only sign-decomposition helpers (nonlinear facts z3 does
// not find on its own: the product's sign encodes the operand signs).
// ---------------------------------------------------------------------------

/// y*r > 0  ==>  (y>0 && r>0) || (y<0 && r<0).
proof fn sd_mul_pos_sign(y: int, r: int)
    requires
        y * r > 0,
    ensures
        (y > 0 && r > 0) || (y < 0 && r < 0),
{
    if y == 0 {
        lemma_mul_by_zero_is_zero(r);
        assert(y * r == 0);
        assert(false);
    } else if r == 0 {
        lemma_mul_by_zero_is_zero(y);
        assert(y * r == 0);
        assert(false);
    } else if y > 0 {
        if r < 0 {
            lemma_mul_strictly_positive(y, -r);
            lemma_mul_unary_negation(y, r);
            assert(y * r < 0);
            assert(false);
        }
    } else {
        // y < 0
        if r > 0 {
            lemma_mul_strictly_positive(-y, r);
            lemma_mul_unary_negation(y, r);
            assert(-(y * r) > 0);
            assert(y * r < 0);
            assert(false);
        }
    }
}

/// y*r < 0  ==>  (y>0 && r<0) || (y<0 && r>0).
proof fn sd_mul_neg_sign(y: int, r: int)
    requires
        y * r < 0,
    ensures
        (y > 0 && r < 0) || (y < 0 && r > 0),
{
    if y == 0 {
        lemma_mul_by_zero_is_zero(r);
        assert(y * r == 0);
        assert(false);
    } else if r == 0 {
        lemma_mul_by_zero_is_zero(y);
        assert(y * r == 0);
        assert(false);
    } else if y > 0 {
        if r > 0 {
            lemma_mul_strictly_positive(y, r);
            assert(false);
        }
        // r < 0: the ensured disjunct holds.
    } else {
        // y < 0
        if r < 0 {
            lemma_mul_cancels_negatives(y, r);
            lemma_mul_strictly_positive(-y, -r);
            assert(false);
        }
        // r > 0: the ensured disjunct holds.
    }
}

// ===========================================================================
// impl SignedDuration { (signed_duration.rs:330-2063)
// ===========================================================================

impl SignedDuration {

    /// Origin Rust: pub const ZERO: SignedDuration =
    ///     SignedDuration { secs: 0, nanos: 0 } (signed_duration.rs:343)
    /// Upstream doc (signed_duration.rs:331-334):
    ///   A duration of zero time.
    pub exec fn zero() -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            d.secs == 0,
            d.nanos == 0,
            sd_total_nanos(&d) == 0,
    {
        SignedDuration { secs: 0, nanos: 0 }
    }

    /// Origin Rust: pub const MIN: SignedDuration =
    ///     SignedDuration { secs: i64::MIN, nanos: -(NANOS_PER_SEC - 1) }
    ///     (signed_duration.rs:356-357)
    /// Upstream doc (signed_duration.rs:345-347):
    ///   The minimum possible duration. Or the "most negative" duration.
    /// Upstream doc examples (signed_duration.rs:352-354) pin the exact
    /// faces: as_secs() == i64::MIN and subsec_nanos() == -999_999_999
    /// -- both carried below. Note the canonical nanos on MIN are
    /// NEGATIVE (unlike Timestamp's nonnegative canonical form).
    pub exec fn min_value() -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            d.secs == i64::MIN,
            d.nanos == -999_999_999,
            sd_total_nanos(&d) == sd_min_total_nanos(),
    {
        SignedDuration { secs: i64::MIN, nanos: -(NANOS_PER_SEC - 1) }
    }

    /// Origin Rust: pub const MAX: SignedDuration =
    ///     SignedDuration { secs: i64::MAX, nanos: NANOS_PER_SEC - 1 }
    ///     (signed_duration.rs:370-371)
    /// Upstream doc (signed_duration.rs:359-361):
    ///   The maximum possible duration.
    /// Upstream doc examples (signed_duration.rs:366-368): as_secs() ==
    ///   i64::MAX and subsec_nanos() == 999_999_999.
    pub exec fn max_value() -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            d.secs == i64::MAX,
            d.nanos == 999_999_999,
            sd_total_nanos(&d) == sd_max_total_nanos(),
    {
        SignedDuration { secs: i64::MAX, nanos: NANOS_PER_SEC - 1 }
    }

    /// Origin Rust: pub(crate) const fn new_unchecked(secs: i64,
    ///     nanos: i32) -> SignedDuration (signed_duration.rs:468-480)
    /// Upstream doc (signed_duration.rs:455-466):
    ///   Creates a new signed duration without handling nanosecond
    ///   overflow or sign differences.
    ///   This might produce tighter code in some cases.
    ///   Note that this should not be made public *and* safe.
    ///   # Panics
    ///   In debug mode only, when |nanos| is greater than or equal to 1
    ///   second. Or when both secs and nanos are non-zero and their
    ///   signs mismatch.
    /// (The three debug_assert!s of the body, signed_duration.rs:472-478,
    ///  are this translation's requires -- upstream debug tier -> spec
    ///  tier; their conjunction is sd_inv.)
    pub(crate) exec fn new_unchecked(secs: i64, nanos: i32) -> (d: SignedDuration)
        requires
            -999_999_999 <= nanos,
            nanos <= 999_999_999,
            nanos == 0
                || secs == 0
                || (secs > 0 && nanos > 0)
                || (secs < 0 && nanos < 0),
        ensures
            sd_inv(&d),
            d.secs == secs,
            d.nanos == nanos,
            sd_total_nanos(&d) == (secs as int) * 1_000_000_000 + (nanos as int),
    {
        SignedDuration { secs, nanos }
    }

    /// Origin Rust: pub const fn new(mut secs: i64, mut nanos: i32)
    ///     -> SignedDuration (signed_duration.rs:405-453)
    /// Upstream doc (signed_duration.rs:373-403):
    ///   Creates a new SignedDuration from the given number of whole
    ///   seconds and additional nanoseconds.
    ///   If the absolute value of the nanoseconds is greater than or equal
    ///   to 1 second, then the excess balances into the number of whole
    ///   seconds.
    ///   # Panics
    ///   When the absolute value of the nanoseconds is greater than or
    ///   equal to 1 second and the excess that carries over to the number
    ///   of whole seconds overflows i64.
    ///   This never panics when nanos is less than 1_000_000_000.
    /// SPEC-DOC MISMATCH candidate J4b-1 (suspects list, notes.md; not
    /// self-filed): the last doc sentence is FALSE -- falsified by
    /// sd_audit_point_a_witness above (nanos = i32::MIN is "less than
    /// 1_000_000_000", lands in the carry branch, and with
    /// secs = i64::MIN + 1 the checked_add overflows). The ensures
    /// below states the preservable face: on every return the value is
    /// canonical and instant-preserving. The panic domain is
    /// sd_new_panic_face, proven reachable.
    /// Upstream doc examples (signed_duration.rs:392-402): new(12, 0) =
    ///   (12, 0); new(12, -1) = (11, 999_999_999);
    ///   new(12, 1_000_000_000) = (13, 0) -- all carried by the
    ///   canonical + instant-preserving postcondition.
    pub exec fn new(secs_in: i64, nanos_in: i32) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            sd_total_nanos(&d)
                == (secs_in as int) * 1_000_000_000 + (nanos_in as int),
    {
        let mut secs: i64 = secs_in;
        let mut nanos: i32 = nanos_in;
        // When |nanos| exceeds 1 second, balance the excess up to seconds
        // (signed_duration.rs:407-418).
        if !(-NANOS_PER_SEC < nanos && nanos < NANOS_PER_SEC) {
            // Upstream safety comment (signed_duration.rs:408): "Never
            // wraps or panics because NANOS_PER_SEC!={0,-1}." -- the
            // trunc division below is reasoned through rust_div.
            let addsecs: i32 = nanos / NANOS_PER_SEC;
            // Upstream panic site (signed_duration.rs:410-414):
            // reachable on e.g. new(i64::MIN+1, i32::MIN) --
            // sd_audit_point_a_witness; transcribed faithfully.
            let opt = secs.checked_add(addsecs as i64);
            secs = match opt {
                Option::Some(v) => v,
                Option::None => upstream_new_carry_panic(),
            };
            // Upstream safety comment (signed_duration.rs:416): "Never
            // wraps or panics because NANOS_PER_SEC!={0,-1}."
            nanos = nanos % NANOS_PER_SEC;
            proof {
                let v = 1_000_000_000int;
                let q = rust_div((nanos_in as int), v);
                let r = rust_rem((nanos_in as int), v);
                assert((addsecs as int) == q);
                assert((nanos as int) == r);
                assert((nanos_in as int) == q * v + r);
                assert(r > -v && r < v);
                assert(-(999_999_999int) <= r && r <= 999_999_999);
                assert((secs as int) == (secs_in as int) + q);
                // The prebalance is instant-preserving.
                assert((secs_in as int) * v + (nanos_in as int)
                    == (secs as int) * v + r);
                assert(sd_nanos_ok(nanos));
            }
        } else {
            proof {
                assert(sd_nanos_ok(nanos_in));
            }
        }
        // Fast path (signed_duration.rs:421-424): done if either unit is
        // zero or they have the same sign (the original signum
        // comparison spelled as sign equality of the nonzero case).
        if nanos == 0 || secs == 0 || (secs > 0) == (nanos > 0) {
            return SignedDuration::new_unchecked(secs, nanos);
        }
        // Balance negative nanos into positive seconds, or positive
        // nanos into negative seconds (signed_duration.rs:427-451).
        if secs < 0 {
            // At this point secs < 0 and nanos > 0.
            // Upstream safety comment (signed_duration.rs:429): "Never
            // wraps because adding +1 to a negative i64 never overflows."
            proof {
                assert((secs as int) < 0);
                assert(1 <= nanos as int);
                assert((nanos as int) <= 999_999_999);
            }
            secs = secs + 1;
            // Upstream safety comment (signed_duration.rs:433-434):
            // "Never wraps because subtracting +1_000_000_000 from a
            // positive i32 never overflows."
            nanos = nanos - NANOS_PER_SEC;
            proof {
                assert((secs as int) <= 0);
                assert(-(999_999_999int) <= nanos as int);
                assert((nanos as int) <= -1);
                // Instant-preserving rebalance.
                assert((secs as int) * 1_000_000_000 + (nanos as int)
                    == (secs_in as int) * 1_000_000_000 + (nanos_in as int));
            }
        } else {
            // At this point secs > 0 and nanos < 0.
            // Upstream safety comment (signed_duration.rs:441-442):
            // "Never wraps because subtracting +1 from a positive i64
            // never overflows."
            proof {
                assert((secs as int) > 0);
                assert(-(999_999_999int) <= nanos as int);
                assert((nanos as int) <= -1);
            }
            secs = secs - 1;
            // Upstream safety comment (signed_duration.rs:446-447):
            // "Never wraps because adding +1_000_000_000 to a negative
            // i32 never overflows."
            nanos = nanos + NANOS_PER_SEC;
            proof {
                assert((secs as int) >= 0);
                assert(1 <= nanos as int);
                assert((nanos as int) <= 999_999_999);
                assert((secs as int) * 1_000_000_000 + (nanos as int)
                    == (secs_in as int) * 1_000_000_000 + (nanos_in as int));
            }
        }
        SignedDuration::new_unchecked(secs, nanos)
    }

    /// Origin Rust: pub const fn from_secs(secs: i64) -> SignedDuration
    ///     (signed_duration.rs:494-496)
    /// Upstream doc (signed_duration.rs:482-492):
    ///   Creates a new SignedDuration from the given number of whole
    ///   seconds.
    /// Upstream doc example (signed_duration.rs:489-491):
    ///   from_secs(12).as_secs() == 12, subsec_nanos() == 0.
    pub exec fn from_secs(secs: i64) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            d.secs == secs,
            d.nanos == 0,
            sd_total_nanos(&d) == (secs as int) * 1_000_000_000,
    {
        SignedDuration::new_unchecked(secs, 0)
    }

    /// Origin Rust: pub const fn from_millis(millis: i64) -> SignedDuration
    ///     (signed_duration.rs:520-528)
    /// Upstream doc (signed_duration.rs:498-518):
    ///   Creates a new SignedDuration from the given number of whole
    ///   milliseconds.
    ///   Note that since this accepts an i64, this method cannot be used
    ///   to construct the full range of possible signed duration values.
    ///   In particular, SignedDuration::as_millis returns an i128, and
    ///   this may be a value that would otherwise overflow an i64.
    /// Upstream doc examples (signed_duration.rs:511-517):
    ///   from_millis(12_456) = (12, 456_000_000);
    ///   from_millis(-12_456) = (-12, -456_000_000) -- carried by the
    ///   canonical + instant-preserving postcondition.
    pub exec fn from_millis(millis: i64) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            sd_total_nanos(&d) == (millis as int) * 1_000_000,
    {
        // Upstream safety comment (signed_duration.rs:521): "OK because
        // MILLIS_PER_SEC!={-1,0}."
        let secs: i64 = millis / MILLIS_PER_SEC;
        // Upstream safety comment (signed_duration.rs:523-526): "OK
        // because MILLIS_PER_SEC!={-1,0} and because
        // millis % MILLIS_PER_SEC can be at most 999, and 999 * 1_000_000
        // never overflows i32."
        let rem: i64 = millis % MILLIS_PER_SEC;
        let nanos: i32 = (rem as i32) * NANOS_PER_MILLI;
        proof {
            let dd = 1_000int;
            let q = (secs as int);
            let r = (rem as int);
            assert(q == rust_div((millis as int), dd));
            assert(r == rust_rem((millis as int), dd));
            assert((millis as int) == q * dd + r);
            assert(r > -dd && r < dd);
            assert(-(999int) <= r && r <= 999);
            assert(sd_nanos_ok(nanos));
            // Trunc remainder sign coupling (rust_rem case def): the
            // nanos carry moves with the sign of millis, so the pair
            // harmonizes (or one component is zero).
            if r < 0 {
                assert((millis as int) < 0);
                assert(q <= 0);
                assert(nanos < 0);
            }
            if r > 0 {
                assert((millis as int) > 0);
                assert(q >= 0);
                assert(nanos > 0);
            }
            if r == 0 {
                assert(nanos == 0);
            }
        }
        SignedDuration::new_unchecked(secs, nanos)
    }

    /// Origin Rust: pub const fn from_micros(micros: i64) -> SignedDuration
    ///     (signed_duration.rs:596-604)
    /// Upstream doc (signed_duration.rs:574-594):
    ///   Creates a new SignedDuration from the given number of whole
    ///   microseconds.
    ///   Note that since this accepts an i64, this method cannot be used
    ///   to construct the full range of possible signed duration values.
    ///   In particular, SignedDuration::as_micros returns an i128, and
    ///   this may be a value that would otherwise overflow an i64.
    /// Upstream doc examples (signed_duration.rs:587-593):
    ///   from_micros(12_000_456) = (12, 456_000);
    ///   from_micros(-12_000_456) = (-12, -456_000).
    /// (Same safety-comment shape as from_millis: the trunc remainder per
    ///  second is in (-1_000_000, 1_000_000) and the product by
    ///  NANOS_PER_MICRO = 1_000 stays inside the subsec bound.)
    pub exec fn from_micros(micros: i64) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            sd_total_nanos(&d) == (micros as int) * 1_000,
    {
        // Upstream safety comment (signed_duration.rs:597): "OK because
        // MICROS_PER_SEC!={-1,0}."
        let secs: i64 = micros / MICROS_PER_SEC;
        // Upstream safety comment (signed_duration.rs:599-601): "OK
        // because MICROS_PER_SEC!={-1,0} and because
        // micros % MICROS_PER_SEC can be at most 999_999, and 999_999 *
        // 1_000 never overflows i32."
        let rem: i64 = micros % MICROS_PER_SEC;
        let nanos: i32 = (rem as i32) * NANOS_PER_MICRO;
        proof {
            let dd = 1_000_000int;
            let q = (secs as int);
            let r = (rem as int);
            assert(q == rust_div((micros as int), dd));
            assert(r == rust_rem((micros as int), dd));
            assert((micros as int) == q * dd + r);
            assert(-(999_999int) <= r && r <= 999_999);
            assert(sd_nanos_ok(nanos));
            if r < 0 {
                assert((micros as int) < 0);
                assert(q <= 0);
                assert(nanos < 0);
            }
            if r > 0 {
                assert((micros as int) > 0);
                assert(q >= 0);
                assert(nanos > 0);
            }
            if r == 0 {
                assert(nanos == 0);
            }
        }
        SignedDuration::new_unchecked(secs, nanos)
    }

    /// Origin Rust: pub const fn from_nanos(nanos: i64) -> SignedDuration
    ///     (signed_duration.rs:674-681)
    /// Upstream doc (signed_duration.rs:650-672):
    ///   Creates a new SignedDuration from the given number of whole
    ///   nanoseconds.
    ///   Note that since this accepts an i64, this method cannot be used
    ///   to construct the full range of possible signed duration values.
    ///   In particular, SignedDuration::as_nanos returns an i128, which
    ///   may be a value that would otherwise overflow an i64. To correctly
    ///   round-trip through an integer number of nanoseconds, use
    ///   SignedDuration::from_nanos_i128.
    /// Upstream doc examples (signed_duration.rs:665-671):
    ///   from_nanos(12_000_000_456) = (12, 456);
    ///   from_nanos(-12_000_000_456) = (-12, -456).
    pub exec fn from_nanos(nanos: i64) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            sd_total_nanos(&d) == (nanos as int),
    {
        const NANOS_PER_SEC_64: i64 = 1_000_000_000;
        // Upstream safety comment (signed_duration.rs:676): "OK because
        // NANOS_PER_SEC!={-1,0}."
        let secs: i64 = nanos / NANOS_PER_SEC_64;
        // Upstream safety comment (signed_duration.rs:678): "OK because
        // NANOS_PER_SEC!={-1,0}." -- the trunc remainder is in
        // (-1e9, 1e9), so the narrowing cast is defined.
        let nanos_sub: i32 = (nanos % NANOS_PER_SEC_64) as i32;
        proof {
            let dd = 1_000_000_000int;
            let q = (secs as int);
            let r = (nanos_sub as int);
            assert(q == rust_div((nanos as int), dd));
            assert(r == rust_rem((nanos as int), dd));
            assert((nanos as int) == q * dd + r);
            assert(r > -dd && r < dd);
            assert(sd_nanos_ok(nanos_sub));
            if r < 0 {
                assert((nanos as int) < 0);
                assert(q <= 0);
            }
            if r > 0 {
                assert((nanos as int) > 0);
                assert(q >= 0);
            }
            if r == 0 {
                assert(nanos_sub == 0);
            }
        }
        SignedDuration::new_unchecked(secs, nanos_sub)
    }

    /// Origin Rust: pub const fn try_from_hours(hours: i64)
    ///     -> Option<SignedDuration> (signed_duration.rs:1733-1744)
    /// Upstream doc (signed_duration.rs:1719-1731):
    ///   Fallibly creates a new SignedDuration from a 64-bit integer
    ///   number of hours.
    ///   If the number of hours is less than SignedDuration::MIN or more
    ///   than SignedDuration::MAX, then this returns None.
    /// Upstream doc example (signed_duration.rs:1730):
    ///   try_from_hours(i64::MAX) == None.
    pub exec fn try_from_hours(hours: i64) -> (r: Option<SignedDuration>)
        ensures
            match r {
                Option::Some(d) => sd_inv(&d)
                    && (d.secs as int) == (hours as int) * 3600
                    && d.nanos == 0,
                Option::None => !(-(2562047788015int) <= hours as int
                    && hours as int <= 2562047788015int),
            },
    {
        // Origin consts (signed_duration.rs:1735,1737): MIN_HOUR =
        // i64::MIN / (SECS_PER_MINUTE * MINS_PER_HOUR), MAX_HOUR =
        // i64::MAX / (SECS_PER_MINUTE * MINS_PER_HOUR) -- trunc division,
        // materialized as the literals of those two const expressions.
        const MIN_HOUR: i64 = -2562047788015;
        const MAX_HOUR: i64 = 2562047788015;
        if !(MIN_HOUR <= hours && hours <= MAX_HOUR) {
            return Option::None;
        }
        // Upstream safety comment (signed_duration.rs:1734): "OK because
        // (SECS_PER_MINUTE*MINS_PER_HOUR)!={-1,0}." -- hours bounded by
        // [MIN_HOUR, MAX_HOUR] keeps hours * 3600 inside i64.
        Option::Some(SignedDuration::from_secs(hours * MINS_PER_HOUR * SECS_PER_MINUTE))
    }

    /// Origin Rust: pub const fn try_from_mins(mins: i64)
    ///     -> Option<SignedDuration> (signed_duration.rs:1760-1769)
    /// Upstream doc (signed_duration.rs:1746-1757):
    ///   Fallibly creates a new SignedDuration from a 64-bit integer
    ///   number of minutes.
    ///   If the number of minutes is less than SignedDuration::MIN or
    ///   more than SignedDuration::MAX, then this returns None.
    /// Upstream doc example (signed_duration.rs:1757):
    ///   try_from_mins(i64::MAX) == None.
    pub exec fn try_from_mins(mins: i64) -> (r: Option<SignedDuration>)
        ensures
            match r {
                Option::Some(d) => sd_inv(&d)
                    && (d.secs as int) == (mins as int) * 60
                    && d.nanos == 0,
                Option::None => !(-(153722867280912930int) <= mins as int
                    && mins as int <= 153722867280912930int),
            },
    {
        // Origin consts (signed_duration.rs:1762,1764): MIN_MINUTE =
        // i64::MIN / SECS_PER_MINUTE, MAX_MINUTE = i64::MAX /
        // SECS_PER_MINUTE (trunc), materialized as literals.
        const MIN_MINUTE: i64 = -153722867280912930;
        const MAX_MINUTE: i64 = 153722867280912930;
        if !(MIN_MINUTE <= mins && mins <= MAX_MINUTE) {
            return Option::None;
        }
        // Upstream safety comment (signed_duration.rs:1761): "OK because
        // SECS_PER_MINUTE!={-1,0}."
        Option::Some(SignedDuration::from_secs(mins * SECS_PER_MINUTE))
    }

    /// Origin Rust: pub const fn from_hours(hours: i64) -> SignedDuration
    ///     (signed_duration.rs:749-759)
    /// Upstream doc (signed_duration.rs:727-747):
    ///   Creates a new SignedDuration from the given number of hours.
    ///   Every hour is exactly 3,600 seconds.
    ///   # Panics
    ///   Panics if the number of hours, after being converted to
    ///   nanoseconds, overflows the minimum or maximum SignedDuration
    ///   values.
    /// (The panic is transcribed faithfully via the external-body helper;
    ///  the ensures states the return face. Callers wanting the no-panic
    ///  guarantee pre-clear try_from_hours -- the upstream API offers
    ///  exactly that split.)
    /// Upstream doc examples (signed_duration.rs:740-746):
    ///   from_hours(24) = (86_400, 0); from_hours(-24) = (-86_400, 0).
    pub exec fn from_hours(hours: i64) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            (d.secs as int) == (hours as int) * 3600,
            d.nanos == 0,
    {
        let opt = SignedDuration::try_from_hours(hours);
        match opt {
            Option::Some(d) => d,
            Option::None => upstream_from_hours_panic(),
        }
    }

    /// Origin Rust: pub const fn from_mins(mins: i64) -> SignedDuration
    ///     (signed_duration.rs:783-793)
    /// Upstream doc (signed_duration.rs:761-781):
    ///   Creates a new SignedDuration from the given number of minutes.
    ///   Every minute is exactly 60 seconds.
    ///   # Panics
    ///   Panics if the number of minutes, after being converted to
    ///   nanoseconds, overflows the minimum or maximum SignedDuration
    ///   values.
    /// Upstream doc examples (signed_duration.rs:774-780):
    ///   from_mins(1_440) = (86_400, 0); from_mins(-1_440) = (-86_400, 0).
    /// (The upstream # Examples call this from_minutes in text? -- no:
    ///  the examples use from_mins(1_440); the upstream name is
    ///  from_mins, "min" abbreviation.)
    pub exec fn from_mins(mins: i64) -> (d: SignedDuration)
        ensures
            sd_inv(&d),
            (d.secs as int) == (mins as int) * 60,
            d.nanos == 0,
    {
        let opt = SignedDuration::try_from_mins(mins);
        match opt {
            Option::Some(d) => d,
            Option::None => upstream_from_mins_panic(),
        }
    }

    /// Origin Rust: pub const fn is_zero(&self) -> bool
    ///     (signed_duration.rs:807-809)
    /// Upstream doc (signed_duration.rs:795-805):
    ///   Returns true if this duration spans no time.
    /// Upstream doc examples (signed_duration.rs:802-804):
    ///   ZERO.is_zero(); !MIN.is_zero(); !MAX.is_zero().
    pub exec fn is_zero(&self) -> (r: bool)
        ensures
            r <==> (self.secs == 0 && self.nanos == 0),
    {
        self.secs == 0 && self.nanos == 0
    }

    /// Origin Rust: pub const fn as_secs(&self) -> i64
    ///     (signed_duration.rs:831-833)
    /// Upstream doc (signed_duration.rs:811-829):
    ///   Returns the number of whole seconds in this duration.
    ///   The value returned is negative when the duration is negative.
    ///   This does not include any fractional component corresponding to
    ///   units less than a second. To access those, use one of the
    ///   subsec methods such as SignedDuration::subsec_nanos.
    /// Upstream doc examples (signed_duration.rs:824-828):
    ///   new(12, 999_999_999).as_secs() == 12;
    ///   new(-12, -999_999_999).as_secs() == -12.
    pub exec fn as_secs(&self) -> (r: i64)
        ensures
            r == self.secs,
    {
        self.secs
    }

    /// Origin Rust: pub const fn subsec_millis(&self) -> i32
    ///     (signed_duration.rs:856-859)
    /// Upstream doc (signed_duration.rs:835-854):
    ///   Returns the fractional part of this duration in whole
    ///   milliseconds.
    ///   The value returned is negative when the duration is negative. It
    ///   is guaranteed that the range of the value returned is in the
    ///   inclusive range -999..=999.
    /// Upstream doc examples (signed_duration.rs:849-853):
    ///   new(12, 123_456_789).subsec_millis() == 123;
    ///   new(-12, -123_456_789).subsec_millis() == -123.
    pub exec fn subsec_millis(&self) -> (r: i32)
        requires
            sd_nanos_ok(self.nanos),
        ensures
            (r as int) == rust_div((self.nanos as int), 1_000_000),
            -999 <= r,
            r <= 999,
    {
        // Upstream safety comment (signed_duration.rs:857): "OK because
        // NANOS_PER_MILLI!={-1,0}."
        proof {
            let q = rust_div((self.nanos as int), 1_000_000);
            let rem = rust_rem((self.nanos as int), 1_000_000);
            assert((self.nanos as int) == q * 1_000_000 + rem);
            assert(rem > -1_000_000 && rem < 1_000_000);
            assert(q >= -999 && q <= 999);
        }
        self.nanos / NANOS_PER_MILLI
    }

    /// Origin Rust: pub const fn subsec_micros(&self) -> i32
    ///     (signed_duration.rs:882-885)
    /// Upstream doc (signed_duration.rs:861-880):
    ///   Returns the fractional part of this duration in whole
    ///   microseconds.
    ///   The value returned is negative when the duration is negative. It
    ///   is guaranteed that the range of the value returned is in the
    ///   inclusive range -999_999..=999_999.
    /// Upstream doc examples (signed_duration.rs:875-879):
    ///   new(12, 123_456_789).subsec_micros() == 123_456;
    ///   new(-12, -123_456_789).subsec_micros() == -123_456.
    pub exec fn subsec_micros(&self) -> (r: i32)
        requires
            sd_nanos_ok(self.nanos),
        ensures
            (r as int) == rust_div((self.nanos as int), 1_000),
            -999_999 <= r,
            r <= 999_999,
    {
        // Upstream safety comment (signed_duration.rs:883): "OK because
        // NANOS_PER_MICRO!={-1,0}."
        proof {
            let q = rust_div((self.nanos as int), 1_000);
            let rem = rust_rem((self.nanos as int), 1_000);
            assert((self.nanos as int) == q * 1_000 + rem);
            assert(rem > -1_000 && rem < 1_000);
            assert(q >= -999_999 && q <= 999_999);
        }
        self.nanos / NANOS_PER_MICRO
    }

    /// Origin Rust: pub const fn subsec_nanos(&self) -> i32
    ///     (signed_duration.rs:908-910)
    /// Upstream doc (signed_duration.rs:887-906):
    ///   Returns the fractional part of this duration in whole
    ///   nanoseconds.
    ///   The value returned is negative when the duration is negative. It
    ///   is guaranteed that the range of the value returned is in the
    ///   inclusive range -999_999_999..=999_999_999.
    /// Upstream doc examples (signed_duration.rs:901-905):
    ///   new(12, 123_456_789).subsec_nanos() == 123_456_789;
    ///   new(-12, -123_456_789).subsec_nanos() == -123_456_789.
    pub exec fn subsec_nanos(&self) -> (r: i32)
        requires
            sd_nanos_ok(self.nanos),
        ensures
            r == self.nanos,
            -999_999_999 <= r,
            r <= 999_999_999,
    {
        self.nanos
    }

    /// Origin Rust: pub const fn as_millis(&self) -> i128
    ///     (signed_duration.rs:931-939)
    /// Upstream doc (signed_duration.rs:912-929):
    ///   Returns the total duration in units of whole milliseconds.
    ///   The value returned is negative when the duration is negative.
    ///   To get only the fractional component of this duration in units
    ///   of whole milliseconds, use SignedDuration::subsec_millis.
    /// Upstream doc examples (signed_duration.rs:924-928):
    ///   new(12, 123_456_789).as_millis() == 12_123;
    ///   new(-12, -123_456_789).as_millis() == -12_123.
    /// Upstream safety comments (signed_duration.rs:932-937): "OK because
    /// 1_000 times any i64 will never overflow i128" / "OK because
    /// NANOS_PER_MILLI!={-1,0}" / "OK because subsec_millis maxes out at
    /// 999, and adding that to i64::MAX*1_000 will never overflow a i128"
    /// -- all discharged below (the i128 fit is linear once widened).
    pub exec fn as_millis(&self) -> (total: i128)
        requires
            sd_nanos_ok(self.nanos),
        ensures
            (total as int) == (self.secs as int) * 1_000
                + rust_div((self.nanos as int), 1_000_000),
    {
        let millis: i128 = (self.secs as i128) * (MILLIS_PER_SEC as i128);
        let subsec_millis: i128 = (self.nanos / NANOS_PER_MILLI) as i128;
        proof {
            let q = rust_div((self.nanos as int), 1_000_000);
            let rem = rust_rem((self.nanos as int), 1_000_000);
            assert((self.nanos as int) == q * 1_000_000 + rem);
            assert(rem > -1_000_000 && rem < 1_000_000);
            assert(q >= -999 && q <= 999);
            assert((subsec_millis as int) == q);
            // i128 fit face (upstream comment :932): |secs| * 1000 is
            // around 9.2e21, far inside the i128 range.
            assert((self.secs as int) * 1_000
                <= 9_223_372_036_854_775_807_000int);
            assert((self.secs as int) * 1_000
                >= -9_223_372_036_854_775_808_000int);
        }
        millis + subsec_millis
    }

    /// Origin Rust: pub const fn as_micros(&self) -> i128
    ///     (signed_duration.rs:960-968)
    /// Upstream doc (signed_duration.rs:941-958):
    ///   Returns the total duration in units of whole microseconds.
    ///   The value returned is negative when the duration is negative.
    ///   To get only the fractional component of this duration in units
    ///   of whole microseconds, use SignedDuration::subsec_micros.
    /// Upstream doc examples (signed_duration.rs:953-957):
    ///   new(12, 123_456_789).as_micros() == 12_123_456;
    ///   new(-12, -123_456_789).as_micros() == -12_123_456.
    /// (Same safety-comment shape as as_millis, signed_duration.rs:961-966.)
    pub exec fn as_micros(&self) -> (total: i128)
        requires
            sd_nanos_ok(self.nanos),
        ensures
            (total as int) == (self.secs as int) * 1_000_000
                + rust_div((self.nanos as int), 1_000),
    {
        let micros: i128 = (self.secs as i128) * (MICROS_PER_SEC as i128);
        let subsec_micros: i128 = (self.nanos / NANOS_PER_MICRO) as i128;
        proof {
            let q = rust_div((self.nanos as int), 1_000);
            let rem = rust_rem((self.nanos as int), 1_000);
            assert((self.nanos as int) == q * 1_000 + rem);
            assert(rem > -1_000 && rem < 1_000);
            assert(q >= -999_999 && q <= 999_999);
            assert((subsec_micros as int) == q);
            assert((self.secs as int) * 1_000_000
                <= 9_223_372_036_854_775_807_000_000int);
        }
        micros + subsec_micros
    }

    /// Origin Rust: pub const fn as_nanos(&self) -> i128
    ///     (signed_duration.rs:989-995)
    /// Upstream doc (signed_duration.rs:970-987):
    ///   Returns the total duration in units of whole nanoseconds.
    ///   The value returned is negative when the duration is negative.
    ///   To get only the fractional component of this duration in units
    ///   of whole nanoseconds, use SignedDuration::subsec_nanos.
    /// Upstream doc examples (signed_duration.rs:982-986):
    ///   new(12, 123_456_789).as_nanos() == 12_123_456_789;
    ///   new(-12, -123_456_789).as_nanos() == -12_123_456_789.
    /// Upstream safety comments (signed_duration.rs:990-993): "OK because
    /// 1_000_000_000 times any i64 will never overflow i128" / "OK
    /// because subsec_nanos maxes out at 999_999_999, and adding that to
    /// i64::MAX*1_000_000_000 will never overflow a i128".
    pub exec fn as_nanos(&self) -> (total: i128)
        requires
            sd_nanos_ok(self.nanos),
        ensures
            (total as int) == sd_total_nanos(self),
    {
        let nanos: i128 = (self.secs as i128) * (NANOS_PER_SEC as i128);
        proof {
            assert((self.secs as int) * 1_000_000_000
                <= 9_223_372_036_854_775_807_000_000_000int);
            assert((self.secs as int) * 1_000_000_000
                >= -9_223_372_036_854_775_808_000_000_000int);
        }
        nanos + (self.nanos as i128)
    }

    /// Origin Rust: pub const fn as_hours(&self) -> i64
    ///     (signed_duration.rs:1878-1880)
    /// Upstream doc (signed_duration.rs:1859-1876):
    ///   Returns the number of whole hours in this duration.
    ///   The value returned is negative when the duration is negative.
    ///   This does not include any fractional component corresponding to
    ///   units less than an hour.
    /// Upstream doc examples (signed_duration.rs:1871-1875):
    ///   new(86_400, 999_999_999).as_hours() == 24;
    ///   new(-86_400, -999_999_999).as_hours() == -24.
    pub exec fn as_hours(&self) -> (r: i64)
        ensures
            (r as int) == rust_div((self.secs as int), 3_600),
    {
        // Origin: self.as_secs() / (MINS_PER_HOUR * SECS_PER_MINUTE);
        // the positive constant divisor keeps the obligation linear.
        proof {
            let q = rust_div((self.secs as int), 3_600);
            let rem = rust_rem((self.secs as int), 3_600);
            assert((self.secs as int) == q * 3_600 + rem);
        }
        self.as_secs() / (MINS_PER_HOUR * SECS_PER_MINUTE)
    }

    /// Origin Rust: pub const fn as_mins(&self) -> i64
    ///     (signed_duration.rs:1901-1903)
    /// Upstream doc (signed_duration.rs:1882-1899):
    ///   Returns the number of whole minutes in this duration.
    ///   The value returned is negative when the duration is negative.
    ///   This does not include any fractional component corresponding to
    ///   units less than a minute.
    /// Upstream doc examples (signed_duration.rs:1894-1898):
    ///   new(3_600, 999_999_999).as_mins() == 60;
    ///   new(-3_600, -999_999_999).as_mins() == -60.
    pub exec fn as_mins(&self) -> (r: i64)
        ensures
            (r as int) == rust_div((self.secs as int), 60),
    {
        proof {
            let q = rust_div((self.secs as int), 60);
            let rem = rust_rem((self.secs as int), 60);
            assert((self.secs as int) == q * 60 + rem);
        }
        self.as_secs() / SECS_PER_MINUTE
    }

    /// Origin Rust: pub const fn is_positive(&self) -> bool
    ///     (signed_duration.rs:2044-2046)
    /// Upstream doc (signed_duration.rs:2032-2042):
    ///   Returns true when this duration is positive. That is, greater
    ///   than SignedDuration::ZERO.
    /// Upstream doc example (signed_duration.rs:2041):
    ///   new(0, 1).is_positive().
    /// (The doc sentence defines positivity against the instant order;
    ///  the impl is the field disjunction. The two agree on canonical
    ///  values, which every public constructor produces.)
    pub exec fn is_positive(&self) -> (r: bool)
        ensures
            r <==> (self.secs > 0 || self.nanos > 0),
    {
        self.secs > 0 || self.nanos > 0
    }

    /// Origin Rust: pub const fn is_negative(&self) -> bool
    ///     (signed_duration.rs:2060-2062)
    /// Upstream doc (signed_duration.rs:2048-2057):
    ///   Returns true when this duration is negative. That is, less than
    ///   SignedDuration::ZERO.
    /// Upstream doc example (signed_duration.rs:2057):
    ///   new(0, -1).is_negative().
    pub exec fn is_negative(&self) -> (r: bool)
        ensures
            r <==> (self.secs < 0 || self.nanos < 0),
    {
        self.secs < 0 || self.nanos < 0
    }

    /// Origin Rust: pub const fn signum(self) -> i8
    ///     (signed_duration.rs:2005-2014)
    /// Upstream doc (signed_duration.rs:1989-1995):
    ///   Returns a number that represents the sign of this duration.
    ///   * When SignedDuration::is_zero is true, this returns 0.
    ///   * When SignedDuration::is_positive is true, this returns 1.
    ///   * When SignedDuration::is_negative is true, this returns -1.
    ///   The above cases are mutually exclusive.
    /// (The mutual-exclusivity sentence holds on canonical values; the
    ///  requires carries the canonical sign tier, the J4 Timestamp
    ///  signum precedent. Every constructor here outputs it.)
    /// Upstream doc example (signed_duration.rs:2002):
    ///   SignedDuration::ZERO.signum() == 0.
    pub exec fn signum(&self) -> (r: i8)
        requires
            sd_signs_agree(self),
        ensures
            if (self.secs == 0 && self.nanos == 0) {
                r == 0
            } else if (self.secs > 0 || self.nanos > 0) {
                r == 1
            } else {
                r == -(1i8)
            },
    {
        if self.is_zero() {
            0
        } else if self.is_positive() {
            1
        } else {
            // Upstream debug_assert!(self.is_negative())
            // (signed_duration.rs:2011): discharged here -- not (zero
            // or positive) plus sign agreement implies some field is
            // negative.
            proof {
                assert(!(self.secs == 0 && self.nanos == 0));
                assert(!(self.secs > 0 || self.nanos > 0));
                assert(self.secs <= 0 && self.nanos <= 0);
                assert(self.secs < 0 || self.nanos < 0);
            }
            -1
        }
    }

    /// Origin Rust: pub const fn abs(self) -> SignedDuration
    ///     (signed_duration.rs:1924-1926)
    /// Upstream doc (signed_duration.rs:1905-1921):
    ///   Returns the absolute value of this signed duration.
    ///   If this duration isn't negative, then this returns the original
    ///   duration unchanged.
    ///   # Panics
    ///   This panics when the seconds component of this signed duration
    ///   is equal to i64::MIN.
    /// Upstream doc example (signed_duration.rs:1920-1921):
    ///   new(1, -1_999_999_999).abs() == new(0, 999_999_999) -- i.e. the
    ///   |instant| face carried below.
    /// Requires note: sd_inv (not merely nanos domain) is needed so that
    /// "returns the original duration unchanged" and the |instant| face
    /// both hold; the nanos negation below is safe because
    /// sd_nanos_ok keeps nanos > i32::MIN -- that second panic face is
    /// NOT upstream-documented (the doc only names i64::MIN seconds; it
    /// is unreachable through any public constructor, so not filed).
    pub exec fn abs(&self) -> (d: SignedDuration)
        requires
            sd_inv(self),
        ensures
            sd_inv(&d),
            sd_total_nanos(&d) == if sd_total_nanos(self) < 0 {
                -(sd_total_nanos(self))
            } else {
                sd_total_nanos(self)
            },
    {
        // Upstream: SignedDuration::new_unchecked(self.secs.abs(),
        // self.nanos.abs()). The i64::MIN face is the documented panic
        // (transcribed via the helper).
        let secs_abs: i64 = if self.secs == i64::MIN {
            upstream_abs_min_secs_panic()
        } else if self.secs < 0 {
            -self.secs
        } else {
            self.secs
        };
        let nanos_abs: i32 = if self.nanos < 0 {
            proof {
                assert((self.nanos as int) >= -999_999_999);
            }
            -self.nanos
        } else {
            self.nanos
        };
        proof {
            assert((secs_abs as int) >= 0);
            assert((nanos_abs as int) >= 0);
            if sd_total_nanos(self) < 0 {
                // Canonical + negative total: both fields are negative
                // (or zero), so field-abs negates the instant exactly.
                assert(self.secs <= 0 && self.nanos <= 0);
                assert((secs_abs as int) * 1_000_000_000 + (nanos_abs as int)
                    == -((self.secs as int) * 1_000_000_000
                        + (self.nanos as int)));
            } else {
                // Doc sentence "If this duration isn't negative, then
                // this returns the original duration unchanged": under
                // sign agreement, a non-negative instant means no field
                // is negative.
                assert(self.secs >= 0 && self.nanos >= 0);
                assert((secs_abs as int) * 1_000_000_000 + (nanos_abs as int)
                    == sd_total_nanos(self));
            }
        }
        SignedDuration::new_unchecked(secs_abs, nanos_abs)
    }

    /// Origin Rust: pub const fn checked_neg(self)
    ///     -> Option<SignedDuration> (signed_duration.rs:1980-1987)
    /// Upstream doc (signed_duration.rs:1951-1977):
    ///   Returns this duration with its sign flipped.
    ///   If this duration is zero, then this returns the duration
    ///   unchanged.
    ///   This returns none if the negation does not exist. This occurs
    ///   in precisely the cases when SignedDuration::as_secs is equal
    ///   to i64::MIN.
    /// Upstream doc examples (signed_duration.rs:1964-1977):
    ///   new(12, 123_456_789).checked_neg() == Some(new(-12, -123_456_789));
    ///   new(-12, -123_456_789).checked_neg() == Some(new(12, 123_456_789));
    ///   MIN.checked_neg() == None.
    pub exec fn checked_neg(&self) -> (r: Option<SignedDuration>)
        requires
            sd_inv(self),
        ensures
            match r {
                Option::Some(d) => sd_inv(&d)
                    && sd_total_nanos(&d) == -(sd_total_nanos(self)),
                // "precisely when as_secs == i64::MIN" (upstream doc).
                Option::None => self.secs == i64::MIN,
            },
    {
        // Upstream safety comment (signed_duration.rs:1984): "Always OK
        // because -999_999_999 <= self.nanos <= 999_999_999" -- the
        // nanosecond negation below cannot overflow; carried by the
        // requires.
        // core::num::checked_neg has no builtin verus spec in this
        // build; spelled out branch-for-branch (None exactly on
        // i64::MIN, Some(-secs) otherwise) -- body-faithful.
        let opt: Option<i64> = if self.secs == i64::MIN {
            Option::None
        } else {
            Option::Some(-self.secs)
        };
        match opt {
            Option::None => Option::None,
            Option::Some(secs_neg) => {
                proof {
                    assert((self.nanos as int) >= -999_999_999);
                }
                Option::Some(SignedDuration::new_unchecked(
                    secs_neg,
                    -self.nanos,
                ))
            }
        }
    }

    /// Origin Rust: pub const fn checked_add(self, rhs: SignedDuration)
    ///     -> Option<SignedDuration> (signed_duration.rs:1037-1092)
    /// Upstream doc (signed_duration.rs:1017-1018):
    ///   Add two signed durations together. If overflow occurs, then
    ///   None is returned.
    /// Upstream doc examples (signed_duration.rs:1025-1034):
    ///   new(12, 500_000_000).checked_add(new(0, 500_000_000))
    ///     == Some(new(13, 0));
    ///   MAX.checked_add(new(0, 1)) == None -- both carried by the
    ///   postcondition (instant-preserving sum; None on overflow).
    /// Upstream safety comment (signed_duration.rs:1044-1045): "OK
    ///  because -999_999_999 <= nanos <= 999_999_999, and so adding them
    ///  together will never overflow an i32." -- requires-borne.
    pub exec fn checked_add(&self, rhs: &SignedDuration)
        -> (r: Option<SignedDuration>)
        requires
            sd_inv(self),
            sd_inv(rhs),
        ensures
            match r {
                Option::Some(d) => sd_inv(&d)
                    && sd_total_nanos(&d) == sd_total_nanos(self)
                        + sd_total_nanos(rhs),
                Option::None => true,
            },
    {
        let opt = self.secs.checked_add(rhs.secs);
        let mut secs: i64 = match opt {
            Option::Some(v) => v,
            Option::None => return Option::None,
        };
        let mut nanos: i32 = self.nanos + rhs.nanos;
        // "The below is effectively SignedDuration::new, but with checked
        // arithmetic ... we know that -1_999_999_998 <= nanos <=
        // 1_999_999_998 ... so we can skip the div and modulus
        // operations" (signed_duration.rs:1047-1054).
        if nanos != 0 {
            if nanos >= NANOS_PER_SEC {
                // Carry (signed_duration.rs:1058-1063).
                nanos = nanos - NANOS_PER_SEC;
                let opt2 = secs.checked_add(1);
                secs = match opt2 {
                    Option::Some(v) => v,
                    Option::None => return Option::None,
                };
            } else if nanos <= -NANOS_PER_SEC {
                // Carry mirror (signed_duration.rs:1064-1069).
                nanos = nanos + NANOS_PER_SEC;
                let opt2 = secs.checked_sub(1);
                secs = match opt2 {
                    Option::Some(v) => v,
                    Option::None => return Option::None,
                };
            }
            // Sign harmonization (signed_duration.rs:1071-1089) -- the
            // remaining branch condition is exactly the fast-path
            // negation of new (secs/nanos nonzero, signs mismatched).
            if secs != 0 && nanos != 0 && !((secs > 0) == (nanos > 0)) {
                if secs < 0 {
                    // Upstream safety comments (signed_duration.rs:
                    // 1077-1080): "OK because secs<0" / "OK because
                    // nanos>0".
                    proof {
                        assert((secs as int) < 0);
                        assert((nanos as int) > 0);
                    }
                    let secs_new: i64 = secs + 1;
                    let nanos_new: i32 = nanos - NANOS_PER_SEC;
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
                    // Upstream safety comments (signed_duration.rs:
                    // 1084-1087): "OK because secs>0" / "OK because
                    // nanos<0".
                    proof {
                        assert((secs as int) > 0);
                        assert((nanos as int) < 0);
                    }
                    let secs_new: i64 = secs - 1;
                    let nanos_new: i32 = nanos + NANOS_PER_SEC;
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
            // Post-harmonization sign agreement: if a repairing branch
            // ran, the pair now harmonizes by its own case analysis; if
            // it did not run, the original condition was harmonious.
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

    /// Origin Rust: pub const fn saturating_add(self, rhs: SignedDuration)
    ///     -> SignedDuration (signed_duration.rs:1111-1120)
    /// Upstream doc (signed_duration.rs:1094-1095):
    ///   Add two signed durations together. If overflow occurs, then
    ///   arithmetic saturates.
    /// Upstream doc examples (signed_duration.rs:1102-1108):
    ///   MAX.saturating_add(new(0, 1)) == MAX;
    ///   MIN.saturating_add(new(0, -1)) == MIN.
    pub exec fn saturating_add(&self, rhs: &SignedDuration) -> (d: SignedDuration)
        requires
            sd_inv(self),
            sd_inv(rhs),
        ensures
            sd_inv(&d),
            sd_total_nanos(&d) == sd_total_nanos(self) + sd_total_nanos(rhs)
                || ((rhs.secs < 0 || rhs.nanos < 0)
                    && sd_total_nanos(&d) == sd_min_total_nanos())
                || (!(rhs.secs < 0 || rhs.nanos < 0)
                    && sd_total_nanos(&d) == sd_max_total_nanos()),
    {
        let opt = self.checked_add(rhs);
        match opt {
            Option::Some(sum) => sum,
            // Overflow: saturate up or down per the sign of rhs
            // (signed_duration.rs:1113-1117).
            Option::None => if rhs.is_negative() {
                SignedDuration::min_value()
            } else {
                SignedDuration::max_value()
            },
        }
    }

    /// Origin Rust: pub const fn checked_sub(self, rhs: SignedDuration)
    ///     -> Option<SignedDuration> (signed_duration.rs:1142-1148)
    /// Upstream doc (signed_duration.rs:1122-1123):
    ///   Subtract one signed duration from another. If overflow occurs,
    ///   then None is returned.
    /// Upstream doc examples (signed_duration.rs:1130-1139):
    ///   new(12, 500_000_000).checked_sub(new(0, 500_000_000))
    ///     == Some(new(12, 0));
    ///   MIN.checked_sub(new(0, 1)) == None.
    pub exec fn checked_sub(&self, rhs: &SignedDuration)
        -> (r: Option<SignedDuration>)
        requires
            sd_inv(self),
            sd_inv(rhs),
        ensures
            match r {
                Option::Some(d) => sd_inv(&d)
                    && sd_total_nanos(&d) == sd_total_nanos(self)
                        - sd_total_nanos(rhs),
                // None is either rhs.secs == i64::MIN (checked_neg) or
                // an overflow inside checked_add -- hence the weak face.
                Option::None => true,
            },
    {
        // Origin body (signed_duration.rs:1146-1147): rhs.checked_neg()
        // then checked_add.
        let opt = rhs.checked_neg();
        match opt {
            Option::Some(rhs_neg) => self.checked_add(&rhs_neg),
            Option::None => Option::None,
        }
    }

    /// Origin Rust: pub const fn saturating_sub(self, rhs: SignedDuration)
    ///     -> SignedDuration (signed_duration.rs:1167-1176)
    /// Upstream doc (signed_duration.rs:1150-1151) says:
    ///   Add two signed durations together. If overflow occurs, then
    ///   arithmetic saturates.
    /// -- the leading verb is "Add" although the routine subtracts (doc
    /// copy-paste slip upstream; the operator family and examples say
    /// subtract). Behavior below follows the impl.
    /// Upstream doc examples (signed_duration.rs:1159-1164):
    ///   MAX.saturating_sub(new(0, -1)) == MAX;
    ///   MIN.saturating_sub(new(0, 1)) == MIN.
    pub exec fn saturating_sub(&self, rhs: &SignedDuration) -> (d: SignedDuration)
        requires
            sd_inv(self),
            sd_inv(rhs),
        ensures
            sd_inv(&d),
            sd_total_nanos(&d) == sd_total_nanos(self) - sd_total_nanos(rhs)
                || ((rhs.secs > 0 || rhs.nanos > 0)
                    && sd_total_nanos(&d) == sd_min_total_nanos())
                || (!(rhs.secs > 0 || rhs.nanos > 0)
                    && sd_total_nanos(&d) == sd_max_total_nanos()),
    {
        let opt = self.checked_sub(rhs);
        match opt {
            Option::Some(diff) => diff,
            // Overflow: saturate per the sign of rhs
            // (signed_duration.rs:1169-1173).
            Option::None => if rhs.is_positive() {
                SignedDuration::min_value()
            } else {
                SignedDuration::max_value()
            },
        }
    }

    /// Origin Rust: pub const fn checked_mul(self, rhs: i32)
    ///     -> Option<SignedDuration> (signed_duration.rs:1193-1204)
    /// Upstream doc (signed_duration.rs:1178-1179):
    ///   Multiply this signed duration by an integer. If the
    ///   multiplication overflows, then None is returned.
    /// Upstream doc example (signed_duration.rs:1186-1190):
    ///   new(12, 500_000_000).checked_mul(2) == Some(new(25, 0)).
    pub exec fn checked_mul(&self, rhs_in: i32) -> (r: Option<SignedDuration>)
        requires
            sd_inv(self),
        ensures
            match r {
                Option::Some(d) => sd_inv(&d)
                    && sd_total_nanos(&d)
                        == sd_total_nanos(self) * (rhs_in as int),
                // Strengthened None face (the two upstream overflow
                // sources, exactly): the i64 secs product overflowed,
                // or the secs-product-plus-carry did. Used by
                // saturating_mul to prove the saturating selector is
                // never the zero-sign corner.
                Option::None =>
                    !(-(9223372036854775808int)
                        <= (self.secs as int) * (rhs_in as int)
                        && (self.secs as int) * (rhs_in as int)
                            <= 9223372036854775807int)
                    || !( -(9223372036854775808int)
                        <= (self.secs as int) * (rhs_in as int)
                            + rust_div(
                                (self.nanos as int) * (rhs_in as int),
                                1_000_000_000)
                        && (self.secs as int) * (rhs_in as int)
                            + rust_div(
                                (self.nanos as int) * (rhs_in as int),
                                1_000_000_000)
                            <= 9223372036854775807int),
            },
    {
        let rhs: i64 = rhs_in as i64;
        // Upstream safety comment (signed_duration.rs:1195):
        // "Multiplying any two i32 values never overflows an i64." --
        // the nonlinear product bound is discharged explicitly below.
        proof {
            let a = (self.nanos as int);
            let b = (rhs_in as int);
            assert((rhs as int) == b);
            assert(-999_999_999 <= a);
            assert(a <= 999_999_999);
            assert(-2_147_483_648 <= b);
            assert(b <= 2_147_483_647);
            // Ground product bounds -- var*var is never self-evident,
            // discharged per sign quadrant through the mul lemma family
            // (lemma_mul_upper_bound; sign flips are native).
            if 0 <= a {
                if 0 <= b {
                    lemma_mul_upper_bound(a, 999_999_999int, b, 2_147_483_647int);
                    assert(0 <= a * b);
                    assert(a * b <= 999_999_999int * 2_147_483_647int);
                    assert(-(999_999_999int * 2_147_483_648int) <= a * b);
                } else {
                    lemma_mul_upper_bound(a, 999_999_999int, -b, 2_147_483_648int);
                    lemma_mul_unary_negation(a, b);
                    assert(a * (-b) == -(a * b));
                    assert(a * b == -(a * (-b)));
                    assert(a * (-b) <= 999_999_999int * 2_147_483_648int);
                    assert(-(999_999_999int * 2_147_483_648int) <= a * b);
                    assert(a * b <= 0);
                }
            } else {
                if 0 <= b {
                    lemma_mul_upper_bound(-a, 999_999_999int, b, 2_147_483_647int);
                    lemma_mul_unary_negation(a, b);
                    assert((-a) * b == -(a * b));
                    assert(a * b == -((-a) * b));
                    assert((-a) * b >= 0);
                    assert(-(999_999_999int * 2_147_483_647int) <= a * b);
                    assert(a * b <= 0);
                } else {
                    lemma_mul_upper_bound(-a, 999_999_999int, -b, 2_147_483_648int);
                    lemma_mul_cancels_negatives(a, b);
                    assert(a * b == (-a) * (-b));
                    assert(0 <= a * b);
                    assert(a * b <= 999_999_999int * 2_147_483_648int);
                }
            }
            assert(999_999_999int * 2_147_483_648int
                < 9_223_372_036_854_775_807int);
            assert(-(999_999_999int * 2_147_483_648int) <= a * b);
            assert(a * b <= 999_999_999int * 2_147_483_648int);
        }
        proof {
            // machine promotion face: the i64 product is a*b
            assert(true);
        }
        let nanos: i64 = (self.nanos as i64) * rhs;
        proof {
            assert((nanos as int) == (self.nanos as int) * (rhs as int));
        }
        // Upstream safety comment (signed_duration.rs:1197): "OK since
        // NANOS_PER_SEC!={-1,0}."
        let addsecs: i64 = nanos / 1_000_000_000;
        // Upstream safety comment (signed_duration.rs:1199): "OK since
        // NANOS_PER_SEC!={-1,0}." -- the trunc remainder is in
        // (-1e9, 1e9), so the narrowing cast is defined.
        let nanos_sub: i32 = (nanos % 1_000_000_000) as i32;
        proof {
            let q = rust_div((nanos as int), 1_000_000_000);
            let rem = rust_rem((nanos as int), 1_000_000_000);
            assert((addsecs as int) == q);
            assert((nanos_sub as int) == rem);
            assert((nanos as int) == q * 1_000_000_000 + rem);
            assert(rem > -1_000_000_000 && rem < 1_000_000_000);
            assert(sd_nanos_ok(nanos_sub));
        }
        let opt = self.secs.checked_mul(rhs);
        let secs: i64 = match opt {
            Option::Some(v) => v,
            Option::None => return Option::None,
        };
        // Upstream: secs.checked_add(addsecs) (signed_duration.rs:1202).
        let opt2 = secs.checked_add(addsecs);
        let secs: i64 = match opt2 {
            Option::Some(v) => v,
            Option::None => return Option::None,
        };
        proof {
            let x = (self.secs as int);
            let y = (self.nanos as int);
            let r = (rhs as int);
            let rin = (rhs_in as int);
            let aa = (addsecs as int);
            let nsub = (nanos_sub as int);
            assert(r == rin);
            // Instant preservation, factor chain:
            // (x*1e9 + y)*r == x*1e9*r + y*r   (right distribution)
            //              == (x*r)*1e9 + (y*r) (associativity+comm.)
            // (x*r + aa)*1e9 + (y*r - aa*1e9)
            //              == (x*r)*1e9 + aa*1e9 + (y*r) - aa*1e9
            //              == (x*r)*1e9 + (y*r)
            assert((nanos as int) == aa * 1_000_000_000 + nsub);
            assert((secs as int) == x * r + aa);
            assert(sd_total_nanos(&SignedDuration { secs, nanos: nanos_sub })
                == ((x * r) + aa) * 1_000_000_000 + nsub);
            assert(nsub == (y * r) - aa * 1_000_000_000);
            assert(sd_total_nanos(&SignedDuration { secs, nanos: nanos_sub })
                == ((x * r) + aa) * 1_000_000_000
                    + ((y * r) - aa * 1_000_000_000));
            assert(sd_total_nanos(self) * rin
                == (x * 1_000_000_000 + y) * rin);
            lemma_mul_is_distributive_add_other_way(
                rin, x * 1_000_000_000, y);
            assert((x * 1_000_000_000) * rin + y * rin
                == (x * 1_000_000_000 + y) * rin);
            assert(sd_total_nanos(self) * rin
                == (x * 1_000_000_000) * rin + (y * rin));
            lemma_mul_is_commutative(1_000_000_000int, rin);
            assert(1_000_000_000 * rin == rin * 1_000_000_000);
            lemma_mul_is_associative(x, 1_000_000_000, rin);
            lemma_mul_is_associative(x, rin, 1_000_000_000);
            assert((x * 1_000_000_000) * rin
                == x * (1_000_000_000 * rin));
            assert(x * (1_000_000_000 * rin)
                == x * (rin * 1_000_000_000));
            assert(x * (rin * 1_000_000_000) == (x * rin) * 1_000_000_000);
            assert((x * 1_000_000_000) * rin == (x * rin) * 1_000_000_000);
            assert(sd_total_nanos(self) * rin
                == (x * rin) * 1_000_000_000 + (y * rin));
            lemma_mul_is_distributive_add_other_way(
                1_000_000_000int, x * rin, aa);
            assert(((x * rin) + aa) * 1_000_000_000
                == (x * rin) * 1_000_000_000 + aa * 1_000_000_000);
            assert(sd_total_nanos(&SignedDuration { secs, nanos: nanos_sub })
                == (x * rin) * 1_000_000_000 + aa * 1_000_000_000
                    + (y * rin) - aa * 1_000_000_000);
            assert(sd_total_nanos(&SignedDuration { secs, nanos: nanos_sub })
                == (x * rin) * 1_000_000_000 + (y * rin));
            assert(sd_total_nanos(&SignedDuration { secs, nanos: nanos_sub })
                == sd_total_nanos(self) * rin);
            // Sign harmonization of the result: both products flip (or
            // keep) their sign together with rhs; the trunc remainder
            // keeps the dividend's sign, so the pair agrees.
            let y = (self.nanos as int);
            let r = (rhs as int);
            let x = (self.secs as int);
            let aa = (addsecs as int);
            if nanos_sub != 0 && secs != 0 {
                if nanos_sub > 0 {
                    // Q == y*r > 0, aa >= 0.
                    assert((nanos as int) > 0);
                    assert(aa >= 0);
                    sd_mul_pos_sign(y, r);
                    if y > 0 {
                        assert(r > 0);
                        // canonical (y>0): x >= 0.
                        assert(x >= 0);
                        if x > 0 {
                            lemma_mul_strictly_positive(x, r);
                            assert(x * r > 0);
                            // secs = x*r + aa > 0.
                        } else {
                            assert(x == 0);
                            assert((secs as int) == aa);
                            // secs != 0 here forces aa > 0.
                        }
                        assert((secs as int) > 0);
                        assert(secs > 0);
                    } else {
                        assert(y < 0);
                        assert(r < 0);
                        // canonical (y<0): x <= 0.
                        assert(x <= 0);
                        if x < 0 {
                            lemma_mul_cancels_negatives(x, r);
                            lemma_mul_strictly_positive(-x, -r);
                            assert(x * r > 0);
                        } else {
                            assert(x == 0);
                            assert((secs as int) == aa);
                        }
                        assert((secs as int) > 0);
                        assert(secs > 0);
                    }
                } else {
                    // Q == y*r < 0, aa <= 0.
                    assert((nanos as int) < 0);
                    assert(aa <= 0);
                    sd_mul_neg_sign(y, r);
                    if y > 0 {
                        assert(r < 0);
                        assert(x >= 0);
                        if x > 0 {
                            lemma_mul_strictly_positive(x, -r);
                            lemma_mul_unary_negation(x, r);
                            assert(x * r < 0);
                        } else {
                            assert(x == 0);
                            assert((secs as int) == aa);
                        }
                        assert((secs as int) < 0);
                        assert(secs < 0);
                    } else {
                        assert(y < 0);
                        assert(r > 0);
                        assert(x <= 0);
                        if x < 0 {
                            lemma_mul_strictly_positive(-x, r);
                            lemma_mul_unary_negation(x, r);
                            assert(x * r < 0);
                        } else {
                            assert(x == 0);
                            assert((secs as int) == aa);
                        }
                        assert((secs as int) < 0);
                        assert(secs < 0);
                    }
                }
            }
            assert(sd_signs_agree(&SignedDuration { secs, nanos: nanos_sub }));
        }
        Option::Some(SignedDuration::new_unchecked(secs, nanos_sub))
    }

    /// Origin Rust: pub const fn saturating_mul(self, rhs: i32)
///     -> SignedDuration (signed_duration.rs:1224-1234)
/// Upstream doc (signed_duration.rs:1206-1208):
///   Multiply this signed duration by an integer. If the
///   multiplication overflows, then the result saturates to either
///   the minimum or maximum duration depending on the sign of the
///   product.
/// Upstream doc examples (signed_duration.rs:1215-1221):
///   new(i64::MAX, 0).saturating_mul(2) == MAX;
///   new(i64::MAX, 0).saturating_mul(-2) == MIN;
///   new(i64::MIN, 0).saturating_mul(2) == MIN;
///   new(i64::MIN, 0).saturating_mul(-2) == MAX.
pub exec fn saturating_mul(&self, rhs: i32) -> (d: SignedDuration)
    requires
        sd_inv(self),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d) == sd_total_nanos(self) * (rhs as int)
            || (sd_signum_spec(self) * sd_i32_signum_spec(rhs) < 0
                && sd_total_nanos(&d) == sd_min_total_nanos())
            || (sd_signum_spec(self) * sd_i32_signum_spec(rhs) > 0
                && sd_total_nanos(&d) == sd_max_total_nanos()),
    {
        let opt = self.checked_mul(rhs);
        match opt {
            Option::Some(product) => product,
            // Overflow: saturate per the product sign
            // (signed_duration.rs:1226-1231): sign = self.signum()
            // * rhs.signum(); the zero-sign product never reaches this
            // arm (a zero factor zeroes both product guards of
            // checked_mul's None face), so the else arm is exactly the
            // positive-sign saturation.
            Option::None => {
                proof {
                    // Zero-sign impossibility on this arm, by cases:
                    if (self.secs == 0 && self.nanos == 0) {
                        lemma_mul_by_zero_is_zero((rhs as int));
                        assert((self.nanos as int) * (rhs as int) == 0);
                        assert(rust_div((self.nanos as int) * (rhs as int),
                            1_000_000_000) == 0);
                        assert((self.secs as int) * (rhs as int)
                            + rust_div((self.nanos as int) * (rhs as int),
                                1_000_000_000) == 0);
                        // Both None-face disjuncts are false on a zero
                        // factor: contradiction with the assumed None.
                        assert(false);
                    }
                    if rhs == 0 {
                        lemma_mul_by_zero_is_zero((self.nanos as int));
                        assert((self.secs as int) * (rhs as int) == 0);
                        assert((self.nanos as int) * (rhs as int) == 0);
                        assert(rust_div((self.nanos as int) * (rhs as int),
                            1_000_000_000) == 0);
                        assert((self.secs as int) * (rhs as int)
                            + rust_div((self.nanos as int) * (rhs as int),
                                1_000_000_000) == 0);
                        assert(false);
                    }
                    // non-both-zero self has nonzero multiplier sign
                    // (signum's own case structure under sd_inv).
                }
                let rhs64: i64 = rhs as i64;
                // Origin: (rhs as i64).signum(), spelled by cases (the
                // core signum method is avoided in exec position).
                let rhs_sign: i64 = if rhs64 > 0 {
                    1
                } else if rhs64 == 0 {
                    0
                } else {
                    -1
                };
                proof {
                    assert((rhs_sign as int) == sd_i32_signum_spec(rhs));
                }
                let self_sign: i64 = self.signum() as i64;
                proof {
                    if (self.secs == 0 && self.nanos == 0) {
                        assert((self_sign as int) == 0);
                    } else if (self.secs > 0 || self.nanos > 0) {
                        assert((self_sign as int) == 1);
                    } else {
                        assert((self_sign as int) == -1);
                    }
                    assert((self_sign as int) == sd_signum_spec(self));
                }
                let sign: i64 = self_sign * rhs_sign;
                if sign < 0 {
                    SignedDuration::min_value()
                } else {
                    SignedDuration::max_value()
                }
            }
        }
    }
}

// ===========================================================================
// core::ops faces (signed_duration.rs:2603-2681). The trait impls
// upstream unwrap the checked variants with .expect; the translated free
// functions carry domain-excluder requires (so the panic the upstream
// .expect text promises is unreachable HERE -- the excluder is a
// reviewed human obligation, recorded per fn) and route the failure arm
// through the dead-arm helper.
// ===========================================================================

/// Origin Rust: impl core::ops::Neg for SignedDuration
///     fn neg(self) -> SignedDuration (signed_duration.rs:2607-2609)
/// Upstream .expect text (the # Panics-equivalent):
///   "overflow when negating signed duration"
pub(crate) exec fn sd_ops_neg(d: &SignedDuration) -> (r: SignedDuration)
    requires
        sd_inv(d),
        d.secs != i64::MIN,
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == -(sd_total_nanos(d)),
{
    let opt = d.checked_neg();
    match opt {
        Option::Some(v) => v,
        Option::None => j4b_dead_arm_unreachable(),
    }
}

/// Origin Rust: impl core::ops::Add for SignedDuration
///     fn add(self, rhs: SignedDuration) -> SignedDuration
///     (signed_duration.rs:2616-2618)
/// Upstream .expect text:
///   "overflow when adding signed durations"
/// Excluder note: checked_add cannot return None when the summed
/// seconds field stays one i64 step away from both edges (all the +1/-1
/// carries and the harmonization step keep it in range), so the
/// boundary-excluded domain below is panic-free.
pub(crate) exec fn sd_ops_add(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(a),
        sd_inv(b),
        -(9223372036854775807int) <= (a.secs as int) + (b.secs as int),
        (a.secs as int) + (b.secs as int) <= 9223372036854775806int,
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(a) + sd_total_nanos(b),
{
    let opt = a.checked_add(b);
    match opt {
        Option::Some(v) => v,
        Option::None => j4b_dead_arm_unreachable(),
    }
}

/// Origin Rust: impl core::ops::AddAssign for SignedDuration
///     fn add_assign(&mut self, rhs: SignedDuration)
///     (signed_duration.rs:2623-2625)
/// Upstream body verdict (audited verbatim): `*self = *self + rhs;` --
/// a genuine ADDITION through the Add operator. No contract inversion
/// (contrast the J4 Timestamp SubAssign suspect, whose body ADDED under
/// a subtraction doc).
pub(crate) exec fn sd_ops_add_assign(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(a),
        sd_inv(b),
        -(9223372036854775807int) <= (a.secs as int) + (b.secs as int),
        (a.secs as int) + (b.secs as int) <= 9223372036854775806int,
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(a) + sd_total_nanos(b),
{
    sd_ops_add(a, b)
}

/// Origin Rust: impl core::ops::Sub for SignedDuration
///     fn sub(self, rhs: SignedDuration) -> SignedDuration
///     (signed_duration.rs:2632-2635)
/// Upstream .expect text:
///   "overflow when subtracting signed durations"
/// Excluder note: the sec difference one step off both edges keeps
/// checked_sub (rhs negation + checked_add) inside the i64 range.
pub(crate) exec fn sd_ops_sub(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(a),
        sd_inv(b),
        b.secs != i64::MIN,
        -(9223372036854775807int) <= (a.secs as int) - (b.secs as int),
        (a.secs as int) - (b.secs as int) <= 9223372036854775806int,
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(a) - sd_total_nanos(b),
{
    let opt = a.checked_sub(b);
    match opt {
        Option::Some(v) => v,
        Option::None => j4b_dead_arm_unreachable(),
    }
}

/// Origin Rust: impl core::ops::SubAssign for SignedDuration
///     fn sub_assign(&mut self, rhs: SignedDuration)
///     (signed_duration.rs:2640-2642)
/// Upstream body verdict (audited verbatim): `*self = *self - rhs;` --
/// a genuine SUBTRACTION through the Sub operator. The J4 Timestamp
/// SubAssign inversion (ts -= rhs moves ts FORWARD, timestamp.rs:740-745)
/// does NOT recur in this file: this upstream SubAssign is faithful to
/// its trait.
pub(crate) exec fn sd_ops_sub_assign(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(a),
        sd_inv(b),
        b.secs != i64::MIN,
        -(9223372036854775807int) <= (a.secs as int) - (b.secs as int),
        (a.secs as int) - (b.secs as int) <= 9223372036854775806int,
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(a) - sd_total_nanos(b),
{
    sd_ops_sub(a, b)
}

/// Origin Rust: impl core::ops::Mul<i32> for SignedDuration
///     fn mul(self, rhs: i32) -> SignedDuration
///     (signed_duration.rs:2649-2652)
/// Upstream .expect text:
///   "overflow when multiplying signed duration by scalar"
/// Excluder note: both the secs*rhs product inside i64 and the full
/// product inside the representable 96-bit span keep checked_mul's
/// None arms out.
pub(crate) exec fn sd_ops_mul(d: &SignedDuration, rhs: i32) -> (r: SignedDuration)
    requires
        sd_inv(d),
        -(9223372036854775808int) <= (d.secs as int) * (rhs as int),
        (d.secs as int) * (rhs as int) <= 9223372036854775807int,
        sd_min_total_nanos() <= sd_total_nanos(d) * (rhs as int),
        sd_total_nanos(d) * (rhs as int) <= sd_max_total_nanos(),
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(d) * (rhs as int),
{
    let opt = d.checked_mul(rhs);
    match opt {
        Option::Some(v) => v,
        Option::None => j4b_dead_arm_unreachable(),
    }
}

/// Origin Rust: impl core::ops::Mul<SignedDuration> for i32
///     fn mul(self, rhs: SignedDuration) -> SignedDuration
///     (signed_duration.rs:2671-2673) -- body is `rhs * self`
///     (commutativity delegation; the same excluder as sd_ops_mul).
pub(crate) exec fn sd_ops_mul_i32_lhs(
    lhs: i32,
    d: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(d),
        -(9223372036854775808int) <= (d.secs as int) * (lhs as int),
        (d.secs as int) * (lhs as int) <= 9223372036854775807int,
        sd_min_total_nanos() <= sd_total_nanos(d) * (lhs as int),
        sd_total_nanos(d) * (lhs as int) <= sd_max_total_nanos(),
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(d) * (lhs as int),
{
    sd_ops_mul(d, lhs)
}

/// Origin Rust: impl core::ops::MulAssign<i32> for SignedDuration
///     fn mul_assign(&mut self, rhs: i32) (signed_duration.rs:2678-2680)
/// Upstream .expect text: "overflow when multiplying signed duration by
/// scalar" (inherits impl Mul<i32> via the `*` operator).
pub(crate) exec fn sd_ops_mul_assign(
    d: &SignedDuration,
    rhs: i32,
) -> (r: SignedDuration)
    requires
        sd_inv(d),
        -(9223372036854775808int) <= (d.secs as int) * (rhs as int),
        (d.secs as int) * (rhs as int) <= 9223372036854775807int,
        sd_min_total_nanos() <= sd_total_nanos(d) * (rhs as int),
        sd_total_nanos(d) * (rhs as int) <= sd_max_total_nanos(),
    ensures
        sd_inv(&r),
        sd_total_nanos(&r) == sd_total_nanos(d) * (rhs as int),
{
    sd_ops_mul(d, rhs)
}

} // verus!
