//! jiff-core 0.1.5 Timestamp core (crates/jiff-core/src/timestamp.rs,
//! 981 lines at pin 627c7358) -- Verus translation, batch J4.
//!
//! Scope: the seconds + nanosecond carry-arithmetic heart of `Timestamp`
//! -- `new` normalization, the from_second/milli/micro/nano constructors
//! with their `as_*` inverses, subsec accessors, sign predicates, and the
//! checked_add/checked_sub family with its per-second variants.
//!
//! Driver mount: `verified/j4-driver.rs` mounts this file via #[path];
//! the merge into the eventual crate root (next to the in-flight J1
//! sources lib.rs / bounds.rs) is deferred to the harness stage per the
//! batch plan.
//!
//! Bounds face materialized inline pending the shared bounds module (J1
//! owns src/bounds.rs; this file inlines the exact boundary constants of
//! b::UnixEpochSeconds (bounds.rs:376-385), b::SignedSubsecNanosecond
//! (bounds.rs:301-313), b::UnixEpochMilliseconds and
//! b::UnixEpochMicroseconds (bounds.rs:329-342), and the time-unit
//! constants (constants.rs:15-38) instead of mounting J1's files).
//!
//! Error carrier model (file-wide):
//! - Upstream `Result<Timestamp, RangeError>` is modeled as
//!   `Result<Timestamp, RangeError>` over the hand-written enum below:
//!   variants stand for the upstream error constructors reached on this
//!   file's paths (`b::UnixEpochSeconds::error()`
//!   `b::SignedSubsecNanosecond::error()`,
//!   `b::SpecialBoundsError::UnixEpochNanoseconds`); no message strings
//!   (the error-carrier-not-prose rule). Note upstream's `new` reuses the
//!   `UnixEpochSeconds` error for its minimum-second/negative-nanos
//!   rejection (timestamp.rs:47-49), so that rejection maps onto the
//!   same variant here.
//! - Upstream `Timestamp::constant` and the core::ops impls panic where
//!   the checked variants error; their `# Panics` docs are moved to
//!   requires on the translated functions (the batch instruction).
//! - The upstream reachable panic in the seconds/nanoseconds balance of
//!   `checked_add`/`checked_sub` (timestamp.rs:421-426 and :485-489) is
//!   transcribed faithfully as a panic branch via an external-body
//!   helper: verus's built-in spec for core panic assumes
//!   non-reachability (requires false), so the branch goes through a
//!   helper whose body is the upstream panic (compiled, unverified) and
//!   whose `-> !` signature gives callers divergence with no
//!   postcondition. Reachability is recorded in the J4 suspects list;
//!   it is NOT handled by returning an error here.
//!
//! Translation faces (toolchain doctrine, established by the J4 probes
//! in out/kverus-run/J4/probe*.rs):
//! - exec machine-int arithmetic carries overflow obligations by
//!   default, so every upstream "Never wraps because ..." comment below
//!   is discharged as a real verifier obligation at the site it guards.
//! - exec machine `/` and `%` lower to the vstd spec fns
//!   `vstd::arithmetic::div_mod::rust_div` / `rust_rem`, so all
//!   trunc-division reasoning (identity, remainder range, sign
//!   coupling) is written against those fns in proof blocks.
//! - Spec-side machine `/`/`%` is EUCLIDEAN, not Rust trunc (probe:
//!   `(-500i64) % 1000i64 == 500`), so spec clauses never use bare
//!   machine division; they use rust_div/rust_rem instead.
//! - `# Panics`-to-requires conversions are annotated inline.
//!
//! Upstream safety-comment audit result (this batch's obligation core):
//! all four "never wraps/overflows" comments of `Timestamp::new`
//! (timestamp.rs:60-81) and the range comments of from_millisecond /
//! from_microsecond / as_millisecond / as_microsecond / as_nanosecond /
//! checked_add_sensible verify as obligations. Two upstream doctrines
//! do NOT verify and are filed as suspects in out/kverus-run/J4/
//! notes.md (not self-filed): the min-second carry guard behind the
//! checked_add/sub family (J4-1) and the unchecked sign carry of
//! checked_add_seconds (J4-3). Their translated postconditions state
//! what is actually preservable (ts_range_inv / ts_field_inv -- see
//! the spec fn stack below); the gap to upstream's debug-asserted
//! canonical form ts_inv is documented at each site.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{rust_div, rust_rem};

verus! {

// ===========================================================================
// Materialized bounds face (inline) --
// Origin jiff-core/src/bounds.rs + constants.rs:
//   UnixEpochSeconds::MIN = -377705116800 - OffsetTotalSeconds::MIN
//     with OffsetTotalSeconds::MIN = -93599 (bounds.rs:277-292)
//   UnixEpochSeconds::MAX = 253402300799 - OffsetTotalSeconds::MAX
//     (bounds.rs:376-385)
//   SignedSubsecNanosecond = -(SubsecNanosecond::MAX)..=MAX with
//     SubsecNanosecond::MAX = NANOS_PER_SEC_32 - 1 (bounds.rs:299-313)
//   UnixEpochMilliseconds = UnixEpochSeconds * MILLIS_PER_SEC
//     (bounds.rs:329-335); UnixEpochMicroseconds = millis * 1_000
//     (bounds.rs:336-342)
// ===========================================================================

/// b::UnixEpochSeconds::MIN (bounds.rs:383, with OffsetTotalSeconds::MIN
/// = -93599).
pub const UNIX_SECONDS_MIN: i64 = -377_705_023_201;
/// b::UnixEpochSeconds::MAX (bounds.rs:384).
pub const UNIX_SECONDS_MAX: i64 = 253_402_207_200;
/// b::SignedSubsecNanosecond bound (bounds.rs:307-313): the greatest
/// magnitude of the sub-second nanosecond component.
pub const SUBSEC_NANOS_MAX: i64 = 999_999_999;
/// c::MILLIS_PER_SEC (constants.rs:16).
pub const MILLIS_PER_SEC: i64 = 1_000;
/// c::MICROS_PER_SEC (constants.rs:18).
pub const MICROS_PER_SEC: i64 = 1_000_000;
/// c::NANOS_PER_SEC_32 (constants.rs:36).
pub const NANOS_PER_SEC_32: i32 = 1_000_000_000;
/// c::NANOS_PER_MILLI_32 (constants.rs:37).
pub const NANOS_PER_MILLI_32: i32 = 1_000_000;
/// c::NANOS_PER_MICRO_32 (constants.rs:38).
pub const NANOS_PER_MICRO_32: i32 = 1_000;

// ---------------------------------------------------------------------------
// Spec predicates. All comparisons live on int; machine values are cast
// at the boundary (the spec-side arithmetic promotion doctrine).
// ---------------------------------------------------------------------------

/// The b::UnixEpochSeconds domain, on int.
pub open spec fn unix_seconds_ok_int(s: int) -> bool {
    UNIX_SECONDS_MIN as int <= s <= UNIX_SECONDS_MAX as int
}

/// The b::UnixEpochSeconds domain.
pub open spec fn unix_seconds_ok(s: i64) -> bool {
    unix_seconds_ok_int(s as int)
}

/// The b::SignedSubsecNanosecond domain, on int.
pub open spec fn subsec_nanos_ok_int(n: int) -> bool {
    -(SUBSEC_NANOS_MAX as int) <= n <= SUBSEC_NANOS_MAX as int
}

/// The b::SignedSubsecNanosecond domain.
pub open spec fn subsec_nanos_ok(n: i32) -> bool {
    subsec_nanos_ok_int(n as int)
}

/// The b::UnixEpochMilliseconds domain (bounds.rs:329-335).
pub open spec fn unix_millis_ok(m: i64) -> bool {
    (UNIX_SECONDS_MIN as int) * 1_000 <= m as int
        && m as int <= (UNIX_SECONDS_MAX as int) * 1_000
}

/// The b::UnixEpochMicroseconds domain (bounds.rs:336-342).
pub open spec fn unix_micros_ok(u: i64) -> bool {
    (UNIX_SECONDS_MIN as int) * 1_000_000 <= u as int
        && u as int <= (UNIX_SECONDS_MAX as int) * 1_000_000
}

/// The exact precondition of b::UnixEpochSeconds::checked_add (the pair
/// sums into the domain; subsumes the i64 overflow check because the
/// domain sits far inside i64).
pub open spec fn unix_seconds_add_ok(a: i64, b: i64) -> bool {
    unix_seconds_ok_int((a as int) + (b as int))
}

// ===========================================================================
// Origin Rust: pub struct Timestamp { second: i64, nanosecond: i32 }
//     (timestamp.rs:13-18)
// (Fields pub: harness-facing translation, the bit-set batch precedent;
//  upstream keeps them private.)
// ===========================================================================

pub struct Timestamp {
    pub second: i64,
    pub nanosecond: i32,
}

// ---------------------------------------------------------------------------
// Spec model faces.
// ---------------------------------------------------------------------------

/// The instant denoted by a Timestamp, in nanoseconds since the Unix
/// epoch (unbounded int).
pub open spec fn ts_total_nanos(t: &Timestamp) -> int {
    (t.second as int) * 1_000_000_000 + (t.nanosecond as int)
}

/// Field-domain tier: both fields inside their materialized bounds.
/// This is the tier every translated Timestamp method preserves.
pub open spec fn ts_field_inv(t: &Timestamp) -> bool {
    unix_seconds_ok(t.second) && subsec_nanos_ok(t.nanosecond)
}

/// The sub-second carry agrees in sign with the second field
/// (new_unchecked debug_assert 4, timestamp.rs:104-108).
pub open spec fn ts_signs_agree(t: &Timestamp) -> bool {
    t.nanosecond == 0
        || t.second == 0
        || (t.second > 0 && t.nanosecond > 0)
        || (t.second < 0 && t.nanosecond < 0)
}

/// No negative sub-second carry on the minimal second
/// (new_unchecked debug_assert 3, timestamp.rs:103).
pub open spec fn ts_min_ok(t: &Timestamp) -> bool {
    t.second != UNIX_SECONDS_MIN || t.nanosecond >= 0
}

/// Sign-preserving tier (fields in range + sign carry agreement): what
/// the checked_add/checked_sub normalization family actually preserves
/// (clause ts_min_ok is dropped -- suspects entry J4-1).
pub open spec fn ts_range_inv(t: &Timestamp) -> bool {
    ts_field_inv(t) && ts_signs_agree(t)
}

/// The full canonical form upstream debug-asserts in new_unchecked
/// (timestamp.rs:101-108, debug tier turned into the spec tier here).
/// Every constructor below establishes it; the checked_add_seconds
/// family does NOT (suspects J4-1/J4-3).
pub open spec fn ts_inv(t: &Timestamp) -> bool {
    ts_range_inv(t) && ts_min_ok(t)
}

// ===========================================================================
// Error carrier (variant identity only; see the file-head model note).
// ===========================================================================

pub enum RangeError {
    /// b::UnixEpochSeconds::error() -- also reused by upstream for the
    /// minimum-second/negative-nanos rejection in Timestamp::new
    /// (timestamp.rs:47-49) and from_nanosecond (timestamp.rs:184-186).
    UnixEpochSeconds,
    /// b::SignedSubsecNanosecond::error().
    SignedSubsecNanosecond,
    /// b::SpecialBoundsError::UnixEpochNanoseconds (bounds.rs:911-915).
    UnixEpochNanoseconds,
}

// ===========================================================================
// Translation-only helpers.
// ===========================================================================

/// Faithful transcription of the upstream reachable panic at
/// timestamp.rs:421-426 (checked_add) and :483-491 (checked_sub):
/// "nanoseconds overflowed seconds in SignedDuration::new". Panic is
/// compiled here (unverified body, the verus core panic spec assumes
/// non-reachability); the `-> !` signature gives callers honest
/// divergence. Reachable on e.g. `Timestamp::UNIX_EPOCH.checked_add
/// (9223372036854775806, 2_147_483_647)` -- see the J4 suspects list.
#[verifier::external_body]
pub fn upstream_panic_balance_overflow() -> ! {
    panic!("nanoseconds overflowed seconds in SignedDuration::new");
}

/// Translation-only filler for match arms that are statically dead under
/// the enclosing requires (the translation of `.unwrap()` on a checked
/// result whose error face the requires has excluded). Never executed;
/// distinct from upstream_panic_balance_overflow, which transcribes an
/// upstream panic site that CAN execute.
#[verifier::external_body]
pub fn j4_dead_arm_unreachable() -> ! {
    panic!("jiff J4 translation: dead match arm reached (contradiction with requires)");
}

// ===========================================================================
// Origin Rust: impl Timestamp { (timestamp.rs:20-599)
// ===========================================================================

impl Timestamp {

    /// Origin Rust: pub const MIN: Timestamp = Timestamp {
    ///     second: b::UnixEpochSeconds::MIN, nanosecond: b::SubsecNanosecond::MIN }
    ///     (timestamp.rs:22-25)
    /// Upstream doc (timestamp.rs:21):
    ///   The minimum allow Unix timestamp.
    /// (constness dropped; SubsecNanosecond::MIN is 0, the unsigned family
    ///  bound -- NOT the signed subsec minimum.)
    pub exec fn min_value() -> (t: Timestamp)
        ensures
            ts_inv(&t),
            t.second == UNIX_SECONDS_MIN,
            t.nanosecond == 0,
    {
        Timestamp { second: UNIX_SECONDS_MIN, nanosecond: 0 }
    }

    /// Origin Rust: pub const MAX: Timestamp = Timestamp {
    ///     second: b::UnixEpochSeconds::MAX, nanosecond: b::SubsecNanosecond::MAX }
    ///     (timestamp.rs:28-31)
    /// Upstream doc (timestamp.rs:27):
    ///   The maximum allow Unix timestamp.
    pub exec fn max_value() -> (t: Timestamp)
        ensures
            ts_inv(&t),
            t.second == UNIX_SECONDS_MAX,
            t.nanosecond == 999_999_999,
    {
        Timestamp { second: UNIX_SECONDS_MAX, nanosecond: 999_999_999 }
    }

    /// Origin Rust: pub const UNIX_EPOCH: Timestamp = Timestamp {
    ///     second: 0, nanosecond: 0 } (timestamp.rs:34)
    /// Upstream doc (timestamp.rs:33):
    ///   The Unix epoch represented as a timestamp.
    pub exec fn unix_epoch() -> (t: Timestamp)
        ensures
            ts_inv(&t),
            t.second == 0,
            t.nanosecond == 0,
            ts_total_nanos(&t) == 0,
    {
        Timestamp { second: 0, nanosecond: 0 }
    }

    /// Origin Rust: pub const fn new_unchecked(secs: i64, nanos: i32) -> Timestamp
    ///     (timestamp.rs:100-110)
    /// Upstream doc (timestamp.rs:96-98):
    ///   Creates a new `Timestamp` without bounds checks.
    ///
    ///   Note that this should not be made public *and* safe.
    /// The upstream debug_assert!s of the body (timestamp.rs:101-108) are
    /// the requires of this translation (upstream debug tier -> spec
    /// tier); ts_inv is exactly their conjunction.
    pub(crate) exec fn new_unchecked(secs: i64, nanos: i32) -> (t: Timestamp)
        requires
            unix_seconds_ok(secs),
            subsec_nanos_ok(nanos),
            secs != UNIX_SECONDS_MIN || nanos >= 0,
            nanos == 0
                || secs == 0
                || (secs > 0 && nanos > 0)
                || (secs < 0 && nanos < 0),
        ensures
            ts_inv(&t),
            t.second == secs,
            t.nanosecond == nanos,
    {
        Timestamp { second: secs, nanosecond: nanos }
    }

    /// Origin Rust: pub const fn new(secs: i64, nanos: i32)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:43-84)
    /// Upstream doc (timestamp.rs:36-42):
    ///   Create a new timestamp from the given number of seconds and its
    ///   sub-second component.
    ///
    ///   This returns an error if `nanos` is not in the range specified by
    ///   `SignedSubsecNanosecond`. An error is also returned when `secs` is
    ///   not in the range specified by `UnixEpochSeconds`.
    /// The ensures below also carries the normalization face: the instant
    /// denoted by the Ok value is the input secs/nanos pair (the carry
    /// rebalancing is instant-preserving).
    pub exec fn new(secs: i64, nanos_in: i32) -> (r: Result<Timestamp, RangeError>)
        ensures
            match r {
                Result::Ok(t) => ts_inv(&t) && ts_total_nanos(&t)
                    == (secs as int) * 1_000_000_000 + (nanos_in as int),
                Result::Err(RangeError::UnixEpochSeconds) => !unix_seconds_ok(secs)
                    || (secs == UNIX_SECONDS_MIN && subsec_nanos_ok(nanos_in)
                        && nanos_in < 0),
                Result::Err(RangeError::SignedSubsecNanosecond) =>
                    unix_seconds_ok(secs) && !subsec_nanos_ok(nanos_in),
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        if !(UNIX_SECONDS_MIN <= secs && secs <= UNIX_SECONDS_MAX) {
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        if !(-999_999_999 <= nanos_in && nanos_in <= 999_999_999) {
            return Result::Err(RangeError::SignedSubsecNanosecond);
        }
        if secs == UNIX_SECONDS_MIN && nanos_in < 0 {
            // Upstream rbail!(b::UnixEpochSeconds::error()),
            // timestamp.rs:47-49 (variant reused -- see the file-head note).
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        let mut secs: i64 = secs;
        let mut nanos: i32 = nanos_in;
        // Fast path (timestamp.rs:50-54). The signum comparison of the
        // original is `secs.signum() == nanos.signum() as i64`, spelled
        // here as sign equality of the nonzero case.
        if nanos == 0 || secs == 0 || (secs > 0) == (nanos > 0) {
            return Result::Ok(Timestamp::new_unchecked(secs, nanos));
        }
        if secs < 0 {
            // At this point secs < 0 and nanos > 0.
            // Upstream safety comment (timestamp.rs:60-62): "Never wraps
            // because adding +1 to a negative i64 never overflows."
            // -- discharged as the overflow obligation of the line below;
            // it holds since 0 < secs.
            secs = secs + 1;
            // Upstream safety comment (timestamp.rs:64-68): "Never wraps
            // because subtracting +1_000_000_000 from a positive i32 never
            // overflows." -- holds since 1 <= nanos <= 999_999_999, so the
            // result is in [-999_999_999, -1].
            nanos = nanos - NANOS_PER_SEC_32;
        } else {
            // At this point secs > 0 and nanos < 0.
            // Upstream safety comment (timestamp.rs:72-76): "Never wraps
            // because subtracting +1 from a positive i64 never overflows."
            secs = secs - 1;
            // Upstream safety comment (timestamp.rs:77-81): "Never wraps
            // because adding +1_000_000_000 to a negative i32 never
            // overflows." -- holds since -999_999_999 <= nanos <= -1, so
            // the result is in [1, 999_999_999].
            nanos = nanos + NANOS_PER_SEC_32;
        }
        Result::Ok(Timestamp::new_unchecked(secs, nanos))
    }

    /// Origin Rust: pub const fn constant(second: i64, nanosecond: i32) -> Timestamp
    ///     (timestamp.rs:92-94)
    /// Upstream doc (timestamp.rs:86-90):
    ///   Creates a new `Timestamp` value in a `const` context.
    ///
    ///   This is identical to [`Timestamp::new`], except that it panics when
    ///   `Timestamp::new` would return an error. This can be more convenient in
    ///   a `const` context where unwrapping a `Result` is not ergonomic.
    /// # Panics-to-requires (timestamp.rs:89): the upstream panic on the
    /// error domain becomes the requires below; the Ok face of `new`
    /// (canonical form + instant preservation) is the postcondition.
    pub exec fn constant(second: i64, nanosecond: i32) -> (t: Timestamp)
        requires
            unix_seconds_ok(second),
            subsec_nanos_ok(nanosecond),
            second != UNIX_SECONDS_MIN || nanosecond >= 0,
        ensures
            ts_inv(&t),
            ts_total_nanos(&t)
                == (second as int) * 1_000_000_000 + (nanosecond as int),
    {
        let r = Timestamp::new(second, nanosecond);
        // The Err arm is statically dead under the requires (the Ok face
        // of `new`'s contract contradicts each Err disjunct); it is filled
        // with the translation-only dead-arm helper for typechecking.
        match r {
            Result::Ok(t) => t,
            Result::Err(_) => j4_dead_arm_unreachable(),
        }
    }

    /// Origin Rust: pub const fn from_second(second: i64)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:121-124)
    /// Upstream doc (timestamp.rs:112-119):
    ///   Constructs a timestamp from seconds since the Unix epoch.
    ///
    ///   This is preferred to [`Timestamp::new`] when it is known that the
    ///   sub-second component is always `0`. In particular, this generates
    ///   less code and is likely to be faster.
    ///
    ///   An error is returned when `second` is not in the range specified by
    ///   [`UnixEpochSeconds`](b::UnixEpochSeconds).
    pub exec fn from_second(second: i64) -> (r: Result<Timestamp, RangeError>)
        ensures
            match r {
                Result::Ok(t) => ts_inv(&t) && t.nanosecond == 0
                    && ts_total_nanos(&t) == (second as int) * 1_000_000_000,
                Result::Err(RangeError::UnixEpochSeconds) => !unix_seconds_ok(second),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        if !(UNIX_SECONDS_MIN <= second && second <= UNIX_SECONDS_MAX) {
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        Result::Ok(Timestamp::new_unchecked(second, 0))
    }

    /// Origin Rust: pub const fn from_millisecond(millisecond: i64)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:131-144)
    /// Upstream doc (timestamp.rs:126-129):
    ///   Constructs a timestamp from milliseconds since the Unix epoch.
    ///
    ///   An error is returned when `millisecond` is not in the range specified by
    ///   [`UnixEpochMilliseconds`](b::UnixEpochMilliseconds).
    pub exec fn from_millisecond(millisecond: i64) -> (r: Result<Timestamp, RangeError>)
        ensures
            match r {
                Result::Ok(t) => ts_inv(&t)
                    && ts_total_nanos(&t) == (millisecond as int) * 1_000_000,
                Result::Err(RangeError::UnixEpochSeconds) =>
                    !unix_millis_ok(millisecond),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        // b::UnixEpochMilliseconds::checkc (timestamp.rs:134), inline face.
        if !((UNIX_SECONDS_MIN * MILLIS_PER_SEC) <= millisecond
            && millisecond <= (UNIX_SECONDS_MAX * MILLIS_PER_SEC)) {
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        // Upstream safety comment (timestamp.rs:135): "OK because
        // MILLIS_PER_SEC!={-1,0}." -- division by the positive constant.
        // Upstream safety comment (timestamp.rs:136-141): "OK because
        // MILLIS_PER_SEC!={-1,0} and because millis % MILLIS_PER_SEC can
        // be at most 999, and 999 * 1_000_000 never overflows i32." --
        // discharged below: the i64 trunc remainder is in (-1_000, 1_000)
        // (guarded by the domain check above, exact div/mod facts per the
        // rust_div/rust_rem doctrine), so it narrows into i32 and the
        // nanosecond product stays inside +/- 999_999_999.
        let secs: i64 = millisecond / MILLIS_PER_SEC;
        let rem: i64 = millisecond % MILLIS_PER_SEC;
        let nanos: i32 = (rem as i32) * NANOS_PER_MILLI_32;
        proof {
            let d = 1_000;
            let q = (secs as int);
            let rem_i = (rem as int);
            assert(q == rust_div((millisecond as int), d));
            assert(rem_i == rust_rem((millisecond as int), d));
            // trunc facts via rust_div/rust_rem unfolding:
            assert((millisecond as int) == q * d + rem_i);
            assert(rem_i > -d && rem_i < d);
            // Domain carries: seconds land in range; the nanosecond
            // product stays inside the signed subsec bound; the trunc
            // remainder carries the sign of its dividend (from the
            // rust_div/rust_rem case definitions), so the pair's signs
            // agree.
            assert(unix_seconds_ok_int(q));
            assert(subsec_nanos_ok_int((nanos as int)));
            if rem_i < 0 {
                assert((millisecond as int) < 0);
                assert(q <= 0);
            }
            if rem_i > 0 {
                assert((millisecond as int) > 0);
                assert(q >= 0);
            }
        }
        Result::Ok(Timestamp::new_unchecked(secs, nanos))
    }

    /// Origin Rust: pub const fn from_microsecond(microsecond: i64)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:151-164)
    /// Upstream doc (timestamp.rs:146-149):
    ///   Constructs a timestamp from microseconds since the Unix epoch.
    ///
    ///   An error is returned when `microsecond` is not in the range specified
    ///   by [`UnixEpochMicroseconds`](b::UnixEpochMicroseconds).
    /// (Same safety-comment shape as from_millisecond: the trunc remainder
    ///  per second is in (-1_000_000, 1_000_000) and the product by
    ///  NANOS_PER_MICRO_32 = 1_000 stays inside the signed subsec bound.)
    pub exec fn from_microsecond(microsecond: i64) -> (r: Result<Timestamp, RangeError>)
        ensures
            match r {
                Result::Ok(t) => ts_inv(&t)
                    && ts_total_nanos(&t) == (microsecond as int) * 1_000,
                Result::Err(RangeError::UnixEpochSeconds) =>
                    !unix_micros_ok(microsecond),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        // b::UnixEpochMicroseconds::checkc (timestamp.rs:154), inline face.
        if !((UNIX_SECONDS_MIN * MICROS_PER_SEC) <= microsecond
            && microsecond <= (UNIX_SECONDS_MAX * MICROS_PER_SEC)) {
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        let secs: i64 = microsecond / MICROS_PER_SEC;
        let rem: i64 = microsecond % MICROS_PER_SEC;
        let nanos: i32 = (rem as i32) * NANOS_PER_MICRO_32;
        proof {
            let d = 1_000_000;
            let q = (secs as int);
            let rem_i = (rem as int);
            assert(q == rust_div((microsecond as int), d));
            assert(rem_i == rust_rem((microsecond as int), d));
            assert((microsecond as int) == q * d + rem_i);
            assert(rem_i > -d && rem_i < d);
            if microsecond < 0 {
                assert(rem_i <= 0);
            }
            if microsecond > 0 {
                assert(rem_i >= 0);
            }
            assert(unix_seconds_ok_int(q));
            assert(subsec_nanos_ok_int((nanos as int)));
            if rem_i < 0 {
                assert((microsecond as int) < 0);
                assert(q <= 0);
            }
            if rem_i > 0 {
                assert((microsecond as int) > 0);
                assert(q >= 0);
            }
        }
        Result::Ok(Timestamp::new_unchecked(secs, nanos))
    }

    /// Origin Rust: pub const fn from_nanosecond(nanosecond: i128)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:171-188)
    /// Upstream doc (timestamp.rs:166-169):
    ///   Constructs a timestamp from nanoseconds since the Unix epoch.
    ///
    ///   An error is returned when `nanosecond` refers to a timestamp outside
    ///   of the range [`Timestamp::MIN`] to [`Timestamp::MAX`].
    /// (Upstream regression #645 test at timestamp.rs:915-927 exercises
    ///  the error faces below -- the i64 narrowing guard first, the
    ///  minimum-second carry guard last.)
    pub exec fn from_nanosecond(nanosecond: i128) -> (r: Result<Timestamp, RangeError>)
        ensures
            match r {
                Result::Ok(t) => ts_inv(&t)
                    && ts_total_nanos(&t) == (nanosecond as int),
                Result::Err(RangeError::UnixEpochNanoseconds) =>
                    !(-(9223372036854775808int)
                        <= rust_div((nanosecond as int), 1_000_000_000)
                        && rust_div((nanosecond as int), 1_000_000_000)
                            <= 9223372036854775807int),
                Result::Err(RangeError::UnixEpochSeconds) =>
                    (-(9223372036854775808int)
                        <= rust_div((nanosecond as int), 1_000_000_000)
                        && rust_div((nanosecond as int), 1_000_000_000)
                            <= 9223372036854775807int)
                    && (!unix_seconds_ok_int(
                            rust_div((nanosecond as int), 1_000_000_000))
                        || (rust_div((nanosecond as int), 1_000_000_000)
                                == UNIX_SECONDS_MIN as int
                            && rust_rem((nanosecond as int), 1_000_000_000) < 0)),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
            },
    {
        // Upstream safety comment (timestamp.rs:175): "OK because
        // NANOS_PER_SEC!={-1,0}."
        let secs: i128 = nanosecond / 1_000_000_000;
        // Upstream guard (timestamp.rs:177-180): the i64 narrowing check
        // that keeps `secs as i64` (line 181) defined; modeled exactly.
        if !(-9223372036854775808i128 <= secs && secs <= 9223372036854775807i128) {
            return Result::Err(RangeError::UnixEpochNanoseconds);
        }
        let secs64: i64 = secs as i64;
        if !(UNIX_SECONDS_MIN <= secs64 && secs64 <= UNIX_SECONDS_MAX) {
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        // Upstream safety comment (timestamp.rs:182): "OK because
        // NANOS_PER_SEC!={-1,0}."
        let rem: i128 = nanosecond % 1_000_000_000;
        let nanosecond32: i32 = rem as i32;
        proof {
            let n = (nanosecond as int);
            let d = 1_000_000_000;
            let q = rust_div(n, d);
            let r = rust_rem(n, d);
            assert((secs as int) == q);
            let rem_i = (rem as int);
            assert(rem_i == r);
            assert(n == q * d + r);
            assert(r > -d && r < d);
            assert(subsec_nanos_ok_int(rem_i));
            // trunc remainder sign coupling (rust_rem case definition):
            if rem_i < 0 {
                assert(n < 0);
                assert(q <= 0);
            }
        }
        if secs64 == UNIX_SECONDS_MIN && nanosecond32 < 0 {
            // Upstream rbail!(b::UnixEpochSeconds::error()),
            // timestamp.rs:184-186 (variant reused -- file-head note).
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        Result::Ok(Timestamp::new_unchecked(secs64, nanosecond32))
    }

    /// Origin Rust: pub const fn as_second(self) -> i64
    ///     (timestamp.rs:195-197)
    /// Upstream doc (timestamp.rs:190-193):
    ///   Returns this timestamp as a number of seconds since the Unix epoch.
    ///
    ///   This only returns the number of whole seconds. That is, if there are
    ///   any fractional seconds in this timestamp, then they are truncated.
    pub exec fn as_second(&self) -> (r: i64)
        ensures
            r == self.second,
    {
        self.second
    }

    /// Origin Rust: pub const fn as_millisecond(self) -> i64
    ///     (timestamp.rs:206-213)
    /// Upstream doc (timestamp.rs:199-205):
    ///   Returns this timestamp as a number of milliseconds since the Unix
    ///   epoch.
    ///
    ///   This only returns the number of whole milliseconds. That is, if there
    ///   are any fractional milliseconds in this timestamp, then they are
    ///   truncated.
    /// Upstream safety comments (timestamp.rs:207-211): "OK because the
    /// range of `Timestamp` guarantees that its representation as
    /// milliseconds fits into an i64" and "subsec_millis maxes out at
    /// 999, and adding that to b::UnixSeconds::MAX*1_000 will never
    /// overflow an i64" -- both discharged as the overflow obligations
    /// below; the tight lower bound (UNIX_SECONDS_MIN * 1_000) needs the
    /// canonical minimum-second carry face, so the requires is the full
    /// upstream canonical tier ts_inv.
    pub exec fn as_millisecond(&self) -> (ms: i64)
        requires
            ts_inv(self),
        ensures
            (ms as int) == (self.second as int) * 1_000
                + rust_div((self.nanosecond as int), 1_000_000),
            (UNIX_SECONDS_MIN as int) * 1_000 <= ms as int,
            ms as int <= (UNIX_SECONDS_MAX as int) * 1_000 + 999,
    {
        // Upstream safety comment (timestamp.rs:209).
        let millis: i64 = self.as_second() * MILLIS_PER_SEC;
        // Upstream safety comment (timestamp.rs:212).
        let sub: i64 = (self.subsec_millisecond()) as i64;
        proof {
            let r = rust_div((self.nanosecond as int), 1_000_000);
            assert(self.nanosecond as int == r * 1_000_000
                + rust_rem((self.nanosecond as int), 1_000_000));
            let rem = rust_rem((self.nanosecond as int), 1_000_000);
            assert(rem >= -1_000_000 && rem < 1_000_000);
            assert(r >= -999 && r <= 999);
        }
        millis + sub
    }

    /// Origin Rust: pub const fn as_microsecond(self) -> i64
    ///     (timestamp.rs:222-229)
    /// Upstream doc (timestamp.rs:215-217):
    ///   Returns this timestamp as a number of microseconds since the Unix
    ///   epoch.
    ///
    ///   This only returns the number of whole microseconds. That is, if there
    ///   are any fractional microseconds in this timestamp, then they are
    ///   truncated.
    /// Same safety-comment shape as as_millisecond
    /// (timestamp.rs:223-228); same canonical-tier requires.
    pub exec fn as_microsecond(&self) -> (us: i64)
        requires
            ts_inv(self),
        ensures
            (us as int) == (self.second as int) * 1_000_000
                + rust_div((self.nanosecond as int), 1_000),
            (UNIX_SECONDS_MIN as int) * 1_000_000 <= us as int,
            us as int <= (UNIX_SECONDS_MAX as int) * 1_000_000 + 999_999,
    {
        let micros: i64 = self.as_second() * MICROS_PER_SEC;
        let sub: i64 = (self.subsec_microsecond()) as i64;
        proof {
            let r = rust_div((self.nanosecond as int), 1_000);
            assert(self.nanosecond as int == r * 1_000
                + rust_rem((self.nanosecond as int), 1_000));
            let rem = rust_rem((self.nanosecond as int), 1_000);
            assert(rem >= -1_000 && rem < 1_000);
            assert(r >= -999_999 && r <= 999_999);
        }
        micros + sub
    }

    /// Origin Rust: pub const fn as_nanosecond(self) -> i128
    ///     (timestamp.rs:234-240)
    /// Upstream doc (timestamp.rs:231-233):
    ///   Returns this timestamp as a number of nanoseconds since the Unix
    ///   epoch.
    /// Upstream safety comments (timestamp.rs:235-239): "1_000_000_000
    /// times any i64 will never overflow i128" and "nanosecond maxes out
    /// at 999_999_999, and adding that to i64::MAX*1_000_000_000 will
    /// never overflow a i128" -- discharged below from ts_field_inv.
    pub exec fn as_nanosecond(&self) -> (ns: i128)
        requires
            ts_field_inv(self),
        ensures
            (ns as int) == ts_total_nanos(self),
    {
        // Upstream safety comment (timestamp.rs:236-238): the explicit
        // bound below is the i128 fit face of "1_000_000_000 times any
        // UnixEpochSeconds value never overflows i128".
        proof {
            assert((self.second as int) >= -(377_705_023_201int));
            assert((self.second as int) <= 253_402_207_200int);
            assert((self.second as int) * 1_000_000_000
                <= 253_402_207_200_000_000_000int);
            assert((self.second as int) * 1_000_000_000
                >= -(377_705_023_201_000_000_000int));
        }
        let nanos: i128 = (self.second as i128) * (NANOS_PER_SEC_32 as i128);
        // Upstream safety comment (timestamp.rs:239).
        nanos + (self.nanosecond as i128)
    }

    /// Origin Rust: pub const fn subsec_millisecond(&self) -> i32
    ///     (timestamp.rs:249-252)
    /// Upstream doc (timestamp.rs:242-248):
    ///   Returns the fractional second component of this timestamp in units of
    ///   microseconds.
    ///
    ///   The value returned is negative when the timestamp is negative. It is
    ///   guaranteed that the range of the value returned is in the inclusive
    ///   range `-999_999..=999_999`.
    /// SPEC-DOC MISMATCH candidate J4-2 (suspects list, notes.md; not
    /// self-filed): the doc says "microseconds" and "-999_999..=999_999",
    /// but the impl divides by NANOS_PER_MILLI_32 = 1_000_000 -- the unit
    /// is milliseconds and the true range is -999..=999. The ensures
    /// below states the impl truth.
    pub exec fn subsec_millisecond(&self) -> (r: i32)
        requires
            subsec_nanos_ok(self.nanosecond),
        ensures
            (r as int) == rust_div((self.nanosecond as int), 1_000_000),
            -999 <= r,
            r <= 999,
    {
        // Upstream safety comment (timestamp.rs:250): "OK because
        // NANOS_PER_MILLI!={-1,0}."
        proof {
            let r = rust_div((self.nanosecond as int), 1_000_000);
            assert(self.nanosecond as int == r * 1_000_000
                + rust_rem((self.nanosecond as int), 1_000_000));
            let rem = rust_rem((self.nanosecond as int), 1_000_000);
            assert(rem >= -1_000_000 && rem < 1_000_000);
            assert(r >= -999 && r <= 999);
        }
        self.nanosecond / NANOS_PER_MILLI_32
    }

    /// Origin Rust: pub const fn subsec_microsecond(&self) -> i32
    ///     (timestamp.rs:261-264)
    /// Upstream doc (timestamp.rs:254-259):
    ///   Returns the fractional second component of this timestamp in units of
    ///   milliseconds.
    ///
    ///   The value returned is negative when the timestamp is negative. It is
    ///   guaranteed that the range of the value returned is in the inclusive
    ///   range `-999..=999`.
    /// SPEC-DOC MISMATCH candidate J4-2 (mirrored; suspects list): the doc
    /// says "milliseconds" and "-999..=999", but the impl divides by
    /// NANOS_PER_MICRO_32 = 1_000 -- the unit is microseconds and the true
    /// range is -999_999..=999_999.
    pub exec fn subsec_microsecond(&self) -> (r: i32)
        requires
            subsec_nanos_ok(self.nanosecond),
        ensures
            (r as int) == rust_div((self.nanosecond as int), 1_000),
            -999_999 <= r,
            r <= 999_999,
    {
        // Upstream safety comment (timestamp.rs:260): "OK because
        // NANOS_PER_MICRO!={-1,0}."
        proof {
            let r = rust_div((self.nanosecond as int), 1_000);
            assert(self.nanosecond as int == r * 1_000
                + rust_rem((self.nanosecond as int), 1_000));
            let rem = rust_rem((self.nanosecond as int), 1_000);
            assert(rem >= -1_000 && rem < 1_000);
            assert(r >= -999_999 && r <= 999_999);
        }
        self.nanosecond / NANOS_PER_MICRO_32
    }

    /// Origin Rust: pub const fn subsec_nanosecond(&self) -> i32
    ///     (timestamp.rs:273-275)
    /// Upstream doc (timestamp.rs:266-272):
    ///   Returns the fractional second component of this timestamp in units of
    ///   nanoseconds.
    ///
    ///   The value returned is negative when the timestamp is negative. It is
    ///   guaranteed that the range of the value returned is in the inclusive
    ///   range `-999,999,999..=999,999,999`.
    pub exec fn subsec_nanosecond(&self) -> (r: i32)
        requires
            subsec_nanos_ok(self.nanosecond),
        ensures
            r == self.nanosecond,
    {
        self.nanosecond
    }

    /// Origin Rust: pub const fn signum(self) -> i8
    ///     (timestamp.rs:305-314)
    /// Upstream doc (timestamp.rs:277-283):
    ///   Returns a number that represents the sign of this timestamp.
    ///
    ///   * When [`Timestamp::is_zero`] is true, this returns `0`.
    ///   * When [`Timestamp::is_positive`] is true, this returns `1`.
    ///   * When [`Timestamp::is_negative`] is true, this returns `-1`.
    ///
    ///   The above cases are mutually exclusive.
    /// (The upstream doc example, timestamp.rs:285-303, documents the
    ///  mixed-sign normalization of `new`; it is carried by `new`'s
    ///  postcondition instead of a doctest here.)
    pub exec fn signum(&self) -> (r: i8)
        requires
            ts_signs_agree(self),
        ensures
            // Behavioral face (the body's own case shape). Under the
            // requires the three cases are mutually exclusive, matching
            // the doc's last sentence; without the sign-carry requires a
            // disharmonious field pair (positive AND negative fields --
            // the J4-3 suspects outputs can produce one upstream) makes
            // signum report its positive verdict while is_negative ALSO
            // holds.
            if (self.second == 0 && self.nanosecond == 0) {
                r == 0
            } else if (self.second > 0 || self.nanosecond > 0) {
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
            // Upstream debug_assert!(self.is_negative()) (timestamp.rs:311):
            // discharged here -- not (zero or positive) implies some field
            // is negative.
            proof {
                assert(!(self.second == 0 && self.nanosecond == 0));
                assert(!(self.second > 0 || self.nanosecond > 0));
                assert(self.second <= 0 && self.nanosecond <= 0);
                assert(self.second < 0 || self.nanosecond < 0);
            }
            -1
        }
    }

    /// Origin Rust: pub const fn is_zero(self) -> bool
    ///     (timestamp.rs:327-329)
    /// Upstream doc (timestamp.rs:316-318):
    ///   Returns true if and only if this timestamp corresponds to the instant
    ///   in time known as the Unix epoch.
    pub exec fn is_zero(&self) -> (r: bool)
        ensures
            r <==> (self.second == 0 && self.nanosecond == 0),
    {
        self.second == 0 && self.nanosecond == 0
    }

    /// Origin Rust: pub const fn is_positive(&self) -> bool
    ///     (timestamp.rs:343-345)
    /// Upstream doc (timestamp.rs:331-333):
    ///   Returns true when this timestamp is positive. That is, after the Unix
    ///   epoch.
    pub exec fn is_positive(&self) -> (r: bool)
        ensures
            r <==> (self.second > 0 || self.nanosecond > 0),
    {
        self.second > 0 || self.nanosecond > 0
    }

    /// Origin Rust: pub const fn is_negative(&self) -> bool
    ///     (timestamp.rs:359-361)
    /// Upstream doc (timestamp.rs:347-349):
    ///   Returns true when this timestamp is negative. That is, before the Unix
    ///   epoch.
    pub exec fn is_negative(&self) -> (r: bool)
        ensures
            r <==> (self.second < 0 || self.nanosecond < 0),
    {
        self.second < 0 || self.nanosecond < 0
    }

    /// Origin Rust: b::UnixEpochSeconds::checked_add (bounds.rs:710-722,
    /// `Bounds` trait face of the define_bounds! expansion),
    /// materialized inline for this file: the checked i64 sum is kept
    /// only when it lands in the UnixEpochSeconds domain (upstream errors
    /// with TryFromIntError/RangeError on the two failure modes; the
    /// domain test subsumes the i64 overflow test).
    pub exec fn checked_add_unix_seconds(a: i64, b: i64) -> (r: Result<i64, RangeError>)
        ensures
            match r {
                Result::Ok(v) =>
                    (v as int) == ((a as int) + (b as int))
                        && unix_seconds_ok_int((v as int)),
                Result::Err(RangeError::UnixEpochSeconds) =>
                    !unix_seconds_add_ok(a, b),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        let opt = a.checked_add(b);
        match opt {
            Option::None => Result::Err(RangeError::UnixEpochSeconds),
            Option::Some(sum) => {
                if UNIX_SECONDS_MIN <= sum && sum <= UNIX_SECONDS_MAX {
                    Result::Ok(sum)
                } else {
                    Result::Err(RangeError::UnixEpochSeconds)
                }
            }
        }
    }

    /// Origin Rust: pub const fn checked_add(self, seconds: i64,
    ///     nanos: i32) -> Result<Timestamp, RangeError>
    ///     (timestamp.rs:412-432)
    /// Upstream doc (timestamp.rs:372-375):
    ///   Add the given number of seconds and nanoseconds to this timestamp.
    ///
    ///   If this would result in a timestamp outside of its boundaries, then
    ///   this returns an error.
    /// Upstream # Examples (timestamp.rs:377-410) pin the mixed-sign carry
    /// faces (mkts(123, 0) + (1, -1) = mkts(123, 999_999_999), etc.) --
    /// carried here by the instant-preserving postcondition.
    /// Requires upgrade over upstream: ts_field_inv of self (the upstream
    /// safety comments implicitly rely on the field domains).
    pub exec fn checked_add(&self, seconds_in: i64, nanos_in: i32)
        -> (r: Result<Timestamp, RangeError>)
        requires
            ts_field_inv(self),
        ensures
            match r {
                Result::Ok(t) => ts_range_inv(&t)
                    // SPEC-DOC MISMATCH candidate J4-1 (suspects list,
                    // notes.md): upstream's own canonical tier
                    // ts_inv (new_unchecked's debug asserts,
                    // timestamp.rs:101-108) is NOT preservable -- the
                    // verus counterexample transcript is in notes.md. The
                    // postcondition states the preservable tier.
                    && ts_total_nanos(&t) == ts_total_nanos(self)
                        + (seconds_in as int) * 1_000_000_000
                        + (nanos_in as int),
                Result::Err(_) => true,
            },
    {
        let mut seconds: i64 = seconds_in;
        let mut nanos: i32 = nanos_in;
        // When |nanos| exceeds one second, balance the excess up to
        // seconds (timestamp.rs:417-429).
        if !(-NANOS_PER_SEC_32 < nanos && nanos < NANOS_PER_SEC_32) {
            // Upstream safety comment (timestamp.rs:419): "Never wraps or
            // panics because NANOS_PER_SEC!={0,-1}." -- the trunc division
            // below is reasoned through rust_div/rust_rem.
            let addsecs: i32 = nanos / NANOS_PER_SEC_32;
            // Upstream panic site (timestamp.rs:421-426):
            // `seconds.checked_add(addsecs as i64)`, panicking "nanoseconds
            // overflowed seconds in SignedDuration::new" on None.
            // Reachable (e.g. seconds = i64::MAX - 1 with nanos =
            // i32::MAX) -- transcribed faithfully via the external-body
            // panic face; suspects J4-P1.
            let opt = seconds.checked_add(addsecs as i64);
            seconds = match opt {
                Option::Some(v) => v,
                Option::None => upstream_panic_balance_overflow(),
            };
            proof {
                let q = rust_div((nanos as int), 1_000_000_000);
                assert((addsecs as int) == q);
                assert((nanos as int) == q * 1_000_000_000
                    + rust_rem((nanos as int), 1_000_000_000));
                assert(-3 <= q && q <= 3);
            }
            // Upstream safety comment (timestamp.rs:427-428): "Never wraps
            // or panics because NANOS_PER_SEC!={0,-1}."
            nanos = nanos % NANOS_PER_SEC_32;
            proof {
                let v = 1_000_000_000;
                let q = rust_div((nanos_in as int), v);
                let r = rust_rem((nanos_in as int), v);
                assert((addsecs as int) == q);
                assert((nanos as int) == r);
                assert((nanos_in as int) == q * v + r);
                assert(r > -v && r < v);
                let s2 = (seconds as int);
                assert(s2 == (seconds_in as int) + q);
                // The prebalance is instant-preserving:
                assert((seconds_in as int) * v + (nanos_in as int)
                    == s2 * v + (r));
            }
        }
        self.checked_add_sensible(seconds, nanos)
    }

    /// Origin Rust: const fn checked_add_sensible(self, seconds: i64,
    ///     nanos: i32) -> Result<Timestamp, RangeError>
    ///     (timestamp.rs:501-548)
    /// "Implementation of `checked_add` that assumes `|nanos| < 1 second`"
    /// (upstream doc comment, timestamp.rs:499) -- the debug_assert of the
    /// original body (timestamp.rs:506-508) is this function's requires.
    /// Upstream safety comments (timestamp.rs:512-513): "OK because we
    /// know both are in the inclusive range [-999_999_999, 999_999_999]
    /// per above math" -- the i32 addition below is its obligation.
    pub exec fn checked_add_sensible(&self, seconds: i64, nanos_in: i32)
        -> (r: Result<Timestamp, RangeError>)
        requires
            ts_field_inv(self),
            -(1_000_000_000int) < (nanos_in as int),
            (nanos_in as int) < 1_000_000_000int,
        ensures
            match r {
                Result::Ok(t) => ts_range_inv(&t)
                    // SPEC-DOC MISMATCH candidate J4-1 (suspects list):
                    // upstream's canonical tier ts_inv includes the
                    // minimum-second carry guard ts_min_ok; verified NOT
                    // preservable (counterexample transcript in
                    // notes.md), so this postcondition ships the
                    // preservable tier ts_range_inv and the honest
                    // instant-preserving identity.
                    && ts_total_nanos(&t) == ts_total_nanos(self)
                        + (seconds as int) * 1_000_000_000
                        + (nanos_in as int),
                Result::Err(_) => true,
            },
    {
        // Origin Rust line 510-511: b::UnixEpochSeconds::checked_add.
        let second_r = Timestamp::checked_add_unix_seconds(self.second, seconds);
        let mut second: i64 = match second_r {
            Result::Ok(v) => v,
            Result::Err(_) => return Result::Err(RangeError::UnixEpochSeconds),
        };
        // Upstream safety comment (timestamp.rs:512-513): the two
        // addends are in [-999_999_999, 999_999_999] and
        // (-999_999_999, 999_999_999) respectively, so the i64-widened
        // sum below stays in the i32 domain.
        let mut nanosecond: i32 = self.nanosecond + nanos_in;
        proof {
            assert(-999_999_999 <= self.nanosecond as int);
            assert(self.nanosecond as int <= 999_999_999);
            assert(-(999_999_999int) <= (nanos_in as int));
            assert((nanos_in as int) <= 999_999_999);
        }
        if nanosecond == 0 {
            // timestamp.rs:517-519: zero carry passthrough.
            return Result::Ok(Timestamp { second, nanosecond });
        }
        if nanosecond >= NANOS_PER_SEC_32 {
            // Upstream carry: timestamp.rs:521-523.
            nanosecond = nanosecond - NANOS_PER_SEC_32;
            let second_r = Timestamp::checked_add_unix_seconds(second, 1);
            second = match second_r {
                Result::Ok(v) => v,
                Result::Err(_) => return Result::Err(RangeError::UnixEpochSeconds),
            };
        } else if nanosecond <= -NANOS_PER_SEC_32 {
            // Upstream carry: timestamp.rs:524-527.
            nanosecond = nanosecond + NANOS_PER_SEC_32;
            let second_r = Timestamp::checked_add_unix_seconds(second, -1);
            second = match second_r {
                Result::Ok(v) => v,
                Result::Err(_) => return Result::Err(RangeError::UnixEpochSeconds),
            };
        }
        // timestamp.rs:528-546: the sign-balance normalization.
        if second != 0
            && nanosecond != 0
            && !((second > 0) == (nanosecond > 0))
        {
            if second < 0 {
                // Upstream safety comment (timestamp.rs:534-535): "OK
                // because second<0." -- the +1 below cannot overflow.
                second = second + 1;
                // Upstream safety comment (timestamp.rs:536-537): "OK
                // because nanosecond>0." -- the subtraction lands in
                // [-999_999_999, -1].
                nanosecond = nanosecond - NANOS_PER_SEC_32;
            } else {
                // Upstream safety comments (timestamp.rs:541-544): "OK
                // because second>0" and "OK because nanosecond<0".
                second = second - 1;
                nanosecond = nanosecond + NANOS_PER_SEC_32;
            }
        }
        Result::Ok(Timestamp { second, nanosecond })
    }

    /// Origin Rust: pub const fn checked_sub(self, seconds: i64,
    ///     nanos: i32) -> Result<Timestamp, RangeError>
    ///     (timestamp.rs:472-497)
    /// Upstream doc (timestamp.rs:434-436):
    ///   Subtracts the given number of seconds and nanoseconds from this
    ///   timestamp.
    /// (The upstream # Examples block, timestamp.rs:438-469, pins the same
    ///  mixed-sign faces mirrored around subtraction.)
    pub exec fn checked_sub(&self, seconds_in: i64, nanos_in: i32)
        -> (r: Result<Timestamp, RangeError>)
        requires
            ts_field_inv(self),
        ensures
            match r {
                Result::Ok(t) => ts_range_inv(&t)
                    // SPEC-DOC MISMATCH candidate J4-1 (suspects list):
                    // same minimum-second carry gap as checked_add.
                    && ts_total_nanos(&t) == ts_total_nanos(self)
                        - (seconds_in as int) * 1_000_000_000
                        - (nanos_in as int),
                Result::Err(_) => true,
            },
    {
        // Upstream seconds negation with the i64::MIN error
        // (timestamp.rs:477-479; upstream checked_neg spelled from the
        // explicit comparison so the negation below carries its size
        // obligation directly).
        let mut seconds: i64;
        if seconds_in == -9223372036854775808i64 {
            return Result::Err(RangeError::UnixEpochSeconds);
        } else {
            seconds = -seconds_in;
        }
        let mut nanos: i32 = nanos_in;
        // When |nanos| exceeds one second, balance the excess up to
        // seconds (timestamp.rs:481-493).
        if !(-NANOS_PER_SEC_32 < nanos && nanos < NANOS_PER_SEC_32) {
            // Upstream safety comment (timestamp.rs:483): "Never wraps or
            // panics because NANOS_PER_SEC!={0,-1}."
            let addsecs: i32 = nanos / NANOS_PER_SEC_32;
            // Upstream panic site (timestamp.rs:485-491):
            // `seconds.checked_sub(addsecs as i64)`, same reachable
            // panic string -- suspects J4-P2, transcribed faithfully.
            let opt = seconds.checked_sub(addsecs as i64);
            seconds = match opt {
                Option::Some(v) => v,
                Option::None => upstream_panic_balance_overflow(),
            };
            // Upstream safety comment (timestamp.rs:491-492): "Never wraps
            // or panics because NANOS_PER_SEC!={0,-1}."
            nanos = nanos % NANOS_PER_SEC_32;
            proof {
                let v = 1_000_000_000;
                let qq = rust_div((nanos_in as int), v);
                let r = rust_rem((nanos_in as int), v);
                assert((addsecs as int) == qq);
                assert((nanos as int) == r);
                assert(r > -v && r < v);
                let s2 = (seconds as int);
                // seconds was -seconds_in up to the checked_sub above:
                assert(s2 == (-(seconds_in as int)) - qq);
            }
        }
        // Upstream safety comment (timestamp.rs:494-495): "Negating `nanos`
        // here is OK because the above guarantees that it's in the
        // inclusive range `[-999_999_999, 999_999_999]`." -- the i32
        // negation below is its obligation (|nanos| < 1e9 either from the
        // input directly or from the prebalance remainder).
        let negnanos: i32 = -nanos;
        proof {
            assert(-999_999_999 <= (nanos as int));
            assert((nanos as int) <= 999_999_999);
        }
        self.checked_add(seconds, negnanos)
    }

    /// Origin Rust: pub const fn checked_add_seconds(self, seconds: i64)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:579-586)
    /// Upstream doc (timestamp.rs:550-556):
    ///   Add the given number of seconds to this timestamp.
    ///
    ///   If this would result in a timestamp outside of its boundaries, then
    ///   this returns an error.
    ///
    ///   The nanosecond component of the timestamp returned is guaranteed to
    ///   match the nanosecond component of `self`.
    /// Upstream # Examples (timestamp.rs:558-577) pin the pure-seconds
    /// add faces.
    /// SPEC-DOC MISMATCH candidate J4-3 (suspects list): the upstream
    /// canonical tier (signs agree, min-second guard -- new_unchecked's
    /// debug asserts) is NOT preservable here (e.g. valid self
    /// {second: -1, nanosecond: -500_000_000} plus 2 seconds returns
    /// {second: 1, nanosecond: -500_000_000}, a sign-disharmonious
    /// representation violating Timestamp's derived Ord/Eq semantics);
    /// the postcondition ships the preservable tier ts_field_inv plus
    /// the nanosecond-identity and instant faces.
    pub exec fn checked_add_seconds(&self, seconds: i64)
        -> (r: Result<Timestamp, RangeError>)
        requires
            ts_field_inv(self),
        ensures
            match r {
                Result::Ok(t) => ts_field_inv(&t)
                    && t.nanosecond == self.nanosecond
                    && ts_total_nanos(&t) == ts_total_nanos(self)
                        + (seconds as int) * 1_000_000_000,
                Result::Err(RangeError::UnixEpochSeconds) =>
                    !unix_seconds_add_ok(self.second, seconds),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        // Origin Rust line 583-584: b::UnixEpochSeconds::checked_add.
        let second_r = Timestamp::checked_add_unix_seconds(self.second, seconds);
        match second_r {
            Result::Ok(second) => Result::Ok(Timestamp {
                second,
                nanosecond: self.nanosecond,
            }),
            Result::Err(_) => Result::Err(RangeError::UnixEpochSeconds),
        }
    }

    /// Origin Rust: pub const fn checked_sub_seconds(self, seconds: i64)
    ///     -> Result<Timestamp, RangeError> (timestamp.rs:590-598)
    /// (Upstream doc comment is only the one-liner "Subtracts the given
    ///  number of seconds from this timestamp.")
    /// Same SPEC-DOC MISMATCH candidate J4-3 as checked_add_seconds.
    pub exec fn checked_sub_seconds(&self, seconds: i64)
        -> (r: Result<Timestamp, RangeError>)
        requires
            ts_field_inv(self),
        ensures
            match r {
                Result::Ok(t) => ts_field_inv(&t)
                    && t.nanosecond == self.nanosecond
                    && ts_total_nanos(&t) == ts_total_nanos(self)
                        - (seconds as int) * 1_000_000_000,
                Result::Err(RangeError::UnixEpochSeconds) =>
                    !unix_seconds_ok_int(
                        (self.second as int) - (seconds as int)),
                Result::Err(RangeError::SignedSubsecNanosecond) => false,
                Result::Err(RangeError::UnixEpochNanoseconds) => false,
            },
    {
        // Upstream seconds negation with the i64::MIN error
        // (timestamp.rs:594-596).
        if seconds == -9223372036854775808i64 {
            return Result::Err(RangeError::UnixEpochSeconds);
        }
        let neg_seconds: i64 = -seconds;
        self.checked_add_seconds(neg_seconds)
    }

    /// Origin Rust: impl core::ops::Add<i64> for Timestamp { fn add(self,
    ///     seconds: i64) -> Timestamp { self.checked_add_seconds(seconds)
    ///     .unwrap() } } (timestamp.rs:631-637)
    /// Upstream doc (timestamp.rs:616-621):
    ///   Adds a number of seconds to a `Timestamp`.
    ///
    ///   # Panics
    ///   When adding would result in a value outside the boundaries of a
    ///   `Timestamp`.
    /// # Panics-to-requires: the unwrap panic becomes the requires below
    /// (checked_add_seconds errors exactly on its violation).
    pub exec fn add_seconds(&self, seconds: i64) -> (t: Timestamp)
        requires
            ts_field_inv(self),
            unix_seconds_add_ok(self.second, seconds),
        ensures
            // SPEC-DOC MISMATCH candidate J4-3 carried from
            // checked_add_seconds (suspects list).
            ts_field_inv(&t),
            t.nanosecond == self.nanosecond,
            ts_total_nanos(&t) == ts_total_nanos(self)
                + (seconds as int) * 1_000_000_000,
    {
        let r = self.checked_add_seconds(seconds);
        match r {
            Result::Ok(t) => t,
            Result::Err(_) => j4_dead_arm_unreachable(),
        }
    }

    /// Origin Rust: impl core::ops::Sub<i64> for Timestamp { fn sub(self,
    ///     seconds: i64) -> Timestamp { self.checked_sub_seconds(seconds)
    ///     .unwrap() } } (timestamp.rs:703-709)
    /// Upstream doc (timestamp.rs:688-696):
    ///   Subtracts a number of seconds from a `Timestamp`.
    ///   # Panics
    ///   When adding would result in a value outside the boundaries of a
    ///   `Timestamp`.
    /// (Upstream's # Panics text says "adding" verbatim.)
    pub exec fn sub_seconds(&self, seconds: i64) -> (t: Timestamp)
        requires
            ts_field_inv(self),
            unix_seconds_ok_int((self.second as int) - (seconds as int)),
        ensures
            // SPEC-DOC MISMATCH candidate J4-3 carried from
            // checked_sub_seconds (suspects list).
            ts_field_inv(&t),
            t.nanosecond == self.nanosecond,
            ts_total_nanos(&t) == ts_total_nanos(self)
                - (seconds as int) * 1_000_000_000,
    {
        let r = self.checked_sub_seconds(seconds);
        match r {
            Result::Ok(t) => t,
            Result::Err(_) => j4_dead_arm_unreachable(),
        }
    }

    /// Origin Rust: impl core::ops::AddAssign<i64> for Timestamp
    ///     (timestamp.rs:668-673), forwarding to the Add<i64> pair.
    /// (The *self mutation is dropped for the value-returning verifier
    ///  face; the # Panics-to-requires conversion of the upstream doc
    ///  (timestamp.rs:662-667) is inherited from add_seconds.)
    ///
    /// SEPARATE note (origin impl core::ops::SubAssign<i64>,
    /// timestamp.rs:740-745): its upstream body is `*self = *self + rhs`
    /// -- the ADDITION -- while its doc (timestamp.rs:734-739) documents
    /// subtraction. This divergence is recorded as suspects entry J4-4
    /// (runtime contrast: `ts -= x` moves x seconds forward upstream);
    /// the sub_assign translation below follows the documented
    /// subtraction contract, not the copy-pasted body.
    pub exec fn add_assign_seconds(&self, seconds: i64) -> (t: Timestamp)
        requires
            ts_field_inv(self),
            unix_seconds_add_ok(self.second, seconds),
        ensures
            ts_field_inv(&t),
            t.nanosecond == self.nanosecond,
            ts_total_nanos(&t) == ts_total_nanos(self)
                + (seconds as int) * 1_000_000_000,
    {
        self.add_seconds(seconds)
    }

    /// Origin Rust: impl core::ops::SubAssign<i64> for Timestamp
    ///     (timestamp.rs:740-745): upstream body is `*self = *self + rhs`
    ///     -- the ADDITION -- while its doc (timestamp.rs:734-739)
    ///     documents subtraction.
    /// SPEC-DOC MISMATCH candidate J4-4 (suspects list, notes.md; upstream
    /// issue number not yet available): the translation below follows
    /// the documented subtraction contract, not the addition body
    /// (runtime contrast: `ts -= x` moves x seconds forward upstream);
    /// see the SEPARATE note above add_assign_seconds.
    pub exec fn sub_assign_seconds(&self, seconds: i64) -> (t: Timestamp)
        requires
            ts_field_inv(self),
            unix_seconds_ok_int((self.second as int) - (seconds as int)),
        ensures
            ts_field_inv(&t),
            t.nanosecond == self.nanosecond,
            ts_total_nanos(&t) == ts_total_nanos(self)
                - (seconds as int) * 1_000_000_000,
    {
        self.sub_seconds(seconds)
    }

    /// Origin Rust: impl Default for Timestamp { fn default() ->
    ///     Timestamp { Timestamp::UNIX_EPOCH } } (timestamp.rs:609-614)
    pub exec fn default() -> (t: Timestamp)
        ensures
            ts_inv(&t),
            t.second == 0,
            t.nanosecond == 0,
    {
        Timestamp::unix_epoch()
    }

    // =======================================================================
    // Deferred (recorded, not translated -- see the J4 notes tail list):
    // - to_datetime/Offset + Debug (timestamp.rs:363-370, :601-607):
    //   tz::Offset and civil::DateTime / string-format faces (J3 and the
    //   out-of-scope fmt declaration).
    // - core::ops::Add<(i64, i32)> / Sub<(i64, i32)> and their AddAssign/
    //   SubAssign forms (timestamp.rs:654-660, :726-732, :681-686,
    //   :753-758): their unwrap-Ok precondition cannot be stated without
    //   the spec twin of checked_add's Ok face; deferred to the ops
    //   harness batch. (Suspects J4-P1/J4-P3 note: these operators
    //   inherit the reachable balance panic and the Err-at-in-boundary
    //   face of checked_add -- e.g. {UNIX_SECONDS_MAX - 1, 999_999_999}
    //   + (2, 0) errors although {UNIX_SECONDS_MAX, 999_999_999} is a
    //   representable in-boundaries value, so the documented # Panics
    //   condition is NOT the exact panic domain upstream.)
    // - arbitrary/quickcheck impls (timestamp.rs:760-815): test tier.
    // =======================================================================
}

} // verus!
