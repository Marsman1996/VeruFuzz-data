//! jiff 0.2.43 Span compare / total / fieldwise family (crates/jiff/
//! src/span.rs, 7587 lines, pin tree read-only) -- Verus translation,
//! batch J11 (the J5/J8 deferred list's compare/total/fieldwise
//! trio).
//!
//! Upstream scope (line numbers measured on the pin tree):
//! 1. span.rs:1426-1457 `Span::fieldwise` and span.rs:3460-3595
//!    `SpanFieldwise` (the struct, `Neg`, `Eq`/`PartialEq` and its
//!    cross-type `PartialEq` variants, `Hash`, the two `From` impls).
//! 2. span.rs:1884-1982 `Span::compare` + span.rs:4360-4535
//!    `SpanCompare` (the struct, `new`, the private `compare` body
//!    span.rs:4512-4534 whose relative==None arm is translated here,
//!    and `From<Span>` at :4537; the relative/-dated `From` impls ride
//!    prune 2).
//! 3. span.rs:1984-2126 `Span::total` + span.rs:4607-4891 `SpanTotal`
//!    (the struct, `new` at :4808-4811, the private `total` body
//!    span.rs:4813-4862 with `total_invariant` at :4864-4874, and
//!    `From<Unit>` at :4877-4882).
//! 4. span.rs:6730-6739 `requires_relative_date_err` -- consumed as
//!    the J10 spec face `sr_requires_relative_err` (jcore_round.rs),
//!    not re-translated.
//! 5. The upstream doc examples and unit-test rows carried as witness
//!    panels: compare doc rows (span.rs:1919-1938), the
//!    SpanCompare/days-are-24-hours error row (:4483-4496), the
//!    fieldwise-vs-compare rows (:3495-3508), the total doc row
//!    (:2020-2021), the total test rows (:6757-6759) and the compare
//!    sort test row (:6826-6831).
//!
//! There is NO upstream `Span::checked_compare`, NO `lenient`/`strict`
//! `get` family, and no macro-generated surface inside this segment --
//! the three names the batch mandate recalled do not grep in the pin
//! tree (span.rs has no `checked_compare`/`lenient` hit; the only
//! macro_rules with `fieldwise` are the test macros `span_eq!` at
//! span.rs:15-25). The mandate's "u64/i64 dual forms" of total do not
//! exist either: upstream `Span::total` returns `f64` only. Recorded
//! in the batch notes.
//!
//! Driver mount: `verified/j11-driver.rs` mounts this file via
//! #[path] next to `src/bounds.rs`, `src/constants.rs`,
//! `src/jcore_signed_duration.rs`, `src/jcore_span.rs`,
//! `src/jcore_span_arith.rs` and `src/jcore_round.rs` (the j10-driver
//! precedent: the closed panels re-verify in this driver's run;
//! src/lib.rs is NOT touched by this batch).
//!
//! List of modeling losses / prunes (each also annotated at its site):
//! 1. Result<T, Error> surfaces materialize as Option<T> (the J1/J5
//!    ledger: error kinds are zero-sized witnesses, error-message
//!    text is quoted in comments but not verified). The compare/total
//!    faces are exact two-sided: the None arm is always the exact
//!    negation of the guard predicate, never a vacuous `true` face.
//! 2. The `relative: Option<SpanRelativeTo<'a>>` fields of both
//!    `SpanCompare` (span.rs:4394) and `SpanTotal` (span.rs:4690) are
//!    clipped with the relative pipeline (SpanRelativeTo / to_relative
//!    / Relative / RelativeCivil / into_relative_span, span.rs:5481-
//!    5708 and :5868-6630): the concurrent J9 batch owns that file,
//!    so this file translates the relative==None arms only -- the
//!    arms whose bodies upstream route through
//!    requires_relative_date_err + the invariant duration. The
//!    `relative()` setters (:4464-4469, :4759-4764) and
//!    `days_are_24_hours` (:4501-4503, :4802-4804), and with them the
//!    DST-comparing / 24-hour-day doc rows (:1941-1971, :2026-2072,
//!    :4429-4462, :4726-4800, :4840-4862), stay deferred with it.
//! 3. The `f64` value shape of `Span::total` (span.rs:2120-2126,
//!    total_invariant :4864-4874) is clipped to the exact rational
//!    underneath: the translated value is the (i128 numer, i128 denom)
//!    pair -- upstream's own precision comment (:4867-4872, quoted at
//!    the site) says the f64 is `nanos_numer / unit_nanos` cast at the
//!    edges, so the ratio pair IS the value upstream approximates.
//!    The IEEE double conversion `(dur as f64) / (unit_nanos as
//!    f64)` itself is not modeled (no float-verification seat in this
//!    toolchain); the exact-divisibility fact (no fractional
//!    component) and the exact rational identity are what the panels
//!    pin.
//! 4. `std::cmp::Ordering` (the return type of the derived compare,
//!    span.rs:1979) materializes as the `SpOrdering` enum (verbatim
//!    variant names; std has no verus-discipline contract to lean on).
//! 5. `SpanFieldwise` upstream is a `repr(transparent)` tuple struct
//!    `SpanFieldwise(pub Span)` (span.rs:3515); it materializes with
//!    the field named `span` (verus field discipline -- pitfall 57
//!    family), with the layout sentence recorded at the struct site.
//! 6. The `Hash` impl (span.rs:3569-3583) is clipped: Hasher plumbing
//!    is std stringlight; the semantic content -- the 11-value feed
//!    sequence (sign then the ten unit magnitudes) -- is recorded at
//!    the site, with the eq-implies-same-sequence implication noted
//!    as definitional once the sequence is spelled.
//! 7. The by-reference `PartialEq` variants for `&SpanFieldwise` /
//!    `&Span` (span.rs:3545-3549, :3563-3567) are auto-deref sugar
//!    over the by-value comparisons and add no semantic content;
//!    noted, not re-translated. `From<SpanFieldwise> for Span`
//!    (:3591-3594) is the field read of a moved value -- its content
//!    is the .span accessor every face here already provides.

use vstd::prelude::*;

use crate::bounds::Sign;
use crate::jcore_signed_duration::{
    SignedDuration, sd_inv, sd_total_nanos,
};
use crate::jcore_span::{
    Span, Unit, sp_field_inv, sp_flags_ok, sp_sign_eq,
    sp_sign_of_ref, sp_zero_sign_ok,
};
use crate::jcore_span_arith::{
    sp_inv_total_nanos, sp_span_largest, sp_unit_max, sp_unit_max_exec,
    sp_unit_rank, sp_unit_rank_exec,
};
use crate::jcore_round::{rm_unit_nanos, sr_requires_relative_err};

verus! {

// ===========================================================================
// (0) The Ordering enum (std::cmp::Ordering, the return type of
// Span::compare, span.rs:1976-1982).
// ===========================================================================

/// Origin Rust: std::cmp::Ordering (the public return type of the
/// derived Ord family; materialized because std carries no
/// verus-discipline contract). The three variants match upstream's
/// exactly.
#[derive(Clone, Copy)]
pub enum SpOrdering {
    Less,
    Equal,
    Greater,
}

/// The total-nanoseconds trichotomy face of an ordering: which
/// side of the (t2 - t1) sign the variant names.
pub open spec fn spc_ordering_of_totals(t1: int, t2: int, o: SpOrdering) -> bool {
    match o {
        SpOrdering::Less => t1 < t2,
        SpOrdering::Equal => t1 == t2,
        SpOrdering::Greater => t1 > t2,
    }
}

// ===========================================================================
// (1) The lex-vs-total ordering bridge. Upstream compares the two
// invariant durations with the DERIVED Ord of SignedDuration
// (`dur1.cmp(&dur2)`, span.rs:4528) -- a lexicographic (secs, nanos)
// compare -- while the canonical elapsed-time meaning is the total
// nanoseconds sd_total_nanos. The two orders coincide on canonical
// durations; this is the consumption seat of the J5 sd64_lex_equiv
// groundwork (jcore_span.rs:3626), extended from the range question
// to the full trichotomy.
// ===========================================================================

/// Lex-to-total, the Less clauses: a lex-smaller canonical duration
/// has strictly fewer total nanoseconds. The reverse (`Less` by
/// totals on canonical values) needs no lemma -- both bridges below
/// feed the exec compare, whose arms decide the direction.
///
/// The sign-agreement tier of sd_inv (secs and nanos signs agree)
/// is REQUIRED for the secs-differ case: without it,
/// {secs: 6, nanos: -999_999_999} would sit lex-above
/// {secs: 5, nanos: +999_999_999} while totalling below it. The
/// sp_to_invariant_duration producer guarantees sd_inv, so every
/// in-transit duration this batch compares is canonical.
pub proof fn spc_lex_total_less(
    d1: &SignedDuration,
    d2: &SignedDuration,
)
    requires
        sd_inv(d1),
        sd_inv(d2),
    ensures
        (((d1.secs as int) < (d2.secs as int))
            ==> (sd_total_nanos(d1) < sd_total_nanos(d2))),
        ((d1.secs == d2.secs)
            && ((d1.nanos as int) < (d2.nanos as int))
            ==> (sd_total_nanos(d1) < sd_total_nanos(d2))),
{
    let s1: int = d1.secs as int;
    let s2: int = d2.secs as int;
    let n1: int = d1.nanos as int;
    let n2: int = d2.nanos as int;
    assert(sd_total_nanos(d1) == s1 * 1_000_000_000 + n1);
    assert(sd_total_nanos(d2) == s2 * 1_000_000_000 + n2);
    if (s1 < s2) {
        // sd_inv's nanos domain.
        assert(-999_999_999 <= n1 && n1 <= 999_999_999);
        assert(-999_999_999 <= n2 && n2 <= 999_999_999);
        assert(s2 >= s1 + 1);
        if (n1 <= 0) {
            // total1 <= s1 * 1e9 <= (s2 - 1) * 1e9, and total2 >=
            // s2 * 1e9 - 999_999_999 -- a full grid step between the
            // two floors.
            assert(s1 * 1_000_000_000 + n1 <= s2 * 1_000_000_000
                - 1_000_000_000);
            assert(s2 * 1_000_000_000 + n2 >= s2 * 1_000_000_000
                - 999_999_999);
            assert(s2 * 1_000_000_000 - 1_000_000_000
                < s2 * 1_000_000_000 - 999_999_999);
        } else {
            // n1 > 0 with d1's sign agreement forces s1 >= 0, hence
            // s2 >= 1, and d2's sign agreement then forces n2 >= 0:
            // total1 <= s1 * 1e9 + 999_999_999 < (s1 + 1) * 1e9
            // <= s2 * 1e9 <= total2.
            assert(s1 >= 0);
            assert(s2 >= 1);
            assert(n2 >= 0);
            assert(s1 * 1_000_000_000 + n1
                <= s1 * 1_000_000_000 + 999_999_999);
            assert(s1 * 1_000_000_000 + 999_999_999
                < s1 * 1_000_000_000 + 1_000_000_000);
            assert(s1 * 1_000_000_000 + 1_000_000_000
                <= s2 * 1_000_000_000);
        }
    }
    // The secs-equal clause is linear.
}

/// Lex-to-total, the Greater clauses: the mirror of
/// spc_lex_total_less, obtained by swapping the two durations.
pub proof fn spc_lex_total_greater(
    d1: &SignedDuration,
    d2: &SignedDuration,
)
    requires
        sd_inv(d1),
        sd_inv(d2),
    ensures
        (((d1.secs as int) > (d2.secs as int))
            ==> (sd_total_nanos(d1) > sd_total_nanos(d2))),
        ((d1.secs == d2.secs)
            && ((d1.nanos as int) > (d2.nanos as int))
            ==> (sd_total_nanos(d1) > sd_total_nanos(d2))),
{
    spc_lex_total_less(d2, d1);
}

/// Origin Rust: the derived-Ord lexicographic compare upstream spells
///     `dur1.cmp(&dur2)` (span.rs:4528; derived Ord on
///     SignedDuration { secs, nanos } -- signed_duration.rs struct
///     order, secs compared first, subsec nanos as the tiebreak).
/// The exec ladder below is the spelled-out trichotomy of that
/// derived compare; the ensures carries it in canonical-form terms
/// (the total-nanoseconds trichotomy, per the lemma pair above).
pub(crate) exec fn sd_lex_cmp_exec(
    d1: &SignedDuration,
    d2: &SignedDuration,
) -> (r: SpOrdering)
    requires
        sd_inv(d1),
        sd_inv(d2),
    ensures
        spc_ordering_of_totals(
            sd_total_nanos(d1),
            sd_total_nanos(d2),
            r,
        ),
{
    if d1.secs < d2.secs {
        proof {
            spc_lex_total_less(d1, d2);
        }
        SpOrdering::Less
    } else if d1.secs > d2.secs {
        proof {
            spc_lex_total_greater(d1, d2);
        }
        SpOrdering::Greater
    } else if d1.nanos < d2.nanos {
        proof {
            spc_lex_total_less(d1, d2);
        }
        SpOrdering::Less
    } else if d1.nanos > d2.nanos {
        proof {
            spc_lex_total_greater(d1, d2);
        }
        SpOrdering::Greater
    } else {
        proof {
            spc_lex_total_less(d1, d2);
            spc_lex_total_greater(d1, d2);
            assert(sd_total_nanos(d1) == sd_total_nanos(d2));
        }
        SpOrdering::Equal
    }
}

// ===========================================================================
// (2) SpanFieldwise (span.rs:3460-3595) and Span::fieldwise
// (span.rs:1426-1457).
// ===========================================================================

/// Origin Rust: pub struct SpanFieldwise(pub Span)
///     (span.rs:3512-3515, `#[derive(Clone, Copy, Debug, Default)]`,
///     `#[repr(transparent)]`).
/// Upstream doc (span.rs:3460-3511, quoted sentence by sentence):
///   A wrapper for `Span` that implements the `Hash`, `Eq` and
///   `PartialEq` traits.
///   A `SpanFieldwise` is meant to make it easy to compare two spans
///   in a "dumb" way based purely on its unit values, while still
///   providing a speed bump to avoid accidentally doing this
///   comparison on `Span` directly. This is distinct from something
///   like `Span::compare` that performs a comparison on the actual
///   elapsed time of two spans.
///   It is generally discouraged to use `SpanFieldwise` since spans
///   that represent an equivalent elapsed amount of time may compare
///   unequal. However, in some cases, it is useful to be able to assert
///   precise field values. For example, Jiff itself makes heavy use of
///   fieldwise comparisons for tests.
///   # Construction: While callers may use `SpanFieldwise(span)`
///   (where `span` has type `Span`) to construct a value of this type,
///   callers may find `Span::fieldwise` more convenient. Namely,
///   `Span::fieldwise` may avoid the need to explicitly import
///   `SpanFieldwise`.
///   # Trait implementations: In addition to implementing the `Hash`,
///   `Eq` and `PartialEq` traits, this type also provides `PartialEq`
///   impls for comparing a `Span` with a `SpanFieldwise`. This
///   simplifies comparisons somewhat while still requiring that at
///   least one of the values has an explicit fieldwise comparison
///   type.
///   # Safety: This type is guaranteed to have the same layout in
///   memory as `Span`.
/// Prune 5: the tuple struct endows a named field `span` (the layout
/// sentence is representation-level and rides the struct shape).
pub struct SpanFieldwise {
    pub span: Span,
}

/// Origin Rust: impl core::ops::Neg for SpanFieldwise
///     fn neg(self) -> SpanFieldwise { SpanFieldwise(self.0.negate()) }
///     (span.rs:3517-3525).
/// Upstream comment (span.rs:3517, verbatim):
///   Exists so that things like `-1.day().fieldwise()` works as
///   expected.
/// The materialization is the J4b free-fn convention (ops as free
/// fns); the receiver tiers are Span::negate's own (jcore_span.rs,
/// sp_field_inv + sp_zero_sign_ok).
pub exec fn spf_neg(a: &SpanFieldwise) -> (r: SpanFieldwise)
    requires
        sp_field_inv(&a.span),
        sp_zero_sign_ok(&a.span),
    ensures
        sp_field_inv(&r.span),
        sp_zero_sign_ok(&r.span),
        r.span.units.year == a.span.units.year
            && r.span.units.month == a.span.units.month
            && r.span.units.week == a.span.units.week
            && r.span.units.day == a.span.units.day
            && r.span.units.hour == a.span.units.hour
            && r.span.units.minute == a.span.units.minute
            && r.span.units.second == a.span.units.second
            && r.span.units.millisecond == a.span.units.millisecond
            && r.span.units.microsecond == a.span.units.microsecond
            && r.span.units.nanosecond == a.span.units.nanosecond
            && r.span.years == a.span.years
            && r.span.months == a.span.months
            && r.span.weeks == a.span.weeks
            && r.span.days == a.span.days
            && r.span.hours == a.span.hours
            && r.span.minutes == a.span.minutes
            && r.span.seconds == a.span.seconds
            && r.span.milliseconds == a.span.milliseconds
            && r.span.microseconds == a.span.microseconds
            && r.span.nanoseconds == a.span.nanoseconds
            && ((a.span.sign is Zero) ==> (r.span.sign is Zero))
            && ((a.span.sign is Positive) ==> (r.span.sign is Negative))
            && ((a.span.sign is Negative) ==> (r.span.sign is Positive)),
{
    SpanFieldwise { span: a.span.negate() }
}

/// Origin Rust: impl PartialEq for SpanFieldwise
///     fn eq(&self, rhs: &SpanFieldwise) -> bool (span.rs:3529-3543),
///     body verbatim:
///         self.0.sign == rhs.0.sign
///             && self.0.years == rhs.0.years
///             && self.0.months == rhs.0.months
///             && self.0.weeks == rhs.0.weeks
///             && self.0.days == rhs.0.days
///             && self.0.hours == rhs.0.hours
///             && self.0.minutes == rhs.0.minutes
///             && self.0.seconds == rhs.0.seconds
///             && self.0.milliseconds == rhs.0.milliseconds
///             && self.0.microseconds == rhs.0.microseconds
///             && self.0.nanoseconds == rhs.0.nanoseconds
/// NOTE the face deliberately does NOT compare the UnitSet flags:
/// two spans with equal sign and ten equal magnitudes but different
/// unit-flag bookkeeping compare EQUAL through this impl upstream, a
/// coarser equality than Span's own derived PartialEq (which compares
/// the whole struct). Intended, not a mismatch: the flags are
/// implementation bookkeeping the "dumb" comparison is entitled to
/// ignore; on the setter-produced tier the two equalities coincide
/// (sp_flags_ok ties every flag to its field being non-zero).
pub open spec fn spf_eq_face(a: &SpanFieldwise, b: &SpanFieldwise) -> bool {
    sp_sign_eq(a.span.sign, b.span.sign)
        && a.span.years == b.span.years
        && a.span.months == b.span.months
        && a.span.weeks == b.span.weeks
        && a.span.days == b.span.days
        && a.span.hours == b.span.hours
        && a.span.minutes == b.span.minutes
        && a.span.seconds == b.span.seconds
        && a.span.milliseconds == b.span.milliseconds
        && a.span.microseconds == b.span.microseconds
        && a.span.nanoseconds == b.span.nanoseconds
}

/// The cross-type face of impl PartialEq<Span> for SpanFieldwise
/// (span.rs:3551-3555, body `self == rhs.fieldwise()`) and of impl
/// PartialEq<SpanFieldwise> for Span (span.rs:3557-3561, body
/// `self.fieldwise() == *rhs`): the same eleven conjuncts against the
/// bare span. One face serves both impls (their bodies are
/// delegations to the same comparison).
pub open spec fn spf_eq_span_face(a: &SpanFieldwise, s: &Span) -> bool {
    sp_sign_eq(a.span.sign, s.sign)
        && a.span.years == s.years
        && a.span.months == s.months
        && a.span.weeks == s.weeks
        && a.span.days == s.days
        && a.span.hours == s.hours
        && a.span.minutes == s.minutes
        && a.span.seconds == s.seconds
        && a.span.milliseconds == s.milliseconds
        && a.span.microseconds == s.microseconds
        && a.span.nanoseconds == s.nanoseconds
}

/// Sign equality without a Copy/Clone on Sign (the mounted J1 Sign
/// has neither -- the J5 pitfall-28 helper family): a three-arm match
/// on the two references.
exec fn spf_sign_eq_exec(a: &Sign, b: &Sign) -> (r: bool)
    ensures
        (r <==> sp_sign_eq(*a, *b)),
{
    match a {
        Sign::Zero => match b {
            Sign::Zero => true,
            _ => false,
        },
        Sign::Positive => match b {
            Sign::Positive => true,
            _ => false,
        },
        Sign::Negative => match b {
            Sign::Negative => true,
            _ => false,
        },
    }
}

/// The by-value exec twin of PartialEq for SpanFieldwise
/// (span.rs:3529-3543): free fn per the J4b convention.
pub exec fn spf_eq(a: &SpanFieldwise, b: &SpanFieldwise) -> (r: bool)
    ensures
        (r <==> spf_eq_face(a, b)),
{
    spf_sign_eq_exec(&a.span.sign, &b.span.sign)
        && a.span.years == b.span.years
        && a.span.months == b.span.months
        && a.span.weeks == b.span.weeks
        && a.span.days == b.span.days
        && a.span.hours == b.span.hours
        && a.span.minutes == b.span.minutes
        && a.span.seconds == b.span.seconds
        && a.span.milliseconds == b.span.milliseconds
        && a.span.microseconds == b.span.microseconds
        && a.span.nanoseconds == b.span.nanoseconds
}

/// The exec twin of impl PartialEq<Span> for SpanFieldwise
/// (span.rs:3551-3555).
pub exec fn spf_eq_span(a: &SpanFieldwise, s: &Span) -> (r: bool)
    ensures
        (r <==> spf_eq_span_face(a, s)),
{
    spf_sign_eq_exec(&a.span.sign, &s.sign)
        && a.span.years == s.years
        && a.span.months == s.months
        && a.span.weeks == s.weeks
        && a.span.days == s.days
        && a.span.hours == s.hours
        && a.span.minutes == s.minutes
        && a.span.seconds == s.seconds
        && a.span.milliseconds == s.milliseconds
        && a.span.microseconds == s.microseconds
        && a.span.nanoseconds == s.nanoseconds
}

/// The exec twin of impl PartialEq<SpanFieldwise> for Span
/// (span.rs:3557-3561).
pub exec fn spf_span_eq_fieldwise(s: &Span, a: &SpanFieldwise) -> (r: bool)
    ensures
        (r <==> spf_eq_span_face(a, s)),
{
    spf_sign_eq_exec(&s.sign, &a.span.sign)
        && s.years == a.span.years
        && s.months == a.span.months
        && s.weeks == a.span.weeks
        && s.days == a.span.days
        && s.hours == a.span.hours
        && s.minutes == a.span.minutes
        && s.seconds == a.span.seconds
        && s.milliseconds == a.span.milliseconds
        && s.microseconds == a.span.microseconds
        && s.nanoseconds == a.span.nanoseconds
}

/// Origin Rust: impl Eq for SpanFieldwise {} (span.rs:3527) and
/// impl core::hash::Hash for SpanFieldwise (span.rs:3569-3583).
/// The Hash body feeds `state` with exactly the same eleven values in
/// the same order the PartialEq body compares them (sign, years,
/// months, weeks, days, hours, minutes, seconds, milliseconds,
/// microseconds, nanoseconds -- span.rs:3571-3581). Prune 6: the
/// Hasher plumbing is std stringlight; the contract content -- equal
/// inputs hash the same feed sequence -- is definitional once the
/// sequence is spelled, and the face fn above IS that spelling (the
/// proof fn materializes the implication for the record).
pub proof fn spf_eq_implies_hash_seq(
    a: &SpanFieldwise,
    b: &SpanFieldwise,
)
    requires
        spf_eq_face(a, b),
{
    // The eleven conjuncts of spf_eq_face are, in order, the eleven
    // hashed values (spf_eq -> same Seq feed); verus-side nothing
    // further is to prove about a black-box Hasher.
    assert(sp_sign_eq(a.span.sign, b.span.sign));
    assert(a.span.years == b.span.years);
    assert(a.span.nanoseconds == b.span.nanoseconds);
}

impl Span {

/// Origin Rust: pub fn fieldwise(self) -> SpanFieldwise
///     { SpanFieldwise(self) } (span.rs:1454-1457).
/// Upstream doc (span.rs:1426-1453, quoted sentence by sentence):
///   Returns this `Span` as a value with a type that implements the
///   `Hash`, `Eq` and `PartialEq` traits in a fieldwise fashion.
///   A `SpanFieldwise` is meant to make it easy to compare two spans
///   in a "dumb" way based purely on its unit values. This is
///   distinct from something like `Span::compare` that performs a
///   comparison on the actual elapsed time of two spans.
///   It is generally discouraged to use `SpanFieldwise` since spans
///   that represent an equivalent elapsed amount of time may compare
///   unequal. However, in some cases, it is useful to be able to
///   assert precise field values. For example, Jiff itself makes
///   heavy use of fieldwise comparisons for tests.
///   (Example header, span.rs:1440-1443:)
///   In short, `SpanFieldwise` considers `2 hours` and `120 minutes`
///   to be distinct values, but `Span::compare` considers them to be
///   equivalent:
pub exec fn fieldwise(&self) -> (r: SpanFieldwise)
    ensures
        r.span == *self,
{
    // Translation note: upstream moves the receiver
    // (SpanFieldwise(self), span.rs:1456); the mounted Span has no
    // Copy, so the value materializes field by field -- Sign through
    // the J5 sp_sign_of_ref copy helper, the Copy UnitSet and the ten
    // magnitudes by value -- with the identity restored by the
    // helper's variant-identity ensures.
    SpanFieldwise {
        span: Span {
            sign: sp_sign_of_ref(&self.sign),
            units: self.units,
            years: self.years,
            months: self.months,
            weeks: self.weeks,
            days: self.days,
            hours: self.hours,
            minutes: self.minutes,
            seconds: self.seconds,
            milliseconds: self.milliseconds,
            microseconds: self.microseconds,
            nanoseconds: self.nanoseconds,
        },
    }
}

} // impl Span (fieldwise)

// ===========================================================================
// (3) SpanCompare (span.rs:4360-4605) and Span::compare
// (span.rs:1884-1982).
// ===========================================================================

/// Origin Rust: pub struct SpanCompare<'a> { span: Span,
///     relative: Option<SpanRelativeTo<'a>> } (span.rs:4391-4395,
///     derive(Clone, Copy, Debug)).
/// Upstream doc (span.rs:4360-4378, quoted sentence by sentence):
///   Options for [`Span::compare`].
///   This type provides a way to ergonomically compare two spans with
///   an optional relative datetime. Namely, a relative datetime is
///   only needed when at least one of the two spans being compared has
///   a non-zero calendar unit (years, months, weeks or days).
///   Otherwise, an error will be returned.
///   Callers may use [`SpanCompare::days_are_24_hours`] to opt into
///   24-hour invariant days (and 7-day weeks) without providing a
///   relative datetime.
///   The main way to construct values of this type is with its `From`
///   trait implementations:
///   * `From<Span> for SpanCompare` compares the given span to the
///   receiver in [`Span::compare`].
///   * `From<(Span, civil::Date)> for SpanCompare` compares the given
///   span to the receiver in [`Span::compare`], relative to the given
///   date. There are also `From` implementations for `civil::
///   DateTime`, `Zoned` and [`SpanRelativeTo`].
/// Prune 2: the `relative` field is clipped with the relative
/// pipeline (the concurrent J9 batch's file); the dated/zoned From
/// impls (span.rs:4549-4605) ride it.
pub struct SpanCompare {
    pub span: Span,
}

/// The compare face in canonical-form terms: on Some, the larger of
/// the two spans' largest units sits at Hour or below (the
/// relative-date requirement passed, span.rs:4525) and the ordering
/// is exactly the total-nanoseconds trichotomy of the two invariant
/// durations (the J5 sd64_lex_equiv meeting-face semantics this batch
/// was told to consume; the Lex<->total bridge is (1) above); on
/// None, the larger unit being variable (Day or above) is the one and
/// only lane.
pub open spec fn spc_compare_none_face(
    s1: &Span,
    s2: &Span,
    r: &Option<SpOrdering>,
) -> bool {
    let max_unit: Unit =
        sp_unit_max(sp_span_largest(s1), sp_span_largest(s2));
    match r {
        Option::Some(o) =>
            (!(sr_requires_relative_err(max_unit)))
                && spc_ordering_of_totals(
                    sp_inv_total_nanos(s1),
                    sp_inv_total_nanos(s2),
                    *o,
                ),
        Option::None => sr_requires_relative_err(max_unit),
    }
}

impl SpanCompare {

/// Origin Rust: fn new(span: Span) -> SpanCompare<'static>
///     { SpanCompare { span, relative: None } } (span.rs:4506-4510,
///     crate-internal).
pub(crate) exec fn new(span: Span) -> (r: SpanCompare)
    ensures
        r.span == span,
{
    SpanCompare { span }
}

/// Origin Rust: impl From<Span> for SpanCompare<'static>
///     { fn from(span: Span) -> SpanCompare { SpanCompare::new(span)
///     } } (span.rs:4537-4541).
/// (The `impl From<&Span> for SpanCompare` twin at span.rs:4543-4547
/// derefs to the same construction; its content is the receiver
/// clone-free variant, noted.)
pub exec fn from_span(span: Span) -> (r: SpanCompare)
    ensures
        r.span == span,
{
    SpanCompare { span }
}


/// Origin Rust: fn compare(self, span: Span) -> Result<Ordering,
///     Error> (span.rs:4506-4534), translated at the relative==None
///     arm (span.rs:4524-4529, the two return Ok(dur1.cmp(&dur2))
///     lanes that share the no-relative body below; the
///     Some(relative) arm at :4531-4533 rides prune 2).
/// Upstream body, verbatim, with the translated lane marked:
///     let (span1, span2) = (span, self.span);
///     let unit = span1.largest_unit().max(span2.largest_unit());
///     let start = match self.relative {
///         Some(r) => match r.to_relative(unit)? { ... },   // pruned
///         None => {
///             requires_relative_date_err(unit)?;
///             let dur1 = span1.to_invariant_duration();
///             let dur2 = span2.to_invariant_duration();
///             return Ok(dur1.cmp(&dur2));                  // here
///         }
///     };
pub(crate) exec fn compare(&self, s1: &Span) -> (r: Option<SpOrdering>)
    requires
        sp_field_inv(s1),
        sp_flags_ok(s1),
        sp_field_inv(&self.span),
        sp_flags_ok(&self.span),
    ensures
        spc_compare_none_face(s1, &self.span, &r),
{
    // span.rs:4513-4514
    let u1: Unit = s1.largest_unit();
    let u2: Unit = self.span.largest_unit();
    let unit: Unit = sp_unit_max_exec(u1, u2);
    proof {
        assert(u1 == sp_span_largest(s1));
        assert(u2 == sp_span_largest(&self.span));
        assert(unit
            == sp_unit_max(sp_span_largest(s1),
                sp_span_largest(&self.span)));
    }
    // span.rs:4525: requires_relative_date_err(unit)? -- the error
    // arm is exactly the variable-unit test (sr_requires_relative_err
    // is the J10 spec face of upstream span.rs:6730-6739).
    if sp_unit_rank_exec(unit) >= sp_unit_rank_exec(Unit::Day) {
        proof {
            assert(sr_requires_relative_err(unit));
        }
        return Option::None;
    }
    proof {
        assert(!(sr_requires_relative_err(unit)));
    }
    // span.rs:4526-4527: the two invariant durations.
    let dur1: SignedDuration = s1.sp_to_invariant_duration();
    let dur2: SignedDuration = self.span.sp_to_invariant_duration();
    proof {
        assert(sd_total_nanos(&dur1) == sp_inv_total_nanos(s1));
        assert(sd_total_nanos(&dur2)
            == sp_inv_total_nanos(&self.span));
    }
    // span.rs:4528: Ok(dur1.cmp(&dur2)) -- the derived-Ord lex
    // compare, carried in canonical terms by sd_lex_cmp_exec.
    Option::Some(sd_lex_cmp_exec(&dur1, &dur2))
}

} // impl SpanCompare

impl Span {

/// Origin Rust: pub fn compare<'a, C: Into<SpanCompare<'a>>>(
///     &self, options: C) -> Result<Ordering, Error>
///     { let options: SpanCompare<'_> = options.into();
///       options.compare(*self) } (span.rs:1975-1982).
/// Upstream doc (span.rs:1884-1974, the prose and contract sentences
/// quoted in full; the example blocks are panel/noted per section):
///   Two spans compare equal when they correspond to the same duration
///   of time, even if their individual fields are different. This is
///   in contrast to the `Eq` trait implementation of `SpanFieldwise`
///   (created by [`Span::fieldwise`]), which performs exact
///   field-wise comparisons. This split exists because the comparison
///   provided by this routine is "heavy" in that it may need to do
///   datetime arithmetic to return an answer. In contrast, the `Eq`
///   trait implementation is "cheap."
///   This routine accepts anything that implements `Into<SpanCompare>`.
///   There are some trait implementations that make using this routine
///   ergonomic:
///   * `From<Span> for SpanCompare` compares the given span to this
///   one.
///   * `From<(Span, civil::Date)> for SpanArithmetic` compares the
///   given span to this one relative to the given date. There are
///   also `From` implementations for `civil::DateTime` and `Zoned`.
///   (NOTE the second bullet says `SpanArithmetic` while pointing at
///   the SpanCompare From impls -- an upstream doc-name slip, recorded
///   in the batch notes, class-3 record-only.)
///   # Errors
///   If either of the spans being compared have a non-zero calendar
///   unit (units bigger than hours), then this routine requires a
///   relative datetime. If one is not provided, then an error is
///   returned.
///   An error can also occur when adding either span to the relative
///   datetime given results in overflow.  [rides prune 2]
///   Callers may use [`SpanArithmetic::days_are_24_hours`] as a
///   special marker instead of providing a relative civil date to
///   indicate that all days should be 24 hours long. This also
///   results in treating all weeks as seven 24 hour days (168 hours).
///   See the examples for [`Span::total`] if you want to sort spans
///   without an `unwrap()` call.
pub exec fn compare_no_relative(
    &self,
    cfg: &SpanCompare,
) -> (r: Option<SpOrdering>)
    requires
        sp_field_inv(self),
        sp_flags_ok(self),
        sp_field_inv(&cfg.span),
        sp_flags_ok(&cfg.span),
    ensures
        spc_compare_none_face(self, &cfg.span, &r),
{
    cfg.compare(self)
}

} // impl Span (compare)

// ===========================================================================
// (4) SpanTotal (span.rs:4607-4952) and Span::total
// (span.rs:1984-2126).
// ===========================================================================

/// Origin Rust: pub struct SpanTotal<'a> { unit: Unit,
///     relative: Option<SpanRelativeTo<'a>> } (span.rs:4687-4691,
///     derive(Clone, Copy, Debug)).
/// Upstream doc (span.rs:4607-4626, quoted sentence by sentence):
///   Options for [`Span::total`].
///   This type provides a way to ergonomically determine the number of
///   a particular unit in a span, with a potentially fractional
///   component, with an optional relative datetime. Namely, a relative
///   datetime is only needed when the span has a non-zero calendar
///   unit (years, months, weeks or days). Otherwise, an error will be
///   returned.
///   Callers may use [`SpanTotal::days_are_24_hours`] to opt into
///   24-hour invariant days (and 7-day weeks) without providing a
///   relative datetime.
///   The main way to construct values of this type is with its `From`
///   trait implementations:
///   * `From<Unit> for SpanTotal` computes a total for the given unit
///   in the receiver span for [`Span::total`].
///   * `From<(Unit, civil::Date)> for SpanTotal` computes a total for
///   the given unit in the receiver span for [`Span::total`], relative
///   to the given date. There are also `From` implementations for
///   `civil::DateTime`, `Zoned` and [`SpanRelativeTo`].
/// Prune 2: the `relative` field is clipped with the relative
/// pipeline; the dated/zoned From impls (span.rs:4884-4950) ride it.
#[derive(Clone, Copy)]
pub struct SpanTotal {
    pub unit: Unit,
}

/// Origin Rust: the `f64` value shape of Span::total -- pruned to its
/// exact rational underneath (prune 3). Numer is
/// `span.to_invariant_duration().as_nanos()` (i128 in upstream,
/// span.rs:4867), denom is `self.unit.duration().as_nanos()`
/// (span.rs:4873); the ratio pair IS the value the upstream f64
/// division approximates, with upstream's own precision comment
/// quoted at the exec site below.
pub struct SpTotalRatio {
    pub numer: i128,
    pub denom: i128,
}

/// The exact-rational result face of total_invariant
/// (span.rs:4864-4874): numer is the span's invariant total in
/// nanoseconds (sp_inv_total_nanos, the J8 spine's own spec face),
/// denom is the unit's invariant nanosecond budget (rm_unit_nanos,
/// the J10 spec face of Unit::duration, span.rs:3928-3944).
pub open spec fn spt_total_inv_face(
    unit: Unit,
    s: &Span,
    r: &SpTotalRatio,
) -> bool {
    ((r.numer as int) == sp_inv_total_nanos(s))
        && ((r.denom as int) == rm_unit_nanos(unit))
        && ((r.denom as int) >= 1)
}

/// Span doc sentence materialized (span.rs:1986-1987, "If the span is
/// not evenly divisible by the requested units, then the number
/// returned may have a fractional component"): even divisibility on
/// the exact rational.
pub open spec fn spt_evenly_divisible(unit: Unit, s: &Span) -> bool {
    sp_inv_total_nanos(s) % rm_unit_nanos(unit) == 0
}

/// Exec twin of the denominator `self.unit.duration().as_nanos()`
/// (span.rs:4873 via Unit::duration at :3928-3944). Local twin
/// because the J10 file's own exec twin is private to it; the
/// Year/Month unreachable arms of upstream stay requires (the J10
/// prune-7 doctrine).
pub(crate) exec fn spt_unit_nanos_exec(u: Unit) -> (r: i128)
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

/// The relative==None config face of the total body: the larger of
/// the requested unit and the span's own largest unit is invariant
/// (Hour or below), which is exactly the
/// requires_relative_date_err(max_unit) pass at span.rs:4823.
pub open spec fn spt_config_ok(cfg: &SpanTotal, s: &Span) -> bool {
    !(sr_requires_relative_err(
        sp_unit_max(cfg.unit, sp_span_largest(s)),
    ))
}

impl SpanTotal {

/// Origin Rust: fn new(unit: Unit) -> SpanTotal<'static>
///     { SpanTotal { unit, relative: None } }
///     (span.rs:4807-4811, crate-internal).
pub(crate) exec fn new(unit: Unit) -> (r: SpanTotal)
    ensures
        r.unit == unit,
{
    SpanTotal { unit }
}

/// Origin Rust: impl From<Unit> for SpanTotal<'static>
///     { fn from(unit: Unit) -> SpanTotal { SpanTotal::new(unit) } }
///     (span.rs:4877-4882).
pub exec fn from_unit(unit: Unit) -> (r: SpanTotal)
    ensures
        r.unit == unit,
{
    SpanTotal::new(unit)
}

/// Origin Rust: fn total_invariant(&self, span: Span) -> f64
///     (span.rs:4864-4874), body verbatim:
///         assert!(self.unit <= Unit::Week);
///         let dur = span.to_invariant_duration().as_nanos();
///         // We do this instead of using
///         // `SignedDuration::as_secs_f64()` because of floating
///         // point precision. It seems that if we represent our
///         // ratio as floats of seconds instead of nanoseconds,
///         // then there is more loss of precision than using
///         // nanoseconds. Unfortunately, this does mean manifesting
///         // `i128` values.
///         (dur as f64) / (self.unit.duration().as_nanos() as f64)
/// The assert! at :4866 is the only fallibility: its rank condition
/// is this fn's requires (panic-site fidelity -- a plain release
/// assert on a crate-internal path, no documented panic face).
/// Prune 3: the trailing f64 division is the exact rational's
/// carrier -- the (numer, denom) pair returned; the quoted comment
/// is upstream's own justification that the pair, not any sec-grade
/// float, is the value of record.
pub(crate) exec fn total_invariant(
    &self,
    span: &Span,
) -> (r: SpTotalRatio)
    requires
        sp_field_inv(span),
        sp_unit_rank(self.unit) <= sp_unit_rank(Unit::Week),
    ensures
        spt_total_inv_face(self.unit, span, &r),
{
    // span.rs:4867
    let dur: SignedDuration = span.sp_to_invariant_duration();
    proof {
        assert(sd_total_nanos(&dur) == sp_inv_total_nanos(span));
    }
    let numer: i128 = dur.as_nanos();
    // span.rs:4873: self.unit.duration().as_nanos()
    let denom: i128 = spt_unit_nanos_exec(self.unit);
    SpTotalRatio { numer, denom }
}

/// Origin Rust: fn total(self, span: Span) -> Result<f64, Error>
///     (span.rs:4813-4862), translated at the relative==None arm
///     (span.rs:4822-4825; the Some(relative) arm at :4816-4821 and
///     the variable-unit measurement at :4827-4862 ride prune 2).
/// Upstream body, verbatim, with the translated lane marked:
///     let max_unit = self.unit.max(span.largest_unit());
///     let relative = match self.relative {
///         Some(r) => match r.to_relative(max_unit)? { ... },  // pruned
///         None => {
///             requires_relative_date_err(max_unit)?;
///             return Ok(self.total_invariant(span));
///         }                                                   // here
///     };
/// Upstream comment inside the pruned arm (span.rs:4833-4839,
/// quoted for the record because the zero-span doctrine it states is
/// the arm's own):
///   A zero span has no direction in which to measure the length of
///   `self.unit` below, so `unit_start_and_end` would be asked to add
///   zero units and fail its assertion. The total is always zero
///   anyway.
pub(crate) exec fn total_no_relative(
    &self,
    span: &Span,
) -> (r: Option<SpTotalRatio>)
    requires
        sp_field_inv(span),
        sp_flags_ok(span),
    ensures
        match r {
            Option::Some(ratio) =>
                spt_config_ok(self, span)
                    && spt_total_inv_face(self.unit, span, &ratio),
            Option::None => !(spt_config_ok(self, span)),
        },
{
    // span.rs:4814
    let existing: Unit = span.largest_unit();
    proof {
        assert(existing == sp_span_largest(span));
    }
    let max_unit: Unit = sp_unit_max_exec(self.unit, existing);
    // span.rs:4822-4823: the relative==None arm calls
    // requires_relative_date_err(max_unit)? -- exactly the
    // variable-unit test.
    if sp_unit_rank_exec(max_unit)
        >= sp_unit_rank_exec(Unit::Day)
    {
        proof {
            assert(sr_requires_relative_err(max_unit));
        }
        return Option::None;
    }
    proof {
        assert(!(sr_requires_relative_err(max_unit)));
        assert(!(self.unit is Year));
        assert(!(self.unit is Month));
        assert(sp_unit_rank(max_unit) <= sp_unit_rank(Unit::Hour));
        assert(sp_unit_rank(max_unit) <= sp_unit_rank(Unit::Week));
        assert(!(self.unit is Day));
    }
    // span.rs:4824: return Ok(self.total_invariant(span));
    Option::Some(self.total_invariant(span))
}

} // impl SpanTotal

impl Span {

/// Origin Rust: pub fn total<'a, T: Into<SpanTotal<'a>>>(
///     &self, options: T) -> Result<f64, Error>
///     { let options: SpanTotal<'_> = options.into();
///       options.total(*self) } (span.rs:2119-2126).
/// Upstream doc (span.rs:1984-2118, the prose and contract sentences
/// quoted in full; the example blocks are panel/noted per section):
///   Returns a floating point number representing the total number of
///   a specific unit (as given) in this span. If the span is not
///   evenly divisible by the requested units, then the number
///   returned may have a fractional component.
///   [Prune 3: the machine-checked face carries that exact rational;
///   the "floating point number" shape is the clipped IEEE wrapper,
///   and the "may have a fractional component" sentence is stated
///   exactly as spt_evenly_divisible's negation witness panel below
///   exercises.]
///   This routine accepts anything that implements `Into<SpanTotal>`.
///   There are some trait implementations that make using this
///   routine ergonomic:
///   * `From<Unit> for SpanTotal` computes a total for the given unit
///   in this span.
///   * `From<(Unit, civil::Date)> for SpanTotal` computes a total for
///   the given unit in this span, relative to the given date. There
///   are also `From` implementations for `civil::DateTime` and
///   `Zoned`.
///   # Errors
///   If this span has any non-zero calendar unit (units bigger than
///   hours), then this routine requires a relative datetime. If one is
///   not provided, then an error is returned.
///   An error can also occur when adding the span to the relative
///   datetime given results in overflow.  [rides prune 2]
///   Callers may use [`SpanArithmetic::days_are_24_hours`] as a
///   special marker instead of providing a relative civil date to
///   indicate that all days should be 24 hours long. This also results
///   in treating all weeks as seven 24 hour days (168 hours).
pub exec fn total_no_relative(
    &self,
    cfg: &SpanTotal,
) -> (r: Option<SpTotalRatio>)
    requires
        sp_field_inv(self),
        sp_flags_ok(self),
    ensures
        match r {
            Option::Some(ratio) =>
                spt_config_ok(cfg, self)
                    && spt_total_inv_face(cfg.unit, self, &ratio),
            Option::None => !(spt_config_ok(cfg, self)),
        },
{
    cfg.total_no_relative(self)
}

} // impl Span

// ===========================================================================
// (5) Witness panels (doc examples and unit-test rows as exec
// asserts). Panel discipline: every assert is ghost; enum tests use
// `is` inside the ghost position only.
// ===========================================================================

/// Doc rows of Span::compare (span.rs:1919-1924):
///   let span1 = 3.hours();
///   let span2 = 180.minutes();
///   assert_eq!(span1.compare(span2)?, std::cmp::Ordering::Equal);
/// Row: equal elapsed time through different fields -> Equal.
exec fn spc_panel_doc_compare_eq()
{
    let s1: Span = Span::new().hours(3);
    let s2: Span = Span::new().minutes(180);
    proof {
        assert(sp_inv_total_nanos(&s1) == 10_800_000_000_000int);
        assert(sp_inv_total_nanos(&s2) == 10_800_000_000_000int);
        // both largest units sit at/below Hour, the guard passes
        assert(!(sr_requires_relative_err(
            sp_unit_max(sp_span_largest(&s1), sp_span_largest(&s2)))));
    }
    let cfg: SpanCompare = SpanCompare::from_span(s2);
    let o: Option<SpOrdering> = s1.compare_no_relative(&cfg);
    assert(o is Some);
    assert(match o {
        Option::Some(x) => x is Equal,
        Option::None => false,
    });
}

/// The fieldwise-vs-compare doc rows (span.rs:3495-3508):
///   assert_ne!(120.minutes().fieldwise(), 2.hours().fieldwise());
///   assert_eq!(120.minutes().compare(2.hours())?, Ordering::Equal);
///   // These comparisons are allowed between a `Span` and a
///   // `SpanFieldwise`. Namely, as long as one value is "fieldwise,"
///   // then the comparison is OK.
///   assert_ne!(120.minutes().fieldwise(), 2.hours());
///   assert_ne!(120.minutes(), 2.hours().fieldwise());
/// Rows: the fieldwise faces are unequal, both mixed
/// Span/SpanFieldwise comparisons are unequal, and the elapsed-time
/// compare is Equal -- the doc's whole point in one panel.
exec fn spf_panel_doc_fieldwise_vs_compare()
{
    let s1: Span = Span::new().minutes(120);
    let s2: Span = Span::new().hours(2);
    let f1: SpanFieldwise = s1.fieldwise();
    let f2: SpanFieldwise = s2.fieldwise();
    proof {
        assert(sp_inv_total_nanos(&s1) == 7_200_000_000_000int);
        assert(sp_inv_total_nanos(&s2) == 7_200_000_000_000int);
        // the faces cannot hold: minutes(120) vs hours(2) differ in
        // the minutes/hours fields.
        assert(!(f1.span.hours == f2.span.hours));
    }
    let e1: bool = spf_eq(&f1, &f2);
    assert(!(e1)); // assert_ne!(120.minutes().fieldwise(),
    //               //   2.hours().fieldwise());
    let e2: bool = spf_eq_span(&f1, &s2);
    assert(!(e2)); // assert_ne!(120.minutes().fieldwise(), 2.hours());
    let e3: bool = spf_span_eq_fieldwise(&s1, &f2);
    assert(!(e3)); // assert_ne!(120.minutes(), 2.hours().fieldwise());
    // ... while the elapsed-time compare is Equal:
    assert(sr_requires_relative_err(
        sp_unit_max(sp_span_largest(&s1), sp_span_largest(&s2)))
        == false);
    let cfg: SpanCompare = SpanCompare::from_span(
        Span::new().hours(2));
    let o: Option<SpOrdering> = s1.compare_no_relative(&cfg);
    assert(o is Some);
    assert(match o {
        Option::Some(x) => x is Equal,
        Option::None => false,
    });
}

/// Doc rows of Span::compare, negative spans (span.rs:1929-1939):
///   let span1 = -1.second();
///   let span2 = 0.seconds();
///   assert_eq!(span1.compare(span2)?, std::cmp::Ordering::Less);
exec fn spc_panel_doc_compare_neg_less()
{
    let s1: Span = Span::new().seconds(-1);
    let s2: Span = Span::new().seconds(0);
    proof {
        assert(sp_inv_total_nanos(&s1) == -1_000_000_000int);
        assert(sp_inv_total_nanos(&s2) == 0int);
    }
    let cfg: SpanCompare = SpanCompare::from_span(s2);
    let o: Option<SpOrdering> = s1.compare_no_relative(&cfg);
    assert(o is Some);
    assert(match o {
        Option::Some(x) => x is Less,
        Option::None => false,
    });
}

/// The doc error row of SpanCompare::days_are_24_hours
/// (span.rs:4483-4996, the no-relative half):
///   let span1 = 2.days().hours(12);
///   let span2 = 60.hours();
///   // No relative date provided, which results in an error.
///   assert_eq!(
///       span1.compare(span2).unwrap_err().to_string(),
///       "using unit 'day' in a span or configuration requires that \
///        either a relative reference time be given or \
///        `jiff::SpanRelativeTo::days_are_24_hours()` is used to
///        indicate invariant 24-hour days, but neither were provided",
///   );
/// The fix row that follows (compare(SpanCompare::from(span2)
/// .days_are_24_hours()) == Equal) rides prune 2. The error arm here
/// is machine-checked: the None face is exactly the variable-unit
/// (Day) guard.
exec fn spc_panel_doc_compare_day_err()
{
    let s1: Span = Span::new().days(2).hours(12);
    let s2: Span = Span::new().hours(60);
    proof {
        assert(sp_span_largest(&s1) is Day);
        assert(sr_requires_relative_err(
            sp_unit_max(sp_span_largest(&s1), sp_span_largest(&s2))));
    }
    let cfg: SpanCompare = SpanCompare::from_span(s2);
    let o: Option<SpOrdering> = s1.compare_no_relative(&cfg);
    assert(o is None);
}

/// The upstream sort test row (span.rs:6826-6831):
///   let span1 = 79.hours().minutes(10);
///   let span2 = 79.hours().seconds(630);
///   let span3 = 78.hours().minutes(50);
///   ... array.sort_by(|sp1, sp2| sp1.compare(sp2).unwrap());
///   assert_eq!(array, [span3, span1, span2].map(SpanFieldwise));
/// Pairwise machine checks: span3 < span1 < span2 by total
/// nanoseconds (283,800s / 285,000s / 285,030s), which is precisely
/// the ascending sort the test asserts.
exec fn spc_panel_test_compare_sort()
{
    let s1: Span = Span::new().hours(79).minutes(10);
    let s2: Span = Span::new().hours(79).seconds(630);
    let s3: Span = Span::new().hours(78).minutes(50);
    proof {
        assert(sp_inv_total_nanos(&s1) == 285_000_000_000_000int);
        assert(sp_inv_total_nanos(&s2) == 285_030_000_000_000int);
        assert(sp_inv_total_nanos(&s3) == 283_800_000_000_000int);
    }
    let t1b: Span = Span::new().hours(79).minutes(10);
    let t2b: Span = Span::new().hours(79).seconds(630);
    proof {
        assert(sp_inv_total_nanos(&t1b) == 285_000_000_000_000int);
        assert(sp_inv_total_nanos(&t2b) == 285_030_000_000_000int);
    }
    let c31: SpanCompare = SpanCompare::from_span(t1b);
    let o31: Option<SpOrdering> = s3.compare_no_relative(&c31);
    assert(match o31 {
        Option::Some(x) => x is Less,
        Option::None => false,
    });
    let c12: SpanCompare = SpanCompare::from_span(t2b);
    let o12: Option<SpOrdering> = s1.compare_no_relative(&c12);
    assert(match o12 {
        Option::Some(x) => x is Less,
        Option::None => false,
    });
    // span1 vs span3, the other direction of the first pair:
    let c13: SpanCompare = SpanCompare::from_span(
        Span::new().hours(78).minutes(50));
    proof {
        assert(sp_inv_total_nanos(&c13.span) == 283_800_000_000_000int);
    }
    let o13: Option<SpOrdering> = s1.compare_no_relative(&c13);
    assert(match o13 {
        Option::Some(x) => x is Greater,
        Option::None => false,
    });
}

/// Doc rows of Span::total (span.rs:2012-2024):
///   let span = 3.hours().minutes(10);
///   assert_eq!(span.total(Unit::Second)?, 11_400.0);
/// Row: 3h10m == 11,400 seconds exactly -- an evenly divisible pair,
/// so the exact rational has no fractional component.
exec fn spt_panel_doc_total_second()
{
    let s: Span = Span::new().hours(3).minutes(10);
    proof {
        assert(sp_inv_total_nanos(&s) == 11_400_000_000_000int);
        assert(spt_evenly_divisible(Unit::Second, &s));
    }
    let cfg: SpanTotal = SpanTotal::from_unit(Unit::Second);
    let r: Option<SpTotalRatio> = s.total_no_relative(&cfg);
    assert(r is Some);
    assert(match r {
        Option::Some(ratio) =>
            (ratio.numer == 11_400_000_000_000i128)
                && (ratio.denom == 1_000_000_000i128),
        Option::None => false,
    });
}

/// The fractional-component witness of the doc sentence
/// "If the span is not evenly divisible by the requested units, then
/// the number returned may have a fractional component"
/// (span.rs:1986-1987), exercised on the doc's own span
/// 3.hours().minutes(10) totaled in Hour units: the exact rational is
/// 11_400_000_000_000 / 3_600_000_000_000 = 19/6 -- a genuine
/// fraction (this is the pair the upstream f64 division
/// approximates; the printed upstream value would be 3.1666...).
exec fn spt_panel_doc_total_fractional()
{
    let s: Span = Span::new().hours(3).minutes(10);
    proof {
        assert(sp_inv_total_nanos(&s) == 11_400_000_000_000int);
        assert(sp_inv_total_nanos(&s) % 3_600_000_000_000int
            == 600_000_000_000int);
        assert(!(spt_evenly_divisible(Unit::Hour, &s)));
    }
    let cfg: SpanTotal = SpanTotal::from_unit(Unit::Hour);
    let r: Option<SpTotalRatio> = s.total_no_relative(&cfg);
    assert(r is Some);
    assert(match r {
        Option::Some(ratio) =>
            (ratio.numer == 11_400_000_000_000i128)
                && (ratio.denom == 3_600_000_000_000i128),
        Option::None => false,
    });
}

/// Upstream test row (span.rs:6757-6759):
///   let span = 130.hours().minutes(20);
///   let total = span.total(Unit::Second).unwrap();
///   assert_eq!(total, 469200.0);
exec fn spt_panel_test_total_second()
{
    let s: Span = Span::new().hours(130).minutes(20);
    proof {
        assert(sp_inv_total_nanos(&s) == 469_200_000_000_000int);
        assert(spt_evenly_divisible(Unit::Second, &s));
    }
    let cfg: SpanTotal = SpanTotal::from_unit(Unit::Second);
    let r: Option<SpTotalRatio> = s.total_no_relative(&cfg);
    assert(r is Some);
    assert(match r {
        Option::Some(ratio) =>
            (ratio.numer == 469_200_000_000_000i128)
                && (ratio.denom == 1_000_000_000i128),
        Option::None => false,
    });
}

/// Negative-total witness (no upstream doc row rides this exact
/// value; the sign handling is the same Span::compare doc sentence
/// "negative spans are less than zero" states, span.rs:1929): -1
/// second totaled in Second units is the exact rational -1 (numer
/// -1e9, denom 1e9).
exec fn spt_panel_total_negative()
{
    let s: Span = Span::new().seconds(-1);
    proof {
        assert(sp_inv_total_nanos(&s) == -1_000_000_000int);
        assert(spt_evenly_divisible(Unit::Second, &s));
    }
    let cfg: SpanTotal = SpanTotal::from_unit(Unit::Second);
    let r: Option<SpTotalRatio> = s.total_no_relative(&cfg);
    assert(r is Some);
    assert(match r {
        Option::Some(ratio) =>
            (ratio.numer == -1_000_000_000i128)
                && (ratio.denom == 1_000_000_000i128),
        Option::None => false,
    });
}

/// The doc error row of SpanTotal::days_are_24_hours
/// (span.rs:4778-4787, the no-relative half):
///   let span = 2.days().hours(12);
///   // No relative date provided, which results in an error.
///   assert_eq!(
///       span.total(Unit::Hour).unwrap_err().to_string(),
///       "using unit 'day' in a span or configuration requires that \
///        either a relative reference time be given or \
///        `jiff::SpanRelativeTo::days_are_24_hours()` is used to
///        indicate invariant 24-hour days, but neither were provided",
///   );
/// The remedy rows the doc shows next (days_are_24_hours and the
/// dated From impl, both totaling 60.0 on this span) ride prune 2.
/// The error arm here is machine-checked as the exact Day-guard
/// None face.
exec fn spt_panel_doc_total_hour_err()
{
    let s: Span = Span::new().days(2).hours(12);
    proof {
        assert(sp_span_largest(&s) is Day);
        assert(sr_requires_relative_err(
            sp_unit_max(Unit::Hour, sp_span_largest(&s))));
    }
    let cfg: SpanTotal = SpanTotal::from_unit(Unit::Hour);
    let r: Option<SpTotalRatio> = s.total_no_relative(&cfg);
    assert(r is None);
}

/// The span_eq! test-macro row (span.rs:15-25, the fieldwise-compare
/// idiom Jiff's own tests use): a freshly-constructed span equals
/// its own reconstruction fieldwise (the eq direction of the
/// face), and fieldwise equality is reflexive-tight on the
/// setter-produced tier.
exec fn spf_panel_eq_row()
{
    let s1: Span = Span::new().hours(2);
    let s2: Span = Span::new().hours(2);
    let f1: SpanFieldwise = s1.fieldwise();
    let f2: SpanFieldwise = s2.fieldwise();
    let e: bool = spf_eq(&f1, &f2);
    assert(e); // span_eq!(span1, span2) is spf_eq(fieldwise, fieldwise)
    let em: bool = spf_eq_span(&f1, &s2);
    assert(em);
}

/// The Neg-face row (span.rs:3517, "Exists so that things like
/// `-1.day().fieldwise()` works as expected"):
/// -(1.day().fieldwise()) is fieldwise-equal to (-1.day()).fieldwise()
/// -- the sign flips, all fields pass through.
exec fn spf_panel_neg_row()
{
    let sp: Span = Span::new().days(1);
    let f: SpanFieldwise = sp.fieldwise();
    let nf: SpanFieldwise = spf_neg(&f);
    let sm: Span = Span::new().days(-1);
    let fm: SpanFieldwise = sm.fieldwise();
    let e: bool = spf_eq(&nf, &fm);
    assert(e);
}

} // verus!
