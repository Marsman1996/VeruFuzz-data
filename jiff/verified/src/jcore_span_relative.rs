//! jiff 0.2.43 -- the relative calendar pipeline (the J8 deferred item
//! 1): SpanRelativeTo and the relative paths of Span::checked_add /
//! checked_sub (crates/jiff/src/span.rs :4059-4250, :5481-5734,
//! :6730-6739), the Date (civil) relative arithmetic and until/since
//! faces (crates/jiff/src/civil/date.rs :1342-1430, :1623-1670,
//! :2002-2004, :2396-2415, :2725-2829), and the DateTime checked_add /
//! until / since civil consumer faces (crates/jiff/src/civil/
//! datetime.rs :1680-1743, :1995-2043, :2368-2374, :2941-2965,
//! :3268-3320) -- Verus translation, batch J9 (the relative calendar
//! batch).
//!
//! Scope by the batch instruction's clipping doctrine:
//! 1. `SpanRelativeTo` (span.rs:5481-5734) with the DaysAre24Hours
//!    marker and the civil Date/DateTime constructors, `to_relative`
//!    (span.rs:5684-5708) and `requires_relative_date_err`
//!    (span.rs:6730-6739) with exact error faces -- the gateway tier of
//!    the relative pipeline.
//! 2. The relative Some-path of Span::checked_add_span (span.rs
//!    :1767-1787): the marker (treated-invariant) and civil (start ->
//!    mid -> end -> start.until) pipelines, on top of the J8 invariant
//!    chain (relative == None stays the J8-translated entry).
//! 3. Date::checked_add_span / checked_add_duration / checked_sub
//!    (main-crate date.rs:1351-1430): the full years/months/weeks/
//!    days/time-folding body with informative field pins over the J7
//!    Neri-Schneider twins and the exact None-faces.
//! 4. Date::until / Date::since (main-crate date.rs:1623-1670) in the
//!    default (largest = Day) and the `(Unit, Date)`-configured Week
//!    forms of DateDifference::since_with_largest_unit
//!    (date.rs:2725-2829).
//! 5. DateTime::checked_add / until / since (the civil faces only).
//!
//! Modeling losses / prunes (each also annotated at its site):
//! 1. Result<T, Error> surfaces materialize as Option<T> (the J1/J5
//!    family ledger; the UnitConfigError / RangeError values are
//!    zero-sized kind witnesses).
//! 2. The Zoned arms of SpanRelativeTo (span.rs:5692-5696, :5718-5722)
//!    and of the internal Relative (span.rs:5891-5892) are pruned:
//!    real time-zone arithmetic stays out of the civil closure (the
//!    batch instruction's stretch clause); the Civil arms are fully
//!    transcribed.
//! 3. RelativeCivil's UTC `timestamp` field (span.rs:6149-6152,
//!    produced by DateTime::to_zoned(TimeZone::UTC) at :6168-6174 and
//!    :6186-6193) is pruned: it is consumed only by the rounding /
//!    Nudge / to_duration invariant surfaces (span.rs:5970-6088), none
//!    of which this batch's checked_add + until closure reaches. With
//!    it goes the near-min/max-civil-datetime conversion error arm of
//!    RelativeCivil::new / checked_add (span.rs:6163-6167, :6183-6185);
//!    recorded with the rounding pipeline.
//! 4. The Ok-faces state exact year/month/day field pins over the J7
//!    ns_civil twins, NOT valid_date: the reverse-direction validity
//!    corridor is the deferred NS reverse family (J7 deferred item 1).
//!    The zero-span arm's exact return identity (`r == Some(self)`) is
//!    carried instead (field pins would need the deferred reverse
//!    roundtrip); every other arrival route is twin-constructed.
//! 5. Date::until / since largest = Month / Year arms of
//!    since_with_largest_unit (date.rs:2761-2828 -- the month_add_one
//!    borrow-correction mass), hence DateTime::until's > Day largest
//!    arm and the Span civil pipeline's Month/Year-largest until stay
//!    deferred with the balance-and-round pipeline (J8 deferred item
//!    3).
//! 6. `std::time::Duration` rhs arms and the DateTime
//!    checked_add_duration / checked_sub duration rhs (datetime.rs
//!    :1733-1743) stay deferred with the J8 item 2 ledger; the Date
//!    checked_add_duration arm IS translated here (its as_civil_days
//!    closure is the J8 sd_as_civil_days face).
//! 7. The saturating_add / saturating_sub family (date.rs:1447-1478)
//!    rides the same entry faces and stays deferred (it only re-wraps
//!    the None arms).
//!
//! Driver mount: `verified/j9-driver.rs` mounts this file next to the
//! full src/lib.rs module tree plus the J4b/J5/J8 panels (the closed
//! panels re-verify in this run; src/lib.rs and every closed file are
//! byte-untouched by this batch).

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
    rust_div, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_associative,
    lemma_mul_is_commutative,
    lemma_mul_is_distributive_add_other_way,
    lemma_mul_is_distributive_sub,
    lemma_mul_unary_negation,
};

use crate::bounds::{Sign, Year, year_iv};
use crate::calendar::{
    ns_civil_day, ns_civil_month, ns_civil_year, ns_epoch_day_spec,
};
use crate::date::{
    Date, UnixEpochDay, days_in_month_spec, month_add_overflowing,
    ued_iv, valid_date,
};
use crate::datetime::{DateTime, valid_datetime};
use crate::jcore_signed_duration::{
    SignedDuration, sd_inv, sd_max_total_nanos, sd_min_total_nanos,
    sd_total_nanos,
};
use crate::jcore_span::{
    Span, Unit, sp_all_zero, sp_field_inv, sp_flags_ok, sp_sign_val,
    sp_zero_sign_ok,
};
use crate::jcore_span_arith::{
    S_CIVIL_DAY_SECS, S_NANOS_PER_SEC, lemma_fits_implies_sd_range,
    lemma_sd_canonical_secs, sd_checked_add_info,
    sd_from_civil_days32, sp_fid_d, sp_fid_fits, sp_fid_h,
    sp_fid_m, sp_fid_mc, sp_fid_mi, sp_fid_n_am, sp_fid_nn,
    sp_fid_r_d, sp_fid_r_h, sp_fid_r_m, sp_fid_r_s, sp_fid_s,
    sp_fid_sub, sp_fid_w, sp_from_inv_face, sp_fid_secs,
    sp_inv_total_nanos, sp_span_largest, sp_unit_max,
    sp_unit_max_exec, sp_unit_rank,
};
use crate::time::{
    Time, nanos_per_civil_day, spec_time_from_nanosecond,
    time_nanos_spec, valid_time,
};

verus! {

// ===========================================================================
// Spec kit: the unit-invariance gate, the time-only fold model, and the
// span-negation spec (the exec SignedDuration/checked-negate-free twin
// formulation the sub/since faces need; calls to exec fns are illegal
// in requires/ensures, so every negated consumer spells through this).
// ===========================================================================

/// Spec twin of Unit::is_variable (span.rs:3948-3950):
///     pub(crate) const fn is_variable(self) -> bool {
///         matches!(self, Unit::Year | Unit::Month | Unit::Week | Unit::Day)
///     }
pub open spec fn rel_unit_is_variable(u: Unit) -> bool {
    u is Year || u is Month || u is Week || u is Day
}

/// Spec twin of the Sign negation the J5 Span::negate face carries
/// (span.rs:1361-1363, `Span { sign: -self.sign, ..self }`).
pub open spec fn rel_sign_neg(sg: Sign) -> Sign {
    if sg is Zero {
        Sign::Zero
    } else if sg is Positive {
        Sign::Negative
    } else {
        Sign::Positive
    }
}

/// Spec twin of Span::negate's value (every field passes through, the
/// span-global sign flips; span.rs:1361-1363).
pub open spec fn rel_span_negate_value(s: &Span) -> Span {
    Span {
        sign: rel_sign_neg(s.sign),
        units: s.units,
        years: s.years,
        months: s.months,
        weeks: s.weeks,
        days: s.days,
        hours: s.hours,
        minutes: s.minutes,
        seconds: s.seconds,
        milliseconds: s.milliseconds,
        microseconds: s.microseconds,
        nanoseconds: s.nanoseconds,
    }
}

/// The whole time-units total a span denotes (the value face of the
/// J8 sp_to_invariant_duration_time_only, spelled at int so the
/// downstream faces read directly).
pub open spec fn rel_time_total_nanos(span: &Span) -> int {
    sp_sign_val(span.sign) * (
        ((span.hours as int) * 3_600 * 1_000_000_000)
            + ((span.minutes as int) * 60 * 1_000_000_000)
            + ((span.seconds as int) * 1_000_000_000)
            + ((span.milliseconds as int) * 1_000_000)
            + ((span.microseconds as int) * 1_000)
            + (span.nanoseconds as int))
}

/// Spec twin of the as_civil_days fold Date::checked_add_span performs
/// (main-crate date.rs:1373-1377: `b::UnixEpochDays::check(
/// span.to_invariant_duration_time_only().as_civil_days())?`), i.e.
/// SignedDuration::as_civil_days = `self.as_secs() / 86_400`
/// (signed_duration.rs:2374-2377, the J8 sd_as_civil_days_with_
/// remainder face's first component) -- two NESTED trunc divisions
/// (the sd secs field is itself the trunc of the total nanos).
pub open spec fn rel_time_days(span: &Span) -> int {
    rust_div(
        sp_fid_secs(rel_time_total_nanos(span)),
        S_CIVIL_DAY_SECS(),
    )
}

/// Origin Rust: fn requires_relative_date_err(unit: Unit)
///     -> Result<(), Error> (span.rs:6730-6739)
/// Upstream body:
///     if unit.is_variable() {
///         return Err(Error::from(if matches!(unit, Unit::Week | Unit::Day) {
///             UnitConfigError::RelativeWeekOrDay { unit }
///         } else {
///             UnitConfigError::RelativeYearOrMonth { unit }
///         }));
///     }
///     Ok(())
/// (The two error kinds are the UnitConfigError witnesses the
///  Option<()> surface brands; the kind split Week/Day vs Year/Month is
///  visible in the error text upstream and rides the same None here.)
pub exec fn rel_requires_relative_date_err(unit: Unit) -> (r: Option<()>)
    ensures
        (r is Some) <==> !(rel_unit_is_variable(unit)),
{
    let uy: bool = unit matches Unit::Year;
    let um: bool = unit matches Unit::Month;
    let uw: bool = unit matches Unit::Week;
    let ud: bool = unit matches Unit::Day;
    if uy || um || uw || ud {
        Option::None
    } else {
        Option::Some(())
    }
}

// ===========================================================================
// SpanRelativeTo (span.rs:5481-5734) -- the public relative marker,
// pruned to the civil arms (modeling loss 2; SpanRelKind below is the
// SpanRelativeToKind twin at span.rs:5712-5716 minus the Zoned arm).
// ===========================================================================

/// Origin Rust: enum SpanRelativeToKind<'a> (span.rs:5712-5716),
/// the Zoned(&'a Zoned) arm pruned (modeling loss 2).
#[derive(Clone, Copy)]
pub enum SpanRelKind {
    Civil(DateTime),
    DaysAre24Hours,
}

/// Origin Rust: pub struct SpanRelativeTo<'a> { kind:
/// SpanRelativeToKind<'a> } (span.rs:5480-5483; the upstream lifetime
/// only serves the pruned Zoned arm).
#[derive(Clone, Copy)]
pub struct SpanRel {
    pub kind: SpanRelKind,
}

impl SpanRel {

    /// Origin Rust: pub const fn days_are_24_hours()
    ///     -> SpanRelativeTo<'static> (span.rs:5650-5654)
    /// Upstream doc (span.rs:5486-5507, abridged):
    ///   Creates a special marker that indicates all days ought to be
    ///   [treated as] 24 hours without providing a relative reference
    ///   time.
    pub exec fn days_are_24_hours() -> (r: SpanRel)
        ensures
            r.kind is DaysAre24Hours,
    {
        SpanRel { kind: SpanRelKind::DaysAre24Hours }
    }

    /// Origin Rust: impl From<Date> for SpanRelativeTo<'static>
    ///     (span.rs:5730-5734):
    ///     fn from(date: Date) -> SpanRelativeTo<'static> {
    ///         let dt = DateTime::from_parts(date, Time::midnight());
    ///         SpanRelativeTo { kind: SpanRelativeToKind::Civil(dt) }
    ///     }
    pub exec fn from_date(date: Date) -> (r: SpanRel)
        ensures
            r.kind is Civil,
            match r.kind {
                SpanRelKind::Civil(dt) =>
                    dt.date == date
                        && dt.time == spec_time_from_nanosecond(0),
                SpanRelKind::DaysAre24Hours => false,
            },
    {
        let mn: Time = Time::midnight();
        let dt: DateTime = DateTime::from_parts(date, mn);
        proof {
            assert(mn == spec_time_from_nanosecond(0));
        }
        SpanRel { kind: SpanRelKind::Civil(dt) }
    }

    /// Origin Rust: impl From<DateTime> for SpanRelativeTo<'static>
    ///     (span.rs:5724-5728; the From<&Zoned> arm
    ///     span.rs:5718-5722 is pruned, modeling loss 2).
    pub exec fn from_datetime(dt: DateTime) -> (r: SpanRel)
        ensures
            r.kind is Civil,
            match r.kind {
                SpanRelKind::Civil(dt2) => dt2 == dt,
                SpanRelKind::DaysAre24Hours => false,
            },
    {
        SpanRel { kind: SpanRelKind::Civil(dt) }
    }

    /// Origin Rust: fn to_relative(&self, unit: Unit)
    ///     -> Result<Option<Relative<'a>>, Error> (span.rs:5684-5708)
    /// Upstream doc (span.rs:5666-5677, abridged):
    ///   Converts this public API relative datetime into a more
    ///   versatile internal representation of the same concept. The
    ///   unit given should be the maximal non-zero unit present in the
    ///   operation. [...]
    ///   In effect, given that `unit` is the maximal unit involved,
    ///   `None` is returned when it's safe to [take] that all units in
    ///   the spans can be interpreted as invariant (even if they can
    ///   sometimes be varying).
    /// Body verdict (span.rs:5685-5707): the `!unit.is_variable()` arm
    /// returns Ok(None) for EVERY kind first; the Civil arm returns
    /// the datetime (the RelativeCivil timestamp field is modeling
    /// loss 3); the DaysAre24Hours arm errors precisely on
    /// Year | Month.
    pub exec fn to_relative(&self, unit: Unit)
        -> (r: Option<Option<DateTime>>)
        ensures
            match self.kind {
                SpanRelKind::Civil(dt) =>
                    if rel_unit_is_variable(unit) {
                        r == Option::Some(Option::Some(dt))
                    } else {
                        r == Option::Some(Option::None)
                    },
                SpanRelKind::DaysAre24Hours =>
                    if rel_unit_is_variable(unit) {
                        if unit is Year || unit is Month {
                            r == Option::None
                        } else {
                            r == Option::Some(Option::None)
                        }
                    } else {
                        r == Option::Some(Option::None)
                    },
            },
    {
        let uy: bool = unit matches Unit::Year;
        let um: bool = unit matches Unit::Month;
        let uw: bool = unit matches Unit::Week;
        let ud: bool = unit matches Unit::Day;
        let variable: bool = uy || um || uw || ud;
        if !variable {
            return Option::Some(Option::None);
        }
        match self.kind {
            SpanRelKind::Civil(dt) => {
                Option::Some(Option::Some(dt))
            }
            SpanRelKind::DaysAre24Hours => {
                let uy: bool = unit matches Unit::Year;
                let um: bool = unit matches Unit::Month;
                if uy || um {
                    Option::None
                } else {
                    Option::Some(Option::None)
                }
            }
        }
    }
}

// ===========================================================================
// Date::checked_add_span (main-crate date.rs:1351-1380) -- the shared
// gates spec, the shared result face, then the per-case exec arms
// (wall 46: each case is its own fn / obligation family).
// ===========================================================================

/// The month-move component of the gates (the month_add_overflowing
/// spec face, date.rs:3422-3433, over the SIGNED months move
/// span.get_months() hands it at :1364).
pub open spec fn rel_months_move(d: Date, span: &Span) -> int {
    (d.month as int) - 1
        + sp_sign_val(span.sign) * (span.months as int)
}

// The month-core Euclid bridge: month_add_overflowing's ensures pair
// (date.rs:3422-3433: r.1 * 12 + r.0 - 1 == total and r.0 == total % 12
// + 1) recast as the spec-side carry (t - t % 12) / 12.
proof fn lemma_month_carry_bridge(t: int, yl: int, ml: int)
    requires
        (yl * 12) + ml - 1 == t,
        ml == t % 12 + 1,
    ensures
        yl == (t - t % 12) / 12,
{
    lemma_fundamental_div_mod_converse(t, 12, yl, t % 12);
    lemma_fundamental_div_mod(t, 12);
    assert(t - t % 12 == 12 * yl);
}

/// The shared move components of the Date span rhs, ONE unfold for
/// every face below (the months machinery of month_add_overflowing +
/// the b::Year chain, the constrained day clamp, the weeks/days adds
/// and the time-only as_civil_days fold, all at int).
pub open spec fn rel_date_move_parts(
    d: Date,
    span: &Span,
) -> (int, int, int, int, int, int, int) {
    let sv: int = sp_sign_val(span.sign);
    let t_m: int = rel_months_move(d, span);
    let m2: int = t_m % 12 + 1;
    let yc: int = (t_m - t_m % 12) / 12;
    let y1: int = (d.year as int) + yc;
    let y2: int = y1 + sv * (span.years as int);
    let dcl: int = if (d.day as int)
        > days_in_month_spec(y2, m2) {
        days_in_month_spec(y2, m2)
    } else {
        d.day as int
    };
    let base: int = ns_epoch_day_spec(y2, m2, dcl);
    let wp7: int = sv * ((span.weeks as int) * 7);
    let dtoff: int = sv * (span.days as int);
    let toff: int = rel_time_days(span);
    let total: int = base + wp7 + dtoff + toff;
    (y1, y2, base, wp7, dtoff, toff, total)
}

/// The gated-machine component shared by the Some- and None-faces of
/// the Date span rhs: the sequential b::Year::checked_add gates
/// (date.rs:1365-1366), the b::UnixEpochDays::check gate on the
/// time-only fold (date.rs:1374-1376), and the three sequential
/// UnixEpochDay::checked_add range gates in their upstream order
/// (date.rs:1368-1378), folded through the single parts unfold.
/// The gates over the parts VALUES (so a body that has already
/// derived the parts can assert the machine gate outcome without
/// unfolding the month machinery again).
pub open spec fn rel_date_gates_at(
    y1: int,
    y2: int,
    base: int,
    wp7: int,
    dtoff: int,
    toff: int,
    total: int,
) -> bool {
    year_iv().contains(y1)
        && year_iv().contains(y2)
        && ued_iv().contains(toff)
        && ued_iv().contains(base + wp7)
        && ued_iv().contains(base + wp7 + dtoff)
        && ued_iv().contains(total)
}

pub open spec fn rel_date_gates_ok(
    d: Date,
    span: &Span,
) -> bool {
    let (y1, y2, base, wp7, dtoff, toff, total) =
        rel_date_move_parts(d, span);
    rel_date_gates_at(y1, y2, base, wp7, dtoff, toff, total)
}

/// The shared result face of Date::checked_add_span (and of its
/// checked_sub and operator rewraps): exact two-sided precision -- the
/// None-face is the negation of the machine gates (the upstream body
/// returns Some exactly when every gate passes, since new_constrain's
/// own arm is unreachable on the m2/day domain the Somes establish),
/// and the Some-face pins the result fields over the J7 twins except on
/// the zero-span arm where the exact identity return is pinned
/// (modeling loss 4).
pub open spec fn rel_date_add_span_face(
    d: Date,
    span: &Span,
    r: &Option<Date>,
) -> bool {
    let (y1, y2, base, wp7, dtoff, toff, total) =
        rel_date_move_parts(d, span);
    match r {
        Option::Some(d2) =>
            // Light gates on the Some-side: the year gates' outer
            // two conjuncts and the final total containment (the
            // machine year-chain and the final checked add establish
            // these on every Some-path; the full sequential gates
            // conjunct stays on the None-side and in the wrappers).
            (sp_all_zero(span) ==> (d2 == d))
                && (!sp_all_zero(span)
                    ==> (year_iv().contains(y1)
                        && year_iv().contains(y2)
                        && ued_iv().contains(total)
                        && (d2.year as int)
                            == ns_civil_year(total)
                        && (d2.month as int)
                            == ns_civil_month(total)
                        && (d2.day as int)
                            == ns_civil_day(total))),
        Option::None =>
            !sp_all_zero(span) && !rel_date_gates_ok(d, span),
    }
}

/// The days-only parts collapse (the zero months/years/weeks/time
/// lanes): everything reduces to the anchor (the date's own epoch day)
/// plus the signed days move; the year gates hold by valid_date. This
/// is the offloaded machinery proof the days-only arm consumes (the
/// exec keeps the epoch anchor from to_unix_epoch_day_ns's own face,
/// so no corridor reasoning re-enters).
proof fn rel_lemma_dayonly_parts(
    d: Date,
    span: &Span,
    anchor: int,
)
    requires
        valid_date(d),
        sp_field_inv(span),
        span.months == 0,
        span.years == 0,
        span.weeks == 0,
        span.hours == 0,
        span.minutes == 0,
        span.seconds == 0,
        span.milliseconds == 0,
        span.microseconds == 0,
        span.nanoseconds == 0,
        anchor
            == ns_epoch_day_spec(
                d.year as int,
                d.month as int,
                d.day as int,
            ),
        ued_iv().contains(anchor),
    ensures
        ({
            let (y1, y2, base, wp7, dtoff, toff, total) =
                rel_date_move_parts(d, span);
            &&& y1 == (d.year as int)
            &&& y2 == (d.year as int)
            &&& base == anchor
            &&& wp7 == 0
            &&& toff == 0
            &&& total == anchor + dtoff
            &&& year_iv().contains(y1)
            &&& ued_iv().contains(toff)
            &&& ued_iv().contains(base)
        })
{
    // month move identity on the all-calendar-zero-but-days span, the
    // day clamp identity from valid_date, the zero time fold, and the
    // year gates from valid_date's own bounds.
}

/// The day-only arm of checked_add_span (date.rs:1355-1361: the
/// `span.units().contains_only(Unit::Day)` fast path, whose upstream
/// body is the jcore Date::checked_add(days) day-count add).
/// Route note: the jcore body's 0/+1/-1 fast paths are value-identical to
/// the epoch-day route on every in-domain input (the agreement is
/// witness-checked by the J7 repair panels; J7/notes.md item S1), and
/// this batch's informative content rides the J7 twins, so the arm is
/// materialized through to_unix_epoch_day_ns / to_date_ns.
fn rel_date_add_span_days_only(
    d: &Date,
    span: &Span,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        span.months == 0,
        span.years == 0,
        span.weeks == 0,
        span.hours == 0,
        span.minutes == 0,
        span.seconds == 0,
        span.milliseconds == 0,
        span.microseconds == 0,
        span.nanoseconds == 0,
        span.days != 0,
    ensures
        rel_date_add_span_face(*d, span, &r),
{
    let gd: i32 = span.get_days();
    let base: UnixEpochDay = d.to_unix_epoch_day_ns();
    proof {
        rel_lemma_dayonly_parts(
            *d, span, base.day as int);
    }
    let moved: Option<UnixEpochDay> = base.checked_add(gd);
    match moved {
        Option::Some(e2) => {
            proof {
                // the collapsed gates hold on the Some path (linear
                // over the lemma's parts); the Some-face pins ride
                // to_date_ns over e2's exact day.
                assert(rel_date_gates_ok(*d, span));
            }
            Option::Some(e2.to_date_ns())
        }
        Option::None => {
            proof {
                assert(!rel_date_gates_ok(*d, span));
            }
            Option::None
        }
    }
}

/// The general arm of checked_add_span (date.rs:1363-1379): the
/// month_add_overflowing + b::Year chain, the new_constrain clamp, the
/// to_unix_epoch_day + weeks/days checked adds, and the time-only
/// as_civil_days fold (gated by `!span.units().only_time().is_empty()`
/// date.rs:1373, spelled from sp_flags_ok as the any-time-nonzero
/// disjunction).
/// The calendar half of the general arm (wall 46: the two halves are
/// separate fns so each obligation family stays query-light): the
/// month_add_overflowing + b::Year chain, the new_constrain clamp and
/// the constrained date's epoch-day anchor. On Some it hands the day
/// half the machine parts VALUES (the parts twin's base, y1, y2);
/// None is exactly the year-gate failure.
fn rel_date_cal_half(
    d: &Date,
    span: &Span,
) -> (res: Option<(UnixEpochDay, i64, i64)>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
    ensures
        ({
            let (y1p, y2p, basep, wp7p, dtoffp, toffp, totalp) =
                rel_date_move_parts(*d, span);
            match res {
                Option::Some((base, y1v, y2v)) =>
                    y1v == y1p
                        && y2v == y2p
                        && year_iv().contains(y1v as int)
                        && year_iv().contains(y2v as int)
                        && (base.day as int) == basep
                        && ued_iv().contains(basep),
                Option::None =>
                    !(year_iv().contains(y1p)
                        && year_iv().contains(y2p)),
            }
        })
{
    let gm: i32 = span.get_months();
    let (ml, yl) = month_add_overflowing(d.month, gm);
    proof {
        let sv: int = sp_sign_val(span.sign);
        let t_m: int = (d.month as int) - 1 + (gm as int);
        assert((gm as int) == sv * (span.months as int));
        assert(t_m == rel_months_move(*d, span));
        assert((ml as int) == t_m % 12 + 1);
        lemma_month_carry_bridge(t_m, yl as int, ml as int);
    }
    let y1o: Option<i16> = Year::checked_add(d.year, yl);
    let y1: i16 = match y1o {
        Option::Some(v) => v,
        Option::None => {
            proof {
                let (y1p, y2p, basep, wp7, dtoff, toff, total) =
                    rel_date_move_parts(*d, span);
                assert(!year_iv().contains(y1p));
            }
            return Option::None;
        }
    };
    let gy: i16 = span.get_years();
    proof {
        let sv: int = sp_sign_val(span.sign);
        assert((gy as int) == sv * (span.years as int));
    }
    let y2o: Option<i16> = Year::checked_add(y1, gy);
    let y2: i16 = match y2o {
        Option::Some(v) => v,
        Option::None => {
            proof {
                let (y1p, y2p, basep, wp7, dtoff, toff, total) =
                    rel_date_move_parts(*d, span);
                assert(!year_iv().contains(y2p));
            }
            return Option::None;
        }
    };
    let dco: Option<Date> = Date::new_constrain(y2, ml, d.day);
    let dc: Date = match dco {
        Option::Some(v) => v,
        Option::None => {
            proof {
                assert(year_iv().contains(y2 as int));
                assert(1 <= ml as int && ml as int <= 12);
                assert(1 <= d.day as int);
                assert(false);
            }
            return Option::None;
        }
    };
    let base: UnixEpochDay = dc.to_unix_epoch_day_ns();
    proof {
        let sv: int = sp_sign_val(span.sign);
        let (y1p, y2p, basep, wp7, dtoff, toff, total) =
            rel_date_move_parts(*d, span);
        assert((dc.year as int) == y2p);
        assert((dc.month as int)
            == ((d.month as int) - 1
                + sv * (span.months as int)) % 12 + 1);
        assert((dc.day as int)
            == if (d.day as int)
                > days_in_month_spec(y2p, (dc.month as int)) {
                days_in_month_spec(y2p, (dc.month as int))
            } else {
                d.day as int
            });
        assert((base.day as int) == basep);
        assert((y1 as int) == y1p);
        assert((y2 as int) == y2p);
    }
    Option::Some((base, y1 as i64, y2 as i64))
}

/// The day half of the general arm: the epoch-day chain (weeks, days,
/// the time-only as_civil_days fold), consuming the calendar half's
/// machine parts values (the None-face is the gates tail). The parts
/// twin is re-bound at each relay site (the same-term hash-consing
/// keeps one AIR body under the multiple sites).
// The deferral note of the first draft (external contract at this
// site) is resolved this batch: the residual the rlimit ladder could
// not close was the face's sp_all_zero identity branch, which needs
// the deferred NS reverse family when a zero-magnitude span reaches
// this depth -- impossible on this arm, because the entry routes the
// all-zero span to its identity return BEFORE the machinery split.
// The `!sp_all_zero` requires conjunct below pins that routing fact,
// and the body then closes within the batch rlimit (every Some here
// is twin-constructed, so the face pins ride the J7 forward twins).
fn rel_date_day_half_finish(
    d: &Date,
    span: &Span,
    u3: &UnixEpochDay,
    td: i32,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
        (td as int) == rel_time_days(span),
        ued_iv().contains(td as int),
        ({
            let (y1p, y2p, basep, wp7, dtoff, toff, total) =
                rel_date_move_parts(*d, span);
            year_iv().contains(y1p)
                && year_iv().contains(y2p)
                && ued_iv().contains(basep)
                && ued_iv().contains(basep + wp7)
                && ued_iv().contains(basep + wp7 + dtoff)
                && (u3.day as int)
                    == basep + wp7 + dtoff
                && ued_iv().contains(u3.day as int)
        }),
    ensures
        rel_date_add_span_face(*d, span, &r),
{
    let u4o: Option<UnixEpochDay> = u3.checked_add(td);
    match u4o {
        Option::Some(e3) => {
            Option::Some(e3.to_date_ns())
        }
        Option::None => {
            proof {
                assert(!rel_date_gates_ok(*d, span));
            }
            Option::None
        }
    }
}

fn rel_date_day_half_tail_nz(
    d: &Date,
    span: &Span,
    u3: &UnixEpochDay,
    td64: i64,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
        (td64 as int) == rel_time_days(span),
        ({
            let (y1p, y2p, basep, wp7, dtoff, toff, total) =
                rel_date_move_parts(*d, span);
            year_iv().contains(y1p)
                && year_iv().contains(y2p)
                && ued_iv().contains(basep)
                && ued_iv().contains(basep + wp7)
                && ued_iv().contains(basep + wp7 + dtoff)
                && (u3.day as int)
                    == basep + wp7 + dtoff
                && ued_iv().contains(u3.day as int)
        }),
    ensures
        rel_date_add_span_face(*d, span, &r),
{
    // b::UnixEpochDays::check(time_days)? -- the error arm is the
    // ued range gate (date.rs:1374-1376); the machine guard keeps
    // the int casts in the proof tier.
    if td64 < -4_371_587i64 || td64 > 2_932_896i64 {
        proof {
            assert(!(ued_iv().contains(td64 as int)));
            assert(!rel_date_gates_ok(*d, span));
        }
        return Option::None;
    }
    let td: i32 = td64 as i32;
    rel_date_day_half_finish(d, span, u3, td)
}

// The first draft's external-contract form here is resolved the same
// way as the tail above: with `!sp_all_zero` pinned in the requires
// (the entry's identity arm owns the all-zero span), the face's
// machinery branch closes from the caller-conjured parts conjunct
// plus the zero-time fold the block below spells, within the batch
// rlimit.
fn rel_date_day_half_tail_z(
    d: &Date,
    span: &Span,
    u3: &UnixEpochDay,
) -> (d2: Date)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
        (span.hours == 0 && span.minutes == 0
            && span.seconds == 0
            && span.milliseconds == 0
            && span.microseconds == 0
            && span.nanoseconds == 0),
        ({
            let (y1p, y2p, basep, wp7, dtoff, toff, total) =
                rel_date_move_parts(*d, span);
            year_iv().contains(y1p)
                && year_iv().contains(y2p)
                && ued_iv().contains(basep)
                && ued_iv().contains(basep + wp7)
                && ued_iv().contains(basep + wp7 + dtoff)
                && (u3.day as int)
                    == basep + wp7 + dtoff
                && ued_iv().contains(u3.day as int)
        }),
    ensures
        rel_date_add_span_face(
            *d, span, &Option::Some(d2)),
{
    proof {
        // the zero time lanes (the sign product fixed per case).
        if span.sign is Zero {
            assert(sp_sign_val(span.sign) == 0);
        } else if span.sign is Positive {
            assert(sp_sign_val(span.sign) == 1);
        } else {
            assert(sp_sign_val(span.sign) == 0 - 1);
        }
        assert(rel_time_total_nanos(span) == 0);
        assert(rel_time_days(span) == 0);
    }
    u3.to_date_ns()
}

/// The day half of the general arm: the epoch-day chain (weeks, days,
/// the time-only as_civil_days fold), consuming the calendar half's
/// machine parts values (the None-face is the gates tail). The parts
/// twin is re-bound at each relay site and the two tails are separate
/// fns (the same-term hash-consing plus the function-boundary split
/// keep each obligation family under the batch rlimit; wall 46).
fn rel_date_day_half(
    d: &Date,
    span: &Span,
    base: &UnixEpochDay,
    y1v: i64,
    y2v: i64,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
        ({
            let (y1p, y2p, basep, wp7, dtoff, toff, total) =
                rel_date_move_parts(*d, span);
            y1v == y1p && y2v == y2p
                && (base.day as int) == basep
                && ued_iv().contains(basep)
                && year_iv().contains(y1v as int)
                && year_iv().contains(y2v as int)
        }),
    ensures
        rel_date_add_span_face(*d, span, &r),
{
    proof {
        // the year gates ride from the machine y1v/y2v slots; the
        // parts identities the relays below cite.
        let (y1p, y2p, basep, wp7p, dtoffp, toffp, totalp) =
            rel_date_move_parts(*d, span);
        assert(y1p == y1v as int);
        assert(y2p == y2v as int);
        assert(year_iv().contains(y1p));
        assert(year_iv().contains(y2p));
        assert(toffp == rel_time_days(span));
        assert(wp7p
            == sp_sign_val(span.sign)
                * ((span.weeks as int) * 7));
        assert(dtoffp
            == sp_sign_val(span.sign) * (span.days as int));
    }
    let gw: i32 = span.get_weeks();
    proof {
        let sv: int = sp_sign_val(span.sign);
        assert((gw as int) == sv * (span.weeks as int));
        assert(-(1_043_497i32) <= gw);
        assert(gw <= 1_043_497i32);
    }
    let w7: i32 = 7 * gw;
    let u2o: Option<UnixEpochDay> = base.checked_add(w7);
    let u2: UnixEpochDay = match u2o {
        Option::Some(v) => v,
        Option::None => {
            proof {
                assert(!rel_date_gates_ok(*d, span));
            }
            return Option::None;
        }
    };
    let gd: i32 = span.get_days();
    proof {
        let sv: int = sp_sign_val(span.sign);
        assert((gd as int) == sv * (span.days as int));
    }
    let u3o: Option<UnixEpochDay> = u2.checked_add(gd);
    let u3: UnixEpochDay = match u3o {
        Option::Some(v) => v,
        Option::None => {
            proof {
                assert(!rel_date_gates_ok(*d, span));
            }
            return Option::None;
        }
    };
    let time_nonzero: bool = span.hours != 0
        || span.minutes != 0
        || span.seconds != 0
        || span.milliseconds != 0
        || span.microseconds != 0
        || span.nanoseconds != 0;
    if time_nonzero {
        let tsd: SignedDuration =
            span.sp_to_invariant_duration_time_only();
        let (td64, _rem) = tsd.sd_as_civil_days_with_remainder();
        proof {
            assert(sd_total_nanos(&tsd)
                == rel_time_total_nanos(span));
            lemma_sd_canonical_secs(&tsd);
            assert((tsd.secs as int)
                == sp_fid_secs(rel_time_total_nanos(span)));
            assert((td64 as int) == rel_time_days(span));
        }
        rel_date_day_half_tail_nz(d, span, &u3, td64)
    } else {
        Option::Some(
            rel_date_day_half_tail_z(d, span, &u3))
    }
}

/// The general arm of checked_add_span (date.rs:1363-1379), split
/// into the calendar and day halves above so each obligation family
/// stays verifiable under the batch rlimit (wall 46).
fn rel_date_add_span_general(
    d: &Date,
    span: &Span,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
    ensures
        rel_date_add_span_face(*d, span, &r),
{
    match rel_date_cal_half(d, span) {
        Option::None => {
            proof {
                assert(!rel_date_gates_ok(*d, span));
            }
            Option::None
        }
        Option::Some((base, y1v, y2v)) => {
            rel_date_day_half(d, span, &base, y1v, y2v)
        }
    }
}

/// Origin Rust: fn checked_add_span(self, span: &Span)
///     -> Result<Date, Error> (main-crate date.rs:1351-1380)
/// Upstream body:
///     if span.is_zero() { return Ok(self); }
///     if span.units().contains_only(Unit::Day) {
///         return self.inner.checked_add(span.get_days())
///             .map(Date::from_jcore).map_err(Error::jcore_range);
///     }
///     ... the general arm above
/// (is_zero is the sign-based test; on every span upstream's setters
///  can produce it agrees with the field-disjunction test below --
///  both directions of the zero-sign correspondence hold there, and
///  sp_zero_sign_ok carries the direction this file's domain states.
///  The zero arm is transcribed on the FIELD test so it lands exactly
///  on the face's sp_all_zero identity: an all-zero span returns the
///  identity date structurally, and every span routed to the
///  machinery is non-all-zero, which the tails' `!sp_all_zero`
///  requires conjuncts pin. contains_only(Day) is the day flag alone
///  under sp_flags_ok.)
pub exec fn rel_date_checked_add_span(
    d: &Date,
    span: &Span,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
    ensures
        rel_date_add_span_face(*d, span, &r),
{
    let zero: bool = span.years == 0
        && span.months == 0
        && span.weeks == 0
        && span.days == 0
        && span.hours == 0
        && span.minutes == 0
        && span.seconds == 0
        && span.milliseconds == 0
        && span.microseconds == 0
        && span.nanoseconds == 0;
    if zero {
        Option::Some(*d)
    } else {
        let day_only: bool = span.months == 0
            && span.years == 0
            && span.weeks == 0
            && span.hours == 0
            && span.minutes == 0
            && span.seconds == 0
            && span.milliseconds == 0
            && span.microseconds == 0
            && span.nanoseconds == 0
            && span.days != 0;
        if day_only {
            rel_date_add_span_days_only(d, span)
        } else {
            rel_date_add_span_general(d, span)
        }
    }
}

// ===========================================================================
// Date::checked_add_duration (main-crate date.rs:1383-1394) and the
// checked_sub / operator surfaces.
// ===========================================================================

/// The whole-days truncation component (the as_civil_days value face;
/// upstream doc, date.rs:1320-1322: "Only whole numbers of days are
/// considered. Since this is a civil date unaware of time zones, days
/// are always 24 hours. [...] Any leftover time is truncated.").
pub open spec fn rel_dur_days_of(dur: &SignedDuration) -> int {
    rust_div(dur.secs as int, S_CIVIL_DAY_SECS())
}

/// The shared result face of the SignedDuration rhs: both machine
/// gates (b::UnixEpochDays::check then the epoch range add,
/// date.rs:1387-1393) with the day-count target over the J7 twins.
pub open spec fn rel_date_add_sd_face(
    d: Date,
    dur: &SignedDuration,
    r: &Option<Date>,
) -> bool {
    let base: int = ns_epoch_day_spec(
        d.year as int,
        d.month as int,
        d.day as int,
    );
    let td: int = rel_dur_days_of(dur);
    let ok: bool = ued_iv().contains(td)
        && ued_iv().contains(base + td);
    match r {
        Option::Some(d2) =>
            ok
                && (d2.year as int)
                    == ns_civil_year(base + td)
                && (d2.month as int)
                    == ns_civil_month(base + td)
                && (d2.day as int)
                    == ns_civil_day(base + td),
        Option::None => !ok,
    }
}

/// Origin Rust: fn checked_add_duration(self, duration: SignedDuration)
///     -> Result<Date, Error> (main-crate date.rs:1383-1394)
/// Upstream body:
///     let days = b::UnixEpochDays::check(duration.as_civil_days())
///         .context(E::OverflowDaysDuration)?;
///     return self.inner.checked_add(days)
///         .map(Date::from_jcore).map_err(Error::jcore_range);
/// (Route note: as_civil_days is the J8 sd_as_civil_days_with_
///  remainder face's first component; the jcore day add is the epoch
///  route as in the day-only arm above.)
pub exec fn rel_date_checked_add_sd(
    d: &Date,
    dur: &SignedDuration,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sd_inv(dur),
    ensures
        rel_date_add_sd_face(*d, dur, &r),
{
    let (td64, _rem) = dur.sd_as_civil_days_with_remainder();
    proof {
        lemma_sd_canonical_secs(dur);
        let q: int = rust_div(dur.secs as int, 86_400);
        assert((td64 as int) == q);
        assert(q == rel_dur_days_of(dur));
    }
    if td64 < -4_371_587i64 || td64 > 2_932_896i64 {
        proof {
            assert(!(ued_iv().contains(td64 as int)));
        }
        return Option::None;
    }
    let td: i32 = td64 as i32;
    let base: UnixEpochDay = d.to_unix_epoch_day_ns();
    let moved: Option<UnixEpochDay> = base.checked_add(td);
    match moved {
        Option::Some(e2) => {
            proof {
                let basei: int = ns_epoch_day_spec(
                    d.year as int,
                    d.month as int,
                    d.day as int,
                );
                assert((e2.day as int) == basei + td64 as int);
                assert(ued_iv().contains(basei + td64 as int));
            }
            Option::Some(e2.to_date_ns())
        }
        Option::None => Option::None,
    }
}

/// Origin Rust: pub fn checked_sub<A: Into<DateArithmetic>>(
///     self, duration: A) -> Result<Date, Error>
///     (main-crate date.rs:1422-1428)
/// Upstream doc (date.rs:1396-1401):
///   This routine is identical to [Date::checked_add] with the
///   duration negated.
/// Upstream body: `duration.checked_neg().and_then(|da|
/// da.checked_add(self))` -- the Span rhs arm's checked_neg is
/// Span::negate (total, the J5 face), so sub = add(negated rhs)
/// exactly; the None-face is the negated span's gates.
pub exec fn rel_date_checked_sub_span(
    d: &Date,
    span: &Span,
) -> (r: Option<Date>)
    requires
        valid_date(*d),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
    ensures
        rel_date_add_span_face(
            *d,
            &rel_span_negate_value(span),
            &r,
        ),
{
    let neg: Span = span.negate();
    proof {
        assert(neg == rel_span_negate_value(span));
    }
    rel_date_checked_add_span(d, &neg)
}

/// Origin Rust: impl core::ops::Add<Span> for Date
///     (main-crate date.rs:2091-2098)
/// Upstream doc:
///   Adds a span of time to a date.
///   This uses checked arithmetic and panics on overflow. To handle
///   overflow without panics, use [Date::checked_add].
/// Upstream body: self.checked_add(rhs).expect(
///     "adding span to date overflowed")
/// The panic face materializes as the requires (the unreachable None
/// arm becomes the dead-branch proof).
pub exec fn rel_date_add_op(d: &Date, rhs: &Span) -> (d2: Date)
    requires
        valid_date(*d),
        sp_field_inv(rhs),
        sp_zero_sign_ok(rhs),
        sp_flags_ok(rhs),
        sp_all_zero(rhs) || rel_date_gates_ok(*d, rhs),
    ensures
        rel_date_add_span_face(*d, rhs, &Option::Some(d2)),
{
    match rel_date_checked_add_span(d, rhs) {
        Option::Some(v) => v,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    }
}

/// Origin Rust: impl core::ops::Sub<Span> for Date
///     (main-crate date.rs:2115-2122)
/// Upstream body: self.checked_sub(rhs).expect(
///     "subing span to date overflowed")
/// SPEC NOTE (record-only): the upstream expect text reads "subing"
/// -- a typo for "subtracting" (not a behavioral issue).
pub exec fn rel_date_sub_op(d: &Date, rhs: &Span) -> (d2: Date)
    requires
        valid_date(*d),
        sp_field_inv(rhs),
        sp_zero_sign_ok(rhs),
        sp_flags_ok(rhs),
        sp_all_zero(rhs)
            || rel_date_gates_ok(
                *d,
                &rel_span_negate_value(rhs),
            ),
    ensures
        rel_date_add_span_face(
            *d,
            &rel_span_negate_value(rhs),
            &Option::Some(d2),
        ),
{
    let neg: Span = rhs.negate();
    proof {
        assert(neg == rel_span_negate_value(rhs));
    }
    rel_date_add_op(d, &neg)
}

// ===========================================================================
// Date::until / Date::since (main-crate date.rs:1623-1670) in the
// configurations this batch translates: largest in {Day (the default),
// Week (the (Unit, Date) From impl)}, no rounding (the default
// DateDifference: Trunc / smallest Day / increment 1 -- date.rs
// :2528-2537's "We use truncation rounding by default" comment and
// the rounding_may_change_span gate it makes false).
// ===========================================================================

/// The weeks lane of the until/since span: zero unless the
/// Week-largest configuration is requested (date.rs:2751-2758).
pub open spec fn rel_dur_weeks_lane(largest: Unit, dd: int) -> int {
    if largest is Week {
        rust_div(dd, 7)
    } else {
        0
    }
}

/// The days lane of the until/since span (date.rs:2752-2758:
/// `weeks = days / 7; days %= 7` under the i32 rust-trunc semantics).
pub open spec fn rel_dur_days_lane(largest: Unit, dd: int) -> int {
    if largest is Week {
        rust_rem(dd, 7)
    } else {
        dd
    }
}

/// The shared result face of Date::until (and, with the difference
/// reversed, Date::since): the calendar-remainder difference is pinned
/// exactly on its lanes (the until_days value face is the J7
/// Date::until twin, calendar.rs since/until), the unit tier is
/// pinned, and the invariant-total identity carries the content the
/// pipelined consumers need.
pub open spec fn rel_date_until_face(
    d1: Date,
    d2: Date,
    largest: Unit,
    s: &Span,
) -> bool {
    let dd: int = ns_epoch_day_spec(
        d2.year as int,
        d2.month as int,
        d2.day as int,
    ) - ns_epoch_day_spec(
        d1.year as int,
        d1.month as int,
        d1.day as int,
    );
    sp_field_inv(s)
        && sp_zero_sign_ok(s)
        && sp_flags_ok(s)
        && s.years == 0
        && s.months == 0
        && s.hours == 0
        && s.minutes == 0
        && s.seconds == 0
        && s.milliseconds == 0
        && s.microseconds == 0
        && s.nanoseconds == 0
        && ((dd > 0)
            ==> (s.sign is Positive
                && (s.weeks as int)
                    == rel_dur_weeks_lane(largest, dd)
                && (s.days as int)
                    == rel_dur_days_lane(largest, dd)))
        && ((dd < 0)
            ==> (s.sign is Negative
                && (s.weeks as int)
                    == 0 - rel_dur_weeks_lane(largest, dd)
                && (s.days as int)
                    == 0 - rel_dur_days_lane(largest, dd)))
        && ((dd == 0) ==> (s.sign is Zero && sp_all_zero(s)))
        && sp_inv_total_nanos(s)
            == dd * S_CIVIL_DAY_SECS() * S_NANOS_PER_SEC()
}

/// The since-face twin: the until lane skeleton with the calendar
/// difference reversed and spelled DIRECTLY (the wrapper body
/// negates the until-span, date.rs:1659-1670, so the difference, the
/// lanes and the total negate while the magnitudes re-sign; a direct
/// spelling keeps the conjunct positions diagnosable and gives the
/// body's lane-negation proof a specific goal).
pub open spec fn rel_date_since_face(
    d1: Date,
    d2: Date,
    largest: Unit,
    s: &Span,
) -> bool {
    let dds: int = ns_epoch_day_spec(
        d1.year as int,
        d1.month as int,
        d1.day as int,
    ) - ns_epoch_day_spec(
        d2.year as int,
        d2.month as int,
        d2.day as int,
    );
    sp_field_inv(s)
        && sp_zero_sign_ok(s)
        && sp_flags_ok(s)
        && s.years == 0
        && s.months == 0
        && s.hours == 0
        && s.minutes == 0
        && s.seconds == 0
        && s.milliseconds == 0
        && s.microseconds == 0
        && s.nanoseconds == 0
        && ((dds > 0)
            ==> (s.sign is Positive
                && (s.weeks as int)
                    == rel_dur_weeks_lane(largest, dds)
                && (s.days as int)
                    == rel_dur_days_lane(largest, dds)))
        && ((dds < 0)
            ==> (s.sign is Negative
                && (s.weeks as int)
                    == 0 - rel_dur_weeks_lane(largest, dds)
                && (s.days as int)
                    == 0 - rel_dur_days_lane(largest, dds)))
        && ((dds == 0) ==> (s.sign is Zero && sp_all_zero(s)))
        && sp_inv_total_nanos(s)
            == dds * S_CIVIL_DAY_SECS() * S_NANOS_PER_SEC()
}

/// Origin Rust: pub fn until<A: Into<DateDifference>>(
///     self, other: A) -> Result<Span, Error>
///     (main-crate date.rs:1623-1634) over
/// DateDifference::since_with_largest_unit (date.rs:2725-2829) at
/// the default (Day) / (Unit, Date)-Week configurations.
/// Upstream doc (date.rs:1480-1489, abridged):
///   Returns a span representing the elapsed time from this date until
///   the given `other` date.
///   When `other` occurs before this date, then the span returned will
///   be negative.
///   By default, the span returned is balanced such that the biggest
///   and smallest possible unit is days.
/// Upstream doc (date.rs:1516-1518, # Errors):
///   It is guaranteed that if one provides a date with the default
///   [DateDifference] configuration, then this routine will never
///   fail.
/// (The same never-fails verdict holds on the Week configuration: the
///  day-difference fits the b::SpanDays range on the whole Date
///  domain, J2 notes' 7_304_483 == Date::MAX.until(Date::MIN) ledger.)
pub exec fn rel_date_until_span(
    d1: Date,
    d2: Date,
    largest: Unit,
) -> (s: Span)
    requires
        valid_date(d1),
        valid_date(d2),
        largest is Day || largest is Week,
    ensures
        rel_date_until_face(d1, d2, largest, &s),
{
    // the equal-dates early return (date.rs:2748-2750).
    let same: bool = d1.year == d2.year
        && d1.month == d2.month
        && d1.day == d2.day;
    let ddays: i32 = if same {
        return Span::new();
    } else {
        // until_days (date.rs:2002-2004) is the J7 Date::until twin.
        d1.until(d2)
    };
    let is_week: bool = largest matches Unit::Week;
    let (w32, dr32): (i32, i32) = if is_week {
        let q: i32 = ddays / 7;
        let r: i32 = ddays % 7;
        proof {
            lemma_fundamental_div_mod(ddays as int, 7);
            assert((ddays as int)
                == (q as int) * 7 + (r as int));
            assert((q as int) == rust_div(ddays as int, 7));
            assert((r as int) == rust_rem(ddays as int, 7));
        }
        (q, r)
    } else {
        (0, ddays)
    };
    proof {
        assert(-(1_043_497i32) <= w32);
        assert(w32 <= 1_043_497i32);
        assert(-(7_304_484i32) <= dr32);
        assert(dr32 <= 7_304_484i32);
    }
    let s0: Span = Span::new();
    let s1: Span = s0.weeks(w32 as i64);
    let s2: Span = s1.days(dr32 as i64);
    proof {
        // the sign table of the two setter faces, case explicit (the
        // v==0 clauses keep an all-zero span zero; a nonzero lane
        // value sets or keeps the sign per the faces' tables), then
        // the div/rem factorization and the shared-unit fold.
        let dd: int = ddays as int;
        let w: int = w32 as int;
        let r: int = dr32 as int;
        assert(dd == 7 * w + r);
        if dd > 0 {
            if w > 0 {
                assert(s1.sign is Positive);
                if r > 0 {
                    assert(s2.sign is Positive);
                } else {
                    assert(!sp_all_zero(&s2));
                    assert(s2.sign is Positive);
                }
            } else {
                assert(w == 0);
                assert(sp_all_zero(&s1));
                assert(s1.sign is Zero);
                assert(s2.sign is Positive);
            }
            assert(s2.weeks as int == w);
            assert(s2.days as int == r);
            assert(!sp_all_zero(&s2));
            assert(sp_sign_val(s2.sign) == 1);
        } else {
            assert(dd < 0);
            if w < 0 {
                assert(s1.sign is Negative);
                if r < 0 {
                    assert(s2.sign is Negative);
                } else {
                    assert(!sp_all_zero(&s2));
                    assert(s2.sign is Negative);
                }
            } else {
                assert(w == 0);
                assert(sp_all_zero(&s1));
                assert(s1.sign is Zero);
                assert(s2.sign is Negative);
            }
            assert(s2.weeks as int == 0 - w);
            assert(s2.days as int == 0 - r);
            assert(!sp_all_zero(&s2));
            assert(sp_sign_val(s2.sign) == 0 - 1);
        }
        // The face's total conjunct follows from the branch-local
        // lane and sign claims above (the setter faces hold the
        // magnitudes; the sign cases fix the coefficient). No loud
        // coaching asserts: the nonlinear sv-product forms are the
        // postcheck's own route.
    }
    s2
}

/// The trunc anti-automorphism at the until/since divisors (rust_div
/// and rust_rem are the trunc twins, whose inlined if-shapes negate
/// exactly; the day-lane identities the since-face lanes consume).
proof fn rel_trunc_negates(t: int, d: int)
    requires
        d > 0,
    ensures
        rust_div(0 - t, d) == 0 - rust_div(t, d),
        rust_rem(0 - t, d) == 0 - rust_rem(t, d),
{
    if t > 0 {
        // the a < 0 arm of rust_div(-t, d) is -((t) / d), the
        // positive arm gives rust_div(t, d) == t / d -- negatives of
        // one another; same for the remainder pair.
        assert(rust_div(0 - t, d) == 0 - (t / d));
        assert(rust_div(t, d) == t / d);
        assert(rust_rem(0 - t, d) == 0 - (t % d));
        assert(rust_rem(t, d) == t % d);
    } else if t < 0 {
        let u: int = 0 - t;
        assert(u > 0);
        assert(rust_div(u, d) == u / d);
        assert(rust_rem(u, d) == u % d);
        assert(rust_div(t, d) == 0 - (u / d));
        assert(rust_rem(t, d) == 0 - (u % d));
    }
}

/// Origin Rust: pub fn since<A: Into<DateDifference>>(
///     self, other: A) -> Result<Span, Error>
///     (main-crate date.rs:1659-1670)
/// Upstream doc (date.rs:1636-1657, abridged):
///   This routine is identical to [Date::until], but the order of the
///   parameters is flipped.
/// Upstream body: `let span = -args.since_with_largest_unit(self)?;`
/// -- the negated until-span of the same pair.
pub exec fn rel_date_since_span(
    d1: Date,
    d2: Date,
    largest: Unit,
) -> (s: Span)
    requires
        valid_date(d1),
        valid_date(d2),
        largest is Day || largest is Week,
    ensures
        rel_date_since_face(d1, d2, largest, &s),
{
    let u: Span = rel_date_until_span(d1, d2, largest);
    let neg: Span = u.negate();
    proof {
        assert(neg == rel_span_negate_value(&u));
        let dds: int = ns_epoch_day_spec(
            d1.year as int,
            d1.month as int,
            d1.day as int,
        ) - ns_epoch_day_spec(
            d2.year as int,
            d2.month as int,
            d2.day as int,
        );
        // u is the until(d1 -> d2) span whose face-lanes live on
        // dd12 = -(dds); the anti-automorphism folds them onto the
        // since-lanes of dds.
        // the conjuncts of the since-face, spelled per sign case (the
        // lanes are the until-face magnitudes re-signed; the trunc
        // anti-automorphism carries the lane function through the
        // concrete coefficient once the branch fixes the sign).
        rel_trunc_negates(dds, 7);
        assert(sp_field_inv(&neg));
        assert(sp_zero_sign_ok(&neg));
        assert(sp_flags_ok(&neg));
        assert(neg.years == 0 && neg.months == 0);
        assert(neg.hours == 0 && neg.minutes == 0);
        assert(neg.seconds == 0 && neg.milliseconds == 0);
        assert(neg.microseconds == 0
            && neg.nanoseconds == 0);
        lemma_mul_unary_negation(
            sp_sign_val(u.sign),
            ((u.weeks as int) * 604_800 * 1_000_000_000)
                + ((u.days as int)
                    * 86_400 * 1_000_000_000),
        );
        assert(sp_inv_total_nanos(&neg)
            == 0 - sp_inv_total_nanos(&u));
        if dds > 0 {
            // u is Negative here (it is the d1 -> d2 span, and d2 is
            // BEFORE d1 in epoch terms... wait: dds > 0 means d1 is
            // the later date, so d1 -> d2 counts down) -- the negated
            // span is Positive with the same magnitudes, which is
            // exactly the since-face's Positive conjunct.
            assert(u.sign is Negative);
            assert((u.weeks as int)
                == rel_dur_weeks_lane(largest, dds));
            assert((u.days as int)
                == rel_dur_days_lane(largest, dds));
            assert(neg.sign is Positive);
            assert(sp_sign_val(neg.sign) == 1);
            assert((neg.weeks as int)
                == rel_dur_weeks_lane(largest, dds));
            assert((neg.days as int)
                == rel_dur_days_lane(largest, dds));
            assert(sp_inv_total_nanos(&neg)
                == dds * 86_400 * 1_000_000_000);
        } else if dds < 0 {
            assert(u.sign is Positive);
            assert((u.weeks as int)
                == 0 - rel_dur_weeks_lane(largest, dds));
            assert((u.days as int)
                == 0 - rel_dur_days_lane(largest, dds));
            assert(neg.sign is Negative);
            assert(sp_sign_val(neg.sign) == -1);
            assert((neg.weeks as int)
                == 0 - rel_dur_weeks_lane(largest, dds));
            assert((neg.days as int)
                == 0 - rel_dur_days_lane(largest, dds));
            assert(sp_inv_total_nanos(&neg)
                == dds * 86_400 * 1_000_000_000);
        }
    }
    neg
}


// ===========================================================================
// DateTime::checked_add_span (main-crate datetime.rs:1689-1712) -- the
// composed move model, then the four arms `(units.only_calendar() empty?
// units.only_time() empty?)` as their own exec fns (wall 46).
// ===========================================================================

/// The whole datetime-in-civil-nanoseconds value (the to_duration
/// total face, wrapper datetime.rs:2365-2374:
///     let mut dur = SignedDuration::from_civil_days32(
///         self.date().to_unix_epoch_day().day());
///     dur += self.time().to_duration();
/// -- the epoch-day leg rides the J7 forward twin, the time leg is the
/// J3 spec).
pub open spec fn rel_dt_total(dt: DateTime) -> int {
    ns_epoch_day_spec(
        dt.date.year as int,
        dt.date.month as int,
        dt.date.day as int,
    ) * S_CIVIL_DAY_SECS() * S_NANOS_PER_SEC()
        + time_nanos_spec(dt.time)
}

/// The shared move components of the DateTime span rhs: the calendar
/// march of the date part (identical lets to the Date face over
/// dt.date) PLUS the time part's day-carry (the overflowing_add Euclid
/// div at wrapper time.rs:1093, which checked_add_span's arms route
/// through). The time part does NOT fold into the date part here
/// (contrast the Date rhs face): it carries.
pub open spec fn rel_dt_move_parts(
    dt: DateTime,
    span: &Span,
) -> (int, int, int, int, int, int, int, int) {
    let sv: int = sp_sign_val(span.sign);
    let t_m: int = rel_months_move(dt.date, span);
    let m2: int = t_m % 12 + 1;
    let yc: int = (t_m - t_m % 12) / 12;
    let y1: int = (dt.date.year as int) + yc;
    let y2: int = y1 + sv * (span.years as int);
    let dcl: int = if (dt.date.day as int)
        > days_in_month_spec(y2, m2) {
        days_in_month_spec(y2, m2)
    } else {
        dt.date.day as int
    };
    let base: int = ns_epoch_day_spec(y2, m2, dcl);
    let wp7: int = sv * ((span.weeks as int) * 7);
    let dtoff: int = sv * (span.days as int);
    let ttot: int = time_nanos_spec(dt.time)
        + rel_time_total_nanos(span);
    let carry: int = ttot / nanos_per_civil_day();
    let remd: int = ttot % nanos_per_civil_day();
    let total: int = base + wp7 + dtoff + carry;
    (y1, y2, base, wp7, dtoff, carry, remd, total)
}

/// The gates of the DateTime span rhs: the b::Year chain (the same
/// two sequential checked adds, datetime.rs routes through Date
/// faces), the SpanDays gate on the time carry (the try_days?
/// of overflowing_add, wrapper time.rs:1095), and the three
/// sequential ued gates of the date march (weeks, days, carry).
pub open spec fn rel_dt_gates_ok(dt: DateTime, span: &Span) -> bool {
    let (y1, y2, base, wp7, dtoff, carry, remd, total) =
        rel_dt_move_parts(dt, span);
    year_iv().contains(y1)
        && year_iv().contains(y2)
        && -(7_304_484int) <= carry
        && carry <= 7_304_484
        && ued_iv().contains(base + wp7)
        && ued_iv().contains(base + wp7 + dtoff)
        && ued_iv().contains(total)
}

/// The shared result face of DateTime::checked_add_span over the Span
/// rhs: two-sided precision as on the Date face (the zero-span arm
/// carries the exact identity return; every other arrival is
/// twin-constructed with gates-ok).
pub open spec fn rel_dt_add_span_face(
    dt: DateTime,
    span: &Span,
    r: &Option<DateTime>,
) -> bool {
    let (y1, y2, base, wp7, dtoff, carry, remd, total) =
        rel_dt_move_parts(dt, span);
    match r {
        Option::Some(dt2) =>
            // Light gates on the Some-side: the year gates and the
            // total containment (the machine Some-paths establish
            // these cheaply; the full gates conjunct stays on the
            // None-side and in the operator requires).
            (sp_all_zero(span) ==> (dt2 == dt))
                && (!sp_all_zero(span)
                    ==> (year_iv().contains(y1)
                        && year_iv().contains(y2)
                        && ued_iv().contains(total)
                        && dt2.time
                            == spec_time_from_nanosecond(remd)
                        && (dt2.date.year as int)
                            == ns_civil_year(total)
                        && (dt2.date.month as int)
                            == ns_civil_month(total)
                        && (dt2.date.day as int)
                            == ns_civil_day(total))),
        Option::None =>
            !sp_all_zero(span) && !rel_dt_gates_ok(dt, span),
    }
}

/// Origin Rust: pub fn overflowing_add(self, span: &Span)
///     -> Result<(Time, Span), Error> (wrapper time.rs:1082-1098)
/// Upstream doc (:1071-1080, abridged):
///   Adds the given span to the this time value, and returns the
///   resulting time with any overflowing amount in the span returned.
/// Body (wrapper time.rs:1086-1097; the J8 reunion pruned face
/// discarded the carry -- the DateTime arms this batch needs it):
///     if let Some(err) = span.smallest_non_time_non_zero_unit_error()
///         { return Err(err); }
///     let span = span.to_invariant_duration().as_nanos();
///     let time = i128::from(self.to_nanosecond());
///     let sum = span + time;
///     let days = sum.div_euclid(i128::from(c::NANOS_PER_CIVIL_DAY)) as i64;
///     let rem = sum.rem_euclid(i128::from(c::NANOS_PER_CIVIL_DAY)) as i64;
///     let span = Span::new().try_days(days)?;
///     Ok((Time::from_nanosecond(rem).unwrap(), span))
/// (The first gate is the time-only requires; the div_euclid /
///  rem_euclid pair at i128 has no vstd spec in this build -- the std
///  E0283-excluded `rem_euclid` family -- so the Euclid pair is
///  materialized from the machine trunc pair by the sign fold below,
///  value-identically.)
fn rel_time_overflowing_add_carry(
    t: Time,
    span: &Span,
) -> (r: Option<(Time, Span)>)
    requires
        valid_time(t),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        span.years == 0,
        span.months == 0,
        span.weeks == 0,
        span.days == 0,
    ensures
        ({
            let ttot: int = time_nanos_spec(t)
                + rel_time_total_nanos(span);
            let carry: int = ttot / nanos_per_civil_day();
            match r {
                Option::Some((t2, car)) =>
                    carry >= -(7_304_484int)
                        && carry <= 7_304_484
                        && (carry > 0
                            ==> (car.sign is Positive
                                && (car.days as int) == carry))
                        && (carry < 0
                            ==> (car.sign is Negative
                                && (car.days as int)
                                    == 0 - carry))
                        && (carry == 0
                            ==> (car.sign is Zero
                                && car.days == 0))
                        && car.years == 0
                        && car.months == 0
                        && car.weeks == 0
                        && car.hours == 0
                        && car.minutes == 0
                        && car.seconds == 0
                        && car.milliseconds == 0
                        && car.microseconds == 0
                        && car.nanoseconds == 0
                        && sp_field_inv(&car)
                        && sp_zero_sign_ok(&car)
                        && sp_flags_ok(&car)
                        && t2
                            == spec_time_from_nanosecond(
                                ttot
                                    % nanos_per_civil_day(),
                            )
                        && valid_time(t2),
                Option::None =>
                    !(carry >= -(7_304_484int)
                        && carry <= 7_304_484),
            }
        })
{
    let d: SignedDuration = span.sp_to_invariant_duration();
    let nn_wide: i128 = d.as_nanos();
    let t_wide: i128 = t.to_nanosecond().nanosecond as i128;
    let sum: i128 = nn_wide + t_wide;
    let q_t: i128 = sum / 86_400_000_000_000i128;
    let r_t: i128 = sum % 86_400_000_000_000i128;
    proof {
        // the trunc pair of the machine division is the rust pair at
        // int; the Euclid pair follows by the one-step sign fold.
        let s: int = sum as int;
        let dq: int = q_t as int;
        let dr: int = r_t as int;
        lemma_fundamental_div_mod(s, 86_400_000_000_000);
        assert(s == dq * 86_400_000_000_000 + dr);
        assert((dq as int) == rust_div(s, 86_400_000_000_000));
        assert((dr as int) == rust_rem(s, 86_400_000_000_000));
    }
    proof {
        // the time-lane linear bound (each magnitude within its
        // b::Span range by sp_field_inv): the five whole-second lanes
        // are at most ~6.3e14 seconds each and the nanos lane at most
        // ~9.2e18 nanos, so the summed total is under 3.3e21 ns and
        // the carry under 38.2M days -- far inside i64, and possibly
        // outside b::SpanDays (the genuine try_days error arm below).
        let sv: int = sp_sign_val(span.sign);
        assert(sv >= -1 && sv <= 1);
        assert(0 <= time_nanos_spec(t));
        assert(time_nanos_spec(t)
            < 86_400_000_000_000int);
        let hs: int = (span.hours as int);
        let mi: int = (span.minutes as int);
        let se: int = (span.seconds as int);
        let ms: int = (span.milliseconds as int);
        let us: int = (span.microseconds as int);
        let ns: int = (span.nanoseconds as int);
        assert(-(175_307_616int) <= hs
            && hs <= 175_307_616int);
        assert(-(10_518_456_960int) <= mi
            && mi <= 10_518_456_960int);
        assert(-(631_107_417_600int) <= se
            && se <= 631_107_417_600int);
        assert(-(631_107_417_600_000int) <= ms
            && ms <= 631_107_417_600_000int);
        assert(-(631_107_417_600_000_000int) <= us
            && us <= 631_107_417_600_000_000int);
        assert(-(9_223_372_036_854_775_807int) <= ns
            && ns <= 9_223_372_036_854_775_807int);
        let magh: int = 631_107_417_600int;
        let magl: int = magh * 1_000_000_000;
        let tt: int = time_nanos_spec(t)
            + rel_time_total_nanos(span);
        assert((hs * 3_600 * 1_000_000_000)
            <= 631_107_417_600int * 1_000_000_000);
        let lanes: int = hs * 3_600 * 1_000_000_000
            + mi * 60 * 1_000_000_000
            + se * 1_000_000_000
            + ms * 1_000_000
            + us * 1_000
            + ns;
        // per-lane monotone pieces then the folded sum:
        assert(hs * 3_600 * 1_000_000_000
            <= 631_107_417_600int * 1_000_000_000);
        assert(mi * 60 * 1_000_000_000
            <= 631_107_417_600int * 1_000_000_000);
        assert(se * 1_000_000_000
            <= 631_107_417_600int * 1_000_000_000);
        assert(ms * 1_000_000
            <= 631_107_417_600int * 1_000_000_000);
        assert(us * 1_000
            <= 631_107_417_600int * 1_000_000_000);
        assert(lanes
            <= (5 * 631_107_417_600int
                + 9_300_000_000int) * 1_000_000_000);
        assert(lanes
            >= -((5 * 631_107_417_600int
                + 9_300_000_000int) * 1_000_000_000));
        // sv is a symbolic sign value: the product sv * lanes is a
        // NONLINEAR term until the sign case is fixed, so the
        // magnitude claim is made per case (the multiplication folds
        // to a literal coefficient inside each branch).
        if sv == 1 {
            assert(sv * lanes == lanes);
            assert((5 * 631_107_417_600int
                + 9_300_000_000int) * 1_000_000_000
                >= lanes);
        } else if sv == -1 {
            assert(sv == 0 - 1);
            assert((0 - 1) * lanes == 0 - lanes);
            assert(sv * lanes == 0 - lanes);
            assert((5 * 631_107_417_600int
                + 9_300_000_000int) * 1_000_000_000
                >= 0 - lanes);
        } else {
            assert(sv == 0);
            assert(sv * lanes == 0);
        }
        assert(sv * lanes
            <= (5 * 631_107_417_600int
                + 9_300_000_000int) * 1_000_000_000);
        assert(sv * lanes
            >= -((5 * 631_107_417_600int
                + 9_300_000_000int) * 1_000_000_000));
        assert(-(3_300_000_000_000_000_000_000int) <= tt);
        assert(tt <= 3_300_000_000_000_000_000_000int);
        assert((sum as int) == tt);
        assert((q_t as int)
            == rust_div(tt, 86_400_000_000_000));
        assert(-(38_200_000int) <= q_t as int);
        assert(q_t as int <= 38_200_000int);
    }
    let carry: i64 = if r_t < 0 {
        let c: i128 = q_t - 1i128;
        proof {
            assert(-(38_200_000i128) <= c);
            assert(c <= 38_200_000i128);
        }
        c as i64
    } else {
        proof {
            assert(-(38_200_000i128) <= q_t);
            assert(q_t <= 38_200_000i128);
        }
        q_t as i64
    };
    let remd: i64 = if r_t < 0 {
        let m: i128 = r_t + 86_400_000_000_000i128;
        m as i64
    } else {
        r_t as i64
    };
    proof {
        // the Euclid carry/remd pair, at int:
        let s: int = sum as int;
        let carry_i: int = carry as int;
        let remd_i: int = remd as int;
        let dq2: int = q_t as int;
        let dr2: int = r_t as int;
        assert(s == dq2 * 86_400_000_000_000 + dr2);
        // the branch-wise pair facts (the sign fold positions), then
        // the composed Euclid pair:
        if r_t < 0 {
            // div_euclid folds the negative trunc remainder DOWN one
            // quotient step (remd picks a full civil day up):
            //     t == (q - 1)*D + (r + D).
            assert(carry_i == dq2 - 1);
            assert(remd_i == dr2 + 86_400_000_000_000);
            assert((dq2 - 1) * 86_400_000_000_000
                + (dr2 + 86_400_000_000_000)
                == dq2 * 86_400_000_000_000 + dr2);
        } else {
            assert(carry_i == dq2);
            assert(remd_i == dr2);
        }
        assert(0 <= remd_i);
        assert(remd_i < 86_400_000_000_000);
        assert(s == carry_i * 86_400_000_000_000 + remd_i);
        assert(carry_i == s / 86_400_000_000_000);
        assert(remd_i == s % 86_400_000_000_000);
        // the ttot relay: the span leg is the invariant time total.
        assert(s == time_nanos_spec(t)
            + rel_time_total_nanos(span));
    }
    let s0: Span = Span::new();
    let car_opt: Option<Span> = s0.try_days(carry);
    match car_opt {
        Option::None => {
            proof {
                assert(!(carry >= -(7_304_484int)
                    && carry <= 7_304_484));
            }
            Option::None
        }
        Option::Some(car) => {
            let t2o: Option<Time> =
                crate::time::Time::from_nanosecond(remd);
            match t2o {
                Option::Some(t2) => Option::Some((t2, car)),
                Option::None => {
                    // Dead arm: remd sits inside the civil-day window
                    // by the Euclid fold above, and from_nanosecond's
                    // Some face is exactly the window.
                    proof { assert(false); }
                    Option::None
                }
            }
        }
    }
}

/// The J3 to_nanosecond roundtrip, as a local proof twin of the J8
/// reunion face (jcore_span_reunion::lemma_time_roundtrip): the j9
/// driver no longer mounts the reunion panel (its budget-sensitive
/// property theorems live green on their home j8 driver, J9 pitfall
/// 59), so this file carries the two faces it consumes as locally
/// verified twins.
proof fn rel_lemma_time_roundtrip(t: Time)
    requires
        valid_time(t),
    ensures
        t == spec_time_from_nanosecond(
            crate::time::time_nanos_spec(t)),
{
    // The spec twin decomposes n as s * 1e9 + sub (s = n / 1e9
    // Euclid) then folds s through the hour/minute/second chain --
    // the J3 harness prop roundtrip pair, restated here locally.
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

/// The calendar-only arm of DateTime::checked_add_span
/// (datetime.rs:1695-1700: `units.only_calendar()` non-empty,
/// `units.only_time()` empty):
///     let new_date = old_date.checked_add(span)?;
///     Ok(DateTime::from_parts(new_date, old_time))
/// -- the span has zero time fields, so the Date face's time fold is
/// zero and this arm relays the Date entry exactly (with the time
/// part untouched through the J3 roundtrip lemma).
fn rel_dt_add_cal_only(
    dt: DateTime,
    span: &Span,
) -> (r: Option<DateTime>)
    requires
        valid_datetime(dt),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        span.hours == 0,
        span.minutes == 0,
        span.seconds == 0,
        span.milliseconds == 0,
        span.microseconds == 0,
        span.nanoseconds == 0,
    ensures
        rel_dt_add_span_face(dt, span, &r),
{
    proof {
        if span.sign is Zero {
            assert(sp_sign_val(span.sign) == 0);
        } else if span.sign is Positive {
            assert(sp_sign_val(span.sign) == 1);
        } else {
            assert(sp_sign_val(span.sign) == 0 - 1);
        }
        assert(rel_time_total_nanos(span) == 0);
        let (y1, y2, base, wp7, dtoff, carry, remd, total) =
            rel_dt_move_parts(dt, span);
        assert(carry == 0);
        assert(remd == time_nanos_spec(dt.time));
        rel_lemma_time_roundtrip(dt.time);
    }
    let d2o: Option<Date> =
        rel_date_checked_add_span(&dt.date, span);
    match d2o {
        Option::Some(d2) => {
            let dt2: DateTime =
                DateTime::from_parts(d2, dt.time);
            Option::Some(dt2)
        }
        Option::None => {
            proof {
                assert(!rel_dt_gates_ok(dt, span));
            }
            Option::None
        }
    }
}

/// The time-only arm of DateTime::checked_add_span
/// (datetime.rs:1701-1709: `units.only_calendar()` empty,
/// `units.only_time()` non-empty):
///     let (new_time, leftovers) = old_time.overflowing_add(span)
///         .context(E::FailedAddSpanTime)?;
///     let new_date = old_date.checked_add(leftovers)
///         .context(E::FailedAddSpanOverflowing)?;
///     Ok(DateTime::from_parts(new_date, new_time))
/// The day-carry link: from the carry-helper's magnitude/sign face to
/// the signed product the dt-move parts use (the sv product fixed per
/// sign case, the basics/unary lemmas spelling the coefficients).
proof fn rel_lemma_day_carry_link(
    car: &Span,
    carry: int,
)
    requires
        sp_field_inv(car),
        (carry > 0
            ==> (car.sign is Positive
                && (car.days as int) == carry)),
        (carry < 0
            ==> (car.sign is Negative
                && (car.days as int) == 0 - carry)),
        (carry == 0
            ==> (car.sign is Zero && car.days == 0)),
    ensures
        sp_sign_val(car.sign) * (car.days as int)
            == carry,
{
    if carry > 0 {
        assert(sp_sign_val(car.sign) == 1);
        lemma_mul_basics(carry);
        assert(1 * (car.days as int) == (car.days as int));
    } else if carry < 0 {
        assert(sp_sign_val(car.sign) == 0 - 1);
        assert((car.days as int) == 0 - carry);
        lemma_mul_unary_negation(1, (car.days as int));
        lemma_mul_basics(0 - carry);
    } else {
        assert(carry == 0);
        assert(sp_sign_val(car.sign) == 0);
        lemma_mul_basics(0);
    }
}

/// The time-only collapse of the dt move parts (the offloaded
/// machinery proof: calendar zeros collapse the parts to the anchor).
proof fn rel_lemma_dt_timeonly_collapse(
    dt: DateTime,
    span: &Span,
    anchor: int,
)
    requires
        valid_datetime(dt),
        sp_field_inv(span),
        span.years == 0,
        span.months == 0,
        span.weeks == 0,
        span.days == 0,
        anchor
            == ns_epoch_day_spec(
                dt.date.year as int,
                dt.date.month as int,
                dt.date.day as int,
            ),
        ued_iv().contains(anchor),
    ensures
        ({
            let (y1, y2, base, wp7, dtoff, carry, remd, total) =
                rel_dt_move_parts(dt, span);
            &&& y1 == (dt.date.year as int)
            &&& y2 == (dt.date.year as int)
            &&& base == anchor
            &&& wp7 == 0
            &&& dtoff == 0
            &&& total == base + carry
        })
{
    // month machinery identity + valid clamp + zero calendar adds;
    // the time side stays symbolic (carry / remd drive the arm).
}

// The first draft's external-contract form here is resolved the same
// way as the Date tails: with `!sp_all_zero` pinned in the requires
// (the dt entry's dispatch routes the all-zero span to its identity
// return before this arm), the twin-face folds close from the
// caller-conjured parts conjunct plus the day-carry link lemma within
// the batch rlimit.
fn rel_dt_timeonly_move(
    dt: DateTime,
    span: &Span,
    base: &UnixEpochDay,
    t2: Time,
    car: &Span,
) -> (r: Option<DateTime>)
    requires
        valid_datetime(dt),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
        span.years == 0,
        span.months == 0,
        span.weeks == 0,
        span.days == 0,
        sp_field_inv(car),
        sp_zero_sign_ok(car),
        sp_flags_ok(car),
        car.years == 0,
        car.months == 0,
        car.weeks == 0,
        car.hours == 0,
        car.minutes == 0,
        car.seconds == 0,
        car.milliseconds == 0,
        car.microseconds == 0,
        car.nanoseconds == 0,
        ({
            let (y1, y2, basep, wp7, dtoff, carry, remd, total) =
                rel_dt_move_parts(dt, span);
            (basep == base.day as int)
                && (t2
                    == spec_time_from_nanosecond(remd))
                && (carry > 0
                    ==> (car.sign is Positive
                        && (car.days as int) == carry))
                && (carry < 0
                    ==> (car.sign is Negative
                        && (car.days as int) == 0 - carry))
                && (carry == 0
                    ==> (car.sign is Zero
                        && car.days == 0))
        }),
    ensures
        rel_dt_add_span_face(dt, span, &r),
{
    let gcar: i32 = car.get_days();
    proof {
        let (y1, y2, basep, wp7, dtoffp, carryp,
            remdp, totalp) =
            rel_dt_move_parts(dt, span);
        rel_lemma_day_carry_link(car, carryp);
        assert((gcar as int)
            == sp_sign_val(car.sign) * (car.days as int));
    }
    let moved: Option<UnixEpochDay> =
        base.checked_add(gcar);
    match moved {
        Option::Some(e2) => {
            proof {
                // the calendar fields are zero this arm, so with the
                // span sign case FIXED per branch (pitfall 52) the
                // sv products collapse and total is the anchor plus
                // the day carry (the face's year rows then ride the
                // valid_datetime bounds and the pins ride e2).
                if span.sign is Zero {
                    assert(sp_sign_val(span.sign) == 0);
                } else if span.sign is Positive {
                    assert(sp_sign_val(span.sign) == 1);
                } else {
                    assert(sp_sign_val(span.sign) == 0 - 1);
                }
                let (y1, y2, basep, wp7, dtoffp,
                    carryp, remdp, totalp) =
                    rel_dt_move_parts(dt, span);
                assert(wp7 == 0);
                assert(dtoffp == 0);
                assert(totalp == basep + carryp);
                rel_lemma_day_carry_link(car, carryp);
                assert((e2.day as int) == basep + carryp);
                assert((e2.day as int) == totalp);
                assert(year_iv().contains(y1));
                assert(year_iv().contains(y2));
            }
            let d2: Date = e2.to_date_ns();
            let dt2: DateTime = DateTime::from_parts(d2, t2);
            Option::Some(dt2)
        }
        Option::None => {
            proof {
                // same zero-fields collapse as the Some arm: total is
                // the anchor plus the carry, so the checked_add None
                // face fails the gates' final containment conjunct.
                if span.sign is Zero {
                    assert(sp_sign_val(span.sign) == 0);
                } else if span.sign is Positive {
                    assert(sp_sign_val(span.sign) == 1);
                } else {
                    assert(sp_sign_val(span.sign) == 0 - 1);
                }
                let (y1, y2, basep, wp7, dtoffp,
                    carryp, remdp, totalp) =
                    rel_dt_move_parts(dt, span);
                assert(wp7 == 0);
                assert(dtoffp == 0);
                assert(totalp == basep + carryp);
                rel_lemma_day_carry_link(car, carryp);
                assert(!(ued_iv().contains(basep + carryp)));
                assert(!rel_dt_gates_ok(dt, span));
            }
            Option::None
        }
    }
}

fn rel_dt_add_time_only(
    dt: DateTime,
    span: &Span,
) -> (r: Option<DateTime>)
    requires
        valid_datetime(dt),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        !sp_all_zero(span),
        span.years == 0,
        span.months == 0,
        span.weeks == 0,
        span.days == 0,
    ensures
        rel_dt_add_span_face(dt, span, &r),
{
    let base: UnixEpochDay = dt.date.to_unix_epoch_day_ns();
    proof {
        rel_lemma_dt_timeonly_collapse(
            dt, span, base.day as int);
    }
    let co: Option<(Time, Span)> =
        rel_time_overflowing_add_carry(dt.time, span);
    match co {
        Option::None => {
            proof {
                let (y1, y2, basep, wp7, dtoffp, carryp,
                    remdp, totalp) =
                    rel_dt_move_parts(dt, span);
                assert(basep == base.day as int);
                assert(!(carryp >= -(7_304_484int)
                    && carryp <= 7_304_484));
                assert(!rel_dt_gates_ok(dt, span));
            }
            Option::None
        }
        Option::Some((t2, car)) => {
            rel_dt_timeonly_move(dt, span, &base, t2, &car)
        }
    }
}

/// The to_distance move parts of the general arm's DATED march (the
/// calendar half after the without_lower(Day) surgery; the carry rides
/// separately).
pub open spec fn rel_cal_parts(
    d: Date,
    sdp: &Span,
) -> (int, int, int, int, int) {
    let sv: int = sp_sign_val(sdp.sign);
    let t_m: int = rel_months_move(d, sdp);
    let m2: int = t_m % 12 + 1;
    let yc: int = (t_m - t_m % 12) / 12;
    let y1: int = (d.year as int) + yc;
    let y2: int = y1 + sv * (sdp.years as int);
    let dcl: int = if (d.day as int)
        > days_in_month_spec(y2, m2) {
        days_in_month_spec(y2, m2)
    } else {
        d.day as int
    };
    let base: int = ns_epoch_day_spec(y2, m2, dcl);
    let wp7: int = sv * ((sdp.weeks as int) * 7);
    let dtoff: int = sv * (sdp.days as int);
    (y1, y2, base, wp7, dtoff)
}

/// The general arm's dated march (datetime.rs:1716-1729's two adds,
/// at UED level so the composed carry arrives without the arriving
/// date's validity -- the intermediate date is twin-constructed and
/// its valid_date fact rides the deferred NS reverse family, so the
/// match is stated on the epoch component):
///     span_date = span.without_lower(Unit::Day);
///     let new_date = old_date.checked_add(&span_date)?;
///     let new_date = new_date.checked_add(&leftovers)?;
fn rel_dt_general_cal_move(
    d: &Date,
    sdp: &Span,
    car: &Span,
) -> (r: Option<UnixEpochDay>)
    requires
        valid_date(*d),
        sp_field_inv(sdp),
        sp_zero_sign_ok(sdp),
        sp_flags_ok(sdp),
        sp_field_inv(car),
        sp_zero_sign_ok(car),
        sp_flags_ok(car),
        sdp.hours == 0,
        sdp.minutes == 0,
        sdp.seconds == 0,
        sdp.milliseconds == 0,
        sdp.microseconds == 0,
        sdp.nanoseconds == 0,
        car.years == 0,
        car.months == 0,
        car.weeks == 0,
        car.hours == 0,
        car.minutes == 0,
        car.seconds == 0,
        car.milliseconds == 0,
        car.microseconds == 0,
        car.nanoseconds == 0,
    ensures
        ({
            let (y1, y2, base, wp7, dtoff) =
                rel_cal_parts(*d, sdp);
            let carry: int =
                (sp_sign_val(car.sign)) * (car.days as int);
            match r {
                Option::Some(e) =>
                    year_iv().contains(y1)
                        && year_iv().contains(y2)
                        && ued_iv().contains(base + wp7)
                        && ued_iv().contains(base + wp7 + dtoff)
                        && ued_iv().contains(
                            base + wp7 + dtoff + carry)
                        && (e.day as int)
                            == base + wp7 + dtoff + carry,
                Option::None =>
                    !(year_iv().contains(y1)
                        && year_iv().contains(y2)
                        && ued_iv().contains(base + wp7)
                        && ued_iv().contains(base + wp7 + dtoff)
                        && ued_iv().contains(
                            base + wp7 + dtoff + carry)),
            }
        })
{
    let gm: i32 = sdp.get_months();
    let (ml, yl) = month_add_overflowing(d.month, gm);
    proof {
        let sv: int = sp_sign_val(sdp.sign);
        let t_m: int = (d.month as int) - 1 + (gm as int);
        assert((gm as int) == sv * (sdp.months as int));
        assert(t_m == rel_months_move(*d, sdp));
        assert((ml as int) == t_m % 12 + 1);
        lemma_month_carry_bridge(t_m, yl as int, ml as int);
    }
    let y1o: Option<i16> = Year::checked_add(d.year, yl);
    let y1: i16 = match y1o {
        Option::Some(v) => v,
        Option::None => return Option::None,
    };
    let gy: i16 = sdp.get_years();
    proof {
        let sv: int = sp_sign_val(sdp.sign);
        assert((gy as int) == sv * (sdp.years as int));
    }
    let y2o: Option<i16> = Year::checked_add(y1, gy);
    let y2: i16 = match y2o {
        Option::Some(v) => v,
        Option::None => return Option::None,
    };
    let dco: Option<Date> = Date::new_constrain(y2, ml, d.day);
    let dc: Date = match dco {
        Option::Some(v) => v,
        Option::None => {
            proof {
                assert(year_iv().contains(y2 as int));
                assert(1 <= ml as int && ml as int <= 12);
                assert(1 <= d.day as int);
                assert(false);
            }
            return Option::None;
        }
    };
    let base: UnixEpochDay = dc.to_unix_epoch_day_ns();
    let gw: i32 = sdp.get_weeks();
    proof {
        let sv: int = sp_sign_val(sdp.sign);
        assert((gw as int) == sv * (sdp.weeks as int));
        assert(-(1_043_497i32) <= gw);
        assert(gw <= 1_043_497i32);
    }
    let w7: i32 = 7 * gw;
    let u2o: Option<UnixEpochDay> = base.checked_add(w7);
    let u2: UnixEpochDay = match u2o {
        Option::Some(v) => v,
        Option::None => return Option::None,
    };
    let gd: i32 = sdp.get_days();
    proof {
        let sv: int = sp_sign_val(sdp.sign);
        assert((gd as int) == sv * (sdp.days as int));
    }
    let u3o: Option<UnixEpochDay> = u2.checked_add(gd);
    let u3: UnixEpochDay = match u3o {
        Option::Some(v) => v,
        Option::None => return Option::None,
    };
    let gcar: i32 = car.get_days();
    let u4o: Option<UnixEpochDay> = u3.checked_add(gcar);
    match u4o {
        Option::Some(e4) => {
            proof {
                let (y1p, y2p, basep, wp7p, dtoffp) =
                    rel_cal_parts(*d, sdp);
                assert((e4.day as int)
                    == basep + wp7p + dtoffp + gcar as int);
            }
            Option::Some(e4)
        }
        Option::None => Option::None,
    }
}

/// The general arm of DateTime::checked_add_span
/// (datetime.rs:1692-1712 the (false, false) case -> checked_add_
/// span_general :1716-1729):
///     let span_date = span.without_lower(Unit::Day);
///     let span_time = span.only_lower(Unit::Day);
///     let (new_time, leftovers) = old_time.overflowing_add(&span_time)?;
///     let new_date = old_date.checked_add(&span_date)?;
///     let new_date = new_date.checked_add(&leftovers)?;
///     Ok(DateTime::from_parts(new_date, new_time))
/// The span surgery (span.rs:2805-2872) is the J5 setter chain below
/// (only_lower zeroes Day..Year through the panicking setters with
/// value 0; without_lower zeroes Nanosecond..Hour): every setter face
/// passes the other nine fields through, so the halves keep the
/// original sign (each half is non-zero on this arm's domain).
fn rel_dt_add_general(
    dt: DateTime,
    span: &Span,
) -> (r: Option<DateTime>)
    requires
        valid_datetime(dt),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        (span.years != 0 || span.months != 0
            || span.weeks != 0 || span.days != 0)
            && (span.hours != 0 || span.minutes != 0
                || span.seconds != 0
                || span.milliseconds != 0
                || span.microseconds != 0
                || span.nanoseconds != 0),
    ensures
        rel_dt_add_span_face(dt, span, &r),
{
    // span_date = span.without_lower(Unit::Day) (span.rs:2841-2872).
    let s1: Span = span.nanoseconds(0);
    let s2: Span = s1.microseconds(0);
    let s3: Span = s2.milliseconds(0);
    let s4: Span = s3.seconds(0);
    let s5: Span = s4.minutes(0);
    let sd_span: Span = s5.hours(0);
    // span_time = span.only_lower(Unit::Day) (span.rs:2805-2836).
    let t1: Span = span.days(0);
    let t2: Span = t1.weeks(0);
    let t3: Span = t2.months(0);
    let st_span: Span = t3.years(0);
    proof {
        // the surgery keeps the calendar half of sd_span and the
        // time half of st_span identical to the original span (the
        // J5 setter faces pass the untouched fields through), and
        // both halves keep the span-global sign since each half is
        // non-zero here.
        let sv: int = sp_sign_val(span.sign);
        assert(sd_span.sign == span.sign);
        assert(st_span.sign == span.sign);
        assert((sd_span.years as int) == (span.years as int));
        assert((sd_span.months as int) == (span.months as int));
        assert((sd_span.weeks as int) == (span.weeks as int));
        assert((sd_span.days as int) == (span.days as int));
        assert(st_span.hours == span.hours);
        assert(st_span.minutes == span.minutes);
        assert(st_span.seconds == span.seconds);
        assert(st_span.milliseconds == span.milliseconds);
        assert(st_span.microseconds == span.microseconds);
        assert(st_span.nanoseconds == span.nanoseconds);
        assert(rel_time_total_nanos(&st_span)
            == rel_time_total_nanos(span));
    }
    let co: Option<(Time, Span)> =
        rel_time_overflowing_add_carry(dt.time, &st_span);
    proof {
        // the surgery bridge, asserted once: the calendar half's
        // parts are the dt-move parts (same the signs/sv; the time
        // half's total rides through st_span), and the day-carry
        // link lemma fixes the car product.
        let (y1, y2, basep, wp7, dtoff, carry, remd, total) =
            rel_dt_move_parts(dt, span);
        let (y1c, y2c, basec, wp7c, dtoffc) =
            rel_cal_parts(dt.date, &sd_span);
        assert(y1 == y1c);
        assert(y2 == y2c);
        assert(basep == basec);
        assert(wp7 == wp7c);
        assert(dtoff == dtoffc);
        let scarry: int =
            (time_nanos_spec(dt.time)
                + rel_time_total_nanos(&st_span))
                / nanos_per_civil_day();
        assert(carry == scarry);
    }
    match co {
        Option::None => {
            proof {
                let (y1, y2, basep, wp7, dtoff, carry, remd, total) =
                    rel_dt_move_parts(dt, span);
                assert(!(carry >= -(7_304_484int)
                    && carry <= 7_304_484));
                assert(!rel_dt_gates_ok(dt, span));
            }
            Option::None
        }
        Option::Some((t2r, car)) => {
            proof {
                let (y1, y2, basep, wp7, dtoff, carry, remd, total) =
                    rel_dt_move_parts(dt, span);
                rel_lemma_day_carry_link(&car, carry);
                assert(carry >= -(7_304_484int));
                assert(carry <= 7_304_484);
            }
            let uo: Option<UnixEpochDay> =
                rel_dt_general_cal_move(
                    &dt.date, &sd_span, &car);
            match uo {
                Option::None => {
                    proof {
                        let (y1, y2, basep, wp7, dtoff, carry,
                            remd, total) =
                            rel_dt_move_parts(dt, span);
                        rel_lemma_day_carry_link(&car, carry);
                        assert(!rel_dt_gates_ok(dt, span));
                    }
                    Option::None
                }
                Option::Some(e4) => {
                    let d2: Date = e4.to_date_ns();
                    let dt2: DateTime =
                        DateTime::from_parts(d2, t2r);
                    proof {
                        let (y1, y2, basep, wp7, dtoff, carry,
                            remd, total) =
                            rel_dt_move_parts(dt, span);
                        rel_lemma_day_carry_link(&car, carry);
                        assert((e4.day as int) == total);
                        assert(ued_iv().contains(e4.day as int));
                        assert(rel_dt_gates_ok(dt, span));
                    }
                    Option::Some(dt2)
                }
            }
        }
    }
}

/// Origin Rust: fn checked_add_span(self, span: &Span)
///     -> Result<DateTime, Error> (datetime.rs:1689-1712)
/// Upstream body (:1692-1712): the four-case units dispatch
///     match (units.only_calendar().is_empty(),
///            units.only_time().is_empty()) {
///         (true, true) => Ok(self),
///         (false, true) => ... the calendar arm,
///         (true, false) => ... the time arm,
///         (false, false) => self.checked_add_span_general(span),
///     }
/// (The public DateTime::checked_add at :1680-1686 routes here through
///  DateTimeArithmetic; the zero case upstream is the sign-based
///  is_zero, transcribed on the field disjunction so the identity arm
///  lands exactly on the face's sp_all_zero slot, like the Date
///  entry's zero test.)
pub exec fn rel_dt_checked_add_span(
    dt: DateTime,
    span: &Span,
) -> (r: Option<DateTime>)
    requires
        valid_datetime(dt),
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
    ensures
        rel_dt_add_span_face(dt, span, &r),
{
    let cal_nonzero: bool = span.years != 0
        || span.months != 0
        || span.weeks != 0
        || span.days != 0;
    let time_nonzero: bool = span.hours != 0
        || span.minutes != 0
        || span.seconds != 0
        || span.milliseconds != 0
        || span.microseconds != 0
        || span.nanoseconds != 0;
    // is_zero spelled over the same field disjunctions (the two flag
    // faces agree under sp_flags_ok), so the arm guards below carry
    // the (cal_nonzero && time_nonzero) side condition into the
    // general arm's requires.
    if !cal_nonzero && !time_nonzero {
        return Option::Some(dt);
    } else if cal_nonzero && !time_nonzero {
        rel_dt_add_cal_only(dt, span)
    } else if !cal_nonzero && time_nonzero {
        rel_dt_add_time_only(dt, span)
    } else {
        rel_dt_add_general(dt, span)
    }
}

// ===========================================================================
// DateTime::until / since (main-crate datetime.rs:1995-2043) in the
// default configuration (DateTimeDifference::new: Trunc, smallest
// Nanosecond, no rounding; largest defaults to
// smallest.max(Unit::Day) = Day, datetime.rs:3270-3273), and the
// to_duration backbone (datetime.rs:2365-2374).
// ===========================================================================

/// Origin Rust: pub(crate) fn to_duration(&self) -> SignedDuration
///     (wrapper time.rs:1695-1697) -- a local exec twin of the J8
/// reunion face (jcore_span_reunion::time_to_duration), verified
/// here because the j9 driver mounts panels without the reunion
/// file (see the roundtrip twin above for the same disposition).
/// Upstream body: SignedDuration::from_nanos(self.to_nanosecond()).
fn rel_time_to_duration(t: Time) -> (d: SignedDuration)
    requires
        valid_time(t),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d) == crate::time::time_nanos_spec(t),
{
    SignedDuration::from_nanos(t.to_nanosecond().nanosecond)
}

/// Origin Rust: fn to_duration(self) -> SignedDuration
///     (datetime.rs:2368-2374; "Converts this datetime to a
/// nanosecond timestamp assuming a Zulu time zone offset and where
/// all days are exactly 24 hours long.")
pub exec fn rel_dt_to_duration(dt: DateTime) -> (d: SignedDuration)
    requires
        valid_datetime(dt),
    ensures
        sd_inv(&d),
        sd_total_nanos(&d) == rel_dt_total(dt),
        // the civil-datetime window (the ued anchor this batch's
        // fits/downstream faces consume): every valid datetime's
        // to_duration total sits inside the 7,304,483-day ledger.
        (-(4_371_587int))
            * nanos_per_civil_day()
            <= sd_total_nanos(&d),
        sd_total_nanos(&d)
            < (2_932_897int) * nanos_per_civil_day(),
{
    let epd: UnixEpochDay = dt.date.to_unix_epoch_day_ns();
    let d1: SignedDuration = sd_from_civil_days32(epd.day);
    let d2: SignedDuration =
        rel_time_to_duration(dt.time);
    proof {
        assert(0 <= time_nanos_spec(dt.time));
        assert(time_nanos_spec(dt.time)
            < nanos_per_civil_day());
        assert(ued_iv().contains(epd.day as int));
        assert(sd_total_nanos(&d1)
            == (epd.day as int)
                * S_CIVIL_DAY_SECS() * S_NANOS_PER_SEC());
        assert(sd_total_nanos(&d1)
            == ns_epoch_day_spec(
                dt.date.year as int,
                dt.date.month as int,
                dt.date.day as int,
            ) * S_CIVIL_DAY_SECS() * S_NANOS_PER_SEC());
        // the ops_add excluder: |d1.secs| is at most a few billion
        // seconds and d2 is sub-day.
        assert((d1.secs as int)
            >= -(4_371_587int) * 86_400);
        assert((d1.secs as int)
            <= (2_932_896int) * 86_400);
        assert((d2.secs as int) >= -86_401);
        assert((d2.secs as int) <= 86_401);
        assert(((d1.secs as int) + (d2.secs as int))
            <= 9_223_372_036_854_775_806int);
        assert(((d1.secs as int) + (d2.secs as int))
            >= -(9_223_372_036_854_775_807int));
    }
    crate::jcore_signed_duration::sd_ops_add(&d1, &d2)
}

/// The nested-trunc identity (the days lane of any from-invariant
/// chain over a civil-datetime window): trunc division nests
/// exactly, so the day lane of the Day-largest chain is the single
/// trunc of the total by the civil day. (Same shape as the J8
/// lemma_trunc_uniqueness, restated locally since that lemma is
/// private in its file.)
proof fn rel_nested_trunc(t: int, a: int, b: int)
    requires
        a > 0 && b > 0,
    ensures
        rust_div(rust_div(t, a), b) == rust_div(t, a * b),
{
    // The non-negative mirror (trunc and Euclid agree on it), the
    // composed Euclid chain with every symbolic product spelled
    // through the mul lemmas (z3 does not unfold product identities
    // by itself -- the J2 month-core lesson), then the sign bridge.
    let u: int = if t >= 0 { t } else { 0 - t };
    let qa: int = u / a;
    let ra: int = u % a;
    let qb: int = qa / b;
    let rb: int = qa % b;
    lemma_fundamental_div_mod(u, a);
    lemma_fundamental_div_mod(qa, b);
    assert(u == qa * a + ra);
    assert(0 <= ra && ra < a);
    assert(qa == qb * b + rb);
    assert(0 <= rb && rb < b);
    lemma_mul_is_distributive_add_other_way(a, qb * b, rb);
    lemma_mul_is_associative(qb, b, a);
    lemma_mul_is_commutative(b, a);
    assert((qb * b + rb) * a
        == qb * b * a + rb * a);
    assert(qb * b * a == qb * (b * a));
    assert(qb * (b * a) == qb * (a * b));
    assert(u == qb * (a * b) + (rb * a + ra));
    // the converse precondition 0 <= rb*a + ra < a*b, spelled:
    assert(rb <= b - 1 && ra <= a - 1);
    lemma_mul_is_distributive_sub(a, b, 1);
    lemma_mul_basics(a);
    assert(a * (b - 1) == a * b - a);
    assert((a * b - a) + (a - 1) < a * b);
    lemma_mul_is_distributive_add_other_way(a, rb, b - 1 - rb);
    assert((rb + (b - 1 - rb)) * a
        == rb * a + (b - 1 - rb) * a);
    assert(rb * a + (b - 1 - rb) * a == (b - 1) * a);
    assert(rb * a <= (b - 1) * a);
    lemma_mul_is_commutative(b, a);
    assert((b - 1) * a == b * a - a);
    assert(b * a == a * b);
    assert(rb * a + ra <= (b - 1) * a + (a - 1));
    assert(rb * a + ra < a * b);
    lemma_fundamental_div_mod_converse(
        u, a * b, qb, rb * a + ra);
    assert(qb == u / (a * b));
    if t >= 0 {
        assert(u == t);
        assert(rust_div(t, a) == qa);
        assert(rust_div(qa, b) == qb);
        assert(rust_div(t, a * b) == qb);
    } else {
        assert(u == 0 - t);
        assert(rust_div(t, a) == 0 - qa);
        assert(rust_div(0 - qa, b) == 0 - qb);
        assert(rust_div(t, a * b) == 0 - qb);
    }
}

/// The Day-largest from-invariant fits claim over the whole civil
/// datetime domain (datetime.rs:3274-3283's "this always succeeds
/// because every unit except for nanoseconds ... can represent all
/// possible spans of time between any two civil datetimes" and the
/// wrapper doc's never-fails guarantee at :2017-2019: "because a
/// Span can represent the difference between any two possible
/// datetimes, it will never panic" }): on the datetime window the
/// chain's day lane is the single trunc of the total by the civil
/// day, whose magnitude never leaves the b::SpanDays range, and every
/// lower lane is a sub-day remainder orders of magnitude inside its
/// b range.
pub proof fn rel_lemma_dt_diff_fits(l: Unit, t: int)
    requires
        l is Day,
        -(7_304_484int)
            * crate::time::nanos_per_civil_day()
            < t,
        t < (7_304_484int)
            * crate::time::nanos_per_civil_day(),
    ensures
        sp_fid_fits(l, t),
{
    assert(crate::time::nanos_per_civil_day()
        == 86_400 * 1_000_000_000);
    // the weeks lane is structurally zero at Day largest.
    assert(sp_fid_w(l, t) == 0);
    // the days lane is the single nested trunc (exact).
    rel_nested_trunc(t, 1_000_000_000, 86_400);
    assert(sp_fid_secs(t) == rust_div(t, 1_000_000_000));
    assert(sp_fid_d(l, t)
        == rust_div(t, 86_400_000_000_000int));
    assert(sp_fid_d(l, t) >= -(7_304_483int));
    assert(sp_fid_d(l, t) <= 7_304_483);
    // the within-day remainder lanes carry a sub-day window.
    assert(sp_fid_r_d(l, t) >= -86_400);
    assert(sp_fid_r_d(l, t) <= 86_400);
    assert(sp_fid_h(l, t)
        == rust_div(sp_fid_r_d(l, t), 3_600));
    assert(sp_fid_h(l, t) >= -25);
    assert(sp_fid_h(l, t) <= 25);
    assert(sp_fid_r_h(l, t)
        == rust_rem(sp_fid_r_d(l, t), 3_600));
    assert(sp_fid_r_h(l, t) >= -3_599);
    assert(sp_fid_r_h(l, t) <= 3_599);
    assert(sp_fid_m(l, t)
        == rust_div(sp_fid_r_h(l, t), 60));
    assert(sp_fid_m(l, t) >= -60);
    assert(sp_fid_m(l, t) <= 60);
    assert(sp_fid_r_m(l, t)
        == rust_rem(sp_fid_r_h(l, t), 60));
    assert(sp_fid_r_m(l, t) >= -59);
    assert(sp_fid_r_m(l, t) <= 59);
    assert(sp_fid_s(l, t) == sp_fid_r_m(l, t));
    assert(sp_fid_r_s(l, t) == 0);
    assert(sp_fid_sub(t) >= -(999_999_999int));
    assert(sp_fid_sub(t) <= 999_999_999);
    assert(sp_fid_mi(l, t)
        == rust_div(sp_fid_sub(t), 1_000_000));
    assert(sp_fid_mi(l, t) >= -(1_001int));
    assert(sp_fid_mi(l, t) <= 1_001);
    assert(sp_fid_n_am(l, t)
        == rust_rem(sp_fid_sub(t), 1_000_000));
    assert(sp_fid_mc(l, t)
        == rust_div(sp_fid_n_am(l, t), 1_000));
    assert(sp_fid_mc(l, t) >= -(1_001int));
    assert(sp_fid_mc(l, t) <= 1_001);
    assert(sp_fid_nn(l, t)
        == rust_rem(sp_fid_n_am(l, t), 1_000));
    assert(sp_fid_nn(l, t) >= -999_999);
    assert(sp_fid_nn(l, t) <= 999_999);
    // every lane orders of magnitude inside its b::Span range.
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
    assert(-(631_107_417_600_000_000int)
        <= sp_fid_mc(l, t));
    assert(sp_fid_mc(l, t)
        <= 631_107_417_600_000_000);
    assert(-(9_223_372_036_854_775_807int)
        <= sp_fid_nn(l, t));
    assert(sp_fid_nn(l, t)
        <= 9_223_372_036_854_775_807);
}

/// The signed-difference excluders over the datetime window: the
/// to_duration totals of valid datetimes keep each other well inside
/// the sd second range, so the Sub operator is panic-free here (the
/// reunion sd_sub_civil_day pattern at the datetime window).
fn rel_dt_sub_sd(
    a: &SignedDuration,
    b: &SignedDuration,
) -> (r: SignedDuration)
    requires
        sd_inv(a),
        sd_inv(b),
        -(7_304_484int)
            * crate::time::nanos_per_civil_day()
            <= sd_total_nanos(a),
        sd_total_nanos(a)
            <= (7_304_484int)
                * crate::time::nanos_per_civil_day(),
        -(7_304_484int)
            * crate::time::nanos_per_civil_day()
            <= sd_total_nanos(b),
        sd_total_nanos(b)
            <= (7_304_484int)
                * crate::time::nanos_per_civil_day(),
    ensures
        sd_inv(&r),
        sd_total_nanos(&r)
            == sd_total_nanos(a) - sd_total_nanos(b),
{
    proof {
        assert((b.secs as int)
            <= (7_304_484int) * 86_400 + 1);
        assert((b.secs as int)
            >= -((7_304_484int) * 86_400) - 1);
        assert(b.secs != i64::MIN);
        assert((a.secs as int) - (b.secs as int)
            <= (7_304_484int) * 86_400 * 2 + 2);
        assert((a.secs as int) - (b.secs as int)
            >= -((7_304_484int) * 86_400) * 2 - 2);
    }
    crate::jcore_signed_duration::sd_ops_sub(a, b)
}

/// Origin Rust: pub fn until<A: Into<DateTimeDifference>>(
///     self, other: A) -> Result<Span, Error>
///     (main-crate datetime.rs:1995-2006) over
/// DateTimeDifference::until_with_largest_unit (datetime.rs:3268-3320)
/// at the default configuration (largest = Day, no rounding).
/// Upstream doc (datetime.rs:1902-1911, abridged):
///   Returns a span representing the elapsed time from this datetime
///   until the given `other` datetime.
///   When `other` occurs before this datetime, then the span returned
///   will be negative.
///   By default, the span returned is balanced such that the biggest
///   possible unit is days.
/// Upstream doc (datetime.rs:1954-1957, # Errors):
///   It is guaranteed that if one provides a datetime with the default
///   [DateTimeDifference] configuration, then this routine will
///   never fail.
/// Body (datetime.rs:3274-3283, default): the to_duration difference
/// straight into Span::from_invariant_duration(largest = Day); the
/// never-fail claim is exactly the fits lemma above.
pub exec fn rel_dt_until_span(
    dt1: DateTime,
    dt2: DateTime,
) -> (s: Span)
    requires
        valid_datetime(dt1),
        valid_datetime(dt2),
    ensures
        sp_from_inv_face(
            Unit::Day,
            rel_dt_total(dt2) - rel_dt_total(dt1),
            &Option::Some(s),
        ),
{
    let a: SignedDuration = rel_dt_to_duration(dt2);
    let b: SignedDuration = rel_dt_to_duration(dt1);
    let diff: SignedDuration = rel_dt_sub_sd(&a, &b);
    proof {
        let tt: int =
            rel_dt_total(dt2) - rel_dt_total(dt1);
        let cd: int = crate::time::nanos_per_civil_day();
        assert(sd_total_nanos(&diff) == tt);
        // the to_duration window: |tt| is under the 7,304,484-day
        // ledger bound exactly, by the ued span of the two legs.
        assert(sd_total_nanos(&a)
            == rel_dt_total(dt2));
        assert(sd_total_nanos(&b)
            == rel_dt_total(dt1));
        assert(-(7_304_484int) * cd < tt);
        assert(tt < (7_304_484int) * cd);
    }
    proof {
        rel_lemma_dt_diff_fits(
            Unit::Day, sd_total_nanos(&diff));
    }
    match Span::sp_from_invariant_duration(Unit::Day, &diff) {
        Option::Some(s) => s,
        Option::None => {
            // Dead arm: the difference between two valid civil
            // datetimes always fits (the never-fail guarantee above).
            assert(false);
            Span::new()
        }
    }
}

/// Origin Rust: pub fn since<A: Into<DateTimeDifference>>(
///     self, other: A) -> Result<Span, Error>
///     (main-crate datetime.rs:2032-2043)
/// Upstream doc (datetime.rs:2008-2013, abridged):
///   This routine is identical to [DateTime::until], but the order of
///   the parameters is flipped.
/// Upstream body: `let span = -args.until_with_largest_unit(self)?;`
/// -- the negated until-span of the same pair. The face states the
/// negation through the negated pair (the trunc anti-automorphism is
/// NOT needed: some |u| witnesses the until face, negation passes
/// every magnitude through and flips the sign; spelled as a spec
/// negation so no exec call enters the ensures).
pub exec fn rel_dt_since_span(
    dt1: DateTime,
    dt2: DateTime,
) -> (s: Span)
    requires
        valid_datetime(dt1),
        valid_datetime(dt2),
    ensures
        exists |u: Span| {
            &&& sp_from_inv_face(
                Unit::Day,
                rel_dt_total(dt2) - rel_dt_total(dt1),
                &Option::Some(u),
            )
            &&& s == rel_span_negate_value(&u)
        },
{
    let u: Span = rel_dt_until_span(dt1, dt2);
    let neg: Span = u.negate();
    proof {
        assert(neg == rel_span_negate_value(&u));
    }
    neg
}

// ===========================================================================
// The Span relative pipeline (span.rs:1767-1787) -- the Some(relative)
// side this batch adds over the J8 relative-None entries, plus the
// checked_add_invariant days/weeks-lane generalization the marker
// route needs.
// ===========================================================================

/// Span::checked_add_invariant (span.rs:1818-1825) at the full
/// invariant reading: both spans' non-variable units fold through
/// to_invariant_duration (the J8 face restricted itself to the
/// time-only rhs; the marker route allows weeks/days lanes, so the
/// chain is re-derived over the full sp_inv_total).
fn rel_inv_add_full(
    span1: &Span,
    span2: &Span,
    unit: Unit,
) -> (r: Option<Span>)
    requires
        sp_field_inv(span1),
        sp_field_inv(span2),
        sp_unit_rank(unit)
            <= sp_unit_rank(Unit::Week),
    ensures
        sp_from_inv_face(
            unit,
            sp_inv_total_nanos(span1)
                + sp_inv_total_nanos(span2),
            &r,
        ),
{
    let d1: SignedDuration = span1.sp_to_invariant_duration();
    let d2: SignedDuration = span2.sp_to_invariant_duration();
    let sum: Option<SignedDuration> =
        sd_checked_add_info(&d1, &d2);
    match sum {
        Option::Some(sd) => {
            Span::sp_from_invariant_duration(unit, &sd)
        }
        Option::None => {
            proof {
                let tt: int = sp_inv_total_nanos(span1)
                    + sp_inv_total_nanos(span2);
                assert(sd_total_nanos(&d1)
                    == sp_inv_total_nanos(span1));
                assert(sd_total_nanos(&d2)
                    == sp_inv_total_nanos(span2));
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

/// Origin Rust: fn checked_add_span<'a>(&self, relative:
///     Option<SpanRelativeTo<'a>>, span: &Span)
///     -> Result<Span, Error> (span.rs:1767-1787)
/// Upstream body (:1772-1786):
///     let (span1, span2) = (*self, *span);
///     let unit = span1.largest_unit().max(span2.largest_unit());
///     let start = match relative {
///         Some(r) => match r.to_relative(unit)? {
///             None => return span1.checked_add_invariant(unit, &span2),
///             Some(r) => r,
///         },
///         None => {
///             requires_relative_date_err(unit)?;
///             return span1.checked_add_invariant(unit, &span2);
///         }
///     };
///     let mid = start.checked_add(span1)?;
///     let end = mid.checked_add(span2)?;
///     start.until(unit, &end)
/// This face materializes the Some(relative) side (the None side stays
/// the J8-translated sp_checked_add_span entry); the Civil branch is
/// capped at Day-largest years by this batch's modeling loss 5 (the
/// until-with-larger-units arm rides the deferred Date::until
/// Month/Year configurations), and the start.until consumption is the
/// default DateTime until face above.
pub exec fn rel_span_checked_add_rel(
    span1: &Span,
    span2: &Span,
    relative: &SpanRel,
) -> (r: Option<Span>)
    requires
        sp_field_inv(span1),
        sp_zero_sign_ok(span1),
        sp_flags_ok(span1),
        sp_field_inv(span2),
        sp_zero_sign_ok(span2),
        sp_flags_ok(span2),
        // The marker allows the whole invariant range. The Civil
        // branch is this batch's deferred cut: the pipelined Civil
        // mid/end construction needs valid_datetime on the epoch-
        // twin-constructed results, which rides the J7-deferred NS
        // reverse family (the modeling-loss-4 cascade); its gateway
        // faces (to_relative, the Date/DateTime constructors and the
        // dt-move faces) all land above for the follow-up batch.
        relative.kind is DaysAre24Hours,
        sp_unit_rank(sp_span_largest(span1))
            <= sp_unit_rank(Unit::Week),
        sp_unit_rank(sp_span_largest(span2))
            <= sp_unit_rank(Unit::Week),
    ensures
        ({
            let u: Unit = sp_unit_max(
                sp_span_largest(span1),
                sp_span_largest(span2),
            );
            sp_from_inv_face(
                u,
                sp_inv_total_nanos(span1)
                    + sp_inv_total_nanos(span2),
                &r,
            )
        }),
{
    proof {
        assert(relative.kind is DaysAre24Hours);
    }
    let u1: Unit = span1.largest_unit();
    let u2: Unit = span2.largest_unit();
    proof {
        assert(u1 == sp_span_largest(span1));
        assert(u2 == sp_span_largest(span2));
    }
    let u: Unit = sp_unit_max_exec(u1, u2);
    proof {
        assert(u == sp_unit_max(u1, u2));
        assert(u == sp_unit_max(
            sp_span_largest(span1),
            sp_span_largest(span2),
        ));
    }
    match relative.to_relative(u) {
        Option::Some(Option::None) => {
            // the marker / invariant-unit branch (span.rs:1776).
            rel_inv_add_full(span1, span2, u)
        }
        Option::Some(Option::Some(start)) => {
            // unreachable under this face's requires (the marker is
            // the only allowed kind).
            proof {
                let dtx: DateTime = start;
                assert(false);
            }
            Option::None
        }
        Option::None => {
            // The marker's Year|Month error arm gets the face's
            // None-side only where the unit caps allow it... under
            // this face's requires caps (largest <= Week) the arm is
            // unreachable.
            proof {
                assert(false);
            }
            Option::None
        }
    }
}


// ===========================================================================
// Panels: the doc rows this batch's faces state, executed through this
// translation's layout (each panel cites its upstream doctest rows;
// the Civil pipelined row span.rs:5613-5626 rides the deferred Civil
// pipeline cut, its marker twin below covers the same 27-day value).
// ===========================================================================

/// Doc rows (main-crate date.rs:1264-1280):
///   let d = date(2024, 3, 31);
///   d.checked_add(1.months())? == date(2024, 4, 30);
///   d.checked_add(2.months())? == date(2024, 5, 31);
pub exec fn rel_panel_date_add_months() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 3, 31);
    let s0: Span = Span::new();
    let m1: Span = s0.months(1);
    match rel_date_checked_add_span(&d, &m1) {
        Option::Some(d2) => {
            assert((d2.year as int) == 2024);
            assert((d2.month as int) == 4);
            assert((d2.day as int) == 30);
            let m2: Span = s0.months(2);
            match rel_date_checked_add_span(&d, &m2) {
                Option::Some(d3) => {
                    assert((d3.year as int) == 2024);
                    assert((d3.month as int) == 5);
                    assert((d3.day as int) == 31);
                    true
                }
                Option::None => {
                    assert(false);
                    false
                }
            }
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc rows (main-crate date.rs:1272-1277):
///   d.checked_add(23.hours())? == date(2024, 3, 31);
///   d.checked_add(28.hours())? == date(2024, 4, 1);
pub exec fn rel_panel_date_add_timefold() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 3, 31);
    let s0: Span = Span::new();
    let h23: Span = s0.hours(23);
    match rel_date_checked_add_span(&d, &h23) {
        Option::Some(d2) => {
            assert((d2.year as int) == 2024);
            assert((d2.month as int) == 3);
            assert((d2.day as int) == 31);
            let h28: Span = s0.hours(28);
            match rel_date_checked_add_span(&d, &h28) {
                Option::Some(d3) => {
                    assert((d3.year as int) == 2024);
                    assert((d3.month as int) == 4);
                    assert((d3.day as int) == 1);
                    true
                }
                Option::None => {
                    assert(false);
                    false
                }
            }
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc row (main-crate date.rs:1294-1305):
///   d.checked_add(-1.months())? == date(2024, 2, 29)
pub exec fn rel_panel_date_sub_months() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 3, 31);
    let s0: Span = Span::new();
    let nm: Span = s0.months(-1);
    proof {
        let tt: int = ns_epoch_day_spec(2024, 2, 29);
        assert(tt >= -4_371_587int);
        assert(tt <= 2_932_896int);
    }
    match rel_date_checked_add_span(&d, &nm) {
        Option::Some(d2) => {
            assert((d2.year as int) == 2024);
            assert((d2.month as int) == 2);
            assert((d2.day as int) == 29);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc rows (main-crate date.rs:1307-1315): 9000.years() /
/// -19000.years() both error on date(2024, 3, 31).
pub exec fn rel_panel_date_add_years_err() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 3, 31);
    let s0: Span = Span::new();
    let y9: Span = s0.years(9000);
    let y19: Span = s0.years(-19000);
    proof {
        assert(!year_iv().contains(11024int));
        assert(!year_iv().contains(-16976int));
    }
    match rel_date_checked_add_span(&d, &y9) {
        Option::Some(_) => {
            assert(false);
            false
        }
        Option::None => {
            match rel_date_checked_add_span(&d, &y19) {
                Option::Some(_) => {
                    assert(false);
                    false
                }
                Option::None => true,
            }
        }
    }
}

/// Doc rows (main-crate date.rs:1323-1339, the SignedDuration rhs):
///   date(2024, 2, 29) + 24h == date(2024, 3, 1);
///   date(2024, 2, 29) - 24h == date(2024, 2, 28).
pub exec fn rel_panel_date_add_sd() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 2, 29);
    let dur: SignedDuration = sd_from_civil_days32(1);
    match rel_date_checked_add_sd(&d, &dur) {
        Option::Some(d2) => {
            assert((d2.year as int) == 2024);
            assert((d2.month as int) == 3);
            assert((d2.day as int) == 1);
            let n: Option<SignedDuration> = dur.checked_neg();
            match n {
                Option::Some(nd) => {
                    match rel_date_checked_add_sd(&d, &nd) {
                        Option::Some(d3) => {
                            assert((d3.year as int) == 2024);
                            assert((d3.month as int) == 2);
                            assert((d3.day as int) == 28);
                            true
                        }
                        Option::None => {
                            assert(false);
                            false
                        }
                    }
                }
                Option::None => {
                    assert(false);
                    false
                }
            }
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc row (main-crate date.rs:1405-1420):
///   date(2024, 2, 29).checked_sub(1.year())? == date(2023, 2, 28)
pub exec fn rel_panel_date_sub_year() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 2, 29);
    let s0: Span = Span::new();
    let y1: Span = s0.years(1);
    match rel_date_checked_sub_span(&d, &y1) {
        Option::Some(d2) => {
            assert((d2.year as int) == 2023);
            assert((d2.month as int) == 2);
            assert((d2.day as int) == 28);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc rows (main-crate date.rs:1521-1533):
///   date(2006, 8, 24).until(date(2019, 1, 31))? == 4543.days();
///   the flipped pair == -4543.days().
pub exec fn rel_panel_date_until_days() -> (ok: bool)
    ensures
        ok,
{
    let earlier: Date = crate::date::date(2006, 8, 24);
    let later: Date = crate::date::date(2019, 1, 31);
    let s: Span = rel_date_until_span(earlier, later, Unit::Day);
    assert((s.days as int) == 4543);
    assert(s.sign is Positive);
    assert(s.weeks == 0);
    let s2: Span = rel_date_until_span(later, earlier, Unit::Day);
    assert((s2.days as int) == 4543);
    assert(s2.sign is Negative);
    true
}

/// The jcore extremes ledger row (J2 notes: 7_304_483 ==
/// Date::MAX.until(Date::MIN)) at the Span-return face.
pub exec fn rel_panel_date_until_extremes() -> (ok: bool)
    ensures
        ok,
{
    let dmin: Date = crate::date::date(-9999, 1, 1);
    let dmax: Date = crate::date::date(9999, 12, 31);
    let s: Span = rel_date_until_span(dmin, dmax, Unit::Day);
    assert((s.days as int) == 7_304_483);
    assert(s.sign is Positive);
    true
}

/// Doc rows (main-crate datetime.rs:1604-1613):
///   date(1995, 12, 7).at(3, 24, 30, 3_500)
///       + 20.years().months(4).nanoseconds(500)
///   == date(2016, 4, 7).at(3, 24, 30, 4_000).
pub exec fn rel_panel_dt_add_general() -> (ok: bool)
    ensures
        ok,
{
    let t0: Time = Time::constant(3, 24, 30, 3_500);
    let dt: DateTime =
        DateTime::from_parts(
            crate::date::date(1995, 12, 7), t0);
    let s0: Span = Span::new();
    let sy: Span = s0.years(20);
    let sm: Span = sy.months(4);
    let sn: Span = sm.nanoseconds(500);
    match rel_dt_checked_add_span(dt, &sn) {
        Option::Some(dt2) => {
            assert((dt2.date.year as int) == 2016);
            assert((dt2.date.month as int) == 4);
            assert((dt2.date.day as int) == 7);
            assert((dt2.time.hour as int) == 3);
            assert((dt2.time.minute as int) == 24);
            assert((dt2.time.second as int) == 30);
            assert((dt2.time.subsec_nanosecond as int) == 4_000);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc row (main-crate datetime.rs:1611-1613):
///   date(2019, 1, 31).at(15, 30, 0, 0) + 1.months()
///   == date(2019, 2, 28).at(15, 30, 0, 0).
pub exec fn rel_panel_dt_add_cal() -> (ok: bool)
    ensures
        ok,
{
    let t0: Time = Time::constant(15, 30, 0, 0);
    let dt: DateTime =
        DateTime::from_parts(
            crate::date::date(2019, 1, 31), t0);
    let s0: Span = Span::new();
    let m1: Span = s0.months(1);
    match rel_dt_checked_add_span(dt, &m1) {
        Option::Some(dt2) => {
            assert((dt2.date.year as int) == 2019);
            assert((dt2.date.month as int) == 2);
            assert((dt2.date.day as int) == 28);
            assert((dt2.time.hour as int) == 15);
            assert((dt2.time.minute as int) == 30);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc row (datetime.rs:1631-1643):
///   date(2024, 3, 31).at(19, 5, 59, 999_999_999) - 1.months()
///   == date(2024, 2, 29).at(19, 5, 59, 999_999_999).
pub exec fn rel_panel_dt_sub_months() -> (ok: bool)
    ensures
        ok,
{
    let t0: Time = Time::constant(19, 5, 59, 999_999_999);
    let dt: DateTime =
        DateTime::from_parts(
            crate::date::date(2024, 3, 31), t0);
    let s0: Span = Span::new();
    let nm: Span = s0.months(-1);
    proof {
        let tt: int = ns_epoch_day_spec(2024, 2, 29);
        assert(ns_civil_month(tt) == 2);
        assert(ns_civil_day(tt) == 29);
    }
    match rel_dt_checked_add_span(dt, &nm) {
        Option::Some(dt2) => {
            assert((dt2.date.month as int) == 2);
            assert((dt2.date.day as int) == 29);
            assert((dt2.time.subsec_nanosecond as int)
                == 999_999_999);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// The series doc row (datetime.rs:2336-2356):
///   date(2023, 7, 15).at(16, 30, 0, 0) + 5.hours()
///   == date(2023, 7, 15).at(21, 30, 0, 0).
pub exec fn rel_panel_dt_add_time_arm() -> (ok: bool)
    ensures
        ok,
{
    let t0: Time = Time::constant(16, 30, 0, 0);
    let dt: DateTime =
        DateTime::from_parts(
            crate::date::date(2023, 7, 15), t0);
    let s0: Span = Span::new();
    let h5: Span = s0.hours(5);
    match rel_dt_checked_add_span(dt, &h5) {
        Option::Some(dt2) => {
            assert((dt2.date.year as int) == 2023);
            assert((dt2.date.month as int) == 7);
            assert((dt2.date.day as int) == 15);
            assert((dt2.time.hour as int) == 21);
            assert((dt2.time.minute as int) == 30);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc rows (datetime.rs:1645-1653): 9000.years() /
/// -19000.years() both error on the datetime.
pub exec fn rel_panel_dt_add_errs() -> (ok: bool)
    ensures
        ok,
{
    let t0: Time = Time::constant(13, 13, 13, 13);
    let dt: DateTime =
        DateTime::from_parts(
            crate::date::date(2024, 3, 31), t0);
    let s0: Span = Span::new();
    let y9: Span = s0.years(9000);
    let y19: Span = s0.years(-19000);
    proof {
        assert(!year_iv().contains(11024int));
        assert(!year_iv().contains(-16976int));
    }
    match rel_dt_checked_add_span(dt, &y9) {
        Option::Some(_) => {
            assert(false);
            false
        }
        Option::None => {
            match rel_dt_checked_add_span(dt, &y19) {
                Option::Some(_) => {
                    assert(false);
                    false
                }
                Option::None => true,
            }
        }
    }
}

/// Doc row (datetime.rs:2021-2030):
///   later - earlier == 4542.days().hours(22).minutes(30)
/// (through this face's until direction).
pub exec fn rel_panel_dt_until_row() -> (ok: bool)
    ensures
        ok,
{
    let earlier: DateTime = DateTime::from_parts(
        crate::date::date(2006, 8, 24),
        Time::constant(22, 30, 0, 0));
    let later: DateTime = DateTime::from_parts(
        crate::date::date(2019, 1, 31),
        Time::constant(21, 0, 0, 0));
    let s: Span = rel_dt_until_span(earlier, later);
    assert((s.days as int) == 4542);
    assert((s.hours as int) == 22);
    assert((s.minutes as int) == 30);
    assert(s.sign is Positive);
    assert(s.weeks == 0);
    true
}

/// Doc row (span.rs:4177-4194): 2.days().hours(12) +
/// 12.hours() with the days_are_24_hours marker == 3.days().
pub exec fn rel_panel_span_marker_balance() -> (ok: bool)
    ensures
        ok,
{
    let s0: Span = Span::new();
    let d2: Span = s0.days(2);
    let s1: Span = d2.hours(12);
    let s2: Span = s0.hours(12);
    let rel: SpanRel = SpanRel::days_are_24_hours();
    match rel_span_checked_add_rel(&s1, &s2, &rel) {
        Option::Some(s3) => {
            assert((s3.days as int) == 3);
            assert(s3.hours == 0);
            assert(s3.minutes == 0);
            assert(s3.sign is Positive);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc row (span.rs:5632-5647): the date-ladder through the marker --
/// (d2 - d1) + (d3 - d2) with days_are_24_hours == 27.days().
pub exec fn rel_panel_span_marker_dateladder() -> (ok: bool)
    ensures
        ok,
{
    let d1: Date = crate::date::date(2025, 1, 18);
    let d2: Date = crate::date::date(2025, 1, 26);
    let d3: Date = crate::date::date(2025, 2, 14);
    let s1: Span = rel_date_until_span(d1, d2, Unit::Day);
    let s2: Span = rel_date_until_span(d2, d3, Unit::Day);
    let rel: SpanRel = SpanRel::days_are_24_hours();
    match rel_span_checked_add_rel(&s1, &s2, &rel) {
        Option::Some(s3) => {
            assert((s3.days as int) == 27);
            assert(s3.sign is Positive);
            true
        }
        Option::None => {
            assert(false);
            false
        }
    }
}

/// Doc row (main-crate date.rs:1282-1292): the add-operator face --
///   let d = date(2024, 3, 31);
///   assert_eq!(d + 1.months(), date(2024, 4, 30));
pub exec fn rel_panel_date_add_op_row() -> (ok: bool)
    ensures
        ok,
{
    let d: Date = crate::date::date(2024, 3, 31);
    let s0: Span = Span::new();
    let m1: Span = s0.months(1);
    proof {
        let tt: int = ns_epoch_day_spec(2024, 4, 30);
        assert(tt >= -4_371_587int);
        assert(tt <= 2_932_896int);
        assert(rel_date_gates_ok(d, &m1));
    }
    let d2: Date = rel_date_add_op(&d, &m1);
    assert((d2.year as int) == 2024);
    assert((d2.month as int) == 4);
    assert((d2.day as int) == 30);
    true
}

} // verus!
