//! jiff 0.2.43 -- the J12 reunion-seats batch: the compare / total /
//! round Some(relative) seats (span.rs :4512-4533, :4814-4821,
//! :5366-5391), the Month/Year-configured arms of
//! DateDifference::since_with_largest_unit with the month_add_one
//! borrow-correction group (civil/date.rs :2761-2828, the J9 notes'
//! strongest remaining jiff face), the last Time quickcheck property
//! prop_until_is_since_negated (civil/time.rs :3367-3370), and the J7
//! leftover Date::at one-line reassembly (civil/date.rs :1221-1230)
//! -- Verus translation, batch J12.
//!
//! Scope by the batch instruction's clipping doctrine:
//! 1. The SpanRelativeTo gateway tier re-transcribed in capped form
//!    (span.rs:5481-5734, verbatim from the J9 panel's verified shape;
//!    this file does NOT mount jcore_span_relative.rs, whose
//!    compliance-repair wave is mid-flight -- the twin below keeps
//!    the same ensures faces so the seats stand alone).
//! 2. The Some(relative) branch contracts of SpanCompare::compare,
//!    SpanTotal::total and SpanRound::round: the full lane
//!    disjunction (None config, marker config, civil config) over
//!    the to_relative mapping, at the lanes each can honestly carry
//!    (see the two-sided face fns and prune 2).
//! 3. Date::until / Date::since in the largest = Month / Year
//!    configurations (date.rs:2761-2828, the month_add_one
//!    borrow-correction mass; the Day/Week configurations are the
//!    J9 panel's own faces).
//! 4. The fifth Time quickcheck property, closed at the wrapper-body
//!    structural level (Time::since is the negation of the
//!    until_with_largest_unit span, time.rs:1259-1267, so the
//!    property reduces to the sign involution of Span::negate).
//! 5. Date::at (date.rs:1221-1230), the J7 leftover.
//!
//! Modeling losses / prunes (each also annotated at its site):
//! 1. Result<T, Error> surfaces materialize as Option<T> (the J1/J5
//!    family ledger; the UnitConfigError values are zero-sized kind
//!    witnesses).
//! 2. The Civil-variable lanes of the three seats (to_relative
//!    returning Some(Some(dt)): compare's start/end checked_add +
//!    to_duration ordering, total's into_relative_span + DST
//!    measurement, round's Relative::round Nudge machinery) ride the
//!    J9-deferred civil pipeline (valid_datetime on the
//!    ns-twin-constructed mid/end, J9 notes' deferred item 1) and
//!    stay capped OUT of this batch by requires: the seats' contracts
//!    are stated over the config x unit domain that excludes them
//!    (the cap is recorded at every site; the definition-level seat
//!    face marks the excluded region with its vacuous contingency).
//! 3. The Zoned arms of SpanRelativeTo (span.rs:5692-5696, :5718-
//!    5722) are pruned as in the J9 batch (real tz arithmetic stays
//!    out of the civil closure); the DaysAre24Hours marker and both
//!    civil constructors are transcribed whole.
//! 4. Date::until / since textbook misconfiguration guards (smallest
//!    < Unit::Day, largest < Unit::Day, DateDifference's rounding
//!    plumbing) ride the J9 precedent: this file translates the
//!    (Unit, Date)-configured largest in {Month, Year} lanes with the
//!    default non-rounding configuration only.
//!
//! Driver mount: `verified/j12-driver.rs` mounts this file next to
//! the lib.rs civil tree (bounds/constants/date/time/datetime) plus
//! the J4b/J5/J8/J10/J11 closed panels (signed-duration, span,
//! span_arith, span_reunion, round, span_total); every closed panel
//! re-verifies unchanged in that run.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;

use crate::bounds::{Sign, year_iv};
use crate::date::{
    Date, days_in_month, days_in_month_spec, valid_date,
};
use crate::datetime::{DateTime, valid_datetime};
use crate::jcore_round::{
    Increment, RoundMode, SpanRound, inc_for_span_ok, inc_inv,
    rm_unit_nanos, sp_round_span_invariant, sr_config_ok,
    sr_eff_largest, sr_round_inv_face, sr_round_none_face,
    sr_rt_total,
};
use crate::jcore_signed_duration::{
    SignedDuration, sd_max_total_nanos, sd_min_total_nanos,
    sd_total_nanos,
};
use crate::jcore_span::{
    Span, Unit, sp_all_zero, sp_field_inv, sp_flags_ok, sp_sign_val,
    sp_zero_sign_ok,
};

use crate::jcore_span_arith::{
    lemma_fid_lane_signs, sp_fid_d, sp_fid_fits, sp_fid_h, sp_fid_m,
    sp_fid_mc, sp_fid_mi, sp_fid_nn, sp_fid_s, sp_fid_secs,
    sp_fid_w, sp_inv_total_nanos, sp_span_largest, sp_unit_max,
    sp_unit_max_exec, sp_unit_rank, sp_unit_rank_exec,
};
use crate::jcore_span_total::{
    SpOrdering, SpTotalRatio, SpanCompare, SpanTotal,
    spc_compare_none_face, spc_ordering_of_totals, sd_lex_cmp_exec,
    spt_config_ok, spt_total_inv_face,
};
use crate::time::{
    Time, nanos_per_civil_day, valid_time,
};

verus! {

// ===========================================================================
// (0) The gateway tier twin: SpanRelativeTo (span.rs:5481-5734), the
// DaysAre24Hours marker and the civil constructors, to_relative
// (span.rs:5684-5708) -- re-transcribed with the same two-sided face
// the J9 panel verified (this file mounts neither
// jcore_span_relative.rs nor j9-driver.rs, so the twin carries the
// seats' own copy of the mapping contract).
// ===========================================================================

/// Spec twin of Unit::is_variable (span.rs:3948-3950):
///     pub(crate) const fn is_variable(self) -> bool {
///         matches!(self, Unit::Year | Unit::Month | Unit::Week | Unit::Day)
///     }
pub open spec fn seat_unit_is_variable(u: Unit) -> bool {
    u is Year || u is Month || u is Week || u is Day
}

/// Origin Rust: enum SpanRelativeToKind<'a> (span.rs:5712-5716), the
/// Zoned(&'a Zoned) arm pruned (prune 3).
#[derive(Clone, Copy)]
pub enum SeatRelKind {
    Civil(DateTime),
    DaysAre24Hours,
}

/// Origin Rust: pub struct SpanRelativeTo<'a> { kind:
///     SpanRelativeToKind<'a> } (span.rs:5480-5483; the upstream
/// lifetime only serves the pruned Zoned arm).
#[derive(Clone, Copy)]
pub struct SpanRel {
    pub kind: SeatRelKind,
}

impl SpanRel {

    /// Origin Rust: pub const fn days_are_24_hours()
    ///     -> SpanRelativeTo<'static> (span.rs:5650-5654)
    /// Upstream doc (span.rs:5486-5507, quoted sentence by sentence):
    ///   Creates a special marker that indicates all days ought to be
    ///   [taken] to be 24 hours without providing a relative
    ///   reference time.
    ///   This is relevant to the following APIs: [Span::checked_add,
    ///   Span::checked_sub, Span::compare, Span::total, Span::round,
    ///   Span::to_duration.]
    ///   Specifically, in a previous version of Jiff, the above APIs
    ///   permitted _silently_ [taking] that days are always 24
    ///   hours when a relative reference date wasn't provided. In
    ///   the current version of Jiff, this silent interpretation
    ///   no longer happens and instead an error will occur.
    ///   If you need to use these APIs with spans that contain
    ///   non-zero units of days or weeks but without a relative
    ///   reference date, then you may use this routine to create a
    ///   special marker for `SpanRelativeTo` that permits the APIs
    ///   above to [take] days as always 24 hours.
    pub exec fn days_are_24_hours() -> (r: SpanRel)
        ensures
            r.kind is DaysAre24Hours,
    {
        SpanRel { kind: SeatRelKind::DaysAre24Hours }
    }

    /// Origin Rust: impl From<Date> for SpanRelativeTo<'static>
    ///     (span.rs:5730-5734):
    ///     fn from(date: Date) -> SpanRelativeTo<'static> {
    ///         let dt = DateTime::from_parts(date, Time::midnight());
    ///         SpanRelativeTo { kind: SpanRelKind::Civil(dt) }
    ///     }
    pub exec fn from_date(date: Date) -> (r: SpanRel)
        ensures
            r.kind is Civil,
            match r.kind {
                SeatRelKind::Civil(dt) =>
                    dt.date == date
                        && dt.time.hour == 0
                        && dt.time.minute == 0
                        && dt.time.second == 0
                        && dt.time.subsec_nanosecond == 0,
                SeatRelKind::DaysAre24Hours => false,
            },
    {
        let mn: Time = Time::midnight();
        let dt: DateTime = DateTime::from_parts(date, mn);
        SpanRel { kind: SeatRelKind::Civil(dt) }
    }

    /// Origin Rust: impl From<DateTime> for SpanRelativeTo<'static>
    ///     (span.rs:5724-5728; the From<&Zoned> arm span.rs:5718-5722
    ///     is pruned, prune 3).
    pub exec fn from_datetime(dt: DateTime) -> (r: SpanRel)
        ensures
            r.kind is Civil,
            match r.kind {
                SeatRelKind::Civil(dt2) => dt2 == dt,
                SeatRelKind::DaysAre24Hours => false,
            },
    {
        SpanRel { kind: SeatRelKind::Civil(dt) }
    }

    /// Origin Rust: fn to_relative(&self, unit: Unit)
    ///     -> Result<Option<Relative<'a>>, Error> (span.rs:5684-5708)
    /// Upstream doc (span.rs:5666-5677, quoted sentence by sentence):
    ///   Converts this public API relative datetime into a more
    ///   versatile internal representation of the same concept.
    ///   The unit given should be the maximal non-zero unit present
    ///   in the operation. (Which might involve two spans, in which
    ///   case, it is the maximal non-zero unit across both spans.)
    ///   Basically, the internal `Relative` type is `Cow` which means
    ///   it isn't `Copy`. But it can present a more uniform API. The
    ///   public API type doesn't have `Cow` so that it can be `Copy`.
    ///   We also take this opportunity to attach some convenient
    ///   data, such as a timestamp when the relative datetime type
    ///   is civil.
    ///   This can return `None` if this `SpanRelativeTo` isn't
    ///   actually a datetime but a "marker" indicating some unit
    ///   (like days) should be treated as invariant. Or `None` is
    ///   returned when the given unit is always invariant (hours or
    ///   smaller).
    ///   In effect, given that `unit` is the maximal unit involved,
    ///   `None` is returned when it's safe to [take] all units
    ///   in the spans can be interpreted as invariant (even if they
    ///   can sometimes be varying).
    ///   # Errors
    ///   If there was a problem doing this conversion, then an error
    ///   is returned. In practice, this only occurs for a civil
    ///   datetime near the civil datetime minimum and maximum values.
    /// Body verdict (span.rs:5685-5707): the `!unit.is_variable()`
    /// arm returns Ok(None) for EVERY kind first; the Civil arm
    /// returns the datetime (the RelativeCivil timestamp field is
    /// the J9 batch's prune 3 and does not reappear here); the
    /// DaysAre24Hours arm errors precisely on Year | Month
    /// (UnitConfigError::RelativeYearOrMonthGivenDaysAre24Hours,
    /// span.rs:5699-5705).
    pub exec fn to_relative(&self, unit: Unit)
        -> (r: Option<Option<DateTime>>)
        ensures
            match self.kind {
                SeatRelKind::Civil(dt) =>
                    if seat_unit_is_variable(unit) {
                        r == Option::Some(Option::Some(dt))
                    } else {
                        r == Option::Some(Option::None)
                    },
                SeatRelKind::DaysAre24Hours =>
                    if unit is Year || unit is Month {
                        if seat_unit_is_variable(unit) {
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
            SeatRelKind::Civil(dt) => {
                Option::Some(Option::Some(dt))
            }
            SeatRelKind::DaysAre24Hours => {
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
// (1) month_add_one (civil/date.rs:3391-3408) and the Month/Year
// borrow-correction group of DateDifference::since_with_largest_unit
// (date.rs:2761-2828).
// ===========================================================================

/// The Sign::from(x) contract at the seat's int width: the -1/0/+1
/// direction of a machine i32 (bounds.rs:1034-1044's from_ordinals
/// family; the three-way case is upstream's Sign::from).
pub open spec fn seat_npz(x: int) -> int {
    if x < 0 {
        0 - 1
    } else if x == 0 {
        0
    } else {
        1
    }
}

/// Exec twin of seat_npz (the exec-side sign tests all spell through
/// this per pitfall 53-54 discipline: bind the match to a local
/// before any guard).
pub exec fn seat_npz_exec(x: i32) -> (r: i32)
    ensures
        (r as int) == seat_npz(x as int),
{
    if x < 0 {
        0 - 1i32
    } else if x == 0 {
        0i32
    } else {
        1i32
    }
}

/// Origin Rust: fn month_add_one(mut year: i16, mut month: i8,
///     delta: Sign) -> Result<(i16, i8), Error>
///     (date.rs:3391-3408) -- the private borrow mover of
///     since_with_largest_unit's day correction (date.rs:2795-2810).
/// Upstream doc (date.rs:3389-3390):
///   Adds or subtracts `sign` from the given `year`/`month`.
///   If month overflows in either direction, then the `year`
///   returned is adjusted as appropriate.
/// Upstream body, verbatim:
///     month += delta.as_i8();
///     if month < 1 {
///         year -= 1;
///         month += 12;
///     } else if month > 12 {
///         year += 1;
///         month -= 12;
///     }
///     let year = b::Year::check(year)?;
///     Ok((year, month))
/// (b::Year::check is the year_iv range gate -- the None face below.)
pub exec fn seat_month_add_one(
    year: i16,
    month: i8,
    delta: Sign,
) -> (r: Option<(i16, i8)>)
    requires
        year_iv().contains(year as int),
        month >= 1,
        month <= 12,
        delta is Positive || delta is Negative,
    ensures
        match r {
            Option::Some((y2, m2)) =>
                year_iv().contains(y2 as int)
                    && 1 <= m2
                    && m2 <= 12
                    && ((delta is Positive)
                        ==> ((m2 as int)
                            == (month as int) + 1
                            || ((month as int) == 12
                                && (m2 as int) == 1
                                && (y2 as int)
                                    == (year as int) + 1)))
                    && ((delta is Negative)
                        ==> ((m2 as int)
                            == (month as int) - 1
                            || ((month as int) == 1
                                && (m2 as int) == 12
                                && (y2 as int)
                                    == (year as int) - 1)))
                    && ((delta is Positive)
                        && !((month as int) == 12)
                        ==> (y2 as int) == (year as int))
                    && ((delta is Negative)
                        && !((month as int) == 1)
                        ==> (y2 as int) == (year as int)),
            Option::None =>
                !year_iv().contains(
                    (if (month as int) == 12
                        && delta is Positive {
                        year as int + 1
                    } else if (month as int) == 1
                        && delta is Negative {
                        year as int - 1
                    } else {
                        year as int
                    }) as int,
                ),
        },
{
    let dy: i8 = Sign::as_i8(delta);
    let mut month2: i8 = month + dy;
    let mut year2: i16 = year;
    if month2 < 1 {
        year2 = year2 - 1;
        month2 = month2 + 12;
    } else if month2 > 12 {
        year2 = year2 + 1;
        month2 = month2 - 12;
    }
    // b::Year::check(year) (date.rs:3406): the plain machine gate --
    // the moved year stays in range by the callers' discharge.
    if -9999 > year2 || year2 > 9999 {
        return Option::None;
    }
    Option::Some((year2, month2))
}

// ===========================================================================
// The Month/Year lane model of DateDifference::since_with_largest_unit
// (date.rs:2761-2828): the borrow-correction group mirrored at int
// width, then the until/since faces over it.
// ===========================================================================

/// The upstream sign derivation of the borrow block (date.rs:2786-
/// 2790):
///     let sign = if years != 0 { Sign::from(years) }
///                else { Sign::from(months) };
/// spelled at the seat's int width.
pub open spec fn seat_myl_sg(d1: Date, d2: Date) -> int {
    let years0: int = (d2.year as int) - (d1.year as int);
    let months0: int = (d2.month as int) - (d1.month as int);
    if years0 != 0 {
        seat_npz(years0)
    } else {
        seat_npz(months0)
    }
}

/// The borrow move of date.rs:2795-2815 (month_add_one + the
/// day_correct / days_in_month2 reassignment), mirrored at int
/// width: (y2m, m2m, day_correct, dim2) of the moved calendar pair.
/// The upstream block, verbatim, with the branches marked:
///     if Sign::from(days) == -sign {
///         let (y, m) = month_add_one(year2, month2, -sign).unwrap();
///         year2 = y; month2 = m;
///         years = year2 - year1;
///         months = i32::from(month2 - month1);
///         let original_days_in_month1 = days_in_month2;
///         days_in_month2 = jcore::civil::days_in_month(year2, month2);
///         day_correct = if sign.is_negative() {
///             -original_days_in_month1
///         } else {
///             days_in_month2
///         };
///     }
pub open spec fn seat_myl_move(d1: Date, d2: Date)
    -> (int, int, int, int)
{
    let y2: int = d2.year as int;
    let m2: int = d2.month as int;
    let da1: int = d1.day as int;
    let da2: int = d2.day as int;
    let years0: int = (d2.year as int) - (d1.year as int);
    let months0: int = (d2.month as int) - (d1.month as int);
    let days0: int = da2 - da1;
    let dim0: int = days_in_month_spec(y2, m2);
    if years0 != 0 || months0 != 0 {
        let sg: int = seat_myl_sg(d1, d2);
        if seat_npz(days0) == 0 - sg {
            let mm: int = m2 - sg;
            let y2m: int = if mm < 1 {
                y2 - 1
            } else if mm > 12 {
                y2 + 1
            } else {
                y2
            };
            let m2m: int = if mm < 1 {
                mm + 12
            } else if mm > 12 {
                mm - 12
            } else {
                mm
            };
            let dim2: int = days_in_month_spec(y2m, m2m);
            let dayc: int = if sg < 0 {
                0 - dim0
            } else {
                dim2
            };
            (y2m, m2m, dayc, dim2)
        } else {
            (y2, m2, 0, dim0)
        }
    } else {
        (y2, m2, 0, dim0)
    }
}

/// The full uncollapsed Month/Year lane triple of
/// since_with_largest_unit (date.rs:2816-2826), mirrored at int
/// width: (years, months, days) AFTER the borrow move and the
/// second (month-carry) correction, BEFORE the largest==Month
/// collapse (which carries upstream's checked_add, date.rs:2823-2826:
///     let day0_trunc = i32::from(day1.min(days_in_month2));
///     days = i32::from(day2) - day0_trunc
///            + i32::from(day_correct);
///     if years != 0 {
///         months = i32::from(month2 - month1);
///         if Sign::from(months) == -sign {
///             let month_correct = sign * 12;
///             year2 -= sign.as_i16();
///             years = year2 - year1;
///             months = i32::from(month2 - month1) + month_correct;
///         }
///     }
/// ).
pub open spec fn seat_myl_parts(d1: Date, d2: Date)
    -> (int, int, int)
{
    let (y2m, m2m, dayc, dim2) = seat_myl_move(d1, d2);
    let y1i: int = d1.year as int;
    let m1: int = d1.month as int;
    let da1: int = d1.day as int;
    let da2: int = d2.day as int;
    let sg: int = seat_myl_sg(d1, d2);
    let years1: int = y2m - y1i;
    let months1: int = m2m - m1;
    let day0t: int = if da1 < dim2 {
        da1
    } else {
        dim2
    };
    let daysv: int = da2 - day0t + dayc;
    let (yrs2, mos2): (int, int) = if years1 != 0 {
        if seat_npz(months1) == 0 - sg {
            (y2m - sg - y1i, months1 + 12 * sg)
        } else {
            (years1, months1)
        }
    } else {
        (years1, months1)
    };
    (yrs2, mos2, daysv)
}

/// The per-field direction of the assembled span: the sign the
/// Span setter chain assigns is the direction of the first nonzero
/// lane in (years, months, days) order -- the J5 sp_set_* sign
/// tables -- and the Temporal balance property keeps every lane on
/// the same side of zero (the exec arms prove it per branch).
pub open spec fn seat_my_dir(yv: int, mv: int, dv: int) -> int {
    if yv != 0 {
        seat_npz(yv)
    } else if mv != 0 {
        seat_npz(mv)
    } else {
        seat_npz(dv)
    }
}

/// The shared result-row face of the Month/Year lanes over a given
/// signed triple: the field pins (magnitudes), the direction sign
/// row, and the zero row.
pub open spec fn seat_my_face_rows(
    yv: int,
    mv: int,
    dv: int,
    s: &Span,
) -> bool {
    sp_field_inv(s)
        && sp_zero_sign_ok(s)
        && sp_flags_ok(s)
        && s.weeks == 0
        && s.hours == 0
        && s.minutes == 0
        && s.seconds == 0
        && s.milliseconds == 0
        && s.microseconds == 0
        && s.nanoseconds == 0
        && (s.years as int) == (if yv >= 0 { yv } else { 0 - yv })
        && (s.months as int) == (if mv >= 0 { mv } else { 0 - mv })
        && (s.days as int) == (if dv >= 0 { dv } else { 0 - dv })
        && (seat_my_dir(yv, mv, dv) == 1
            ==> (s.sign is Positive
                && yv >= 0
                && mv >= 0
                && dv >= 0))
        && (seat_my_dir(yv, mv, dv) == 0 - 1
            ==> (s.sign is Negative
                && yv <= 0
                && mv <= 0
                && dv <= 0))
        && (seat_my_dir(yv, mv, dv) == 0
            ==> (yv == 0 && mv == 0 && dv == 0
                && s.sign is Zero
                && sp_all_zero(s)))
}

/// The until-face over the collapsed lanes: largest == Month
/// carries upstream's checked_add collapse (date.rs:2823-2826:
///     if largest == Unit::Month && years != 0 {
///         months = b::SpanMonths::checked_add(
///             months, i32::from(years) * 12)?;
///         years = 0;
///     }
/// ); the triple asked of the value face is the collapsed one.
pub open spec fn seat_my_collapsed(
    largest: Unit,
    yv: int,
    mv: int,
    dv: int,
) -> (int, int, int) {
    if largest is Month && yv != 0 {
        (0, mv + 12 * yv, dv)
    } else {
        (yv, mv, dv)
    }
}

/// The full result face of the Month-configured until/since seats.
/// On Some: the collapsed lane triple drives the value rows; on
/// None: the largest == Month collapse total lands outside
/// b::SpanMonths's range (upstream's checked_add, the only fallible
/// step of the whole group -- the rest is upstream's own
/// "It is guaranteed that if one provides a date with the default
/// [DateDifference] configuration, then this routine will never
/// fail" (date.rs:1516-1518) carrying over to the Week config, and
/// the Month/Year config keeping exactly this one error lane).
pub open spec fn seat_my_lane_face(
    d1: Date,
    d2: Date,
    largest: Unit,
    yv: int,
    mv: int,
    dv: int,
    r: &Option<Span>,
) -> bool {
    let (yv2, mv2, dv2) = seat_my_collapsed(largest, yv, mv, dv);
    let total: int = mv + 12 * yv;
    let ok: bool = !(largest is Month && yv != 0)
        || (0 - 239_976) <= total && total <= 239_976;
    match r {
        Option::Some(s) =>
            ok && seat_my_face_rows(yv2, mv2, dv2, s),
        Option::None => !ok,
    }
}

/// The direction-consistency claim of the lane parts (the Temporal
/// balance property of the borrow-correction group: every nonzero
/// lane of the final triple sits on the same side of zero as the
/// upstream `sign` variable, date.rs:2786-2826), plus the per-lane
/// magnitude facts the setter chain needs. Stated at spec width so
/// the exec arms consume it after bridging their machine lanes.
pub open spec fn seat_my_parts_ok_spec(
    d1: Date,
    d2: Date,
    largest: Unit,
) -> bool {
    let (yv, mv, dv): (int, int, int) = seat_myl_parts(d1, d2);
    let (yv2, mv2, dv2): (int, int, int)
        = seat_my_collapsed(largest, yv, mv, dv);
    (seat_my_dir(yv2, mv2, dv2) == 1
        ==> (yv2 >= 0 && mv2 >= 0 && dv2 >= 0))
        && (seat_my_dir(yv2, mv2, dv2) == 0 - 1
            ==> (yv2 <= 0 && mv2 <= 0 && dv2 <= 0))
        && (seat_my_dir(yv2, mv2, dv2) == 0
            ==> (yv2 == 0 && mv2 == 0 && dv2 == 0))
        && ((0 - 19998) <= yv && yv <= 19998)
        && ((0 - 239_976) <= mv && mv <= 239_976)
        && ((0 - 62) <= dv && dv <= 62)
}

/// The proof of seat_my_parts_ok_spec, by the upstream sign tree:
/// the day lane from the borrow structure (date.rs:2808-2826), the
/// years lane from the month_add_one move, the months lane from the
/// month-carry correction.
proof fn seat_lemma_my_direction(d1: Date, d2: Date, largest: Unit)
    requires
        valid_date(d1),
        valid_date(d2),
    ensures
        seat_my_parts_ok_spec(d1, d2, largest),
{
    let y1: int = d1.year as int;
    let m1: int = d1.month as int;
    let da1: int = d1.day as int;
    let y2: int = d2.year as int;
    let m2: int = d2.month as int;
    let da2: int = d2.day as int;
    let years0: int = y2 - y1;
    let months0: int = m2 - m1;
    let days0: int = da2 - da1;
    if years0 == 0 && months0 == 0 {
        // the block-skipped lane: (0, 0, days0), trivially balanced.
        assert(seat_myl_move(d1, d2) == (y2, m2, 0,
            days_in_month_spec(y2, m2)));
        let (yv, mv, dv): (int, int, int) = seat_myl_parts(d1, d2);
        assert(yv == 0 && mv == 0 && dv == days0);
        assert(seat_my_collapsed(largest, yv, mv, dv)
            == (0, 0, days0));
        if days0 > 0 {
            assert(seat_my_dir(0, 0, days0) == 1);
        } else if days0 < 0 {
            assert(seat_my_dir(0, 0, days0) == 0 - 1);
        } else {
            assert(seat_my_dir(0, 0, days0) == 0);
        }
    } else {
        let sg: int = seat_myl_sg(d1, d2);
        assert(sg == 1 || sg == 0 - 1);
        if sg == 1 {
            // years0 > 0, or years0 == 0 && months0 > 0
            if years0 != 0 {
                assert(years0 > 0);
                assert(y2 > y1);
            } else {
                assert(months0 > 0);
                assert(m2 > m1);
            }
        } else {
            if years0 != 0 {
                assert(years0 < 0);
                assert(y2 < y1);
            } else {
                assert(months0 < 0);
                assert(m2 < m1);
            }
        }
        let (y2m, m2m, dayc, dim2): (int, int, int, int)
            = seat_myl_move(d1, d2);
        let years1: int = y2m - y1;
        let months1: int = m2m - m1;
        assert(1 <= m2m && m2m <= 12);
        assert(seat_myl_move(d1, d2)
            == (y2m, m2m, dayc, dim2));
        // the day lane (date.rs:2808-2826).
        let day0t: int = if da1 < dim2 { da1 } else { dim2 };
        let dv0: int = da2 - day0t + dayc;
        if seat_npz(days0) == 0 - sg {
            // borrow fired: dayc is the moved-month correction.
            assert(dayc != 0);
            if sg == 1 {
                assert(dayc == dim2);
                assert(dv0 >= da2 - dim2 + dim2);
                assert(da2 >= 1);
                assert(dv0 >= 1);
                assert(y2m <= y2 + 1 && y2m >= y2 - 1);
                assert(months1 == m2m - m1);
            } else {
                assert(dayc == 0
                    - days_in_month_spec(y2, m2));
                assert(da1 >= 1);
                assert(da2
                    <= days_in_month_spec(y2, m2));
                assert(dv0 < 0);
                assert(y2m <= y2 + 1 && y2m >= y2 - 1);
            }
        } else {
            // no borrow: Sign::from(days) != -sign.
            if sg == 1 {
                assert(seat_npz(days0) != 0 - 1);
                assert(days0 >= 0);
                assert(da2 >= da1);
                if da1 < dim2 {
                    assert(day0t == da1);
                    assert(dv0 == days0 + 0);
                } else {
                    assert(day0t == dim2);
                    assert(da2 >= da1);
                    assert(da1 >= dim2);
                    assert(dv0 == da2 - dim2);
                    assert(dv0 >= 0);
                }
            } else {
                assert(seat_npz(days0) != 1);
                assert(days0 <= 0);
                assert(da2 <= da1);
                if da1 < dim2 {
                    assert(day0t == da1);
                    assert(dv0 == days0);
                } else {
                    assert(day0t == dim2);
                    assert(da1 >= dim2);
                    assert(da2 >= 1);
                    assert(dv0 <= days_in_month_spec(y2, m2)
                        - dim2);
                    assert(dv0 <= 0);
                }
            }
        }
        // magnitude bounds of the pre-correction lanes.
        assert((0 - 19998) <= years1 && years1 <= 19998);
        assert((0 - 11) <= months1 && months1 <= 11);
        assert((0 - 62) <= dv0 && dv0 <= 62);
        // the years lane and the month-carry correction.
        let (yrs2, mos2, dv2r): (int, int, int)
            = seat_myl_parts(d1, d2);
        assert(dv2r == dv0);
        if years1 != 0 {
            if seat_npz(months1) == 0 - sg {
                // correction fires: month1b carries, year moves one
                // more step toward d1's side.
                if sg == 1 {
                    assert(months1 < 0);
                    assert(months1 >= 0 - 11);
                    assert(mos2 == months1 + 12);
                    assert(mos2 >= 1);
                    // years1 and sg agree in sign here (years1 > 0
                    // when the block's sign is positive), so the
                    // corrected years lane stays nonnegative.
                    assert(years1 > 0);
                    assert(yrs2 == years1 - 1);
                    assert(yrs2 >= 0);
                    assert(dv2r >= 0);
                } else {
                    assert(months1 > 0);
                    assert(months1 <= 11);
                    assert(mos2 == months1 - 12);
                    assert(mos2 <= 0 - 1);
                    assert(years1 < 0);
                    assert(yrs2 == years1 + 1);
                    assert(yrs2 <= 0);
                    // the day lane rides on the same-side-or-zero
                    // table: dv0 == 0 is reachable when d1 and d2
                    // share their day-of-month and the direction is
                    // negative (the face row's `<=`).
                    assert(dv2r <= 0);
                }
                assert((0 - 19998) <= yrs2 && yrs2 <= 19998);
                assert((0 - 239_976) <= mos2
                    && mos2 <= 239_976);
            } else {
                // correction does not fire.
                assert(yrs2 == years1);
                assert(mos2 == months1);
                if sg == 1 {
                    // years1's sign is positive-or-zero for a
                    // positive block sign: years0 > 0 keeps years1
                    // in [.. ], and years0 == 0 means the move
                    // never wraps (m2 >= 2), so years1 == 0.
                    if years0 != 0 {
                        // wrapped years0-1 or plain years0
                        assert(years1 >= 0);
                    } else {
                        assert(m2 >= 2);
                        assert(m2m == m2 - 1);
                        assert(y2m == y2);
                        assert(years1 == 0);
                    }
                    assert(months1 >= 0 || years1 == 0);
                    if years1 == 0 {
                        // block sign comes from months0 > 0 and
                        // the moved months lane stays nonnegative.
                        assert(years0 == 0 && months0 > 0);
                        assert(mos2 == m2m - m1);
                        assert(m2m >= 1);
                        assert(mos2 >= 0 - 11);
                        if mos2 < 0 {
                            assert(m2m < m1);
                            assert(m2 - 1 < m1);
                            assert(months0 <= 0);
                            assert(months0 > 0);
                            assert(false);
                        }
                        assert(mos2 >= 0);
                    } else {
                        // years signed the block; months1 cannot be
                        // negative here (the correction would have
                        // fired), so it is positive or zero.
                        assert(seat_npz(months1) != 0 - 1);
                        assert(months1 >= 0);
                    }
                } else {
                    if years0 != 0 {
                        assert(years1 <= 0);
                    } else {
                        assert(m2 <= 11);
                        assert(m2m == m2 + 1);
                        assert(y2m == y2);
                        assert(years1 == 0);
                    }
                    if years1 == 0 {
                        assert(years0 == 0 && months0 < 0);
                        assert(mos2 == m2m - m1);
                        if mos2 > 0 {
                            assert(m2m > m1);
                            // for a months-signed negative block,
                            // the moved month is m2+1 <= 12 and m1
                            // is strictly above months0's sign side
                            assert(false);
                        }
                        assert(mos2 <= 0);
                    } else {
                        assert(seat_npz(months1) != 1);
                        assert(months1 <= 0);
                    }
                }
                if sg == 1 {
                    assert(dv2r >= 0);
                    assert(yrs2 >= 0 && mos2 >= 0
                        && ((yrs2 == 0 && mos2 == 0) || true));
                } else {
                    assert(dv2r <= 0);
                    assert(yrs2 <= 0 && mos2 <= 0);
                }
            }
        } else {
            // years1 == 0: no correction, and the block sign came
            // from the months lane (or the move neutralized it with
            // the months lane staying on the sign's side).
            assert(yrs2 == 0);
            assert(mos2 == months1);
            if sg == 1 {
                // sign comes from months0 > 0 (years0 == 0 means no
                // wrap when sign is positive), or years0 > 0 wrapped
                // down to exactly zero -- which forces m2m = 12 and
                // months1 = 12 - m1 >= 0.
                if years0 == 0 {
                    assert(months0 > 0);
                    assert(m2 >= 2);
                    assert(y2m == y2);
                    if seat_npz(days0) == 0 - sg {
                        assert(m2m == m2 - 1);
                        assert(months1 == months0 - 1);
                        assert(months1 >= 0);
                    } else {
                        assert(m2m == m2);
                        assert(months1 == months0);
                        assert(months1 > 0);
                    }
                } else {
                    // years0 > 0 wrapped: y2m = y2 - 1 (m2 == 1),
                    // m2m = 12, months1 = 12 - m1 >= 0.
                    assert(y2m == y2 - 1);
                    assert(m2m == 12);
                    assert(months1 >= 0);
                    assert(dv2r >= 0);
                }
                assert(dv2r >= 0);
            } else {
                if years0 == 0 {
                    assert(months0 < 0);
                    assert(m2 <= 11);
                    assert(y2m == y2);
                    if seat_npz(days0) == 0 - sg {
                        assert(m2m == m2 + 1);
                        assert(months1 == months0 + 1);
                        assert(months1 <= 0);
                    } else {
                        assert(months1 == months0);
                        assert(months1 < 0);
                    }
                } else {
                    assert(y2m == y2 + 1);
                    assert(m2m == 1);
                    assert(months1 <= 0);
                    assert(dv2r <= 0);
                }
                assert(dv2r <= 0);
            }
        }
        // collapse keeps the lanes on the same side (the total is
        // the same-signed years*12 + months sum).
        let (yv2, mv2, dvc): (int, int, int)
            = seat_my_collapsed(largest, yrs2, mos2, dv2r);
        if largest is Month && yrs2 != 0 {
            assert(yv2 == 0 && mv2 == mos2 + 12 * yrs2
                && dvc == dv2r);
            if yrs2 > 0 {
                assert(yrs2 >= 1);
                assert(mos2 >= 0);
                assert(mv2 >= 0);
            } else {
                assert(yrs2 <= 0 - 1);
                assert(mos2 <= 0);
                assert(mv2 <= 0);
            }
        }
        // seat_my_dir rows over the collapsed triple.
        let dired: int = seat_my_dir(yv2, mv2, dvc);
        if dired == 1 {
            assert(yv2 >= 0 && mv2 >= 0 && dvc >= 0);
        } else if dired == 0 - 1 {
            assert(yv2 <= 0 && mv2 <= 0 && dvc <= 0);
        } else {
            assert(yv2 == 0 && mv2 == 0 && dvc == 0);
        }
    }
}

/// Origin Rust: fn DateDifference::since_with_largest_unit(&self,
///     d1: Date) -> Result<Span, Error> (date.rs:2725-2829) at the
/// largest = Month / Year lanes (the Day/Week lanes are the J9
/// batch's rel_date_until_span / rel_date_since_span faces), and
/// the body of Date::until (date.rs:1623-1634):
///     let args: DateDifference = other.into();
///     let span = args.since_with_largest_unit(self)?;
///     if args.rounding_may_change_span() {
///         span.round(args.round.relative(self))
///     } else {
///         Ok(span)
///     }
/// -- this seat materializes the until wrapper over the default
/// (Unit, Date)-configured DateDifference with largest = Month or
/// Year (smallest stays Day, so rounding_calendar_only_may_change_
/// span is false and the round call never fires, mirror of the J9
/// Day/Week precedent).
/// Upstream doc (date.rs:1480-1489, quoted):
///   Returns a span representing the elapsed time from this date
///   until the given `other` date.
///   When `other` occurs before this date, then the span returned will
///   be negative.
///   Depending on the input provided, the span returned is rounded. It
///   may also be balanced up to bigger units than the default. By
///   default, the span returned is balanced such that the biggest
///   and smallest possible unit is days.
///   This operation is configured by providing a [`DateDifference`]
///   value. Since this routine accepts anything that implements
///   `Into<DateDifference>`, once can pass a `Date` directly. One
///   can also pass a `(Unit, Date)`, where `Unit` is treated as
///   [`DateDifference::largest`].
/// The # Properties doc (date.rs:1492-1498, quoted in full):
///   It is guaranteed that if the returned span is subtracted from
///   `other`, and if no rounding is requested, and if the largest unit
///   request is at most `Unit::Day`, then the original date will be
///   returned.
///   This routine is equivalent to `self.since(other).map(|span| -span)`
///   if no rounding options are set. If rounding options are set, then
///   it's equivalent to
///   `self.since(other_without_rounding_options).map(|span| -span)`,
///   followed by a call to [`Span::round`] with the appropriate rounding
///   options set. This is because the negation of a span can result in
///   different rounding results depending on the rounding mode.
/// The never-fail # Errors doc (date.rs:1500-1518, quoted):
///   # Errors
///   An error can occur if `DateDifference` is misconfigured. For
///   example, if the smallest unit provided is bigger than the
///   largest unit.
///   It is guaranteed that if one provides a date with the default
///   [`DateDifference`] configuration, then this routine will never
///   fail.
/// -- with the Month-largest config keeping exactly one fallible
/// step: the SpanMonths collapse (the seat's None face above).
pub exec fn seat_date_until_my(
    d1: Date,
    d2: Date,
    largest: Unit,
) -> (r: Option<Span>)
    requires
        valid_date(d1),
        valid_date(d2),
        largest is Month || largest is Year,
    ensures
        match seat_myl_parts(d1, d2) {
            (yv, mv, dv) =>
                seat_my_lane_face(d1, d2, largest, yv, mv, dv, &r),
        },
{
    // The straight-line machine mirror of date.rs:2779-2826, at i32
    // width (upstream's i16 year arithmetic is range-provable: the
    // year differences are bounded by 9999*2).
    let y1i: i32 = d1.year as i32;
    let m1i: i32 = d1.month as i32;
    let da1: i32 = d1.day as i32;
    let y2i: i32 = d2.year as i32;
    let m2i: i32 = d2.month as i32;
    let da2: i32 = d2.day as i32;
    let years: i32 = y2i - y1i;
    let months: i32 = m2i - m1i;
    let mut days: i32 = da2 - da1;
    proof {
        // the spec/machine cast bridges (every lane below reads
        // through these).
        assert((y1i as int) == (d1.year as int));
        assert((m1i as int) == (d1.month as int));
        assert((da1 as int) == (d1.day as int));
        assert((y2i as int) == (d2.year as int));
        assert((m2i as int) == (d2.month as int));
        assert((da2 as int) == (d2.day as int));
    }
    if years == 0 && months == 0 {
        // the block skip (date.rs:2781): both calendar lanes are
        // zero, the day difference carries the whole span.
        if days == 0 {
            proof {
                assert(seat_myl_move(d1, d2)
                    == (y2i as int, m2i as int, 0,
                        days_in_month_spec(
                            y2i as int, m2i as int)));
                assert(seat_myl_parts(d1, d2) == (0, 0, 0));
                seat_lemma_my_direction(d1, d2, largest);
            }
            return Option::Some(Span::new());
        }
        proof {
            assert(seat_myl_move(d1, d2)
                == (y2i as int, m2i as int, 0,
                    days_in_month_spec(
                        y2i as int, m2i as int)));
            assert(seat_myl_parts(d1, d2)
                == (0, 0, days as int));
            seat_lemma_my_direction(d1, d2, largest);
            assert(-30int <= days as int
                && days as int <= 30int);
        }
        let s0: Span = Span::new();
        let s3: Span = s0.days(days as i64);
        return Option::Some(s3);
    }
    let sg: i32 = if years != 0 {
        seat_npz_exec(years)
    } else {
        seat_npz_exec(months)
    };
    // date.rs:2791-2792: the d2 calendar pair and its month size.
    let mut year2: i32 = y2i;
    let mut month2: i32 = m2i;
    let mut dim2: i32 = d2.days_in_month() as i32;
    let dim0: i32 = dim2;
    let mut dayc: i32 = 0;
    let sg_pos: bool = sg == 1;
    let mut borrowed: bool = false;
    if seat_npz_exec(days) == 0 - sg {
        // date.rs:2795-2810: month_add_one(year2, month2, -sign)
        // with the upstream justification of the unwrap (quoted
        // verbatim from the comment right above the call,
        // date.rs:2779-2793):
        //   // Justifying this operation as infallible is quite
        //   // tricky. It can only fail in two cases: year2=9999,
        //   // month2=12 and sign=Negative or year2=-9999, month2=1
        //   // and sign=Positive. In both of those cases, year will
        //   // overflow its boundaries.
        //   // However, neither case is possible. Namely, whenever
        //   // sign=Negative, it follows that either `year1 > year2`
        //   // or `month1 > month2`. But there are no such values
        //   // of `year1` or `month1` that satisfy `year1 > 9999 or
        //   // month1 > 12` because `9999` is the maximum legal year
        //   // value.
        //   // A similar argument follows for sign=Positive and
        //   // `year2=-9999` and `month2=1`. Therefore, this
        //   // `unwrap()` is okay.
        borrowed = true;
        let dy: Sign = if sg_pos {
            Sign::Negative
        } else {
            Sign::Positive
        };
        proof {
            // the two-case argument, mirrored at the seat's widths.
            if sg < 0 {
                if years != 0 {
                    assert((y2i as int) < (y1i as int));
                    // y2 <= 9998, so the wrap-up reaches only 9999.
                    assert((y2i as int) <= 9998);
                } else {
                    assert((months as int) < 0);
                    assert((m2i as int) < (m1i as int));
                    // month2 + 1 never wraps.
                    assert((m2i as int) <= 11);
                }
            } else {
                if years != 0 {
                    assert((y2i as int) > (y1i as int));
                    assert((y2i as int) >= -9998);
                } else {
                    assert((months as int) > 0);
                    assert((m2i as int) > (m1i as int));
                    assert((m2i as int) >= 2);
                }
            }
        }
        let moved: Option<(i16, i8)> = seat_month_add_one(
            year2 as i16,
            month2 as i8,
            dy,
        );
        let (yv2, mv2): (i16, i8) = match moved {
            Option::Some(v) => v,
            Option::None => {
                proof {
                    // the moved target stays inside year_iv by the
                    // case argument above; the None face says the
                    // target is out of the interval, so the arm is
                    // dead.
                    let mmi: int = (month2 as int)
                        - (if dy is Positive {
                            1
                        } else {
                            0 - 1
                        });
                    let ytarget: int = if mmi < 1 {
                        year2 as int - 1
                    } else if mmi > 12 {
                        year2 as int + 1
                    } else {
                        year2 as int
                    };
                    assert(year_iv().contains(ytarget));
                    assert(false);
                }
                unreachable!()
            }
        };
        year2 = yv2 as i32;
        month2 = mv2 as i32;
        assert(1 <= month2 && month2 <= 12);
        // date.rs:2803-2810: the moved month's size and the day
        // correction.
        dim2 = days_in_month(year2 as i16, month2 as i8) as i32;
        dayc = if sg_pos { dim2 } else { 0 - dim0 };
    }
    // date.rs:2808-2809
    let day0t: i32 = if da1 < dim2 { da1 } else { dim2 };
    days = da2 - day0t + dayc;
    proof {
        // the spec/machine mirror of the borrow move and the day
        // lane.
        let (y2m, m2m, daycs, dim2s): (int, int, int, int)
            = seat_myl_move(d1, d2);
        assert((y2m, m2m, daycs, dim2s)
            == seat_myl_move(d1, d2));
        assert((year2 as int) == y2m);
        assert((month2 as int) == m2m);
        assert((dayc as int) == daycs);
        assert((dim2 as int) == dim2s);
        assert((days as int)
            == (d2.day as int)
                - (if (d1.day as int) < dim2s {
                    d1.day as int
                } else {
                    dim2s
                }) + daycs);
    }
    // date.rs:2817-2826: the month-carry correction.
    let mut yrs3: i32 = year2 - y1i;
    let mut mos3: i32 = month2 - m1i;
    if yrs3 != 0 {
        mos3 = month2 - m1i;
        if seat_npz_exec(mos3) == 0 - sg {
            proof {
                // the correction keeps the years lane inside the
                // SpanYears domain: years1 is on the block's sign
                // side (or zero), and the zero case moves exactly
                // one step (yrs3 = +-1).
                let years1i: int = (year2 as int) - (y1i as int);
                let mos1i: int = (month2 as int) - (m1i as int);
                assert((yrs3 as int) == years1i);
                assert((mos3 as int) == mos1i);
                if sg < 0 {
                    assert(seat_npz(mos1i) == 1);
                    assert(mos1i > 0);
                    if years1i < 0 {
                        assert((year2 as int) < (y1i as int));
                        // corrected years = years1 + 1 in
                        // [-19997..0]
                        assert(years1i >= 0 - 19998);
                    } else {
                        assert(years1i == 0);
                        // corrected years = 1
                    }
                } else {
                    assert(seat_npz(mos1i) == 0 - 1);
                    assert(mos1i < 0);
                    if years1i > 0 {
                        assert((year2 as int) > (y1i as int));
                        assert(years1i <= 19998);
                    } else {
                        assert(years1i == 0);
                    }
                }
            }
            mos3 = mos3 + sg * 12;
            year2 = year2 - sg;
            yrs3 = year2 - y1i;
            proof {
                assert(-19998 <= yrs3 && yrs3 <= 19998);
                assert(-239_976 <= mos3 && mos3 <= 239_976);
            }
        }
    } else {
        proof {
            assert((yrs3 as int)
                == ((year2 as int) - (y1i as int)));
            assert((mos3 as int)
                == ((month2 as int) - (m1i as int)));
        }
    }
    // the lane triple of the exec mirrors the uncollapsed spec
    // parts; the direction consistency comes from the sign-tree
    // lemma.
    let lane_years: i32 = yrs3;
    let lane_months: i32 = mos3;
    let lane_days: i32 = days;
    if largest matches Unit::Month && yrs3 != 0 {
        // date.rs:2823-2826: b::SpanMonths::checked_add(months,
        // i32::from(years) * 12)? -- the one fallible step.
        let total: i32 = mos3 + yrs3 * 12;
        proof {
            let (yv, mv, dv): (int, int, int)
                = seat_myl_parts(d1, d2);
            assert((lane_years as int) == yv);
            assert((lane_months as int) == mv);
            assert((lane_days as int) == dv);
        }
        if total < 0 - 239_976 || total > 239_976 {
            proof {
                let (yv, mv, dv): (int, int, int)
                    = seat_myl_parts(d1, d2);
                assert(yv != 0);
                assert((total as int) == mv + 12 * yv);
                assert(!((0 - 239_976int) <= mv + 12 * yv
                    && mv + 12 * yv <= 239_976int));
            }
            return Option::None;
        }
        mos3 = total;
        yrs3 = 0;
    }
    proof {
        let (yv, mv, dv): (int, int, int) = seat_myl_parts(d1, d2);
        assert((lane_years as int) == yv);
        assert((lane_months as int) == mv);
        assert((lane_days as int) == dv);
        let (yv2, mv2, dv2): (int, int, int)
            = seat_my_collapsed(largest, yv, mv, dv);
        if largest is Month && yv != 0 {
            assert(yv2 == 0);
            assert(mv2 == mv + 12 * yv);
            assert((yrs3 as int) == 0);
            assert((mos3 as int) == mv2);
        } else {
            assert((yrs3 as int) == yv2);
            assert((mos3 as int) == mv2);
        }
        assert((days as int) == dv2);
        seat_lemma_my_direction(d1, d2, largest);
        // setter-domain bounds on the collapsed lanes.
        assert(-19998int <= (yrs3 as int)
            && (yrs3 as int) <= 19998int);
        assert(-239_976int <= (mos3 as int)
            && (mos3 as int) <= 239_976int);
        assert(-7_304_484int <= (days as int)
            && (days as int) <= 7_304_484int);
        // the direction consistency rows over the collapsed triple.
        assert(seat_my_dir(yv2, mv2, dv2) == 1
            ==> ((yrs3 as int) >= 0
                && (mos3 as int) >= 0
                && (days as int) >= 0));
        assert(seat_my_dir(yv2, mv2, dv2) == 0 - 1
            ==> ((yrs3 as int) <= 0
                && (mos3 as int) <= 0
                && (days as int) <= 0));
        assert(seat_my_dir(yv2, mv2, dv2) == 0
            ==> (yrs3 == 0 && mos3 == 0 && days == 0));
    }
    // Span::new().years(years).months(months).days(days)
    // (date.rs:2827).
    let s0: Span = Span::new();
    let s1: Span = s0.years(yrs3 as i64);
    let s2: Span = s1.months(mos3 as i64);
    let s3: Span = s2.days(days as i64);
    proof {
        // the chain sign tables: with the direction consistency
        // rows above, the first nonzero setter fixes the global
        // sign and the same-side lanes preserve it (the J5
        // sp_set_* faces), and every field stores its magnitude.
        let (yv, mv, dv): (int, int, int)
            = seat_myl_parts(d1, d2);
        let (yv2, mv2, dv2): (int, int, int)
            = seat_my_collapsed(largest, yv, mv, dv);
        let dired: int = seat_my_dir(yv2, mv2, dv2);
        if dired == 1 {
            assert((yrs3 as int) >= 0);
            if yrs3 > 0 {
                assert(s1.sign is Positive);
            } else {
                assert(s1.sign is Zero);
            }
            if mos3 > 0 {
                assert(s2.sign is Positive);
            } else {
                assert(s2.sign == s1.sign);
            }
            if days > 0 {
                assert(s3.sign is Positive);
            } else {
                assert(s3.sign == s2.sign);
            }
        } else if dired == 0 - 1 {
            assert((yrs3 as int) <= 0);
            if yrs3 < 0 {
                assert(s1.sign is Negative);
            } else {
                assert(s1.sign is Zero);
            }
            if mos3 < 0 {
                assert(s2.sign is Negative);
            } else {
                assert(s2.sign == s1.sign);
            }
            if days < 0 {
                assert(s3.sign is Negative);
            } else {
                assert(s3.sign == s2.sign);
            }
        } else {
            assert(yrs3 == 0 && mos3 == 0 && days == 0);
            assert(sp_all_zero(&s3));
            assert(s3.sign is Zero);
        }
    }
    Option::Some(s3)
}

/// Origin Rust: pub fn since<A: Into<DateDifference>>(
///     self, other: A) -> Result<Span, Error> (date.rs:1627-1670):
///     let args: DateDifference = other.into();
///     let span = -args.since_with_largest_unit(self)?;
///     if args.rounding_may_change_span() {
///         span.round(args.round.relative(self))
///     } else {
///         Ok(span)
///     }
/// Upstream doc (date.rs:1631-1634, quoted):
///   This routine is identical to [`Date::until`], but the order of
///   the parameters is flipped.
///   # Errors
///   This has the same error conditions as [`Date::until`].
/// Upstream doc example (date.rs:1640-1649, quoted):
///   let earlier = date(2006, 8, 24);
///   let later = date(2019, 1, 31);
///   assert_eq!(later - earlier, 4543.days().fieldwise());
///   // Equivalent to:
///   assert_eq!(later.since(earlier).unwrap(), 4543.days().fieldwise());
/// (-- the Day-config rows are the J9 panel's; the Month/Year rows
///  below ride this seat.)
/// -- the since wrapper negates the SAME d1->d2 lane triple the
/// until wrapper returns (args.since_with_largest_unit(self) is the
/// d1 -> config.date span in both wrappers), so the seat's face is
/// the until face over the negated triple.
pub exec fn seat_date_since_my(
    d1: Date,
    d2: Date,
    largest: Unit,
) -> (r: Option<Span>)
    requires
        valid_date(d1),
        valid_date(d2),
        largest is Month || largest is Year,
    ensures
        match seat_myl_parts(d1, d2) {
            (yv, mv, dv) =>
                seat_my_lane_face(
                    d1,
                    d2,
                    largest,
                    0 - yv,
                    0 - mv,
                    0 - dv,
                    &r,
                ),
        },
{
    let u: Option<Span> = seat_date_until_my(d1, d2, largest);
    match u {
        Option::None => Option::None,
        Option::Some(su) => {
            let s: Span = su.negate();
            proof {
                // the negated value sits on the negated triple with
                // the same lane magnitudes (span.rs:1361-1363's
                // Span::negate keeps every magnitude and flips the
                // global sign only).
                let (yv, mv, dv): (int, int, int)
                    = seat_myl_parts(d1, d2);
                let (yv2, mv2, dv2): (int, int, int)
                    = seat_my_collapsed(largest, yv, mv, dv);
                assert(seat_my_collapsed(
                    largest, 0 - yv, 0 - mv, 0 - dv)
                    == (0 - yv2, 0 - mv2, 0 - dv2));
                let dired: int = seat_my_dir(yv2, mv2, dv2);
                assert(seat_my_dir(0 - yv2, 0 - mv2, 0 - dv2)
                    == 0 - dired);
            }
            Option::Some(s)
        }
    }
}

// ===========================================================================
// (2) The compare seat: SpanCompare's Some(relative) arm
// (span.rs:4512-4533).
// ===========================================================================

/// The adjoined config surface (upstream's SpanCompare carries the
/// relative field; the J11 panel's struct is the relative==None
/// core, so this seat's struct adjoins the Option; no derives --
/// SpanCompare/Span upstream is the same non-Copy non-Clone shape).
pub struct SeatSpCompare {
    pub base: SpanCompare,
    pub rel: Option<SpanRel>,
}

/// Origin Rust: impl From<Span> for SpanCompare<'static>
///     (span.rs:4537-4541) -- the relative defaults to None.
pub exec fn seat_spc_from_span(span: Span) -> (r: SeatSpCompare)
    ensures
        r.base.span == span,
        r.rel is None,
{
    SeatSpCompare {
        base: SpanCompare::from_span(span),
        rel: Option::None,
    }
}

/// Origin Rust: pub fn relative<R: Into<SpanRelativeTo<'a>>>(
///     self, relative: R) -> SpanCompare<'a>
///     { SpanCompare { relative: Some(relative.into()), ..self } }
///     (span.rs:4358-4363).
/// Upstream doc (span.rs:4305-4357, quoted in full minus the zoned
/// bullet, prune 3):
///   Set the relative date to use when comparing spans.
///   A relative date is only needed when either span has non-zero
///   units bigger than hours. (If both spans have zero units bigger
///   than hours, then a relative date is not used.)
///   # Errors
///   If a relative date is needed and one wasn't provided, then an
///   error is returned.
///   # Example: this example demonstrates why a relative date is
///   sometimes needed: [the 2024-11-03 Toronto dst example, the zoned
///   rows ride prune 3.]
impl SeatSpCompare {

/// (impl block: the setter / dispatch members; the face fns stay
/// module-top per the impl-scope discipline.)
pub exec fn seat_spc_relative(
    self,
    rel: SpanRel,
) -> (r: SeatSpCompare)
    requires
        sp_field_inv(&self.base.span),
    ensures
        r.base.span == self.base.span,
        r.rel == Option::Some(rel),
{
    SeatSpCompare {
        base: self.base,
        rel: Option::Some(rel),
    }
}

/// Origin Rust: pub fn days_are_24_hours(self) -> SpanCompare<'a>
///     { self.relative(SpanRelativeTo::days_are_24_hours()) }
///     (span.rs:4470-4496, the last setter).
/// Upstream doc example (span.rs:4480-4496, quoted in full):
///   use jiff::{SpanCompare, ToSpan};
///   let span1 = 2.days().hours(12);
///   let span2 = 60.hours();
///   // No relative date provided, which results in an error.
///   assert_eq!(
///       span1.compare(span2).unwrap_err().to_string(),
///       "using unit 'day' in a span or configuration requires that \
///        either a relative reference time be given or \
///        `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate \
///        invariant 24-hour days, but neither were provided",
///   );
///   let ordering = span1.compare(
///       SpanCompare::from(span2).days_are_24_hours(),
///   )?;
///   assert_eq!(ordering, std::cmp::Ordering::Equal);
pub exec fn seat_spc_days_are_24_hours(
    self,
) -> (r: SeatSpCompare)
    requires
        sp_field_inv(&self.base.span),
    ensures
        r.base.span == self.base.span,
        r.rel == Option::Some(
            SpanRel { kind: SeatRelKind::DaysAre24Hours }),
{
    SeatSpCompare {
        base: self.base,
        rel: Option::Some(SpanRel::days_are_24_hours()),
    }
}

} // impl SeatSpCompare

/// The full branch contract of SpanCompare::compare (span.rs
/// :4512-4533), the two-sided three-lane disjunction, module-top
/// per the pitfall-58 discipline:
/// - the None config: the J11 relative==None arm face verbatim
///   (the variable-unit error lane vs the invariant-duration lex
///   ordering);
/// - the DaysAre24Hours marker: the Year/Month error lane
///   (UnitConfigError::RelativeYearOrMonthGivenDaysAre24Hours,
///   span.rs:5699-5705) vs the same invariant-duration ordering;
/// - the Civil config: the invariant-unit lane keeps the same
///   ordering (to_relative returns Ok(None) for an invariant unit
///   under every kind, so the branch that remains at span.rs
///   :4524-4529 fires); the variable-unit region is the
///   Civil-pipeline territory (prune 2's cap: the seats' callers
///   keep it out, and this face states the vacuous None
///   contingency for it).
pub open spec fn seat_spc_face(
    s1: &Span,
    sc: &SeatSpCompare,
    r: &Option<SpOrdering>,
) -> bool {
    let unit: Unit = sp_unit_max(
        sp_span_largest(s1),
        sp_span_largest(&sc.base.span),
    );
    match sc.rel {
        Option::None =>
            spc_compare_none_face(s1, &sc.base.span, r),
        Option::Some(c) =>
            match c.kind {
                SeatRelKind::DaysAre24Hours =>
                    if unit is Year || unit is Month {
                        r == Option::None
                    } else {
                        match r {
                            Option::Some(o) =>
                                spc_ordering_of_totals(
                                    sp_inv_total_nanos(s1),
                                    sp_inv_total_nanos(
                                        &sc.base.span),
                                    *o,
                                ),
                            Option::None => false,
                        }
                    },
                SeatRelKind::Civil(_) =>
                    if seat_unit_is_variable(unit) {
                        // prune 2's cap: callers exclude this
                        // region (the requires below); the face's
                        // claim here is the vacuous contingency.
                        r == Option::None
                    } else {
                        match r {
                            Option::Some(o) =>
                                spc_ordering_of_totals(
                                    sp_inv_total_nanos(s1),
                                    sp_inv_total_nanos(
                                        &sc.base.span),
                                    *o,
                                ),
                            Option::None => false,
                        }
                    },
            },
    }
}

/// Origin Rust: fn compare(self, span: Span)
///     -> Result<Ordering, Error> (span.rs:4506-4534), body
///     verbatim with the seats' lanes marked:
///     let (span1, span2) = (span, self.span);
///     let unit = span1.largest_unit().max(span2.largest_unit());
///     let start = match self.relative {
///         Some(r) => match r.to_relative(unit)? {
///             Some(r) => r,                             // prune 2
///             None => {
///                 let dur1 = span1.to_invariant_duration();
///                 let dur2 = span2.to_invariant_duration();
///                 return Ok(dur1.cmp(&dur2));          // here
///             }
///         },
///         None => {
///             requires_relative_date_err(unit)?;
///             let dur1 = span1.to_invariant_duration();
///             let dur2 = span2.to_invariant_duration();
///             return Ok(dur1.cmp(&dur2));              // J11 here
///         }
///     };
///     let end1 = start.checked_add(span1)?.to_duration();   // prune 2
///     let end2 = start.checked_add(span2)?.to_duration();  // prune 2
///     Ok(end1.cmp(&end2))
/// Upstream # Errors half doc (span.rs:1903-1907, quoted):
///   If either of the spans being compared have a non-zero calendar
///   unit (units bigger than hours), then this routine requires a
///   relative datetime. If one is not provided, then an error is
///   returned.
impl SeatSpCompare {

pub exec fn seat_spc_compare(
    &self,
    s1: &Span,
) -> (r: Option<SpOrdering>)
    requires
        sp_field_inv(s1),
        sp_zero_sign_ok(s1),
        sp_flags_ok(s1),
        sp_field_inv(&self.base.span),
        sp_zero_sign_ok(&self.base.span),
        sp_flags_ok(&self.base.span),
        // prune 2's cap: exclude the Civil-variable region.
        !(match self.rel {
            Option::Some(c) =>
                c.kind is Civil
                    && seat_unit_is_variable(sp_unit_max(
                        sp_span_largest(s1),
                        sp_span_largest(&self.base.span),
                    )),
            Option::None => false,
        }),
    ensures
        seat_spc_face(s1, self, &r),
{
    let u1: Unit = s1.largest_unit();
    let u2: Unit = self.base.span.largest_unit();
    let unit: Unit = sp_unit_max_exec(u1, u2);
    proof {
        assert(u1 == sp_span_largest(s1));
        assert(u2 == sp_span_largest(&self.base.span));
        assert(unit
            == sp_unit_max(sp_span_largest(s1),
                sp_span_largest(&self.base.span)));
    }
    match self.rel {
        Option::None => {
            // the J11 arm, relayed.
            self.base.compare(s1)
        }
        Option::Some(c) => {
            let tr: Option<Option<DateTime>>
                = c.to_relative(unit);
            match tr {
                Option::None => {
                    // the marker + Year/Month error lane
                    // (span.rs:4515-4517's to_relative
                    // ?-return).
                    proof {
                        assert(unit is Year || unit is Month);
                    }
                    Option::None
                }
                Option::Some(Option::Some(_dt)) => {
                    // the Civil-variable pipeline lane (prune 2):
                    // unreachable under the requires cap.
                    proof { assert(false); }
                    unreachable!()
                }
                Option::Some(Option::None) => {
                    // the marker / civil-invariant
                    // intersection with the invariant ordering
                    // (span.rs:4518-4521 == :4524-4529).
                    let dur1: SignedDuration =
                        s1.sp_to_invariant_duration();
                    let dur2: SignedDuration =
                        self.base.span
                            .sp_to_invariant_duration();
                    proof {
                        assert(sd_total_nanos(&dur1)
                            == sp_inv_total_nanos(s1));
                        assert(sd_total_nanos(&dur2)
                            == sp_inv_total_nanos(
                                &self.base.span));
                    }
                    Option::Some(sd_lex_cmp_exec(&dur1, &dur2))
                }
            }
        }
    }
}

} // impl SeatSpCompare

// ===========================================================================
// (3) The total seat: SpanTotal's Some(relative) arm
// (span.rs:4813-4821).
// ===========================================================================

/// The adjoined config surface of SpanTotal (the J11 struct is the
/// relative==None core; upstream's SpanTotal carries the relative
/// field at span.rs:4687-4691; no Copy -- the SpanTotal core's own
/// carried-Span shape makes the config non-Copy here as upstream).
pub struct SeatSpTotal {
    pub base: SpanTotal,
    pub rel: Option<SpanRel>,
}

/// Origin Rust: impl From<Unit> for SpanTotal<'static>
///     (span.rs:4877-4882) -- the relative defaults to None.
pub exec fn seat_spt_from_unit(unit: Unit) -> (r: SeatSpTotal)
    ensures
        r.base.unit == unit,
        r.rel is None,
{
    SeatSpTotal {
        base: SpanTotal::from_unit(unit),
        rel: Option::None,
    }
}

/// Origin Rust: pub fn relative<R: Into<SpanRelativeTo<'a>>>(
///     self, relative: R) -> SpanTotal<'a>
///     { SpanTotal { relative: Some(relative.into()), ..self } }
///     (span.rs:4744-4759).
/// Upstream doc (span.rs:4694-4753, quoted in full minus the zoned
/// rows, prune 3):
///   Set the relative date to use when computing the total.
///   A relative date is only needed when the span has non-zero units
///   bigger than hours. (If the span has zero units bigger than
///   hours, then a relative date is not used.)
///   # Errors
///   If a relative date is needed and one wasn't provided, then an
///   error is returned.
///   If this span has a non-zero calendar unit and the relative
///   datetime given results in overflow, then an error is returned.
///   # Example
///   This example shows the total number of months in a span
///   consisting of 31 days: [2024-03-02 rows; the zoned DST rows and
///   the civil Month-exactness rows ride prune 2.]
impl SeatSpTotal {

pub exec fn seat_spt_relative(
    self,
    rel: SpanRel,
) -> (r: SeatSpTotal)
    ensures
        r.base.unit == self.base.unit,
        r.rel == Option::Some(rel),
{
    SeatSpTotal {
        base: self.base,
        rel: Option::Some(rel),
    }
}

/// Origin Rust: pub fn days_are_24_hours(self) -> SpanTotal<'a>
///     { self.relative(SpanRelativeTo::days_are_24_hours()) }
///     (span.rs:4764-4806).
/// Upstream doc example (span.rs:4774-4802, quoted in full):
///   use jiff::{civil::date, SpanTotal, ToSpan, Unit};
///   let span = 2.days().hours(12);
///   // No relative date provided, which results in an error.
///   assert_eq!(
///       span.total(Unit::Hour).unwrap_err().to_string(),
///       "using unit 'day' in a span or configuration requires that \
///        either a relative reference time be given or \
///        `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate \
///        invariant 24-hour days, but neither were provided",
///   );
///   // If we can [take] all days as 24 hours, then we can assert it:
///   let total = span.total(
///       SpanTotal::from(Unit::Hour).days_are_24_hours(),
///   )?;
///   assert_eq!(total, 60.0);
///   // Or provide a relative datetime, which is preferred if possible:
///   let total = span.total((Unit::Hour, date(2025, 1, 26)))?;
///   assert_eq!(total, 60.0);
/// (the two 60.0 rows are the panel rows below: the marker arm at
///  the ratio (60, 1), and the civil+invariant-unit arm through the
///  same invariant lanes.)
pub exec fn seat_spt_days_are_24_hours(
    self,
) -> (r: SeatSpTotal)
    ensures
        r.base.unit == self.base.unit,
        r.rel == Option::Some(
            SpanRel { kind: SeatRelKind::DaysAre24Hours }),
{
    SeatSpTotal {
        base: self.base,
        rel: Option::Some(SpanRel::days_are_24_hours()),
    }
}

} // impl SeatSpTotal

/// The full branch contract of SpanTotal::total (span.rs:4813-4821),
/// the two-sided three-lane disjunction, in the J11 exact-rational
/// value shape (SpTotalRatio), module-top per the pitfall-58
/// discipline:
/// - the None config: the J11 relative==None arm face verbatim;
/// - the DaysAre24Hours marker: the Year/Month error lane vs
///   total_invariant's ratio;
/// - the Civil config: the invariant-unit lane keeps the same
///   ratio; the variable-unit region is prune 2's cap (with the
///   vacuous contingency stated, as in seat_spc_face).
pub open spec fn seat_spt_face(
    st: &SeatSpTotal,
    span: &Span,
    r: &Option<SpTotalRatio>,
) -> bool {
    let unit: Unit = sp_unit_max(st.base.unit, sp_span_largest(span));
    match st.rel {
        Option::None =>
            match r {
                Option::Some(ratio) =>
                    spt_config_ok(&st.base, span)
                        && spt_total_inv_face(
                            st.base.unit, span, ratio),
                Option::None => !(spt_config_ok(&st.base, span)),
            },
        Option::Some(c) =>
            match c.kind {
                SeatRelKind::DaysAre24Hours =>
                    if unit is Year || unit is Month {
                        r == Option::None
                    } else {
                        match r {
                            Option::Some(ratio) =>
                                spt_total_inv_face(
                                    st.base.unit, span, ratio),
                            Option::None => false,
                        }
                    },
                SeatRelKind::Civil(_) =>
                    if seat_unit_is_variable(unit) {
                        // prune 2's cap: vacuous contingency.
                        r == Option::None
                    } else {
                        match r {
                            Option::Some(ratio) =>
                                spt_total_inv_face(
                                    st.base.unit, span, ratio),
                            Option::None => false,
                        }
                    },
            },
    }
}

/// Origin Rust: fn total(self, span: Span) -> Result<f64, Error>
///     (span.rs:4813-4862), body verbatim with the seats' lanes
///     marked:
///     let max_unit = self.unit.max(span.largest_unit());
///     let relative = match self.relative {
///         Some(r) => match r.to_relative(max_unit)? {
///             Some(r) => r,                     // splice 2
///             None => {
///                 return Ok(self.total_invariant(span));  // here
///             }
///         },
///         None => {
///             requires_relative_date_err(max_unit)?;
///             return Ok(self.total_invariant(span));  // J11 here
///         }
///     };
///     let relspan = relative.into_relative_span(self.unit, span)?;  // prune 2
///     [...the 123,456,789 seconds and DST measurement tails...]
/// Upstream doc quotes: the # Errors half of Span::total
/// (span.rs:2033-2048) is attached at the J11 face and carries the
/// marker sentence: "Callers may use
/// [`SpanArithmetic::days_are_24_hours`] as a special marker instead
/// of providing a relative civil date to indicate that all days
/// should be 24 hours long. This also results in treating all weeks
/// as seven 24 hour days (168 hours)." -- NOTE the doc says
/// `SpanArithmetic` here as well: the config surface for the three
/// marker seats is SpanTotal/SpanCompare's own (the J11 finding-13
/// companion sites, span.rs:2007, :1910 and round's :2189; recorded
/// as this batch's class-3 doc candidate, not filed).
impl SeatSpTotal {

pub exec fn seat_spt_total(
    &self,
    span: &Span,
) -> (r: Option<SpTotalRatio>)
    requires
        sp_field_inv(span),
        sp_flags_ok(span),
        // prune 2's cap: exclude the Civil-variable region.
        !(match self.rel {
            Option::Some(c) =>
                c.kind is Civil
                    && seat_unit_is_variable(sp_unit_max(
                        self.base.unit,
                        sp_span_largest(span),
                    )),
            Option::None => false,
        }),
    ensures
        seat_spt_face(self, span, &r),
{
    let existing: Unit = span.largest_unit();
    proof {
        assert(existing == sp_span_largest(span));
    }
    let max_unit: Unit = sp_unit_max_exec(self.base.unit, existing);
    match self.rel {
        Option::None => {
            // the J11 arm, relayed.
            self.base.total_no_relative(span)
        }
        Option::Some(c) => {
            let tr: Option<Option<DateTime>>
                = c.to_relative(max_unit);
            match tr {
                Option::None => {
                    // the marker + Year/Month error lane.
                    proof {
                        assert(max_unit is Year
                            || max_unit is Month);
                    }
                    Option::None
                }
                Option::Some(Option::Some(_dt)) => {
                    // the Civil-variable pipeline lane (prune 2):
                    // unreachable under the requires cap.
                    proof { assert(false); }
                    unreachable!()
                }
                Option::Some(Option::None) => {
                    // the marker / civil-invariant lane:
                    // total_invariant's exact rational
                    // (span.rs:4818-4819 == :4824-4825).
                    proof {
                        // Some(None) means the max unit is neither
                        // Year nor Month (both configs' error /
                        // to_relative lanes), so the requested unit
                        // sits at Week or below (the marker keeps
                        // Week/Day variable lanes invariant here).
                        assert(!(max_unit is Year));
                        assert(!(max_unit is Month));
                        assert(sp_unit_rank(max_unit)
                            <= sp_unit_rank(Unit::Week));
                        assert(sp_unit_rank(self.base.unit)
                            <= sp_unit_rank(max_unit));
                        assert(sp_unit_rank(self.base.unit)
                            <= sp_unit_rank(Unit::Week));
                        assert(!(self.base.unit is Year));
                        assert(!(self.base.unit is Month));
                    }
                    Option::Some(self.base.total_invariant(span))
                }
            }
        }
    }
}

} // impl SeatSpTotal

// ===========================================================================
// (4) The round seat: SpanRound's Some(relative) arm
// (span.rs:5366-5391).
// ===========================================================================

/// The adjoined config surface of SpanRound (the J10 struct is the
/// relative==None core; upstream's SpanRound carries the relative
/// field at span.rs:4952-4960; Copy kept only this base struct's
/// shape in the J10 file -- the seat adjoin drops it with the
/// Option field's construction-site discipline below).
pub struct SeatSpRound {
    pub base: SpanRound,
    pub rel: Option<SpanRel>,
}

/// Origin Rust: pub fn relative<R: Into<SpanRelativeTo<'a>>>(
///     self, relative: R) -> SpanRound<'a>
///     { SpanRound { relative: Some(relative.into()), ..self } }
///     (span.rs:5224-5292).
/// Upstream doc (span.rs:5210-5223 + :5266-5292, quoted in full
/// minus the zoned bullets/examples, prune 3):
///   Set the relative datetime to use when rounding a span.
///   A relative datetime is only required when calendar units (units
///   greater than hours) are involved. This includes having calendar
///   units in the original span, or calendar units in the configured
///   smallest or largest unit. A relative datetime is required when
///   calendar units are used because the duration of a particular
///   calendar unit (like 1 month or 1 year) is variable and depends
///   on the date. For example, 1 month from 2024-01-01 is 31 days,
///   but 1 month from 2024-02-01 is 29 days.
///   A relative datetime is provided by anything that implements
///   `Into<SpanRelativeTo>`. There are a few convenience trait
///   implementations provided:
///   * `From<civil::DateTime> for SpanRelativeTo` uses a civil
///   datetime. In this case, all days will be considered 24 hours
///   long.
///   * `From<civil::Date> for SpanRelativeTo` uses a civil date. In
///   this case, all days will be considered 24 hours long.
///   Note that one can impose 24-hour days without providing a
///   reference date via [`SpanRelativeTo::days_are_24_hours`].
///   # Errors
///   If rounding involves a calendar unit (units bigger than hours)
///   and no relative datetime is provided, then this configuration
///   will lead to an error when used with [`Span::round`].
impl SeatSpRound {

pub exec fn seat_sr_relative(
    self,
    rel: SpanRel,
) -> (r: SeatSpRound)
    ensures
        r.base == self.base,
        r.rel == Option::Some(rel),
{
    SeatSpRound {
        base: self.base,
        rel: Option::Some(rel),
    }
}

/// Origin Rust: pub fn days_are_24_hours(self) -> SpanRound<'a>
///     { self.relative(SpanRelativeTo::days_are_24_hours()) }
///     (span.rs:5296-5320).
/// Upstream doc example (span.rs:5300-5318, quoted in full):
///   use jiff::{SpanRound, ToSpan, Unit};
///   let span = 2.days().hours(12);
///   // No relative date provided, which results in an error.
///   assert_eq!(
///       span.round(Unit::Day).unwrap_err().to_string(),
///       "error with `smallest` rounding option: using unit 'day' in a \
///        span or configuration requires that either a relative reference \
///        time be given or \
///        `jiff::SpanRelativeTo::days_are_24_hours()` is used to indicate \
///        invariant 24-hour days, but neither were provided",
///   );
///   let rounded = span.round(
///       SpanRound::new().smallest(Unit::Day).days_are_24_hours(),
///   )?;
///   assert_eq!(rounded, 3.days().fieldwise());
/// (the 3.days row is the seat's own panel row below; its None-lane
///  error row is J10's.)
pub exec fn seat_sr_days_are_24_hours(
    self,
) -> (r: SeatSpRound)
    ensures
        r.base == self.base,
        r.rel == Option::Some(
            SpanRel { kind: SeatRelKind::DaysAre24Hours }),
{
    SeatSpRound {
        base: self.base,
        rel: Option::Some(SpanRel::days_are_24_hours()),
    }
}

} // impl SeatSpRound

/// The full branch contract of SpanRound::round (span.rs:5354-5400)
/// at the seats' three lanes, stated from the eff-largest /
/// eff-increment precomputation upward, module-top per the
/// pitfall-58 discipline:
/// - the None config: the J10 relative==None arm face verbatim;
/// - the DaysAre24Hours marker: the Year/Month error lane vs
///   round_span_invariant's face;
/// - the Civil config: the invariant-unit lane keeps the same
///   round_span_invariant face; the variable-unit region is prune
///   2's cap (vacuous contingency stated as in seat_spc_face).
pub open spec fn seat_sr_face(
    stag: &SeatSpRound,
    span: &Span,
    r: &Option<Span>,
) -> bool {
    let largest: Unit = sr_eff_largest(&stag.base, span);
    let existing: Unit = sp_span_largest(span);
    let max_unit: Unit = sp_unit_max(existing, largest);
    match stag.rel {
        Option::None =>
            sr_round_none_face(&stag.base, span, r),
        Option::Some(c) =>
            match c.kind {
                SeatRelKind::DaysAre24Hours =>
                    if max_unit is Year || max_unit is Month {
                        r == Option::None
                    } else {
                        // sr_round_inv_face is itself the two-sided
                        // disjunction (Some: the from-invariant face
                        // at the rounded total; None: the round-over
                        // / non-fit error arms) -- no always-Some
                        // claim (round_span_invariant is fallible,
                        // span.rs:6638-6645).
                        inc_for_span_ok(
                            stag.base.smallest,
                            stag.base.increment,
                        )
                            && sp_unit_rank(largest)
                                >= sp_unit_rank(stag.base.smallest)
                            && sr_round_inv_face(
                                span,
                                largest,
                                &Increment {
                                    unit: stag.base.smallest,
                                    value: stag.base.increment
                                        as i32,
                                },
                                stag.base.mode,
                                r,
                            )
                    },
                SeatRelKind::Civil(_) =>
                    if seat_unit_is_variable(max_unit) {
                        // prune 2's cap: vacuous contingency.
                        r == Option::None
                    } else {
                        inc_for_span_ok(
                            stag.base.smallest,
                            stag.base.increment,
                        )
                            && sp_unit_rank(largest)
                                >= sp_unit_rank(stag.base.smallest)
                            && sr_round_inv_face(
                                span,
                                largest,
                                &Increment {
                                    unit: stag.base.smallest,
                                    value: stag.base.increment
                                        as i32,
                                },
                                stag.base.mode,
                                r,
                            )
                    },
            },
    }
}

/// Origin Rust: fn round(&self, span: Span) -> Result<Span, Error>
///     (span.rs:5354-5400), body verbatim with the seats' lanes
///     marked:
///     let existing_largest = span.largest_unit();
///     let largest = self.largest
///         .unwrap_or_else(|| self.smallest.max(existing_largest));
///     let max = existing_largest.max(largest);
///     let increment = Increment::for_span(self.smallest,
///         self.increment)?;                       // here (gate)
///     if largest < self.smallest {
///         return Err(...LargestSmallerThanSmallest...);
///     }                                            // here (gate)
///     let relative = match self.relative {
///         Some(ref r) => {
///             match r.to_relative(max)? {
///                 Some(r) => r,                     // splice 2
///                 None => {
///                     // If our reference point is civil time, then
///                     // [...the upstream marker comment, quoted at
///                     // the None lane of sr_round_none_face...]
///                     return Ok(round_span_invariant(
///                         span, largest, &increment, self.mode,
///                     )?);                         // here
///                 }
///             }
///         }
///         None => { ... the J10 arm ... }          // J10 here
///     };
///     relative.round(span, largest, &increment, self.mode)  // prune 2
/// -- the seat materializes the marker lane plus the J10 relay; the
/// config gates (for_span, largest < smallest) stay in the requires
/// so the value face is the round_span_invariant contract (the J10
/// "caller-side requires carry the config conjunction" precedent).
impl SeatSpRound {

pub exec fn seat_sr_round(
    &self,
    span: &Span,
) -> (r: Option<Span>)
    requires
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        // the rel-matched config conjunction: the None lane needs
        // the whole J10 config face; the Some lanes need the
        // for_span gate and the largest>=smallest / largest<=Week
        // rank window (the marker's to_relative call keeps the
        // max unit at or below Week on every non-error lane).
        (match self.rel {
            Option::None => sr_config_ok(&self.base, span),
            Option::Some(_c) =>
                inc_for_span_ok(
                    self.base.smallest, self.base.increment,
                )
                    && sp_unit_rank(
                        sr_eff_largest(&self.base, span))
                        >= sp_unit_rank(self.base.smallest)
                    && sp_unit_rank(
                        sr_eff_largest(&self.base, span))
                        <= sp_unit_rank(Unit::Week),
        }),
        // prune 2's cap: exclude the Civil-variable region.
        !(match self.rel {
            Option::Some(c) =>
                c.kind is Civil
                    && seat_unit_is_variable(sp_unit_max(
                        sp_span_largest(span),
                        sr_eff_largest(&self.base, span),
                    )),
            Option::None => false,
        }),
    ensures
        seat_sr_face(self, span, &r),
{
    let existing_largest: Unit = span.largest_unit();
    proof {
        assert(existing_largest == sp_span_largest(span));
    }
    let largest: Unit = match self.base.largest {
        Option::Some(u) => u,
        Option::None =>
            sp_unit_max_exec(self.base.smallest, existing_largest),
    };
    proof {
        assert(largest == sr_eff_largest(&self.base, span));
    }
    let max_unit: Unit = sp_unit_max_exec(existing_largest, largest);
    match self.rel {
        Option::None => {
            // the J10 arm, relayed (the seat's requires carries
            // sr_config_ok for this lane).
            self.base.round_no_relative(span)
        }
        Option::Some(c) => {
            let tr: Option<Option<DateTime>>
                = c.to_relative(max_unit);
            match tr {
                Option::None => {
                    // the marker + Year/Month error lane
                    // (span.rs:5370-5375).
                    proof {
                        assert(max_unit is Year
                            || max_unit is Month);
                    }
                    Option::None
                }
                Option::Some(Option::Some(_dt)) => {
                    // the Civil-variable pipeline lane (prune 2):
                    // unreachable under the requires cap.
                    proof { assert(false); }
                    unreachable!()
                }
                Option::Some(Option::None) => {
                    // the marker / civil-invariant lane
                    // (span.rs:5376-5384): the invariant
                    // nanosecond pipeline, its own obligation
                    // family (the wall-46 split).
                    Self::seat_sr_round_inv_arm(self, span,
                        largest)
                }
            }
        }
    }
}

/// The invariant-lane arm of the round seat (span.rs:5376-5384's
/// round_span_invariant relay): the for_span gate is discharged by
/// the seat's config requires, and the Week-or-below rank window
/// keeps every Increment/Unit out of the calendar arms -- the arm
/// carries only the value face.
pub exec fn seat_sr_round_inv_arm(
    stag: &SeatSpRound,
    span: &Span,
    largest: Unit,
) -> (r: Option<Span>)
    requires
        sp_field_inv(span),
        sp_zero_sign_ok(span),
        sp_flags_ok(span),
        inc_for_span_ok(stag.base.smallest, stag.base.increment),
        sp_unit_rank(largest)
            >= sp_unit_rank(stag.base.smallest),
        sp_unit_rank(largest) <= sp_unit_rank(Unit::Week),
        largest == sr_eff_largest(&stag.base, span),
        // the caller's to_relative dispatch routed here: a marker
        // config arrives with the max unit out of the Year/Month
        // error lane, a civil config with an invariant max unit.
        !(stag.rel is None)
            && match stag.rel {
                Option::Some(c) =>
                    match c.kind {
                        SeatRelKind::DaysAre24Hours =>
                            !(sp_unit_max(
                                sp_span_largest(span), largest)
                                is Year)
                                && !(sp_unit_max(
                                    sp_span_largest(span),
                                    largest)
                                    is Month),
                        SeatRelKind::Civil(_) =>
                            !seat_unit_is_variable(
                                sp_unit_max(
                                    sp_span_largest(span),
                                    largest)),
                    },
                Option::None => false,
            },
    ensures
        match stag.rel {
            // routed to the J10 lane, never here
            Option::None => false,
            Option::Some(c) =>
                match c.kind {
                    SeatRelKind::DaysAre24Hours =>
                        if sp_unit_max(sp_span_largest(span), largest)
                            is Year
                            || sp_unit_max(
                                sp_span_largest(span), largest)
                                is Month {
                            r == Option::None
                        } else {
                            // the two-sided sr_round_inv_face
                            // disjunction carries the None arms
                            // (round-over / non-fit), not an
                            // always-Some claim.
                            inc_for_span_ok(
                                stag.base.smallest,
                                stag.base.increment,
                            )
                                && sp_unit_rank(largest)
                                    >= sp_unit_rank(
                                        stag.base.smallest)
                                && sr_round_inv_face(
                                    span,
                                    largest,
                                    &Increment {
                                        unit: stag.base.smallest,
                                        value: stag.base.increment
                                            as i32,
                                    },
                                    stag.base.mode,
                                    &r,
                                )
                        },
                    SeatRelKind::Civil(_) =>
                        if seat_unit_is_variable(
                            sp_unit_max(sp_span_largest(span), largest),
                        ) {
                            r == Option::None
                        } else {
                            inc_for_span_ok(
                                stag.base.smallest,
                                stag.base.increment,
                            )
                                && sp_unit_rank(largest)
                                    >= sp_unit_rank(
                                        stag.base.smallest)
                                && sr_round_inv_face(
                                    span,
                                    largest,
                                    &Increment {
                                        unit: stag.base.smallest,
                                        value: stag.base.increment
                                            as i32,
                                    },
                                    stag.base.mode,
                                    &r,
                                )
                        },
                },
        },
{
    proof {
        // the rank window keeps the smallest unit at or below
        // Week, out of sp_round_span_invariant's calendar prunes.
        assert(!(stag.base.smallest is Year));
        assert(!(stag.base.smallest is Month));
        assert(sp_unit_rank(stag.base.smallest)
            <= sp_unit_rank(largest));
        assert(sp_unit_rank(largest)
            <= sp_unit_rank(Unit::Week));
    }
    match Increment::for_span(
        stag.base.smallest,
        stag.base.increment,
    ) {
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
        Option::Some(inc) => {
            proof {
                assert(inc.unit == stag.base.smallest);
                assert(inc.value == stag.base.increment as i32);
                assert((inc.value as int)
                    == (stag.base.increment as int));
                assert(inc == Increment {
                    unit: stag.base.smallest,
                    value: stag.base.increment as i32,
                });
                // the caller's to_relative(Some(None)) dispatch
                // pinned the max unit's two error lanes off, so
                // the sr_round_inv_face conjuncts reduce to the
                // round_span_invariant contract below.
                assert(sp_unit_max(sp_span_largest(span), largest)
                    is Week
                    || sp_unit_max(sp_span_largest(span), largest)
                        is Day
                    || !seat_unit_is_variable(
                        sp_unit_max(sp_span_largest(span),
                            largest)));
            }
            sp_round_span_invariant(
                span,
                largest,
                &inc,
                stag.base.mode,
            )
        }
    }
}

} // impl SeatSpRound

/// The full branch contract of SpanRound::round (span.rs:5354-5400)
/// at the seats' three lanes, stated from the eff-largest /
/// eff-increment precomputation upward, module-top per the
/// pitfall-58 discipline:
/// - the None config: the J10 relative==None arm face verbatim;
/// - the DaysAre24Hours marker: the Year/Month error lane vs
///   round_span_invariant's face;
/// - the Civil config: the invariant-unit lane keeps the same
///   round_span_invariant face; the variable-unit region is prune
///   2's cap (vacuous contingency stated as in seat_spc_face).

// ===========================================================================
// (5) The last Time quickcheck property
// prop_until_is_since_negated (civil/time.rs:3367-3370).
//
// The until twin below re-transcribes the J8 reun panel's
// time_until_span with its own fits discharge (the J8 driver's
// panel is NOT mounted here: in this batch's fatter union the
// reunion exec theorems reproduce the J9 pitfall-59 mount
// sensitivity -- 2 obligations flipped at rlimit 300 and the
// wall-47/58 rlimit-600 panic fired at reunion :773 -- so the
// seats carry their own local twin instead of importing the
// flaky closed-file obligations).
// ===========================================================================

/// The fits folklore lemma at the civil-day window, re-transcribed
/// from the J8 reunion twin (wrapper time.rs:2560's
/// `.expect("difference in civil times is always in bounds")`
/// discharge): a total strictly inside one civil day is
/// fits-representable at EVERY bucket largest.
proof fn seat_lemma_time_diff_fits(l: Unit, t: int)
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
    if l is Week {
        assert(sp_fid_w(l, t) >= -(86_400int) / 604_800int - 1);
        assert(sp_fid_w(l, t) <= 86_400int / 604_800int + 1);
    }
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Day) {
        assert(sp_fid_d(l, t) >= -(86_400int) / 86_400int - 1);
        assert(sp_fid_d(l, t) <= 86_400int / 86_400int + 1);
    }
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Hour) {
        assert(sp_fid_h(l, t) >= -86_400int / 3600int - 1);
        assert(sp_fid_h(l, t) <= 86_400int / 3600int + 1);
    }
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Minute) {
        assert(sp_fid_m(l, t) >= -(86_400int) / 60int - 1);
        assert(sp_fid_m(l, t) <= 86_400int / 60int + 1);
    }
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Second) {
        assert(sp_fid_s(l, t) >= -86_400 - 1);
        assert(sp_fid_s(l, t) <= 86_400 + 1);
    }
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Millisecond) {
        assert(sp_fid_mi(l, t)
            >= -(86_400int) * 1_000 - 1_000_000 - 1);
        assert(sp_fid_mi(l, t)
            <= 86_400 * 1_000 + 1_000_000 + 1);
    }
    if sp_unit_rank(l) >= sp_unit_rank(Unit::Microsecond) {
        assert(sp_fid_mc(l, t)
            >= -(86_400int) * 1_000_000 - 1_000_000_000 - 1);
        assert(sp_fid_mc(l, t)
            <= 86_400 * 1_000_000 + 1_000_000_000 + 1);
    }
    assert(sp_fid_nn(l, t) >= -86_400_000_000_000 - 1);
    assert(sp_fid_nn(l, t) <= 86_400_000_000_000 + 1);
    // Each bound sits orders of magnitude inside the b::Span ranges.
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

/// Origin Rust: fn TimeDifference::until_with_largest_unit(&self,
///     t1: Time) -> Result<Span, Error> (wrapper time.rs:2539-2562)
/// at the default configuration (largest == Unit::Hour, the
/// equal-times early return included via the diff), body verbatim:
///     let t2 = self.time;
///     if t1 == t2 { return Ok(Span::new()); }
///     let start = t1.to_duration();
///     let end = t2.to_duration();
///     let span = Span::from_invariant_duration(largest, end - start)
///         .expect("difference in civil times is always in bounds");
///     Ok(span)
/// Face: the J8 reun panel's time_until_span tier-and-identity
/// skeleton (the every-valid-input shape; the round tail never
/// fires on the default config's no-rounding gate).
pub exec fn seat_time_until_span(
    t1: Time,
    t2: Time,
) -> (s: Span)
    requires
        valid_time(t1),
        valid_time(t2),
    ensures
        sp_field_inv(&s),
        sp_zero_sign_ok(&s),
        sp_flags_ok(&s),
        s.years == 0,
        s.months == 0,
        s.weeks == 0,
        s.days == 0,
        sp_inv_total_nanos(&s)
            == (crate::time::time_nanos_spec(t2)
                - crate::time::time_nanos_spec(t1)),
{
    // the civil-day window is until_nanoseconds' own face (the J3
    // core, wrapper time.rs:1690-1692).
    let nanos: i64 = t1.until_nanoseconds(t2);
    let d: SignedDuration = SignedDuration::from_nanos(nanos);
    proof {
        let tot: int = crate::time::time_nanos_spec(t2)
            - crate::time::time_nanos_spec(t1);
        assert((nanos as int) == tot);
        seat_lemma_time_diff_fits(Unit::Hour, tot);
    }
    match Span::sp_from_invariant_duration(Unit::Hour, &d) {
        Option::Some(s) => s,
        Option::None => {
            // Dead arm: the fits lemma discharged the upstream
            // expect (wrapper time.rs:2560).
            proof { assert(false); }
            unreachable!()
        }
    }
}

/// Origin Rust (civil/time.rs:3347-3371, the quickcheck property
/// block; the quoted fn is its fifth and last member):
///     fn prop_until_is_since_negated(t1: Time, t2: Time) -> bool {
///         t1.until(t2).unwrap().get_nanoseconds()
///             == t1.since(t2).unwrap().negate().get_nanoseconds()
///     }
/// The property closes structurally at the wrapper bodies
/// (time.rs:1223-1234 and :1259-1267):
///     pub fn until<A: Into<TimeDifference>>(
///         self, other: A) -> Result<Span, Error> {
///         let args: TimeDifference = other.into();
///         let span = args.until_with_largest_unit(self)?;
///         if args.rounding_may_change_span() { span.round(args.round) }
///         else { Ok(span) }
///     }
///     pub fn since<A: Into<TimeDifference>>(
///         self, other: A) -> Result<Span, Error> {
///         let args: TimeDifference = other.into();
///         let span = -args.until_with_largest_unit(self)?;
///         ...
///     }
/// -- since(t1, t2) is the NEGATION of the very same
/// until_with_largest_unit(t1 -> t2) span until(t1, t2) returns, so
/// t1.since(t2).negate() is the double negation of
/// t1.until(t2), and Span::negate (span.rs:1361-1363) keeps every
/// field magnitude while flipping the global sign only: the sign
/// involution makes the double negation the identity, nanoseconds
/// field included. (J8's deferral had estimated a trunc
/// anti-automorphism at the from_invariant face; the wrapper-body
/// route needs no anti-automorphism.)
pub exec fn seat_prop_until_is_since_negated(
    t1: Time,
    t2: Time,
) -> (b: bool)
    requires
        valid_time(t1),
        valid_time(t2),
    ensures
        b,
{
    // t1.until(t2) -- the local twin above carries the
    // default-config wrapper body (largest = Hour,
    // rounding_may_change_span false on the default
    // TimeDifference).
    let u: Span = seat_time_until_span(t1, t2);
    // t1.since(t2) -- the negation of the same span (the wrapper
    // body's `-args.until_with_largest_unit(self)`).
    let s: Span = u.negate();
    // ... and the property's `.negate()` of since:
    let s2: Span = s.negate();
    proof {
        // the sign involution: negate(negate(u)) lands back on the
        // u sign case-by-case, magnitudes untouched throughout.
        if u.sign is Zero {
            assert(s.sign is Zero);
            assert(s2.sign is Zero);
        } else if u.sign is Positive {
            assert(s.sign is Negative);
            assert(s2.sign is Positive);
        } else {
            assert(s.sign is Positive);
            assert(s2.sign is Negative);
        }
        assert(s2.nanoseconds == u.nanoseconds);
    }
    let v1: i64 = u.get_nanoseconds();
    let v2: i64 = s2.get_nanoseconds();
    v1 == v2
}

// ===========================================================================
// (6) Date::at (date.rs:1221-1230), the J7 leftover.
// ===========================================================================

/// Origin Rust: pub const fn at(self, hour: i8, minute: i8,
///     second: i8, subsec_nanosecond: i32) -> DateTime
///     (date.rs:1217-1230), body verbatim:
///     DateTime::from_parts(
///         self,
///         Time::constant(hour, minute, second, subsec_nanosecond),
///     )
/// Upstream doc (date.rs:1164-1216, quoted sentence by sentence,
/// minus the first (date-material) example):
///   Similarly, when used in a const context, invalid parameters will
///   prevent your Rust program from compiling.
///   # Example
///   ```
///   use jiff::civil::date;
///   assert_eq!(
///       date(2010, 3, 14).at(2, 30, 0, 0).to_string(),
///       "2010-03-14T02:30:00",
///   );
///   ```
///   One can also flip the order by making use of [`Time::on`]:
///   ```
///   use jiff::civil::time;
///   assert_eq!(
///       time(2, 30, 0, 0).on(2010, 3, 14).to_string(),
///       "2010-03-14T02:30:00",
///   );
///   ```
/// (The panicking const face is the requires -- the J2
///  Date::constant / J3 Time::constant precedent. The Time::on
///  reassembly twin is recorded here; its body is this same
///  from_parts row with the receivers flipped.)
pub exec fn seat_date_at(
    d: Date,
    hour: i8,
    minute: i8,
    second: i8,
    subsec_nanosecond: i32,
) -> (dt: DateTime)
    requires
        valid_date(d),
        crate::time::hour_iv().contains(hour as int),
        crate::time::minute_iv().contains(minute as int),
        crate::time::second_iv().contains(second as int),
        crate::time::subsec_iv().contains(subsec_nanosecond as int),
    ensures
        dt.date == d
            && dt.time.hour as int == hour as int
            && dt.time.minute as int == minute as int
            && dt.time.second as int == second as int
            && dt.time.subsec_nanosecond as int
                == subsec_nanosecond as int
            && valid_datetime(dt),
{
    let t: Time = Time::constant(hour, minute, second, subsec_nanosecond);
    DateTime::from_parts(d, t)
}

// ===========================================================================
// (7) The doc-witness panels: every upstream row this batch's domain
// states, machine-checked at its own literal.
// ===========================================================================

/// Date::until bigger-units doc rows (date.rs:1532-1544, quoted):
///   let d1 = date(1995, 12, 07);
///   let d2 = date(2019, 01, 31);
///   // The default limits durations to using "days" as the biggest unit.
///   let span = d1.until(d2)?;
///   assert_eq!(span.to_string(), "P8456D");
///   // But we can ask for units all the way up to years.
///   let span = d1.until((Unit::Year, d2))?;
///   assert_eq!(span.to_string(), "P23Y1M24D");
/// Rows pinned: the Year-config P23Y1M24D row, plus the
/// Month-config collapse of the same pair (P277M, the
/// largest==Month checked_add lane on a value-days pair).
exec fn seat_panel_until_year_month_doc()
{
    let d1: Date = Date::constant(1995, 12, 7);
    let d2: Date = Date::constant(2019, 1, 31);
    proof {
        // the lane walk of the pair: no day borrow (days0 == 24),
        // the month-carry correction fires
        // (months1 == -11 == -sign), years folds to 23.
        assert(seat_myl_sg(d1, d2) == 1);
        assert(seat_myl_move(d1, d2)
            == (2019, 1, 0, 31));
        assert(seat_myl_parts(d1, d2) == (23, 1, 24));
    }
    let ry: Option<Span> = seat_date_until_my(d1, d2, Unit::Year);
    assert(ry is Some);
    let sy: Span = match ry {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(sy.sign is Positive);
    assert(sy.years == 23i16);
    assert(sy.months == 1i32);
    assert(sy.days == 24i32);
    assert(sy.weeks == 0i32);
    assert(sy.hours == 0i32);
    // the Month-config collapse of the same pair: 1 + 23*12 == 277.
    let rm: Option<Span> = seat_date_until_my(d1, d2, Unit::Month);
    assert(rm is Some);
    let sm: Span = match rm {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(sm.sign is Positive);
    assert(sm.years == 0i16);
    assert(sm.months == 277i32);
    assert(sm.days == 24i32);
}

/// The reversibility doc example (date.rs:1566-1594, quoted):
///   let d1 = date(2024, 3, 2);
///   let d2 = date(2024, 5, 1);
///   let span = d1.until((Unit::Month, d2))?;
///   assert_eq!(span, 1.month().days(29).fieldwise());
///   let maybe_original = d2.checked_sub(span)?;
///   // Not the same as the original datetime!
///   assert_eq!(maybe_original, date(2024, 3, 3));
///   // But in the default configuration, days are always the biggest unit
///   // and reversibility is guaranteed.
///   let span = d1.until(d2)?;
///   assert_eq!(span, 60.days().fieldwise());
///   let is_original = d2.checked_sub(span)?;
///   assert_eq!(is_original, d1);
/// -- rows pinned here: the Month-config 1.month().days(29) lane
/// (the day-borrow row of the borrow-correction group; d2's checked
/// sub route belongs to the J9 relative panel). The doc's
/// non-reversibility claim is a RECORD here: for Month-year
/// lanes the span is calendar-directional, adding it back to d2
/// lands on 2024-03-03, not d1 -- recorded, not machine-checked
/// (the checked_sub side sits in the relative panel's closed file).
exec fn seat_panel_until_month_borrow_doc()
{
    let d1: Date = Date::constant(2024, 3, 2);
    let d2: Date = Date::constant(2024, 5, 1);
    proof {
        // the day borrow fires (days0 == -1 == -sign), the move
        // lands on April 2024, day_correct == 30.
        assert(seat_myl_sg(d1, d2) == 1);
        assert(seat_myl_move(d1, d2) == (2024, 4, 30, 30));
        assert(seat_myl_parts(d1, d2) == (0, 1, 29));
    }
    let r: Option<Span> = seat_date_until_my(d1, d2, Unit::Month);
    assert(r is Some);
    let s: Span = match r {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(s.sign is Positive);
    assert(s.years == 0i16);
    assert(s.months == 1i32);
    assert(s.days == 29i32);
    assert(s.weeks == 0i32);
}

/// The negative-direction witness rows: the Year-config until of
/// the doc pair flipped (years/months/days all negative, the
/// corrected years lane folds 1995+1-2019 == -23), plus since's
/// negation of the positive triple (the wrapper is the negated
/// d1->d2 lane computation, not a fresh d2->d1 walk).
exec fn seat_panel_until_since_negative()
{
    let d1: Date = Date::constant(2019, 1, 31);
    let d2: Date = Date::constant(1995, 12, 7);
    proof {
        // no borrow (days0 == -24, sign == -1), the month-carry
        // correction fires (months1 == +11 == -sign).
        assert(seat_myl_sg(d1, d2) == 0 - 1);
        assert(seat_myl_move(d1, d2) == (1995, 12, 0, 31));
        assert(seat_myl_parts(d1, d2) == (-23, -1, -24));
    }
    let ry: Option<Span> = seat_date_until_my(d1, d2, Unit::Year);
    assert(ry is Some);
    let sy: Span = match ry {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(sy.sign is Negative);
    assert(sy.years == 23i16);
    assert(sy.months == 1i32);
    assert(sy.days == 24i32);
    // since(d1, d2) == -(the 2019->1995 lane triple): positive
    // again, same magnitudes.
    proof {
        let (yv, mv, dv): (int, int, int) = seat_myl_parts(d1, d2);
        assert((0 - yv, 0 - mv, 0 - dv) == (23, 1, 24));
    }
    let rs: Option<Span> = seat_date_since_my(d1, d2, Unit::Year);
    assert(rs is Some);
    let ss: Span = match rs {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(ss.sign is Positive);
    assert(ss.years == 23i16);
    assert(ss.months == 1i32);
    assert(ss.days == 24i32);
}

/// The Month-collapse overflow row: the extreme-span pair whose
/// largest == Month collapse exceeds b::SpanMonths's range
/// (upstream's checked_add error, the seat's one fallible lane --
/// the default-Day doc's never-fail guarantee does not extend to
/// this configuration corner; a witness, upstream has no doc row).
exec fn seat_panel_until_month_overflow()
{
    let d1: Date = Date::constant(-9999, 1, 31);
    let d2: Date = Date::constant(9999, 12, 30);
    proof {
        assert(seat_myl_sg(d1, d2) == 1);
        assert(seat_myl_move(d1, d2) == (9999, 11, 30, 30));
        let (yv, mv, dv): (int, int, int) = seat_myl_parts(d1, d2);
        assert((yv, mv, dv) == (19998, 10, 30));
        assert(mv + 12 * yv == 239_986);
        assert(!(0 - 239_976 <= 239_986 && 239_986 <= 239_976));
    }
    let r: Option<Span> = seat_date_until_my(d1, d2, Unit::Month);
    assert(r is None);
}

/// The zero and block-skipped rows: equal dates return the zero
/// span under the Year config (date.rs:2748-2750), and a same-month
/// pair keeps (0, 0, dd) lanes.
exec fn seat_panel_until_zero_and_dayonly()
{
    let d1: Date = Date::constant(2024, 3, 2);
    proof {
        assert(seat_myl_move(d1, d1) == (2024, 3, 0, 31));
        assert(seat_myl_parts(d1, d1) == (0, 0, 0));
    }
    let rz: Option<Span> = seat_date_until_my(d1, d1, Unit::Year);
    assert(rz is Some);
    let sz: Span = match rz {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(sz.sign is Zero);
    assert(sz.years == 0i16);
    assert(sz.months == 0i32);
    assert(sz.days == 0i32);

    let d2: Date = Date::constant(2024, 3, 29);
    proof {
        assert(seat_myl_move(d1, d2) == (2024, 3, 0, 31));
        assert(seat_myl_parts(d1, d2) == (0, 0, 27));
    }
    let rd: Option<Span> = seat_date_until_my(d1, d2, Unit::Month);
    assert(rd is Some);
    let sd: Span = match rd {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(sd.sign is Positive);
    assert(sd.years == 0i16);
    assert(sd.months == 0i32);
    assert(sd.days == 27i32);
}

/// SpanCompare::days_are_24_hours doc rows (span.rs:4480-4496,
/// quoted at seat_spc_days_are_24_hours): the 2.days().hours(12) vs
/// 60.hours marker row (Equal), the marker + Year-unit error row
/// (span.rs:5699-5705's RelativeYearOrMonthGivenDaysAre24Hours
/// lane), and the civil-config row on the invariant-unit region
/// (3.hours vs 180.minutes relative to 2024-01-01 -- to_relative
/// returns Ok(None) for an invariant max unit under every kind, so
/// the ordering is the invariant one).
exec fn seat_panel_spc_marker_rows()
{
    let span1: Span = Span::new().days(2).hours(12);
    let span2: Span = Span::new().hours(60);
    proof {
        assert(sp_inv_total_nanos(&span1)
            == 216_000_000_000_000int);
        assert(sp_inv_total_nanos(&span2)
            == 216_000_000_000_000int);
    }
    let cfg24: SeatSpCompare =
        seat_spc_from_span(span2).seat_spc_days_are_24_hours();
    let o: Option<SpOrdering> = cfg24.seat_spc_compare(&span1);
    assert(o is Some);
    assert(match o {
        Option::Some(x) => x is Equal,
        Option::None => false,
    });

    // the marker + Year-lane error witness (both spans carry
    // years, so the max unit is Year).
    let y1: Span = Span::new().years(1);
    let y2: Span = Span::new().years(1);
    let cfgy24: SeatSpCompare =
        seat_spc_from_span(y2).seat_spc_days_are_24_hours();
    let o2: Option<SpOrdering> = cfgy24.seat_spc_compare(&y1);
    assert(o2 is None);

    // the civil-config row on the invariant-unit region.
    let s1h: Span = Span::new().hours(3);
    let s2m: Span = Span::new().minutes(180);
    let rc: SpanRel =
        SpanRel::from_date(Date::constant(2024, 1, 1));
    let cfgcr: SeatSpCompare =
        seat_spc_from_span(s2m).seat_spc_relative(rc);
    let o3: Option<SpOrdering> = cfgcr.seat_spc_compare(&s1h);
    assert(o3 is Some);
    assert(match o3 {
        Option::Some(x) => x is Equal,
        Option::None => false,
    });
}

/// SpanTotal::days_are_24_hours doc rows: the 60.0 row of
/// 2.days().hours(12) in Unit::Hour (span.rs:4783-4796, quoted at
/// seat_spt_days_are_24_hours; exact rational (216e12, 3.6e12),
/// evenly 60), and Span::total's 24-hour-days example
/// (span.rs:2030-2044):
///   # Example: 24 hour days
///   This shows how to find the total number of 24 hour days in
///   `123,456,789` seconds.
///   ```
///   use jiff::{SpanTotal, ToSpan, Unit};
///   let span = 123_456_789.seconds();
///   ```
///   assert_eq!(
///       span.total(SpanTotal::from(Unit::Day).days_are_24_hours())?,
///       1428.8980208333332,
///   );
/// -- pinned as the exact rational (123456789e9, 86400e9) =
/// 1428 + 77589/86400 nanosecond-grade seconds (NOT evenly
/// divisible: the fractional-component doc sentence's witness).
exec fn seat_panel_spt_marker_rows()
{
    let span1: Span = Span::new().days(2).hours(12);
    let c124: SeatSpTotal = seat_spt_from_unit(Unit::Hour)
        .seat_spt_days_are_24_hours();
    let r1: Option<SpTotalRatio> = c124.seat_spt_total(&span1);
    assert(r1 is Some);
    let t1: SpTotalRatio = match r1 {
        Option::Some(x) => x,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(t1.numer == 216_000_000_000_000i128);
    assert(t1.denom == 3_600_000_000_000i128);
    assert(t1.numer == 60i128 * t1.denom);

    // the fractional row.
    let span2: Span = Span::new().seconds(123_456_789);
    let c224: SeatSpTotal = seat_spt_from_unit(Unit::Day)
        .seat_spt_days_are_24_hours();
    let r2: Option<SpTotalRatio> = c224.seat_spt_total(&span2);
    assert(r2 is Some);
    let t2: SpTotalRatio = match r2 {
        Option::Some(x) => x,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(t2.numer == 123_456_789_000_000_000i128);
    assert(t2.denom == 86_400_000_000_000i128);
    assert(t2.numer
        == 1428i128 * t2.denom + 77_589_000_000_000i128);
    // not evenly divisible (span.rs:1986-1987's "may have a
    // fractional component" sentence, on its own witness).
    assert(!(t2.numer % t2.denom == 0));
}

/// SpanRound::days_are_24_hours doc row (span.rs:5300-5318, quoted
/// at seat_sr_days_are_24_hours): 2.days().hours(12) rounded at
/// smallest == Day with the marker lands on 3.days() (the
/// HalfExpand default: 2.5 days rounds up).
exec fn seat_panel_sr_marker_row()
{
    let span: Span = Span::new().days(2).hours(12);
    let base: SpanRound = SpanRound::new().smallest(Unit::Day);
    let stag24: SeatSpRound = SeatSpRound {
        base: base,
        rel: Option::None,
    }.seat_sr_days_are_24_hours();
    proof {
        // the hint ladder, the J10 sr_panel_doc_span_round style:
        // the 2.days().hours(12) total is 216e12 nanoseconds, the
        // Day increment is 86.4e12, the decision core sits exactly
        // on the tie (quotient 2, remainder 43.2e12 == half the
        // increment), and HalfExpand bumps ties away from zero.
        assert(sp_inv_total_nanos(&span)
            == 216_000_000_000_000int);
        assert(sp_span_largest(&span) is Day);
        assert(sr_eff_largest(&base, &span) is Day);
        assert(base.mode is HalfExpand);
        assert((base.increment as int)
            * rm_unit_nanos(base.smallest)
            == 86_400_000_000_000int);
        lemma_fundamental_div_mod_converse(
            216_000_000_000_000int,
            86_400_000_000_000int,
            2int,
            43_200_000_000_000int,
        );
        assert(2 * 43_200_000_000_000int
            == 86_400_000_000_000int);
        assert(sr_rt_total(&base, &span)
            == 259_200_000_000_000int);
        assert(inc_for_span_ok(Unit::Day, 1));
        assert(sd_min_total_nanos()
            <= 259_200_000_000_000int);
        assert(259_200_000_000_000int
            <= sd_max_total_nanos());
        assert(sp_fid_fits(Unit::Day,
            259_200_000_000_000int));
    }
    let r: Option<Span> = stag24.seat_sr_round(&span);
    assert(r is Some);
    let s: Span = match r {
        Option::Some(s) => s,
        Option::None => {
            proof { assert(false); }
            unreachable!()
        }
    };
    assert(s.sign is Positive);
    assert(s.days == 3i32);
    assert(s.years == 0i16);
    assert(s.months == 0i32);
    assert(s.weeks == 0i32);
    assert(s.hours == 0i32);
    assert(s.minutes == 0i32);
    assert(s.seconds == 0i32);
    assert(s.nanoseconds == 0i64);
}

/// prop_until_is_since_negated at upstream's own doctest pair
/// (`time(3, 24, 30, 3500)` and `time(15, 30, 0, 0)`,
/// time.rs:1209-1221's until example rows), plus the equal-times
/// degenerate row of the same property.
exec fn seat_panel_prop_negated_witness()
{
    let t1: Time = Time::constant(3, 24, 30, 3500);
    let t2: Time = Time::constant(15, 30, 0, 0);
    let b: bool = seat_prop_until_is_since_negated(t1, t2);
    assert(b);
    let bz: bool = seat_prop_until_is_since_negated(t1, t1);
    assert(bz);
}

/// Date::at doc rows (date.rs:1200-1216, quoted at seat_date_at):
/// the 2010-03-14 reassembly lands on the civil datetime with the
/// date intact and 02:30:00 as the time component.
exec fn seat_panel_date_at_doc()
{
    let d: Date = Date::constant(2010, 3, 14);
    let dt: DateTime = seat_date_at(d, 2, 30, 0, 0);
    assert(dt.date == d);
    assert(dt.time.hour == 2i8);
    assert(dt.time.minute == 30i8);
    assert(dt.time.second == 0i8);
    assert(dt.time.subsec_nanosecond == 0i32);
    assert(valid_datetime(dt));
}

} // verus!
