//! jiff J9 batch driver -- the relative calendar pipeline (the J8
//! deferred item 1): SpanRelativeTo / the Span checked_add relative
//! paths, the Date (civil) checked_add_span / checked_sub Span+duration
//! rhs faces, the Date until/since Span-return face, and the civil
//! DateTime checked_add / until / since faces. Mounted standalone
//! (the j8-driver precedent; src/lib.rs stays untouched by this batch).
//!
//! Mounts (all read-only, closed panels except the J9 file):
//! - the full src/lib.rs module tree (bounds, constants, date, time,
//!   weekday, datetime, calendar) -- the J1-J7 civil panels, whose
//!   Date/Time/DateTime faces are the consumer closure of the relative
//!   pipeline (month_add_overflowing, the Date/UnixEpochDay checked
//!   arithmetic, the J7 NS informative twins, DateTime/Time structs).
//! - `src/jcore_signed_duration.rs` (J4b): the SignedDuration core.
//! - `src/jcore_span.rs` (J5): the Span core (struct, setters,
//!   getters, negate, units).
//! - `src/jcore_span_arith.rs` (J8): the invariant-duration spine
//!   (to/from_invariant_duration, sd_as_*_with_remainder, the
//!   checked_add invariant chain at relative == None).
//! - `src/jcore_span_relative.rs` (J9): this batch's file. (The J8
//!   `src/jcore_span_reunion.rs` panel is NOT mounted here: its four
//!   property theorems are budget-sensitive to the mount context --
//!   they flip run-to-run at rlimit 600 inside this fatter union
//!   while verifying green on their home j8 driver at 300 (J9
//!   pitfall 59). The two faces this file consumes from it (the
//!   Time to_nanosecond roundtrip lemma and to_duration) ship as
//!   locally verified twins inside jcore_span_relative.rs, so the
//!   obligations stay real on this panel too.)

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/bounds.rs"]
mod bounds;

#[path = "src/constants.rs"]
mod constants;

#[path = "src/date.rs"]
mod date;

#[path = "src/time.rs"]
mod time;

#[path = "src/weekday.rs"]
mod weekday;

#[path = "src/datetime.rs"]
mod datetime;

#[path = "src/calendar.rs"]
mod calendar;

#[path = "src/jcore_signed_duration.rs"]
mod jcore_signed_duration;

#[path = "src/jcore_span.rs"]
mod jcore_span;

#[path = "src/jcore_span_arith.rs"]
mod jcore_span_arith;

fn main() {}

#[path = "src/jcore_span_relative.rs"]
mod jcore_span_relative;
