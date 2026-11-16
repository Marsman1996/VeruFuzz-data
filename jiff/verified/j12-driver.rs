//! jiff J12 batch driver -- the reunion seats (the compare / total /
//! round Some(relative) three, the Date until/since Month/Year
//! configs, the last Time quickcheck property and the Date::at
//! leftover), mounted standalone (the j10/j11 driver precedent; the
//! batch's option a). The closed panels it mounts are re-verified in
//! this run, so the panel below is expected to sit near the J11
//! closed set plus the J8 reunion and civil tree additions this
//! batch consumes; the J12-owned obligations ride this file's mounts.
//! src/lib.rs itself is untouched, and NEITHER jcore_span_relative.rs
//! NOR j9-driver.rs is mounted (the concurrent compliance-repair wave
//! owns those; this batch translates its own capped gateway twin).
//!
//! Mounts (all read-only, closed panels except the J12 file):
//! - `src/bounds.rs` (J1): the Sign enum and range helpers.
//! - `src/constants.rs` (J2): the unit-constant layer.
//! - `src/date.rs` (J2/J7): the Date core (fields, days_in_month,
//!   Date::constant) the Month/Year lanes consume.
//! - `src/time.rs` (J3): the Time core (Time::constant /
//!   Time::midnight, the quickcheck property seat's domain).
//! - `src/datetime.rs` (J6): the civil datetime reassembly core
//!   (DateTime::from_parts / valid_datetime).
//! - `src/jcore_signed_duration.rs` (J4b): the SignedDuration core.
//! - `src/jcore_span.rs` (J5): the Span core.
//! - `src/jcore_span_arith.rs` (J8): the composition spine.
//! - `src/jcore_round.rs` (J10): the rounding family.
//! - `src/jcore_span_total.rs` (J11): the compare/total family.
//! - `src/jcore_relative_seats.rs` (J12, this batch).

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

#[path = "src/datetime.rs"]
mod datetime;

#[path = "src/jcore_signed_duration.rs"]
mod jcore_signed_duration;

#[path = "src/jcore_span.rs"]
mod jcore_span;

#[path = "src/jcore_span_arith.rs"]
mod jcore_span_arith;

#[path = "src/jcore_round.rs"]
mod jcore_round;

#[path = "src/jcore_span_total.rs"]
mod jcore_span_total;

#[path = "src/jcore_relative_seats.rs"]
mod jcore_relative_seats;

fn main() {}
