//! jiff J10 batch driver -- the rounding family, mounted standalone
//! (the J5/J8 driver precedent; the batch's option a). The driver's
//! module tree replicates the lib.rs shape for the panels this
//! batch consumes; the closed panels it mounts are re-verified in
//! this run, so the expected panel sits near bounds 34 +
//! signed-duration 57 + span 100 + arith-spine magnitudes; the
//! J10-owned obligations ride this file's mounts. src/lib.rs itself
//! is untouched.
//!
//! Mounts (all read-only, closed panels except the J10 file):
//! - `src/bounds.rs` (J1): the Sign enum and range helpers.
//! - `src/constants.rs` (J2): the unit-constant layer.
//! - `src/jcore_signed_duration.rs` (J4b): the SignedDuration core
//!   (sd_inv / sd_total_nanos, constructors, as_nanos, the
//!   as_*_with_remainder family the arith spine consumes).
//! - `src/jcore_span.rs` (J5): the Span core (struct, setters,
//!   getters, negate, largest_unit).
//! - `src/jcore_span_arith.rs` (J8): to_invariant_duration /
//!   from_invariant_duration (the composition spine this batch's
//!   round skeleton consumes), the unit-rank twins.
//! - `src/jcore_round.rs` (J10, this batch): util/round.rs
//!   (Increment + the RoundMode decision core) and the SpanRound
//!   consumer face of span.rs.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/bounds.rs"]
mod bounds;

#[path = "src/constants.rs"]
mod constants;

#[path = "src/jcore_signed_duration.rs"]
mod jcore_signed_duration;

#[path = "src/jcore_span.rs"]
mod jcore_span;

#[path = "src/jcore_span_arith.rs"]
mod jcore_span_arith;

#[path = "src/jcore_round.rs"]
mod jcore_round;

fn main() {}
