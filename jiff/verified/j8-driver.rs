//! jiff J8 batch driver -- the Span invariant-duration composition
//! spine, mounted standalone (the j5-driver precedent; the batch's
//! option a. The driver's module tree replicates the lib.rs shape: the
//! closed panels it mounts are re-verified in this run, so the panel
//! below is expected to sit near bounds 34 + signed-duration 57 +
//! span 100 + arith (this batch's own) + reunion (this batch's
//! Time-consuming faces) magnitudes; src/lib.rs itself is untouched).
//!
//! Mounts (all read-only, closed panels except the J8 file):
//! - `src/bounds.rs` (J1): the Sign enum and range helpers every
//!   Span face leans on.
//! - `src/jcore_signed_duration.rs` (J4b): the SignedDuration core the
//!   composition consumes (sd_inv / sd_total_nanos, from_* / as_*
//!   constructors, checked_add, the sd_ops_* Add/Sub free fns).
//! - `src/jcore_span.rs` (J5): the Span core (struct, tier stack,
//!   setters, getters, negate).
//! - `src/jcore_span_arith.rs` (J8): to_invariant_duration /
//!   from_invariant_duration and the checked_add invariant chain.
//! - `src/time.rs` (J3): the civil time core the J8 reunion faces
//!   consume (Time, valid_time, until_nanoseconds, from_nanosecond).

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

#[path = "src/time.rs"]
mod time;

fn main() {}

#[path = "src/jcore_span_reunion.rs"]
mod jcore_span_reunion;
