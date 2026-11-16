//! jiff J11 batch driver -- the Span compare/total/fieldwise family,
//! mounted standalone (the j10-driver precedent; the batch's option a).
//! The driver's module tree replicates the lib.rs shape for the panels
//! this batch consumes; the closed panels it mounts are re-verified in
//! this run, so the expected panel sits near the j10 325-face baseline
//! plus the J11-owned obligations. src/lib.rs itself is untouched.
//!
//! Mounts (all read-only, closed panels except the J11 file):
//! - `src/bounds.rs` (J1): the Sign enum and range helpers.
//! - `src/constants.rs` (J2): the unit-constant layer.
//! - `src/jcore_signed_duration.rs` (J4b): the SignedDuration core
//!   (sd_inv / sd_total_nanos, the as_nanos edge the total face
//!   consumes).
//! - `src/jcore_span.rs` (J5): the Span core (struct, tier stack,
//!   setters, getters, negate, largest_unit, the sd64 lex geometry).
//! - `src/jcore_span_arith.rs` (J8): the composition spine
//!   (to_invariant_duration with its exact total-nanoseconds face,
//!   the unit-rank twins).
//! - `src/jcore_round.rs` (J10): the rounding family, for the shared
//!   faces this batch consumes (rm_unit_nanos for the total
//!   denominator, sr_requires_relative_err for the
//!   requires_relative_date_err guard).
//! - `src/jcore_span_total.rs` (J11, this batch): Span::fieldwise /
//!   SpanFieldwise, SpanCompare and Span::compare, SpanTotal and
//!   Span::total (the relative==None arms), the SpOrdering material
//!   and the lex-vs-total trichotomy bridge.

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

#[path = "src/jcore_span_total.rs"]
mod jcore_span_total;

fn main() {}
