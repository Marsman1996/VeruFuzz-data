//! jiff J5 batch driver -- Span core arithmetic, mounted standalone.
//!
//! Mounts (all read-only, closed panels):
//! - `src/bounds.rs` (the J1 closed panel): this file's Span needs the
//!   `Sign` enum plus the `const_check` / `checked_mul` width-indexed
//!   range helpers; Sign's `From<i64>`/`Mul` cut faces are re-cut in
//!   src/jcore_span.rs itself (citing upstream jcore bounds.rs lines).
//! - `src/jcore_span.rs`: the J5 translation (span.rs constructor /
//!   getter / sign / checked_mul core plus SignedDuration::as_nanos64,
//!   the J4b-designated meeting point that lives in
//!   signed_duration.rs:997-1009 upstream, not in span.rs).
//!
//! `src/jcore_signed_duration.rs` IS mounted (the J4b closed panel,
//! re-verified as part of this driver's run): the batch's designated
//! meeting face `SignedDuration::as_nanos64` (upstream
//! signed_duration.rs:997-1009, whose gcd with span.rs the batch
//! grep pinned down) lives on the J4b type and consumes its
//! sd_inv / sd_total_nanos spec stack directly. The span-vs-span
//! checked_add path that would also want that mount is deferred
//! (see notes.md).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/bounds.rs"]
mod bounds;

#[path = "src/jcore_signed_duration.rs"]
mod jcore_signed_duration;

#[path = "src/jcore_span.rs"]
mod jcore_span;

fn main() {}
