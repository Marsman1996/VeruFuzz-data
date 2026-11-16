//! jiff 0.2.43 (pin 627c7358, crates/jiff) -- root of the Verus
//! transcription tree. Current batch: the bounded-integer foundation of
//! crates/jiff-core/src/bounds.rs (the Bounds trait surface, the
//! define_bounds! template instances, const_check / const_checked_add /
//! checked_mul, Sign, and next_multiple_of), all mounted as `mod bounds`.
//!
//! Modeling ledger (single source per face; downstream batches mount
//! here, nothing is re-copied):
//! 1. Result<T, BoundsError> surfaces materialize as Option<T>: the
//!    upstream error value is a zero-sized witness (RawBoundsError is
//!    PhantomData-only, BoundsError only brands a kind), so Option::None
//!    is the complete error face; error message text is not verified.
//! 2. The 30+ macro-generated boundary types share one template
//!    (bounds.rs:26-137); two representative instantiations (Month i8
//!    1..=12, Year i16 -9999..=9999) are transcribed against a spec-only
//!    Interval model, the rest are the same template with different
//!    interval constants.
//! 3. The `Primitive` cast trait dissolves into direct casts (bit-vec
//!    BitBlock precedent); const fn materializes as exec fn (no const
//!    verification in this build); `impl Into<i64>` parameters
//!    materialize as the direct i64 parameter.
//! 4. Sign's core::ops (Neg, Mul) and From<iX>/From<f64> faces are
//!    outside this batch's listed surface; from_ordinals materializes at
//!    the i64 and i16 widths (other widths are the same template).

mod bounds;

// Batch J2 (append-only additions, per the batch discipline);
// `date` is pub so the J2 harness (verified/harness/quickcheck_date.rs)
// can mount this crate root and reach the spec faces.
mod constants;
pub mod date;

// Batch J3 (append-only additions, per the batch discipline); `time`
// is pub for the same harness-mount reason
// (verified/harness/quickcheck_time.rs).
pub mod time;

// Batch J6 (append-only additions, per the batch discipline); the civil
// datetime reassembly core and the weekday core; both pub for the harness
// mount (verified/harness/quickcheck_weekday.rs).
pub mod datetime;
pub mod weekday;

// Verification driver (single-file driver form; downstream harness files
// reference this crate root instead of duplicating content).

// Batch J7 (append-only additions, per the batch discipline); the
// Neri-Schneider turnover family (weekday shift, day-of-year accessors,
// from_day_of_year walks, era, and the informative NS twins the frozen
// J2 date.rs faces could not carry); pub for eventual harness mounts.
pub mod calendar;

fn main() {}
