//! jiff J13 batch driver -- the J12 reunion-seat closeout (the
//! j12-driver mounts plus weekday/calendar: the seats' union at one
//! fatter step toward the j9 neighborhood). Two aims, one mount:
//! 1. Re-verify the J12 seat family (jcore_relative_seats.rs) at 0
//!    errors: the J12 run's single non-green obligation was the
//!    closed jcore_span_arith arm sp_fid_arm_second, which flipped
//!    inside the J12 union at both rlimit 300 and 600 while staying
//!    green on its home j11-driver (the pitfall-59/61 fatter-mount
//!    form). Evicting jcore_span_arith from this mount is NOT
//!    structurally possible: jcore_round.rs, jcore_span_total.rs,
//!    jcore_span_relative.rs and jcore_relative_seats.rs all import
//!    its faces (the closed round/total panels included), so the
//!    honest closeout route for a union that carries the seats is
//!    COMPOSITION: this driver re-measures the arith spine in a new
//!    union (the j9 mount's calendar/weekday/relative additions --
//!    the same neighbors inside which the spine verifies green on
//!    j9-driver at 549 v0e), and the arith panel's own driver
//!    (j11-driver, 359 v0e) stays the arbiter per the J9 precedent.
//! 2. Mount the j9-neighborhood civil tree additions (weekday,
//!    calendar) -- NOT jcore_span_relative.rs itself in this cycle
//!    (see the cycle-c2 ledger note below): the seats' Civil-variable
//!    value lanes (Some(Some(dt))) consume the relative calendar
//!    pipeline's faces, and the routing stays deferred with the NS
//!    reverse family (the batch notes carry the root cause).
//!
//! Mounts (all read-only, closed panels except the J12 file):
//! - the full src/lib.rs module tree (bounds, constants, date, time,
//!   weekday, datetime, calendar) -- the J1-J7 civil panels (the
//!   j9-driver precedent; weekday/calendar are jcore_span_relative
//!   dependencies).
//! - `src/jcore_signed_duration.rs` (J4b): the SignedDuration core.
//! - `src/jcore_span.rs` (J5): the Span core.
//! - `src/jcore_span_arith.rs` (J8): the invariant-duration spine
//!   (imported by the round/total/relative/seats panels; its own
//!   arbiter is j11-driver).
//! - `src/jcore_round.rs` (J10): the rounding family.
//! - `src/jcore_span_total.rs` (J11): the compare/total family.
//! - `src/jcore_span_relative.rs` (J9): the relative calendar
//!   pipeline (first time mounted next to the seats).
//! - `src/jcore_relative_seats.rs` (J12, this batch's seat file;
//!   the flaky jcore_span_reunion.rs stays unmounted per pitfall 61).
//!
//! BATCH LEDGER UPDATE (cycle c2): this driver ran first WITH
//! jcore_span_relative mounted (run-c1: 680 verified, 1 error) and
//! the single flip was the closed relative file's obligation
//! rel_dt_since_span (jcore_span_relative.rs:3071 -- its ensures'
//! exists-quantifier picked a different auto trigger inside this
//! union; the pitfall-59/61 drift shape, at the third closed panel
//! in a row), while jcore_span_arith's sp_fid_arm_second -- the
//! J12 flake this batch was told to cure -- verified GREEN in this
//! same composition. The seats import the arith/round/total panels
//! but NOT the relative panel, so cycle c2 drops the relative
//! mount (and only it) to close the seats' union at 0 errors; the
//! arith spine's own arbiter stays j11-driver. The relative mount +
//! the Civil-variable value routing stay deferred with their root
//! cause recorded in the batch notes (the lanes need the J7 NS
//! reverse family).

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

#[path = "src/jcore_round.rs"]
mod jcore_round;

#[path = "src/jcore_span_total.rs"]
mod jcore_span_total;

// Cycle c2: the relative mount is dropped (see the batch ledger
// note above); the seats file does not import it.
// #[path = "src/jcore_span_relative.rs"]
// mod jcore_span_relative;

#[path = "src/jcore_relative_seats.rs"]
mod jcore_relative_seats;

fn main() {}
