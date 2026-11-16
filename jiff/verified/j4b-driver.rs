//! jiff J4b batch driver -- SignedDuration arithmetic core, mounted
//! standalone.
//!
//! `#[path]` mounts verified/src/jcore_signed_duration.rs only: the
//! translation is fully self-contained (inline time-unit constants, no
//! bounds.rs / lib.rs / jcore_timestamp.rs dependencies), so mounting
//! J1/J4's heavier panels adds nothing to the verification surface (the
//! signed-duration arithmetic core has no interaction with Timestamp
//! inside this batch's translated surface). The bit-set harness-mount
//! precedent places the `fn main()` tail here.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/jcore_signed_duration.rs"]
mod jcore_signed_duration;

fn main() {}
