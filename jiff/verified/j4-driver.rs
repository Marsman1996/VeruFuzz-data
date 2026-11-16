//! jiff J4 batch driver -- jiff-core Timestamp core (seconds +
//! nanosecond carry arithmetic), mounted standalone.
//!
//! `#[path]` mounts verified/src/jcore_timestamp.rs (the upstream
//! leaf-name mount; a future merge into src/lib.rs alongside the J1
//! files is deferred to the harness stage, per out/kverus-run/J4/
//! notes.md). The bit-set harness-mount precedent places the
//! `fn main()` tail here.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/jcore_timestamp.rs"]
mod jcore_timestamp;

fn main() {}
