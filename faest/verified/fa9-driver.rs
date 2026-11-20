//! faest FA9 batch driver -- the parameter.rs constant tower, mounted
//! standalone (the jiff j10/j11 and tpm t3/t4 driver precedents).
//! src/lib.rs is NOT mounted: the FA2 batch holds lib.rs this window
//! (its mod lines for the fields panel), and lib.rs carries no
//! verified content of its own beyond the module tree -- so the FA1
//! faces this batch consumes are mounted here by path, in the t3
//! shape. The closed panels are re-verified in this run; no FA1 file
//! is modified.
//!
//! Mounts (all read-only, closed panels except the FA9 file):
//! - `src/parameter.rs` (FA1): the tau table (12 configurations),
//!   the WGRIND and OWF-Lambda pins, and the tau-offset exec/spec
//!   faces.
//! - `src/utils.rs` (FA1): the challenge-decode and byte-utility
//!   family, consuming the FA1 parameter pins through the same
//!   module-relative use the lib.rs form has.
//! - `src/parameter_tower.rs` (FA9, this batch): the remaining
//!   constant groups (universal hashing padding B, the three
//!   BaseParameters levels, the six OWFParameters rows, the twelve
//!   FAESTParameters SIGNATURE_SIZE/decom pins), the spec mirrors of
//!   the upstream typenum chains, the get_decom_size exec twin, and
//!   the constant-identity theorem set.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/utils.rs"]
mod utils;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

fn main() {}
