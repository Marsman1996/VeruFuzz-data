//! tpm-core T3 batch driver -- the CRB (command response buffer)
//! register-flow family, mounted standalone (the jiff j10/j11 driver
//! precedent). The driver's module tree replicates the crate paths
//! the batch's twins consume; src/lib.rs itself is untouched (T2 owns
//! it this window), so every module of the T1 src zone this batch
//! references is mounted here by path and re-verified in this run.
//!
//! Mounts (all read-only):
//! - `src/endian.rs` (T1): the word-decode spec twins be16_of/be32_of
//!   and their exec helpers.
//! - `src/cursor.rs` (T1): the read cursor (recv's header-field read
//!   rides read_be32's exact value face).
//! - `src/msg.rs` (T1): TPM_HEADER_LEN, the response header width.
//! - `src/crb.rs` (T3, this batch): register map, buffer caps,
//!   polling-budget arithmetic, CrbErr.
//! - `src/crb_phy.rs` (T3, this batch): the CrbPhy trust-boundary
//!   trait (spec faces only) and the two pure span checks.
//! - `src/crb_core.rs` (T3, this batch): the Crb driver state machine
//!   (request/relinquish locality, send, recv, transmit, exchange).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/endian.rs"]
mod endian;

#[path = "src/cursor.rs"]
mod cursor;

#[path = "src/msg.rs"]
mod msg;

#[path = "src/crb.rs"]
mod crb;

#[path = "src/crb_phy.rs"]
mod crb_phy;

#[path = "src/crb_core.rs"]
mod crb_core;

fn main() {}
