//! tpm-core batch T4 driver -- the session and authorization family
//! (upstream family D: src/crypto.rs, src/auth.rs, src/session.rs),
//! mounted standalone (the jiff j10/j11 driver precedent; T1's own
//! single driver lives in src/lib.rs and stays untouched -- this
//! driver remounts the closed T1 panels it consumes plus the three
//! T4 files, so the reported panel covers the batch's own
//! obligations over the already-verified dependency set).
//!
//! Mounts (all read-only):
//! - `src/endian.rs`, `src/cursor.rs` (T1): the be16/be32 bridge seed
//!   pair and the parsing Cursor (position-discipline faces that
//!   parse_rsp_auth consumes).
//! - `src/types.rs` (T1): the tag/rc constant layer pulled in by the
//!   buf mount below.
//! - `src/buf.rs` (T1): the same_outside_range window-preservation
//!   spec helper that the T4 layout writers reuse (single source of
//!   verified facts; nothing re-copied).
//! - `src/crypto.rs` (T4): trust-boundary traits with ghost update
//!   streams, the trusted digest/HMAC oracles, and the single-round
//!   kdfa32.
//! - `src/auth.rs` (T4): the authorization-area layout write pair
//!   (write_cmd_session / patch_hmac), the full-supervision
//!   parse_rsp_auth, and the constant-trip ct_eq32 core.
//! - `src/session.rs` (T4): the AuthSession state machine
//!   (open_session / set_passphrase / begin / finalize /
//!   check_response / close), cfb_material, and the parameter
//!   encryption pass-throughs.
//!
//! The trailing empty main satisfies the standalone-file invocation
//! form (T1 lib.rs driver precedent).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/endian.rs"]
mod endian;

#[path = "src/cursor.rs"]
mod cursor;

#[path = "src/types.rs"]
mod types;

#[path = "src/buf.rs"]
mod buf;

#[path = "src/crypto.rs"]
mod crypto;

#[path = "src/auth.rs"]
mod auth;

#[path = "src/session.rs"]
mod session;

fn main() {}
