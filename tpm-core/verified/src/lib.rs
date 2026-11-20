//! tpm-core 0.1.4 (repo root src/lib.rs) -- Verus transcription tree,
//! crate root.
//!
//! Mirrors the upstream module tree (src/lib.rs) restricted to the
//! batches already transcribed. This file carries the byte/word decode
//! and buffer accounting family (upstream src/endian.rs, cursor.rs,
//! types.rs, buf.rs, cmd.rs, msg.rs, rsp.rs); the protocol, session,
//! and handle-space families mount in later batches. Module visibility
//! is here opened pub for the harness mounts that reference this file
//! via #[path] (single source of verified facts; nothing re-copied).
//!
//! The upstream module tree is no_std with an empty dependency list;
//! this twin runs on the vstd prelude only.

use vstd::prelude::*;

pub mod crypto;
pub mod auth;
pub mod session;

pub mod handle;
pub mod rewrite;
pub mod table;
pub mod chip;
pub mod module;
pub mod xfer;
pub mod secure;
pub mod boot;
pub mod probe;

pub mod buf;
pub mod cmd;
pub mod cursor;
pub mod endian;
pub mod msg;
pub mod rsp;
pub mod types;
pub mod mmio;
pub mod phy;
pub mod tis;
pub mod tis_core;

pub use buf::{BufKind, TpmBuf, TPM2B_HEADER_SIZE, TPM_HEADER_SIZE};
pub use msg::{ParseError, Response};
pub use rsp::{PcrBanks, PcrValue};
pub use types::{TpmRc, TpmTag};
pub use mmio::{TisMmio, TisMmioBackend};
pub use phy::TisPhy;
pub use tis::{TisErr, MAX_LOCALITY};
pub use tis_core::Tis;

// Verification driver (single-file driver form; the trailing empty
// main satisfies the standalone-file invocation; the harness zone never
// duplicates this file's content).
fn main() {}
