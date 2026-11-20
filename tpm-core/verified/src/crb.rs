//! tpm-core 0.1.4 CRB 2.0 control-area register constants (src/crb.rs)
//! -- Verus translation.
//!
//! Bank T3 (CRB command/response buffer flow). This layer models the
//! CRB 2.0 control-area register semantics according to TCG PTP and
//! covers only the memory-mapped / command-buffer startup mode:
//! commands are triggered by writing the INVOKE bit in ctrl_start,
//! and completion is signaled when the device clears that bit itself
//! (upstream header comment, src/crb.rs:1-7). The register map and
//! the polling-budget arithmetic live here; the driver state machine
//! (src/crb_core.rs) and the trust-boundary trait (src/crb_phy.rs)
//! mount in the sibling twin files.
//!
//! Visibility note (T1-4 precedent): the constants referenced by the
//! public spec faces of this batch (CMD_BUF_CAP, RSP_BUF_CAP,
//! MAX_LOCALITY, POLL_INTERVAL_MS) are opened pub from the upstream
//! pub(crate); every constant a public ensures names must be public,
//! so the register constants that appear only inside exec bodies keep
//! their upstream pub(crate) visibility. Runtime faces are unchanged.

use vstd::prelude::*;

verus! {

// ===================================================================
// Control register offsets (src/crb.rs:9-20)
// ===================================================================

/// Origin Rust: pub(crate) const REG_LOC_STATE: u32 = 0x0000; (src/crb.rs:13)
pub(crate) const REG_LOC_STATE: u32 = 0x0000;
/// Origin Rust: pub(crate) const REG_LOC_CTRL: u32 = 0x0008; (src/crb.rs:14)
pub(crate) const REG_LOC_CTRL: u32 = 0x0008;
/// Origin Rust: pub(crate) const REG_CTRL_REQ: u32 = 0x0040; (src/crb.rs:15)
pub(crate) const REG_CTRL_REQ: u32 = 0x0040;
/// Origin Rust: pub(crate) const REG_CTRL_STS: u32 = 0x0044; (src/crb.rs:16)
pub(crate) const REG_CTRL_STS: u32 = 0x0044;
/// Origin Rust: pub(crate) const REG_CTRL_CANCEL: u32 = 0x0048; (src/crb.rs:17)
pub(crate) const REG_CTRL_CANCEL: u32 = 0x0048;
/// Origin Rust: pub(crate) const REG_CTRL_START: u32 = 0x004C; (src/crb.rs:18)
pub(crate) const REG_CTRL_START: u32 = 0x004C;
/// Origin Rust: pub(crate) const REG_CTRL_CMD_SIZE: u32 = 0x0058; (src/crb.rs:19)
pub(crate) const REG_CTRL_CMD_SIZE: u32 = 0x0058;
/// Origin Rust: pub const REG_CTRL_RSP_SIZE: u32 = 0x0064; (src/crb.rs:20)
pub const REG_CTRL_RSP_SIZE: u32 = 0x0064;

// ===================================================================
// Register bits (src/crb.rs:22-39)
// ===================================================================

/// Origin Rust: pub(crate) const LOC_CTRL_REQUEST: u32 = 0x01; (src/crb.rs:26)
pub(crate) const LOC_CTRL_REQUEST: u32 = 0x01;
/// Origin Rust: pub(crate) const LOC_CTRL_RELINQUISH: u32 = 0x02; (src/crb.rs:27)
pub(crate) const LOC_CTRL_RELINQUISH: u32 = 0x02;

/// Origin Rust: pub(crate) const LOC_STATE_ASSIGNED: u32 = 0x02; (src/crb.rs:29)
pub(crate) const LOC_STATE_ASSIGNED: u32 = 0x02;
/// Origin Rust: pub(crate) const LOC_STATE_VALID: u32 = 0x80; (src/crb.rs:30)
pub(crate) const LOC_STATE_VALID: u32 = 0x80;

/// Origin Rust: pub(crate) const CTRL_REQ_CMD_READY: u32 = 0x01; (src/crb.rs:32)
pub(crate) const CTRL_REQ_CMD_READY: u32 = 0x01;
/// Origin Rust: pub(crate) const CTRL_REQ_GO_IDLE: u32 = 0x02; (src/crb.rs:33)
pub(crate) const CTRL_REQ_GO_IDLE: u32 = 0x02;

/// Origin Rust: pub(crate) const CTRL_STS_ERROR: u32 = 0x01; (src/crb.rs:35)
pub(crate) const CTRL_STS_ERROR: u32 = 0x01;

/// Origin Rust: pub(crate) const CTRL_START_INVOKE: u32 = 0x01; (src/crb.rs:37)
pub(crate) const CTRL_START_INVOKE: u32 = 0x01;

/// Origin Rust: pub(crate) const CTRL_CANCEL_CLEAR: u32 = 0x00; (src/crb.rs:39)
pub(crate) const CTRL_CANCEL_CLEAR: u32 = 0x00;

// ===================================================================
// Buffer mapping upper bounds (src/crb.rs:41-46)
// ===================================================================

/// Origin Rust: pub(crate) const CMD_BUF_CAP: usize = 4096; (src/crb.rs:45)
/// Opened pub: the public send ensures names this bound (ghost-only
/// visibility relaxation, upstream face pub(crate)).
pub const CMD_BUF_CAP: usize = 4096;
/// Origin Rust: pub(crate) const RSP_BUF_CAP: usize = 4096; (src/crb.rs:46)
/// Opened pub for the public recv ensures, same note as CMD_BUF_CAP.
pub const RSP_BUF_CAP: usize = 4096;

// ===================================================================
// locality value range (src/crb.rs:48-52)
// ===================================================================

/// Origin Rust: pub const MAX_LOCALITY: u8 = 5; (src/crb.rs:52)
pub const MAX_LOCALITY: u8 = 5;

// ===================================================================
// polling budget (src/crb.rs:54-75)
// ===================================================================

/// Origin Rust: pub const POLL_INTERVAL_MS: u32 = 1; (src/crb.rs:58)
pub const POLL_INTERVAL_MS: u32 = 1;
/// Origin Rust: /// Timeout for handshake actions (locality, cmd_ready, go_idle).
/// pub const TIMEOUT_C_MS: u32 = 750; (src/crb.rs:60-61)
pub const TIMEOUT_C_MS: u32 = 750;
/// Origin Rust: /// Timeout for command completion.
/// pub(crate) const TIMEOUT_LONG_MS: u32 = 4000; (src/crb.rs:63-64)
pub(crate) const TIMEOUT_LONG_MS: u32 = 4000;

/// Origin Rust: /// Convert millisecond timeout to polling count, returning at least 1.
/// #[inline]
/// pub fn budget_of(timeout_ms: u32) -> u32 {
///     let n = timeout_ms / POLL_INTERVAL_MS;
///     if n == 0 { 1 } else { n }
/// } (src/crb.rs:66-75; exact face: the returned count is the interval
/// quotient when non-zero, else 1; never below one poll).
pub exec fn budget_of(timeout_ms: u32) -> (r: u32)
    ensures
        ((timeout_ms as int) / (POLL_INTERVAL_MS as int)) == 0 ==> r == 1,
        ((timeout_ms as int) / (POLL_INTERVAL_MS as int)) > 0 ==> (r as int)
            == ((timeout_ms as int) / (POLL_INTERVAL_MS as int)),
        (r as int) >= 1,
{
    let n = timeout_ms / POLL_INTERVAL_MS;
    if n == 0 {
        1
    } else {
        n
    }
}

// ===================================================================
// Errors (src/crb.rs:77-91)
// ===================================================================

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum CrbErr {
///     /// Physical-layer error. The bus itself is malfunctioning.
///     Phy,
///     /// Polling budget exhausted.
///     Timeout,
///     /// Device state does not match the specification.
///     Protocol,
///     /// Command or response length is invalid.
///     BadLength,
/// } (src/crb.rs:81-91; the Clone/Copy/PartialEq/Eq/Debug derives
/// have no Verus twin -- no exec code in this tree compares or prints
/// CrbErr values; spec-mode equality is structural, the T1
/// ParseError precedent).
pub enum CrbErr {
    /// Physical-layer error. The bus itself is malfunctioning.
    Phy,
    /// Polling budget exhausted.
    Timeout,
    /// Device state does not match the specification.
    Protocol,
    /// Command or response length is invalid.
    BadLength,
}

} // verus!
