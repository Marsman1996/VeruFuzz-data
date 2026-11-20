//! tpm-core 0.1.4 device-family probe (src/probe.rs) -- Verus
//! translation.
//!
//! Upstream face: one capability query against the link whose
//! response TAG alone decides the family -- 0x8001 (ST_NO_SESSIONS)
//! means TPM 2.0, anything else is conservatively classified 1.2
//! (probe.rs:1-66). The link is borrowed, not taken, so the boot
//! sequence can resume; the not-ready and transport-error cases
//! both fall back to the 1.2 lane ("do not enable the 2.0-specific
//! path" -- the doc's conservative-classification sentence).
//!
//! Re-erected here:
//!  - the full 22-byte query image (the same capability shape the
//!    boot property read uses, against PT_TOTAL_COMMANDS):
//!    u16::from_be_bytes lowered to the base-256 sum in usize,
//!    Origin-noted (the exact be16_of arithmetic, no truncation
//!    at that width);
//!  - the conservative-classification discipline on the public
//!    face: only an entry-ready link can classify TwoZero (the
//!    response's tag bytes are read against the local scratch
//!    buffer, which dies with this call -- the response-tag side
//!    of the classification stays structural in the body, exactly
//!    as upstream; the OneTwo arm covers the not-ready and the
//!    transport-error cases the doc names).

use vstd::prelude::*;

verus! {

use super::cmd::CC_GET_CAPABILITY;
use super::cursor::be32_bytes;
use super::msg::build_header;
use super::tis_core::TPM_HEADER_LEN;
use super::phy::TisPhy;
use super::tis::MAX_LOCALITY;
use super::xfer::Xfer;

// ------------------------------------------------------------------
// Constants (probe.rs:9-24)
// ------------------------------------------------------------------

/// Origin Rust: /// Property sub-item for probing: the total number of commands implemented by the device. Any such item
/// works -- the probe only looks at the response tag, not the payload.
/// const PT_TOTAL_COMMANDS: u32 = 0x0000_0129; (probe.rs:17-19)
/// Restated pub (Origin note): the twin's public image face cites
/// it; upstream keeps it file-private. Runtime value unchanged.
pub const PT_TOTAL_COMMANDS: u32 = 0x0000_0129;
/// Origin Rust: /// Total length of the probe command: 10-byte header + three u32 payload words.
/// const PROBE_LEN: usize = TPM_HEADER_LEN + 12; (probe.rs:20-21)
/// Restated pub (Origin note): same reason as PT_TOTAL_COMMANDS.
pub const PROBE_LEN: usize = TPM_HEADER_LEN + 12;
/// Origin Rust: /// Scratch buffer for the probe response. It only reads the first two bytes (tag), so a header-sized
/// margin is enough.
/// const PROBE_RSP: usize = 64; (probe.rs:22-24)
pub const PROBE_RSP: usize = 64;
/// The request tag of no-sessions packets (msg.rs pub(crate), the
/// boot.rs restatement precedent).
pub const ST_NO_SESSIONS: u16 = 0x8001;
/// The capability value of the fixed query (cmd.rs pub(crate), the
/// boot.rs restatement precedent).
pub const CAP_TPM_PROPERTIES: u32 = 0x0000_0006;

// ------------------------------------------------------------------
// Family (probe.rs:9-16)
// ------------------------------------------------------------------

/// Origin Rust: /// Device family.
/// #[derive(Clone, Copy, PartialEq, Eq)]
/// pub enum Family {
///     /// 1.2: use the `tpm1` path.
///     OneTwo,
///     /// 2.0: use the root session/authorization path.
///     TwoZero,
/// } (probe.rs:9-16; the derives carry no Verus twin)
pub enum Family {
    /// 1.2: use the `tpm1` path.
    OneTwo,
    /// 2.0: use the root session/authorization path.
    TwoZero,
}

/// Origin Rust: /// Determine the device family.
/// ///
/// /// This borrows the link to send a single command and returns immediately; the link remains owned by
/// /// the caller for the subsequent boot sequence to take over. If the link is not in a send-ready state, it is
/// /// conservatively classified as 1.2 -- do not enable the 2.0-specific path, even if it means admitting
/// /// less capability rather than misclassifying an unready device as 2.0 and running the authorization
/// /// handshake against it.
/// pub fn probe_family<P: TisPhy>(x: &mut Xfer<P>) -> Family {
///     if !x.ready() { return Family::OneTwo; }
///     ... assemble PROBE_LEN command ...
///     match x.run(&cmd, PROBE_LEN, &mut rsp) {
///         Ok((_n, _rc)) => { let tag = ...; if tag == ST_NO_SESSIONS { TwoZero } else { OneTwo } }
///         Err(_) => Family::OneTwo,
///     }
/// } (probe.rs:25-66; u16::from_be_bytes lowered to the base-256
/// sum in usize -- the exact be16_of arithmetic, no truncation
/// face needed at that width; the local scratch arrays keep the
/// fixed-image assembly faces)
pub exec fn probe_family<P: TisPhy>(x: &mut Xfer<P>) -> (r: Family)
    ensures
        // the conservative-classification discipline: only a ready
        // link, a completed round trip and a 2.0-shaped tag spell
        // the 2.0 lane
        match r {
            Family::TwoZero =>
                ((old(x).tis.locality as int) < (MAX_LOCALITY as int) && !old(x).tis.held),
            Family::OneTwo => true,
        },
{
    if !x.ready() {
        return Family::OneTwo;
    }
    let hdr = build_header(ST_NO_SESSIONS, CC_GET_CAPABILITY, PROBE_LEN as u32);
    let a = be32_bytes(CAP_TPM_PROPERTIES);
    let b = be32_bytes(PT_TOTAL_COMMANDS);
    let c = be32_bytes(1u32);
    let mut cmd = [0u8; PROBE_LEN];
    cmd[0] = hdr[0];
    cmd[1] = hdr[1];
    cmd[2] = hdr[2];
    cmd[3] = hdr[3];
    cmd[4] = hdr[4];
    cmd[5] = hdr[5];
    cmd[6] = hdr[6];
    cmd[7] = hdr[7];
    cmd[8] = hdr[8];
    cmd[9] = hdr[9];
    cmd[TPM_HEADER_LEN] = a[0];
    cmd[TPM_HEADER_LEN + 1] = a[1];
    cmd[TPM_HEADER_LEN + 2] = a[2];
    cmd[TPM_HEADER_LEN + 3] = a[3];
    cmd[TPM_HEADER_LEN + 4] = b[0];
    cmd[TPM_HEADER_LEN + 5] = b[1];
    cmd[TPM_HEADER_LEN + 6] = b[2];
    cmd[TPM_HEADER_LEN + 7] = b[3];
    cmd[TPM_HEADER_LEN + 8] = c[0];
    cmd[TPM_HEADER_LEN + 9] = c[1];
    cmd[TPM_HEADER_LEN + 10] = c[2];
    cmd[TPM_HEADER_LEN + 11] = c[3];
    let mut rsp = [0u8; PROBE_RSP];
    match x.run(&cmd, PROBE_LEN, &mut rsp) {
        Result::Ok((_n, _rc)) => {
            // u16::from_be_bytes lowered: the two tag bytes' base-256
            // sum compared against the tag constant
            let tag0 = (rsp[0] as usize) * 256;
            let tag1 = rsp[1] as usize;
            let tag = tag0 + tag1;
            if tag == (ST_NO_SESSIONS as usize) {
                Family::TwoZero
            } else {
                Family::OneTwo
            }
        }
        Result::Err(_) => Family::OneTwo,
    }
}

} // verus!
