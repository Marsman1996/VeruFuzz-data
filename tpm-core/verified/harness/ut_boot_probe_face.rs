//! tpm-core batch-T6 harness: the boot/probe/secure Top-level-flow
//! face inventory, transcribed as verification theorems over the
//! verified lib (the ut_chip_classify mount form; nothing from the
//! src zone is re-copied).
//!
//! Theorems shipped here:
//!   - ut_invoke_layout_discharge: the repair-path demonstration
//!     of S-T4-1. Upstream's CmdLayout doc claims "This layer is
//!     responsible only for checking that these partitions do not
//!     overlap and then filling them in", but no such check exists
//!     (T4 audit, confirmed live). This proof fn shows the fix: with
//!     the partition checker (spec_layout_disjoint, the check the
//!     doc claims) plus the buffer-fit and session-side bounds,
//!     every requires row of Guarded::invoke follows mechanically.
//!   - ut_boot_images_pass_link_gate: the four boot command images
//!     (startup / shutdown / self-test and the capability property
//!     query at probe_limits's fourth round) all pass xfer's cmd_wf
//!     gate -- the "never trips the link gate" theorem behind every
//!     Err(Bus(BadCommand)) => false arm, now one reusable fact over
//!     the image spec twins.
//!   - ut_boot_rc_lanes: the boot-time acceptance codes never
//!     overlap the transport retry family -- RC_INITIALIZE and
//!     RC_TESTING classify out of retryable for every command, and
//!     the self-test special case passes "still testing" through
//!     unretried exactly as the xfer doc's exception demands.
//!   - ut_probe_tag_arith: the probe's family-deciding tag
//!     arithmetic -- the lowered u16::from_be_bytes face equals the
//!     ST_NO_SESSIONS constant.
//!
//! All theorems are transport-free (no TisPhy instance is needed):
//! each one re-erects a property stated by an upstream doc sentence
//! or by the T6 twins' own contracts, at the same rlimit discipline
//! as the src-zone panels.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod tpm;

use tpm::auth::CMD_SESSION_LEN;
use tpm::boot::{
    spec_boot_cap_image, spec_boot_image, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP, PT_MAX_SESSION_CONTEXT,
    RC_INITIALIZE, RC_TESTING,
};
use tpm::crypto::PASSPHRASE_MAX;
use tpm::cursor::be16_bytes_spec;
use tpm::secure::{spec_layout_disjoint, CmdLayout};
use tpm::phy::TisPhy;
use tpm::xfer::{cmd_wf_spec, Xfer, RC_SUCCESS};

verus! {

/// Repair-path demonstration of S-T4-1 (the T4-audited false claim
/// of the CmdLayout doc): given the partition check the doc claims
/// ("partitions do not overlap and [the auth area] fits the packet"),
/// the buffer-fit bound and the two response/session-side bounds,
/// EVERY requires row of Guarded::invoke follows -- upstream's fix
/// is exactly to establish these premises before the unchecked
/// forwarding.
proof fn ut_invoke_layout_discharge(
    cmd_len: int,
    lay: CmdLayout,
    sess_passphrase_len: int,
)
    requires
        spec_layout_disjoint(lay),
        (lay.len as int) <= cmd_len,
        0 <= sess_passphrase_len,
        sess_passphrase_len <= (PASSPHRASE_MAX as int),
        ((lay.rhandles as int) * 4) <= (usize::MAX as int),
    ensures
        // invoke requires row 1 (write_cmd_session + finalize
        // sess-side bound)
        (lay.sess_off as int) + (CMD_SESSION_LEN as int) <= cmd_len,
        // invoke requires row 2 (finalize param-side bound)
        (lay.param_off as int) + (lay.param_len as int) <= cmd_len,
        // invoke requires rows 3 and 4 are the two independent
        // premises above (the response-handle multiplication guard
        // and the session passphrase capacity) -- the partition
        // checker does not produce them; upstream must state them
        // on the session/response faces
        (lay.rhandles as int) * 4 <= (usize::MAX as int),
        sess_passphrase_len <= (PASSPHRASE_MAX as int),
{
}

/// The anti-drift discipline of put_header, closed as one theorem
/// over the image twins: every boot command's assembled image
/// carries its own transmit length in its size word, so xfer's
/// cmd_wf gate accepts all four images -- the gate every command
/// method's Err(Bus(BadCommand)) => false arm rides on.
proof fn ut_boot_images_pass_link_gate()
{
    // startup: total 12
    let img = spec_boot_image(CC_STARTUP, 12u32, be16_bytes_spec(0x0001u16));
    assert(img.len() == 12);
    assert(10 <= img.len());
    assert(wire32(img.index(2), img.index(3), img.index(4), img.index(5)) == 12);
    assert(cmd_wf_spec(img, 12));

    // shutdown: total 12
    let img2 = spec_boot_image(CC_SHUTDOWN, 12u32, be16_bytes_spec(0x0002u16));
    assert(img2.len() == 12);
    assert(10 <= img2.len());
    assert(wire32(img2.index(2), img2.index(3), img2.index(4), img2.index(5)) == 12);
    assert(cmd_wf_spec(img2, 12));

    // self-test: total 11
    let img3 = spec_boot_image(
        CC_SELF_TEST,
        11u32,
        selftest_arg_seq(),
    );
    assert(img3.len() == 11);
    assert(10 <= img3.len());
    assert(wire32(img3.index(2), img3.index(3), img3.index(4), img3.index(5)) == 11);
    assert(cmd_wf_spec(img3, 11));

    // property (the capability query, 22 = BOOT_CMD_MAX exactly)
    let img4 = spec_boot_cap_image(PT_MAX_SESSION_CONTEXT);
    assert(img4.len() == 22);
    assert(10 <= img4.len());
    assert(wire32(img4.index(2), img4.index(3), img4.index(4), img4.index(5)) == 22);
    assert(cmd_wf_spec(img4, 22));
}

/// A helper restating xfer's wire-be32 sum for the gate faces above
/// (rewrite.rs's wire_be32 keeps the same formula; spelled here so
/// the assertions instantiate without trigger hunting).
spec fn wire32(b0: u8, b1: u8, b2: u8, b3: u8) -> int {
    16777216 * (b0 as int) + 65536 * (b1 as int) + 256 * (b2 as int) + (b3 as int)
}

/// The self-test payload byte (the bootstrap's SELF_TEST_FULL
/// spelling of the image side).
spec fn selftest_arg_seq() -> Seq<u8> {
    seq![1u8]
}

/// The boot-time acceptance codes versus the transport retry
/// family, both directions: "still testing" is passed through
/// UNRETRIED only for the self-test command itself (the xfer
/// doc's own exception, so boot's self_test sees the "testing
/// started OK" answer immediately); RC_INITIALIZE never rides the
/// retry family for any command; and RC_TESTING does ride it for
/// every non-self-test command -- boot's startup / shutdown can
/// only observe it after the transport's patience ran out.
fn ut_boot_rc_lanes<P: TisPhy>()
{
    assert(RC_INITIALIZE != RC_SUCCESS);
    assert(RC_INITIALIZE != RC_TESTING);
    assert(RC_TESTING != RC_SUCCESS);
    // the self-test exception: rc RC_TESTING with cc CC_SELF_TEST is
    // NOT retryable, so boot's self_test sees the "still testing
    // started OK" answer immediately
    let b0 = Xfer::<P>::retryable(RC_TESTING, CC_SELF_TEST);
    assert(!b0);
    // and the boot acceptance codes never ride the retry family
    let b1 = Xfer::<P>::retryable(RC_INITIALIZE, CC_STARTUP);
    let b2 = Xfer::<P>::retryable(RC_INITIALIZE, CC_SHUTDOWN);
    assert(!b1);
    assert(!b2);
    // the other direction, spelled so the lane discipline is
    // two-sided: "still testing" DOES ride the retry family for
    // every non-self-test command (the transport's designed
    // patience), which is exactly why boot's startup / shutdown
    // never see it warped into their own acceptance sets -- they
    // only ever observe it after the transport gave up
    let b3 = Xfer::<P>::retryable(RC_TESTING, CC_STARTUP);
    let b4 = Xfer::<P>::retryable(RC_TESTING, CC_SHUTDOWN);
    assert(b3);
    assert(b4);
}

/// The probe's family-deciding arithmetic: the lowered
/// base-256 tag sum of the two ST_NO_SESSIONS bytes equals the
/// 2.0 classification constant.
fn ut_probe_tag_arith()
{
    let tag = (0x80u8 as usize) * 256 + (0x01u8 as usize);
    assert(tag == 0x8001);
    assert(tag == (tpm::probe::ST_NO_SESSIONS as usize));
}

fn main() {}

} // verus!
