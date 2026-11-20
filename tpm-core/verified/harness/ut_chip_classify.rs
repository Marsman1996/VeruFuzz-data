//! tpm-core batch-T5 harness: the upstream inline unit test
//! `context_load_rc_handle_short_response_is_not_protocol`
//! (code/src/chip.rs:208-237, test fn at chip.rs:221), transcribed
//! as verification theorems.
//!
//! Upstream UT shape (chip.rs:221-236): a FakeChip transport whose
//! response is exactly the 10-byte header with return code
//! 0x0000_008B (TPM_RC_HANDLE), a command blob of CTX_FIXED (18)
//! zero bytes, and the assertion that CtxIo::load classifies the
//! error as Err(IoErr::NotFound) -- i.e. the return-code
//! classification check (chip.rs:165-168) takes precedence over
//! the short-response span check (chip.rs:169-172), so the caller
//! forgets the slot instead of treating the chip as broken.
//!
//! Theorems shipped here:
//!   - ut_rc_handle_classifies_not_found: the exact classification
//!     of the UT's return code rc = 0x8B (the classification-side
//!     content of the upstream assert).
//!   - ut_format1_mask_precedence: a TPM_RC_HANDLE response with
//!     the Format-1 selector bit (TPM_RC_P) and a nonzero handle
//!     index still classifies NotFound -- the upstream doc's own
//!     warning case ("TPM_RC_HANDLE | P | N would be
//!     misclassified" without the mask).
//!   - ut_short_header_response_shape: the FakeChip's 10-byte
//!     response, built exactly as the upstream test builds it
//!     (arr[6] = 0x00; arr[7] = 0x00; arr[8] = 0x00; arr[9] =
//!     0x8B), has its rc word equal 0x8B, and 0x8B is not
//!     RC_SUCCESS -- the "short response is not protocol-broken"
//!     evidence, per the load body's preserved check order
//!     (classification before span).
//!   - ut_classification_table_distinct: the no-space and timeout
//!     classes stay distinct from NotFound over their documented
//!     codes, and an off-table code stays Fatal (the "relaxing
//!     this would silently swallow state inconsistencies"
//!     boundary).
//!
//! INTEGRATION-FORM NOTE (deferred record D-T5-4): replaying the
//! upstream assert end-to-end through CtxIo::load would require
//! the verified adapter to expose which of its exits produced an
//! error value; this build's generic single-verification model
//! keeps transport-propagated and locally-derived errors
//! inseparable in the final state (the #T4-11 dichotomy limit), so
//! the adapter-level Err arms are open and the UT is carried as
//! the classification theorems above plus the structurally
//! preserved check order in the verified load body (the
//! classification return sits BEFORE the span rejection there;
//! Origin-noted in chip.rs).

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod tpm;

use tpm::chip::{classify_rc, rc_value, spec_rc_value, RC_SUCCESS};
use tpm::module::IoErr;
use tpm::rewrite::wire_be32;

verus! {

/// Upstream UT (chip.rs:221), classification side: rc =
/// TPM_RC_HANDLE classifies NotFound.
fn ut_rc_handle_classifies_not_found()
{
    let e = classify_rc(0x0000_008Bu32);
    let hit = match e {
        IoErr::NotFound => true,
        _ => false,
    };
    assert(hit);
    // and the masked value is exactly the handle code
    let v = rc_value(0x0000_008Bu32);
    assert(v == 0x0000_008Bu32);
}

/// The Format-1 mask caveat of the upstream doc (chip.rs:13-18):
/// TPM_RC_HANDLE | P | (index << 8) must still classify NotFound.
/// 0x19CB = 0x8B | 0x40 | 3 << 8: bit 7 set (Format-1), bit 6 set
/// (TPM_RC_P), index 3.
fn ut_format1_mask_precedence()
{
    let v = rc_value(0x0000_19CBu32);
    assert(v == 0x0000_008Bu32);
    let e = classify_rc(0x0000_19CBu32);
    let hit = match e {
        IoErr::NotFound => true,
        _ => false,
    };
    assert(hit);
    // spec-level echo of the same fact over the mask twin
    assert(spec_rc_value(0x0000_19CBu32) == 0x8B);
}

/// The FakeChip response shape of the upstream test (chip.rs:223-
/// 232): a 10-byte header whose rc word at offset 6 is 0x8B -- a
/// nonzero rc, so the verified load's classification arm fires
/// before the short-response span rejection.
fn ut_short_header_response_shape()
{
    let mut arr = [0u8; 10];
    arr[6] = 0x00;
    arr[7] = 0x00;
    arr[8] = 0x00;
    arr[9] = 0x8B;
    // the rc word of exactly these bytes is the UT's handle code
    assert(wire_be32(arr@, 6) == 0x8B);
    assert(wire_be32(arr@, 6) != RC_SUCCESS);
    // so the classification the load body performs at its rc
    // branch is NotFound, and the response's span (10 bytes, one
    // header short of a handle word) never gets to speak first
    let e = classify_rc(0x0000_008Bu32);
    let hit = match e {
        IoErr::NotFound => true,
        _ => false,
    };
    assert(hit);
}

/// The classification table keeps the three recoverable classes
/// and the Fatal default in their documented lanes
/// (chip.rs:36-59).
fn ut_classification_table_distinct()
{
    let e_mem = classify_rc(0x0000_0902u32);
    let mem = match e_mem {
        IoErr::NoSpace => true,
        _ => false,
    };
    assert(mem);

    let e_retry = classify_rc(0x0000_0922u32);
    let retry = match e_retry {
        IoErr::Timeout => true,
        _ => false,
    };
    assert(retry);

    let e_intg = classify_rc(0x0000_009Fu32);
    let intg = match e_intg {
        IoErr::Integrity => true,
        _ => false,
    };
    assert(intg);

    // off-table value stays Fatal
    let e_fatal = classify_rc(0x0000_0005u32);
    let fatal = match e_fatal {
        IoErr::Fatal => true,
        _ => false,
    };
    assert(fatal);
}

fn main() {}

} // verus!
