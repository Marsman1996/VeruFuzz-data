//! tpm-core 0.1.4 TIS register constants and address arithmetic
//! (src/tis.rs) -- Verus translation.
//!
//! Upstream face: the ACCESS_*/STS_* bit constants, the four
//! per-locality register addresses, and the millisecond-to-budget
//! conversion (src/tis.rs:1-54). The verifiable properties re-erected
//! here: every register stays inside its own locality window
//! (base = locality * 4096), the four offsets are pairwise distinct
//! across all locality pairs, and budget_of is always at least one
//! (the polling-count face the upstream doc states at tis.rs:32-35).

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------
// Register bit constants (tis.rs:1-10)
// ------------------------------------------------------------------

/// Origin Rust: pub(crate) const ACCESS_VALID: u8 = 0x80; (tis.rs:1)
pub(crate) const ACCESS_VALID: u8 = 0x80;
/// Origin Rust: pub(crate) const ACCESS_ACTIVE_LOCALITY: u8 = 0x20; (tis.rs:2)
pub(crate) const ACCESS_ACTIVE_LOCALITY: u8 = 0x20;
/// Origin Rust: pub const ACCESS_REQUEST_PENDING: u8 = 0x04; (tis.rs:3)
pub const ACCESS_REQUEST_PENDING: u8 = 0x04;
/// Origin Rust: pub(crate) const ACCESS_REQUEST_USE: u8 = 0x02; (tis.rs:4)
pub(crate) const ACCESS_REQUEST_USE: u8 = 0x02;
/// Origin Rust: pub(crate) const STS_VALID: u8 = 0x80; (tis.rs:5)
pub(crate) const STS_VALID: u8 = 0x80;
/// Origin Rust: pub(crate) const STS_COMMAND_READY: u8 = 0x40; (tis.rs:6)
pub(crate) const STS_COMMAND_READY: u8 = 0x40;
/// Origin Rust: pub(crate) const STS_GO: u8 = 0x20; (tis.rs:7)
pub(crate) const STS_GO: u8 = 0x20;
/// Origin Rust: pub(crate) const STS_DATA_AVAIL: u8 = 0x10; (tis.rs:8)
pub(crate) const STS_DATA_AVAIL: u8 = 0x10;
/// Origin Rust: pub(crate) const STS_DATA_EXPECT: u8 = 0x08; (tis.rs:9)
pub(crate) const STS_DATA_EXPECT: u8 = 0x08;
/// Origin Rust: pub const STS_RESPONSE_RETRY: u8 = 0x02; (tis.rs:10)
pub const STS_RESPONSE_RETRY: u8 = 0x02;

/// Origin Rust: /// Allowed locality value range.
/// pub const MAX_LOCALITY: u8 = 5; (tis.rs:11-12)
pub const MAX_LOCALITY: u8 = 5;

// ------------------------------------------------------------------
// Register addresses (tis.rs:13-24)
// ------------------------------------------------------------------

/// Offsets of the four TIS registers inside one locality window of
/// 4096 bytes (spec twins of the exec address arithmetic below).
pub open spec fn tis_reg_offset_access() -> int {
    0
}

/// Status register offset 0x18.
pub open spec fn tis_reg_offset_sts() -> int {
    0x18
}

/// Data FIFO offset 0x24.
pub open spec fn tis_reg_offset_fifo() -> int {
    0x24
}

/// DID/VID offset 0x0F00.
pub open spec fn tis_reg_offset_did_vid() -> int {
    0x0F00
}

/// Locality base address of the TIS register window (l * 4096).
pub open spec fn tis_reg_base(l: u8) -> int {
    (l as int) * 4096
}

/// Origin Rust: pub(crate) fn reg_access(l: u8) -> u32 {
///     (l as u32) * 4096u32
/// } (tis.rs:13-15)
pub(crate) exec fn reg_access(l: u8) -> (r: u32)
    ensures
        r as int == tis_reg_base(l) + tis_reg_offset_access(),
{
    (l as u32) * 4096u32
}

/// Origin Rust: pub(crate) fn reg_sts(l: u8) -> u32 {
///     0x0018u32 + (l as u32) * 4096u32
/// } (tis.rs:16-18)
pub(crate) exec fn reg_sts(l: u8) -> (r: u32)
    ensures
        r as int == tis_reg_base(l) + tis_reg_offset_sts(),
{
    0x0018u32 + (l as u32) * 4096u32
}

/// Origin Rust: pub(crate) fn reg_data_fifo(l: u8) -> u32 {
///     0x0024u32 + (l as u32) * 4096u32
/// } (tis.rs:19-21)
pub(crate) exec fn reg_data_fifo(l: u8) -> (r: u32)
    ensures
        r as int == tis_reg_base(l) + tis_reg_offset_fifo(),
{
    0x0024u32 + (l as u32) * 4096u32
}

/// Origin Rust: pub fn reg_did_vid(l: u8) -> u32 {
///     0x0F00u32 + (l as u32) * 4096u32
/// } (tis.rs:22-24)
pub exec fn reg_did_vid(l: u8) -> (r: u32)
    ensures
        r as int == tis_reg_base(l) + tis_reg_offset_did_vid(),
{
    0x0F00u32 + (l as u32) * 4096u32
}

// ------------------------------------------------------------------
// Polling interval and timeouts (tis.rs:25-31)
// ------------------------------------------------------------------

/// Origin Rust: /// Single polling interval in milliseconds.
/// pub const POLL_INTERVAL_MS: u32 = 1; (tis.rs:25-26)
pub const POLL_INTERVAL_MS: u32 = 1;

/// Origin Rust: /// Four timeout tiers defined by the specification, in milliseconds.
/// pub(crate) const TIMEOUT_A_MS: u32 = 750; (tis.rs:27-28)
pub(crate) const TIMEOUT_A_MS: u32 = 750;
/// Origin Rust: pub(crate) const TIMEOUT_B_MS: u32 = 30000; (tis.rs:29)
pub(crate) const TIMEOUT_B_MS: u32 = 30000;
/// Origin Rust: pub const TIMEOUT_C_MS: u32 = 750; (tis.rs:30)
pub const TIMEOUT_C_MS: u32 = 750;
/// Origin Rust: pub const TIMEOUT_D_MS: u32 = 750; (tis.rs:31)
pub const TIMEOUT_D_MS: u32 = 750;

// ------------------------------------------------------------------
// Polling budget (tis.rs:32-43)
// ------------------------------------------------------------------

/// Origin Rust: /// Convert a millisecond timeout to a polling budget.
/// ///
/// /// It always returns at least one: a loop with a zero budget that declares a timeout without reading a
/// /// single register is a configuration error, not a runtime race.
/// pub fn budget_of(timeout_ms: u32) -> u32 {
///     let n = timeout_ms / POLL_INTERVAL_MS;
///     if n == 0 { 1 } else { n }
/// } (tis.rs:32-43; the doc's "at least one" claim is carried as
/// the lower-bound postcondition)
pub exec fn budget_of(timeout_ms: u32) -> (r: u32)
    ensures
        r >= 1,
        timeout_ms == 0 ==> r == 1,
        timeout_ms >= 1 ==> r == timeout_ms,
{
    let n = timeout_ms / POLL_INTERVAL_MS;
    assert(n == timeout_ms);
    if n == 0 {
        1
    } else {
        n
    }
}

// ------------------------------------------------------------------
// Error type (tis.rs:44-54)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum TisErr {
///     /// Physical-layer error; the bus itself is broken, and retries are pointless.
///     Phy,
///     /// Polling budget exhausted.
///     Timeout,
///     /// Device state does not match the specification.
///     Protocol,
///     /// The peer declared a length shorter than a message header or beyond the receive buffer.
///     BadLength,
/// } (tis.rs:44-54; the derives have no Verus twin -- no exec code in
/// this tree compares TisErr values by ==; per-variant doc lines kept
/// verbatim above)
pub enum TisErr {
    /// Physical-layer error; the bus itself is broken, and retries are pointless.
    Phy,
    /// Polling budget exhausted.
    Timeout,
    /// Device state does not match the specification.
    Protocol,
    /// The peer declared a length shorter than a message header or beyond the receive buffer.
    BadLength,
}

// ------------------------------------------------------------------
// Register-address lemmas (file tail per the proof zone banner).
// ------------------------------------------------------------------

/// The four TIS register addresses of any two localities never
/// collide, and each address map is injective in the locality: two
/// equal addresses imply the same register offset and the same
/// locality. All four offsets (0x00, 0x18, 0x24, 0x0F00) lie inside
/// one 4096-byte locality window and are pairwise distinct, so
/// offset + 4096 * l1 == offset' + 4096 * l2 with offset != offset'
/// would need 4096 to divide a difference strictly below 4096.
pub(crate) proof fn lemma_reg_addresses_distinct()
    ensures
        forall|l1: u8, l2: u8|
            tis_reg_base(l1) + tis_reg_offset_did_vid()
                != tis_reg_base(l2) + tis_reg_offset_access(),
        forall|l1: u8, l2: u8|
            tis_reg_base(l1) + tis_reg_offset_did_vid()
                != tis_reg_base(l2) + tis_reg_offset_sts(),
        forall|l1: u8, l2: u8|
            tis_reg_base(l1) + tis_reg_offset_did_vid()
                != tis_reg_base(l2) + tis_reg_offset_fifo(),
        forall|l1: u8, l2: u8|
            tis_reg_base(l1) + tis_reg_offset_fifo()
                != tis_reg_base(l2) + tis_reg_offset_sts(),
        forall|l1: u8, l2: u8|
            tis_reg_base(l1) + tis_reg_offset_fifo()
                != tis_reg_base(l2) + tis_reg_offset_access(),
        forall|l1: u8, l2: u8|
            tis_reg_base(l1) + tis_reg_offset_sts()
                != tis_reg_base(l2) + tis_reg_offset_access(),
        forall|l1: u8, l2: u8|
            (tis_reg_base(l1) + tis_reg_offset_access()
                == tis_reg_base(l2) + tis_reg_offset_access())
                <==> l1 == l2,
        forall|l1: u8, l2: u8|
            (tis_reg_base(l1) + tis_reg_offset_sts()
                == tis_reg_base(l2) + tis_reg_offset_sts())
                <==> l1 == l2,
        forall|l1: u8, l2: u8|
            (tis_reg_base(l1) + tis_reg_offset_fifo()
                == tis_reg_base(l2) + tis_reg_offset_fifo())
                <==> l1 == l2,
        forall|l1: u8, l2: u8|
            (tis_reg_base(l1) + tis_reg_offset_did_vid()
                == tis_reg_base(l2) + tis_reg_offset_did_vid())
                <==> l1 == l2,
{
    // the exec twins reg_access / reg_sts / reg_data_fifo /
    // reg_did_vid each satisfy r == offset + l * 4096 (their own
    // ensures), so this lemma transports to each exec address
    // Cross-offset collisions are impossible: 4096 * (l1 - l2) would
    // have to equal a nonzero offset difference of magnitude below
    // 4096, and on the u8 range any nonzero multiple of 4096 is at
    // least 4096 away from zero.
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_did_vid()
            == tis_reg_base(l2) + tis_reg_offset_access()
        implies false
    by {
        assert(tis_reg_offset_did_vid() == 3840 && tis_reg_offset_access() == 0);
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
        assert((l1 as int) != (l2 as int) ==> (4096 * ((l1 as int) - (l2 as int))) <= -4096 || (4096 * ((l1 as int) - (l2 as int))) >= 4096);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_did_vid()
            == tis_reg_base(l2) + tis_reg_offset_sts()
        implies false
    by {
        assert(tis_reg_offset_did_vid() == 3840 && tis_reg_offset_sts() == 24);
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
        assert((l1 as int) != (l2 as int) ==> (4096 * ((l1 as int) - (l2 as int))) <= -4096 || (4096 * ((l1 as int) - (l2 as int))) >= 4096);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_did_vid()
            == tis_reg_base(l2) + tis_reg_offset_fifo()
        implies false
    by {
        assert(tis_reg_offset_did_vid() == 3840 && tis_reg_offset_fifo() == 36);
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
        assert((l1 as int) != (l2 as int) ==> (4096 * ((l1 as int) - (l2 as int))) <= -4096 || (4096 * ((l1 as int) - (l2 as int))) >= 4096);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_fifo()
            == tis_reg_base(l2) + tis_reg_offset_sts()
        implies false
    by {
        assert(tis_reg_offset_fifo() == 36 && tis_reg_offset_sts() == 24);
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
        assert((l1 as int) != (l2 as int) ==> (4096 * ((l1 as int) - (l2 as int))) <= -4096 || (4096 * ((l1 as int) - (l2 as int))) >= 4096);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_fifo()
            == tis_reg_base(l2) + tis_reg_offset_access()
        implies false
    by {
        assert(tis_reg_offset_fifo() == 36 && tis_reg_offset_access() == 0);
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
        assert((l1 as int) != (l2 as int) ==> (4096 * ((l1 as int) - (l2 as int))) <= -4096 || (4096 * ((l1 as int) - (l2 as int))) >= 4096);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_sts()
            == tis_reg_base(l2) + tis_reg_offset_access()
        implies false
    by {
        assert(tis_reg_offset_sts() == 24 && tis_reg_offset_access() == 0);
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
        assert((l1 as int) != (l2 as int) ==> (4096 * ((l1 as int) - (l2 as int))) <= -4096 || (4096 * ((l1 as int) - (l2 as int))) >= 4096);
    }
    // Same-offset maps are injective on the u8 range.
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_access()
            == tis_reg_base(l2) + tis_reg_offset_access()
        implies (l1 as int) == (l2 as int)
    by {
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_sts()
            == tis_reg_base(l2) + tis_reg_offset_sts()
        implies (l1 as int) == (l2 as int)
    by {
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_fifo()
            == tis_reg_base(l2) + tis_reg_offset_fifo()
        implies (l1 as int) == (l2 as int)
    by {
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
    }
    assert forall|l1: u8, l2: u8|
        tis_reg_base(l1) + tis_reg_offset_did_vid()
            == tis_reg_base(l2) + tis_reg_offset_did_vid()
        implies (l1 as int) == (l2 as int)
    by {
        assert((l1 as int) <= 255 && (l2 as int) <= 255);
    }
    // And the trivial direction: same locality gives same address.
    assert forall|l1: u8, l2: u8|
        l1 == l2 implies tis_reg_base(l1) + tis_reg_offset_did_vid()
            == tis_reg_base(l2) + tis_reg_offset_did_vid()
    by {}
    assert forall|l1: u8, l2: u8|
        l1 == l2 implies tis_reg_base(l1) + tis_reg_offset_access()
            == tis_reg_base(l2) + tis_reg_offset_access()
    by {}
    assert forall|l1: u8, l2: u8|
        l1 == l2 implies tis_reg_base(l1) + tis_reg_offset_sts()
            == tis_reg_base(l2) + tis_reg_offset_sts()
    by {}
    assert forall|l1: u8, l2: u8|
        l1 == l2 implies tis_reg_base(l1) + tis_reg_offset_fifo()
            == tis_reg_base(l2) + tis_reg_offset_fifo()
    by {}
}

} // verus!
