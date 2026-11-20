//! tpm-core 0.1.4 command payload builders (src/cmd.rs) -- Verus
//! translation.
//!
//! Family face: every payload builder outputs the exact big-endian
//! layout its upstream doc block declares, and the selection-bitmap
//! builder keeps its below-24 single-selection property (the doc line
//! "the two approaches are equivalent for values below 24" is the
//! domain where the bitmap claims hold; see the suspects row for
//! pcr_idx >= 24 in the out/ ledger).

use vstd::prelude::*;

verus! {

use super::cursor::{be16_bytes, be16_bytes_spec, be32_bytes, be32_bytes_spec};

pub(crate) const CC_SELF_TEST: u32 = 0x0000_0143;
pub(crate) const CC_STARTUP: u32 = 0x0000_0144;
pub(crate) const CC_SHUTDOWN: u32 = 0x0000_0145;
pub(crate) const CC_CONTEXT_LOAD: u32 = 0x0000_0161;
pub(crate) const CC_CONTEXT_SAVE: u32 = 0x0000_0162;
pub(crate) const CC_FLUSH_CONTEXT: u32 = 0x0000_0165;
pub const CC_GET_CAPABILITY: u32 = 0x0000_017A;
pub(crate) const CC_GET_RANDOM: u32 = 0x0000_017B;
pub(crate) const CC_PCR_READ: u32 = 0x0000_017E;
pub(crate) const CC_PCR_EXTEND: u32 = 0x0000_0182;
pub const CAP_HANDLES: u32 = 0x0000_0001;
pub const CAP_COMMANDS: u32 = 0x0000_0002;
pub const CAP_PCRS: u32 = 0x0000_0005;
pub(crate) const CAP_TPM_PROPERTIES: u32 = 0x0000_0006;
pub const SU_CLEAR: u16 = 0x0000;
pub const SU_STATE: u16 = 0x0001;
/// Origin Rust: /// The PC Client platform has a fixed 24 PCRs (TCG PC Client PFP).
/// pub const PLATFORM_PCR: u32 = 24; (src/cmd.rs:19-20)
pub const PLATFORM_PCR: u32 = 24;
/// Origin Rust: /// Number of bytes required for the selection bitmap that covers 24 PCRs: ceil(24 / 8).
/// const PCR_SELECT_MIN: usize = 3; (src/cmd.rs:21-22)
pub(crate) const PCR_SELECT_MIN: usize = 3;
/// Origin Rust: /// Maximum size for a single random-data fetch. If the request is larger, it must be split over
/// multiple calls.
/// pub const MAX_RNG_DATA: u16 = 128; (src/cmd.rs:23-25)
pub const MAX_RNG_DATA: u16 = 128;

// SHA256_LEN lives in the crypto module upstream; fixed digest size
// for the pcr_extend payload (Part 3, SHA-256 = 32; upstream imports
/// crypto::SHA256_LEN).
pub(crate) const SHA256_LEN: usize = 32;

/// Origin Rust: fn bit_value(n: u32) -> u8 {
///     if n == 0 { 1 } else if ... else { 128 }
/// } (src/cmd.rs:26-44)
/// spec twin of the bit ladder.
pub open spec fn bit_value_of(n: u32) -> u8 {
    if n == 0u32 {
        1u8
    } else if n == 1u32 {
        2u8
    } else if n == 2u32 {
        4u8
    } else if n == 3u32 {
        8u8
    } else if n == 4u32 {
        16u8
    } else if n == 5u32 {
        32u8
    } else if n == 6u32 {
        64u8
    } else {
        128u8
    }
}

pub(crate) exec fn bit_value(n: u32) -> (r: u8)
    ensures
        r == bit_value_of(n),
{
    if n == 0 {
        1
    } else if n == 1 {
        2
    } else if n == 2 {
        4
    } else if n == 3 {
        8
    } else if n == 4 {
        16
    } else if n == 5 {
        32
    } else if n == 6 {
        64
    } else {
        128
    }
}

/// Origin Rust: /// Generate a selection bitmap that selects only a single PCR.
/// ...
/// fn pcr_select_bitmap(pcr_idx: u32) -> [u8; PCR_SELECT_MIN] (src/cmd.rs:45-60)
/// SPEC-DOC MISMATCH candidate (not filed): the doc line claims
/// "selects only a single PCR" without a domain note, but the bitmap
/// has 3 bytes and the third match arm parks any pcr_idx >= 24 onto
/// byte 2 -- pcr_idx 24 selects PCR 16 silently. The single-selection
/// bite below is proved for pcr_idx < 24 (the domain the upstream
/// comment restricts itself to a few lines later); the wrap has a
/// suspects row in the out/ ledger.
pub open spec fn pcr_select_bitmap_spec(pcr_idx: u32) -> Seq<u8> {
    let byte_idx = pcr_idx / 8;
    let mask = bit_value_of(pcr_idx % 8);
    if byte_idx == 0 {
        seq![mask, 0u8, 0u8]
    } else if byte_idx == 1 {
        seq![0u8, mask, 0u8]
    } else {
        seq![0u8, 0u8, mask]
    }
}

pub(crate) exec fn pcr_select_bitmap(pcr_idx: u32) -> (r: [u8; 3])
    ensures
        r@ == pcr_select_bitmap_spec(pcr_idx),
{
    let byte_idx = pcr_idx / 8;
    let mask = bit_value(pcr_idx % 8);
    if byte_idx == 0 {
        [mask, 0, 0]
    } else if byte_idx == 1 {
        [0, mask, 0]
    } else {
        [0, 0, mask]
    }
}

// ------------------------------------------------------------------
// PCR-selection semantics (the single-selection face below 24)
// ------------------------------------------------------------------

/// Truth of "bit position i is set in byte b", by the /, % ladder
/// over the constant powers of two (no bit-vector solver switch; the
/// ladder form matches the upstream note about feeding integer
/// reasoning directly).
pub open spec fn bit_set_at(b: u8, i: int) -> bool {
    if i == 0 {
        b % 2 == 1
    } else if i == 1 {
        b / 2 % 2 == 1
    } else if i == 2 {
        b / 4 % 2 == 1
    } else if i == 3 {
        b / 8 % 2 == 1
    } else if i == 4 {
        b / 16 % 2 == 1
    } else if i == 5 {
        b / 32 % 2 == 1
    } else if i == 6 {
        b / 64 % 2 == 1
    } else {
        b / 128 == 1
    }
}

/// Truth of "PCR index j is selected by a 3-byte selection bitmap".
pub open spec fn bitmap_selects(m: Seq<u8>, j: int) -> bool {
    0 <= j < 24 && m.len() == 3 && bit_set_at(m[j / 8], j % 8)
}

/// A mask byte selects exactly its own bit position among 0..8: the
/// k-th ladder value has its bit-k probe come back true and every
/// other bit probe come back false (proved by the full two-level
/// ladder -- every (k, i) leaf pins both skolem constants, so each
/// leaf folds a fixed-shift division).
pub(crate) proof fn lemma_mask_bit_exact(k: u32, i: int)
    requires
        0 <= k < 8,
        0 <= i < 8,
    ensures
        bit_set_at(bit_value_of(k), i) == (k as int == i),
{
    if i == 0 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 % 2 == 1) == true);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 % 2 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 % 2 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 % 2 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 % 2 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 % 2 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 % 2 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 % 2 == 1) == false);
        }
    } else if i == 1 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 2 % 2 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 2 % 2 == 1) == true);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 2 % 2 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 2 % 2 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 2 % 2 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 2 % 2 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 2 % 2 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 2 % 2 == 1) == false);
        }
    } else if i == 2 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 4 % 2 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 4 % 2 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 4 % 2 == 1) == true);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 4 % 2 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 4 % 2 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 4 % 2 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 4 % 2 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 4 % 2 == 1) == false);
        }
    } else if i == 3 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 8 % 2 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 8 % 2 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 8 % 2 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 8 % 2 == 1) == true);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 8 % 2 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 8 % 2 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 8 % 2 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 8 % 2 == 1) == false);
        }
    } else if i == 4 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 16 % 2 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 16 % 2 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 16 % 2 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 16 % 2 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 16 % 2 == 1) == true);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 16 % 2 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 16 % 2 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 16 % 2 == 1) == false);
        }
    } else if i == 5 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 32 % 2 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 32 % 2 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 32 % 2 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 32 % 2 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 32 % 2 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 32 % 2 == 1) == true);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 32 % 2 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 32 % 2 == 1) == false);
        }
    } else if i == 6 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 64 % 2 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 64 % 2 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 64 % 2 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 64 % 2 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 64 % 2 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 64 % 2 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 64 % 2 == 1) == true);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 64 % 2 == 1) == false);
        }
    } else if i == 7 {
        if k == 0u32 {
            assert(bit_value_of(k) == 1u8);
            assert((1u8 / 128 == 1) == false);
        }
        if k == 1u32 {
            assert(bit_value_of(k) == 2u8);
            assert((2u8 / 128 == 1) == false);
        }
        if k == 2u32 {
            assert(bit_value_of(k) == 4u8);
            assert((4u8 / 128 == 1) == false);
        }
        if k == 3u32 {
            assert(bit_value_of(k) == 8u8);
            assert((8u8 / 128 == 1) == false);
        }
        if k == 4u32 {
            assert(bit_value_of(k) == 16u8);
            assert((16u8 / 128 == 1) == false);
        }
        if k == 5u32 {
            assert(bit_value_of(k) == 32u8);
            assert((32u8 / 128 == 1) == false);
        }
        if k == 6u32 {
            assert(bit_value_of(k) == 64u8);
            assert((64u8 / 128 == 1) == false);
        }
        if k == 7u32 {
            assert(bit_value_of(k) == 128u8);
            assert((128u8 / 128 == 1) == true);
        }
    }
}

/// A zero byte selects nothing.
proof fn lemma_zero_bit_not_set(i: int)
    requires
        0 <= i < 8,
    ensures
        !bit_set_at(0u8, i),
{
    if i == 0 {
        assert(0u8 % 2 == 0);
    } else if i <= 1 {
        assert(0u8 / 2 == 0);
    } else if i <= 2 {
        assert(0u8 / 4 == 0);
    } else if i <= 3 {
        assert(0u8 / 8 == 0);
    } else if i <= 4 {
        assert(0u8 / 16 == 0);
    } else if i <= 5 {
        assert(0u8 / 32 == 0);
    } else if i <= 6 {
        assert(0u8 / 64 == 0);
    } else {
        assert(0u8 / 128 == 0);
    }
}

/// The upstream doc claim verbatim: the bitmap "selects only a single
/// PCR" -- provable exactly for indices below 24 (the domain the
/// upstream comment restricts itself to). For pcr_idx >= 24 the third
/// branch keeps a mask in byte 2 only, so the claim breaks (suspects
/// row in the out/ ledger, with the concrete wrap indices).
pub proof fn lemma_pcr_select_single(pcr_idx: u32)
    requires
        pcr_idx < 24,
    ensures
        bitmap_selects(pcr_select_bitmap_spec(pcr_idx), pcr_idx as int),
        forall|j: int|
            0 <= j < 24 && j != (pcr_idx as int)
                ==> !bitmap_selects(pcr_select_bitmap_spec(pcr_idx), j),
{
    let byte_idx = pcr_idx / 8;
    let bit_idx = pcr_idx % 8;
    let mask = bit_value_of(bit_idx);
    assert(pcr_idx as int == 8 * (byte_idx as int) + (bit_idx as int));
    // the own byte carries the mask; the other two bytes are zero
    if byte_idx == 0 {
        assert(pcr_select_bitmap_spec(pcr_idx).index(pcr_idx as int / 8) == mask);
        assert(pcr_select_bitmap_spec(pcr_idx).index(1) == 0u8);
        assert(pcr_select_bitmap_spec(pcr_idx).index(2) == 0u8);
    } else if byte_idx == 1 {
        assert(pcr_select_bitmap_spec(pcr_idx).index(0) == 0u8);
        assert(pcr_select_bitmap_spec(pcr_idx).index(pcr_idx as int / 8) == mask);
        assert(pcr_select_bitmap_spec(pcr_idx).index(2) == 0u8);
    } else {
        assert(pcr_select_bitmap_spec(pcr_idx).index(0) == 0u8);
        assert(pcr_select_bitmap_spec(pcr_idx).index(1) == 0u8);
        assert(pcr_select_bitmap_spec(pcr_idx).index(pcr_idx as int / 8) == mask);
    }
    lemma_mask_bit_exact(bit_idx, bit_idx as int);
    assert forall|j: int|
        0 <= j < 24 && j != (pcr_idx as int)
        implies !bitmap_selects(pcr_select_bitmap_spec(pcr_idx), j)
    by {
        if j / 8 == (pcr_idx as int) / 8 {
            lemma_mask_bit_exact(bit_idx, j % 8);
        } else {
            lemma_zero_bit_not_set(j % 8);
        }
    };
}

// ------------------------------------------------------------------
// Payload builders
// ------------------------------------------------------------------

/// Origin Rust: /// PCR handle value. ... The PCR handle type code is 0, so the handle value is simply the
/// PCR index itself. (src/cmd.rs:61-70)
pub fn pcr_handle(pcr_idx: u32) -> (r: u32)
    ensures
        r == pcr_idx,
{
    /* Origin Rust: pcr_handle body: `pcr_idx` (src/cmd.rs:69). */
    pcr_idx
}

/// Origin Rust: `TPM2_PCR_Read` payload (Part 3 22.4):
/// count u32 = 1, hashAlg u16, sizeofSelect u8 = 3, pcrSelect u8[3].
/// pub fn pcr_read_payload(alg_id: u16, pcr_idx: u32) -> [u8; 10] (src/cmd.rs:71-95)
pub fn pcr_read_payload(alg_id: u16, pcr_idx: u32) -> (r: [u8; 10])
    ensures
        r@ == be32_bytes_spec(1)
            .add(be16_bytes_spec(alg_id))
            .add(seq![3u8])
            .add(pcr_select_bitmap_spec(pcr_idx)),
{
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let sel = pcr_select_bitmap(pcr_idx);
    [
        cnt[0],
        cnt[1],
        cnt[2],
        cnt[3],
        alg[0],
        alg[1],
        PCR_SELECT_MIN as u8,
        sel[0],
        sel[1],
        sel[2],
    ]
}

/// Origin Rust: pub fn pcr_extend_payload(alg_id: u16, digest: &[u8; SHA256_LEN])
///     -> [u8; PCR_EXTEND_PARAM_LEN] where PCR_EXTEND_PARAM_LEN =
///     6 + SHA256_LEN = 38 (src/cmd.rs:97-135; the copy_from_slice of
/// the 32 digest bytes is lowered to the spelled element
/// assignments, same bytes; doc lines: "count u32 = 1, hashAlg u16,
/// digest u8[32]")
pub fn pcr_extend_payload(alg_id: u16, digest: &[u8; 32]) -> (r: [u8; 38])
    ensures
        r@ == be32_bytes_spec(1)
            .add(be16_bytes_spec(alg_id))
            .add(digest@),
{
    let cnt = be32_bytes(1);
    let alg = be16_bytes(alg_id);
    let mut out = [0u8; 38];
    out[0] = cnt[0];
    out[1] = cnt[1];
    out[2] = cnt[2];
    out[3] = cnt[3];
    out[4] = alg[0];
    out[5] = alg[1];
    out[6] = digest[0];
    out[7] = digest[1];
    out[8] = digest[2];
    out[9] = digest[3];
    out[10] = digest[4];
    out[11] = digest[5];
    out[12] = digest[6];
    out[13] = digest[7];
    out[14] = digest[8];
    out[15] = digest[9];
    out[16] = digest[10];
    out[17] = digest[11];
    out[18] = digest[12];
    out[19] = digest[13];
    out[20] = digest[14];
    out[21] = digest[15];
    out[22] = digest[16];
    out[23] = digest[17];
    out[24] = digest[18];
    out[25] = digest[19];
    out[26] = digest[20];
    out[27] = digest[21];
    out[28] = digest[22];
    out[29] = digest[23];
    out[30] = digest[24];
    out[31] = digest[25];
    out[32] = digest[26];
    out[33] = digest[27];
    out[34] = digest[28];
    out[35] = digest[29];
    out[36] = digest[30];
    out[37] = digest[31];
    out
}

/// Origin Rust: `TPM2_GetCapability` payload (Part 3 30.2):
/// capability u32, property u32, propertyCount u32.
/// pub fn get_capability_payload(capability: u32, property: u32, count: u32) -> [u8; 12]
/// (src/cmd.rs:136-150)
pub fn get_capability_payload(capability: u32, property: u32, count: u32) -> (r: [u8; 12])
    ensures
        r@ == be32_bytes_spec(capability)
            .add(be32_bytes_spec(property))
            .add(be32_bytes_spec(count)),
{
    let a = be32_bytes(capability);
    let b = be32_bytes(property);
    let c = be32_bytes(count);
    [
        a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3],
    ]
}

/// Origin Rust: `TPM2_GetRandom` payload (Part 3 16.1). The upper bound
/// is enforced at the type level ... the caller must split it itself
/// instead of relying on the peer to truncate it.
/// pub fn get_random_payload(bytes_requested: u16) -> [u8; 2] (src/cmd.rs:151-157)
pub fn get_random_payload(bytes_requested: u16) -> (r: [u8; 2])
    ensures
        r@ == be16_bytes_spec(bytes_requested),
{
    be16_bytes(bytes_requested)
}

/// Origin Rust: `TPM2_Shutdown` payload (Part 3 9.4).
/// pub fn shutdown_payload(shutdown_type: u16) -> [u8; 2] (src/cmd.rs:158-161)
pub fn shutdown_payload(shutdown_type: u16) -> (r: [u8; 2])
    ensures
        r@ == be16_bytes_spec(shutdown_type),
{
    be16_bytes(shutdown_type)
}

/// Origin Rust: `TPM2_FlushContext` payload (Part 3 28.4). The handle
/// follows the header and there is no authorization area.
/// pub fn flush_context_payload(handle: u32) -> [u8; 4] (src/cmd.rs:162-165)
pub fn flush_context_payload(handle: u32) -> (r: [u8; 4])
    ensures
        r@ == be32_bytes_spec(handle),
{
    be32_bytes(handle)
}

} // verus!
