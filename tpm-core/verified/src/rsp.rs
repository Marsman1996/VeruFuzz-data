//! tpm-core 0.1.4 response payload parsers (src/rsp.rs) -- Verus
//! translation.
//!
//! Faces re-erected: count/size bounds are checked before any slice is
//! taken; every returned slice is provably inside the input buffer;
//! the error kinds discriminate the wire-field faces. (The exact
//! byte-ordering faces of the banks loop are deferred -- the caller
//! faces that consume PcrBanks reopen them when the boot batch needs
//! the per-bank values; see the out/ ledger deferred list.)

use vstd::prelude::*;

verus! {

use super::cursor::{any_nonzero, Cursor};
use super::msg::ParseError;

/// Origin Rust: /// Upper bound on the number of PCR banks that can be allocated simultaneously.
/// const MAX_PCR_BANKS: usize = 5; (src/rsp.rs:3-4)
pub const MAX_PCR_BANKS: usize = 5;
/// Origin Rust: /// Accepted upper bound for `sizeofSelect`. The PC Client platform has a fixed 24 PCRs (3 bytes), and
/// this leaves some margin while rejecting arbitrary lengths from the peer.
/// const PCR_SELECT_MAX: usize = 8; (src/rsp.rs:5-7)
pub const PCR_SELECT_MAX: usize = 8;
/// Origin Rust: /// Upper bound on digest length (SHA-512).
/// const MAX_DIGEST_SIZE: usize = 64; (src/rsp.rs:8-9)
pub const MAX_DIGEST_SIZE: usize = 64;
pub const ALG_SHA1: u16 = 0x0004;
pub const ALG_SHA256: u16 = 0x000B;
pub const ALG_SHA384: u16 = 0x000C;
pub const ALG_SHA512: u16 = 0x000D;
pub const ALG_SM3_256: u16 = 0x0012;

/// Origin Rust: /// Length of a known algorithm's digest.
/// ///
/// /// Returning `0` means "this implementation does not recognize the algorithm" -- not an error, but a
/// signal that the length must be probed separately (by reading PCR 0 once). ... (src/rsp.rs:15-20)
pub open spec fn digest_size_of_spec(alg_id: u16) -> u16 {
    if alg_id == ALG_SHA1 {
        20u16
    } else if alg_id == ALG_SHA256 {
        32u16
    } else if alg_id == ALG_SHA384 {
        48u16
    } else if alg_id == ALG_SHA512 {
        64u16
    } else if alg_id == ALG_SM3_256 {
        32u16
    } else {
        0u16
    }
}

/// Origin Rust: fn digest_size_of(alg_id: u16) -> u16 (src/rsp.rs:21-35)
pub exec fn digest_size_of(alg_id: u16) -> (r: u16)
    ensures
        r == digest_size_of_spec(alg_id),
{
    if alg_id == ALG_SHA1 {
        20
    } else if alg_id == ALG_SHA256 {
        32
    } else if alg_id == ALG_SHA384 {
        48
    } else if alg_id == ALG_SHA512 {
        64
    } else if alg_id == ALG_SM3_256 {
        32
    } else {
        0
    }
}

// ------------------------------------------------------------------
// wire faces
// ------------------------------------------------------------------

/// count field of the GetCapability property/allocation payloads (wire
/// offset 5..9).
pub open spec fn getcap_wire_count(body: &[u8]) -> int {
    if (9 as int) <= (body.len() as int) {
        16777216 * (body@[5] as int)
            + 65536 * (body@[6] as int)
            + 256 * (body@[7] as int)
            + (body@[8] as int)
    } else {
        0
    }
}

/// first property value pair's value field of the TPM properties
/// payload (wire offset 13..17).
pub open spec fn prop_wire_value(body: &[u8]) -> int {
    if (17 as int) <= (body.len() as int) {
        16777216 * (body@[13] as int)
            + 65536 * (body@[14] as int)
            + 256 * (body@[15] as int)
            + (body@[16] as int)
    } else {
        0
    }
}

// ------------------------------------------------------------------
// parse_tpm_property (rsp.rs:36-60)
// ------------------------------------------------------------------

/// Origin Rust: /// Parse the return value of `TPM2_GetCapability(TPM_CAP_TPM_PROPERTIES)`.
/// ///
/// Payload layout (Part 3 30.2):
///
/// ```text
/// moreData      u8
/// capability    u32
/// count         u32
/// [property u32, value u32] * count
/// ```
/// A count of zero is a legal response (for example, when the peer is
/// in firmware-upgrade mode), but the caller cannot use any value
/// from it, so this is treated as "no data" rather than returning a
/// fabricated zero. (src/rsp.rs:36-60)
pub(crate) exec fn parse_tpm_property(body: &[u8]) -> (r: Result<u32, ParseError>)
    ensures
        match r {
            Result::Ok(v) =>
                (17 as int) <= (body.len() as int)
                    && (v as int) == prop_wire_value(body)
                    && getcap_wire_count(body) != 0,
            Result::Err(ParseError::Truncated) =>
                (body.len() as int) < 9
                    || ((9 as int) <= (body.len() as int)
                        && (body.len() as int) < 17
                        && getcap_wire_count(body) != 0),
            Result::Err(ParseError::Malformed) => false,
            Result::Err(ParseError::Capacity) => false,
            Result::Err(ParseError::Unsupported) =>
                (9 as int) <= (body.len() as int) && getcap_wire_count(body) == 0,
            Result::Err(ParseError::TpmError(_)) => false,
        },
{
    let mut c = Cursor::new();
    let _more = match c.read_u8(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let _cap = match c.read_be32(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let count = match c.read_be32(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if count == 0 {
        return Err(ParseError::Unsupported);
    }
    match c.read_be32(body) {
        Option::Some(_) => {
        }
        Option::None => return Err(ParseError::Truncated),
    }
    match c.read_be32(body) {
        Option::Some(v) => Ok(v),
        Option::None => return Err(ParseError::Truncated),
    }
}

// ------------------------------------------------------------------
// PcrBanks and parse_pcr_allocation (rsp.rs:61-121)
// ------------------------------------------------------------------

/// Origin Rust: /// Table of allocated PCR banks.
/// ///
/// `digest_sizes[i] == 0` means that the implementation does not recognize the algorithm for that
/// bank, and the length must be probed separately.
/// pub struct PcrBanks {
///     pub algs: [u16; 5], pub digest_sizes: [u16; 5], pub count: usize,
/// } (src/rsp.rs:61-69)
pub struct PcrBanks {
    pub algs: [u16; 5],
    pub digest_sizes: [u16; 5],
    pub count: usize,
}

impl PcrBanks {
    /// Origin Rust: pub fn empty() -> PcrBanks (src/rsp.rs:70-78)
    pub exec fn empty() -> (b: PcrBanks)
        ensures
            b.count == 0,
            forall|i: int| 0 <= i < 5 ==> b.algs@.index(i) == 0u16,
            forall|i: int| 0 <= i < 5 ==> b.digest_sizes@.index(i) == 0u16,
    {
        PcrBanks {
            algs: [0, 0, 0, 0, 0],
            digest_sizes: [0, 0, 0, 0, 0],
            count: 0,
        }
    }
}

/// Origin Rust: /// Parse `TPM2_GetCapability(TPM_CAP_PCRS)` and determine which banks are actually allocated.
/// ...
/// Three upper bounds constitute the entire safety argument of this function: `count <=
/// MAX_PCR_BANKS` limits the loop iterations, `sizeofSelect <= PCR_SELECT_MAX` limits the
/// per-iteration stride, and the cursor's `read_bytes` checks the bitmap value -- all three are
/// validated before use. (src/rsp.rs:79-95; the {--text--} layout block
/// rides the upstream doc)
pub exec fn parse_pcr_allocation(body: &[u8]) -> (r: Result<PcrBanks, ParseError>)
    ensures
        match r {
            Result::Ok(banks) =>
                (9 as int) <= (body.len() as int)
                    && (banks.count as int) <= (MAX_PCR_BANKS as int)
                    && getcap_wire_count(body) <= (MAX_PCR_BANKS as int),
            Result::Err(ParseError::Truncated) => true,
            Result::Err(ParseError::Malformed) =>
                (12 as int) <= (body.len() as int),
            Result::Err(ParseError::Capacity) =>
                (9 as int) <= (body.len() as int)
                    && getcap_wire_count(body) > (MAX_PCR_BANKS as int),
            Result::Err(ParseError::Unsupported) => false,
            Result::Err(ParseError::TpmError(_)) => false,
        },
{
    let mut c = Cursor::new();
    let _more = match c.read_u8(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let _cap = match c.read_be32(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let count = match c.read_be32(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if count > MAX_PCR_BANKS as u32 {
        return Err(ParseError::Capacity);
    }
    let mut banks = PcrBanks::empty();
    let mut iter: u32 = 0;
    while iter < count
        invariant
            iter <= count,
            (count as int) <= (MAX_PCR_BANKS as int),
            (banks.count as int) <= (iter as int),
            // cursor position folds the uniform 3-byte bank header
            // walk per processed iteration; only boundedness matters
            (9 as int) <= (c.pos as int),
            (c.pos as int) <= (body.len() as int),
        decreases
            count - iter,
    {
        let alg_id = match c.read_be16(body) {
            Option::Some(v) => v,
            Option::None => return Err(ParseError::Truncated),
        };
        let sel_size = match c.read_u8(body) {
            Option::Some(v) => v,
            Option::None => return Err(ParseError::Truncated),
        };
        if sel_size as usize > PCR_SELECT_MAX {
            return Err(ParseError::Malformed);
        }
        let select = match c.read_bytes(body, sel_size as usize) {
            Option::Some(s) => s,
            Option::None => return Err(ParseError::Truncated),
        };
        if any_nonzero(select) {
            banks.algs[banks.count] = alg_id;
            banks.digest_sizes[banks.count] = digest_size_of(alg_id);
            banks.count += 1;
        }
        iter += 1;
    }
    Ok(banks)
}

// ------------------------------------------------------------------
// PcrValue and parse_pcr_read (rsp.rs:122-166)
// ------------------------------------------------------------------

/// Origin Rust: /// Result of a single PCR read: algorithm ID + digest bytes.
/// pub struct PcrValue<'a> { pub alg_id: u16, pub digest: &'a [u8] }(src/rsp.rs:122-126)
pub struct PcrValue<'a> {
    pub alg_id: u16,
    pub digest: &'a [u8],
}

/// selection-count field (wire offset 4..8).
pub open spec fn pr_wire_sel_count(body: &[u8]) -> int {
    if (8 as int) <= (body.len() as int) {
        16777216 * (body@[4] as int)
            + 65536 * (body@[5] as int)
            + 256 * (body@[6] as int)
            + (body@[7] as int)
    } else {
        0
    }
}

/// hashAlg field (wire offset 8..10).
pub open spec fn pr_wire_alg(body: &[u8]) -> u16 {
    if (10 as int) <= (body.len() as int) {
        ((body@[8] as int) * 256 + (body@[9] as int)) as u16
    } else {
        0u16
    }
}

/// sizeofSelect byte (wire offset 10).
pub open spec fn pr_wire_sel_size(body: &[u8]) -> int {
    if (11 as int) <= (body.len() as int) {
        (body@[10] as int)
    } else {
        0
    }
}

/// digest-count field (wire offset 11+s .. 15+s, s the skipped
/// selection width).
pub open spec fn pr_wire_digest_count(body: &[u8]) -> int {
    let s = pr_wire_sel_size(body);
    if ((15 + s) as int) <= (body.len() as int) {
        16777216 * (body@[11 + s] as int)
            + 65536 * (body@[12 + s] as int)
            + 256 * (body@[13 + s] as int)
            + (body@[14 + s] as int)
    } else {
        0
    }
}

/// digest-size field (wire offset 15+s .. 17+s).
pub open spec fn pr_wire_digest_size(body: &[u8]) -> int {
    let s = pr_wire_sel_size(body);
    if ((17 + s) as int) <= (body.len() as int) {
        256 * (body@[15 + s] as int) + (body@[16 + s] as int)
    } else {
        0
    }
}

/// digest region start (wire offset 17+s).
pub open spec fn pr_digest_start(body: &[u8]) -> int {
    17 + pr_wire_sel_size(body)
}

/// Origin Rust: /// Parse a `TPM2_PCR_Read` response (Part 3 22.4).
/// ... Only the "one selection, one digest" form is accepted -- this
/// matches the request constructed by the command side. Any extra
/// response content from the peer is not guessed, and is rejected
/// outright. (src/rsp.rs:127-138)
pub exec fn parse_pcr_read(body: &[u8]) -> (r: Result<PcrValue, ParseError>)
    ensures
        match r {
            Result::Ok(pv) =>
                pr_wire_sel_count(body) == 1
                    && pr_wire_sel_size(body) <= (PCR_SELECT_MAX as int)
                    && pr_wire_digest_count(body) == 1
                    && pr_wire_digest_size(body) <= (MAX_DIGEST_SIZE as int)
                    && (pv.alg_id as int) == (pr_wire_alg(body) as int)
                    && pv.digest@ == body@.subrange(
                        pr_digest_start(body),
                        pr_digest_start(body) + pr_wire_digest_size(body),
                    ),
            Result::Err(ParseError::Truncated) => true,
            Result::Err(ParseError::Malformed) =>
                ((11 as int) <= (body.len() as int)
                    && pr_wire_sel_size(body) > (PCR_SELECT_MAX as int))
                    || ((17 + pr_wire_sel_size(body)) <= (body.len() as int)
                        && pr_wire_digest_size(body) > (MAX_DIGEST_SIZE as int)),
            Result::Err(ParseError::Capacity) => false,
            Result::Err(ParseError::Unsupported) =>
                ((8 as int) <= (body.len() as int)
                    && pr_wire_sel_count(body) != 1)
                    || (((15 + pr_wire_sel_size(body)) as int)
                        <= (body.len() as int)
                        && pr_wire_digest_count(body) != 1),
            Result::Err(ParseError::TpmError(_)) => false,
        },
{
    let mut c = Cursor::new();
    match c.read_be32(body) {
        Option::Some(_) => {
        }
        Option::None => return Err(ParseError::Truncated),
    }
    let sel_count = match c.read_be32(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if sel_count != 1 {
        return Err(ParseError::Unsupported);
    }
    let alg_id = match c.read_be16(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let sel_size = match c.read_u8(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if sel_size as usize > PCR_SELECT_MAX {
        return Err(ParseError::Malformed);
    }
    if !c.skip(body, sel_size as usize) {
        return Err(ParseError::Truncated);
    }
    let digest_count = match c.read_be32(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if digest_count != 1 {
        return Err(ParseError::Unsupported);
    }
    let digest_size = match c.read_be16(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if digest_size as usize > MAX_DIGEST_SIZE {
        return Err(ParseError::Malformed);
    }
    let digest = match c.read_bytes(body, digest_size as usize) {
        Option::Some(d) => d,
        Option::None => return Err(ParseError::Truncated),
    };
    Ok(PcrValue { alg_id, digest })
}

// ------------------------------------------------------------------
// parse_random (rsp.rs:167-180)
// ------------------------------------------------------------------

/// TPM2B size field (wire offset 0..2) of the GetRandom response.
pub open spec fn rnd_wire_size(body: &[u8]) -> int {
    if (2 as int) <= (body.len() as int) {
        256 * (body@[0] as int) + (body@[1] as int)
    } else {
        0
    }
}

/// Origin Rust: /// Parse a `TPM2_GetRandom` response (Part 3 16.1): a single `TPM2B_DIGEST`.
/// ///
/// This returns a borrowed slice rather than copying. The caller decides how many bytes to trim using
/// `max`; this layer only guarantees that the returned slice is within the payload and does not exceed the
/// length declared by the peer. (src/rsp.rs:167-171)
pub exec fn parse_random(body: &[u8], max: u16) -> (r: Result<&[u8], ParseError>)
    ensures
        match r {
            Result::Ok(s) =>
                (2 as int) <= (body.len() as int)
                    && rnd_wire_size(body) <= (max as int)
                    && ((2 + rnd_wire_size(body)) as int) <= (body.len() as int)
                    && s@ == body@.subrange(
                        2,
                        (2 + rnd_wire_size(body)) as int,
                    )
                    && (s@.len() as int) == rnd_wire_size(body),
            Result::Err(ParseError::Truncated) =>
                (body.len() as int) < 2
                    || (rnd_wire_size(body) <= (max as int)
                        && ((2 + rnd_wire_size(body)) as int) > (body.len() as int)),
            Result::Err(ParseError::Malformed) =>
                (2 as int) <= (body.len() as int)
                    && rnd_wire_size(body) > (max as int),
            Result::Err(ParseError::Capacity) => false,
            Result::Err(ParseError::Unsupported) => false,
            Result::Err(ParseError::TpmError(_)) => false,
        },
{
    let mut c = Cursor::new();
    let size = match c.read_be16(body) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if size > max {
        return Err(ParseError::Malformed);
    }
    match c.read_bytes(body, size as usize) {
        Option::Some(s) => Ok(s),
        Option::None => return Err(ParseError::Truncated),
    }
}

} // verus!
