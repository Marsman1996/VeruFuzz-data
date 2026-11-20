//! tpm-core 0.1.4 endian conversion helpers (src/endian.rs) -- Verus
//! translation.
//!
//! Upstream face: the private word-decode pair be16_of_exec /
//! be32_of_exec (src/endian.rs:1-6). The spec twins below re-erect the
//! word-value faces that the verified sibling branch points at through
//! the cursor.rs doc headers ("the inverse of spec_be16_at" -- those
//! spec fns are not part of this runtime tree, so the twin carries
//! their name forward as be16_of / be32_of).

use vstd::prelude::*;

verus! {

/// Word value of a big-endian byte pair (the face the verified branch
/// names `spec_be16_at`).
pub open spec fn be16_of(b0: u8, b1: u8) -> int {
    256 * (b0 as int) + (b1 as int)
}

/// Word value of a big-endian byte quadruple (`spec_be32_at`).
pub open spec fn be32_of(b0: u8, b1: u8, b2: u8, b3: u8) -> int {
    16777216 * (b0 as int)
        + 65536 * (b1 as int)
        + 256 * (b2 as int)
        + (b3 as int)
}

/// Origin Rust: pub(crate) fn be16_of_exec(b0: u8, b1: u8) -> u16 {
///     u16::from_be_bytes([b0, b1])
/// } (src/endian.rs:1-3; the from_be_bytes spelling is lowered to the
/// explicit weighted sum, same value face).
pub(crate) exec fn be16_of_exec(b0: u8, b1: u8) -> (v: u16)
    ensures
        (v as int) == be16_of(b0, b1),
{
    let hi = (b0 as u16) * 256u16;
    let lo = b1 as u16;
    hi + lo
}

/// Origin Rust: pub(crate) fn be32_of_exec(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
///     u32::from_be_bytes([b0, b1, b2, b3])
/// } (src/endian.rs:4-6; lowered to the explicit weighted sum).
pub(crate) exec fn be32_of_exec(b0: u8, b1: u8, b2: u8, b3: u8) -> (v: u32)
    ensures
        (v as int) == be32_of(b0, b1, b2, b3),
{
    let w3 = (b0 as u32) * 16777216u32;
    let w2 = (b1 as u32) * 65536u32;
    let w1 = (b2 as u32) * 256u32;
    let w0 = b3 as u32;
    let a = w3 + w2;
    let b = w1 + w0;
    a + b
}

// ------------------------------------------------------------------
// Bridge lemmas (word value vs byte-sequence roundtrips).
// ------------------------------------------------------------------

/// be16 roundtrip: the big-endian quotient/remainder split of any u16
/// re-decodes to the same word (the spec-level core; the exec twin
/// be16_of_exec carries its own ensures, so this lemma feeds the byte
/// faces pulled from a wire slice).
proof fn lemma_be16_roundtrip(v: u16)
    ensures
        be16_of((v / 256) as u8, (v % 256) as u8) == v as int,
{
    assert(v as int <= 65535);
    assert((v as int / 256) <= 255);
    assert(256 * (v as int / 256) + (v as int % 256) == v as int);
}

/// be32 roundtrip: decoding the big-endian encoding of any u32 gives
/// back the word.
proof fn lemma_be32_roundtrip(v: u32)
    ensures
        be32_of(
            (v / 16777216) as u8,
            (v / 65536 % 256) as u8,
            (v / 256 % 256) as u8,
            (v % 256) as u8,
        ) == v as int,
{
    assert(v as int <= 4294967295);
    assert((v as int / 16777216) <= 255);
    assert(((v as int / 65536) % 256) == ((v as int / 65536) - 256 * (v as int / 16777216)));
    assert(((v as int / 256) % 256) == ((v as int / 256) - 256 * (v as int / 65536)));
    assert(
        16777216 * (v as int / 16777216)
            + 65536 * ((v as int / 65536) % 256)
            + 256 * ((v as int / 256) % 256)
            + (v as int % 256)
            == v as int
    );
}

} // verus!
