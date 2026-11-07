//! Upstream code/base64ct/src/alphabet/shacrypt.rs mirror
//!
//! Upstream pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614; the code/ tree is unmodified.
//! Transcription notes (the same ledger conventions as standard.rs):
//! - The DECODER/ENCODER const array loops are unrolled in place (step order kept); the bit formulas go
//!   through the `*_term` semantic bridges of super.
//! - crypt(3) table: ['.'-'9']=0..11, A=12..37, a=38..63; the 2 ENCODER
//!   Apply steps are cumulative-diff typed, accumulated serially in the upstream execution order (as in bcrypt).
//! - Base64ShaCrypt additionally overrides the 3-byte packing (the crypt(3) big-endian order); its
//!   bit-level conclusion lives in super's decode_pack_crypt/encode_pack_indices_crypt.
//! - crypt and shacrypt have identical upstream tables; the separate domain here only mirrors the file split.
//! - Covered surface: the bit-level (6-bit table) layer; the table-level encode/decode drivers and the
//!   fixed-vector roundtrips (the impl_tests macro of tests/shacrypt.rs) are isomorphic to the proven std
//!   driver but not transcribed here (the SMT cost multiplies).

use vstd::prelude::*;

use super::decode_range_term;
use super::encode_apply_term;

verus! {

/* ============================================================
 * spec semantic tables
 * ============================================================ */

/// Origin: shacrypt.rs DECODER -- the semantic table ('.'-'9'=0..11, A=12..37, a=38..63)
pub open spec fn b64_digit_shacrypt(c: u8) -> int {
    if 0x2e <= c <= 0x39 {
        c as int - 0x2e
    } else if 0x41 <= c <= 0x5a {
        c as int - 0x41 + 12
    } else if 0x61 <= c <= 0x7a {
        c as int - 0x61 + 38
    } else {
        -1
    }
}

/// Origin: shacrypt.rs ENCODER -- the semantic table
pub open spec fn b64_char_shacrypt(v: int) -> u8 {
    if v <= 11 {
        (0x2e + v) as u8
    } else if v <= 37 {
        (0x41 + v - 12) as u8
    } else {
        (0x61 + v - 38) as u8
    }
}

/* ============================================================
 * exec table look-up (verbatim transcription, step order kept)
 * ============================================================ */

/// Origin: shacrypt.rs DECODER (the 3 Range steps unrolled in place; BASE='.')
/// Upstream doc (alphabet.rs:52-52):
///   Decode 6-bits of a Base64 message.
pub exec fn decode_6bits_shacrypt(src: u8) -> (ret: i16)
    ensures
        ret == b64_digit_shacrypt(src),
        ret == -1 || (0 <= ret <= 63),
{
    let mut ret: i16 = -1;
    let t0 = decode_range_term(0x2e, 0x39, -45, src);
    let t1 = decode_range_term(0x41, 0x5a, -52, src);
    let t2 = decode_range_term(0x61, 0x7a, -58, src);
    proof {
        if 0x2e <= src <= 0x39 {
            assert(t0 == src as int - 45);
        } else if 0x41 <= src <= 0x5a {
            assert(t1 == src as int - 52);
        } else if 0x61 <= src <= 0x7a {
            assert(t2 == src as int - 58);
        }
    }
    ret = ret + t0 + t1 + t2;
    ret
}

/// Origin: shacrypt.rs ENCODER -- Apply('9'=57,7), Apply('Z'=90,6) accumulated serially in the upstream order
/// Upstream doc (alphabet.rs:91-91):
///   Encode 6-bits of a Base64 message.
pub exec fn encode_6bits_shacrypt(src: i16) -> (r: u8)
    requires
        0 <= src <= 63,
    ensures
        r == b64_char_shacrypt(src as int),
{
    let mut diff: i16 = src + 0x2e;
    proof {
        assert(diff >= 0 && diff <= 150);
        assert(57 - diff >= -256 && 57 - diff <= 255);
    }
    let u1 = encode_apply_term(57, 7, diff);
    diff = diff + u1;
    proof {
        assert(diff >= 0 && diff <= 200);
        assert(90 - diff >= -256 && 90 - diff <= 255);
    }
    let u2 = encode_apply_term(90, 6, diff);
    diff = diff + u2;
    diff as u8
}

/* ============================================================
 * Shared lemmas (the standalone proof fn sits at the file tail)
 * ============================================================ */

/// decode_6bits o encode_6bits == id (the 6-bit-layer roundtrip)
pub exec fn enc6_roundtrip_shacrypt(v: i16) -> (r: i16)
    requires
        0 <= v <= 63,
    ensures
        r == v,
{
    let c = encode_6bits_shacrypt(v);
    decode_6bits_shacrypt(c)
}

// ===========================================================================
// Proof lemma (placed at the file end; signature and contract untouched)
// ===========================================================================
/// digit(char(v)) == v (the shacrypt alphabet inverse)
pub proof fn digit_char_inverse_shacrypt(v: int)
    requires
        0 <= v < 64,
    ensures
        b64_digit_shacrypt(b64_char_shacrypt(v)) == v,
{
    if v <= 11 {
    } else if v <= 37 {
    } else {
    }
}
} // verus!
