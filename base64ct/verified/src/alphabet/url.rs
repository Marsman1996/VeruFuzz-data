//!
//! Upstream pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614; the code/ tree is unmodified.
//! Transcription notes (the same ledger conventions as standard.rs):
//! - The DECODER/ENCODER const array loops are unrolled in place (step order kept); the bit formulas go
//!   through the `*_term` semantic bridges of super.
//! - The type difference is only the PADDED const bit plus the tables; semantics are carried by table fns.
//! - Covered surface: the bit-level (6-bit table) layer; the table-level encode/decode drivers and the
//!   fixed-vector roundtrips (the impl_tests macro of tests/url.rs) are isomorphic to the proven std
//!   driver but not transcribed here (the SMT cost multiplies).

use vstd::prelude::*;

use super::decode_eq_term;
use super::decode_range_term;
use super::encode_apply_term;
use super::encode_diff_term;

verus! {

/* ============================================================
 * spec semantic tables
 * ============================================================ */

/// Origin: url.rs DECODER -- the semantic table (62='-', 63='_')
pub open spec fn b64_digit_url(c: u8) -> int {
    if 0x41 <= c <= 0x5a {
        c as int - 0x41
    } else if 0x61 <= c <= 0x7a {
        c as int - 0x61 + 26
    } else if 0x30 <= c <= 0x39 {
        c as int - 0x30 + 52
    } else if c == 0x2d {
        62
    } else if c == 0x5f {
        63
    } else {
        -1
    }
}

/// Origin: url.rs ENCODER -- the semantic table
pub open spec fn b64_char_url(v: int) -> u8 {
    if v <= 25 {
        (0x41 + v) as u8
    } else if v <= 51 {
        (0x61 + v - 26) as u8
    } else if v <= 61 {
        (0x30 + v - 52) as u8
    } else if v == 62 {
        0x2d
    } else {
        0x5f
    }
}

/* ============================================================
 * exec table look-up (verbatim transcription, step order kept)
 * ============================================================ */

/// Origin: url.rs:41-47 DECODER (the 5 steps unrolled in place)
/// Upstream doc (alphabet.rs:52-52):
///   Decode 6-bits of a Base64 message.
pub exec fn decode_6bits_url(src: u8) -> (ret: i16)
    ensures
        ret == b64_digit_url(src),
        ret == -1 || (0 <= ret <= 63),
{
    let mut ret: i16 = -1;
    let t0 = decode_range_term(0x41, 0x5a, -64, src);
    let t1 = decode_range_term(0x61, 0x7a, -70, src);
    let t2 = decode_range_term(0x30, 0x39, 5, src);
    let t3 = decode_eq_term(0x2d, 63, src);
    let t4 = decode_eq_term(0x5f, 64, src);
    proof {
        if 0x41 <= src <= 0x5a {
            assert(t0 == src as int - 64);
        } else if 0x61 <= src <= 0x7a {
            assert(t1 == src as int - 70);
        } else if 0x30 <= src <= 0x39 {
            assert(t2 == src as int + 5);
        } else if src == 0x2d {
            assert(t3 == 63);
        } else if src == 0x5f {
            assert(t4 == 64);
        }
    }
    ret = ret + t0 + t1 + t2 + t3 + t4;
    ret
}

/// Origin: url.rs:49-56 ENCODER (direct sum of the 4 Diff steps; BASE='A')
/// Upstream doc (alphabet.rs:91-91):
///   Encode 6-bits of a Base64 message.
pub exec fn encode_6bits_url(src: i16) -> (r: u8)
    requires
        0 <= src <= 63,
    ensures
        r == b64_char_url(src as int),
{
    let diff0 = src + 0x41;
    let t0 = encode_diff_term(25, 6, src);
    let t1 = encode_diff_term(51, -75, src);
    let t2 = encode_diff_term(61, -13, src);
    let t3 = encode_diff_term(62, 49, src);
    proof {
        assert(25 - src >= -256 && 25 - src <= 255);
        assert(51 - src >= -256 && 51 - src <= 255);
        assert(61 - src >= -256 && 61 - src <= 255);
        assert(62 - src >= -256 && 62 - src <= 255);
    }
    let diff = diff0 + t0 + t1 + t2 + t3;
    diff as u8
}

/* ============================================================
 * Shared lemmas (the standalone proof fn sits at the file tail)
 * ============================================================ */

/// decode_6bits o encode_6bits == id (the 6-bit-layer roundtrip)
pub exec fn enc6_roundtrip_url(v: i16) -> (r: i16)
    requires
        0 <= v <= 63,
    ensures
        r == v,
{
    let c = encode_6bits_url(v);
    decode_6bits_url(c)
}

// ===========================================================================
// Proof lemma (placed at the file end; signature and contract untouched)
// ===========================================================================
/// digit(char(v)) == v (the alphabet inverse)
pub proof fn digit_char_inverse_url(v: int)
    requires
        0 <= v < 64,
    ensures
        b64_digit_url(b64_char_url(v)) == v,
{
    if v <= 25 {
    } else if v <= 51 {
    } else if v <= 61 {
    } else {
    }
}
} // verus!
