//! Upstream code/base64ct/src/alphabet/bcrypt.rs mirror
//!
//! Upstream pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614; the code/ tree is unmodified.
//! Transcription notes (the same ledger conventions as standard.rs):
//! - The DECODER/ENCODER const array loops are unrolled in place (step order kept); the bit formulas go
//!   through the `*_term` semantic bridges of super.
//! - bcrypt table: '.'=0, '/'=1, A..Z=2..27, a..z=28..53, '0'..'9'=54..63;
//!   the 3 ENCODER Apply steps are cumulative-diff typed, accumulated serially in the upstream execution order.
//! - Apply('/'=47,17), Apply('Z'=90,6), Apply('z'=122,-75) accumulated serially.
//! - Covered surface: the bit-level (6-bit table) layer; the table-level encode/decode drivers and the
//!   fixed-vector roundtrips (the impl_tests macro of tests/bcrypt.rs) are isomorphic to the proven std
//!   driver but not transcribed here (the SMT cost multiplies).

use vstd::prelude::*;

use super::decode_range_term;
use super::encode_apply_term;

verus! {

/* ============================================================
 * spec semantic tables
 * ============================================================ */

/// Origin: bcrypt.rs DECODER -- the semantic table ('.'=0, '/'=1, A=2..27, a=28..53, '0'..'9'=54..63)
pub open spec fn b64_digit_bcrypt(c: u8) -> int {
    if c == 0x2e {
        0
    } else if c == 0x2f {
        1
    } else if 0x41 <= c <= 0x5a {
        c as int - 0x41 + 2
    } else if 0x61 <= c <= 0x7a {
        c as int - 0x61 + 28
    } else if 0x30 <= c <= 0x39 {
        c as int - 0x30 + 54
    } else {
        -1
    }
}

/// Origin: bcrypt.rs ENCODER -- the semantic table
pub open spec fn b64_char_bcrypt(v: int) -> u8 {
    if v <= 1 {
        (0x2e + v) as u8
    } else if v <= 27 {
        (0x41 + v - 2) as u8
    } else if v <= 53 {
        (0x61 + v - 28) as u8
    } else {
        (0x30 + v - 54) as u8
    }
}

/* ============================================================
 * exec table look-up (verbatim transcription, step order kept)
 * ============================================================ */

/// Origin: bcrypt.rs DECODER (the 4 Range steps unrolled in place; BASE='.')
/// Upstream doc (alphabet.rs:52-52):
///   Decode 6-bits of a Base64 message.
pub exec fn decode_6bits_bcrypt(src: u8) -> (ret: i16)
    ensures
        ret == b64_digit_bcrypt(src),
        ret == -1 || (0 <= ret <= 63),
{
    let mut ret: i16 = -1;
    let t0 = decode_range_term(0x2e, 0x2f, -45, src);
    let t1 = decode_range_term(0x41, 0x5a, -62, src);
    let t2 = decode_range_term(0x61, 0x7a, -68, src);
    let t3 = decode_range_term(0x30, 0x39, 7, src);
    proof {
        if src == 0x2e {
            assert(t0 == src as int - 45);
        } else if src == 0x2f {
            assert(t0 == src as int - 45);
        } else if 0x41 <= src <= 0x5a {
            assert(t1 == src as int - 62);
        } else if 0x61 <= src <= 0x7a {
            assert(t2 == src as int - 68);
        } else if 0x30 <= src <= 0x39 {
            assert(t3 == src as int + 7);
        }
    }
    ret = ret + t0 + t1 + t2 + t3;
    ret
}

/// Origin: bcrypt.rs ENCODER -- Apply('/'=47,17), Apply('Z'=90,6),
/// Apply('z'=122,-75) accumulated serially in the upstream execution order (cumulative-diff typed)
/// Upstream doc (alphabet.rs:91-91):
///   Encode 6-bits of a Base64 message.
pub exec fn encode_6bits_bcrypt(src: i16) -> (r: u8)
    requires
        0 <= src <= 63,
    ensures
        r == b64_char_bcrypt(src as int),
{
    let mut diff: i16 = src + 0x2e;
    proof {
        assert(diff >= 0 && diff <= 0x2e + 63);
        assert(47 - diff >= -256 && 47 - diff <= 255);
    }
    let u1 = encode_apply_term(47, 17, diff);
    diff = diff + u1;
    proof {
        assert(diff >= 0 && diff <= 200);
        assert(90 - diff >= -256 && 90 - diff <= 255);
    }
    let u2 = encode_apply_term(90, 6, diff);
    diff = diff + u2;
    proof {
        assert(diff >= 0 && diff <= 260);
        assert(122 - diff >= -256 && 122 - diff <= 255);
    }
    let u3 = encode_apply_term(122, -75, diff);
    diff = diff + u3;
    diff as u8
}

/* ============================================================
 * Shared lemmas (the standalone proof fn sits at the file tail)
 * ============================================================ */

/// decode_6bits o encode_6bits == id (the 6-bit-layer roundtrip)
pub exec fn enc6_roundtrip_bcrypt(v: i16) -> (r: i16)
    requires
        0 <= v <= 63,
    ensures
        r == v,
{
    let c = encode_6bits_bcrypt(v);
    decode_6bits_bcrypt(c)
}

// ===========================================================================
// Proof lemma (placed at the file end; signature and contract untouched)
// ===========================================================================
/// digit(char(v)) == v (the bcrypt alphabet inverse)
pub proof fn digit_char_inverse_bcrypt(v: int)
    requires
        0 <= v < 64,
    ensures
        b64_digit_bcrypt(b64_char_bcrypt(v)) == v,
{
    if v <= 1 {
    } else if v <= 27 {
    } else if v <= 53 {
    } else {
    }
}
} // verus!
