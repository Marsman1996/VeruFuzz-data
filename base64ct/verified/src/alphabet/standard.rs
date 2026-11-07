//! Standard Base64 alphabet mirror (Base64 / Base64Unpadded)
//!
//! Upstream: code/base64ct/src/alphabet/standard.rs (pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614)
//! The upstream tree is unmodified; this file is the verified-side copy.
//!
//! Transcription notes:
//! - The `Base64`/`Base64Unpadded` pair differs only in the `PADDED` const bit, so the semantics are
//!   carried by a `padded: bool` parameter (the encoding.rs caller unwraps it into the two top-level APIs).
//! - The DECODER/ENCODER const array loops are unrolled in place (step order kept); every step's formula
//!   is transcribed verbatim through the `*_term` semantic bridges of super (=alphabet).
//! - The upstream `type Unpadded = Base64Unpadded` associated type is a type-domain mapping, not transcribed.
//!
//! This file also defines the standard alphabet's complete spec semantic model (digit/char tables, the
//! 3-byte block codec models, the whole-string encode/decode models, the canonical criterion), consumed
//! by the encoding.rs drivers and harness assertions -- this is the single source of truth.

use vstd::prelude::*;

use super::decode_eq_term;
use super::decode_pack_std;
use super::decode_range_term;
use super::encode_diff_term;
use super::encode_pack_indices_std;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============================================================
 * Spec semantic model: the standard alphabet digit table
 * ============================================================ */

/// Origin: DECODER (standard.rs:40-46) -- the semantic table
/// `[A-Z]->0..26, [a-z]->26..52, [0-9]->52..62, '+'->62, '/'->63`; -1 = the invalid sentinel
pub open spec fn b64_digit_std(c: u8) -> int {
    if 0x41 <= c <= 0x5a {
        c as int - 0x41
    } else if 0x61 <= c <= 0x7a {
        c as int - 0x61 + 26
    } else if 0x30 <= c <= 0x39 {
        c as int - 0x30 + 52
    } else if c == 0x2b {
        62
    } else if c == 0x2f {
        63
    } else {
        -1
    }
}

/// Origin: ENCODER (standard.rs:49-54, BASE='A' + 4 Diff steps) -- the semantic table
/// `v in [0,64)` mapped to the alphabet character
pub open spec fn b64_char_std(v: int) -> u8 {
    if v <= 25 {
        (0x41 + v) as u8
    } else if v <= 51 {
        (0x61 + v - 26) as u8
    } else if v <= 61 {
        (0x30 + v - 52) as u8
    } else if v == 62 {
        0x2b
    } else {
        0x2f
    }
}

/// 3-byte block -> the 4-character 6-bit indices (standard big-endian packing)
/// Origin: alphabet.rs:77-89 `Alphabet::encode_3bytes`, the first half
pub open spec fn b64_enc_idx_std(s: Seq<u8>, o: int) -> int {
    if o == 0 {
        s[0] as int / 4
    } else if o == 1 {
        (s[0] as int % 4) * 16 + s[1] as int / 16
    } else if o == 2 {
        (s[1] as int % 16) * 4 + s[2] as int / 64
    } else {
        s[2] as int % 64
    }
}

/// 4 character digits -> 3 bytes (standard big-endian packing)
/// Origin: alphabet.rs:36-50 `Alphabet::decode_3bytes` -- the bit synthesis
pub open spec fn b64_dec_bytes_std(c0: int, c1: int, c2: int, c3: int) -> (int, int, int) {
    (c0 * 4 + c1 / 16, (c1 * 16 + c2 / 4) % 256, (c2 * 64 + c3) % 256)
}

/// Encoded-length model: `n` bytes -> the character count (the two `padded` cases
/// aligned with upstream encoding.rs:364-377 `encoded_len_inner`)
pub open spec fn b64_elen_model_std(n: int, padded: bool) -> nat {
    let full = n / 3;
    let tail = n % 3;
    let v = if padded {
        4 * ((n + 2) / 3)
    } else {
        4 * full + (if tail == 0 {
            0
        } else {
            tail + 1 // tail==1 -> 2 chars; tail==2 -> 3 chars
        })
    };
    if v >= 0 {
        v as nat
    } else {
        0nat
    }
}

/// Encode-position value model (with tail handling and the padded '=' completion) -- the position-level authority
/// Origin: encoding.rs:185-232 `Encoding::encode` -- the semantic model (pos form)
pub open spec fn b64_encode_pos_std(s: Seq<u8>, padded: bool, j: int) -> u8 {
    let n = s.len() as int;
    let full = n / 3;
    let f = 3 * full;
    if j < 4 * full {
        b64_char_std(b64_enc_idx_std(s.subrange(3 * (j / 4), 3 * (j / 4) + 3), j % 4))
    } else if n % 3 == 1 {
        if j == 4 * full {
            b64_char_std(s[f] as int / 4)
        } else if j == 4 * full + 1 {
            b64_char_std((s[f] as int % 4) * 16)
        } else {
            0x3D
        }
    } else if n % 3 == 2 {
        if j == 4 * full {
            b64_char_std(s[f] as int / 4)
        } else if j == 4 * full + 1 {
            b64_char_std((s[f] as int % 4) * 16 + s[f + 1] as int / 16)
        } else if j == 4 * full + 2 {
            b64_char_std((s[f + 1] as int % 16) * 4)
        } else {
            0x3D
        }
    } else {
        0x3D
    }
}

/// Whole-string encode model = the position-value model mounted over all positions
/// Origin: encoding.rs:185-232 `Encoding::encode` -- the semantic model (Seq form)
pub open spec fn b64_encode_model_std(s: Seq<u8>, padded: bool) -> (o: Seq<u8>) {
    Seq::new(
        b64_elen_model_std(s.len() as int, padded),
        |j: int| b64_encode_pos_std(s, padded, j),
    )
}

/// Decode-position value model -- the position-level authority (u%4 in {0,2,3} domain)
/// Origin: encoding.rs:64-102 `Encoding::decode` -- the semantic model (pos form)
pub open spec fn b64_decode_pos_std(ug: Seq<u8>, j: int) -> u8 {
    let n = ug.len() as int;
    let full = n / 4;
    let f = 4 * full;
    if 0 <= j && j < 3 * full {
        let b = j / 3;
        let bytes = b64_dec_bytes_std(
            b64_digit_std(ug[4 * b]),
            b64_digit_std(ug[4 * b + 1]),
            b64_digit_std(ug[4 * b + 2]),
            b64_digit_std(ug[4 * b + 3]),
        );
        let o3 = j - 3 * b;
        if o3 == 0 {
            bytes.0 as u8
        } else if o3 == 1 {
            bytes.1 as u8
        } else {
            bytes.2 as u8
        }
    } else if n % 4 == 2 {
        b64_dec_bytes_std(b64_digit_std(ug[f]), b64_digit_std(ug[f + 1]), 0, 0).0 as u8
    } else {
        // tail == 3: 2 bytes; the tail block is 'A'-padded (digit 0) for the bit synthesis
        if j == 3 * full {
            b64_dec_bytes_std(
                b64_digit_std(ug[f]),
                b64_digit_std(ug[f + 1]),
                0,
                0,
            ).0 as u8
        } else {
            b64_dec_bytes_std(
                b64_digit_std(ug[f]),
                b64_digit_std(ug[f + 1]),
                b64_digit_std(ug[f + 2]),
                0,
            ).1 as u8
        }
    }
}

/// Data-string (after removing the counted pads) decode model (Seq form)
/// Origin: encoding.rs:64-102 `Encoding::decode` -- the semantic model (u%4 in {0,2,3} domain)
pub open spec fn b64_decode_model_std(ug: Seq<u8>) -> (o: Seq<u8>) {
    let n = ug.len() as int;
    let dlen = 3 * (n / 4) + (3 * (n % 4)) / 4;
    Seq::new(
        if dlen >= 0 {
            dlen as nat
        } else {
            0nat
        },
        |j: int| b64_decode_pos_std(ug, j),
    )
}

/// Counts pads: only the last two bytes are counted (upstream encoding.rs:265-297 decode_padding)
pub open spec fn b64_pad_count_std(src: Seq<u8>) -> int {
    let n = src.len() as int;
    let p1: int = if n >= 1 && src[n - 1] == 0x3D {
        1
    } else {
        0
    };
    let p2: int = if n >= 2 && src[n - 2] == 0x3D {
        1
    } else {
        0
    };
    p1 + p2
}

/// Pad structure is legal: count != 1, or count == 1 with the lone '=' being exactly the last byte
pub open spec fn b64_pad_ok_std(src: Seq<u8>) -> bool {
    let n = src.len() as int;
    let count = b64_pad_count_std(src);
    (n % 4 == 0) && (count == 0 || count == 2 || (count == 1 && n >= 1 && src[n - 1] == 0x3D))
}

/// Pad data-bit err flag: the upstream encoding.rs:284-294 `[.., b0] if padding_len == 1`
/// branch semantics (set to 1 when count==1 and the last byte is not '=')
pub open spec fn b64_pad_err_std(src: Seq<u8>) -> int {
    let n = src.len() as int;
    let count = b64_pad_count_std(src);
    if count == 1 && n >= 1 && src[n - 1] != 0x3D {
        1
    } else {
        0
    }
}

/// Canonical criterion: the source string decodes as a whole and the tail block round-trips identically
/// Origin: encoding.rs:299-337 `validate_last_block` -- the semantics
/// (consumed via b64_tailblock_zip_ok_std/..._mismatch_at_std against validate_last_block_std's obligations)
pub open spec fn b64_canonical_std(src: Seq<u8>, padded: bool) -> bool {
    let n = src.len() as int;
    let u = if padded {
        n - b64_pad_count_std(src)
    } else {
        n
    };
    if n == 0 {
        true
    } else {
        let dec = b64_decode_model_std(src.subrange(0, u));
        b64_tailblock_zip_ok_std(src, dec, padded)
    }
}

/// Mismatch witness (parameterized position form: w is the witness position) -- the provable carrier of the driver-level negative side
pub open spec fn b64_tailblock_zip_mismatch_at_std(
    enc: Seq<u8>,
    dec: Seq<u8>,
    padded: bool,
    w: int,
) -> bool {
    let nd = dec.len() as int;
    let ne = enc.len() as int;
    let dbs = if nd == 0 {
        0
    } else {
        ((nd - 1) / 3) * 3
    };
    let ebs = if ne == 0 {
        0
    } else {
        ((ne - 1) / 4) * 4
    };
    0 <= w
        && w
            < b64_elen_model_std(dec.subrange(dbs, nd).len() as int, padded) as int
        && 0 <= w
        && w < ne - ebs
        && b64_encode_model_std(dec.subrange(dbs, nd), padded)[w] != enc[ebs + w]
}


/// validate_last_block mismatch existence (a provable negative-side form; trigger friendly)
/// Origin: encoding.rs:299-337 `validate_last_block` -- the spec simplification (negative side)
pub open spec fn b64_tailblock_zip_mismatch_exists_std(
    encoded: Seq<u8>,
    decoded: Seq<u8>,
    padded: bool,
) -> bool {
    let nd = decoded.len() as int;
    let ne = encoded.len() as int;
    let dbs = if nd == 0 {
        0
    } else {
        ((nd - 1) / 3) * 3
    };
    let ebs = if ne == 0 {
        0
    } else {
        ((ne - 1) / 4) * 4
    };
    exists|j: int|
        b64_tailblock_zip_mismatch_at_std(encoded, decoded, padded, j)
}

/// The tail decoded block re-encodes exactly equal to the tail encoded block iff there is no mismatch position
/// Origin: encoding.rs:299-337 `validate_last_block` -- the spec simplification (positive side)
pub open spec fn b64_tailblock_zip_ok_std(encoded: Seq<u8>, decoded: Seq<u8>, padded: bool) -> bool {
    !b64_tailblock_zip_mismatch_exists_std(encoded, decoded, padded)
}

/// The full semantic merge of standard-alphabet decode (the driver-level ensures reference it)
pub open spec fn b64_decodes_ok_std(src: Seq<u8>, padded: bool) -> bool {
    let n = src.len() as int;
    let u = if padded {
        n - b64_pad_count_std(src)
    } else {
        n
    };
    (if padded {
        b64_pad_ok_std(src)
    } else {
        true
    }) && (u % 4 != 1) && (forall|j: int| 0 <= j < u ==> b64_digit_std(src[j]) != -1)
        && b64_canonical_std(src, padded)
}

/// Decoded-byte-count model (upstream encoding.rs:344-352 `decoded_len`; u is the data length)
pub open spec fn b64_dec_len_model_std(u: int) -> int {
    3 * (u / 4) + (3 * (u % 4)) / 4
}

/* ============================================================
 * exec layer: verbatim transcription (step order kept, Origin comment numbering kept)
 * ============================================================ */

/// Origin: alphabet.rs:53-73 `Alphabet::decode_6bits` x the standard DECODER
/// Upstream doc (alphabet.rs:52-52):
///   Decode 6-bits of a Base64 message.
pub exec fn decode_6bits_std(src: u8) -> (ret: i16)
    ensures
        ret == b64_digit_std(src),
        ret == -1 || (0 <= ret <= 63),
{
    let mut ret: i16 = -1;
    /* Origin Rust: for step in Self::DECODER { ret += match step { ... } }
       -- the 5 DECODER steps unrolled in place, the step order matching one to one */
    /* Origin Rust: DecodeStep::Range(b'A'..=b'Z', -64) */
    let t0 = decode_range_term(0x41, 0x5a, -64, src);
    /* Origin Rust: DecodeStep::Range(b'a'..=b'z', -70) */
    let t1 = decode_range_term(0x61, 0x7a, -70, src);
    /* Origin Rust: DecodeStep::Range(b'0'..=b'9', 5) */
    let t2 = decode_range_term(0x30, 0x39, 5, src);
    /* Origin Rust: DecodeStep::Eq(b'+', 63) */
    let t3 = decode_eq_term(0x2b, 63, src);
    /* Origin Rust: DecodeStep::Eq(b'/', 64) */
    let t4 = decode_eq_term(0x2f, 64, src);
    proof {
        if 0x41 <= src <= 0x5a {
            assert(t0 == src as int - 64);
            assert(t1 == 0 && t2 == 0 && t3 == 0 && t4 == 0);
        } else if 0x61 <= src <= 0x7a {
            assert(t1 == src as int - 70);
            assert(t0 == 0 && t2 == 0 && t3 == 0 && t4 == 0);
        } else if 0x30 <= src <= 0x39 {
            assert(t2 == src as int + 5);
            assert(t0 == 0 && t1 == 0 && t3 == 0 && t4 == 0);
        } else if src == 0x2b {
            assert(t3 == 63);
            assert(t0 == 0 && t1 == 0 && t2 == 0 && t4 == 0);
        } else if src == 0x2f {
            assert(t4 == 64);
            assert(t0 == 0 && t1 == 0 && t2 == 0 && t3 == 0);
        } else {
            assert(t0 == 0 && t1 == 0 && t2 == 0 && t3 == 0 && t4 == 0);
        }
    }
    ret = ret + t0 + t1 + t2 + t3 + t4;
    ret
}

/// Origin: alphabet.rs:91-104 `Alphabet::encode_6bits` x the standard ENCODER
/// (BASE = b'A'; the 4 ENCODER steps are all Diff-type, depending only on src, so they add up directly)
/// Upstream doc (alphabet.rs:91-91):
///   Encode 6-bits of a Base64 message.
pub exec fn encode_6bits_std(src: i16) -> (r: u8)
    requires
        0 <= src <= 63,
    ensures
        r == b64_char_std(src as int),
{
    /* Origin Rust: let mut diff = src + Self::BASE as i16; */
    let diff0 = src + 0x41;
    /* Origin Rust: EncodeStep::Diff(25, 6) */
    let t0 = encode_diff_term(25, 6, src);
    /* Origin Rust: EncodeStep::Diff(51, -75) */
    let t1 = encode_diff_term(51, -75, src);
    /* Origin Rust: EncodeStep::Diff(61, -(b'+' as i16 - 0x1c)) = Diff(61, -15) */
    let t2 = encode_diff_term(61, -15, src);
    /* Origin Rust: EncodeStep::Diff(62, b'/' as i16 - b'+' as i16 - 1) = Diff(62, 3) */
    let t3 = encode_diff_term(62, 3, src);
    proof {
        assert(25 - src >= -256 && 25 - src <= 255);
        assert(51 - src >= -256 && 51 - src <= 255);
        assert(61 - src >= -256 && 61 - src <= 255);
        assert(62 - src >= -256 && 62 - src <= 255);
        if src <= 25 {
            assert(t0 == 0 && t1 == 0 && t2 == 0 && t3 == 0);
            assert(diff0 == src + 0x41);
        } else if src <= 51 {
            assert(t0 == 6);
            assert(t1 == 0 && t2 == 0 && t3 == 0);
            assert(diff0 + t0 == src + 0x41 + 6);
        } else if src <= 61 {
            assert(t0 == 6 && t1 == -75);
            assert(t2 == 0 && t3 == 0);
            assert(diff0 + t0 + t1 == src + 0x41 + 6 - 75);
        } else if src == 62 {
            assert(t0 == 6 && t1 == -75 && t2 == -15);
            assert(t3 == 0);
            assert(diff0 + t0 + t1 + t2 == 0x2b);
        } else {
            assert(t0 == 6 && t1 == -75 && t2 == -15 && t3 == 3);
            assert(diff0 + t0 + t1 + t2 + t3 == 0x2f);
        }
    }
    let diff = diff0 + t0 + t1 + t2 + t3;
    diff as u8
}

/// Origin: alphabet.rs:36-50 `Alphabet::decode_3bytes` (the standard table)
/// Upstream doc (alphabet.rs:34-34):
///   Decode 3 bytes of a Base64 message.
pub exec fn decode_3bytes_std(src: &[u8], dst: &mut [u8]) -> (e: i16)
    requires
        src.len() == 4,
        dst.len() >= 3,
    ensures
        (0 <= b64_digit_std(src@[0])
            && b64_digit_std(src@[0]) <= 63
            && 0 <= b64_digit_std(src@[1])
            && b64_digit_std(src@[1]) <= 63
            && 0 <= b64_digit_std(src@[2])
            && b64_digit_std(src@[2]) <= 63
            && 0 <= b64_digit_std(src@[3])
            && b64_digit_std(src@[3]) <= 63) ==> (
            e == 0
                && (final(dst)@[0] as int, final(dst)@[1] as int, final(dst)@[2] as int)
                    == b64_dec_bytes_std(
                        b64_digit_std(src@[0]),
                        b64_digit_std(src@[1]),
                        b64_digit_std(src@[2]),
                        b64_digit_std(src@[3]),
                    )
        ),
        b64_digit_std(src@[0]) == -1 || b64_digit_std(src@[1]) == -1 || b64_digit_std(src@[2]) == -1
            || b64_digit_std(src@[3]) == -1 ==> (e == 1),
{
    /* Origin Rust: let c0 = Self::decode_6bits(src[0]); ... (x4) */
    let c0 = decode_6bits_std(src[0]);
    let c1 = decode_6bits_std(src[1]);
    let c2 = decode_6bits_std(src[2]);
    let c3 = decode_6bits_std(src[3]);
    /* Origin Rust: dst[0] = ((c0 << 2) | (c1 >> 4)) as u8; ...
       -- the bit-synthesis body lives in decode_pack_std (closed at the bit level) */
    let (e2, d0, d1, d2) = decode_pack_std(c0, c1, c2, c3);
    dst[0] = d0;
    dst[1] = d1;
    dst[2] = d2;
    e2
}

/// Origin: alphabet.rs:77-89 `Alphabet::encode_3bytes` (the standard table)
/// Upstream doc (alphabet.rs:75-75):
///   Encode 3-bytes of a Base64 message.
pub exec fn encode_3bytes_std(src: &[u8], dst: &mut [u8])
    requires
        src.len() == 3,
        dst.len() >= 4,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|o: int| 0 <= o < 4 ==> final(dst)@[o]
            == b64_char_std(b64_enc_idx_std(src@.subrange(0, 3), o)),
        forall|j: int| (4 <= j < old(dst)@.len()) ==> final(dst)@[j] == old(dst)@[j],
{
    /* Origin Rust: let b0 = src[0] as i16; let b1 = src[1] as i16; let b2 = src[2] as i16;
       dst[0] = Self::encode_6bits(b0 >> 2); ...
       -- the 6-bit index-extraction body lives in encode_pack_indices_std (closed at the bit level) */
    let (i0, i1, i2, i3) = encode_pack_indices_std(src);
    proof {
        assert(i0 >= 0 && i0 <= 63);
        assert(i1 >= 0 && i1 <= 63);
        assert(i2 >= 0 && i2 <= 63);
        assert(i3 >= 0 && i3 <= 63);
    }
    dst[0] = encode_6bits_std(i0);
    dst[1] = encode_6bits_std(i1);
    dst[2] = encode_6bits_std(i2);
    dst[3] = encode_6bits_std(i3);
}

/// Origin: the fixed-point call form of encode_3bytes_std (for the driver index loop; the slice boilerplate is absorbed here)
pub exec fn encode_3bytes_std_at(src: &[u8], src_off: usize, dst: &mut [u8], dst_off: usize)
    requires
        src_off + 3 <= src.len(),
        dst_off + 4 <= dst.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|j: int| dst_off as int <= j < dst_off as int + 4 ==> #[trigger] final(dst)@[j]
            == b64_char_std(b64_enc_idx_std(src@.subrange(src_off as int, src_off as int + 3), j - dst_off as int)),
        forall|j: int| #![trigger final(dst)@[j]]
            ((0 <= j < old(dst)@.len()
                && (j < dst_off as int || j >= dst_off as int + 4)) ==> (final(dst)@[j]
            == old(dst)@[j])),
{
    encode_3bytes_std(&src[src_off..src_off + 3], &mut dst[dst_off..dst_off + 4]);
    proof {
        assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4).len() == 4);
        assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[0]
            == final(dst)@[dst_off as int]);
        assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[1]
            == final(dst)@[dst_off as int + 1]);
        assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[2]
            == final(dst)@[dst_off as int + 2]);
        assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[3]
            == final(dst)@[dst_off as int + 3]);
        assert forall|j: int| dst_off as int <= j < dst_off as int + 4 implies
            final(dst)@[j]
                == b64_char_std(b64_enc_idx_std(src@.subrange(src_off as int, src_off as int + 3), j - dst_off as int)) by {
            let o = j - dst_off as int;
            assert(0 <= o < 4);
            if o == 0 {
                assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[0]
                    == b64_char_std(b64_enc_idx_std(src@.subrange(src_off as int, src_off as int + 3), 0)));
            } else if o == 1 {
                assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[1]
                    == b64_char_std(b64_enc_idx_std(src@.subrange(src_off as int, src_off as int + 3), 1)));
            } else if o == 2 {
                assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[2]
                    == b64_char_std(b64_enc_idx_std(src@.subrange(src_off as int, src_off as int + 3), 2)));
            } else {
                assert(final(dst)@.subrange(dst_off as int, dst_off as int + 4)[3]
                    == b64_char_std(b64_enc_idx_std(src@.subrange(src_off as int, src_off as int + 3), 3)));
            }
        }
    }
}

/// Origin: the fixed-point call form of decode_3bytes_std (for the driver index loop)
pub exec fn decode_3bytes_std_at(src: &[u8], src_off: usize, dst: &mut [u8], dst_off: usize) -> (e: i16)
    requires
        src_off + 4 <= src.len(),
        dst_off + 3 <= dst.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|j: int| #![trigger final(dst)@[j]]
            ((0 <= j < old(dst)@.len()
                && (j < dst_off as int || j >= dst_off as int + 3)) ==> (final(dst)@[j]
            == old(dst)@[j])),
        (0 <= b64_digit_std(src@[src_off as int])
            && b64_digit_std(src@[src_off as int]) <= 63
            && 0 <= b64_digit_std(src@[src_off as int + 1])
            && b64_digit_std(src@[src_off as int + 1]) <= 63
            && 0 <= b64_digit_std(src@[src_off as int + 2])
            && b64_digit_std(src@[src_off as int + 2]) <= 63
            && 0 <= b64_digit_std(src@[src_off as int + 3])
            && b64_digit_std(src@[src_off as int + 3]) <= 63) ==> (
            e == 0
                && final(dst)@[dst_off as int] as int
                    == b64_dec_bytes_std(
                        b64_digit_std(src@[src_off as int]),
                        b64_digit_std(src@[src_off as int + 1]),
                        b64_digit_std(src@[src_off as int + 2]),
                        b64_digit_std(src@[src_off as int + 3]),
                    ).0
                && final(dst)@[dst_off as int + 1] as int
                    == b64_dec_bytes_std(
                        b64_digit_std(src@[src_off as int]),
                        b64_digit_std(src@[src_off as int + 1]),
                        b64_digit_std(src@[src_off as int + 2]),
                        b64_digit_std(src@[src_off as int + 3]),
                    ).1
                && final(dst)@[dst_off as int + 2] as int
                    == b64_dec_bytes_std(
                        b64_digit_std(src@[src_off as int]),
                        b64_digit_std(src@[src_off as int + 1]),
                        b64_digit_std(src@[src_off as int + 2]),
                        b64_digit_std(src@[src_off as int + 3]),
                    ).2
        ),
        b64_digit_std(src@[src_off as int]) == -1 || b64_digit_std(src@[src_off as int + 1]) == -1 || b64_digit_std(src@[src_off as int + 2]) == -1
            || b64_digit_std(src@[src_off as int + 3]) == -1 ==> (e == 1),
{
    decode_3bytes_std(&src[src_off..src_off + 4], &mut dst[dst_off..dst_off + 3])
}

/* ============================================================
 * Shared lemmas (the shape common to every alphabet; the single copy)
 * ============================================================ */

/// digit(char(v)) == v: the char table <-> digit table inverse (the inverse-side core of the roundtrip)
pub proof fn digit_char_inverse_std(v: int)
    requires
        0 <= v < 64,
    ensures
        b64_digit_std(b64_char_std(v)) == v,
{
    if v <= 25 {
    } else if v <= 51 {
    } else if v <= 61 {
    } else {
    }
}

/// The encoding output is all ASCII (the semantic precondition of the upstream `str::from_utf8_unchecked`)
pub proof fn char_ascii_std(v: int)
    requires
        0 <= v < 64,
    ensures
        b64_char_std(v) < 0x80,
    {
    }

// ===========================================================================
// Proof lemmas (placed at the file end so the spec/exec surface reads linearly;
// signatures and contracts untouched)
// ===========================================================================
/// Seq::new exit lemma: model[j] == pos(j). Verus adaptation: `Seq::new(n, f)[j]`
/// cannot unfold automatically (no trigger), so this lemma pins the exit with a proven
/// derivation pattern (len-assert + subrange triggers...).
pub proof fn lemma_enc_index(s: Seq<u8>, padded: bool, j: int)
    requires
        0 <= j < b64_elen_model_std(s.len() as int, padded) as int,
    ensures
        b64_encode_model_std(s, padded)[j] == b64_encode_pos_std(s, padded, j),
{
    let m = b64_encode_model_std(s, padded);
    let ml = b64_elen_model_std(s.len() as int, padded);
    assert(m.len() == ml);
    assert(0 <= j && j < ml as int);
    assert forall|q: int| 0 <= q < m.len() as int implies
        m[q] == b64_encode_pos_std(s, padded, q) by {
        assert(m.subrange(0, m.len() as int)[q] == m[q]);
    }
}

/// Seq::new exit lemma: decode model[j] == pos(j) (same derivation pattern as lemma_enc_index)
pub proof fn lemma_dec_index(ug: Seq<u8>, j: int)
    requires
        0 <= j < 3 * (ug.len() as int / 4) + (3 * (ug.len() as int % 4)) / 4,
    ensures
        b64_decode_model_std(ug)[j] == b64_decode_pos_std(ug, j),
{
    let m = b64_decode_model_std(ug);
    let n = ug.len() as int;
    let dlen = 3 * (n / 4) + (3 * (n % 4)) / 4;
    assert(m.len() as int == if dlen >= 0 {
        dlen
    } else {
        0
    });
    assert(0 <= j && j < m.len() as int);
    assert forall|q: int| 0 <= q < m.len() as int implies
        m[q] == b64_decode_pos_std(ug, q) by {
        assert(m.subrange(0, m.len() as int)[q] == m[q]);
    }
}

/// Tail block t==1: pos agrees with the tmp indices (the reuse lemma feeding the driver tail proofs)
pub proof fn lemma_enc_tail1_pos_chars(s: Seq<u8>, padded: bool, tmp: Seq<u8>, o: int)
    requires
        s.len() as int % 3 == 1,
        tmp.len() == 3,
        tmp[0] == s[(s.len() as int - 1) as int],
        tmp[1] == 0,
        tmp[2] == 0,
        0 <= o <= 1,
    ensures
        b64_encode_pos_std(s, padded, 4 * (s.len() as int / 3) + o)
            == b64_char_std(b64_enc_idx_std(tmp, o)),
{
    let n = s.len() as int;
    let f = 3 * (n / 3);
    assert(f == n - 1);
    assert(tmp[0] == s[f]);
}

/// Tail block t==2: pos agrees with the tmp indices (o in {0,1,2})
pub proof fn lemma_enc_tail2_pos_chars(s: Seq<u8>, padded: bool, tmp: Seq<u8>, o: int)
    requires
        s.len() as int % 3 == 2,
        tmp.len() == 3,
        tmp[0] == s[(s.len() as int - 2) as int],
        tmp[1] == s[(s.len() as int - 1) as int],
        tmp[2] == 0,
        0 <= o <= 2,
    ensures
        b64_encode_pos_std(s, padded, 4 * (s.len() as int / 3) + o)
            == b64_char_std(b64_enc_idx_std(tmp, o)),
{
    let n = s.len() as int;
    let f = 3 * (n / 3);
    assert(f == n - 2);
    assert(tmp[0] == s[f]);
    assert(tmp[1] == s[f + 1]);
}

/// mismatch_at(w) ==> a mismatch position exists: the explicit proof closure of the SMT counterexample side
pub proof fn lemma_mismatch_at_implies_exists(
    enc: Seq<u8>,
    dec: Seq<u8>,
    padded: bool,
    w: int,
)
    requires
        b64_tailblock_zip_mismatch_at_std(enc, dec, padded, w),
    ensures
        b64_tailblock_zip_mismatch_exists_std(enc, dec, padded),
{
}
} // verus!
