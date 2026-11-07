//! base64ct generic alphabet mechanism mirror
//!
//! Upstream: https://github.com/RustCrypto/formats (SUBDIR=base64ct)
//!   pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614 (see code/base64ct/src/alphabet.rs;
//!   the upstream counterpart is the `Alphabet` trait plus the `DecodeStep`/`EncodeStep` enums)
//!
//! The upstream tree is unmodified; all of the transcription below lands only in this verified copy.
//!
//! Mirror and transcription ledger (KVerus relax conventions; see out/bug-finder-summary.md):
//! 1. The `Alphabet` trait (const tables + the `Unpadded` associated type) is not turned into a Verus trait:
//!    all six alphabet instances are monomorphized into per-alphabet exec fns (see alphabet/standard.rs etc.);
//!    this file carries the whole shared mechanism, i.e. the per-step semantic bridges of the upstream
//!    `decode_6bits`/`encode_6bits` bit formulas (the `*_term` quartet) plus the two 3-byte packing cores.
//!    Every bit-level conclusion is closed in these six places.
//! 2. `for step in Self::DECODER/ENCODER` (compile-time const array loops) are unrolled in place into straight-line
//!    calls, the step order matching the upstream array element order one to one; each Origin comment keeps the numbering.
//! 3. `DecodeStep::Range(RangeInclusive<u8>, i16)` / `Eq(u8, i16)` /
//!    `EncodeStep::Apply(u8, i16)` / `Diff(u8, i16)` enums themselves are not transcribed: their byte
//!    effects are carried by the matching `*_term` with explicit parameters (lo/hi/value/threshold/offset).
//! 4. The `debug_assert`s inside fn bodies are debug-only assertions; release semantics are unchanged, not transcribed
//!    (their validity is carried by this file's requires).
//! 5. The upstream `Alphabet` supertrait bounds (Copy/Debug/Eq/Send/Sized/Sync) are type-domain
//!    constraints, outside the executable semantics surface, not transcribed.
//! 6. The default (standard big-endian packing) cores of `decode_3bytes`/`encode_3bytes` and the
//!    shacrypt override (crypt(3) packing) cores land in `decode_pack_std`/`encode_pack_indices_std`
//!    and `decode_pack_crypt`/`encode_pack_indices_crypt`, respectively.
//! 7. `is_pad_ct` (encoding.rs:354-360, the branchless '=' matcher) has exactly the same shape as `decode_eq_term(0x3D, 1, _)`;
//!    encoding.rs instantiates decode_eq_term directly.
//! 8. Bit-level proof-form note (a Verus quirk): in spec/proof mode i16 `+`/`-`/`*` promote to int
//!    while `&`/`|`/`<<`/`>>` keep the machine type, so every bit-level assertion takes the "exec let variables
//!    + self-contained implication" form (premises inline, machine-suffix constants); see each proof block.

pub mod bcrypt;
pub mod crypt;
pub mod pbkdf2;
pub mod shacrypt;
pub mod standard;
pub mod url;

use vstd::prelude::*;

verus! {

/* ============================================================
 * The semantic bridge of the constant-time steps (the upstream Sc00bz bit tricks, one step one proof)
 * ============================================================ */

/// Origin: alphabet.rs:53-73 `Alphabet::decode_6bits`, the `DecodeStep::Range` branch:
/// ```text
/// let start = *range.start() as i16 - 1;
/// let end   = *range.end() as i16 + 1;
/// (((start - src as i16) & (src as i16 - end)) >> 8) & (src as i16 + *offset)
/// ```
/// Semantics (this fn's ensures, provable at the bit level): src in [lo, hi] contributes `src + offset`,
/// otherwise it contributes 0.
/// Upstream doc (alphabet.rs:110-110):
///   Match the given range, offsetting the input on match.
pub exec fn decode_range_term(lo: u8, hi: u8, offset: i16, src: u8) -> (t: i16)
    requires
        lo <= hi,
        -(0x4000 as i16) <= offset,
        offset <= 0x4000 as i16,
    ensures
        lo <= src <= hi ==> (t == src as int + offset as int),
        src < lo || src > hi ==> (t == 0),
{
    /* Origin Rust: let start = *range.start() as i16 - 1; let end = *range.end() as i16 + 1; */
    let s = src as i16;
    let start = lo as i16 - 1;
    let end = hi as i16 + 1;
    let a = start - s;
    let b = s - end;
    let x = a & b;
    let m = x >> 8;
    let so = s + offset;
    proof {
        if lo <= src <= hi {
            // inside the range: a, b both in [-256,-1] -> high byte all ones -> mask 0xFFFF
            assert((a >= (-256i16)) && (a <= (-1i16)) && (b >= (-256i16)) && (b <= (-1i16)) && (x == (a & b)) && (m == (x >> 8))
                ==> (m == (-1i16))) by (bit_vector);
            assert(m == (-1i16));
            // mask all ones: AND with (s+offset) keeps the original value
            let mm = m & so;
            assert((m == (-1i16)) && (mm == (m & so)) ==> (mm == so)) by (bit_vector);
            assert((m & so) == so);
        } else if src < lo {
            // left of the range: a = start-s in [0,255] -> high byte 0 -> mask 0
            assert(a >= 0 && a <= 255);
            assert((a >= (0i16)) && (a <= (255i16)) && (x == (a & b)) && (m == (x >> 8))
                ==> (m == (0i16))) by (bit_vector);
            assert(m == (0i16));
            let mm = m & so;
            assert((m == (0i16)) && (mm == (m & so)) ==> (mm == (0i16))) by (bit_vector);
            assert((m & so) == 0);
        } else {
            // right of the range: b = s-end in [0,254] -> high byte 0 -> mask 0
            assert(b >= 0 && b <= 255);
            assert((b >= (0i16)) && (b <= (255i16)) && (x == (a & b)) && (m == (x >> 8))
                ==> (m == (0i16))) by (bit_vector);
            assert(m == (0i16));
            let mm = m & so;
            assert((m == (0i16)) && (mm == (m & so)) ==> (mm == (0i16))) by (bit_vector);
            assert((m & so) == 0);
        }
    }
    (m) & (so)
}

/// Origin: alphabet.rs:53-73 `Alphabet::decode_6bits`, the `DecodeStep::Eq` branch:
/// ```text
/// let start = *value as i16 - 1;
/// let end   = *value as i16 + 1;
/// (((start - src as i16) & (src as i16 - end)) >> 8) & *offset
/// ```
/// Semantics: src == v contributes `offset`, otherwise 0.
/// Upstream doc (alphabet.rs:113-113):
///   Match the given value, returning the associated offset on match.
pub exec fn decode_eq_term(v: u8, offset: i16, src: u8) -> (t: i16)
    requires
        -(0x4000 as i16) <= offset,
        offset <= 0x4000 as i16,
    ensures
        src == v ==> (t == offset as int),
        src != v ==> (t == 0),
{
    /* Origin Rust: let start = *value as i16 - 1; let end = *value as i16 + 1; */
    let s = src as i16;
    let start = v as i16 - 1;
    let end = v as i16 + 1;
    let a = start - s;
    let b = s - end;
    let x = a & b;
    let m = x >> 8;
    proof {
        if src < v {
            assert(a >= 0 && a <= 255);
            assert((a >= (0i16)) && (a <= (255i16)) && (x == (a & b)) && (m == (x >> 8))
                ==> (m == (0i16))) by (bit_vector);
            assert(m == (0i16));
            let mm = m & offset;
            assert((m == (0i16)) && (mm == (m & offset)) ==> (mm == (0i16))) by (bit_vector);
            assert((m & offset) == 0);
        } else if src > v {
            assert(b >= 0 && b <= 255);
            assert((b >= (0i16)) && (b <= (255i16)) && (x == (a & b)) && (m == (x >> 8))
                ==> (m == (0i16))) by (bit_vector);
            assert(m == (0i16));
            let mm = m & offset;
            assert((m == (0i16)) && (mm == (m & offset)) ==> (mm == (0i16))) by (bit_vector);
            assert((m & offset) == 0);
        } else {
            assert(a >= -256 && a <= -1);
            assert(b >= -256 && b <= -1);
            assert((a >= (-256i16)) && (a <= (-1i16)) && (b >= (-256i16)) && (b <= (-1i16)) && (x == (a & b)) && (m == (x >> 8))
                ==> (m == (-1i16))) by (bit_vector);
            assert(m == (-1i16));
            let mm = m & offset;
            assert((m == (-1i16)) && (mm == (m & offset)) ==> (mm == offset)) by (bit_vector);
            assert((m & offset) == offset);
        }
    }
    (m) & (offset)
}

/// Origin: alphabet.rs:91-104 `Alphabet::encode_6bits`, the `EncodeStep::Apply` branch:
/// `diff += ((threshold as i16 - diff) >> 8) & offset`
/// Semantics: when threshold is strictly below the current accumulated diff, add offset, otherwise add 0.
/// The upstream accumulated diff always stays near table values (every alphabet is < 300), so requires
/// gives the window [-256, 255] where the bit trick holds (outside it the polluted high bits break the test).
/// Upstream doc (alphabet.rs:120-120):
///   Apply the given offset to the cumulative result on match.
pub exec fn encode_apply_term(threshold: u8, offset: i16, diff: i16) -> (t: i16)
    requires
        -(0x4000 as i16) <= offset,
        offset <= 0x4000 as i16,
        -256 <= threshold as i16 - diff,
        threshold as i16 - diff <= 255,
    ensures
        diff > threshold as i16 ==> (t == offset as int),
        diff <= threshold as i16 ==> (t == 0),
{
    let th = threshold as i16;
    let y = th - diff;
    let m = y >> 8;
    proof {
        if diff > th {
            assert(y >= -256 && y <= -1);
            assert((y >= (-256i16)) && (y <= (-1i16)) && (m == (y >> 8))
                ==> (m == (-1i16))) by (bit_vector);
            assert(m == (-1i16));
            let mm = m & offset;
            assert((m == (-1i16)) && (mm == (m & offset)) ==> (mm == offset)) by (bit_vector);
            assert((m & offset) == offset);
        } else {
            assert(y >= 0 && y <= 255);
            assert((y >= (0i16)) && (y <= (255i16)) && (m == (y >> 8))
                ==> (m == (0i16))) by (bit_vector);
            assert(m == (0i16));
            let mm = m & offset;
            assert((m == (0i16)) && (mm == (m & offset)) ==> (mm == (0i16))) by (bit_vector);
            assert((m & offset) == 0);
        }
    }
    (m) & (offset)
}

/// Origin: alphabet.rs:91-104 `Alphabet::encode_6bits`, the `EncodeStep::Diff` branch:
/// `diff += ((threshold as i16 - src) >> 8) & offset`
/// Semantics: when threshold is strictly below the 6-bit value src, add offset, otherwise add 0.
/// Upstream doc (alphabet.rs:123-123):
///   Compute a difference using the given offset on match.
pub exec fn encode_diff_term(threshold: u8, offset: i16, src: i16) -> (t: i16)
    requires
        -(0x4000 as i16) <= offset,
        offset <= 0x4000 as i16,
        -256 <= threshold as i16 - src,
        threshold as i16 - src <= 255,
    ensures
        src > threshold as i16 ==> (t == offset as int),
        src <= threshold as i16 ==> (t == 0),
{
    let th = threshold as i16;
    let y = th - src;
    let m = y >> 8;
    proof {
        if src > th {
            assert(y >= -256 && y <= -1);
            assert((y >= (-256i16)) && (y <= (-1i16)) && (m == (y >> 8))
                ==> (m == (-1i16))) by (bit_vector);
            assert(m == (-1i16));
            let mm = m & offset;
            assert((m == (-1i16)) && (mm == (m & offset)) ==> (mm == offset)) by (bit_vector);
            assert((m & offset) == offset);
        } else {
            assert(y >= 0 && y <= 255);
            assert((y >= (0i16)) && (y <= (255i16)) && (m == (y >> 8))
                ==> (m == (0i16))) by (bit_vector);
            assert(m == (0i16));
            let mm = m & offset;
            assert((m == (0i16)) && (mm == (m & offset)) ==> (mm == (0i16))) by (bit_vector);
            assert((m & offset) == 0);
        }
    }
    (m) & (offset)
}

/* ============================================================
 * 3-byte <-> 4-character packing cores (two packing families, closed at the bit level)
 * ============================================================ */

/// Origin: alphabet.rs:36-50 `Alphabet::decode_3bytes`, the bit-synthesis tail
/// (the standard big-endian packing core of the standard/url/bcrypt/pbkdf2/crypt family):
/// ```text
/// dst[0] = ((c0 << 2) | (c1 >> 4)) as u8;
/// dst[1] = ((c1 << 4) | (c2 >> 2)) as u8;
/// dst[2] = ((c2 << 6) | c3) as u8;
/// ((c0 | c1 | c2 | c3) >> 8) & 1
/// ```
/// c0..c3 are the decode_6bits outputs: values {-1} (the invalid sentinel) + [0,63].
/// Upstream doc (alphabet.rs:34-34):
///   Decode 3 bytes of a Base64 message.
pub exec fn decode_pack_std(c0: i16, c1: i16, c2: i16, c3: i16) -> (r: (i16, u8, u8, u8))
    requires
        -1 <= c0 <= 63,
        -1 <= c1 <= 63,
        -1 <= c2 <= 63,
        -1 <= c3 <= 63,
    ensures
        c0 >= 0 && c1 >= 0 && c2 >= 0 && c3 >= 0 ==> (
            r.0 == 0
                && r.1 as int == c0 as int * 4 + c1 as int / 16
                && r.2 as int == ((c1 as int) * 16 + c2 as int / 4) % 256
                && r.3 as int == ((c2 as int) * 64 + c3 as int) % 256
        ),
        c0 == -1 || c1 == -1 || c2 == -1 || c3 == -1 ==> (r.0 == 1),
{
    /* Origin Rust: dst[0] = ((c0 << 2) | (c1 >> 4)) as u8; etc. (the bit synthesis mapped verbatim) */
    let e0 = ((c0 << 2) | (c1 >> 4));
    let e1 = ((c1 << 4) | (c2 >> 2));
    let e2 = ((c2 << 6) | c3);
    let orv = (c0 | c1) | (c2 | c3);
    let f = ((orv >> 8) & 1);
    #[verifier::truncate]
    let d0 = e0 as u8;
    #[verifier::truncate]
    let d1 = e1 as u8;
    #[verifier::truncate]
    let d2 = e2 as u8;
    proof {
        if c0 >= 0 && c1 >= 0 && c2 >= 0 && c3 >= 0 {
            assert(((c0 >= (0i16)) && (c0 <= (63i16)) && (c1 >= (0i16)) && (c1 <= (63i16)) && (c2 >= (0i16)) && (c2 <= (63i16)) && (c3 >= (0i16)) && (c3 <= (63i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> (8i16)) & (1i16))))
                ==> (f == (0i16))) by (bit_vector);
            assert(f == 0);
            assert((c0 >= (0i16)) && (c0 <= (63i16)) && (c1 >= (0i16)) && (c1 <= (63i16)) && (e0 == (((c0 << (2i16))) | ((c1 >> (4i16)))))
                ==> (e0 == ((c0 * (4i16)) + (c1 / (16i16))))) by (bit_vector);
            assert((c1 >= (0i16)) && (c1 <= (63i16)) && (c2 >= (0i16)) && (c2 <= (63i16)) && (e1 == (((c1 << (4i16))) | ((c2 >> (2i16)))))
                ==> (e1 == ((c1 * (16i16)) + (c2 / (4i16))))) by (bit_vector);
            assert((c2 >= (0i16)) && (c2 <= (63i16)) && (c3 >= (0i16)) && (c3 <= (63i16)) && (e2 == (((c2 << (6i16))) | (c3)))
                ==> (e2 == ((c2 * (64i16)) + (c3)))) by (bit_vector);
            // high-bit truncation `as u8` <-> mod 256 (e1 can reach 1008, e2 can reach 4095)
            assert((d0 == (e0 as u8)) && (e0 == ((c0 * (4i16)) + (c1 / (16i16)))) && (c0 >= (0i16)) && (c0 <= (63i16)) && (c1 >= (0i16)) && (c1 <= (63i16))
                ==> (d0 == (e0 % (256i16)))) by (bit_vector);
            assert((d1 == (e1 as u8)) && (e1 == ((c1 * (16i16)) + (c2 / (4i16)))) && (c1 >= (0i16)) && (c1 <= (63i16)) && (c2 >= (0i16)) && (c2 <= (63i16))
                ==> (d1 == (e1 % (256i16)))) by (bit_vector);
            assert((d2 == (e2 as u8)) && (e2 == ((c2 * (64i16)) + (c3))) && (c2 >= (0i16)) && (c2 <= (63i16)) && (c3 >= (0i16)) && (c3 <= (63i16))
                ==> (d2 == (e2 % (256i16)))) by (bit_vector);
            assert(c0 * 4 + c1 / 16 >= 0 && c0 * 4 + c1 / 16 <= 252 + 3);
            assert(c1 * 16 + c2 / 4 >= 0 && c1 * 16 + c2 / 4 <= 1008 + 15);
            assert(c2 * 64 + c3 >= 0 && c2 * 64 + c3 <= 4032 + 63);
        } else {
            // a -1 is present: -1 (an all-ones bit pattern) OR anything stays -1 -> error bit = 1
            if c0 == -1 {
                assert((c0 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            } else if c1 == -1 {
                assert((c1 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            } else if c2 == -1 {
                assert((c2 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            } else {
                assert((c3 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            }
        }
    }
    (f, d0, d1, d2)
}

/// Origin: alphabet.rs:77-89 `Alphabet::encode_3bytes`, the 6-bit index extraction
/// (the standard big-endian packing core):
/// ```text
/// dst[0] = Self::encode_6bits(b0 >> 2);
/// dst[1] = Self::encode_6bits(((b0 << 4) | (b1 >> 4)) & 63);
/// dst[2] = Self::encode_6bits(((b1 << 2) | (b2 >> 6)) & 63);
/// dst[3] = Self::encode_6bits(b2 & 63);
/// ```
/// The output goes up to the index layer; character generation is done by each alphabet's encode_6bits.
/// Upstream doc (alphabet.rs:75-75):
///   Encode 3-bytes of a Base64 message.
pub exec fn encode_pack_indices_std(src: &[u8]) -> (r: (i16, i16, i16, i16))
    requires
        src.len() == 3,
    ensures
        r.0 as int == src@[0] as int / 4,
        r.1 as int == (src@[0] as int % 4) * 16 + src@[1] as int / 16,
        r.2 as int == (src@[1] as int % 16) * 4 + src@[2] as int / 64,
        r.3 as int == src@[2] as int % 64,
{
    /* Origin Rust: let b0 = src[0] as i16; let b1 = src[1] as i16; let b2 = src[2] as i16; */
    let b0 = src[0] as i16;
    let b1 = src[1] as i16;
    let b2 = src[2] as i16;
    let i0 = b0 >> 2;
    let i1 = ((b0 << 4) | (b1 >> 4)) & 63;
    let i2 = ((b1 << 2) | (b2 >> 6)) & 63;
    let i3 = b2 & 63;
    proof {
        assert((b0 >= (0i16)) && (b0 <= (255i16)) && (i0 == (b0 >> (2i16)))
            ==> (i0 == (b0 / (4i16)))) by (bit_vector);
        assert((b0 >= (0i16)) && (b0 <= (255i16)) && (b1 >= (0i16)) && (b1 <= (255i16)) && (i1 == ((((b0 << (4i16))) | ((b1 >> (4i16)))) & (63i16)))
            ==> (i1 == (((b0 % (4i16)) * (16i16)) + (b1 / (16i16))))) by (bit_vector);
        assert((b1 >= (0i16)) && (b1 <= (255i16)) && (b2 >= (0i16)) && (b2 <= (255i16)) && (i2 == ((((b1 << (2i16))) | ((b2 >> (6i16)))) & (63i16)))
            ==> (i2 == (((b1 % (16i16)) * (4i16)) + (b2 / (64i16))))) by (bit_vector);
        assert((b2 >= (0i16)) && (b2 <= (255i16)) && (i3 == (b2 & (63i16)))
            ==> (i3 == (b2 % (64i16)))) by (bit_vector);
        assert(i0 >= 0 && i0 <= 63);
        assert(i1 >= 0 && i1 <= 63);
        assert(i2 >= 0 && i2 <= 63);
        assert(i3 >= 0 && i3 <= 63);
    }
    (i0, i1, i2, i3)
}

/// Origin: alphabet/shacrypt.rs:47-63 `Base64ShaCrypt::decode_3bytes` override
/// (crypt(3) packing; under this packing none of the three bytes needs >255 truncation):
/// ```text
/// dst[0] = (c0 | ((c1 & 0x3) << 6)) as u8;
/// dst[1] = ((c1 >> 2) | ((c2 & 0xF) << 4)) as u8;
/// dst[2] = ((c2 >> 4) | (c3 << 2)) as u8;
/// ```
pub exec fn decode_pack_crypt(c0: i16, c1: i16, c2: i16, c3: i16) -> (r: (i16, u8, u8, u8))
    requires
        -1 <= c0 <= 63,
        -1 <= c1 <= 63,
        -1 <= c2 <= 63,
        -1 <= c3 <= 63,
    ensures
        c0 >= 0 && c1 >= 0 && c2 >= 0 && c3 >= 0 ==> (
            r.0 == 0
                && r.1 as int == c0 as int + (c1 as int % 4) * 64
                && r.2 as int == c1 as int / 4 + (c2 as int % 16) * 16
                && r.3 as int == c2 as int / 16 + c3 as int * 4
        ),
        c0 == -1 || c1 == -1 || c2 == -1 || c3 == -1 ==> (r.0 == 1),
{
    let e0 = (c0 | ((c1 & 0x3) << 6));
    let e1 = ((c1 >> 2) | ((c2 & 0xF) << 4));
    let e2 = ((c2 >> 4) | (c3 << 2));
    let orv = (c0 | c1) | (c2 | c3);
    let f = ((orv >> 8) & 1);
    #[verifier::truncate]
    let d0 = e0 as u8;
    #[verifier::truncate]
    let d1 = e1 as u8;
    #[verifier::truncate]
    let d2 = e2 as u8;
    proof {
        if c0 >= 0 && c1 >= 0 && c2 >= 0 && c3 >= 0 {
            assert(((c0 >= (0i16)) && (c0 <= (63i16)) && (c1 >= (0i16)) && (c1 <= (63i16)) && (c2 >= (0i16)) && (c2 <= (63i16)) && (c3 >= (0i16)) && (c3 <= (63i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> (8i16)) & (1i16))))
                ==> (f == (0i16))) by (bit_vector);
            assert(f == 0);
            assert(((c0 >= (0i16)) && (c0 <= (63i16)) && (c1 >= (0i16)) && (c1 <= (63i16)) && (e0 == (c0 | ((c1 & (3i16)) << (6i16)))))
                ==> ((e0 == (c0 + ((c1 % (4i16)) * (64i16)))))) by (bit_vector);
            assert(((c1 >= (0i16)) && (c1 <= (63i16)) && (c2 >= (0i16)) && (c2 <= (63i16)) && (e1 == ((c1 >> (2i16)) | ((c2 & (15i16)) << (4i16)))))
                ==> ((e1 == ((c1 / (4i16)) + ((c2 % (16i16)) * (16i16)))))) by (bit_vector);
            assert((c2 >= (0i16)) && (c2 <= (63i16)) && (c3 >= (0i16)) && (c3 <= (63i16)) && (e2 == ((c2 >> (4i16)) | (c3 << (2i16))))
                ==> (e2 == ((c2 / (16i16)) + (c3 * (4i16))))) by (bit_vector);
            assert(c0 + (c1 % 4) * 64 >= 0 && c0 + (c1 % 4) * 64 <= 63 + 192);
            assert(c1 / 4 + (c2 % 16) * 16 >= 0 && c1 / 4 + (c2 % 16) * 16 <= 15 + 240);
            assert(c2 / 16 + c3 * 4 >= 0 && c2 / 16 + c3 * 4 <= 3 + 252);
        } else {
            if c0 == -1 {
                assert((c0 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            } else if c1 == -1 {
                assert((c1 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            } else if c2 == -1 {
                assert((c2 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            } else {
                assert((c3 == (-1i16)) && (orv == ((c0 | c1) | (c2 | c3))) && (f == ((orv >> 8) & (1i16)))
                    ==> (f == (1i16))) by (bit_vector);
            }
        }
    }
    (f, d0, d1, d2)
}

/// Origin: alphabet/shacrypt.rs:66-81 `Base64ShaCrypt::encode_3bytes` override:
/// ```text
/// dst[0] = Self::encode_6bits(b0 & 63);
/// dst[1] = Self::encode_6bits(((b1 << 2) | (b0 >> 6)) & 63);
/// dst[2] = Self::encode_6bits(((b2 << 4) | (b1 >> 4)) & 63);
/// dst[3] = Self::encode_6bits(b2 >> 2);
/// ```
pub exec fn encode_pack_indices_crypt(src: &[u8]) -> (r: (i16, i16, i16, i16))
    requires
        src.len() == 3,
    ensures
        r.0 as int == src@[0] as int % 64,
        r.1 as int == (src@[1] as int % 16) * 4 + src@[0] as int / 64,
        r.2 as int == (src@[2] as int % 4) * 16 + src@[1] as int / 16,
        r.3 as int == src@[2] as int / 4,
{
    let b0 = src[0] as i16;
    let b1 = src[1] as i16;
    let b2 = src[2] as i16;
    let i0 = b0 & 63;
    let i1 = ((b1 << 2) | (b0 >> 6)) & 63;
    let i2 = ((b2 << 4) | (b1 >> 4)) & 63;
    let i3 = b2 >> 2;
    proof {
        assert((b0 >= (0i16)) && (b0 <= (255i16)) && (i0 == (b0 & (63i16)))
            ==> (i0 == (b0 % (64i16)))) by (bit_vector);
        assert((b0 >= (0i16)) && (b0 <= (255i16)) && (b1 >= (0i16)) && (b1 <= (255i16)) && (i1 == ((((b1 << (2i16))) | ((b0 >> (6i16)))) & (63i16)))
            ==> (i1 == (((b1 % (16i16)) * (4i16)) + (b0 / (64i16))))) by (bit_vector);
        assert((b1 >= (0i16)) && (b1 <= (255i16)) && (b2 >= (0i16)) && (b2 <= (255i16)) && (i2 == ((((b2 << (4i16))) | ((b1 >> (4i16)))) & (63i16)))
            ==> (i2 == (((b2 % (4i16)) * (16i16)) + (b1 / (16i16))))) by (bit_vector);
        assert((b2 >= (0i16)) && (b2 <= (255i16)) && (i3 == (b2 >> (2i16)))
            ==> (i3 == (b2 / (4i16)))) by (bit_vector);
        assert(i0 >= 0 && i0 <= 63);
        assert(i1 >= 0 && i1 <= 63);
        assert(i2 >= 0 && i2 <= 63);
        assert(i3 >= 0 && i3 <= 63);
    }
    (i0, i1, i2, i3)
}

} // verus!
