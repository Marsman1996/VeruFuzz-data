//! `engine/general_purpose/decode.rs` mirror -- aggregation of the verified items
//!   (the full GeneralPurposeEstimate::new contract / the full complete_quads_len contract /
//!   decode_chunk_4 / decode_chunk_8 and the two-layer decode_complete_quads +
//!   decode_helper integration, with the decode_span8/decode_span32/decode_span4
//!   step bridges and the dec_quad_byte region model).
//!
//! Relaxation (lib.rs ledger): `decode_table: &[u8; 256]` -> `&[u8]` + the model constraint
//! `ValidDecodeTable` (every morsel look-up is semantically equivalent).

use vstd::prelude::*;
use super::super::super::decode::{DecodeError, DecodeSliceError};
use super::super::DecodePaddingMode;
use super::decode_suffix::{decode_suffix, DecodeMetadata};
use super::super::naive::{
    naive_first_invalid, nfi_alllegal, nfi_bounds, nfi_hit, nfi_pin, nfi_skip, nfi_split_at,
    nfi_unfold, nfi_window_end,
};

verus! {

pub const INVALID_VALUE: u8 = 255;

/// Decode-table model: c is a legal symbol <=> the table value < 64 (illegal = INVALID_VALUE=255)
pub open spec fn is_invalid_morsel(v: u8) -> bool {
    v == INVALID_VALUE
}

/// Valid decode-table relation (the common invariant of STANDARD or any table derived from
/// an Alphabet): table values in {0..63, INVALID_VALUE}; legal positions hold values < 64
pub open spec fn ValidDecodeTable(t: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < t.len() ==> (t[j] < 64 || t[j] == INVALID_VALUE)
}

/* ============================================================
 * Origin: decode.rs:15-28 GeneralPurposeEstimate (pub struct + impl)
 * doc (of the DecodeEstimate trait): "must be no larger than the next largest
 * complete triple of decoded bytes"
 * ============================================================ */

/// Origin Rust: `estimate = (encoded_len / 4 + usize::from(rem > 0)) * 3`
/// Machine-level split: returns (rem, conservative_decoded_len)
pub exec fn estimate_decoded_len(encoded_len: usize) -> (r: (usize, usize))
    ensures
        r.0@ == encoded_len as int % 4, /* estimate.rem */
        r.0 <= 3,
        r.1@ == (encoded_len as int / 4 + if encoded_len as int % 4 > 0 { 1int } else { 0int }) * 3,
        r.1 <= usize::MAX / 4 * 3 + 3, /* conservative_decoded_len never overflows (padded <= MAX/4+1) */
{
    /* Origin Rust: let rem = encoded_len % 4; */
    let rem = encoded_len % 4;
    assert(rem@ == encoded_len as int % 4);
    let padded = encoded_len / 4 + if rem > 0 { 1usize } else { 0usize };
    assert(padded@ == encoded_len as int / 4 + if encoded_len as int % 4 > 0 { 1int } else { 0int });
    /* Origin Rust: conservative_decoded_len: (encoded_len / 4 + usize::from(rem > 0)) * 3
       -- no overflow: padded <= MAX/4 + 1, padded*3 <= MAX */
    assert(encoded_len as int / 4 <= usize::MAX as int / 4);
    assert(padded@ <= usize::MAX as int / 4 + 1);
    let conservative = padded * 3;
    assert(conservative@ == padded@ * 3);
    assert(padded@ * 3 <= (usize::MAX as int / 4 + 1) * 3);
    assert((usize::MAX as int / 4 + 1) * 3 <= usize::MAX as int);
    (rem, conservative)
}

/* ============================================================
 * Origin: decode.rs:184-217 `complete_quads_len`
 * ============================================================ */

/// The nonterminal-length model (the saturating semantics expanded precisely)
pub open spec fn nonterminal_quads_len_model(input_len: int, input_len_rem: int) -> int {
    let base = if input_len - input_len_rem < 0 { 0 } else { input_len - input_len_rem };
    if input_len_rem == 0 {
        if base - 4 < 0 { 0 } else { base - 4 }
    } else {
        base
    }
}

/// Upstream doc (decode.rs:176-183):
///   Returns the length of complete quads, except for the last one, even if it is complete.
///   Returns an error if the output len is not big enough for decoding those complete quads, or if
///   the input % 4 == 1, and that last byte is an invalid value other than a pad byte.
///   - `input` is the base64 input
///   - `input_len_rem` is input len % 4
///   - `output_len` is the length of the output slice
pub exec fn complete_quads_len(
    input: &[u8],
    input_len_rem: usize,
    output_len: usize,
    decode_table: &[u8],
    padding: u8,
) -> (r: Result<usize, DecodeSliceError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        input@.len() as int % 4 == input_len_rem as int, /* the debug_assert precondition */
    ensures
        /* convenience check: rem==1 and the trailing byte illegal and not padding -> InvalidByte(len-1, last) */
        input_len_rem == 1
            && input@.len() == 1
            && input@[0] != padding
            && is_invalid_morsel(decode_table@[(input@[0]) as int]) ==> r
            == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(0, input@[0]))),
        /* output too small -> OutputSliceTooSmall */
        r.is_ok() ==> r.get_Ok_0()@ == nonterminal_quads_len_model(
            (input@.len() as int),
            (input_len_rem as int),
        ),
        /* output too small -> OutputSliceTooSmall (but when the rem==1 trailing-byte convenience check fires, upstream reports InvalidByte first -- both exits coexist; the positive contract is the previous clause) */
        /* the full-exit characterization (feeding back the naive chain: the front
           check turns Err exactly in the two named cases; every other input shape
           returns Ok with the exact nonterminal length, so a caller whose loop
           reports an InvalidByte in the completed-quads region knows no front-check
           error shadowed it) */
        ((input_len_rem != 1)
            || (input@.len() == 0)
            || (input@ [(input@.len() as int) - 1] == padding)
            || (decode_table@ [(input@ [(input@.len() as int) - 1]) as int] < 64))
            && (output_len as int) >= nonterminal_quads_len_model(
                (input@.len() as int),
                (input_len_rem as int),
            ) / 4 * 3 ==> r.is_ok(),
        r.is_ok() ==> (output_len as int) >= (r.get_Ok_0()@ / 4 * 3),
{
    let ghost bytes = input@;
    /* Origin Rust:
       if input_len_rem == 1 {
           let last_byte = input[input.len() - 1];
           if last_byte != padding.as_u8()
               && decode_table[usize::from(last_byte)] == INVALID_VALUE {
               return Err(DecodeError::InvalidByte(input.len() - 1, last_byte).into()); } } */
    if input_len_rem == 1 {
        let last_index = input.len() - 1; /* rem==1 => len >= 1, no underflow */
        let last_byte = input[last_index];
        assert(last_byte == bytes[input@.len() as int - 1]);
        let morsel = decode_table[last_byte as usize];
        assert(morsel == decode_table@[(last_byte) as int]);
        if last_byte != padding && morsel == INVALID_VALUE {
            return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(last_index, last_byte)));
        }
    }
    /* Origin Rust:
       let input_complete_nonterminal_quads_len = input.len()
           .saturating_sub(input_len_rem)
           .saturating_sub(usize::from(input_len_rem == 0) * 4); */
    let base = input.len() - input_len_rem; /* rem = len%4 => input.len() - input_len_rem never underflows */
    /* Origin Rust: .saturating_sub(usize::from(input_len_rem == 0) * 4)
       -- rewritten equivalently as an explicit bound check (0 when rem==0 and len<4) */
    let nonterminal = if input_len_rem == 0 {
        if base >= 4 { base - 4 } else { 0 }
    } else { base };
    assert(nonterminal@ == nonterminal_quads_len_model((input@.len() as int), (input_len_rem as int)));
    /* Origin Rust:
       if output_len < input_complete_nonterminal_quads_len / 4 * 3 {
           return Err(DecodeSliceError::OutputSliceTooSmall); } */
    if output_len < nonterminal / 4 * 3 {
        return Result::Err(DecodeSliceError::OutputSliceTooSmall);
    }
    proof {
        assert(Result::<usize, DecodeSliceError>::Ok(nonterminal).get_Ok_0()@ == nonterminal@);
        assert(nonterminal@ == nonterminal_quads_len_model((input@.len() as int), (input_len_rem as int)));
    }
    Result::Ok(nonterminal)
}

/* ============================================================
 * Origin: decode.rs:309-352 `decode_chunk_4` (4 input -> 3 output)
 * ============================================================ */

/// The 4-morsel -> 3-byte bit-composition model:
/// o0 = m0<<2 | m1>>4, o1 = (m1&&0xF)<<4 | m2>>2, o2 = (m2&&0x3)<<6 | m3
/// Upstream doc (decode.rs:308-308):
///   Like [`decode_chunk_8`] but for 4 bytes of input and 3 bytes of output.
pub exec fn decode_chunk_4(
    input: &[u8],
    index_at_start_of_input: usize,
    decode_table: &[u8],
    output: &mut [u8],
) -> (r: Result<(), DecodeError>)
    requires
        input@.len() == 4,
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        output@.len() >= 3,
        /* index_at_start_of_input + 3 does not overflow (the upstream offset reporting needs +3) */
        index_at_start_of_input + 3 <= usize::MAX,
    ensures
        /* all four morsels legal ==> exact byte-composition output, only the first 3 bytes written */
        (
            decode_table@[(input@[0]) as int] < 64
                && decode_table@[(input@[1]) as int] < 64
                && decode_table@[(input@[2]) as int] < 64
                && decode_table@[(input@[3]) as int] < 64
        ) ==> r.is_ok()
            && final(output)@.len() == old(output)@.len()
            && final(output)@[0] == morsel_pair_lo(
                decode_table@[(input@[0]) as int],
                decode_table@[(input@[1]) as int],
            )
            && final(output)@[1] == morsel_pair_mid(
                decode_table@[(input@[1]) as int],
                decode_table@[(input@[2]) as int],
            )
            && final(output)@[2] == morsel_pair_hi(
                decode_table@[(input@[2]) as int],
                decode_table@[(input@[3]) as int],
            ),
        /* the first illegal morsel reported with exact offset/byte */
        is_invalid_morsel(decode_table@[(input@[0]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte(index_at_start_of_input, input@[0]),
        ),
        decode_table@[(input@[0]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[1]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 1) as usize, input@[1]),
        ),
        decode_table@[(input@[0]) as int] < 64
            && decode_table@[(input@[1]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[2]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 2) as usize, input@[2]),
        ),
        decode_table@[(input@[0]) as int] < 64
            && decode_table@[(input@[1]) as int] < 64
            && decode_table@[(input@[2]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[3]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 3) as usize, input@[3]),
        ),
        /* scan-covered exit faces (the mirror of decode_chunk_8's): the
           first-invalid scan over the 4-slice view pins the exact error and,
           on the all-legal reach, the byte conjuncts plus the untouched tail */
        naive_first_invalid(input@, decode_table@, 4, 0) < 4 ==> r == Result::Err(
            DecodeError::InvalidByte(
                ((index_at_start_of_input as int) + naive_first_invalid(
                    input@,
                    decode_table@,
                    4,
                    0,
                )) as usize,
                input@[naive_first_invalid(input@, decode_table@, 4, 0) as int],
            ),
        ),
        naive_first_invalid(input@, decode_table@, 4, 0) == 4 ==> r.is_ok()
            && final(output)@.len() == old(output)@.len()
            && final(output)@ [0] == morsel_pair_lo(
                decode_table@[(input@[0]) as int],
                decode_table@[(input@[1]) as int],
            )
            && final(output)@ [1] == morsel_pair_mid(
                decode_table@[(input@[1]) as int],
                decode_table@[(input@[2]) as int],
            )
            && final(output)@ [2] == morsel_pair_hi(
                decode_table@[(input@[2]) as int],
                decode_table@[(input@[3]) as int],
            )
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                3 <= j && j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j]),
{
    /* Origin Rust:
       let morsel = decode_table[usize::from(input[0])];
       if morsel == INVALID_VALUE { return Err(InvalidByte(index_at_start_of_input, input[0])); }
       let mut accum = u32::from(morsel) << 26; ... (18 repetitions) ...
       output[..3].copy_from_slice(&accum.to_be_bytes()[..3]);
       -- u32 bit packing + copy_from_slice have limited support, rewritten as the equivalent
          byte-by-byte write (bit-semantically equivalent: accum.to_be_bytes()[..3] is exactly the following triple) */
    let m0 = decode_table[input[0] as usize];
    assert(m0 == decode_table@[(input@[0]) as int]);
    if m0 == INVALID_VALUE {
    proof {
        assert(m0 == decode_table@[(input@[0]) as int]);
        assert(is_invalid_morsel(decode_table@[(input@[0]) as int]));
        nfi_unfold(input@, decode_table@, 4, 0);
        assert(naive_first_invalid(input@, decode_table@, 4, 0) == 0);
    }
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input, input[0]));
    }
    assert(m0 < 64);
    let m1 = decode_table[input[1] as usize];
    assert(m1 == decode_table@[(input@[1]) as int]);
    if m1 == INVALID_VALUE {
    proof {
        assert(m1 == decode_table@[(input@[1]) as int]);
        assert(is_invalid_morsel(decode_table@[(input@[1]) as int]));
        nfi_unfold(input@, decode_table@, 4, 0);
        nfi_unfold(input@, decode_table@, 4, 1);
        assert(naive_first_invalid(input@, decode_table@, 4, 0) == 1);
    }
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 1, input[1]));
    }
    assert(m1 < 64);
    let m2 = decode_table[input[2] as usize];
    assert(m2 == decode_table@[(input@[2]) as int]);
    if m2 == INVALID_VALUE {
    proof {
        assert(m2 == decode_table@[(input@[2]) as int]);
        assert(is_invalid_morsel(decode_table@[(input@[2]) as int]));
        nfi_unfold(input@, decode_table@, 4, 0);
        nfi_unfold(input@, decode_table@, 4, 1);
        nfi_unfold(input@, decode_table@, 4, 2);
        assert(naive_first_invalid(input@, decode_table@, 4, 0) == 2);
    }
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 2, input[2]));
    }
    assert(m2 < 64);
    let m3 = decode_table[input[3] as usize];
    assert(m3 == decode_table@[(input@[3]) as int]);
    if m3 == INVALID_VALUE {
    proof {
        assert(m3 == decode_table@[(input@[3]) as int]);
        assert(is_invalid_morsel(decode_table@[(input@[3]) as int]));
        nfi_unfold(input@, decode_table@, 4, 0);
        nfi_unfold(input@, decode_table@, 4, 1);
        nfi_unfold(input@, decode_table@, 4, 2);
        nfi_unfold(input@, decode_table@, 4, 3);
        assert(naive_first_invalid(input@, decode_table@, 4, 0) == 3);
    }
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 3, input[3]));
    }
    assert(m3 < 64);
    /* accum = m0<<26 | m1<<20 | m2<<14 | m3<<8 (u32); the first 3 bytes after unshifting: */
    proof {
        assert(morsel_pair_lo(m0, m1) == ((m0 as u32) * 4 + (m1 as u32) / 16) as u8) by (bit_vector)
            requires m0 < 64, m1 < 64;
    }
    let o0 = (((m0 as u32) * 4) + ((m1 as u32) / 16)) as u8;
    let o1 = (((m1 as u32) % 16 * 16) + (((m2 as u32) / 4) as u32)) as u8;
    let o2 = (((m2 as u32) % 4 * 64) + (m3 as u32)) as u8;
    assert(o0 == morsel_pair_lo(m0, m1));
    assert(o1 == morsel_pair_mid(m1, m2));
    assert(o2 == morsel_pair_hi(m2, m3));
    output[0] = o0;
    output[1] = o1;
    output[2] = o2;
    proof {
        assert(m0 == decode_table@[(input@[0]) as int]);
        assert(m1 == decode_table@[(input@[1]) as int]);
        assert(m2 == decode_table@[(input@[2]) as int]);
        assert(m3 == decode_table@[(input@[3]) as int]);
        assert forall|t: int|
            #![trigger decode_table@[(input@[t]) as int]] 0 <= t && t < 4 ==> decode_table@[
            (input@[t]) as int
        ] < 64 by {
            if t == 0 {
                assert(m0 < 64);
            } else if t == 1 {
                assert(m1 < 64);
            } else if t == 2 {
                assert(m2 < 64);
            } else if t == 3 {
                assert(m3 < 64);
            }
        }
        /* the scan-covered Ok face: the all-legal reach forces the scan to 4 */
        nfi_bounds(input@, decode_table@, 4, 0);
        if naive_first_invalid(input@, decode_table@, 4, 0) < 4 {
            let ghost p = naive_first_invalid(input@, decode_table@, 4, 0);
            nfi_hit(input@, decode_table@, 4, 0);
            assert(0 <= p && p < 4);
            assert(is_invalid_morsel(decode_table@[(input@[p]) as int]));
            assert(decode_table@[(input@[p]) as int] < 64);
            assert(decode_table@[(input@[p]) as int] == 255);
            assert(false);
        }
        assert(naive_first_invalid(input@, decode_table@, 4, 0) == 4);
        assert(output@.len() >= 3);
        let ghost q0 = old(output)@;
        assert(output@ == q0.update(0, o0).update(1, o1).update(2, o2));
        let ghost q1 = q0.update(0, o0);
        let ghost q2 = q1.update(1, o1);
        assert forall|j: int|
            #![trigger output@ [j]] 3 <= j && j < old(output)@.len() ==> output@ [j] == old(output)@ [j] by {
            if 3 <= j && j < old(output)@.len() {
                vstd::seq::lemma_seq_update_different(q0, j, 0, o0);
                vstd::seq::lemma_seq_update_different(q1, j, 1, o1);
                vstd::seq::lemma_seq_update_different(q2, j, 2, o2);
                assert(output@ [j] == q0 [j]);
            }
        }
    }
    Result::Ok(())
}

/// Bit-composition pair model (spec, shared by chunk_4/suffix)
/// int semantics (on the legal-morsel <= 63 domain): o0 = m0*4 + m1/16,
/// o1 = (m1%16)*16 + m2/4, o2 = (m2%4)*64 + m3 -- corresponding verbatim to the prefix of
/// the upstream u32 accum's to_be_bytes; the expressions use the u32 word shape
/// (isomorphic with the exec side, int semantics equivalent: each segment's value <= 255, no truncation difference).
pub open spec fn morsel_pair_lo(m0: u8, m1: u8) -> u8 {
    ((m0 as u32) * 4 + (m1 as u32) / 16) as u8
}

pub open spec fn morsel_pair_mid(m1: u8, m2: u8) -> u8 {
    ((m1 as u32) % 16 * 16 + (m2 as u32) / 4) as u8
}

pub open spec fn morsel_pair_hi(m2: u8, m3: u8) -> u8 {
    ((m2 as u32) % 4 * 64 + (m3 as u32)) as u8
}

/* ============================================================
 * Origin: decode.rs:213-265 `decode_chunk_8` (8 input bytes -> 6 output)
 * Upstream doc (decode.rs:208-212):
 *   Decode 8 bytes of input into 6 bytes of output.
 *   `input` is the 8 bytes to decode.
 *   `index_at_start_of_input` is the offset in the overall input (used for reporting errors
 *   accurately)
 *   `decode_table` is the lookup table for the particular base64 alphabet.
 *   `output` will have its first 6 bytes overwritten
 * Transcription notes: the accumulated u64 word is machine-levelized
 *   pair-by-pair (probe rule R6); the trailing write of upstream's
 *   copy_from_slice becomes six per-pair extraction stores:
 *   the eight morsel loads and their early returns are verbatim, and
 *   the byte-extraction semantics of the accumulated word are carried
 *   by the two-term shadow words (bit-identical; each pair projection
 *   verifies standalone, per the probe-proven R6).
 * ============================================================ */
pub(crate) exec fn decode_chunk_8(
    input: &[u8],
    index_at_start_of_input: usize,
    decode_table: &[u8],
    output: &mut [u8],
) -> (r: Result<(), DecodeError>)
    requires
        input@.len() == 8,
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        output@.len() >= 6,
        index_at_start_of_input + 7 <= usize::MAX,
    ensures
        (
            decode_table@[(input@[0]) as int] < 64 &&
            decode_table@[(input@[1]) as int] < 64 &&
            decode_table@[(input@[2]) as int] < 64 &&
            decode_table@[(input@[3]) as int] < 64 &&
            decode_table@[(input@[4]) as int] < 64 &&
            decode_table@[(input@[5]) as int] < 64 &&
            decode_table@[(input@[6]) as int] < 64 &&
            decode_table@[(input@[7]) as int] < 64
        ) ==> r.is_ok()
            && final(output)@.len() == old(output)@.len()
            && final(output)@ [0] == morsel_pair_lo(
                decode_table@[(input@[0]) as int],
                decode_table@[(input@[1]) as int],
            )
            && final(output)@ [1] == morsel_pair_mid(
                decode_table@[(input@[1]) as int],
                decode_table@[(input@[2]) as int],
            )
            && final(output)@ [2] == morsel_pair_hi(
                decode_table@[(input@[2]) as int],
                decode_table@[(input@[3]) as int],
            )
            && final(output)@ [3] == morsel_pair_lo(
                decode_table@[(input@[4]) as int],
                decode_table@[(input@[5]) as int],
            )
            && final(output)@ [4] == morsel_pair_mid(
                decode_table@[(input@[5]) as int],
                decode_table@[(input@[6]) as int],
            )
            && final(output)@ [5] == morsel_pair_hi(
                decode_table@[(input@[6]) as int],
                decode_table@[(input@[7]) as int],
            )
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                6 <= j && j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j]),
        is_invalid_morsel(decode_table@[(input@[0]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte(index_at_start_of_input, input@[0]),
        ),
        decode_table@[(input@[0]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[1]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 1) as usize, input@[1]),
        ),
        decode_table@[(input@[0]) as int] < 64 && decode_table@[(input@[1]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[2]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 2) as usize, input@[2]),
        ),
        decode_table@[(input@[0]) as int] < 64 && decode_table@[(input@[1]) as int] < 64 && decode_table@[(input@[2]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[3]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 3) as usize, input@[3]),
        ),
        decode_table@[(input@[0]) as int] < 64 && decode_table@[(input@[1]) as int] < 64 && decode_table@[(input@[2]) as int] < 64 && decode_table@[(input@[3]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[4]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 4) as usize, input@[4]),
        ),
        decode_table@[(input@[0]) as int] < 64 && decode_table@[(input@[1]) as int] < 64 && decode_table@[(input@[2]) as int] < 64 && decode_table@[(input@[3]) as int] < 64 && decode_table@[(input@[4]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[5]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 5) as usize, input@[5]),
        ),
        decode_table@[(input@[0]) as int] < 64 && decode_table@[(input@[1]) as int] < 64 && decode_table@[(input@[2]) as int] < 64 && decode_table@[(input@[3]) as int] < 64 && decode_table@[(input@[4]) as int] < 64 && decode_table@[(input@[5]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[6]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 6) as usize, input@[6]),
        ),
        decode_table@[(input@[0]) as int] < 64 && decode_table@[(input@[1]) as int] < 64 && decode_table@[(input@[2]) as int] < 64 && decode_table@[(input@[3]) as int] < 64 && decode_table@[(input@[4]) as int] < 64 && decode_table@[(input@[5]) as int] < 64 && decode_table@[(input@[6]) as int] < 64
            && is_invalid_morsel(decode_table@[(input@[7]) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte((index_at_start_of_input + 7) as usize, input@[7]),
        ),
        /* scan-covered exit faces: the first-invalid scan over the 8-slice view
           pins both the exact error and (on the all-legal reach) the byte
           conjuncts -- the integration layers consume these by scan algebra
           instead of re-deriving the per-slot cascade */
        naive_first_invalid(input@, decode_table@, 8, 0) < 8 ==> r == Result::Err(
            DecodeError::InvalidByte(
                ((index_at_start_of_input as int) + naive_first_invalid(
                    input@,
                    decode_table@,
                    8,
                    0,
                )) as usize,
                input@[naive_first_invalid(input@, decode_table@, 8, 0) as int],
            ),
        ),
        naive_first_invalid(input@, decode_table@, 8, 0) == 8 ==> r.is_ok()
            && final(output)@.len() == old(output)@.len()
            && final(output)@ [0] == morsel_pair_lo(
                decode_table@[(input@[0]) as int],
                decode_table@[(input@[1]) as int],
            )
            && final(output)@ [1] == morsel_pair_mid(
                decode_table@[(input@[1]) as int],
                decode_table@[(input@[2]) as int],
            )
            && final(output)@ [2] == morsel_pair_hi(
                decode_table@[(input@[2]) as int],
                decode_table@[(input@[3]) as int],
            )
            && final(output)@ [3] == morsel_pair_lo(
                decode_table@[(input@[4]) as int],
                decode_table@[(input@[5]) as int],
            )
            && final(output)@ [4] == morsel_pair_mid(
                decode_table@[(input@[5]) as int],
                decode_table@[(input@[6]) as int],
            )
            && final(output)@ [5] == morsel_pair_hi(
                decode_table@[(input@[6]) as int],
                decode_table@[(input@[7]) as int],
            )
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                6 <= j && j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j]),
    {
        let m0 = decode_table[input[0] as usize];
        if m0 == INVALID_VALUE {
            proof {
                assert(m0 == decode_table@[(input@[0]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[0]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 0);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input, input[0]));
        }
        assert(m0 < 64);
        let m1 = decode_table[input[1] as usize];
        if m1 == INVALID_VALUE {
            proof {
                assert(m1 == decode_table@[(input@[1]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[1]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 1);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 1, input[1]));
        }
        assert(m1 < 64);
        let m2 = decode_table[input[2] as usize];
        if m2 == INVALID_VALUE {
            proof {
                assert(m2 == decode_table@[(input@[2]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[2]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                nfi_unfold(input@, decode_table@, 8, 2);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 2);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 2, input[2]));
        }
        assert(m2 < 64);
        let m3 = decode_table[input[3] as usize];
        if m3 == INVALID_VALUE {
            proof {
                assert(m3 == decode_table@[(input@[3]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[3]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                nfi_unfold(input@, decode_table@, 8, 2);
                nfi_unfold(input@, decode_table@, 8, 3);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 3);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 3, input[3]));
        }
        assert(m3 < 64);
        let m4 = decode_table[input[4] as usize];
        if m4 == INVALID_VALUE {
            proof {
                assert(m4 == decode_table@[(input@[4]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[4]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                nfi_unfold(input@, decode_table@, 8, 2);
                nfi_unfold(input@, decode_table@, 8, 3);
                nfi_unfold(input@, decode_table@, 8, 4);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 4);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 4, input[4]));
        }
        assert(m4 < 64);
        let m5 = decode_table[input[5] as usize];
        if m5 == INVALID_VALUE {
            proof {
                assert(m5 == decode_table@[(input@[5]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[5]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                nfi_unfold(input@, decode_table@, 8, 2);
                nfi_unfold(input@, decode_table@, 8, 3);
                nfi_unfold(input@, decode_table@, 8, 4);
                nfi_unfold(input@, decode_table@, 8, 5);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 5);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 5, input[5]));
        }
        assert(m5 < 64);
        let m6 = decode_table[input[6] as usize];
        if m6 == INVALID_VALUE {
            proof {
                assert(m6 == decode_table@[(input@[6]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[6]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                nfi_unfold(input@, decode_table@, 8, 2);
                nfi_unfold(input@, decode_table@, 8, 3);
                nfi_unfold(input@, decode_table@, 8, 4);
                nfi_unfold(input@, decode_table@, 8, 5);
                nfi_unfold(input@, decode_table@, 8, 6);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 6);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 6, input[6]));
        }
        assert(m6 < 64);
        let m7 = decode_table[input[7] as usize];
        if m7 == INVALID_VALUE {
            proof {
                assert(m7 == decode_table@[(input@[7]) as int]);
                assert(is_invalid_morsel(decode_table@[(input@[7]) as int]));
                nfi_unfold(input@, decode_table@, 8, 0);
                nfi_unfold(input@, decode_table@, 8, 1);
                nfi_unfold(input@, decode_table@, 8, 2);
                nfi_unfold(input@, decode_table@, 8, 3);
                nfi_unfold(input@, decode_table@, 8, 4);
                nfi_unfold(input@, decode_table@, 8, 5);
                nfi_unfold(input@, decode_table@, 8, 6);
                nfi_unfold(input@, decode_table@, 8, 7);
                assert(naive_first_invalid(input@, decode_table@, 8, 0) == 7);
            }
            return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 7, input[7]));
        }
        assert(m7 < 64);
        /* Origin Rust (verbatim): let mut accum = u64::from(morsel) << 58;
           accum |= u64::from(morsel) << 52; ... accum |= u64::from(morsel) << 16;
           -- machine-levelization per the settled probe rule R6 (the full 8-term
           word is a bv false-negative at the middle shifts; every per-pair
           two-term projection verifies standalone): the accumulated word's six
           written bytes each carry exactly one morsel pair, so the byte
           extraction spells each pair through its own two-term shadow word
           (bit-identical to the copy_from_slice of accum.to_be_bytes()[..6]).
           The six shadows below tile the accumulated word's top 48 bits. */
        let w0 = ((m0 as u64) << 58) | ((m1 as u64) << 52);
        let w1 = ((m1 as u64) << 52) | ((m2 as u64) << 46);
        let w2 = ((m2 as u64) << 46) | ((m3 as u64) << 40);
        let w3 = ((m4 as u64) << 34) | ((m5 as u64) << 28);
        let w4 = ((m5 as u64) << 28) | ((m6 as u64) << 22);
        let w5 = ((m6 as u64) << 22) | ((m7 as u64) << 16);

        proof {
            assert(m0 == decode_table@[(input@[0]) as int]);
            assert(0 <= m0 && m0 < 64);
            assert(m1 == decode_table@[(input@[1]) as int]);
            assert(0 <= m1 && m1 < 64);
            assert(m2 == decode_table@[(input@[2]) as int]);
            assert(0 <= m2 && m2 < 64);
            assert(m3 == decode_table@[(input@[3]) as int]);
            assert(0 <= m3 && m3 < 64);
            assert(m4 == decode_table@[(input@[4]) as int]);
            assert(0 <= m4 && m4 < 64);
            assert(m5 == decode_table@[(input@[5]) as int]);
            assert(0 <= m5 && m5 < 64);
            assert(m6 == decode_table@[(input@[6]) as int]);
            assert(0 <= m6 && m6 < 64);
            assert(m7 == decode_table@[(input@[7]) as int]);
            assert(0 <= m7 && m7 < 64);
            /* the per-pair two-term projections (the probe-proven R6 forms) */
            assert(((m0 < 64) && (m1 < 64)) ==> (((((((m0 as u64) << 58) | ((m1 as u64) << 52))) >> 56) as u8) == ((((m0 as u32) * 4) + ((m1 as u32) / 16)) as u8))) by (bit_vector);
            assert(morsel_pair_lo(m0, m1) == ((((m0 as u32) * 4) + ((m1 as u32) / 16)) as u8));
            assert(((m1 < 64) && (m2 < 64)) ==> (((((((m1 as u64) << 52) | ((m2 as u64) << 46))) >> 48) as u8) == (((((m1 as u32) % 16) * 16) + ((m2 as u32) / 4)) as u8))) by (bit_vector);
            assert(morsel_pair_mid(m1, m2) == (((((m1 as u32) % 16) * 16) + ((m2 as u32) / 4)) as u8));
            assert(((m2 < 64) && (m3 < 64)) ==> (((((((m2 as u64) << 46) | ((m3 as u64) << 40))) >> 40) as u8) == (((((m2 as u32) % 4) * 64) + ((m3 as u32) / 1)) as u8))) by (bit_vector);
            assert(morsel_pair_hi(m2, m3) == (((((m2 as u32) % 4) * 64) + ((m3 as u32) / 1)) as u8));
            assert(((m4 < 64) && (m5 < 64)) ==> (((((((m4 as u64) << 34) | ((m5 as u64) << 28))) >> 32) as u8) == ((((m4 as u32) * 4) + ((m5 as u32) / 16)) as u8))) by (bit_vector);
            assert(morsel_pair_lo(m4, m5) == ((((m4 as u32) * 4) + ((m5 as u32) / 16)) as u8));
            assert(((m5 < 64) && (m6 < 64)) ==> (((((((m5 as u64) << 28) | ((m6 as u64) << 22))) >> 24) as u8) == (((((m5 as u32) % 16) * 16) + ((m6 as u32) / 4)) as u8))) by (bit_vector);
            assert(morsel_pair_mid(m5, m6) == (((((m5 as u32) % 16) * 16) + ((m6 as u32) / 4)) as u8));
            assert(((m6 < 64) && (m7 < 64)) ==> (((((((m6 as u64) << 22) | ((m7 as u64) << 16))) >> 16) as u8) == (((((m6 as u32) % 4) * 64) + ((m7 as u32) / 1)) as u8))) by (bit_vector);
            assert(morsel_pair_hi(m6, m7) == (((((m6 as u32) % 4) * 64) + ((m7 as u32) / 1)) as u8));
        }
    /* Origin Rust: output[0] = accum.to_be_bytes()[0] (bit-extraction store) */
        output[0] = (w0 >> 56) as u8;
        output[1] = (w1 >> 48) as u8;
        output[2] = (w2 >> 40) as u8;
        output[3] = (w3 >> 32) as u8;
        output[4] = (w4 >> 24) as u8;
        output[5] = (w5 >> 16) as u8;
        proof {
            /* the scan-covered Ok face: all 8 morsels legal (the per-site asserts
               above) forces the first-invalid scan over the slice to reach 8 */
            assert(m0 == decode_table@[(input@[0]) as int]);
            assert(m1 == decode_table@[(input@[1]) as int]);
            assert(m2 == decode_table@[(input@[2]) as int]);
            assert(m3 == decode_table@[(input@[3]) as int]);
            assert(m4 == decode_table@[(input@[4]) as int]);
            assert(m5 == decode_table@[(input@[5]) as int]);
            assert(m6 == decode_table@[(input@[6]) as int]);
            assert(m7 == decode_table@[(input@[7]) as int]);
            assert forall|t: int|
                #![trigger decode_table@[(input@[t]) as int]] 0 <= t && t < 8 ==> decode_table@[
                (input@[t]) as int
            ] < 64 by {
                if t == 0 {
                    assert(m0 < 64);
                    assert(decode_table@[(input@[0]) as int] < 64);
                } else if t == 1 {
                    assert(m1 < 64);
                } else if t == 2 {
                    assert(m2 < 64);
                } else if t == 3 {
                    assert(m3 < 64);
                } else if t == 4 {
                    assert(m4 < 64);
                } else if t == 5 {
                    assert(m5 < 64);
                } else if t == 6 {
                    assert(m6 < 64);
                } else if t == 7 {
                    assert(m7 < 64);
                }
            }
            nfi_bounds(input@, decode_table@, 8, 0);
            if naive_first_invalid(input@, decode_table@, 8, 0) < 8 {
                let ghost p = naive_first_invalid(input@, decode_table@, 8, 0);
                nfi_hit(input@, decode_table@, 8, 0);
                assert(0 <= p && p < 8);
                assert(is_invalid_morsel(decode_table@[(input@[p]) as int]));
                assert(decode_table@[(input@[p]) as int] < 64);
                assert(decode_table@[(input@[p]) as int] == 255);
                assert(false);
            }
            assert(naive_first_invalid(input@, decode_table@, 8, 0) == 8);
            assert(output@ [0] == morsel_pair_lo(m0, m1));
            assert(output@ [1] == morsel_pair_mid(m1, m2));
            assert(output@ [2] == morsel_pair_hi(m2, m3));
            assert(output@ [3] == morsel_pair_lo(m4, m5));
            assert(output@ [4] == morsel_pair_mid(m5, m6));
            assert(output@ [5] == morsel_pair_hi(m6, m7));
            assert forall|j: int|
                #![trigger output@ [j]]
                6 <= j && j < old(output)@.len() ==> output@ [j] == old(output)@ [j] by {
                assert(output@ [j] == output@ [j]);
            }
        }
        Result::Ok(())
    }

/* ============================================================
 * Origin: decode.rs:92-174 `decode_complete_quads` -- the two-layer loop
 * integration (this batch). The per-chunk bridge below carries one upstream
 * decode_chunk_8 call; decode_span32 chains four of them (the 32-byte unrolled
 * iteration); decode_complete_quads runs the two-layer lattice (32-byte chunks
 * then the 4-byte remainder through decode_chunk_4) on the machine-level offset
 * transcript of the upstream chunks_exact loops.
 * ============================================================ */

/// The decoded-quad byte model anchored at `out0` (the integration's own output
/// base, a quad-lattice position: out0 % 3 == 0, its input base out0/3*4).
/// The byte at absolute output position j >= out0 belongs to the quad
/// k = (j - out0)/3 with in-quad byte m = (j - out0)%3; the quad reads the four
/// table morsels of its input window [out0/3*4 + 4k, +4) and composes them
/// through the morsel_pair models (the exact semantics of decode_chunk_4/8).
pub open spec fn dec_quad_byte(decode_table: Seq<u8>, input: Seq<u8>, out0: int, j: int) -> u8 {
    let b = out0 / 3 * 4;
    let k = (j - out0) / 3;
    let m = (j - out0) % 3;
    let base = b + 4 * k;
    if m == 0 {
        morsel_pair_lo(
            decode_table[input[base] as int],
            decode_table[input[base + 1] as int],
        )
    } else if m == 1 {
        morsel_pair_mid(
            decode_table[input[base + 1] as int],
            decode_table[input[base + 2] as int],
        )
    } else {
        morsel_pair_hi(
            decode_table[input[base + 2] as int],
            decode_table[input[base + 3] as int],
        )
    }
}

/// One upstream decode_chunk_8 call, bridged to absolute coordinates: the byte
/// conjuncts re-anchor at the integration's out0, the error cover threads the
/// whole-input first-invalid scan, and the untouched windows close over the
/// whole output slice (the borrow-end concatenation of the &mut sub-slice).
pub(crate) exec fn decode_span8(
    input: &[u8],
    decode_table: &[u8],
    output: &mut [u8],
    ib: usize,
    ob: usize,
    out0: usize,
) -> (r: Result<(), DecodeError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        /* the integration's output anchor sits on the quad lattice */
        (out0 as int) % 3 == 0,
        /* the chunk's own bases sit on the same lattice, exactly two quads in */
        (out0 as int) <= (ob as int),
        ((ob as int) - (out0 as int)) % 3 == 0,
        ((ib as int) - (out0 as int) / 3 * 4) == 4 * (((ob as int) - (out0 as int)) / 3),
        (((ob as int) - (out0 as int)) / 3) % 2 == 0,
        (ib as int) + 8 <= input@.len() as int,
        (ib as int) + 8 <= input.len() as int,
        (ib as int) + 7 <= usize::MAX as int,
        (ob as int) + 6 <= output@.len() as int,
        (ob as int) + 6 <= output.len() as int,
    ensures
        final(output)@.len() == old(output)@.len(),
        /* the scan-pinned error face over the chunk's whole-input window (the
           low-window scan term indexes both the exact offset and byte) */
        r.is_err() ==> naive_first_invalid(
            input@,
            decode_table@,
            ((ib as int) + 8),
            (ib as int),
        ) < ((ib as int) + 8) && r == Result::Err(DecodeError::InvalidByte(
            (naive_first_invalid(input@, decode_table@, ((ib as int) + 8), (ib as int))) as usize,
            input@[naive_first_invalid(input@, decode_table@, ((ib as int) + 8), (ib as int)) as int],
        )),
        /* the Ok face: exact re-anchored bytes, whole-slice no-splash both below
           and above the 6-byte window, and the window's own legality */
        r.is_ok()
            ==> final(output)@.len() == old(output)@.len()
            && final(output)@ [(ob as int) + 0] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 0,
            )
            && final(output)@ [(ob as int) + 1] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 1,
            )
            && final(output)@ [(ob as int) + 2] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 2,
            )
            && final(output)@ [(ob as int) + 3] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 3,
            )
            && final(output)@ [(ob as int) + 4] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 4,
            )
            && final(output)@ [(ob as int) + 5] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 5,
            )
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                (0 <= j && j < (ob as int)) ==> final(output)@ [j] == old(output)@ [j])
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                ((ob as int) + 6) <= j && j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j])
            && (forall|t: int|
                #![trigger decode_table@[(input@[t]) as int]]
                (ib as int) <= t && t < ((ib as int) + 8) ==> decode_table@[(input@[t]) as int]
                    < 64),
{
    let ghost g_in = input@;
    let ghost g_table = decode_table@;
    let ghost g_out_entry = old(output)@;
    /* Origin Rust: decode_chunk_8(&chunk[0..8], input_index, decode_table,
       &mut chunk_output[0..6]) -- the slice binds through the whole slices */
    let sub_in = &input[ib..(ib + 8)];
    let ghost g_sub_in = sub_in@;
    proof {
        assert(g_sub_in == g_in.subrange((ib as int), ((ib as int) + 8)));
        assert(g_sub_in.len() == 8);
    }
    let sub_out = &mut output[ob..(ob + 6)];
    let cr = decode_chunk_8(sub_in, ib, decode_table, sub_out);
    let ghost g_sub_fin = sub_out@;
    /* the borrow-end concatenation of the &mut sub-slice (ambient, pinned) */
    assert(output@ == g_out_entry.subrange(0, (ob as int)) + g_sub_fin
        + g_out_entry.subrange(((ob as int) + 6), g_out_entry.len() as int));
    match cr {
        Result::Err(e) => {
            proof {
                /* the sub-scan is below 8 (the scan-covered Ok face excludes 8) */
                nfi_bounds(g_sub_in, g_table, 8, 0);
                assert(naive_first_invalid(g_sub_in, g_table, 8, 0) != 8);
                let ghost p = naive_first_invalid(g_sub_in, g_table, 8, 0);
                assert(0 <= p && p < 8);
                nfi_hit(g_sub_in, g_table, 8, 0);
                /* the contract's Err face: the error is exactly at ib + p */
                assert(e == DecodeError::InvalidByte(((ib as int) + p) as usize, g_sub_in[p]));
                /* the whole-input scan pins to ib + p: legal prefix assembled
                   through the sub-slice bridge */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ib as int) <= t && t < ((ib as int) + p) ==> !is_invalid_morsel(
                    g_table[(g_in[t]) as int],
                ) by {
                    if (ib as int) <= t && t < ((ib as int) + p) {
                        vstd::seq::lemma_seq_subrange_index(
                            g_in,
                            (ib as int),
                            ((ib as int) + 8),
                            (t - (ib as int)),
                        );
                        assert(g_in[t] == g_sub_in[t - (ib as int)]);
                        assert(!is_invalid_morsel(g_table[(g_sub_in[t - (ib as int)]) as int]));
                    }
                }
                vstd::seq::lemma_seq_subrange_index(g_in, (ib as int), ((ib as int) + 8), p);
                assert(g_in[(ib as int) + p] == g_sub_in[p]);
                assert(is_invalid_morsel(g_table[(g_in[(ib as int) + p]) as int]));
                nfi_split_at(g_in, g_table, ((ib as int) + 8), (ib as int), ((ib as int) + p));
                assert(naive_first_invalid(g_in, g_table, ((ib as int) + 8), (ib as int))
                    == ((ib as int) + p));
            }
            proof {
                assert(!(Result::<(), DecodeError>::Err(e)).is_ok());
                assert((Result::<(), DecodeError>::Err(e)).is_err());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* per-slot legality inversions (the scan-covered Ok face: each
                   error clause's antecedent would have made the chunk return
                   Err) -- the morsel terms live on the sub view, so they are
                   the sub's own bytes */
                assert(!is_invalid_morsel(g_table[(g_sub_in[0]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[1]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[2]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[3]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[4]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[5]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[6]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[7]) as int]));
                /* the whole-window legality (bridge-mapped) */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ib as int) <= t && t < ((ib as int) + 8) ==> decode_table@[(input@ [t]) as int]
                        < 64 by {
                    if (ib as int) <= t && t < ((ib as int) + 8) {
                        vstd::seq::lemma_seq_subrange_index(
                            g_in,
                            (ib as int),
                            ((ib as int) + 8),
                            (t - (ib as int)),
                        );
                        assert(g_in[t] == g_sub_in[t - (ib as int)]);
                        assert(g_table[(g_in[t]) as int] < 64);
                    }
                }
                /* both scans reach their ends (all bytes legal) */
                nfi_bounds(g_in, g_table, ((ib as int) + 8), (ib as int));
                if naive_first_invalid(g_in, g_table, ((ib as int) + 8), (ib as int)) < (ib as int) + 8 {
                    let ghost p = naive_first_invalid(g_in, g_table, ((ib as int) + 8), (ib as int));
                    nfi_hit(g_in, g_table, ((ib as int) + 8), (ib as int));
                    assert(0 <= p && p < 8);
                    assert(is_invalid_morsel(g_table[(g_in[p]) as int]));
                    assert(false);
                }
                if naive_first_invalid(g_sub_in, g_table, 8, 0) < 8 {
                    let ghost p = naive_first_invalid(g_sub_in, g_table, 8, 0);
                    nfi_hit(g_sub_in, g_table, 8, 0);
                    assert(0 <= p && p < 8);
                    assert(is_invalid_morsel(g_table[(g_sub_in[p]) as int]));
                    vstd::seq::lemma_seq_subrange_index(
                        g_in,
                        (ib as int),
                        ((ib as int) + 8),
                        p,
                    );
                    assert(g_in[(ib as int) + p] == g_sub_in[p]);
                    assert(is_invalid_morsel(g_table[(g_in[(ib as int) + p]) as int]));
                    assert(false);
                }
                /* the written bytes, restated on the whole output through the
                   borrow-end concatenation (each position via add-index chains) */
                vstd::seq::lemma_seq_subrange_len(g_out_entry, 0, (ob as int));
                vstd::seq::lemma_seq_subrange_len(
                    g_out_entry,
                    ((ob as int) + 6),
                    g_out_entry.len() as int,
                );
                vstd::seq::lemma_seq_add_len(
                    g_out_entry.subrange(0, (ob as int)),
                    g_sub_fin,
                );
                vstd::seq::lemma_seq_add_len(
                    g_sub_fin,
                    g_out_entry.subrange(((ob as int) + 6), g_out_entry.len() as int),
                );
                assert(output@ [(ob as int) + 0] == morsel_pair_lo(
                    g_table[(g_sub_in[0]) as int],
                    g_table[(g_sub_in[1]) as int],
                ));
                assert(output@ [(ob as int) + 1] == morsel_pair_mid(
                    g_table[(g_sub_in[1]) as int],
                    g_table[(g_sub_in[2]) as int],
                ));
                assert(output@ [(ob as int) + 2] == morsel_pair_hi(
                    g_table[(g_sub_in[2]) as int],
                    g_table[(g_sub_in[3]) as int],
                ));
                assert(output@ [(ob as int) + 3] == morsel_pair_lo(
                    g_table[(g_sub_in[4]) as int],
                    g_table[(g_sub_in[5]) as int],
                ));
                assert(output@ [(ob as int) + 4] == morsel_pair_mid(
                    g_table[(g_sub_in[5]) as int],
                    g_table[(g_sub_in[6]) as int],
                ));
                assert(output@ [(ob as int) + 5] == morsel_pair_hi(
                    g_table[(g_sub_in[6]) as int],
                    g_table[(g_sub_in[7]) as int],
                ));
                /* the sub bytes and the whole-input bytes agree (value bridges) */
                assert(g_sub_in[0] == g_in[(ib as int) + 0]);
                assert(g_sub_in[1] == g_in[(ib as int) + 1]);
                assert(g_sub_in[2] == g_in[(ib as int) + 2]);
                assert(g_sub_in[3] == g_in[(ib as int) + 3]);
                assert(g_sub_in[4] == g_in[(ib as int) + 4]);
                assert(g_sub_in[5] == g_in[(ib as int) + 5]);
                assert(g_sub_in[6] == g_in[(ib as int) + 6]);
                assert(g_sub_in[7] == g_in[(ib as int) + 7]);
                /* the re-anchored quad model at each written position (the
                   lattice arithmetic: the chunk's quads sit at out0-relative
                   quad indices gq and gq+1) */
                let gq = (((ob as int) - (out0 as int)) / 3) / 2 * 2;
                assert((ob as int) == (out0 as int) + 3 * (gq + 0));
                assert((ib as int) == (out0 as int) / 3 * 4 + 4 * gq);
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 0)
                    == morsel_pair_lo(
                        g_table[(g_in[(ib as int) + 0]) as int],
                        g_table[(g_in[(ib as int) + 1]) as int],
                    ));
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 1)
                    == morsel_pair_mid(
                        g_table[(g_in[(ib as int) + 1]) as int],
                        g_table[(g_in[(ib as int) + 2]) as int],
                    ));
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 2)
                    == morsel_pair_hi(
                        g_table[(g_in[(ib as int) + 2]) as int],
                        g_table[(g_in[(ib as int) + 3]) as int],
                    ));
                assert(((ob as int) + 3 - (out0 as int)) / 3 == gq + 1);
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 3)
                    == morsel_pair_lo(
                        g_table[(g_in[(ib as int) + 4]) as int],
                        g_table[(g_in[(ib as int) + 5]) as int],
                    ));
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 4)
                    == morsel_pair_mid(
                        g_table[(g_in[(ib as int) + 5]) as int],
                        g_table[(g_in[(ib as int) + 6]) as int],
                    ));
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 5)
                    == morsel_pair_hi(
                        g_table[(g_in[(ib as int) + 6]) as int],
                        g_table[(g_in[(ib as int) + 7]) as int],
                    ));
                /* the untouched windows (prefix and tail, via the concat chains) */
                assert forall|j: int|
                    #![trigger output@ [j]]
                    (0 <= j && j < (ob as int)) ==> output@ [j] == g_out_entry [j] by {
                    if 0 <= j && j < (ob as int) {
                        vstd::seq::lemma_seq_subrange_len(g_out_entry, 0, (ob as int));
                        vstd::seq::lemma_seq_subrange_index(g_out_entry, 0, (ob as int), j);
                        vstd::seq::lemma_seq_add_index1(
                            g_out_entry.subrange(0, (ob as int)),
                            g_sub_fin.add(
                                g_out_entry.subrange(((ob as int) + 6), g_out_entry.len() as int),
                            ),
                            j,
                        );
                        assert(output@ [j] == g_out_entry [j]);
                    }
                }
                assert forall|j: int|
                    #![trigger output@ [j]]
                    ((ob as int) + 6) <= j && j < output@.len() ==> output@ [j] == g_out_entry [j] by {
                    if ((ob as int) + 6) <= j && j < output@.len() {
                        vstd::seq::lemma_seq_subrange_len(g_out_entry, 0, (ob as int));
                        vstd::seq::lemma_seq_add_len(
                            g_out_entry.subrange(0, (ob as int)),
                            g_sub_fin,
                        );
                        vstd::seq::lemma_seq_subrange_index(
                            g_out_entry,
                            ((ob as int) + 6),
                            g_out_entry.len() as int,
                            j - ((ob as int) + 6),
                        );
                        vstd::seq::lemma_seq_add_index2(
                            (g_out_entry.subrange(0, (ob as int))).add(g_sub_fin),
                            g_out_entry.subrange(((ob as int) + 6), g_out_entry.len() as int),
                            j,
                        );
                        vstd::seq::lemma_seq_add_index2(
                            g_sub_fin,
                            g_out_entry.subrange(((ob as int) + 6), g_out_entry.len() as int),
                            j - (ob as int),
                        );
                        assert(output@ [j] == g_out_entry [j]);
                    }
                }
                /* the six written bytes land at their whole-output positions
                   (the concat's middle segment) */
                assert(output@ [(ob as int) + 0] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 0,
                ));
                assert(output@ [(ob as int) + 1] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 1,
                ));
                assert(output@ [(ob as int) + 2] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 2,
                ));
                assert(output@ [(ob as int) + 3] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 3,
                ));
                assert(output@ [(ob as int) + 4] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 4,
                ));
                assert(output@ [(ob as int) + 5] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 5,
                ));
            }
        },
    }
    Result::Ok(())
}

/// One full 32-byte unrolled iteration of decode_complete_quads: four
/// decode_span8 bridges chained on one accumulated legality, exporting the
/// iteration's whole-span scan face plus its twenty-four re-anchored byte
/// conjuncts as ground facts (the decode-side mirror of the encode fast_step32
/// pattern: the outer loop consumes this one step contract).
/* rlimit note (ledgered raise, this fn only): the four-chunk chain body check
   exceeds the default budget (unsolvable at default and at 40/60 pre-flip; the
   naive-first module order keeps the drv minimum at 80 while the alphabet
   harness panel needs 100 on this build -- the ladder lives in the batch's
   execution ledger). */
#[verifier::rlimit(200)]
pub(crate) exec fn decode_span32(
    input: &[u8],
    decode_table: &[u8],
    output: &mut [u8],
    ibase: usize,
    obase: usize,
    out0: usize,
) -> (r: Result<(), DecodeError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        (out0 as int) % 3 == 0,
        (out0 as int) <= (obase as int),
        ((obase as int) - (out0 as int)) % 3 == 0,
        (((obase as int) - (out0 as int)) / 3) % 2 == 0,
        ((ibase as int) - (out0 as int) / 3 * 4) == 4 * (((obase as int) - (out0 as int)) / 3),
        (ibase as int) + 32 <= input@.len() as int,
        (ibase as int) + 32 <= input.len() as int,
        (ibase as int) + 31 <= usize::MAX as int,
        (obase as int) + 24 <= output@.len() as int,
        (obase as int) + 24 <= output.len() as int,
    ensures
        final(output)@.len() == old(output)@.len(),
        /* the scan-pinned error face over the iteration's whole input window */
        r.is_err() ==> naive_first_invalid(
            input@,
            decode_table@,
            ((ibase as int) + 32),
            (ibase as int),
        ) < ((ibase as int) + 32) && r == Result::Err(DecodeError::InvalidByte(
            (naive_first_invalid(input@, decode_table@, ((ibase as int) + 32), (ibase as int))) as usize,
            input@[naive_first_invalid(input@, decode_table@, ((ibase as int) + 32), (ibase as int)) as int],
        )),
        /* the Ok face: the twenty-four re-anchored byte conjuncts, the
           whole-slice no-splash windows, and the window's own legality */
        r.is_ok()
            ==> final(output)@.len() == old(output)@.len()
            && final(output)@ [((obase as int) + 0)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 0),
            )
            && final(output)@ [((obase as int) + 1)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 1),
            )
            && final(output)@ [((obase as int) + 2)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 2),
            )
            && final(output)@ [((obase as int) + 3)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 3),
            )
            && final(output)@ [((obase as int) + 4)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 4),
            )
            && final(output)@ [((obase as int) + 5)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 5),
            )
            && final(output)@ [((obase as int) + 6)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 6),
            )
            && final(output)@ [((obase as int) + 7)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 7),
            )
            && final(output)@ [((obase as int) + 8)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 8),
            )
            && final(output)@ [((obase as int) + 9)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 9),
            )
            && final(output)@ [((obase as int) + 10)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 10),
            )
            && final(output)@ [((obase as int) + 11)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 11),
            )
            && final(output)@ [((obase as int) + 12)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 12),
            )
            && final(output)@ [((obase as int) + 13)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 13),
            )
            && final(output)@ [((obase as int) + 14)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 14),
            )
            && final(output)@ [((obase as int) + 15)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 15),
            )
            && final(output)@ [((obase as int) + 16)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 16),
            )
            && final(output)@ [((obase as int) + 17)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 17),
            )
            && final(output)@ [((obase as int) + 18)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 18),
            )
            && final(output)@ [((obase as int) + 19)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 19),
            )
            && final(output)@ [((obase as int) + 20)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 20),
            )
            && final(output)@ [((obase as int) + 21)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 21),
            )
            && final(output)@ [((obase as int) + 22)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 22),
            )
            && final(output)@ [((obase as int) + 23)] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                ((obase as int) + 23),
            )
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                ((0 <= j && j < (obase as int)) || (
                    ((obase as int) + 24) <= j && j < old(output)@.len()
                )) ==> final(output)@ [j] == old(output)@ [j])
            && (forall|t: int|
                #![trigger decode_table@[(input@[t]) as int]]
                (ibase as int) <= t && t < ((ibase as int) + 32) ==> decode_table@[(input@[t]) as int]
                    < 64),
{
    let ghost g_in = input@;
    let ghost g_table = decode_table@;
    let ghost g_entry = old(output)@;

    /* Origin Rust: decode_chunk_8(&chunk[0..8], input_index + 0, ...) */
    proof {
                let ghost q0 = ((obase as int) - (out0 as int)) / 3;
                assert(((obase as int) - (out0 as int)) == 3 * q0);
                assert((((obase as int) + 0)) - (out0 as int) == 3 * (q0 + 0));
                assert(((((obase as int) + 0)) - (out0 as int)) / 3 == q0 + 0);
                assert((((ibase as int) + 0)) == (out0 as int) / 3 * 4 + 4 * (q0 + 0));
                assert((((ibase as int) + 0)) - (out0 as int) / 3 * 4 == 4 * ((((obase as int) + 0)) - (out0 as int)) / 3);
                assert((((ibase as int) + 0)) + 8 <= (g_in.len() as int));
                assert((((ibase as int) + 0)) + 8 <= (input.len() as int));
                assert((((ibase as int) + 0)) + 7 <= usize::MAX as int);
                assert((((obase as int) + 0)) + 6 <= (output@.len() as int));
                assert((((obase as int) + 0)) + 6 <= (output.len() as int));
    }
    let cr0 = decode_span8(input, decode_table, output, ibase + 0, obase + 0, out0);
    match cr0 {
        Result::Err(e) => {
            proof {
                /* the chunk's scan window [chunk base, +8): its hit facts */
                let ghost z = naive_first_invalid(g_in, g_table, (((ibase as int) + 8)), (((ibase as int) + 0)));
                nfi_bounds(g_in, g_table, (((ibase as int) + 8)), (((ibase as int) + 0)));
                nfi_hit(g_in, g_table, (((ibase as int) + 8)), (((ibase as int) + 0)));
                assert((((ibase as int) + 0)) <= z && z < (((ibase as int) + 8)));
                assert(is_invalid_morsel(g_table[(g_in[z]) as int]));
                /* the accumulated legal prefix [ibase, z) */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < z ==> !is_invalid_morsel(
                    g_table[(g_in[t]) as int],
                ) by {
                    if (ibase as int) <= t && t < z {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    }
                }
                nfi_split_at(g_in, g_table, ((ibase as int) + 32), (ibase as int), z);
                assert(naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int)) == z);
                assert(!(Result::<(), DecodeError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* fold this chunk's window legality into the accumulated prefix */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < (((ibase as int) + 8)) ==> decode_table@[(input@ [t]) as int] < 64 by {
                    if (ibase as int) <= t && t < (((ibase as int) + 8)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    }
                }
                /* the chunk's six bytes on the current state */
                assert(output@ [((obase as int) + 0)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 0),
                ));
                assert(output@ [((obase as int) + 1)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 1),
                ));
                assert(output@ [((obase as int) + 2)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 2),
                ));
                assert(output@ [((obase as int) + 3)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 3),
                ));
                assert(output@ [((obase as int) + 4)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 4),
                ));
                assert(output@ [((obase as int) + 5)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 5),
                ));
                /* the earlier slots carried through this call's below window */
                /* the whole prefix below the chunk stays untouched */                assert forall|j: int|
                    #![trigger output@ [j]]
                    (0 <= j && j < (obase as int)) ==> output@ [j] == g_entry [j] by {
                    if 0 <= j && j < (obase as int) {
                        assert(output@ [j] == g_entry [j]);
                    }
                }
            }
        },
    }

    /* Origin Rust: decode_chunk_8(&chunk[8..16], input_index + 8, ...) */
    proof {
                let ghost q0 = ((obase as int) - (out0 as int)) / 3;
                assert(((obase as int) - (out0 as int)) == 3 * q0);
                assert((((obase as int) + 6)) - (out0 as int) == 3 * (q0 + 2));
                assert(((((obase as int) + 6)) - (out0 as int)) / 3 == q0 + 2);
                assert((((ibase as int) + 8)) == (out0 as int) / 3 * 4 + 4 * (q0 + 2));
                assert((((ibase as int) + 8)) - (out0 as int) / 3 * 4 == 4 * ((((obase as int) + 6)) - (out0 as int)) / 3);
                assert((((ibase as int) + 8)) + 8 <= (g_in.len() as int));
                assert((((ibase as int) + 8)) + 8 <= (input.len() as int));
                assert((((ibase as int) + 8)) + 7 <= usize::MAX as int);
                assert((((obase as int) + 6)) + 6 <= (output@.len() as int));
                assert((((obase as int) + 6)) + 6 <= (output.len() as int));
    }
    let cr1 = decode_span8(input, decode_table, output, ibase + 8, obase + 6, out0);
    match cr1 {
        Result::Err(e) => {
            proof {
                /* the chunk's scan window [chunk base, +8): its hit facts */
                let ghost z = naive_first_invalid(g_in, g_table, (((ibase as int) + 16)), (((ibase as int) + 8)));
                nfi_bounds(g_in, g_table, (((ibase as int) + 16)), (((ibase as int) + 8)));
                nfi_hit(g_in, g_table, (((ibase as int) + 16)), (((ibase as int) + 8)));
                assert((((ibase as int) + 8)) <= z && z < (((ibase as int) + 16)));
                assert(is_invalid_morsel(g_table[(g_in[z]) as int]));
                /* the accumulated legal prefix [ibase, z) */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < z ==> !is_invalid_morsel(
                    g_table[(g_in[t]) as int],
                ) by {
                    if (ibase as int) <= t && t < (((ibase as int) + 8)) {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    } else if (((ibase as int) + 8)) <= t && t < z {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    }
                }
                nfi_split_at(g_in, g_table, ((ibase as int) + 32), (ibase as int), z);
                assert(naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int)) == z);
                assert(!(Result::<(), DecodeError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* fold this chunk's window legality into the accumulated prefix */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < (((ibase as int) + 16)) ==> decode_table@[(input@ [t]) as int] < 64 by {
                    if (ibase as int) <= t && t < (((ibase as int) + 8)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    } else if (((ibase as int) + 8)) <= t && t < (((ibase as int) + 16)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    }
                }
                /* the chunk's six bytes on the current state */
                assert(output@ [((obase as int) + 6)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 6),
                ));
                assert(output@ [((obase as int) + 7)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 7),
                ));
                assert(output@ [((obase as int) + 8)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 8),
                ));
                assert(output@ [((obase as int) + 9)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 9),
                ));
                assert(output@ [((obase as int) + 10)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 10),
                ));
                assert(output@ [((obase as int) + 11)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 11),
                ));
                /* the earlier slots carried through this call's below window */
                    assert(output@ [((obase as int) + 0)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 0),
                    ));
                    assert(output@ [((obase as int) + 1)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 1),
                    ));
                    assert(output@ [((obase as int) + 2)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 2),
                    ));
                    assert(output@ [((obase as int) + 3)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 3),
                    ));
                    assert(output@ [((obase as int) + 4)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 4),
                    ));
                    assert(output@ [((obase as int) + 5)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 5),
                    ));
                /* the whole prefix below the chunk stays untouched */                assert forall|j: int|
                    #![trigger output@ [j]]
                    (0 <= j && j < (obase as int)) ==> output@ [j] == g_entry [j] by {
                    if 0 <= j && j < (obase as int) {
                        assert(output@ [j] == g_entry [j]);
                    }
                }
            }
        },
    }

    /* Origin Rust: decode_chunk_8(&chunk[16..24], input_index + 16, ...) */
    proof {
                let ghost q0 = ((obase as int) - (out0 as int)) / 3;
                assert(((obase as int) - (out0 as int)) == 3 * q0);
                assert((((obase as int) + 12)) - (out0 as int) == 3 * (q0 + 4));
                assert(((((obase as int) + 12)) - (out0 as int)) / 3 == q0 + 4);
                assert((((ibase as int) + 16)) == (out0 as int) / 3 * 4 + 4 * (q0 + 4));
                assert((((ibase as int) + 16)) - (out0 as int) / 3 * 4 == 4 * ((((obase as int) + 12)) - (out0 as int)) / 3);
                assert((((ibase as int) + 16)) + 8 <= (g_in.len() as int));
                assert((((ibase as int) + 16)) + 8 <= (input.len() as int));
                assert((((ibase as int) + 16)) + 7 <= usize::MAX as int);
                assert((((obase as int) + 12)) + 6 <= (output@.len() as int));
                assert((((obase as int) + 12)) + 6 <= (output.len() as int));
    }
    let cr2 = decode_span8(input, decode_table, output, ibase + 16, obase + 12, out0);
    match cr2 {
        Result::Err(e) => {
            proof {
                /* the chunk's scan window [chunk base, +8): its hit facts */
                let ghost z = naive_first_invalid(g_in, g_table, (((ibase as int) + 24)), (((ibase as int) + 16)));
                nfi_bounds(g_in, g_table, (((ibase as int) + 24)), (((ibase as int) + 16)));
                nfi_hit(g_in, g_table, (((ibase as int) + 24)), (((ibase as int) + 16)));
                assert((((ibase as int) + 16)) <= z && z < (((ibase as int) + 24)));
                assert(is_invalid_morsel(g_table[(g_in[z]) as int]));
                /* the accumulated legal prefix [ibase, z) */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < z ==> !is_invalid_morsel(
                    g_table[(g_in[t]) as int],
                ) by {
                    if (ibase as int) <= t && t < (((ibase as int) + 16)) {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    } else if (((ibase as int) + 16)) <= t && t < z {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    }
                }
                nfi_split_at(g_in, g_table, ((ibase as int) + 32), (ibase as int), z);
                assert(naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int)) == z);
                assert(!(Result::<(), DecodeError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* fold this chunk's window legality into the accumulated prefix */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < (((ibase as int) + 24)) ==> decode_table@[(input@ [t]) as int] < 64 by {
                    if (ibase as int) <= t && t < (((ibase as int) + 16)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    } else if (((ibase as int) + 16)) <= t && t < (((ibase as int) + 24)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    }
                }
                /* the chunk's six bytes on the current state */
                assert(output@ [((obase as int) + 12)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 12),
                ));
                assert(output@ [((obase as int) + 13)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 13),
                ));
                assert(output@ [((obase as int) + 14)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 14),
                ));
                assert(output@ [((obase as int) + 15)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 15),
                ));
                assert(output@ [((obase as int) + 16)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 16),
                ));
                assert(output@ [((obase as int) + 17)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 17),
                ));
                /* the earlier slots carried through this call's below window */
                    assert(output@ [((obase as int) + 0)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 0),
                    ));
                    assert(output@ [((obase as int) + 1)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 1),
                    ));
                    assert(output@ [((obase as int) + 2)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 2),
                    ));
                    assert(output@ [((obase as int) + 3)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 3),
                    ));
                    assert(output@ [((obase as int) + 4)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 4),
                    ));
                    assert(output@ [((obase as int) + 5)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 5),
                    ));
                    assert(output@ [((obase as int) + 6)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 6),
                    ));
                    assert(output@ [((obase as int) + 7)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 7),
                    ));
                    assert(output@ [((obase as int) + 8)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 8),
                    ));
                    assert(output@ [((obase as int) + 9)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 9),
                    ));
                    assert(output@ [((obase as int) + 10)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 10),
                    ));
                    assert(output@ [((obase as int) + 11)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 11),
                    ));
                /* the whole prefix below the chunk stays untouched */                assert forall|j: int|
                    #![trigger output@ [j]]
                    (0 <= j && j < (obase as int)) ==> output@ [j] == g_entry [j] by {
                    if 0 <= j && j < (obase as int) {
                        assert(output@ [j] == g_entry [j]);
                    }
                }
            }
        },
    }

    /* Origin Rust: decode_chunk_8(&chunk[24..32], input_index + 24, ...) */
    proof {
                let ghost q0 = ((obase as int) - (out0 as int)) / 3;
                assert(((obase as int) - (out0 as int)) == 3 * q0);
                assert((((obase as int) + 18)) - (out0 as int) == 3 * (q0 + 6));
                assert(((((obase as int) + 18)) - (out0 as int)) / 3 == q0 + 6);
                assert((((ibase as int) + 24)) == (out0 as int) / 3 * 4 + 4 * (q0 + 6));
                assert((((ibase as int) + 24)) - (out0 as int) / 3 * 4 == 4 * ((((obase as int) + 18)) - (out0 as int)) / 3);
                assert((((ibase as int) + 24)) + 8 <= (g_in.len() as int));
                assert((((ibase as int) + 24)) + 8 <= (input.len() as int));
                assert((((ibase as int) + 24)) + 7 <= usize::MAX as int);
                assert((((obase as int) + 18)) + 6 <= (output@.len() as int));
                assert((((obase as int) + 18)) + 6 <= (output.len() as int));
    }
    let cr3 = decode_span8(input, decode_table, output, ibase + 24, obase + 18, out0);
    match cr3 {
        Result::Err(e) => {
            proof {
                /* the chunk's scan window [chunk base, +8): its hit facts */
                let ghost z = naive_first_invalid(g_in, g_table, (((ibase as int) + 32)), (((ibase as int) + 24)));
                nfi_bounds(g_in, g_table, (((ibase as int) + 32)), (((ibase as int) + 24)));
                nfi_hit(g_in, g_table, (((ibase as int) + 32)), (((ibase as int) + 24)));
                assert((((ibase as int) + 24)) <= z && z < (((ibase as int) + 32)));
                assert(is_invalid_morsel(g_table[(g_in[z]) as int]));
                /* the accumulated legal prefix [ibase, z) */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < z ==> !is_invalid_morsel(
                    g_table[(g_in[t]) as int],
                ) by {
                    if (ibase as int) <= t && t < (((ibase as int) + 24)) {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    } else if (((ibase as int) + 24)) <= t && t < z {
                        assert(!is_invalid_morsel(g_table[(g_in[t]) as int]));
                    }
                }
                nfi_split_at(g_in, g_table, ((ibase as int) + 32), (ibase as int), z);
                assert(naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int)) == z);
                assert(!(Result::<(), DecodeError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* fold this chunk's window legality into the accumulated prefix */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ibase as int) <= t && t < (((ibase as int) + 32)) ==> decode_table@[(input@ [t]) as int] < 64 by {
                    if (ibase as int) <= t && t < (((ibase as int) + 24)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    } else if (((ibase as int) + 24)) <= t && t < (((ibase as int) + 32)) {
                        assert(decode_table@[(input@ [t]) as int] < 64);
                    }
                }
                /* the chunk's six bytes on the current state */
                assert(output@ [((obase as int) + 18)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 18),
                ));
                assert(output@ [((obase as int) + 19)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 19),
                ));
                assert(output@ [((obase as int) + 20)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 20),
                ));
                assert(output@ [((obase as int) + 21)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 21),
                ));
                assert(output@ [((obase as int) + 22)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 22),
                ));
                assert(output@ [((obase as int) + 23)] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    ((obase as int) + 23),
                ));
                /* the earlier slots carried through this call's below window */
                    assert(output@ [((obase as int) + 0)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 0),
                    ));
                    assert(output@ [((obase as int) + 1)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 1),
                    ));
                    assert(output@ [((obase as int) + 2)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 2),
                    ));
                    assert(output@ [((obase as int) + 3)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 3),
                    ));
                    assert(output@ [((obase as int) + 4)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 4),
                    ));
                    assert(output@ [((obase as int) + 5)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 5),
                    ));
                    assert(output@ [((obase as int) + 6)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 6),
                    ));
                    assert(output@ [((obase as int) + 7)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 7),
                    ));
                    assert(output@ [((obase as int) + 8)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 8),
                    ));
                    assert(output@ [((obase as int) + 9)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 9),
                    ));
                    assert(output@ [((obase as int) + 10)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 10),
                    ));
                    assert(output@ [((obase as int) + 11)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 11),
                    ));
                    assert(output@ [((obase as int) + 12)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 12),
                    ));
                    assert(output@ [((obase as int) + 13)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 13),
                    ));
                    assert(output@ [((obase as int) + 14)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 14),
                    ));
                    assert(output@ [((obase as int) + 15)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 15),
                    ));
                    assert(output@ [((obase as int) + 16)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 16),
                    ));
                    assert(output@ [((obase as int) + 17)] == dec_quad_byte(
                        g_table,
                        g_in,
                        (out0 as int),
                        ((obase as int) + 17),
                    ));
                /* the whole prefix below the chunk stays untouched */                assert forall|j: int|
                    #![trigger output@ [j]]
                    (0 <= j && j < (obase as int)) ==> output@ [j] == g_entry [j] by {
                    if 0 <= j && j < (obase as int) {
                        assert(output@ [j] == g_entry [j]);
                    }
                }
            }
        },
    }
    proof {
        /* the all-legal reach forces the whole-span scan to its end */
        nfi_bounds(g_in, g_table, ((ibase as int) + 32), (ibase as int));
        if naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int)) < ((ibase as int) + 32) {
            let ghost p = naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int));
            nfi_hit(g_in, g_table, ((ibase as int) + 32), (ibase as int));
            assert((ibase as int) <= p && p < ((ibase as int) + 32));
            assert(is_invalid_morsel(g_table[(g_in[p]) as int]));
            assert(decode_table@[(input@ [p]) as int] < 64);
            assert(false);
        }
        assert(naive_first_invalid(g_in, g_table, ((ibase as int) + 32), (ibase as int))
            == ((ibase as int) + 32));
        /* the whole-output untouched tail above the iteration's window */
        assert forall|j: int|
            #![trigger output@ [j]]
            ((obase as int) + 24) <= j && j < output@.len() ==> output@ [j] == g_entry [j] by {
            if ((obase as int) + 24) <= j && j < output@.len() {
                assert(output@ [j] == g_entry [j]);
            }
        }
    }
    Result::Ok(())
}

/// The 4-byte counterpart of decode_span8: one upstream decode_chunk_4 call
/// bridged to absolute coordinates (the inner chunks_exact(4) layer of
/// decode_complete_quads consumes this one step contract per quad).
pub(crate) exec fn decode_span4(
    input: &[u8],
    decode_table: &[u8],
    output: &mut [u8],
    ib: usize,
    ob: usize,
    out0: usize,
) -> (r: Result<(), DecodeError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        (out0 as int) % 3 == 0,
        (out0 as int) <= (ob as int),
        ((ob as int) - (out0 as int)) % 3 == 0,
        ((ib as int) - (out0 as int) / 3 * 4) == 4 * (((ob as int) - (out0 as int)) / 3),
        (ib as int) + 4 <= input@.len() as int,
        (ib as int) + 4 <= input.len() as int,
        (ib as int) + 3 <= usize::MAX as int,
        (ob as int) + 3 <= output@.len() as int,
        (ob as int) + 3 <= output.len() as int,
    ensures
        final(output)@.len() == old(output)@.len(),
        /* the scan-pinned error face over the quad's whole-input window */
        r.is_err() ==> naive_first_invalid(
            input@,
            decode_table@,
            ((ib as int) + 4),
            (ib as int),
        ) < ((ib as int) + 4) && r == Result::Err(DecodeError::InvalidByte(
            (naive_first_invalid(input@, decode_table@, ((ib as int) + 4), (ib as int))) as usize,
            input@[naive_first_invalid(input@, decode_table@, ((ib as int) + 4), (ib as int)) as int],
        )),
        /* the Ok face: exact re-anchored bytes, whole-slice no-splash both below
           and above the 3-byte window, and the window's own legality */
        r.is_ok()
            ==> final(output)@.len() == old(output)@.len()
            && final(output)@ [(ob as int) + 0] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 0,
            )
            && final(output)@ [(ob as int) + 1] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 1,
            )
            && final(output)@ [(ob as int) + 2] == dec_quad_byte(
                decode_table@,
                input@,
                (out0 as int),
                (ob as int) + 2,
            )
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                (0 <= j && j < (ob as int)) ==> final(output)@ [j] == old(output)@ [j])
            && (forall|j: int|
                #![trigger final(output)@ [j]]
                ((ob as int) + 3) <= j && j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j])
            && (forall|t: int|
                #![trigger decode_table@[(input@[t]) as int]]
                (ib as int) <= t && t < ((ib as int) + 4) ==> decode_table@[(input@[t]) as int]
                    < 64),
{
    let ghost g_in = input@;
    let ghost g_table = decode_table@;
    let ghost g_out_entry = old(output)@;
    /* Origin Rust: decode_chunk_4(chunk, ..., chunk_output) -- the slice binds
       through the whole slices */
    let sub_in = &input[ib..(ib + 4)];
    let ghost g_sub_in = sub_in@;
    proof {
        assert(g_sub_in == g_in.subrange((ib as int), ((ib as int) + 4)));
        assert(g_sub_in.len() == 4);
    }
    let sub_out = &mut output[ob..(ob + 3)];
    let cr = decode_chunk_4(sub_in, ib, decode_table, sub_out);
    let ghost g_sub_fin = sub_out@;
    /* the borrow-end concatenation of the &mut sub-slice (ambient, pinned) */
    assert(output@ == g_out_entry.subrange(0, (ob as int)) + g_sub_fin
        + g_out_entry.subrange(((ob as int) + 3), g_out_entry.len() as int));
    match cr {
        Result::Err(e) => {
            proof {
                nfi_bounds(g_sub_in, g_table, 4, 0);
                assert(naive_first_invalid(g_sub_in, g_table, 4, 0) != 4);
                let ghost p = naive_first_invalid(g_sub_in, g_table, 4, 0);
                assert(0 <= p && p < 4);
                nfi_hit(g_sub_in, g_table, 4, 0);
                /* the contract's Err face: the error is exactly at ib + p */
                assert(e == DecodeError::InvalidByte(((ib as int) + p) as usize, g_sub_in[p]));
                /* the whole-input scan pins to ib + p */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ib as int) <= t && t < ((ib as int) + p) ==> !is_invalid_morsel(
                    g_table[(g_in[t]) as int],
                ) by {
                    if (ib as int) <= t && t < ((ib as int) + p) {
                        vstd::seq::lemma_seq_subrange_index(
                            g_in,
                            (ib as int),
                            ((ib as int) + 4),
                            (t - (ib as int)),
                        );
                        assert(g_in[t] == g_sub_in[t - (ib as int)]);
                        assert(!is_invalid_morsel(g_table[(g_sub_in[t - (ib as int)]) as int]));
                    }
                }
                vstd::seq::lemma_seq_subrange_index(g_in, (ib as int), ((ib as int) + 4), p);
                assert(g_in[(ib as int) + p] == g_sub_in[p]);
                assert(is_invalid_morsel(g_table[(g_in[(ib as int) + p]) as int]));
                nfi_split_at(g_in, g_table, ((ib as int) + 4), (ib as int), ((ib as int) + p));
                assert(naive_first_invalid(g_in, g_table, ((ib as int) + 4), (ib as int))
                    == ((ib as int) + p));
                assert(!(Result::<(), DecodeError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* per-slot legality inversions on the sub view */
                assert(!is_invalid_morsel(g_table[(g_sub_in[0]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[1]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[2]) as int]));
                assert(!is_invalid_morsel(g_table[(g_sub_in[3]) as int]));
                /* the whole-window legality (bridge-mapped) */
                assert forall|t: int|
                    #![trigger g_table[(g_in[t]) as int]]
                    (ib as int) <= t && t < ((ib as int) + 4) ==> decode_table@[(input@ [t]) as int]
                        < 64 by {
                    if (ib as int) <= t && t < ((ib as int) + 4) {
                        vstd::seq::lemma_seq_subrange_index(
                            g_in,
                            (ib as int),
                            ((ib as int) + 4),
                            (t - (ib as int)),
                        );
                        assert(g_in[t] == g_sub_in[t - (ib as int)]);
                        assert(g_table[(g_in[t]) as int] < 64);
                    }
                }
                /* both scans reach their ends */
                nfi_bounds(g_in, g_table, ((ib as int) + 4), (ib as int));
                if naive_first_invalid(g_in, g_table, ((ib as int) + 4), (ib as int)) < ((ib as int) + 4) {
                    let ghost p = naive_first_invalid(g_in, g_table, ((ib as int) + 4), (ib as int));
                    nfi_hit(g_in, g_table, ((ib as int) + 4), (ib as int));
                    assert(0 <= p && p < 4);
                    assert(is_invalid_morsel(g_table[(g_in[p]) as int]));
                    assert(false);
                }
                if naive_first_invalid(g_sub_in, g_table, 4, 0) < 4 {
                    let ghost p = naive_first_invalid(g_sub_in, g_table, 4, 0);
                    nfi_hit(g_sub_in, g_table, 4, 0);
                    assert(0 <= p && p < 4);
                    assert(is_invalid_morsel(g_table[(g_sub_in[p]) as int]));
                    vstd::seq::lemma_seq_subrange_index(g_in, (ib as int), ((ib as int) + 4), p);
                    assert(g_in[(ib as int) + p] == g_sub_in[p]);
                    assert(is_invalid_morsel(g_table[(g_in[(ib as int) + p]) as int]));
                    assert(false);
                }
                /* the written bytes restated on the whole output (the concat's
                   middle segment) */
                vstd::seq::lemma_seq_subrange_len(g_out_entry, 0, (ob as int));
                vstd::seq::lemma_seq_subrange_len(
                    g_out_entry,
                    ((ob as int) + 3),
                    g_out_entry.len() as int,
                );
                vstd::seq::lemma_seq_add_len(
                    g_out_entry.subrange(0, (ob as int)),
                    g_sub_fin,
                );
                vstd::seq::lemma_seq_add_len(
                    g_sub_fin,
                    g_out_entry.subrange(((ob as int) + 3), g_out_entry.len() as int),
                );
                assert(output@ [(ob as int) + 0] == morsel_pair_lo(
                    g_table[(g_sub_in[0]) as int],
                    g_table[(g_sub_in[1]) as int],
                ));
                assert(output@ [(ob as int) + 1] == morsel_pair_mid(
                    g_table[(g_sub_in[1]) as int],
                    g_table[(g_sub_in[2]) as int],
                ));
                assert(output@ [(ob as int) + 2] == morsel_pair_hi(
                    g_table[(g_sub_in[2]) as int],
                    g_table[(g_sub_in[3]) as int],
                ));
                /* the value bridges */
                assert(g_sub_in[0] == g_in[(ib as int) + 0]);
                assert(g_sub_in[1] == g_in[(ib as int) + 1]);
                assert(g_sub_in[2] == g_in[(ib as int) + 2]);
                assert(g_sub_in[3] == g_in[(ib as int) + 3]);
                /* the re-anchored quad model at each written position */
                let gq = ((ob as int) - (out0 as int)) / 3;
                assert((ob as int) == (out0 as int) + 3 * gq);
                assert((ib as int) == (out0 as int) / 3 * 4 + 4 * gq);
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 0)
                    == morsel_pair_lo(
                        g_table[(g_in[(ib as int) + 0]) as int],
                        g_table[(g_in[(ib as int) + 1]) as int],
                    ));
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 1)
                    == morsel_pair_mid(
                        g_table[(g_in[(ib as int) + 1]) as int],
                        g_table[(g_in[(ib as int) + 2]) as int],
                    ));
                assert(dec_quad_byte(g_table, g_in, (out0 as int), (ob as int) + 2)
                    == morsel_pair_hi(
                        g_table[(g_in[(ib as int) + 2]) as int],
                        g_table[(g_in[(ib as int) + 3]) as int],
                    ));
                /* the untouched windows */
                assert forall|j: int|
                    #![trigger output@ [j]]
                    (0 <= j && j < (ob as int)) ==> output@ [j] == g_out_entry [j] by {
                    if 0 <= j && j < (ob as int) {
                        vstd::seq::lemma_seq_subrange_len(g_out_entry, 0, (ob as int));
                        vstd::seq::lemma_seq_subrange_index(g_out_entry, 0, (ob as int), j);
                        vstd::seq::lemma_seq_add_index1(
                            g_out_entry.subrange(0, (ob as int)),
                            g_sub_fin.add(
                                g_out_entry.subrange(((ob as int) + 3), g_out_entry.len() as int),
                            ),
                            j,
                        );
                        assert(output@ [j] == g_out_entry [j]);
                    }
                }
                assert forall|j: int|
                    #![trigger output@ [j]]
                    ((ob as int) + 3) <= j && j < output@.len() ==> output@ [j] == g_out_entry [j] by {
                    if ((ob as int) + 3) <= j && j < output@.len() {
                        vstd::seq::lemma_seq_subrange_len(g_out_entry, 0, (ob as int));
                        vstd::seq::lemma_seq_add_len(
                            g_out_entry.subrange(0, (ob as int)),
                            g_sub_fin,
                        );
                        vstd::seq::lemma_seq_subrange_index(
                            g_out_entry,
                            ((ob as int) + 3),
                            g_out_entry.len() as int,
                            j - ((ob as int) + 3),
                        );
                        vstd::seq::lemma_seq_add_index2(
                            (g_out_entry.subrange(0, (ob as int))).add(g_sub_fin),
                            g_out_entry.subrange(((ob as int) + 3), g_out_entry.len() as int),
                            j,
                        );
                        vstd::seq::lemma_seq_add_index2(
                            g_sub_fin,
                            g_out_entry.subrange(((ob as int) + 3), g_out_entry.len() as int),
                            j - (ob as int),
                        );
                        assert(output@ [j] == g_out_entry [j]);
                    }
                }
                assert(output@ [(ob as int) + 0] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 0,
                ));
                assert(output@ [(ob as int) + 1] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 1,
                ));
                assert(output@ [(ob as int) + 2] == dec_quad_byte(
                    g_table,
                    g_in,
                    (out0 as int),
                    (ob as int) + 2,
                ));
            }
        },
    }
    Result::Ok(())
}


/// Upstream doc (decode.rs:92-94):
///   Decode the complete non-terminal quads in `input[input_index_start..input_index_end]` (both
///   bounds multiples of 4), writing to `output` starting at `output_index_start`, which must equal
///   `input_index_start / 4 * 3`. Error offsets are reported in absolute input coordinates.
/// Transcription notes: the two chunks_exact layers (32-byte unrolled then the 4-byte
/// remainder) run as offset cursors over the whole slices (the lib.rs ledger's
/// chunks_exact rewrite); the 32-byte layer consumes the single-step
/// decode_span32 contract, the 4-byte layer the decode_span4 contract; the
/// output room is the caller's (upstream complete_quads_len) check, so this fn
/// carries it as a requires and has no OutputSliceTooSmall exit.
/* rlimit note (ledgered raise, this fn only): the outer 32-byte layer's loop
   maintenance query is over the default budget in the suffix-props harness
   panel (default-fail re-measured post-flip; 100 green across all five
   contexts -- the ladder lives in the batch's execution ledger). */
#[verifier::rlimit(100)]
pub(crate) exec fn decode_complete_quads(
    input: &[u8],
    input_index_start: usize,
    input_index_end: usize,
    decode_table: &[u8],
    output: &mut [u8],
    output_index_start: usize,
) -> (r: Result<(), DecodeSliceError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        input_index_start % 4 == 0,
        input_index_end % 4 == 0,
        input_index_start <= input_index_end,
        (input_index_end as int) <= input@.len() as int,
        (input_index_end as int) <= input.len() as int,
        (input_index_end as int) + 7 <= usize::MAX as int,
        output_index_start == input_index_start / 4 * 3,
        ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3)) <= output@.len() as int,
        ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3)) <= output.len() as int,
    ensures
        final(output)@.len() == old(output)@.len(),
        /* the iff first-invalid scan characterization over the whole window */
        naive_first_invalid(input@, decode_table@, (input_index_end as int), (input_index_start as int)) < (input_index_end as int) ==> r
            == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
            (naive_first_invalid(input@, decode_table@, (input_index_end as int), (input_index_start as int))) as usize,
            input@[naive_first_invalid(input@, decode_table@, (input_index_end as int), (input_index_start as int)) as int],
        ))),
        /* the result-gated Ok face (the composition layer consumes this one:
           on Ok the whole-window scan reached the end, the region model holds,
           and both no-splash windows are untouched) */
        r.is_ok()
            ==> naive_first_invalid(input@, decode_table@, (input_index_end as int), (input_index_start as int))
                == (input_index_end as int)
            && forall|j: int|
                #![trigger final(output)@ [j]]
                ((output_index_start as int) <= j && j < ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3))) ==> final(output)@ [j]
                    == dec_quad_byte(
                        decode_table@,
                        input@,
                        (output_index_start as int),
                        j,
                    )
            && forall|j: int|
                #![trigger final(output)@ [j]]
                ((0 <= j && j < (output_index_start as int)) || (
                    ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3)) <= j
                        && j < old(output)@.len()
                )) ==> final(output)@ [j] == old(output)@ [j],
        naive_first_invalid(input@, decode_table@, (input_index_end as int), (input_index_start as int)) == (input_index_end as int) ==> r.is_ok()
            && forall|j: int|
                #![trigger final(output)@ [j]]
                ((output_index_start as int) <= j && j < ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3))) ==> final(output)@ [j]
                    == dec_quad_byte(
                        decode_table@,
                        input@,
                        (output_index_start as int),
                        j,
                    )
            && forall|j: int|
                #![trigger final(output)@ [j]]
                ((0 <= j && j < (output_index_start as int)) || (
                    ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3)) <= j
                        && j < old(output)@.len()
                )) ==> final(output)@ [j] == old(output)@ [j],
{
    let ghost g_in = input@;
    let ghost g_table = decode_table@;
    let ghost g_entry = old(output)@;

    /* Origin Rust:
       const UNROLLED_INPUT_CHUNK_SIZE: usize = 32;
       let quads_len = input_index_end - input_index_start;
       let unrolled_loop_len = quads_len - quads_len % 32;
       let input_unrolled_loop_end = input_index_start + unrolled_loop_len; */
    let quads_len = input_index_end - input_index_start;
    let unrolled_len = quads_len - (quads_len % 32);
    let unrolled_end = input_index_start + unrolled_len;

    /* the outer layer: one decode_span32 step per 32-byte chunk, chaining the
       first-invalid scan and the written-region model on the cursor pair */
    let mut cur: usize = input_index_start;
    let mut ow: usize = output_index_start;
    while cur < unrolled_end
        invariant
            decode_table@.len() == 256,
            g_table == decode_table@,
            ValidDecodeTable(g_table),
            g_in == input@,
            g_entry == old(output)@,
            output@.len() == g_entry.len(),
            input_index_start % 4 == 0,
            input_index_end % 4 == 0,
            input_index_start <= input_index_end,
            (input_index_end as int) <= g_in.len() as int,
            (input_index_end as int) + 7 <= usize::MAX as int,
            output_index_start == input_index_start / 4 * 3,
            ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3)) <= output@.len(),
            (input_index_start as int) <= (cur as int) <= (unrolled_end as int),
            ((cur as int) - (input_index_start as int)) % 32 == 0,
            (unrolled_end as int) == (input_index_start as int) + (unrolled_len as int),
            (unrolled_len as int) == ((input_index_end as int) - (input_index_start as int))
                - (((input_index_end as int) - (input_index_start as int)) % 32),
            (ow as int) == (output_index_start as int) + ((cur as int) - (input_index_start as int)) / 4 * 3,
            naive_first_invalid(g_in, g_table, (input_index_end as int), (input_index_start as int))
                == naive_first_invalid(g_in, g_table, (input_index_end as int), (cur as int)),
            forall|j: int|
                #![trigger output@ [j]]
                ((output_index_start as int) <= j && j < (ow as int)) ==> output@ [j]
                    == dec_quad_byte(g_table, g_in, (output_index_start as int), j),
            forall|j: int|
                #![trigger output@ [j]]
                ((0 <= j && j < (output_index_start as int)) || (
                    (ow as int) <= j && j < (output@.len() as int)
                )) ==> output@ [j] == g_entry [j],
        decreases (unrolled_end as int) - (cur as int)
    {
        proof {
            /* the span32 lattice requirements off the cursor pair */
            let k = ((cur as int) - (input_index_start as int)) / 32;
            assert((cur as int) == (input_index_start as int) + 32 * k);
            let q0 = ((ow as int) - (output_index_start as int)) / 3;
            assert(((ow as int) - (output_index_start as int)) == 24 * k);
            assert(((ow as int) - (output_index_start as int)) == 3 * q0);
            assert((q0) == 8 * k);
            assert((q0) % 2 == 0);
            assert(((ow as int) - (output_index_start as int)) % 3 == 0);
            assert((output_index_start as int) % 3 == 0);
            assert((cur as int) == (output_index_start as int) / 3 * 4 + 4 * q0);
            assert((cur as int) - (output_index_start as int) / 3 * 4 == 4 * (((ow as int) - (output_index_start as int)) / 3));
            assert((cur as int) + 32 <= (unrolled_end as int));
            assert((cur as int) + 32 <= (g_in.len() as int));
            assert((cur as int) + 32 <= (input.len() as int));
            assert((cur as int) + 31 <= usize::MAX as int);
            assert((ow as int) + 24 <= (output@.len() as int));
            assert((ow as int) + 24 <= (output.len() as int));
        }
        let step = decode_span32(input, decode_table, output, cur, ow, output_index_start);
        match step {
            Result::Err(e) => {
                proof {
                    /* the step's scan-pinned error chains onto the whole-window scan */
                    let z = naive_first_invalid(g_in, g_table, ((cur as int) + 32), (cur as int));
                    assert(z < ((cur as int) + 32));
                    nfi_pin(g_in, g_table, ((cur as int) + 32), (input_index_end as int), (cur as int));
                    assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (cur as int)) == z);
                    assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (input_index_start as int)) == z);
                    assert(z < (input_index_end as int));
                    assert(!(Result::<(), DecodeSliceError>::Err(DecodeSliceError::DecodeError(e))).is_ok());
                }
                return Result::Err(DecodeSliceError::DecodeError(e));
            },
            Result::Ok(()) => {
                proof {
                    /* the step's window legality re-extends the scan chain */
                    nfi_skip(
                        g_in,
                        g_table,
                        (input_index_end as int),
                        (cur as int),
                        ((cur as int) + 32),
                    );
                    assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (cur as int))
                        == naive_first_invalid(g_in, g_table, (input_index_end as int), ((cur as int) + 32)));
                    /* the written region extends through the step's twenty-four
                       ground slots */
                    assert forall|j: int|
                        #![trigger output@ [j]]
                        ((output_index_start as int) <= j && j < ((ow as int) + 24)) ==> output@ [j]
                            == dec_quad_byte(
                            g_table,
                            g_in,
                            (output_index_start as int),
                            j,
                        ) by {
                        if (output_index_start as int) <= j && j < (ow as int) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == (ow as int) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 1) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 2) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 3) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 4) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 5) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 6) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 7) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 8) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 9) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 10) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 11) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 12) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 13) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 14) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 15) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 16) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 17) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 18) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 19) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 20) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 21) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 22) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 23) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        }
                    }
                    /* the untouched windows re-extend */
                    assert forall|j: int|
                        #![trigger output@ [j]]
                        ((0 <= j && j < (output_index_start as int)) || (
                            ((ow as int) + 24) <= j && j < (output@.len() as int)
                        )) ==> output@ [j] == g_entry [j] by {
                        if (0 <= j && j < (output_index_start as int)) || (
                            ((ow as int) + 24) <= j && j < (output@.len() as int)
                        ) {
                            assert(output@ [j] == g_entry [j]);
                        }
                    }
                }
            },
        }
        /* Origin Rust: the cursor arithmetic of the enumerate() loops */
        cur += 32;
        ow += 24;
        proof {
            assert(((cur as int) - (input_index_start as int)) % 32 == 0);
            assert((cur as int) <= (unrolled_end as int));
            assert(((cur as int) - 32 - (input_index_start as int)) % 32 == 0);
            assert((unrolled_end as int) - (cur as int) >= 0);
            assert((ow as int) == (output_index_start as int) + ((cur as int) - (input_index_start as int)) / 4 * 3);
        }
    }

    /* the inner layer: the remaining quads (less than 32 bytes, at most 7 quads),
       each one a decode_span4 step */
    while cur < input_index_end
        invariant
            decode_table@.len() == 256,
            g_table == decode_table@,
            ValidDecodeTable(g_table),
            g_in == input@,
            g_entry == old(output)@,
            output@.len() == g_entry.len(),
            input_index_start % 4 == 0,
            input_index_end % 4 == 0,
            input_index_start <= input_index_end,
            (input_index_end as int) <= g_in.len() as int,
            (input_index_end as int) + 7 <= usize::MAX as int,
            output_index_start == input_index_start / 4 * 3,
            ((output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3)) <= output@.len(),
            (input_index_start as int) <= (cur as int) <= (input_index_end as int),
            ((cur as int) - (input_index_start as int)) % 4 == 0,
            (unrolled_end as int) == (input_index_start as int) + (unrolled_len as int),
            (unrolled_len as int) == ((input_index_end as int) - (input_index_start as int))
                - (((input_index_end as int) - (input_index_start as int)) % 32),
            (ow as int) == (output_index_start as int) + ((cur as int) - (input_index_start as int)) / 4 * 3,
            naive_first_invalid(g_in, g_table, (input_index_end as int), (input_index_start as int))
                == naive_first_invalid(g_in, g_table, (input_index_end as int), (cur as int)),
            forall|j: int|
                #![trigger output@ [j]]
                ((output_index_start as int) <= j && j < (ow as int)) ==> output@ [j]
                    == dec_quad_byte(g_table, g_in, (output_index_start as int), j),
            forall|j: int|
                #![trigger output@ [j]]
                ((0 <= j && j < (output_index_start as int)) || (
                    (ow as int) <= j && j < (output@.len() as int)
                )) ==> output@ [j] == g_entry [j],
        decreases (input_index_end as int) - (cur as int)
    {
        proof {
            /* the span4 lattice requirements off the cursor pair */
            let k = ((cur as int) - (input_index_start as int)) / 4;
            assert((cur as int) == (input_index_start as int) + 4 * k);
            assert((ow as int) - (output_index_start as int) == 3 * k);
            assert(((ow as int) - (output_index_start as int)) % 3 == 0);
            assert((output_index_start as int) % 3 == 0);
            assert((cur as int) == (output_index_start as int) / 3 * 4 + 4 * (((ow as int) - (output_index_start as int)) / 3));
            assert((cur as int) + 4 <= (input_index_end as int));
            assert((cur as int) + 4 <= (g_in.len() as int));
            assert((cur as int) + 4 <= (input.len() as int));
            assert((cur as int) + 3 <= usize::MAX as int);
            assert((ow as int) + 3 <= (output@.len() as int));
            assert((ow as int) + 3 <= (output.len() as int));
        }
        let step = decode_span4(input, decode_table, output, cur, ow, output_index_start);
        match step {
            Result::Err(e) => {
                proof {
                    let z = naive_first_invalid(g_in, g_table, ((cur as int) + 4), (cur as int));
                    assert(z < ((cur as int) + 4));
                    nfi_pin(g_in, g_table, ((cur as int) + 4), (input_index_end as int), (cur as int));
                    assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (cur as int)) == z);
                    assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (input_index_start as int)) == z);
                    assert(z < (input_index_end as int));
                    assert(!(Result::<(), DecodeSliceError>::Err(DecodeSliceError::DecodeError(e))).is_ok());
                }
                return Result::Err(DecodeSliceError::DecodeError(e));
            },
            Result::Ok(()) => {
                proof {
                    nfi_skip(
                        g_in,
                        g_table,
                        (input_index_end as int),
                        (cur as int),
                        ((cur as int) + 4),
                    );
                    assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (cur as int))
                        == naive_first_invalid(g_in, g_table, (input_index_end as int), ((cur as int) + 4)));
                    assert forall|j: int|
                        #![trigger output@ [j]]
                        ((output_index_start as int) <= j && j < ((ow as int) + 3)) ==> output@ [j]
                            == dec_quad_byte(
                            g_table,
                            g_in,
                            (output_index_start as int),
                            j,
                        ) by {
                        if (output_index_start as int) <= j && j < (ow as int) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == (ow as int) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 1) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        } else if j == ((ow as int) + 2) {
                            assert(output@ [j] == dec_quad_byte(
                                g_table,
                                g_in,
                                (output_index_start as int),
                                j,
                            ));
                        }
                    }
                    assert forall|j: int|
                        #![trigger output@ [j]]
                        ((0 <= j && j < (output_index_start as int)) || (
                            ((ow as int) + 3) <= j && j < (output@.len() as int)
                        )) ==> output@ [j] == g_entry [j] by {
                        if (0 <= j && j < (output_index_start as int)) || (
                            ((ow as int) + 3) <= j && j < (output@.len() as int)
                        ) {
                            assert(output@ [j] == g_entry [j]);
                        }
                    }
                }
            },
        }
        /* Origin Rust: the cursor arithmetic of the chunks_exact(4) loop */
        cur += 4;
        ow += 3;
        proof {
            assert(((cur as int) - (input_index_start as int)) % 4 == 0);
            assert((ow as int) == (output_index_start as int) + ((cur as int) - (input_index_start as int)) / 4 * 3);
        }
    }
    /* loop exits: cursor pair exactly at the window end */
    proof {
        assert((cur as int) == (input_index_end as int));
        assert((ow as int) == (output_index_start as int) + (((input_index_end as int) - (input_index_start as int)) / 4 * 3));
        /* the all-legal reach closes the scan chain at the window end */
        assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (input_index_end as int))
            == (input_index_end as int));
        assert(naive_first_invalid(g_in, g_table, (input_index_end as int), (input_index_start as int))
            == (input_index_end as int));
    }
    Result::Ok(())
}

/* ============================================================
 * Origin: decode.rs:30-90 `decode_helper` -- the integration composition
 * (this batch): the complete_quads_len front check, the two-layer
 * decode_complete_quads over the whole nonterminal region, and the
 * decode_suffix tail, with the simd_prefix closure monomorphized to the
 * scalar engine's only possible value (0, 0) -- the same precedent as the
 * encode side's encode_helper.
 * ============================================================ */

/// Upstream doc (decode.rs:30-45):
///   Helper to avoid duplicating `num_chunks` calculation, which is costly on short inputs.
///   Returns the decode metadata, or an error.
/// Transcription notes: the `estimate: &GeneralPurposeEstimate` parameter is
/// monomorphized to its `rem` field (the only field the body reads; the
/// conservative length was the callers' preallocation helper); the GeneralPurposeEstimate
/// struct itself carries the verified construction contract (estimate_decoded_len above).
pub(crate) exec fn decode_helper(
    input: &[u8],
    rem: usize,
    output: &mut [u8],
    decode_table: &[u8],
    decode_allow_trailing_bits: bool,
    padding: u8,
    padding_mode: DecodePaddingMode,
) -> (r: Result<DecodeMetadata, DecodeSliceError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        input@.len() as int % 4 == rem as int,
        /* the offset-reporting slack family of the components */
        (input@.len() as int) <= usize::MAX as int - 8,
        (output@.len() as int) <= usize::MAX as int - 4,
    ensures
        r.is_ok() ==> final(output)@.len() == old(output)@.len(),
        /* the front-check pass-through (verbatim from the complete_quads_len
           positive clause) */
        rem == 1
            && input@.len() == 1
            && input@[0] != padding
            && is_invalid_morsel(decode_table@[(input@[0]) as int]) ==> r
            == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(0, input@[0]))),
        /* the exact first-invalid clause of the complete-quads region:
           the named front-check exclusions (trailing illegal non-pad byte / the
           output room) hold and the region holds an invalid morsel -> verbatim
           report at the scan position (the complete_quads iff face; the suffix
           never runs in this case) */
        ((naive_first_invalid(
            input@,
            decode_table@,
            nonterminal_quads_len_model((input@.len() as int), (rem as int)),
            0,
        ) as int) < nonterminal_quads_len_model(
            (input@.len() as int),
            (rem as int),
        ))
            && !(rem == 1
                && input@.len() > 0
                && input@ [(input@.len() as int) - 1] != padding
                && is_invalid_morsel(
                    decode_table@ [(input@ [(input@.len() as int) - 1]) as int],
                ))
            && ((old(output)@.len() as int) >= nonterminal_quads_len_model(
                (input@.len() as int),
                (rem as int),
            ) / 4 * 3)
            ==> r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
            (naive_first_invalid(
                input@,
                decode_table@,
                nonterminal_quads_len_model((input@.len() as int), (rem as int)),
                0,
            )) as usize,
            input@ [naive_first_invalid(
                input@,
                decode_table@,
                nonterminal_quads_len_model((input@.len() as int), (rem as int)),
                0,
            ) as int],
        ))),
        /* the pass-through of the exit-safety face: on success the decoded
           length is the complete-quads region plus at most 3 suffix bytes; an
           all-empty input is the 0-byte success */
        r.is_ok() ==> (r.get_Ok_0().decoded_len as int) >= nonterminal_quads_len_model(
            (input@.len() as int),
            (rem as int),
        ) / 4 * 3,
        r.is_ok() ==> ((r.get_Ok_0().decoded_len as int) - nonterminal_quads_len_model(
            (input@.len() as int),
            (rem as int),
        ) / 4 * 3) <= 3,
        input@.len() == 0 ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == 0,
        /* The Ok-path no-splash clause above the decoded length is not re-
           stated at this boundary: the window forall of the complete-quads
           layer does not transport into this caller frame for trigger
           matching (its own caller-span consumption verifies; at this depth
           the composition keeps the naive_internal_decode contract shape --
           lengths, exactness and the exitfaces only). */
{
    let ghost g_in = input@;
    let ghost g_table = decode_table@;
    let ghost g_entry = old(output)@;
    /* Origin Rust:
       let input_complete_nonterminal_quads_len =
           complete_quads_len(input, estimate.rem, output.len(), decode_table, padding)?; */
    let front = complete_quads_len(input, rem, output.len(), decode_table, padding);
    let nt = match front {
        Result::Err(e) => {
            proof {
                assert(!(Result::<DecodeMetadata, DecodeSliceError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(v) => v,
    };
    proof {
        assert((nt as int) == nonterminal_quads_len_model((g_in.len() as int), (rem as int)));
        assert((nt as int) <= g_in.len() as int);
        assert((g_in.len() as int) - (nt as int) <= 4);
        assert((nt as int) <= usize::MAX as int - 8);
        assert(((old(output)@.len() as int)) >= (nt as int) / 4 * 3);
    }
    /* Origin Rust: let output_complete_quad_len = input_complete_nonterminal_quads_len / 4 * 3;
       -- the in-quad division bridge */
    let ocql = nt / 4 * 3;
    /* Origin Rust: let (input_index, output_index) = simd_prefix(input,
       input_complete_nonterminal_quads_len, output);
       -- the scalar engine's simd_prefix is the pure-scalar (0, 0) (upstream doc:
       "(0, 0) (pure scalar) is always valid") */
    let input_index: usize = 0;
    let output_index: usize = 0;
    proof {
        assert((input_index as int) == 0);
        assert((output_index as int) == 0);
        assert((nt as int) % 4 == 0);
        assert((nt as int) + 7 <= usize::MAX as int);
        assert((output_index as int) + (nt as int) / 4 * 3 <= (output.len() as int));
    }
    /* Origin Rust: decode_complete_quads(input, input_index,
       input_complete_nonterminal_quads_len, decode_table, output,
       output_index)?; */
    let cq = decode_complete_quads(input, input_index, nt, decode_table, output, output_index);
    match cq {
        Result::Err(e) => {
            proof {
                assert(!(Result::<DecodeMetadata, DecodeSliceError>::Err(e)).is_ok());
            }
            return Result::Err(e);
        },
        Result::Ok(()) => {
            proof {
                /* the callee's iff faces: on its Ok the whole-window scan reached
                   the end (the Err face is a ground implication), which opens the
                   Ok clause's no-splash conjuncts */
                assert(cq.is_ok());
                nfi_bounds(input@, decode_table@, (nt as int), 0);
                assert(naive_first_invalid(input@, decode_table@, (nt as int), 0) < (nt as int) ==> (cq == Result::<(), DecodeSliceError>::Err(
                    DecodeSliceError::DecodeError(DecodeError::InvalidByte(
                        naive_first_invalid(input@, decode_table@, (nt as int), 0) as usize,
                        input@[naive_first_invalid(input@, decode_table@, (nt as int), 0) as int],
                    )),
                )));
                assert(naive_first_invalid(input@, decode_table@, (nt as int), 0) == (nt as int));
                assert((nt as int) / 4 * 3 == (ocql as int));
            }
        },
    }
    /* the post-state of the complete-quads layer: the suffix's entry state */
    let ghost cq_state = output@;
    /* Origin Rust: super::decode_suffix::decode_suffix(input,
       input_complete_nonterminal_quads_len, output, output_complete_quad_len,
       decode_table, decode_allow_trailing_bits, padding, padding_mode) */
    let res = decode_suffix(
        input,
        nt,
        output,
        ocql,
        decode_table,
        decode_allow_trailing_bits,
        padding,
        padding_mode,
        Ghost(false),
    );
    proof {
        /* the exit-face rounding: on Ok the metadata length relation uses the
           suffix's own exit-safety clauses (output_index == ocql here) */
        if res.is_ok() {
            let md = res.get_Ok_0();
            assert((md.decoded_len as int) >= (ocql as int));
            assert((md.decoded_len as int) - (ocql as int) <= 3);
        }
    }
    res
}

/* ============================================================
 * integration record (coverage-diff-set batch; see out/bug-finder-summary.md)
 * - `decode_complete_quads` and `decode_helper` are transcribed and verified
 *   above: the 32-byte unrolled layer consumes the single-step decode_span32
 *   contract (four decode_span8 bridges, each one upstream decode_chunk_8
 *   call), the 4-byte remainder layer the decode_span4 contract (one
 *   decode_chunk_4 call per quad); the first-invalid scan algebra
 *   (naive_first_invalid + the nfi_* lemmas of engine/naive.rs) threads the
 *   error covers in absolute coordinates and the dec_quad_byte model carries
 *   the Ok-path region bytes. The one ledgered rlimit raise of this file is
 *   the decode_span32 body check (the four-chunk chain).
 * ============================================================ */

} // verus!
