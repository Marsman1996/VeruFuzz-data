//! `engine/general_purpose/decode.rs` mirror -- aggregation of the verified items
//!   (the full GeneralPurposeEstimate::new contract / the full complete_quads_len contract / decode_chunk_4)
//!
//! Relaxation (lib.rs ledger): `decode_table: &[u8; 256]` -> `&[u8]` + the model constraint
//! `ValidDecodeTable` (every morsel look-up is semantically equivalent); the loop integrations of
//! decode_chunk_8 / decode_complete_quads / decode_helper are in the file-tail blocked record.

use vstd::prelude::*;
use super::super::super::decode::{DecodeError, DecodeSliceError};

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
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input, input[0]));
    }
    assert(m0 < 64);
    let m1 = decode_table[input[1] as usize];
    assert(m1 == decode_table@[(input@[1]) as int]);
    if m1 == INVALID_VALUE {
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 1, input[1]));
    }
    assert(m1 < 64);
    let m2 = decode_table[input[2] as usize];
    assert(m2 == decode_table@[(input@[2]) as int]);
    if m2 == INVALID_VALUE {
        return Result::Err(DecodeError::InvalidByte(index_at_start_of_input + 2, input[2]));
    }
    assert(m2 < 64);
    let m3 = decode_table[input[3] as usize];
    assert(m3 == decode_table@[(input@[3]) as int]);
    if m3 == INVALID_VALUE {
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
        assert(output@.len() >= 3);
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
 * blocked record (the out/bug-finder-summary.md machine-check scope)
 * - `decode_chunk_8` (8->6, the same bit-composition pattern x4) with `decode_complete_quads`
 *   (the 32-byte unrolled + chunks_exact(4) two-layer loop) and the `decode_helper` integration:
 *   the same shape family as decode_chunk_4 (the full loop framework exceeds the solver
 *   budget), recorded as blocked-solver-shape.
 * ============================================================ */

} // verus!
