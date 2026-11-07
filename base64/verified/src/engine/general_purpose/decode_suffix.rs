//! `engine/general_purpose/decode_suffix.rs` mirror -- the verbatim transcription of `decode_suffix`
//!
//! Transcription baseline: an upstream-isomorphic while scan (the suffix is <= 4 bytes), the
//! morsel/first_pad/last_symbol state machine, the three padding-mode states and the
//! trailing-bits mask check, output through get_mut bounds checking.
//!
//! Contract scope: the obligation anchors (each error branch's reachability + the
//! panic-free surface + the output bounds) live in this file; the semantic depth (the
//! error variants/offsets/composed bytes) is carried by the harness case-table lemmas
//! (harness/ut_decode_suffix_props.rs). `morsels: [u8;4]` is relaxed into 4 local variables (semantically equivalent: only loaded in order into the u32 composition).

use vstd::prelude::*;
use super::super::super::decode::{DecodeError, DecodeSliceError};
use super::decode::{ValidDecodeTable, INVALID_VALUE};
use super::super::DecodePaddingMode;

verus! {

/// Origin: engine/mod.rs:502 `DecodeMetadata`
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct DecodeMetadata {
    pub decoded_len: usize,
    pub padding_offset: Option<usize>,
}

/* ============================================================
 * Origin: decode_suffix.rs:13-170 `decode_suffix`
 * ============================================================ */

/// Upstream doc (decode_suffix.rs:7-11):
///   Decode the last 0-4 bytes, checking for trailing set bits and padding per the provided
///   parameters.
///   Returns the decode metadata representing the total number of bytes decoded, including the ones
///   indicated as already written by `output_index`.
pub exec fn decode_suffix(
    input: &[u8],
    input_index: usize,
    output: &mut [u8],
    output_index: usize,
    decode_table: &[u8],
    decode_allow_trailing_bits: bool,
    padding: u8,
    padding_mode: DecodePaddingMode,
) -> (r: Result<DecodeMetadata, DecodeSliceError>)
    requires
        input_index <= input@.len(),
        input@.len() - input_index <= 4,
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        /* caller contract (satisfied at every upstream call site): output_index is an offset within output;
           the incr/write obligations need +4 not to overflow */
        ((output_index as int) + 4) <= usize::MAX as int,
        /* the InvalidLastSymbol offset = input_index + morsels - 1 neither underflows nor overflows */
        (input_index as int) <= usize::MAX as int - 8,
    ensures
        /* exit-safety face: on success the incremental output is <= 3 bytes and decoded_len is monotone */
        match r {
            Result::Ok(md) => (((md.decoded_len as int) >= (output_index as int))
                && (((md.decoded_len as int) - (output_index as int)) <= 3)),
            Result::Err(_) => true,
        },
        /* an all-empty input is always Ok with 0 bytes (the upstream !input.is_empty() gate) */
        (input@.len() == 0) ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == (output_index as int),
        /* no exit writes unauthorized bytes beyond output[old_idx ..] (the output increment is controlled) */
        r.is_ok() ==> final(output)@.len() == old(output)@.len(),
{
    let ghost bytes = input@;
    let mut out_idx = output_index; /* local mutable mirror (ensures refers to the parameter's entry value) */
    /* Origin Rust: let mut morsels_in_leftover = 0;
       let mut padding_bytes_count = 0;
       let mut first_padding_offset: usize = 0;
       let mut last_symbol = 0_u8;
       let mut last_symbol_value = 0_u8;
       let mut morsels = [0_u8; 4]; -- the morsels array becomes 4 local variables */
    let mut morsels_in_leftover: usize = 0;
    let mut padding_bytes_count: usize = 0;
    let mut first_padding_offset: usize = 0;
    let mut last_symbol: u8 = 0;
    let mut last_symbol_value: u8 = 0;
    let mut m0: u8 = 0;
    let mut m1: u8 = 0;
    let mut m2: u8 = 0;
    let mut m3: u8 = 0;

    /* Origin Rust: for (leftover_index, &b) in input[input_index..].iter().enumerate() {
       ... (the byte-by-byte state machine) ... } */
    let mut leftover_index: usize = 0;
    while leftover_index < input.len() - input_index
        invariant
            0 <= (leftover_index as int) <= (input@.len() - input_index),
            bytes == input@,
            input_index <= input@.len(),
            (input@.len() - input_index) <= 4,
            decode_table@.len() == 256,
            ValidDecodeTable(decode_table@),
            (morsels_in_leftover as int) + (padding_bytes_count as int) == (leftover_index as int),
            (morsels_in_leftover as int) + (padding_bytes_count as int) <= 4,
            (padding_bytes_count > 0) ==> ((first_padding_offset as int) < (leftover_index as int)),
            ((morsels_in_leftover as int) >= 1) ==> (m0 <= 63),
            ((morsels_in_leftover as int) <= 0) ==> (m0 == 0),
            ((morsels_in_leftover as int) >= 2) ==> (m1 <= 63),
            ((morsels_in_leftover as int) <= 1) ==> (m1 == 0),
            ((morsels_in_leftover as int) >= 3) ==> (m2 <= 63),
            ((morsels_in_leftover as int) <= 2) ==> (m2 == 0),
            ((morsels_in_leftover as int) >= 4) ==> (m3 <= 63),
            ((morsels_in_leftover as int) <= 3) ==> (m3 == 0),
            (out_idx as int) == (output_index as int),  /* the local mirror untouched (no output writes this early) */
        decreases (input.len() - input_index) - leftover_index
    {
        proof {
            assert((input_index as int) + (leftover_index as int) <= (input@.len() as int));
        }
        let gx = input_index + leftover_index;
        assert(gx as int == (input_index as int) + (leftover_index as int));
        let b = input[gx];
        assert(b == bytes[gx as int]);
        /* Origin Rust: if b == padding.as_u8() { ... }; */
        if b == padding {
            if leftover_index < 2 {
                /* Origin Rust: return Err(DecodeError::InvalidByte(bad_padding_index,
                   b).into()); #2 -- padding at positions 0/1 inside the quad */
                proof {
                    assert((input_index as int) + (leftover_index as int) <= (input@.len() as int));
                }
                return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
                    input_index + leftover_index,
                    b,
                )));
            }
            if padding_bytes_count == 0 {
                first_padding_offset = leftover_index;
            }
            padding_bytes_count += 1;
            leftover_index += 1;
            continue;
        }
        if padding_bytes_count > 0 {
            /* Origin Rust: #1 -- a non-padding byte after padding */
            proof {
                assert((first_padding_offset as int) < (leftover_index as int));
                assert(
                    ((input_index as int) + (leftover_index as int)) <= (input@.len() as int)
                );
                assert(
                    ((input_index as int) + (first_padding_offset as int)) < (input@.len() as int)
                );
            }
            return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
                input_index + first_padding_offset,
                padding,
            )));
        }
        last_symbol = b;
        assert(((b) as int) >= 0 && ((b) as int) < 256);
        assert(decode_table@.len() == 256);
        let morsel = decode_table[b as usize];
        proof {
            assert(morsel == decode_table@[(b) as int]);
            assert(ValidDecodeTable(decode_table@));
        }
        assert(morsel == decode_table@[(b) as int]);
        last_symbol_value = morsel;
        if morsel == INVALID_VALUE {
            /* Origin Rust: invalid morsel -- InvalidByte(offset, b) */
            return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
                input_index + leftover_index,
                b,
            )));
        }
        assert(morsel < 64);
        /* Origin Rust: morsels[morsels_in_leftover] = morsel; (array -> 4 variables) */
        if morsels_in_leftover == 0 {
            m0 = morsel;
        } else if morsels_in_leftover == 1 {
            m1 = morsel;
        } else if morsels_in_leftover == 2 {
            m2 = morsel;
        } else {
            m3 = morsel;
        }
        morsels_in_leftover += 1;
        leftover_index += 1;
    }
    /* Origin Rust:
       if !input.is_empty() && morsels_in_leftover < 2 {
           return Err(DecodeError::InvalidLength(input_index + morsels_in_leftover).into()); } */
    if !input.is_empty() && morsels_in_leftover < 2 {
        proof {
            assert((input_index as int) + (morsels_in_leftover as int) <= (input@.len() as int));
        }
        return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidLength(
            input_index + morsels_in_leftover,
        )));
    }
    /* Origin Rust: match padding_mode { ... } */
    match padding_mode {
        DecodePaddingMode::Indifferent => {}
        DecodePaddingMode::RequireCanonical => {
            if (padding_bytes_count + morsels_in_leftover) % 4 != 0 {
                return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidPadding));
            }
        }
        DecodePaddingMode::RequireNone => {
            if padding_bytes_count > 0 {
                return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidPadding));
            }
        }
    }
    /* Origin Rust:
       let leftover_bytes_to_append = morsels_in_leftover * 6 / 8;
       let mut leftover_num = (u32::from(morsels[0]) << 26) | (u32::from(morsels[1]) << 20)
           | (u32::from(morsels[2]) << 14) | (u32::from(morsels[3]) << 8);
       let mask = !0_u32 >> (leftover_bytes_to_append * 8);
       if !decode_allow_trailing_bits && (leftover_num & mask) != 0 {
           return Err(DecodeError::InvalidLastSymbol { offset: input_index +
               morsels_in_leftover - 1, symbol: last_symbol,
               symbol_value: last_symbol_value }.into()); } */
    proof {
        assert((morsels_in_leftover as int) <= 4);
        assert(((morsels_in_leftover as int) * 6) <= 24);
    }
    /* m_i <= 63 bottom line: the unloaded positions stay 0 */
    assert(m0 <= 63 && m1 <= 63 && m2 <= 63 && m3 <= 63);
    let leftover_bytes_to_append = morsels_in_leftover * 6 / 8;
    assert((leftover_bytes_to_append as int) <= 3);
    let leftover_num: u32 = assembled_leftover_num_u32(m0, m1, m2, m3);
    let mask: u32 = assembled_mask(leftover_bytes_to_append);
    if !decode_allow_trailing_bits && (leftover_num & mask) != 0 {
        proof {
            /* after the InvalidLength check: input non-empty => morsels >= 2;
               empty input => num==0 => (num & mask)==0 (a bit_vector lemma); the branch is unreachable */
            if (input@.len() as int) == 0 {
                assert(m0 == 0 && m1 == 0 && m2 == 0 && m3 == 0);
                assert(leftover_num_model(0, 0, 0, 0) == 0u32) by (bit_vector);
                assert(leftover_num@ == leftover_num_model(m0, m1, m2, m3));
                assert(leftover_num@ == 0);
                assert(leftover_num == 0u32);
                assert((0u32 & mask) == 0u32) by (bit_vector);
                assert((leftover_num & mask) == 0u32);
                assert(false);
            }
            assert((morsels_in_leftover as int) >= 2);
            assert((morsels_in_leftover as int) >= 1);
            assert((input_index as int) + (morsels_in_leftover as int) <= (input@.len() as int));
        }
        return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidLastSymbol {
            offset: ((input_index + morsels_in_leftover) - 1),
            symbol: last_symbol,
            symbol_value: last_symbol_value,
        }));
    }
    /* Origin Rust:
       for _ in 0..leftover_bytes_to_append {
           let hi_byte = (leftover_num >> 24) as u8;
           leftover_num <<= 8;
           *output.get_mut(out_idx).ok_or(DecodeSliceError::OutputSliceTooSmall)?
               = hi_byte;
           out_idx += 1; } */
    proof {
        /* empty input => morsels==0 => the incremental output is 0 (the output loop never enters) */
        if (input@.len() as int) == 0 {
            assert((morsels_in_leftover as int) <= ((input@.len() as int) - (input_index as int)));
            assert((morsels_in_leftover as int) == 0);
            assert((leftover_bytes_to_append as int) == 0);
        }
    }
    let mut appended: usize = 0;
    while appended < leftover_bytes_to_append
        invariant
            0 <= (appended as int) <= (leftover_bytes_to_append as int) <= 3,
            (out_idx as int) == (output_index as int) + (appended as int),
            ((output_index as int) + 4) <= usize::MAX as int,
            input_index <= input@.len(),
            (input@.len() - input_index) <= 4,
            decode_table@.len() == 256,
            ValidDecodeTable(decode_table@),
            output@.len() == old(output)@.len(),
            ((input@.len() as int) - (input_index as int)) >= (morsels_in_leftover as int),
            ((input@.len() as int) == 0) ==> ((leftover_bytes_to_append as int) == 0),
        decreases leftover_bytes_to_append - appended
    {
        assert((appended as int) * 8 <= 24);
        assert((appended as int) * 8 < 32);
        let shift_amt = (8 * appended) as u32;
        let shifted = leftover_num << shift_amt;
        let hi_byte = (shifted >> 24) as u8;
        assert((out_idx as int) + 1 <= usize::MAX as int);
        if out_idx < output.len() {
            output[out_idx] = hi_byte;
        } else {
            return Result::Err(DecodeSliceError::OutputSliceTooSmall);
        }
        out_idx += 1;
        appended += 1;
    }
    /* Origin Rust: Ok(DecodeMetadata::new(out_idx,
       if padding_bytes_count > 0 { Some(input_index + first_padding_offset) } else { None })) */
    Result::Ok(DecodeMetadata {
        decoded_len: out_idx,
        padding_offset: if padding_bytes_count > 0 {
            proof {
                assert((input_index as int) + (first_padding_offset as int) <= (input@.len() as int));
            }
            Option::Some(input_index + first_padding_offset)
        } else {
            Option::None
        },
    })
}

/* ---------- Transcription helpers (bit-composition-equivalent rewrites; the spec side computes directly for the harness) ---------- */

/// Origin Rust: (m0 << 26 | m1 << 20 | m2 << 14 | m3 << 8) as u32
/// int semantics: with m_i <= 63 the bit segments do not overlap, the OR equals the
/// weighted per-segment sum; the expression uses the u32 word shape (isomorphic with exec).
pub open spec fn leftover_num_model(m0: u8, m1: u8, m2: u8, m3: u8) -> u32 {
    ((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14) | ((m3 as u32) << 8)
}

pub exec fn assembled_leftover_num_u32(m0: u8, m1: u8, m2: u8, m3: u8) -> (r: u32)
    requires
        m0 <= 63,
        m1 <= 63,
        m2 <= 63,
        m3 <= 63,
    ensures
        r@ == leftover_num_model(m0, m1, m2, m3),
        r@ >= 0,
        r@ <= 0xFFFFFFFF,
{
    /* Origin Rust: (u32::from(morsels[0]) << 26) | (<< 20) | (<< 14) | (<< 8)
       -- the word-OR shape isomorphic with the model (the bit segments do not overlap) */
    let a = (m0 as u32) << 26;
    let b = (m1 as u32) << 20;
    let c = (m2 as u32) << 14;
    let d = (m3 as u32) << 8;
    let r = (a | b) | c | d;
    r
}

pub open spec fn mask_model(bytes_to_append: int) -> int {
    /* the shift-free arithmetic form of !0_u32 >> (bytes_to_append*8) (bytes_to_append in [0,3]) */
    if bytes_to_append == 0 {
        4294967295
    } else if bytes_to_append == 1 {
        16777215
    } else if bytes_to_append == 2 {
        65535
    } else {
        255
    }
}

pub exec fn assembled_mask(bytes_to_append: usize) -> (r: u32)
    requires bytes_to_append <= 3,
    ensures r@ == mask_model(bytes_to_append as int),
{
    /* Origin Rust: !0_u32 >> (leftover_bytes_to_append * 8)
       -- bytes_to_append is in [0,3] (upstream, because morsels_in_leftover <= 4,
       leftover_bytes_to_append = morsels*6/8 <= 3), rewritten in the equivalent case-constant form */
    let m = if bytes_to_append == 0 {
        0xFFFFFFFFu32
    } else if bytes_to_append == 1 {
        0x00FFFFFFu32
    } else if bytes_to_append == 2 {
        0x0000FFFFu32
    } else {
        0x000000FFu32
    };
    m
}

} // verus!
