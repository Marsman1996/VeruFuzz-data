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
use super::decode::{
    is_invalid_morsel, morsel_pair_hi, morsel_pair_lo, morsel_pair_mid, ValidDecodeTable,
    INVALID_VALUE,
};
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
    Ghost(suff_ok_hyp): Ghost<bool>,
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
        /* the sufficient-Ok hypothesis: when the suffix window takes one of the
           five pinned canonical forms (see the spec fns below), the caller may
           pass Ghost(true) and the Ok exit is established outright */
        suff_ok_hyp ==> suff_ok_shapes_disj(
            input@,
            (input_index as int),
            decode_table@,
            padding,
            padding_mode,
            (output@.len() as int),
            (output_index as int),
        ),
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
        /* no-splash clauses (the harness composition layer of the decode chain):
           writes touch only [output_index, decoded_len); every byte outside stays
           as-is -- below the write base on Ok, above the write base on Ok, and the
           whole slice on Err (all Err exits precede the output loop) */
        r.is_ok() ==> forall|j: int|
            #![trigger final(output)@ [j]] 0 <= j < (output_index as int) ==> (
                final(output)@ [j] == old(output)@ [j]
            ),
        r.is_ok() ==> forall|j: int|
            #![trigger final(output)@ [j]] (((r.get_Ok_0().decoded_len as int) <= j)
                && (j < (old(output)@.len() as int))) ==> (final(output)@ [j] == old(output)@ [j]),
        /* the Err-type exits (all decode errors) return before the first write;
           the Err-kind OutputSliceTooSmall may carry writes made before the
           failing iteration (upstream writes each byte then re-checks) */
        r.is_err() && (r.get_Err_0() != DecodeSliceError::OutputSliceTooSmall) ==> (
            final(output)@ == old(output)@
        ),
        /* S*-shape tail-semantics clauses (the helper domain's 2/3-symbol
           suffixes: the appended byte count identifies the suffix shape --
           one appended byte means two symbols, two means three; the
           appended bytes are the morsel-pair composition of the suffix's
           leading bytes, and the padding_offset face carries the four
           suffix padding shapes: symbols-only, 2+2, 3+1, symbols-only-3) */
        (r.is_ok()
            && (((r.get_Ok_0().decoded_len as int) - (output_index as int)) == 1)) ==> (
            final(output)@[(output_index as int)] == morsel_pair_lo(decode_table@[(input@[(input_index as int)]) as int], decode_table@[(input@[((input_index as int) + 1)]) as int])
            && (input@[(input_index as int)] != padding)
            && (input@[((input_index as int) + 1)] != padding)
            && ((((input_index as int) + 2)) <= (input@.len() as int))
            && (match r.get_Ok_0().padding_offset {
                Option::Some(q) => (
                    (q as int) == ((input_index as int) + 2)
                    && (forall|y: int|
                        #![trigger input@ [y]] ((((input_index as int) + 2) <= y)
                            && (y < (input@.len() as int))) ==> (input@ [y] == padding))),
                Option::None => (((input@.len() as int) - (input_index as int)) == 2),
            })),
        (r.is_ok()
            && (((r.get_Ok_0().decoded_len as int) - (output_index as int)) == 2)) ==> (
            final(output)@[(output_index as int)] == morsel_pair_lo(decode_table@[(input@[(input_index as int)]) as int], decode_table@[(input@[((input_index as int) + 1)]) as int])
            && final(output)@[(output_index as int) + 1]
                == morsel_pair_mid(decode_table@[(input@[((input_index as int) + 1)]) as int], decode_table@[(input@[((input_index as int) + 2)]) as int])
            && (input@[(input_index as int)] != padding)
            && (input@[((input_index as int) + 1)] != padding)
            && (input@[((input_index as int) + 2)] != padding)
            && ((((input_index as int) + 3)) <= (input@.len() as int))
            && (match r.get_Ok_0().padding_offset {
                Option::Some(q) => (
                    (q as int) == ((input_index as int) + 3)
                    && (forall|y: int|
                        #![trigger input@ [y]] ((((input_index as int) + 3) <= y)
                            && (y < (input@.len() as int))) ==> (input@ [y] == padding))),
                Option::None => (((input@.len() as int) - (input_index as int)) == 3),
            })),
        /* the InvalidLastSymbol enumeration (universal over the 2/3-symbol
           suffixes and the padding four-way): the error reports the LAST
           symbol of the suffix run -- its offset is the run's last position,
           the byte there is the reported symbol with its table value,
           everything up to it is a symbol run, everything after it padding */
        (r.is_err()
            && (match r.get_Err_0() {
                DecodeSliceError::DecodeError(DecodeError::InvalidLastSymbol {
                    offset: _,
                    symbol: _,
                    symbol_value: _,
                }) => true,
                _ => false,
            })) ==> (match r.get_Err_0() {
            DecodeSliceError::DecodeError(DecodeError::InvalidLastSymbol {
                offset,
                symbol,
                symbol_value,
            }) => (
                ((input_index as int) + 1 <= (offset as int))
                    && ((offset as int) <= (input_index as int) + 3)
                    && ((offset as int) < (input@.len() as int))
                    && (input@ [offset as int] == symbol)
                    && (input@ [offset as int] != padding)
                    && (symbol_value == decode_table@ [(input@ [offset as int]) as int])
                    && (forall|j: int|
                        #![trigger input@ [j]] ((input_index as int) <= j
                            && j <= (offset as int)) ==> (input@ [j] != padding))
                    && (forall|j: int|
                        #![trigger input@ [j]] (((offset as int) + 1) <= j
                            && j < (input@.len() as int)) ==> (input@ [j] == padding))),
            _ => true,
        }),
        /* the sufficient-Ok faces (the converse direction of the S*-shape
           clauses): each pinned form implies the Ok exit at the exact
           appended length and the exact padding_offset shape -- the
           roundtrip witness consumes these */
        suff_ok_hyp
            && suff_form_2sym_pad2(
                input@,
                (input_index as int),
                decode_table@,
                padding,
                padding_mode,
                (old(output)@.len() as int),
                (output_index as int),
            ) ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == (output_index as int) + 1
            && (match r.get_Ok_0().padding_offset {
                Option::Some(q) => (q as int) == ((input_index as int) + 2),
                Option::None => false,
            }),
        suff_ok_hyp
            && suff_form_2sym(
                input@,
                (input_index as int),
                decode_table@,
                padding,
                padding_mode,
                (old(output)@.len() as int),
                (output_index as int),
            ) ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == (output_index as int) + 1
            && r.get_Ok_0().padding_offset == Option::None,
        suff_ok_hyp
            && suff_form_3sym_pad1(
                input@,
                (input_index as int),
                decode_table@,
                padding,
                padding_mode,
                (old(output)@.len() as int),
                (output_index as int),
            ) ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == (output_index as int) + 2
            && (match r.get_Ok_0().padding_offset {
                Option::Some(q) => (q as int) == ((input_index as int) + 3),
                Option::None => false,
            }),
        suff_ok_hyp
            && suff_form_3sym(
                input@,
                (input_index as int),
                decode_table@,
                padding,
                padding_mode,
                (old(output)@.len() as int),
                (output_index as int),
            ) ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == (output_index as int) + 2
            && r.get_Ok_0().padding_offset == Option::None,
        suff_ok_hyp
            && suff_form_4sym(
                input@,
                (input_index as int),
                decode_table@,
                padding,
                (old(output)@.len() as int),
                (output_index as int),
            ) ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == (output_index as int) + 3
            && r.get_Ok_0().padding_offset == Option::None
            && final(output)@[(output_index as int)] == morsel_pair_lo(
                decode_table@[(input@[(input_index as int)]) as int],
                decode_table@[(input@[((input_index as int) + 1)]) as int],
            )
            && final(output)@[(output_index as int) + 1] == morsel_pair_mid(
                decode_table@[(input@[((input_index as int) + 1)]) as int],
                decode_table@[(input@[((input_index as int) + 2)]) as int],
            )
            && final(output)@[(output_index as int) + 2] == morsel_pair_hi(
                decode_table@[(input@[((input_index as int) + 2)]) as int],
                decode_table@[(input@[((input_index as int) + 3)]) as int],
            ),
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
            ((morsels_in_leftover as int) >= 1) ==> (last_symbol
                == input@[((input_index as int) + (morsels_in_leftover as int)) - 1]),
            ((morsels_in_leftover as int) >= 1) ==> (last_symbol != padding),
            ((morsels_in_leftover as int) >= 1) ==> (last_symbol_value
                == decode_table@[(input@[((input_index as int) + (morsels_in_leftover as int)) - 1]) as int]),
            ((morsels_in_leftover as int) >= 3) ==> (m2 <= 63),
            ((morsels_in_leftover as int) <= 2) ==> (m2 == 0),
            ((morsels_in_leftover as int) >= 4) ==> (m3 <= 63),
            ((morsels_in_leftover as int) <= 3) ==> (m3 == 0),
            /* unconditional positional locks: the first k symbols sit at the
               window's first k positions (a padding byte at position 0/1 exits
               with InvalidByte, so the k-th morsel is always read at ii+k-1) */
            ((morsels_in_leftover as int) >= 1) ==> (m0
                == decode_table@[(input@[(input_index as int)]) as int]),
            ((morsels_in_leftover as int) >= 2) ==> (m1
                == decode_table@[(input@[((input_index as int) + 1)]) as int]),
            ((morsels_in_leftover as int) >= 3) ==> (m2
                == decode_table@[(input@[((input_index as int) + 2)]) as int]),
            ((morsels_in_leftover as int) >= 4) ==> (m3
                == decode_table@[(input@[((input_index as int) + 3)]) as int]),
            (out_idx as int) == (output_index as int),  /* the local mirror untouched (no output writes this early) */
            /* S*-shape run-structure face: everything scanned so far is a
               contiguous symbol run followed by a contiguous padding run;
               the first padding byte always sits at offset >= 2 (an earlier
               padding byte returns InvalidByte instead of reaching here) */
            (padding_bytes_count == 0) ==> (forall|j: int|
                #![trigger input@ [j]] (((input_index as int) <= j)
                    && (j < ((input_index as int) + (leftover_index as int)))) ==> (input@ [j]
                    != padding)),
            (padding_bytes_count > 0) ==> ((morsels_in_leftover as int)
                == (first_padding_offset as int)),
            (padding_bytes_count > 0) ==> ((2 <= (first_padding_offset as int))
                && ((first_padding_offset as int) < (leftover_index as int))
                && (forall|j: int|
                    #![trigger input@ [j]] (((input_index as int) <= j)
                        && (j < ((input_index as int) + (first_padding_offset as int)))) ==> (input@ [j]
                        != padding))
                && (forall|j: int|
                    #![trigger input@ [j]]
                    ((((input_index as int) + (first_padding_offset as int)) <= j)
                        && (j < ((input_index as int) + (leftover_index as int)))) ==> (input@ [j]
                        == padding))),
            /* the S*-shape position locks: each morsel equals the decode
               table value at the window's next non-padding position (miss
               form while the run is not yet complete, hit form once seen);
               morsels beyond the third carry no lock */
            ((morsels_in_leftover as int) == 0) ==> (fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding) == ((input_index as int) + (leftover_index as int))),
            ((morsels_in_leftover as int) >= 1) ==> (fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding) < ((input_index as int) + (leftover_index as int))),
            ((morsels_in_leftover as int) >= 1) ==> (m0 == decode_table@[(input@[fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding)]) as int]),
            ((morsels_in_leftover as int) == 1) ==> (nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding) == ((input_index as int) + (leftover_index as int))),
            ((morsels_in_leftover as int) >= 2) ==> (nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding) < ((input_index as int) + (leftover_index as int))),
            ((morsels_in_leftover as int) >= 2) ==> (m1 == decode_table@[(input@[nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding)]) as int]),
            ((morsels_in_leftover as int) == 2) ==> (nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding) == ((input_index as int) + (leftover_index as int))),
            ((morsels_in_leftover as int) >= 3) ==> (nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding) < ((input_index as int) + (leftover_index as int))),
            ((morsels_in_leftover as int) >= 3) ==> (m2 == decode_table@[(input@[nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding)]) as int]),
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
            proof {
                /* S*-shape lock maintenance under a padding byte: the
                   positions found so far stay put; a still-missing scan
                   keeps missing over the extended window */
                assert((gx as int) == (input_index as int) + (leftover_index as int));
                if morsels_in_leftover == 0 {
                    fnp_miss_extend(input@, (input_index as int), (gx as int), padding);
                } else if morsels_in_leftover == 1 {
                    fnp_stable(input@, (input_index as int), (gx as int), padding);
                    nnp_miss_extend(input@, (input_index as int), (gx as int), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding);
                } else if morsels_in_leftover == 2 {
                    fnp_stable(input@, (input_index as int), (gx as int), padding);
                    nnp_stable(input@, (input_index as int), (gx as int), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding);
                    nnp_miss_extend(input@, (input_index as int), (gx as int), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding);
                } else {
                    fnp_stable(input@, (input_index as int), (gx as int), padding);
                    nnp_stable(input@, (input_index as int), (gx as int), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding);
                    nnp_stable(input@, (input_index as int), (gx as int), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding);
                }
            }
            proof {
                if padding_bytes_count == 0 {
                    assert((morsels_in_leftover as int) == (leftover_index as int));
                }
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
        proof {
            /* the last-symbol trackers point at the just-seen symbol */
            assert(b == input@[((input_index as int) + (leftover_index as int))]);
        }
        if morsel == INVALID_VALUE {
            /* Origin Rust: invalid morsel -- InvalidByte(offset, b) */
            return Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
                input_index + leftover_index,
                b,
            )));
        }
        assert(morsel < 64);
        proof {
            /* S*-shape lock maintenance (the pre-window is [ii, li), the new
               symbol sits at gx == ii + li, the extended window ends at
               gx + 1); the morsel equals the table value at the new window's
               next non-padding position */
            assert((gx as int) == (input_index as int) + (leftover_index as int));
            if morsels_in_leftover == 0 {
                fnp_miss(input@, (input_index as int), (gx as int), padding);
                fnp_extend(input@, (input_index as int), (gx as int), padding);
                nnp_end_miss(input@, (input_index as int), (gx as int) + 1, (gx as int), padding);
            } else if morsels_in_leftover == 1 {
                fnp_stable(input@, (input_index as int), (gx as int), padding);
                nnp_extend(input@, (input_index as int), (gx as int), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding);
                nnp_end_miss(input@, (input_index as int), (gx as int) + 1, (gx as int), padding);
            } else if morsels_in_leftover == 2 {
                fnp_stable(input@, (input_index as int), (gx as int), padding);
                nnp_stable(input@, (input_index as int), (gx as int), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding);
                nnp_extend(input@, (input_index as int), (gx as int), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding);
                nnp_end_miss(input@, (input_index as int), (gx as int) + 1, (gx as int), padding);
            } else {
                /* the fourth symbol carries no lock; keep the run-structure
                   faces: the tracked positions of the earlier locks stay put */
                fnp_stable(input@, (input_index as int), (gx as int), padding);
                nnp_stable(input@, (input_index as int), (gx as int), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding);
                nnp_stable(input@, (input_index as int), (gx as int), nnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), fnp(input@, (input_index as int), ((input_index as int) + (leftover_index as int)), padding), padding), padding);
            }
        }
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
    /* the sufficient-Ok shape dispatch: under the hypothesis, the pins and the
       run structure pin the exact morsel/padding split of the window. The case
       conditions are the pins themselves, so the escaping implications serve the
       InvalidLength / padding-mode exits, the trailing-bits kill and the
       padding_offset face below. */
    proof {
        if suff_ok_hyp {
            let LEN = (input@.len() as int);
            let II = (input_index as int);
            assert((leftover_index as int) == LEN - II);
            assert((morsels_in_leftover as int) + (padding_bytes_count as int) == LEN - II);
            if (LEN - II) == 2 {
                /* the bare two-symbol form: the run structure forbids padding */
                if padding_bytes_count > 0 {
                    assert((first_padding_offset as int) >= 2);
                    assert((leftover_index as int) == 2);
                    assert(false);
                }
                assert((morsels_in_leftover as int) == 2);
            } else if (LEN - II) == 3 {
                /* the bare three-symbol form: a padding byte would sit inside the
                   pinned symbol positions */
                if padding_bytes_count > 0 {
                    assert((first_padding_offset as int) == 2);
                    assert(input@[II + 2] == padding);
                    assert(input@[II + 2] != padding);
                    assert(false);
                }
                assert((morsels_in_leftover as int) == 3);
            } else {
                /* (LEN - II) == 4: the mid-window pins give the split */
                assert((LEN - II) == 4);
                if input@[II + 2] == padding {
                    /* 2sym+2pad: count >= 1 (otherwise the run covers the pinned
                       padding positions) and fpo == 2 (fpo == 3 would force a
                       symbol at II+2) */
                    if padding_bytes_count == 0 {
                        assert(input@[II + 2] != padding);
                        assert(false);
                    }
                    assert((first_padding_offset as int) >= 2);
                    assert((leftover_index as int) == 4);
                    if (first_padding_offset as int) == 3 {
                        assert(input@[II + 2] != padding);
                        assert(false);
                    }
                    assert((first_padding_offset as int) == 2);
                    assert((morsels_in_leftover as int) == 2);
                    assert((padding_bytes_count as int) == 2);
                } else {
                    assert(input@[II + 2] != padding);
                    if input@[II + 3] == padding {
                        /* 3sym+1pad */
                        assert((first_padding_offset as int) >= 2);
                        if (first_padding_offset as int) == 2 {
                            assert(input@[II + 2] == padding);
                            assert(false);
                        }
                        assert((first_padding_offset as int) == 3);
                        assert((morsels_in_leftover as int) == 3);
                        assert((padding_bytes_count as int) == 1);
                    } else {
                        /* 4sym: no padding position exists */
                        if padding_bytes_count > 0 {
                            assert((2 <= (first_padding_offset as int))
                                && ((first_padding_offset as int) < 4));
                            assert(input@[II + (first_padding_offset as int)] == padding);
                            assert(false);
                        }
                        assert((morsels_in_leftover as int) == 4);
                    }
                }
            }
        }
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
            /* the InvalidLastSymbol enumeration flatten: the last-seen symbol
               sits exactly at the reported offset, everything up to it is a
               symbol run, everything after it is padding */
            assert(last_symbol
                == input@[((input_index as int) + (morsels_in_leftover as int)) - 1]);
            assert((((input_index as int) + (morsels_in_leftover as int)) - 1)
                < (input@.len() as int));
            assert(last_symbol_value
                == decode_table@[(input@[((input_index as int) + (morsels_in_leftover as int)) - 1]) as int]);
            let last_pos = ((input_index as int) + (morsels_in_leftover as int)) - 1;
            assert(forall|j: int|
                #![trigger input@ [j]] (((input_index as int) <= j)
                    && (j <= last_pos)) ==> (input@ [j] != padding));
            assert(forall|j: int|
                #![trigger input@ [j]] (((last_pos + 1) <= j)
                    && (j < (input@.len() as int))) ==> (input@ [j] == padding));
            /* the sufficient-Ok falsification: each pinned form's low-bits
               hypothesis kills the guard, so this exit is unreachable under the
               hypothesis (the per-bit argument is stated over the full 4-term
               shift chain; the reduced chains need bit-blasting and are proven
               only as part of the by (bit_vector) kills) */
            if suff_ok_hyp {
                assert((leftover_bytes_to_append as int)
                    == (morsels_in_leftover as int) * 6 / 8);
                if (morsels_in_leftover as int) == 2 {
                    assert(m2 == 0 && m3 == 0);
                    assert((leftover_bytes_to_append as int) == 1);
                    assert(mask@ == mask_model(1));
                    assert(mask == 0x00FFFFFFu32);
                    /* the second symbol's table value carries zero low bits
                       (the positional lock joins the form's pin by congruence) */
                    assert(m1 == decode_table@[(input@[((input_index as int) + 1)]) as int]);
                    assert((decode_table@[(input@[((input_index as int) + 1)]) as int] & 15)
                        == 0);
                    assert((m1 & 15) == 0);
                    assert(leftover_num@ == leftover_num_model(m0, m1, m2, m3));
                    assert(leftover_num
                        == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14)
                            | ((m3 as u32) << 8)));
                    assert((leftover_num & mask) == 0u32) by (bit_vector)
                        requires
                            m0 < 64,
                            m1 < 64,
                            m2 == 0u8,
                            m3 == 0u8,
                            (m1 & 15) == 0,
                            mask == 0x00FFFFFFu32,
                            leftover_num
                                == (((m0 as u32) << 26) | ((m1 as u32) << 20)
                                    | ((m2 as u32) << 14) | ((m3 as u32) << 8));
                    assert(false);
                } else if (morsels_in_leftover as int) == 3 {
                    assert(m3 == 0);
                    assert((leftover_bytes_to_append as int) == 2);
                    assert(mask@ == mask_model(2));
                    assert(mask == 0x0000FFFFu32);
                    /* the third symbol's table value carries zero low bits */
                    assert(m2 == decode_table@[(input@[((input_index as int) + 2)]) as int]);
                    assert((decode_table@[(input@[((input_index as int) + 2)]) as int] & 3)
                        == 0);
                    assert((m2 & 3) == 0);
                    assert(leftover_num@ == leftover_num_model(m0, m1, m2, m3));
                    assert(leftover_num
                        == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14)
                            | ((m3 as u32) << 8)));
                    assert((leftover_num & mask) == 0u32) by (bit_vector)
                        requires
                            m0 < 64,
                            m1 < 64,
                            m2 < 64,
                            m3 == 0u8,
                            (m2 & 3) == 0,
                            mask == 0x0000FFFFu32,
                            leftover_num
                                == (((m0 as u32) << 26) | ((m1 as u32) << 20)
                                    | ((m2 as u32) << 14) | ((m3 as u32) << 8));
                    assert(false);
                } else {
                    /* four symbols: the assembled word leaves nothing below the cut */
                    assert((morsels_in_leftover as int) == 4);
                    assert((leftover_bytes_to_append as int) == 3);
                    assert(mask@ == mask_model(3));
                    assert(mask == 0x000000FFu32);
                    assert(leftover_num@ == leftover_num_model(m0, m1, m2, m3));
                    assert(leftover_num
                        == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14)
                            | ((m3 as u32) << 8)));
                    assert((leftover_num & mask) == 0u32) by (bit_vector)
                        requires
                            m0 < 64,
                            m1 < 64,
                            m2 < 64,
                            m3 < 64,
                            mask == 0x000000FFu32,
                            leftover_num
                                == (((m0 as u32) << 26) | ((m1 as u32) << 20)
                                    | ((m2 as u32) << 14) | ((m3 as u32) << 8));
                    assert(false);
                }
            }
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
    let ghost g_out_old = old(output)@;
    let ghost bv_num_ghost: u32 = ((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14) | ((m3 as u32) << 8);
    while appended < leftover_bytes_to_append
        invariant
            0 <= (appended as int) <= (leftover_bytes_to_append as int) <= 3,
            g_out_old == old(output)@,
            (out_idx as int) == (output_index as int) + (appended as int),
            forall|j: int|
                #![trigger output@ [j]] 0 <= j < (output_index as int) ==> (output@ [j]
                    == g_out_old [j]),
            forall|j: int|
                #![trigger output@ [j]] (((out_idx as int) <= j)
                    && (j < (output@.len() as int))) ==> (output@ [j] == g_out_old [j]),
            ((output_index as int) + 4) <= usize::MAX as int,
            input_index <= input@.len(),
            (input@.len() - input_index) <= 4,
            decode_table@.len() == 256,
            ValidDecodeTable(decode_table@),
            output@.len() == old(output)@.len(),
            ((input@.len() as int) - (input_index as int)) >= (morsels_in_leftover as int),
            ((input@.len() as int) == 0) ==> ((leftover_bytes_to_append as int) == 0),
            /* carry the assembled composition through the loop (loop-body
               queries restate their enabling facts in the invariant list) */
            m0 <= 63,
            m1 <= 63,
            m2 <= 63,
            m3 <= 63,
            leftover_num@ == leftover_num_model(m0, m1, m2, m3),
            bv_num_ghost@ == leftover_num_model(m0, m1, m2, m3),
            bv_num_ghost == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14) | ((m3 as u32) << 8)),
            leftover_num == bv_num_ghost,
            /* the positional locks persist through the write loop (the morsels
               never change here); together with the byte-value locks below they
               carry the 4sym form's value face at the function end */
            ((morsels_in_leftover as int) >= 1) ==> (m0
                == decode_table@[(input@[(input_index as int)]) as int]),
            ((morsels_in_leftover as int) >= 2) ==> (m1
                == decode_table@[(input@[((input_index as int) + 1)]) as int]),
            ((morsels_in_leftover as int) >= 3) ==> (m2
                == decode_table@[(input@[((input_index as int) + 2)]) as int]),
            ((morsels_in_leftover as int) >= 4) ==> (m3
                == decode_table@[(input@[((input_index as int) + 3)]) as int]),
            /* the sufficient-Ok dispatch (aggregate form: under the hypothesis
               the morsel count is 2/3/4 with its appended region and its form's
               output room; the single disjunction lets the write-loop body
               falsify the OutputSliceTooSmall exit) */
            suff_ok_hyp
                ==> (((morsels_in_leftover as int) == 2)
                    && ((leftover_bytes_to_append as int) == 1)
                    && ((output@.len() as int) >= (output_index as int) + 1)
                    || ((morsels_in_leftover as int) == 3)
                        && ((leftover_bytes_to_append as int) == 2)
                        && ((output@.len() as int) >= (output_index as int) + 2)
                    || ((morsels_in_leftover as int) == 4)
                        && ((leftover_bytes_to_append as int) == 3)
                        && ((output@.len() as int) >= (output_index as int) + 3)),
            /* S*-shape byte-value locks: the appended bytes are the morsel-pair
               composition of the morsels (the k-th byte takes bits from the
               k-th and (k+1)-th morsels) */
            ((appended as int) == 1) ==> (output@[(output_index as int)]
                == morsel_pair_lo(m0, m1)),
            ((appended as int) == 2) ==> (output@[(output_index as int)]
                == morsel_pair_lo(m0, m1)
                && output@[(output_index as int) + 1]
                    == morsel_pair_mid(m1, m2)),
            ((appended as int) == 3) ==> (output@[(output_index as int)]
                == morsel_pair_lo(m0, m1)
                && output@[(output_index as int) + 1]
                    == morsel_pair_mid(m1, m2)
                && output@[(output_index as int) + 2]
                    == morsel_pair_hi(m2, m3)),
        decreases leftover_bytes_to_append - appended
    {
        assert((appended as int) * 8 <= 24);
        assert((appended as int) * 8 < 32);
        let shift_amt = (8 * appended) as u32;
        let shifted = leftover_num << shift_amt;
        let hi_byte = (shifted >> 24) as u8;
        proof {
            /* the byte-value locks: each face's enabling facts (morsel bounds,
               the assembled-word equalities) ride in the invariant list; the
               bit-vector layer proves the bit identities from the machine
               definitions carried in the requires */
            if appended == 0 {
                assert(hi_byte == morsel_pair_lo(m0, m1)) by (bit_vector)
                    requires
                        m0 < 64,
                        m1 < 64,
                        m2 < 64,
                        m3 < 64,
                        shift_amt == 0,
                        hi_byte == ((shifted >> 24) as u8),
                        shifted == (leftover_num << shift_amt),
                        leftover_num == bv_num_ghost,
                        bv_num_ghost == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14) | ((m3 as u32) << 8));
            } else if appended == 1 {
                assert(hi_byte == morsel_pair_mid(m1, m2)) by (bit_vector)
                    requires
                        m0 < 64,
                        m1 < 64,
                        m2 < 64,
                        m3 < 64,
                        shift_amt == 8,
                        hi_byte == ((shifted >> 24) as u8),
                        shifted == (leftover_num << shift_amt),
                        leftover_num == bv_num_ghost,
                        bv_num_ghost == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14) | ((m3 as u32) << 8));
            } else {
                assert(hi_byte == morsel_pair_hi(m2, m3)) by (bit_vector)
                    requires
                        m0 < 64,
                        m1 < 64,
                        m2 < 64,
                        m3 < 64,
                        shift_amt == 16,
                        hi_byte == ((shifted >> 24) as u8),
                        shifted == (leftover_num << shift_amt),
                        leftover_num == bv_num_ghost,
                        bv_num_ghost == (((m0 as u32) << 26) | ((m1 as u32) << 20) | ((m2 as u32) << 14) | ((m3 as u32) << 8));
            }
        }
        assert((out_idx as int) + 1 <= usize::MAX as int);
        if out_idx < output.len() {
            output[out_idx] = hi_byte;
        } else {
            return Result::Err(DecodeSliceError::OutputSliceTooSmall);
        }
        out_idx += 1;
        appended += 1;
    }
    /* The S*-shape flatten of the tail-semantics clauses: the full window's
       positions and the run structure follow from the loop invariants; the
       appended bytes come from the write loop's byte-value locks. */
    if leftover_bytes_to_append == 1 {
        proof {
            assert((morsels_in_leftover as int) == 2);
            assert(((input_index as int) + (leftover_index as int)) == (input@.len() as int));
            let LEN = (input@.len() as int);
            assert(((input_index as int)) < LEN);
            /* the leading two bytes are symbols */
            if padding_bytes_count == 0 {
                assert((leftover_index as int) >= 2);
            } else {
                assert((first_padding_offset as int) >= 2);
            }
            /* the first scan hits at the base; the second one right after */
            assert(input@[(input_index as int)] != padding);
            assert(input@[((input_index as int) + 1)] != padding);
            fnp_step(input@, (input_index as int), LEN, padding);
            assert(fnp(input@, (input_index as int), LEN, padding) == (input_index as int));
            assert(nnp(input@, (input_index as int), LEN, (input_index as int), padding)
                == nnp(input@, ((input_index as int) + 1), LEN, (input_index as int), padding));
            nnp_step(input@, ((input_index as int) + 1), LEN, (input_index as int), padding);
            assert(nnp(input@, (input_index as int), LEN, (input_index as int), padding) == ((input_index as int) + 1));
            /* morsels equal the table values at the flat positions */
            assert(((input_index as int) + (leftover_index as int)) == LEN);
            assert(m0 == decode_table@[(input@[(input_index as int)]) as int]);
            assert(m1 == decode_table@[(input@[((input_index as int) + 1)]) as int]);
            /* the appended byte face and the four-way padding shape */
            assert(final(output)@[(output_index as int)] == morsel_pair_lo(m0, m1));
            if padding_bytes_count > 0 {
                assert((first_padding_offset as int) == 2);
            }
            assert(forall|y: int|
                #![trigger input@ [y]] ((((input_index as int) + 2) <= y)
                    && (y < (input@.len() as int))) ==> (input@ [y] == padding));
        }
    } else if leftover_bytes_to_append == 2 {
        proof {
            assert((morsels_in_leftover as int) == 3);
            assert(((input_index as int) + (leftover_index as int)) == (input@.len() as int));
            let LEN = (input@.len() as int);
            assert(((input_index as int)) < LEN);
            if padding_bytes_count == 0 {
                assert((leftover_index as int) >= 3);
            } else {
                assert((first_padding_offset as int) >= 3);
            }
            assert(input@[(input_index as int)] != padding);
            assert(input@[((input_index as int) + 1)] != padding);
            assert(input@[((input_index as int) + 2)] != padding);
            fnp_step(input@, (input_index as int), LEN, padding);
            assert(fnp(input@, (input_index as int), LEN, padding) == (input_index as int));
            assert(nnp(input@, (input_index as int), LEN, (input_index as int), padding)
                == nnp(input@, ((input_index as int) + 1), LEN, (input_index as int), padding));
            nnp_step(input@, ((input_index as int) + 1), LEN, (input_index as int), padding);
            assert(nnp(input@, (input_index as int), LEN, (input_index as int), padding) == ((input_index as int) + 1));
            assert(nnp(input@, ((input_index as int) + 1), LEN, ((input_index as int) + 1), padding)
                == nnp(input@, ((input_index as int) + 2), LEN, ((input_index as int) + 1), padding));
            nnp_step(input@, ((input_index as int) + 2), LEN, ((input_index as int) + 1), padding);
            assert(nnp(input@, ((input_index as int) + 1), LEN, ((input_index as int) + 1), padding)
                == ((input_index as int) + 2));
            assert(((input_index as int) + (leftover_index as int)) == LEN);
            assert(m0 == decode_table@[(input@[(input_index as int)]) as int]);
            assert(m1 == decode_table@[(input@[((input_index as int) + 1)]) as int]);
            assert(m2 == decode_table@[(input@[((input_index as int) + 2)]) as int]);
            assert(final(output)@[(output_index as int)] == morsel_pair_lo(m0, m1));
            assert(final(output)@[(output_index as int) + 1]
                == morsel_pair_mid(m1, m2));
            if padding_bytes_count > 0 {
                assert((first_padding_offset as int) == 3);
            }
            assert(forall|y: int|
                #![trigger input@ [y]] ((((input_index as int) + 3) <= y)
                    && (y < (input@.len() as int))) ==> (input@ [y] == padding));
        }
    }
    let rv: Result<DecodeMetadata, DecodeSliceError> = Result::Ok(DecodeMetadata {
        decoded_len: out_idx,
        padding_offset: if padding_bytes_count > 0 {
            proof {
                assert((input_index as int) + (first_padding_offset as int) <= (input@.len() as int));
            }
            Option::Some(input_index + first_padding_offset)
        } else {
            Option::None
        },
    });
    proof {
        /* the result-shape map for the S*-shape clauses' padding face */
        if padding_bytes_count > 0 {
            assert(rv.get_Ok_0().padding_offset
                == Option::Some((input_index + first_padding_offset) as usize));
            assert((rv.get_Ok_0().padding_offset.get_Some_0() as int)
                == ((input_index as int) + (first_padding_offset as int)));
        } else {
            assert(rv.get_Ok_0().padding_offset == Option::None);
        }
        assert((rv.get_Ok_0().decoded_len as int)
            == ((output_index as int) + (leftover_bytes_to_append as int)));
    }
    rv
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

/* ============================================================
 * Sufficient-Ok suffix forms: the pinned shapes under which decode_suffix
 * returns Ok outright (the ghost hypothesis parameter carries them). Each
 * form pins the suffix window's symbol/padding layout, the validity and
 * the trailing-bits condition of the symbol table values, the compatible
 * padding modes, and the output room for the appended region. Together
 * with the S*-shape clauses (the value half) these forms give the full
 * Ok-establishment converse.
 * ============================================================ */

/// the 2-symbol + 2-padding canonical form (e.g. "QQ==")
pub open spec fn suff_form_2sym_pad2(
    s: Seq<u8>,
    ii: int,
    t: Seq<u8>,
    pad: u8,
    m: DecodePaddingMode,
    out_len: int,
    oi: int,
) -> bool {
    s.len() - ii == 4
        && s[ii] != pad
        && s[ii + 1] != pad
        && !is_invalid_morsel(t[s[ii] as int])
        && !is_invalid_morsel(t[s[ii + 1] as int])
        && (t[s[ii + 1] as int] & 15) == 0
        && s[ii + 2] == pad
        && s[ii + 3] == pad
        && (m == DecodePaddingMode::Indifferent || m == DecodePaddingMode::RequireCanonical)
        && out_len >= oi + 1
}

/// the bare 2-symbol form (an unpadded final partial quad)
pub open spec fn suff_form_2sym(
    s: Seq<u8>,
    ii: int,
    t: Seq<u8>,
    pad: u8,
    m: DecodePaddingMode,
    out_len: int,
    oi: int,
) -> bool {
    s.len() - ii == 2
        && s[ii] != pad
        && s[ii + 1] != pad
        && !is_invalid_morsel(t[s[ii] as int])
        && !is_invalid_morsel(t[s[ii + 1] as int])
        && (t[s[ii + 1] as int] & 15) == 0
        && (m == DecodePaddingMode::Indifferent || m == DecodePaddingMode::RequireNone)
        && out_len >= oi + 1
}

/// the 3-symbol + 1-padding canonical form (e.g. "QUR=")
pub open spec fn suff_form_3sym_pad1(
    s: Seq<u8>,
    ii: int,
    t: Seq<u8>,
    pad: u8,
    m: DecodePaddingMode,
    out_len: int,
    oi: int,
) -> bool {
    s.len() - ii == 4
        && s[ii] != pad
        && s[ii + 1] != pad
        && s[ii + 2] != pad
        && !is_invalid_morsel(t[s[ii] as int])
        && !is_invalid_morsel(t[s[ii + 1] as int])
        && !is_invalid_morsel(t[s[ii + 2] as int])
        && (t[s[ii + 2] as int] & 3) == 0
        && s[ii + 3] == pad
        && (m == DecodePaddingMode::Indifferent || m == DecodePaddingMode::RequireCanonical)
        && out_len >= oi + 2
}

/// the bare 3-symbol form (an unpadded final partial quad)
pub open spec fn suff_form_3sym(
    s: Seq<u8>,
    ii: int,
    t: Seq<u8>,
    pad: u8,
    m: DecodePaddingMode,
    out_len: int,
    oi: int,
) -> bool {
    s.len() - ii == 3
        && s[ii] != pad
        && s[ii + 1] != pad
        && s[ii + 2] != pad
        && !is_invalid_morsel(t[s[ii] as int])
        && !is_invalid_morsel(t[s[ii + 1] as int])
        && !is_invalid_morsel(t[s[ii + 2] as int])
        && (t[s[ii + 2] as int] & 3) == 0
        && (m == DecodePaddingMode::Indifferent || m == DecodePaddingMode::RequireNone)
        && out_len >= oi + 2
}

/// the full-quad 4-symbol form (e.g. a complete final quad; no trailing-bits
/// condition is needed -- the assembled word leaves no ragged bits)
pub open spec fn suff_form_4sym(
    s: Seq<u8>,
    ii: int,
    t: Seq<u8>,
    pad: u8,
    out_len: int,
    oi: int,
) -> bool {
    s.len() - ii == 4
        && s[ii] != pad
        && s[ii + 1] != pad
        && s[ii + 2] != pad
        && s[ii + 3] != pad
        && !is_invalid_morsel(t[s[ii] as int])
        && !is_invalid_morsel(t[s[ii + 1] as int])
        && !is_invalid_morsel(t[s[ii + 2] as int])
        && !is_invalid_morsel(t[s[ii + 3] as int])
        && out_len >= oi + 3
}

/// the five-form disjunction the ghost hypothesis gates
pub open spec fn suff_ok_shapes_disj(
    s: Seq<u8>,
    ii: int,
    t: Seq<u8>,
    pad: u8,
    m: DecodePaddingMode,
    out_len: int,
    oi: int,
) -> bool {
    suff_form_2sym_pad2(s, ii, t, pad, m, out_len, oi)
        || suff_form_2sym(s, ii, t, pad, m, out_len, oi)
        || suff_form_3sym_pad1(s, ii, t, pad, m, out_len, oi)
        || suff_form_3sym(s, ii, t, pad, m, out_len, oi)
        || suff_form_4sym(s, ii, t, pad, out_len, oi)
}

/* ============================================================
 * S*-shape position-scan family (spec-side positions for the suffix's
 * non-padding bytes; two scans: the first non-padding position, then the
 * next one after a given position). The lemma set carries the scan algebra:
 * range bounds, hit/miss characterizations, window-stability, and the
 * hit/miss extension lemmas over window-extension by a single byte.
 * ============================================================ */

/// the first y in [lo, hi) with s[y] != pad; hi when none
pub open spec fn fnp(s: Seq<u8>, lo: int, hi: int, pad: u8) -> int
    decreases hi - lo
{
    if lo >= hi {
        hi
    } else if s[lo] != pad {
        lo
    } else {
        fnp(s, lo + 1, hi, pad)
    }
}

/// the first y in [lo, hi) with s[y] != pad and y > p; hi when none
pub open spec fn nnp(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8) -> int
    decreases hi - lo
{
    if lo >= hi {
        hi
    } else if s[lo] != pad && lo > p {
        lo
    } else {
        nnp(s, lo + 1, hi, p, pad)
    }
}

/// both scans land inside [lo, hi]
pub proof fn fnp_range(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires 0 <= lo <= hi <= s.len(),
    ensures lo <= fnp(s, lo, hi, pad) <= hi,
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        fnp_range(s, lo + 1, hi, pad);
    }
}

pub proof fn nnp_range(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires 0 <= lo <= hi <= s.len(),
    ensures lo <= nnp(s, lo, hi, p, pad) <= hi,
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        nnp_range(s, lo + 1, hi, p, pad);
    }
}

/// hit: below hi means a non-padding symbol with a padding prefix
pub proof fn fnp_hit(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires 0 <= lo <= hi <= s.len(),
    ensures fnp(s, lo, hi, pad) < hi ==> (s[fnp(s, lo, hi, pad)] != pad
        && (forall|y: int|
            #![trigger s[y]] lo <= y < fnp(s, lo, hi, pad) ==> s[y] == pad)),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        fnp_hit(s, lo + 1, hi, pad);
    }
}

/// miss: reaching hi means the whole window is padding
pub proof fn fnp_miss(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires 0 <= lo <= hi <= s.len(),
    ensures fnp(s, lo, hi, pad) == hi ==> (forall|y: int|
        #![trigger s[y]] lo <= y < hi ==> s[y] == pad),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        fnp_miss(s, lo + 1, hi, pad);
    }
}

/// hit for the second scan (scoped from the scan base lo, not from p)
pub proof fn nnp_hit(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires 0 <= lo <= hi <= s.len(), p < hi,
    ensures nnp(s, lo, hi, p, pad) < hi ==> (s[nnp(s, lo, hi, p, pad)] != pad
        && nnp(s, lo, hi, p, pad) > p
        && (forall|y: int|
            #![trigger s[y]] (lo <= y < nnp(s, lo, hi, p, pad) && y > p) ==> s[y]
                == pad)),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        nnp_hit(s, lo + 1, hi, p, pad);
    }
}

/// miss for the second scan (window-restricted, as above)
pub proof fn nnp_miss(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires 0 <= lo <= hi <= s.len(),
    ensures nnp(s, lo, hi, p, pad) == hi ==> (forall|y: int|
        #![trigger s[y]] (lo <= y < hi && y > p) ==> s[y] == pad),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        nnp_miss(s, lo + 1, hi, p, pad);
    }
}

/// window extension leaves an already-found position unchanged
pub proof fn fnp_stable(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires
        0 <= lo <= hi < s.len(),
        fnp(s, lo, hi, pad) < hi,
    ensures fnp(s, lo, hi + 1, pad) == fnp(s, lo, hi, pad),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        fnp_range(s, lo + 1, hi, pad);
        if fnp(s, lo, hi, pad) == lo {
            assert(s[lo] != pad);
            assert(fnp(s, lo, hi + 1, pad) == lo);
        } else {
            assert(s[lo] == pad);
            fnp_stable(s, lo + 1, hi, pad);
            assert(fnp(s, lo + 1, hi + 1, pad) == fnp(s, lo + 1, hi, pad));
            assert(fnp(s, lo, hi + 1, pad) == fnp(s, lo + 1, hi + 1, pad));
            assert(fnp(s, lo, hi, pad) == fnp(s, lo + 1, hi, pad));
        }
    }
}

pub proof fn nnp_stable(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires
        0 <= lo <= hi < s.len(),
        p < hi,
        nnp(s, lo, hi, p, pad) < hi,
    ensures nnp(s, lo, hi + 1, p, pad) == nnp(s, lo, hi, p, pad),
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        nnp_range(s, lo + 1, hi, p, pad);
        if nnp(s, lo, hi, p, pad) == lo {
            assert(s[lo] != pad && lo > p);
            assert(nnp(s, lo, hi + 1, p, pad) == lo);
        } else {
            assert(s[lo] == pad || lo <= p);
            nnp_stable(s, lo + 1, hi, p, pad);
            assert(nnp(s, lo + 1, hi + 1, p, pad) == nnp(s, lo + 1, hi, p, pad));
            assert(nnp(s, lo, hi + 1, p, pad) == nnp(s, lo + 1, hi + 1, p, pad));
            assert(nnp(s, lo, hi, p, pad) == nnp(s, lo + 1, hi, p, pad));
        }
    }
}

/// one definitional step (default fuel allows a single unfolding)
pub proof fn fnp_step(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires 0 <= lo < hi <= s.len(),
    ensures fnp(s, lo, hi, pad) == (if s[lo] != pad { lo } else { fnp(s, lo + 1, hi, pad) }),
{
}

pub proof fn fnp_base(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires lo >= hi,
    ensures fnp(s, lo, hi, pad) == hi,
{
}

pub proof fn nnp_step(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires 0 <= lo < hi <= s.len(),
    ensures nnp(s, lo, hi, p, pad) == (if s[lo] != pad && lo > p { lo } else { nnp(s, lo + 1, hi, p, pad) }),
{
}

pub proof fn nnp_base(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires lo >= hi,
    ensures nnp(s, lo, hi, p, pad) == hi,
{
}

/// hit-at-append: an all-padding window whose next byte is a symbol
pub proof fn fnp_extend(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires
        0 <= lo <= hi < s.len(),
        fnp(s, lo, hi, pad) == hi,
        s[hi] != pad,
    ensures
        fnp(s, lo, hi + 1, pad) == hi,
    decreases hi - lo,
{
    if lo == hi {
    } else {
        assert(s[lo] == pad);
        fnp_extend(s, lo + 1, hi, pad);
    }
}

pub proof fn nnp_extend(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires
        0 <= lo <= hi < s.len(),
        p < hi,
        nnp(s, lo, hi, p, pad) == hi,
        s[hi] != pad,
        hi > p,
    ensures
        nnp(s, lo, hi + 1, p, pad) == hi,
    decreases hi - lo,
{
    if lo == hi {
    } else {
        assert(s[lo] == pad || lo <= p);
        nnp_extend(s, lo + 1, hi, p, pad);
    }
}

/// miss-at-append: appending more padding keeps the miss
pub proof fn fnp_miss_extend(s: Seq<u8>, lo: int, hi: int, pad: u8)
    requires
        0 <= lo <= hi < s.len(),
        fnp(s, lo, hi, pad) == hi,
        s[hi] == pad,
    ensures
        fnp(s, lo, hi + 1, pad) == hi + 1,
    decreases hi - lo,
{
    if lo == hi {
        fnp_step(s, lo, hi + 1, pad);
        fnp_base(s, lo + 1, hi + 1, pad);
    } else {
        fnp_step(s, lo, hi, pad);
        assert(s[lo] == pad);
        fnp_miss_extend(s, lo + 1, hi, pad);
        fnp_step(s, lo, hi + 1, pad);
    }
}

pub proof fn nnp_miss_extend(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires
        0 <= lo <= hi < s.len(),
        nnp(s, lo, hi, p, pad) == hi,
        s[hi] == pad,
    ensures
        nnp(s, lo, hi + 1, p, pad) == hi + 1,
    decreases hi - lo,
{
    if lo == hi {
        nnp_step(s, lo, hi + 1, p, pad);
        nnp_base(s, lo + 1, hi + 1, p, pad);
    } else {
        nnp_step(s, lo, hi, p, pad);
        assert(!(s[lo] != pad && lo > p));
        assert(s[lo] == pad || lo <= p);
        nnp_miss_extend(s, lo + 1, hi, p, pad);
        nnp_step(s, lo, hi + 1, p, pad);
    }
}

/// a boundary at or past p forces the second scan to miss
pub proof fn nnp_end_miss(s: Seq<u8>, lo: int, hi: int, p: int, pad: u8)
    requires
        0 <= lo <= hi <= s.len(),
        hi <= p + 1,
    ensures
        nnp(s, lo, hi, p, pad) == hi,
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        nnp_end_miss(s, lo + 1, hi, p, pad);
    }
}

} // verus!
