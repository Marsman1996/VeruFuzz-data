//! `engine/naive.rs` mirror -- the Naive test-oracle engine (upstream `#[cfg(test)] mod naive;`)
//!
//! Reachability note: upstream compiles this module only under `cfg(test)`; it is the
//! rstest oracle that the engine test suite compares GeneralPurpose against. Its functions
//! are therefore library-internal test machinery, not public API; transcribing them is a
//! coverage-diff-set batch item (the machine-checkable scalar surface), not a bug hunt.

use vstd::prelude::*;

use super::super::decode::{DecodeError, DecodeSliceError};
use super::DecodePaddingMode;
use super::general_purpose::ValidAlphabetSymbols;
use super::general_purpose::decode::{
    complete_quads_len, is_invalid_morsel, morsel_pair_hi, morsel_pair_lo, morsel_pair_mid,
    nonterminal_quads_len_model, ValidDecodeTable, INVALID_VALUE,
};
use super::general_purpose::decode_suffix::{decode_suffix, DecodeMetadata};

verus! {

// items land here (engine/naive.rs mirror batch)

/* ============================================================
 * Origin: naive.rs:33-41 `Naive::decode_byte_into_u32`
 * ============================================================ */

/// Upstream doc (naive.rs:33-41): (no upstream doc comment on this item; it is a private
/// helper of the cfg(test) oracle engine).
/// Machine-levelization (lib.rs ledger): `self.decode_table` -> table parameter.
pub exec fn naive_decode_byte(
    decode_table: &[u8],
    offset: usize,
    byte: u8,
) -> (r: Result<u32, DecodeError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
    ensures
        /* table value == INVALID_VALUE -> Err(InvalidByte) with the exact offset/byte */
        is_invalid_morsel(decode_table@[(byte) as int]) ==> r == Result::Err(
            DecodeError::InvalidByte(offset, byte),
        ),
        /* legal symbol -> Ok with the table value as u32 (< 64) */
        decode_table@[(byte) as int] < 64 ==> r.is_ok()
            && r.get_Ok_0()@ == (decode_table@[(byte) as int]) as int,
{
    /* Origin Rust:
       let decoded = self.decode_table[byte as usize];
       if decoded == general_purpose::INVALID_VALUE {
           return Err(DecodeError::InvalidByte(offset, byte));
       }
       Ok(decoded as u32) */
    let decoded = decode_table[byte as usize];
    assert(decoded == decode_table@[(byte) as int]);
    if decoded == INVALID_VALUE {
        return Result::Err(DecodeError::InvalidByte(offset, byte));
    }
    assert(decoded < 64);
    Result::Ok(decoded as u32)
}

/* ============================================================
 * Origin: naive.rs:48-106 `impl Engine for Naive::internal_encode`
 * ============================================================ */

/// The four 6-bit indices of a 3-byte group (the complete-chunk bit slicing):
/// idx0 = b0>>2; idx1 = (b0<<4|b1>>4)&0x3F; idx2 = (b1<<2|b2>>6)&0x3F; idx3 = b2&0x3F.
/// Int/u32 semantics (each index in [0,63]); the rem tail paths reuse these with a
/// zero virtual neighbor byte (the bottom-bit-zero padding of the upstream code).
pub open spec fn naive_enc_idx0(b0: u8) -> u32 {
    ((b0 as u32) / 4) as u32
}

pub open spec fn naive_enc_idx1(b0: u8, b1: u8) -> u32 {
    (((b0 as u32) % 4 * 16 + (b1 as u32) / 16)) as u32
}

pub open spec fn naive_enc_idx2(b1: u8, b2: u8) -> u32 {
    (((b1 as u32) % 16 * 4 + (b2 as u32) / 64)) as u32
}

pub open spec fn naive_enc_idx3(b2: u8) -> u32 {
    ((b2 as u32) % 64) as u32
}

/// The unpadded base64 output length of `input_len` bytes:
/// 4 per complete 3-byte chunk, plus the 2/3-byte reminder tail, plus 0 when rem == 0.
pub open spec fn naive_unpadded_enc_len(input_len: int) -> int {
    let rem = input_len % 3;
    let complete = input_len - rem;
    complete / 3 * 4 + (if rem == 1 {
        2int
    } else if rem == 2 {
        3int
    } else {
        0int
    })
}

/// The base64 encoding byte model: the k-th written byte for complete-chunk positions
/// (k < complete/3*4, per-naive_enc_idx0..3 of the 3-byte group) and for the rem==2 /
/// rem==1 tail positions (with the zero virtual neighbor byte). Domain: 0 <= k < r.
pub open spec fn naive_encoded_byte(symbols: Seq<u8>, input: Seq<u8>, k: int) -> u8 {
    let len = input.len();
    let rem = len % 3;
    let complete = len - rem;
    if k < complete / 3 * 4 {
        let c = k / 4;
        let b0 = input[c * 3];
        let b1 = input[c * 3 + 1];
        let b2 = input[c * 3 + 2];
        let p = k % 4;
        if p == 0 {
            symbols[naive_enc_idx0(b0) as int]
        } else if p == 1 {
            symbols[naive_enc_idx1(b0, b1) as int]
        } else if p == 2 {
            symbols[naive_enc_idx2(b1, b2) as int]
        } else {
            symbols[naive_enc_idx3(b2) as int]
        }
    } else if rem == 2 {
        let b0 = input[complete];
        let b1 = input[complete + 1];
        let p = k - complete / 3 * 4;
        if p == 0 {
            symbols[naive_enc_idx0(b0) as int]
        } else if p == 1 {
            symbols[naive_enc_idx1(b0, b1) as int]
        } else {
            symbols[naive_enc_idx2(b1, 0) as int]
        }
    } else {
        /* rem == 1 (rem == 0 never indexes the tail region) */
        let b0 = input[complete];
        let p = k - complete / 3 * 4;
        if p == 0 {
            symbols[naive_enc_idx0(b0) as int]
        } else {
            symbols[naive_enc_idx1(b0, 0) as int]
        }
    }
}

/// Upstream doc (naive.rs:48-106; the `Engine` trait doc at engine/mod.rs:78-86, `#[doc(hidden)]`):
///   This is not meant to be called directly; it is only for `Engine` implementors.
///   See the other `encode*` functions on this trait.
///
///   Encode the `input` bytes into the `output` buffer based on the mapping in `encode_table`.
///
///   `output` will be long enough to hold the encoded data.
///
///   Returns the number of bytes written.
///
///   No padding should be written; that is handled separately.
///
///   Must not write any bytes into the output slice other than the encoded data.
/// Machine-levelization (lib.rs ledger): `self.encode_table` -> `symbols` (the
/// symbols sequence IS the encode table, see build_encode_table); unlike the u64
/// GeneralPurpose engine there is no length cap: the contract is universal over input lengths.
pub exec fn naive_internal_encode(symbols: &[u8], input: &[u8], output: &mut [u8]) -> (r: usize)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        naive_unpadded_enc_len(input@.len() as int) <= output@.len() as int,
    ensures
        final(output)@.len() == old(output)@.len(),
        r@ == naive_unpadded_enc_len(input@.len() as int),
        /* the full per-byte encoding model over the whole written region
           (complete-chunk quads and the 2/3-byte tails alike): the region
           face the decode composition consumes */
        forall|k: int|
            #![trigger final(output)@[k]]
            0 <= k < r@ ==> final(output)@[k] == naive_encoded_byte(symbols@, input@, k),
        /* every written byte is a printable alphabet symbol */
        forall|k: int| #![trigger final(output)@[k]] 0 <= k < r@ ==> 32 <= final(output)@[k] <= 126,
        forall|j: int| r@ <= j < final(output)@.len() ==> final(output)@[j] == old(output)@[j],
        /* the rem==2 tail: the last three written bytes per the 6-bit group models
           (b0,b1 = the last two input bytes; the third index uses the zero virtual neighbor) */
        input@.len() as int % 3 == 2 ==> (final(output)@[(((
            input@.len() as int
        ) - 2) / 3 * 4)] == symbols@[(naive_enc_idx0(input@[(input@.len() as int) - 2])) as int]
            && final(output)@[((((
                input@.len() as int
            ) - 2) / 3 * 4) + 1)] == symbols@[(
                naive_enc_idx1(
                    input@[(input@.len() as int) - 2],
                    input@[(input@.len() as int) - 1],
                )
            ) as int]
            && final(output)@[((((
                input@.len() as int
            ) - 2) / 3 * 4) + 2)] == symbols@[(
                naive_enc_idx2(input@[(input@.len() as int) - 1], 0)
            ) as int]),
        /* the rem==1 tail: the last two written bytes per the 6-bit group models */
        input@.len() as int % 3 == 1 ==> (final(output)@[(((
            input@.len() as int
        ) - 1) / 3 * 4)] == symbols@[(naive_enc_idx0(input@[(input@.len() as int) - 1])) as int]
            && final(output)@[((((
                input@.len() as int
            ) - 1) / 3 * 4) + 1)] == symbols@[(
                naive_enc_idx1(input@[(input@.len() as int) - 1], 0)
            ) as int]),
{
    let ghost g_symbols = symbols@;
    let ghost g_input = input@;
    /* Origin Rust: // complete chunks first
       const LOW_SIX_BITS: u32 = 0x3F; (folded into the index computations below) */
    /* Origin Rust: let rem = input.len() % Self::ENCODE_INPUT_CHUNK_SIZE; */
    let rem = input.len() % 3;
    assert(rem@ == g_input.len() as int % 3);
    /* Origin Rust: // will never underflow
       let complete_chunk_len = input.len() - rem; */
    let complete_chunk_len = input.len() - rem;
    assert(complete_chunk_len@ == g_input.len() as int - g_input.len() as int % 3);
    assert(complete_chunk_len as int % 3 == 0);
    let mut input_index: usize = 0;
    let mut output_index: usize = 0;
    /* Origin Rust: if let Some(last_complete_chunk_index) =
       complete_chunk_len.checked_sub(Self::ENCODE_INPUT_CHUNK_SIZE) {
           while input_index <= last_complete_chunk_index { ... } }
       -- checked_sub rewrite (lib.rs ledger item 4): the loop runs while another complete
          3-byte chunk remains; the machine subtraction is underflow-free because the
          loop invariant carries input_index <= complete_chunk_len */
    while complete_chunk_len - input_index >= 3
        invariant
            0 <= input_index <= complete_chunk_len,
            complete_chunk_len@ == g_input.len() as int - g_input.len() as int % 3,
            complete_chunk_len as int % 3 == 0,
            complete_chunk_len as int <= g_input.len() as int,
            output@.len() == old(output)@.len(),
            g_symbols == symbols@,
            g_input == input@,
            symbols@.len() == 64,
            ValidAlphabetSymbols(g_symbols),
            naive_unpadded_enc_len(g_input.len() as int) <= output@.len() as int,
            (output_index as int) == (input_index as int) / 3 * 4,
            (input_index as int) % 3 == 0,
            /* every written byte so far is a printable alphabet symbol */
            forall|k: int|
                #![trigger output@[k]] 0 <= k < output_index as int ==> 32 <= output@[k] <= 126,
            /* the per-byte model equality over the complete-chunk region */
            forall|k: int|
                #![trigger output@[k]]
                0 <= k < output_index as int ==> output@[k] == naive_encoded_byte(
                    g_symbols,
                    g_input,
                    k,
                ),
            forall|j: int| output_index as int <= j < output@.len() ==> output@[j] == old(output)@[j],
        decreases complete_chunk_len - input_index
    {
        proof {
            /* guard -> chunk bounds: a full 3-byte chunk is still within input */
            assert((complete_chunk_len as int) >= (input_index as int) + 3);
            assert((input_index as int) < g_input.len() as int);
            assert(((input_index as int) + 2) < g_input.len() as int);
        }
        /* Origin Rust: let chunk = &input[input_index..input_index + Self::ENCODE_INPUT_CHUNK_SIZE];
           -- slice rewrite: direct index reads onto the original input slice */
        let b0 = input[input_index];
        let b1 = input[input_index + 1];
        let b2 = input[input_index + 2];
        assert(b0 == g_input[input_index as int]);
        assert(b1 == g_input[(input_index as int) + 1]);
        assert(b2 == g_input[(input_index as int) + 2]);
        proof {
            /* the four 6-bit indices are in [0,63] (no u8 overflow in the compositions) */
            assert(b0 % 4 <= 3);
            assert(b0 % 4 * 16 + b1 / 16 <= 63);
            assert(b1 % 16 * 4 + b2 / 64 <= 63);
            assert(b2 % 64 <= 63);
        }
        /* Origin Rust:
           let chunk_int: u32 = (chunk[0] as u32).shl(16) | (chunk[1] as u32).shl(8) | (chunk[2] as u32);
           output[output_index] = self.encode_table[chunk_int.shr(18) as usize];
           output[output_index + 1] = self.encode_table[chunk_int.shr(12_u8).bitand(LOW_SIX_BITS) as usize];
           output[output_index + 2] = self.encode_table[chunk_int.shr(6_u8).bitand(LOW_SIX_BITS) as usize];
           output[output_index + 3] = self.encode_table[chunk_int.bitand(LOW_SIX_BITS) as usize];
           -- the u32 shl/shr/bitand chain packs the 3 bytes into the low 24 bits and slices
              four 6-bit groups; the byte-composed form below is bit-equivalent (the same
              rewrite family as decode_chunk_4 in general_purpose/decode.rs):
              chunk_int>>18 == b0>>2; (chunk_int>>12)&0x3F == (b0&0x3)<<4 | b1>>4;
              (chunk_int>>6)&0x3F == (b1&0xF)<<2 | b2>>6; chunk_int&0x3F == b2&0x3F */
        let i0 = b0 / 4;
        let i1 = b0 % 4 * 16 + b1 / 16;
        let i2 = b1 % 16 * 4 + b2 / 64;
        let i3 = b2 % 64;
        proof {
            assert(i0@ == naive_enc_idx0(b0)@);
            assert(i1@ == naive_enc_idx1(b0, b1)@);
            assert(i2@ == naive_enc_idx2(b1, b2)@);
            assert(i3@ == naive_enc_idx3(b2)@);
            /* output capacity for this chunk's 4 bytes */
            let c = (input_index as int) / 3;
            assert(output_index as int == 4 * c);
            assert(c + 1 <= complete_chunk_len as int / 3);
            assert(output_index as int + 4 <= complete_chunk_len as int / 3 * 4);
            assert(
                complete_chunk_len as int / 3 * 4 <= naive_unpadded_enc_len(
                    g_input.len() as int,
                )
            );
        }
        output[output_index] = symbols[i0 as usize];
        output[output_index + 1] = symbols[i1 as usize];
        output[output_index + 2] = symbols[i2 as usize];
        output[output_index + 3] = symbols[i3 as usize];
        proof {
            /* the four new positions match the region model: k/4*3 == input_index,
               so the model's group bytes are exactly this chunk's b0/b1/b2 (the
               model's complete == this loop's complete_chunk_len, the same
               len - len%3 expression the loop invariant already carries) */
            let kc = (output_index as int) / 4;
            assert((output_index as int) % 4 == 0);
            assert((kc * 3) == (input_index as int));
            assert(naive_encoded_byte(g_symbols, g_input, (output_index as int))
                == g_symbols[naive_enc_idx0(b0) as int]);
            assert(naive_encoded_byte(g_symbols, g_input, (output_index as int) + 1)
                == g_symbols[naive_enc_idx1(b0, b1) as int]);
            assert(naive_encoded_byte(g_symbols, g_input, (output_index as int) + 2)
                == g_symbols[naive_enc_idx2(b1, b2) as int]);
            assert(naive_encoded_byte(g_symbols, g_input, (output_index as int) + 3)
                == g_symbols[naive_enc_idx3(b2) as int]);
            assert(output@[(output_index as int)] == g_symbols[naive_enc_idx0(b0) as int]);
            assert(output@[(output_index as int) + 1] == g_symbols[naive_enc_idx1(b0, b1) as int]);
            assert(output@[(output_index as int) + 2] == g_symbols[naive_enc_idx2(b1, b2) as int]);
            assert(output@[(output_index as int) + 3] == g_symbols[naive_enc_idx3(b2) as int]);
            /* the four new positions hold alphabet symbols, hence printable ASCII
               (ValidAlphabetSymbols instantiated at each 6-bit index) */
            assert(0 <= i0@ && i0@ < 64);
            assert(0 <= i1@ && i1@ < 64);
            assert(0 <= i2@ && i2@ < 64);
            assert(0 <= i3@ && i3@ < 64);
            assert(32 <= output@[(output_index as int)] <= 126);
            assert(32 <= output@[(output_index as int) + 1] <= 126);
            assert(32 <= output@[(output_index as int) + 2] <= 126);
            assert(32 <= output@[(output_index as int) + 3] <= 126);
            assert(output@.len() == old(output)@.len());
        }
        input_index += 3;
        output_index += 4;
    }
    /* the loop walks whole 3-byte chunks: exit is exactly at input_index == complete_chunk_len */
    proof {
        assert((complete_chunk_len as int) - (input_index as int) < 3);
        assert((input_index as int) % 3 == 0);
        assert(((complete_chunk_len as int) - (input_index as int)) % 3 == 0);
        assert(input_index as int == complete_chunk_len as int);
        assert((output_index as int) == complete_chunk_len as int / 3 * 4);
    }
    /* Origin Rust: // then leftovers
       if rem == 2 { ... output_index += 3; } else if rem == 1 { ... output_index += 2; } */
    if rem == 2 {
        proof {
            assert(complete_chunk_len as int + 1 < g_input.len() as int);
            assert(
                output_index as int + 3 <= naive_unpadded_enc_len(g_input.len() as int)
            );
        }
        /* Origin Rust: let chunk = &input[input_index..input_index + 2]; (slice rewrite) */
        let b0 = input[input_index];
        let b1 = input[input_index + 1];
        assert(b0 == g_input[complete_chunk_len as int]);
        assert(b1 == g_input[(complete_chunk_len as int) + 1]);
        /* Origin Rust:
           output[output_index] = self.encode_table[chunk[0].shr(2) as usize];
           output[output_index + 1] = self.encode_table[(chunk[0].shl(4_u8).bitor(chunk[1].shr(4_u8)) as u32)
               .bitand(LOW_SIX_BITS) as usize];
           output[output_index + 2] = self.encode_table[(chunk[1].shl(2_u8) as u32)
               .bitand(LOW_SIX_BITS) as usize]; */
        let i0 = b0 / 4;
        let i1 = b0 % 4 * 16 + b1 / 16;
        /* the third output: (b1 << 2) & 0x3F == idx2(b1, 0) (zero virtual neighbor byte) */
        let i2 = b1 % 16 * 4;
        proof {
            assert(i0@ == naive_enc_idx0(b0)@);
            assert(i1@ == naive_enc_idx1(b0, b1)@);
            assert(i2@ == naive_enc_idx2(b1, 0)@);
            assert(g_input.len() as int % 3 == 2);
            assert(complete_chunk_len as int == g_input.len() as int - 2);
            assert((output_index as int) - complete_chunk_len as int / 3 * 4 == 0);
        }
        output[output_index] = symbols[i0 as usize];
        output[output_index + 1] = symbols[i1 as usize];
        output[output_index + 2] = symbols[i2 as usize];
        proof {
            let base = complete_chunk_len as int / 3 * 4;
            assert((output_index as int) - base == 0);
            assert(naive_encoded_byte(g_symbols, g_input, base) == g_symbols[naive_enc_idx0(
                b0,
            ) as int]);
            assert(naive_encoded_byte(g_symbols, g_input, base + 1) == g_symbols[naive_enc_idx1(
                b0,
                b1,
            ) as int]);
            assert(naive_encoded_byte(g_symbols, g_input, base + 2) == g_symbols[naive_enc_idx2(
                b1,
                0,
            ) as int]);
            assert(output@[base] == g_symbols[naive_enc_idx0(b0) as int]);
            assert(output@[base + 1] == g_symbols[naive_enc_idx1(b0, b1) as int]);
            assert(output@[base + 2] == g_symbols[naive_enc_idx2(b1, 0) as int]);
        }
        output_index += 3;
    } else if rem == 1 {
        proof {
            assert((complete_chunk_len as int) < (g_input.len() as int));
            assert(
                output_index as int + 2 <= naive_unpadded_enc_len(g_input.len() as int)
            );
        }
        /* Origin Rust: let byte = input[input_index]; */
        let byte = input[input_index];
        assert(byte == g_input[complete_chunk_len as int]);
        /* Origin Rust:
           output[output_index] = self.encode_table[byte.shr(2) as usize];
           output[output_index + 1] = self.encode_table[(byte.shl(4_u8) as u32)
               .bitand(LOW_SIX_BITS) as usize]; */
        let i0 = byte / 4;
        /* the second output: (byte << 4) & 0x3F == idx1(byte, 0) (zero virtual neighbor byte) */
        let i1 = byte % 4 * 16;
        proof {
            assert(i0@ == naive_enc_idx0(byte)@);
            assert(i1@ == naive_enc_idx1(byte, 0)@);
            assert(g_input.len() as int % 3 == 1);
            assert(complete_chunk_len as int == g_input.len() as int - 1);
            assert((output_index as int) - complete_chunk_len as int / 3 * 4 == 0);
        }
        output[output_index] = symbols[i0 as usize];
        output[output_index + 1] = symbols[i1 as usize];
        proof {
            let base = complete_chunk_len as int / 3 * 4;
            assert((output_index as int) - base == 0);
            assert(naive_encoded_byte(g_symbols, g_input, base) == g_symbols[naive_enc_idx0(
                byte,
            ) as int]);
            assert(naive_encoded_byte(g_symbols, g_input, base + 1) == g_symbols[naive_enc_idx1(
                byte,
                0,
            ) as int]);
            assert(output@[base] == g_symbols[naive_enc_idx0(byte) as int]);
            assert(output@[base + 1] == g_symbols[naive_enc_idx1(byte, 0) as int]);
        }
        output_index += 2;
    }
    proof {
        assert((output_index as int) == naive_unpadded_enc_len(g_input.len() as int));
    }
    output_index
}

/* ============================================================
 * Origin: naive.rs:112-157 `impl Engine for Naive::internal_decode`
 * ============================================================ */

/// The first invalid morsel position in the complete-quads region [0, nt):
/// scans input bytes through the decode table (better morsel -> recurse);
/// returns nt when the whole region is legal. The offset/byte of the reported
/// InvalidByte error is exactly this position and its input byte.
pub open spec fn naive_first_invalid(input: Seq<u8>, table: Seq<u8>, nt: int, i: int) -> int
    decreases nt - i
{
    if i >= nt {
        nt
    } else if is_invalid_morsel(table[input[i] as int]) {
        i
    } else {
        naive_first_invalid(input, table, nt, i + 1)
    }
}

/// Lemma: the one-step unfold of the first-invalid scan (valid at i -> skip;
/// invalid at i -> stop at i)
pub proof fn nfi_unfold(input: Seq<u8>, table: Seq<u8>, nt: int, i: int)
    requires
        0 <= i < nt,
    ensures
        !is_invalid_morsel(table[input[i] as int]) ==> naive_first_invalid(input, table, nt, i)
            == naive_first_invalid(input, table, nt, i + 1),
        is_invalid_morsel(table[input[i] as int]) ==> naive_first_invalid(input, table, nt, i) == i,
{
}

/// Lemma: a fully legal region [z, i) -> the scan from z reaches i
pub proof fn nfi_skip(input: Seq<u8>, table: Seq<u8>, nt: int, z: int, i: int)
    requires
        0 <= z <= i <= nt,
        forall|j: int| z <= j < i ==> !is_invalid_morsel(table[input[j] as int]),
    ensures naive_first_invalid(input, table, nt, z) == naive_first_invalid(input, table, nt, i)
    decreases i - z
{
    if z == i {
    } else {
        nfi_unfold(input, table, nt, z);
        nfi_skip(input, table, nt, z + 1, i);
    }
}

/// Upstream doc (naive.rs:112-157; the `Engine` trait doc at engine/mod.rs:101-118, `#[doc(hidden)]`):
///   This is not meant to be called directly; it is only for `Engine` implementors.
///   See the other `decode*` functions on this trait.
///
///   Decode `input` base64 bytes into the `output` buffer.
///
///   `decode_estimate` is the result of [Engine::internal_decoded_len_estimate()], which is passed in to avoid
///   calculating it again (expensive on short inputs).`
///
///   Each complete 4-byte chunk of encoded data decodes to 3 bytes of decoded data, but this
///   function must also handle the final possibly partial chunk.
///   If the input length is not a multiple of 4, or uses padding bytes to reach a multiple of 4,
///   the trailing 2 or 3 bytes must decode to 1 or 2 bytes, respectively, as per the
///   [RFC](https://tools.ietf.org/html/rfc4648#section-3.5).
///
///   Decoding must not write any bytes into the output slice other than the decoded data.
///
///   Non-canonical trailing bits in the final symbols or non-canonical padding must be reported as
///   errors unless the engine is configured otherwise.
/// Machine-levelization (lib.rs ledger): `self.decode_table`/`self.padding`/the three
/// `self.config` bits -> explicit parameters; `estimate: NaiveEstimate` -> its two fields
/// (estimate_rem, estimate_complete_chunk_len). Contract scope: the front check and the
/// suffix call pass through the verified callee contracts (complete_quads_len /
/// decode_suffix). Two composition limits are component-split (file-tail note):
/// (1) the exact first-invalid-morsel clause of the complete-quads loop cannot be stated
/// at the fn boundary because the verified complete_quads_len contract does not
/// characterize its non-convenience Err exit, so a front-check Err is not contract-excludable
/// even when the region holds an invalid morsel (upstream's own complete_quads_len returns
/// Err there only for the two machine-checkable conditions; the four in-loop early
/// returns keep the ground per-position first-invalid facts, verified per iteration);
/// (2) the per-byte written semantics of the Ok path cannot be stated because the
/// verified decode_suffix contract preserves only the output length (no
/// untouched-below-output_index clause) -- the harness can witness the composition through
/// the already-verified decode_chunk_4/morsel_pair models.
pub exec fn naive_internal_decode(
    input: &[u8],
    output: &mut [u8],
    estimate_rem: usize,
    estimate_complete_chunk_len: usize,
    decode_table: &[u8],
    padding: u8,
    decode_allow_trailing_bits: bool,
    decode_padding_mode: DecodePaddingMode,
) -> (r: Result<DecodeMetadata, DecodeSliceError>)
    requires
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        /* the NaiveEstimate construction relation (naive_estimate) */
        input@.len() as int % 4 == estimate_rem as int,
        estimate_complete_chunk_len as int == input@.len() as int - estimate_rem as int,
        /* offset-reporting slack (the same caller contract decode_suffix carries) */
        input@.len() as int <= usize::MAX as int - 8,
        /* the output_index increment obligations of decode_suffix need +4 */
        output@.len() as int <= usize::MAX as int - 4,
    ensures
        /* the decode_suffix contract preserves the output length only on its Ok exit;
           on the fn-Err exits of naive_internal_decode the output was never handed to a
           callee that could alias it, so the clause is stated symmetric-Ok */
        r.is_ok() ==> final(output)@.len() == old(output)@.len(),
        /* pass-through of the complete_quads_len convenience check (upstream lines 118-124):
           rem == 1 and the single trailing byte is neither padding nor a legal symbol */
        estimate_rem == 1
            && input@.len() == 1
            && input@[0] != padding
            && is_invalid_morsel(decode_table@[(input@[0]) as int]) ==> r == Result::Err(
            DecodeSliceError::DecodeError(DecodeError::InvalidByte(0, input@[0])),
        ),
        /* component-split (see the contract-scope comment above and the file-tail note):
           the exact first-invalid-morsel clause of the complete-quads loop
           (first illegal symbol in [0, NT) -> Err(InvalidByte(NFI, input[NFI]))) is not
           provable at this boundary because complete_quads_len's verified contract does
           not characterize its remaining Err exit, so a front-check Err cannot be ruled
           out by the requires even when the region holds an invalid morsel; the four
           in-loop early returns each carry the ground first-invalid facts
           (verified per iteration via naive_decode_byte's ensures + the nfi_unfold scan) */
        /* pass-through of the decode_suffix exit-safety face: on success the decoded
           length carries the loop's output_index (the complete-quads decode length, NT/4*3)
           plus at most 3 incremental suffix bytes; an all-empty input is always a
           0-byte success (the upstream !input.is_empty() gate inside decode_suffix) */
        r.is_ok() ==> (r.get_Ok_0().decoded_len as int) >= nonterminal_quads_len_model(
            (input@.len() as int),
            (estimate_rem as int),
        ) / 4 * 3,
        r.is_ok() ==> ((r.get_Ok_0().decoded_len as int) - nonterminal_quads_len_model(
            (input@.len() as int),
            (estimate_rem as int),
        ) / 4 * 3) <= 3,
        input@.len() == 0 ==> r.is_ok()
            && (r.get_Ok_0().decoded_len as int) == 0,
        /* the exact first-invalid-morsel clause (the full-domain feed: with the
           front check excluded by the strengthened complete_quads_len contract,
           the first illegal symbol in the completed-quads region is reported
           verbatim -- the component-split of the earlier file-tail note is
           discharged for this clause).
           The named front-check exclusions:
             - not (rem == 1 && trailing illegal non-pad byte)
             - output room for the whole nonterminal region */
        ((naive_first_invalid(
            input@,
            decode_table@,
            nonterminal_quads_len_model((input@.len() as int), (estimate_rem as int)),
            0,
        ) as int) < nonterminal_quads_len_model(
            (input@.len() as int),
            (estimate_rem as int),
        ))
            && !(estimate_rem == 1
                && input@.len() > 0
                && input@ [(input@.len() as int) - 1] != padding
                && is_invalid_morsel(
                    decode_table@ [(input@ [(input@.len() as int) - 1]) as int],
                ))
            && ((old(output)@.len() as int) >= nonterminal_quads_len_model(
                (input@.len() as int),
                (estimate_rem as int),
            ) / 4 * 3)
            ==> r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(
                (naive_first_invalid(
                    input@,
                    decode_table@,
                    nonterminal_quads_len_model((input@.len() as int), (estimate_rem as int)),
                    0,
                )) as usize,
                input@ [naive_first_invalid(
                    input@,
                    decode_table@,
                    nonterminal_quads_len_model((input@.len() as int), (estimate_rem as int)),
                    0,
                ) as int],
            ))),
{
    let ghost g_input = input@;
    let ghost g_table = decode_table@;
    /* empty-input fast path (upstream semantic composition, restructured): upstream's
       complete_quads_len with input len 0 returns Ok(0) (saturating), the chunks_exact(4)
       loop runs zero iterations, and decode_suffix over an empty input is verified to
       return Ok with decoded_len == output_index == 0 -- the short-circuit below is the
       same composition with the empty-input exit-safety of the verified decode_suffix;
       it exists so the empty-input postcondition does not have to reason across the
       under-specified front-check callee Err branch */
    if input.len() == 0 {
        /* Origin Rust: (implicit upstream composition, see the note above) */
        return decode_suffix(
            input,
            0,
            output,
            0,
            decode_table,
            decode_allow_trailing_bits,
            padding,
            decode_padding_mode,
            Ghost(false),
        );
    }
    /* Origin Rust:
       let complete_nonterminal_quads_len = general_purpose::decode::complete_quads_len(
           input, estimate.rem, output.len(), &self.decode_table, self.padding)?; */
    let front = complete_quads_len(input, estimate_rem, output.len(), decode_table, padding);
    let nt = match front {
        Result::Err(e) => return Result::Err(e),
        Result::Ok(v) => v,
    };
    proof {
        assert((nt as int) == nonterminal_quads_len_model((input@.len() as int), (estimate_rem as int)));
    }
    /* the model bounds needed to thread the decode_suffix caller contract:
       NT <= input_len, the suffix region input@.len() - NT is at most 4 bytes,
       and NT is a multiple of 4 (the quad-loop division bridges) */
    proof {
        assert((nt as int) <= g_input.len() as int);
        assert((g_input.len() as int) - (nt as int) <= 4);
        assert((nt as int) <= usize::MAX as int - 8);
        assert(g_input.len() as int % 4 == (estimate_rem as int));
        assert(g_input.len() as int >= (estimate_rem as int));
        assert(
            g_input.len() as int - (estimate_rem as int) == 4 * (g_input.len() as int / 4)
        );
        assert((g_input.len() as int - (estimate_rem as int)) % 4 == 0);
        assert((nt as int) % 4 == 0);
    }
    /* Origin Rust: const BOTTOM_BYTE: u32 = 0xFF; (the u32 word form is rewritten below) */
    /* Origin Rust:
       let quad_count = input[..complete_nonterminal_quads_len].chunks_exact(4).len();
       -- chunks_exact(4).enumerate() becomes the chunk_index while loop (lib.rs ledger: the
          slice-range chunks_exact(4) bind is rewritten into the offset computation on the
          original slice; the `?` operators of the loop become the explicit early returns) */
    let quad_count = nt / 4;
    assert((quad_count as int) == (nt as int) / 4);
    /* machine-level output re-check (unreachable when the callee is faithful: complete_quads_len
       returns Err(OutputSliceTooSmall) when output.len() < nt/4*3; the verified callee contract
       states the Ok-value model only, so the loop's write bounds carry the check explicitly,
       lib.rs ledger item 4) */
    if output.len() < quad_count * 3 {
        return Result::Err(DecodeSliceError::OutputSliceTooSmall);
    }
    assert(output@.len() as int >= (quad_count as int) * 3);
    let mut chunk_index: usize = 0;
    while chunk_index < quad_count
        invariant
            0 <= chunk_index <= quad_count,
            (nt as int) == nonterminal_quads_len_model((g_input.len() as int), (estimate_rem as int)),
            (quad_count as int) == (nt as int) / 4,
            g_input == input@,
            g_table == decode_table@,
            decode_table@.len() == 256,
            ValidDecodeTable(decode_table@),
            output@.len() == old(output)@.len(),
            output@.len() as int >= (quad_count as int) * 3,
            input@.len() as int <= usize::MAX as int - 8,
            (nt as int) <= g_input.len() as int,
            (nt as int) % 4 == 0,
            naive_first_invalid(g_input, g_table, (nt as int), 0) == naive_first_invalid(
                g_input,
                g_table,
                (nt as int),
                (4 * chunk_index) as int,
            ),
        decreases quad_count - chunk_index
    {
        /* Origin Rust: let input_index = chunk_index * 4; let output_index = chunk_index * 3; */
        let input_index = chunk_index * 4;
        let output_index = chunk_index * 3;
        proof {
            assert((input_index as int) == (chunk_index as int) * 4);
            assert((output_index as int) == (chunk_index as int) * 3);
            assert((nt as int) % 4 == 0);
            assert((4 * (chunk_index as int)) + 3 < (nt as int));
            assert((input_index as int) + 3 < g_input.len() as int);
            assert((output_index as int) + 2 < output@.len() as int);
        }
        /* Origin Rust: let chunk = &input[input_index..input_index + 4]; (slice rewrite) */
        let i0 = input[input_index];
        let i1 = input[input_index + 1];
        let i2 = input[input_index + 2];
        let i3 = input[input_index + 3];
        assert(i0 == g_input[input_index as int]);
        assert(i1 == g_input[(input_index as int) + 1]);
        assert(i2 == g_input[(input_index as int) + 2]);
        assert(i3 == g_input[(input_index as int) + 3]);
        /* Origin Rust: self.decode_byte_into_u32(input_index, chunk[0])?.shl(18) | ...
       -- the `?` becomes the explicit early return; the morsel u32 shl/bor packing:
          decoded_int = m0<<18 | m1<<12 | m2<<6 | m3; the output bytes are the three
          truncated big-endian bytes of decoded_int, rewritten bit-equivalently to the
          verified morsel_pair_lo/mid/hi models (the same rewrite family as
          decode_chunk_4 in general_purpose/decode.rs) */
        let m0r = naive_decode_byte(decode_table, input_index, i0);
        let m0 = match m0r {
            Result::Err(e) => {
                proof {
                    nfi_unfold(g_input, g_table, (nt as int), input_index as int);
                    assert(naive_first_invalid(g_input, g_table, (nt as int), input_index as int) == input_index as int);
                    assert(naive_first_invalid(g_input, g_table, (nt as int), 0) == input_index as int);
                }
                return Result::Err(DecodeSliceError::DecodeError(e));
            },
            Result::Ok(v) => v as u8,
        };
        assert(m0 < 64);
        let m1r = naive_decode_byte(decode_table, input_index + 1, i1);
        let m1 = match m1r {
            Result::Err(e) => {
                proof {
                    nfi_unfold(g_input, g_table, (nt as int), input_index as int);
                    nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 1);
                    assert(!is_invalid_morsel(g_table[(i0) as int]));
                    assert(naive_first_invalid(g_input, g_table, (nt as int), input_index as int) == naive_first_invalid(
                        g_input, g_table, (nt as int), (input_index as int) + 1,
                    ));
                    assert(naive_first_invalid(g_input, g_table, (nt as int), (input_index as int) + 1) == (input_index as int) + 1);
                    assert(naive_first_invalid(g_input, g_table, (nt as int), 0) == (input_index as int) + 1);
                }
                return Result::Err(DecodeSliceError::DecodeError(e));
            },
            Result::Ok(v) => v as u8,
        };
        assert(m1 < 64);
        let m2r = naive_decode_byte(decode_table, input_index + 2, i2);
        let m2 = match m2r {
            Result::Err(e) => {
                proof {
                    nfi_unfold(g_input, g_table, (nt as int), input_index as int);
                    nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 1);
                    nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 2);
                    assert(!is_invalid_morsel(g_table[(i0) as int]));
                    assert(!is_invalid_morsel(g_table[(i1) as int]));
                    assert(naive_first_invalid(g_input, g_table, (nt as int), input_index as int) == naive_first_invalid(
                        g_input, g_table, (nt as int), (input_index as int) + 2,
                    ));
                    assert(naive_first_invalid(g_input, g_table, (nt as int), (input_index as int) + 2) == (input_index as int) + 2);
                    assert(naive_first_invalid(g_input, g_table, (nt as int), 0) == (input_index as int) + 2);
                }
                return Result::Err(DecodeSliceError::DecodeError(e));
            },
            Result::Ok(v) => v as u8,
        };
        assert(m2 < 64);
        let m3r = naive_decode_byte(decode_table, input_index + 3, i3);
        let m3 = match m3r {
            Result::Err(e) => {
                proof {
                    nfi_unfold(g_input, g_table, (nt as int), input_index as int);
                    nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 1);
                    nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 2);
                    nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 3);
                    assert(!is_invalid_morsel(g_table[(i0) as int]));
                    assert(!is_invalid_morsel(g_table[(i1) as int]));
                    assert(!is_invalid_morsel(g_table[(i2) as int]));
                    assert(naive_first_invalid(g_input, g_table, (nt as int), input_index as int) == naive_first_invalid(
                        g_input, g_table, (nt as int), (input_index as int) + 3,
                    ));
                    assert(naive_first_invalid(g_input, g_table, (nt as int), (input_index as int) + 3) == (input_index as int) + 3);
                    assert(naive_first_invalid(g_input, g_table, (nt as int), 0) == (input_index as int) + 3);
                }
                return Result::Err(DecodeSliceError::DecodeError(e));
            },
            Result::Ok(v) => v as u8,
        };
        assert(m3 < 64);
        proof {
            assert(morsel_pair_lo(m0, m1) == (((m0 as u32) * 4) + ((m1 as u32) / 16)) as u8) by (bit_vector)
                requires m0 < 64, m1 < 64;
            assert(morsel_pair_mid(m1, m2) == (((m1 as u32) % 16 * 16) + ((m2 as u32) / 4)) as u8) by (bit_vector)
                requires m1 < 64, m2 < 64;
            assert(morsel_pair_hi(m2, m3) == (((m2 as u32) % 4 * 64) + (m3 as u32)) as u8) by (bit_vector)
                requires m2 < 64, m3 < 64;
        }
        /* Origin Rust:
           output[output_index] = decoded_int.shr(16_u8).bitand(BOTTOM_BYTE) as u8;
           output[output_index + 1] = decoded_int.shr(8_u8).bitand(BOTTOM_BYTE) as u8;
           output[output_index + 2] = decoded_int.bitand(BOTTOM_BYTE) as u8; */
        let o0 = (((m0 as u32) * 4) + ((m1 as u32) / 16)) as u8;
        let o1 = (((m1 as u32) % 16 * 16) + ((m2 as u32) / 4)) as u8;
        let o2 = (((m2 as u32) % 4 * 64) + (m3 as u32)) as u8;
        assert(o0 == morsel_pair_lo(m0, m1));
        assert(o1 == morsel_pair_mid(m1, m2));
        assert(o2 == morsel_pair_hi(m2, m3));
        output[output_index] = o0;
        output[output_index + 1] = o1;
        output[output_index + 2] = o2;
        proof {
            /* this iteration's four morsels are all legal (the four decode_byte Ok
               results), so the scan advances over the whole quad; the four unfold
               links chain ground-position facts, no quantifier instantiation needed */
            nfi_unfold(g_input, g_table, (nt as int), input_index as int);
            nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 1);
            nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 2);
            nfi_unfold(g_input, g_table, (nt as int), (input_index as int) + 3);
            assert(!is_invalid_morsel(g_table[(i0) as int]));
            assert(!is_invalid_morsel(g_table[(i1) as int]));
            assert(!is_invalid_morsel(g_table[(i2) as int]));
            assert(!is_invalid_morsel(g_table[(i3) as int]));
            assert(naive_first_invalid(g_input, g_table, (nt as int), input_index as int) == naive_first_invalid(
                g_input,
                g_table,
                (nt as int),
                (input_index as int) + 4,
            ));
        }
        chunk_index += 1;
    }
    /* Origin Rust:
       general_purpose::decode_suffix::decode_suffix(
           input, complete_nonterminal_quads_len, output,
           complete_nonterminal_quads_len / 4 * 3,
           &self.decode_table, self.config.decode_allow_trailing_bits,
           self.padding, self.config.decode_padding_mode) */
    let base_output_index = quad_count * 3;
    assert((base_output_index as int) == (quad_count as int) * 3);
    proof {
        assert((base_output_index as int) + 4 <= usize::MAX as int);
        assert((nt as int) <= usize::MAX as int - 8);
        assert((nt as int) <= g_input.len() as int);
        assert((g_input.len() as int) - (nt as int) <= 4);
    }
    decode_suffix(
        input,
        nt,
        output,
        base_output_index,
        decode_table,
        decode_allow_trailing_bits,
        padding,
        decode_padding_mode,
        Ghost(false),
    )
}

/* ============================================================
 * Origin: naive.rs:168-191 `NaiveEstimate` (pub struct + impl NaiveEstimate
 * + impl DecodeEstimate)
 * ============================================================ */

/// Upstream doc (naive.rs:176-184; the `DecodeEstimate` trait doc at engine/mod.rs:474-484):
///   The decode estimate used by an engine implementation. Users do not need to interact with this;
///   it is only for engine implementors.
///   Implementors may store relevant data here when constructing this to avoid having to calculate
///   them again during actual decoding.
///   Returns a conservative (err on the side of too big) estimate of the decoded length to use
///   for pre-allocating buffers, etc.
///
///   The estimate must be no larger than the next largest complete triple of decoded bytes.
///   That is, the final quad of symbols to decode may be assumed to be complete with no padding.
/// Machine-level split: returns (rem, complete_chunk_len) -- the two fields of NaiveEstimate
/// (construction contract; the struct itself is data plumbing, see lib.rs ledger).
pub exec fn naive_estimate(input_len: usize) -> (r: (usize, usize))
    ensures
        r.0@ == input_len as int % 4,
        r.0 <= 3,
        r.1@ == input_len as int - input_len as int % 4,
{
    /* Origin Rust: let rem = input_len % Naive::DECODE_INPUT_CHUNK_SIZE;
       let complete_chunk_len = input_len - rem; */
    let rem = input_len % 4;
    assert(rem@ == input_len as int % 4);
    let complete_chunk_len = input_len - rem; /* no underflow: rem = input_len % 4 */
    assert(complete_chunk_len@ == input_len as int - input_len as int % 4);
    (rem, complete_chunk_len)
}

/// Upstream doc (naive.rs:187-191; the `DecodeEstimate` trait doc at engine/mod.rs:477-484):
///   Returns a conservative (err on the side of too big) estimate of the decoded length to use
///   for pre-allocating buffers, etc.
///
///   The estimate must be no larger than the next largest complete triple of decoded bytes.
///   That is, the final quad of symbols to decode may be assumed to be complete with no padding.
/// Machine-level split: takes the two NaiveEstimate fields as parameters (struct data plumbing,
/// see lib.rs ledger); the estimate formula is transcribed verbatim with the no-overflow proof.
pub exec fn naive_decoded_len_estimate(complete_chunk_len: usize, rem: usize) -> (r: usize)
    ensures
        r@ == (complete_chunk_len as int / 4 + if rem as int > 0 { 1int } else { 0int }) * 3,
{
    /* Origin Rust: ((self.complete_chunk_len / 4) + ((self.rem > 0) as usize)) * 3 */
    let padded = complete_chunk_len / 4 + if rem > 0 { 1usize } else { 0usize };
    assert(padded@ == complete_chunk_len as int / 4 + if rem as int > 0 { 1int } else { 0int });
    /* no-overflow proof (same idiom as estimate_decoded_len in general_purpose/decode.rs):
       complete_chunk_len/4 <= MAX/4, so padded <= MAX/4 + 1, so padded*3 <= MAX */
    assert(complete_chunk_len as int / 4 <= usize::MAX as int / 4);
    assert(padded@ <= usize::MAX as int / 4 + 1);
    let r = padded * 3;
    assert(r@ == padded@ * 3);
    assert(padded@ * 3 <= (usize::MAX as int / 4 + 1) * 3);
    assert((usize::MAX as int / 4 + 1) * 3 <= usize::MAX as int);
    r
}

/* ============================================================
 * Origin: naive.rs:193-204 `NaiveConfig` (pub struct + impl Config)
 * ============================================================ */

/// Origin: naive.rs:193 `NaiveConfig` (upstream derives Clone, Copy, Debug; the Debug derive
/// is dropped because the verified `DecodePaddingMode` mirror carries no Debug)
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NaiveConfig {
    pub encode_padding: bool,
    pub decode_allow_trailing_bits: bool,
    pub decode_padding_mode: DecodePaddingMode,
}

/// Upstream doc (naive.rs:200-204; the `Config` trait doc at engine/mod.rs:460-465):
///   The minimal level of configuration that engines must support.
///   Returns `true` if padding should be added after the encoded output.
///
///   Padding is added outside the engine's `encode()` since the engine may be used
///   to encode only a chunk of the overall output, so it can't always know when
///   output is "done" and would therefore need padding (if configured).
/// Machine-level split: the trait-method accessor becomes the struct's field accessor function.
pub exec fn naive_config_encode_padding(cfg: &NaiveConfig) -> (r: bool)
    ensures
        r == cfg.encode_padding,
{
    /* Origin Rust: impl Config for NaiveConfig {
       fn encode_padding(&self) -> bool { self.encode_padding } } */
    cfg.encode_padding
}

/* ============================================================
 * Scan-algebra lemmas over naive_first_invalid (shared by the general_purpose
 * decode integration: the two-layer complete-quads loop threads its first-
 * invalid contracts through these; single source, no copies).
 * ============================================================ */

/// The scan result stays inside [i, nt].
pub proof fn nfi_bounds(input: Seq<u8>, table: Seq<u8>, nt: int, i: int)
    requires
        0 <= i <= nt,
        nt <= input.len(),
    ensures
        i <= naive_first_invalid(input, table, nt, i) <= nt,
    decreases nt - i,
{
    if i >= nt {
    } else {
        nfi_bounds(input, table, nt, i + 1);
    }
}

/// A scan hit below m pins every wider bound: the first invalid does not move
/// when the scan horizon extends (the loop-exit error chain).
pub proof fn nfi_pin(input: Seq<u8>, table: Seq<u8>, m: int, nt: int, i: int)
    requires
        0 <= i <= m <= nt,
        nt <= input.len(),
    ensures
        naive_first_invalid(input, table, m, i) < m ==> naive_first_invalid(
            input,
            table,
            nt,
            i,
        ) == naive_first_invalid(input, table, m, i),
    decreases m - i,
{
    if naive_first_invalid(input, table, m, i) >= m {
    } else {
        if i >= m {
            assert(false);
        } else {
            nfi_unfold(input, table, m, i);
            nfi_unfold(input, table, nt, i);
            if is_invalid_morsel(table[input[i] as int]) {
                assert(naive_first_invalid(input, table, m, i) == i);
                assert(naive_first_invalid(input, table, nt, i) == i);
            } else {
                nfi_pin(input, table, m, nt, i + 1);
            }
        }
    }
}

/// A scan that reaches nt means the whole region is legal (the mid-loop Ok
/// consumption of the general_purpose spans).
pub proof fn nfi_alllegal(input: Seq<u8>, table: Seq<u8>, nt: int, i: int)
    requires
        0 <= i <= nt,
        nt <= input.len(),
    ensures
        naive_first_invalid(input, table, nt, i) == nt ==> (forall|q: int|
            #![trigger table[input[q] as int]]
            i <= q < nt ==> !is_invalid_morsel(table[input[q] as int])),
    decreases nt - i,
{
    if i >= nt {
    } else {
        nfi_unfold(input, table, nt, i);
        if naive_first_invalid(input, table, nt, i) == nt {
            assert(naive_first_invalid(input, table, nt, i + 1) == nt);
            nfi_alllegal(input, table, nt, i + 1);
        }
    }
}

/// A scan hit below nt means the hit position is illegal and everything before
/// it in [i, hit) is legal (the span-level Err consumption of the general_purpose
/// chunks: the error cover is indexed by exactly this scan).
pub proof fn nfi_hit(input: Seq<u8>, table: Seq<u8>, nt: int, i: int)
    requires
        0 <= i <= nt,
        nt <= input.len(),
    ensures
        naive_first_invalid(input, table, nt, i) < nt ==> ((is_invalid_morsel(
            table[input[naive_first_invalid(input, table, nt, i) as int] as int],
        )) && (forall|q: int|
            #![trigger table[input[q] as int]]
            i <= q < naive_first_invalid(input, table, nt, i) ==> !is_invalid_morsel(
                table[input[q] as int],
            ))),
    decreases nt - i,
{
    if i >= nt {
    } else {
        nfi_unfold(input, table, nt, i);
        if naive_first_invalid(input, table, nt, i) < nt {
            if is_invalid_morsel(table[input[i] as int]) {
                assert(naive_first_invalid(input, table, nt, i) == i);
                assert(naive_first_invalid(input, table, nt, i) == i + 0);
            } else {
                assert(naive_first_invalid(input, table, nt, i) == naive_first_invalid(input, table, nt, i + 1));
                nfi_hit(input, table, nt, i + 1);
            }
        }
    }
}

/// A ground-first-invalid at z with a legal prefix [i, z) pins the scan to z
/// (the span-level scan chain over the accumulated-legal prefix).
pub proof fn nfi_split_at(input: Seq<u8>, table: Seq<u8>, nt: int, i: int, z: int)
    requires
        0 <= i <= z < nt,
        nt <= input.len(),
        forall|q: int|
            #![trigger table[input[q] as int]] i <= q < z ==> !is_invalid_morsel(
                table[input[q] as int],
            ),
        is_invalid_morsel(table[input[z] as int]),
    ensures
        naive_first_invalid(input, table, nt, i) == z,
{
    nfi_skip(input, table, nt, i, z);
    nfi_unfold(input, table, nt, z);
    assert(naive_first_invalid(input, table, nt, z) == z);
}


/// A full-window scan (horizon nt) reaching nt forces every smaller horizon m in
/// [z, nt] to also reach m (the span's Ok chain: window scans == window ends).
pub proof fn nfi_window_end(input: Seq<u8>, table: Seq<u8>, z: int, m: int, nt: int)
    requires
        0 <= z <= m <= nt <= input.len(),
    ensures
        naive_first_invalid(input, table, nt, z) == nt ==> naive_first_invalid(
            input,
            table,
            m,
            z,
        ) == m,
{
    if naive_first_invalid(input, table, m, z) < m {
        nfi_pin(input, table, m, nt, z);
        assert(naive_first_invalid(input, table, nt, z) < m);
        assert(naive_first_invalid(input, table, nt, z) != nt);
    }
    nfi_bounds(input, table, m, z);
}

} // verus!

/* ============================================================
 * Component-split record (the two composition limits of this batch; the file keeps
 * the machine-check face whole -- no index-bound/overflow/panic obligation was relaxed)
 * 1. naive_internal_encode: the composite per-byte semantic ensure
 *    forall|k in [0, r)| final(output)@[k] == naive_encoded_byte(symbols@, input@, k)
 *    stalled past the solver-stability budget while it verified in isolation: with the
 *    asserted region fact present the back-edge invariant fails, and vice versa under the
 *    alternate snapshot encoding (evidence: out/verus-bugfinder/probe-enc-invariant.rs
 *    reproduces the 4-writes-per-iteration region-invariant pattern passing standalone).
 *    Kept instead: the machine-exact unpadded-length model (r == naive_unpadded_enc_len),
 *    full-region printability (32..=126 via ValidAlphabetSymbols), full suffix
 *    preservation beyond r, and the concrete last-tail model bytes for the rem==2/rem==1
 *    paths (positions expressed from input@.len() alone, covering every input of
 *    length 1..6 -- the roundtrip exemplar domain). The naive_encoded_byte model stays
 *    exported for per-instance harness witnessing.
 * 2. naive_internal_decode: the exact first-invalid-morsel clause
 *    (first illegal symbol in the complete-quads region -> Err(InvalidByte(NFI, input[NFI])))
 *    is not provable at the fn boundary because the verified complete_quads_len contract
 *    under-specifies its non-convenience Err exit, so a front-check Err cannot be
 *    contract-excluded even when the region holds an invalid morsel. The four in-loop
 *    early returns each keep ground first-invalid facts (naive_decode_byte's ensures +
 *    the nfi_unfold scan, verified per iteration), and the naive_first_invalid /
 *    nfi_unfold / nfi_skip algebra is exported for harness witnessing. The Ok-path
 *    per-chunk byte semantics are additionally not re-ensurable because the verified
 *    decode_suffix contract preserves only the output length (no untouched-below-
 *    output_index clause); the morsel_pair_lo/mid/hi composition is witnessed through
 *    the already-verified decode_chunk_4 contract family.
 * ============================================================ */
