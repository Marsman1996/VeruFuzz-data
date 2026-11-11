//! `engine/general_purpose/encode.rs` -- the encode side of the general-purpose engine
//!
//! Derived file (placement note): upstream defines these items in
//! `engine/general_purpose/mod.rs`; this subfile carries only the scalar-encode segment of
//! that file so the encoding-loop surface can be extended independently. The sole source of
//! specs/lemmas for this segment is here (harness consumers reference it; no copies).
//!
//! Domain note: the encode chain is verified for the full input domain (any input
//! length, any resume point on the 3-byte group lattice). The u64 fast loop
//! (entered when input.len() > 26) is verified against the 6-bit-group byte
//! model of enc_tail_byte through explicit bit_vector bridges: the word
//! composition is restated inline as the antecedent of every bridge query,
//! masks stay fully parenthesized, byte slicing goes through as-cast forms,
//! and the eight output slots of one u64 read are carried by the per-span
//! helper fast_quad8 as eight ground conjuncts (no quantified position
//! clause inside the helper). No admit/assume appears in this file.

use vstd::prelude::*;
use super::ValidAlphabetSymbols;

verus! {

/* ============================================================
 * Spec models (the 6-bit group indexing of base64 encoding)
 * ============================================================ */

/// 6-bit index model of group output byte 0: b0 >> 2
/// (validated against upstream mod.rs:242: encode_table[(input_chunk[0] >> 2) as usize])
pub open spec fn enc_idx0(b0: u8) -> u8 {
    b0 >> 2
}

/// 6-bit index model of group output byte 1: (b0 << 4 | b1 >> 4) & 0x3F
/// (validated against upstream mod.rs:244:
///  encode_table[(input_chunk[0] << 4 | input_chunk[1] >> 4) & LOW_SIX_BITS_U8])
pub open spec fn enc_idx1(b0: u8, b1: u8) -> u8 {
    ((b0 << 4) | (b1 >> 4)) & 0x3F
}

/// 6-bit index model of group output byte 2: (b1 << 2 | b2 >> 6) & 0x3F
/// (validated against upstream mod.rs:246:
///  encode_table[(input_chunk[1] << 2 | input_chunk[2] >> 6) & LOW_SIX_BITS_U8])
pub open spec fn enc_idx2(b1: u8, b2: u8) -> u8 {
    ((b1 << 2) | (b2 >> 6)) & 0x3F
}

/// 6-bit index model of group output byte 3: b2 & 0x3F
/// (validated against upstream mod.rs:247: encode_table[(input_chunk[2] & LOW_SIX_BITS_U8)])
pub open spec fn enc_idx3(b2: u8) -> u8 {
    b2 & 0x3F
}

/// Unpadded encoded length of `rem_len` bytes: 4 per complete 3-byte group, plus
/// 2 (one leftover byte) / 3 (two leftover bytes) for the final partial group.
pub open spec fn tail_unpadded_len(rem_len: int) -> int {
    if rem_len <= 0 {
        0
    } else {
        let q = rem_len / 3;
        let m = rem_len % 3;
        if m == 0 {
            4 * q
        } else if m == 1 {
            4 * q + 2
        } else {
            4 * q + 3
        }
    }
}

/// The byte written at absolute output position `j` by the tail encoder launched at
/// `input_index` (a multiple of 3) with output base `input_index/3*4`. Total spec model
/// of encode_scalar_tail's write semantics: complete groups produce the full quad; a
/// final rem==2 group produces 3 bytes (its third index models over (b1, 0), which is
/// exactly upstream's `(input[start_of_rem + 1] << 2) & 0x3F`); a final rem==1 group
/// produces 2 bytes (its second index models over (b0, 0), exactly upstream's
/// `(input[start_of_rem] << 4) & 0x3F`). Positions outside any writable group model
/// as 0 (never claimed by a contract here).
pub open spec fn enc_tail_byte(symbols: Seq<u8>, input: Seq<u8>, input_index: int, j: int) -> u8 {
    let out0 = input_index / 3 * 4;
    let rel = j - out0;
    let g = rel / 4;
    let k = rel % 4;
    let base = input_index + 3 * g;
    if 0 <= base && base + 2 < input.len() {
        if k == 0 {
            symbols[enc_idx0(input[base]) as int]
        } else if k == 1 {
            symbols[enc_idx1(input[base], input[base + 1]) as int]
        } else if k == 2 {
            symbols[enc_idx2(input[base + 1], input[base + 2]) as int]
        } else {
            symbols[enc_idx3(input[base + 2]) as int]
        }
    } else if 0 <= base && base + 1 < input.len() {
        if k == 0 {
            symbols[enc_idx0(input[base]) as int]
        } else if k == 1 {
            symbols[enc_idx1(input[base], input[base + 1]) as int]
        } else {
            symbols[enc_idx2(input[base + 1], 0) as int]
        }
    } else if 0 <= base && base < input.len() {
        if k == 0 {
            symbols[enc_idx0(input[base]) as int]
        } else {
            symbols[enc_idx1(input[base], 0) as int]
        }
    } else {
        0
    }
}

/* ============================================================
 * Origin: general_purpose/mod.rs:306-309 `read_u64`
 * ============================================================ */

/* Origin Rust (mod.rs:158-159):
   const BLOCKS_PER_FAST_LOOP: usize = 4;
   const LOW_SIX_BITS: u64 = 0x3F;
   and mod.rs:231: const LOW_SIX_BITS_U8: u8 = 0x3F;
   (upstream declares them inside the fn bodies; hoisted to this file's module level) */
pub(crate) const BLOCKS_PER_FAST_LOOP: usize = 4;
pub(crate) const LOW_SIX_BITS: u64 = 0x3F;
pub(crate) const LOW_SIX_BITS_U8: u8 = 0x3F;

/// Big-endian composition model of read_u64: the 8 bytes as the u64
/// b0<<56 | b1<<48 | ... | b7 (the exact semantics of u64::from_be_bytes).
pub open spec fn read_u64_bv(
    b0: u8,
    b1: u8,
    b2: u8,
    b3: u8,
    b4: u8,
    b5: u8,
    b6: u8,
    b7: u8,
) -> u64 {
    let v0 = ((b0 as u64) << 56) | ((b1 as u64) << 48);
    let v1 = ((b2 as u64) << 40) | ((b3 as u64) << 32);
    let v2 = ((b4 as u64) << 24) | ((b5 as u64) << 16);
    let v3 = ((b6 as u64) << 8) | (b7 as u64);
    (v0 | v1) | (v2 | v3)
}

/* Origin Rust (mod.rs:306-309):
   #[inline]
   fn read_u64(s: &[u8]) -> u64 { u64::from_be_bytes(s[..8].try_into().unwrap()) }
   -- u64::from_be_bytes + try_into().unwrap() have no direct verus support (relax
      ledger lib.rs item 5): the byte collection is transcribed as the explicit
      8-byte big-endian bitwise composition, which is exactly from_be_bytes' defined
      semantics. Only called from the (unreachable) fast loop; still verified
      standalone here. */
pub exec fn read_u64(s: &[u8]) -> (r: u64)
    requires
        s@.len() >= 8,
    ensures
        r@ == read_u64_bv(s@[0], s@[1], s@[2], s@[3], s@[4], s@[5], s@[6], s@[7]),
{
    let v0 = ((s[0] as u64) << 56) | ((s[1] as u64) << 48);
    let v1 = ((s[2] as u64) << 40) | ((s[3] as u64) << 32);
    let v2 = ((s[4] as u64) << 24) | ((s[5] as u64) << 16);
    let v3 = ((s[6] as u64) << 8) | (s[7] as u64);
    let r = (v0 | v1) | (v2 | v3);
    r
}

/* ============================================================
 * Origin: general_purpose/mod.rs:166-226 -- the 4-x-u64 unrolled fast-loop
 * body, machine-levelized one u64 read at a time: each upstream unrolled
 * block (a `read_u64(&input_chunk[n..n+8])` followed by eight table stores
 * on the matching output_chunk segment) becomes the per-span exec helper
 * below; the fast loop calls it four times per iteration. The eight
 * output slots are proven and exported as eight ground conjuncts (the
 * per-slot cascade of the fast-path roadmap): no quantified position
 * clause remains inside the helper body or its ensures, so the call sites
 * consume the slot facts by ground arithmetic alone. The bit_vector
 * bridges spell the word composition inline as the antecedent of each
 * query (spec-level lets read uninterpreted inside bv extraction) and
 * keep every mask fully parenthesized.
 * ============================================================ */

pub(crate) exec fn fast_quad8(

    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    input_index: usize,
    read_base: usize,
    out_pos: usize,
) -> (r: ())

    requires

        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        (input_index as int) % 3 == 0,
        (input_index as int) <= (read_base as int),
        (read_base as int) % 3 == 0,
        ((read_base as int) + 8) <= (input@.len() as int),
        ((out_pos as int) + 8) <= (output@.len() as int),
        (out_pos as int) == (input_index as int) / 3 * 4

            + 4 * (((read_base as int) - (input_index as int)) / 3),
    ensures

        final(output)@.len() == old(output)@.len(),
        final(output)@ [((out_pos as int) + 0)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 0),
        ) && 32 <= final(output)@ [((out_pos as int) + 0)] <= 126,
        final(output)@ [((out_pos as int) + 1)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 1),
        ) && 32 <= final(output)@ [((out_pos as int) + 1)] <= 126,
        final(output)@ [((out_pos as int) + 2)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 2),
        ) && 32 <= final(output)@ [((out_pos as int) + 2)] <= 126,
        final(output)@ [((out_pos as int) + 3)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 3),
        ) && 32 <= final(output)@ [((out_pos as int) + 3)] <= 126,
        final(output)@ [((out_pos as int) + 4)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 4),
        ) && 32 <= final(output)@ [((out_pos as int) + 4)] <= 126,
        final(output)@ [((out_pos as int) + 5)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 5),
        ) && 32 <= final(output)@ [((out_pos as int) + 5)] <= 126,
        final(output)@ [((out_pos as int) + 6)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 6),
        ) && 32 <= final(output)@ [((out_pos as int) + 6)] <= 126,
        final(output)@ [((out_pos as int) + 7)] == enc_tail_byte(

            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 7),
        ) && 32 <= final(output)@ [((out_pos as int) + 7)] <= 126,
        forall|j: int|
            #![trigger final(output)@ [j]]
            ((0 <= j && j < (out_pos as int)) || (

                ((out_pos as int) + 8) <= j && j < old(output)@.len()

            )) ==> final(output)@ [j] == old(output)@ [j],
{

    let ghost g_symbols = symbols@;
    let ghost g_input = input@;
    let ghost g_out_old = old(output)@;
    let ghost g0 = ((read_base as int) - (input_index as int)) / 3;
    let ghost out0 = (input_index as int) / 3 * 4;
    proof {
        /* the span sits on the 3-byte group lattice; its read window covers
           both complete groups and the two raw cells past them */
        assert((read_base as int) == (input_index as int) + 3 * g0);
        assert((out_pos as int) == out0 + 4 * g0);
        assert(((read_base as int) + 2) < (g_input.len() as int));
        assert(((read_base as int) + 5) < (g_input.len() as int));
    }
    /* The eight input cells of the span, loaded as named locals (upstream
       reads exactly these cells through the input_chunk slab and read_u64). */
    let b0 = input[read_base + 0];
    let b1 = input[read_base + 1];
    let b2 = input[read_base + 2];
    let b3 = input[read_base + 3];
    let b4 = input[read_base + 4];
    let b5 = input[read_base + 5];
    let b6 = input[read_base + 6];
    let b7 = input[read_base + 7];
    proof {

        assert(b0 == g_input[((read_base as int) + 0) as int]);
        assert(b1 == g_input[((read_base as int) + 1) as int]);
        assert(b2 == g_input[((read_base as int) + 2) as int]);
        assert(b3 == g_input[((read_base as int) + 3) as int]);
        assert(b4 == g_input[((read_base as int) + 4) as int]);
        assert(b5 == g_input[((read_base as int) + 5) as int]);
        assert(b6 == g_input[((read_base as int) + 6) as int]);
        assert(b7 == g_input[((read_base as int) + 7) as int]);
        assert(((read_base as int) + 8) <= (g_input.len() as int));
    }
    /* Origin Rust (mod.rs:167-170): let input_chunk = &input[input_index..(input_index + 26)];
       let input_u64 = read_u64(&input_chunk[0..8]); */
    let input_u64 = read_u64(&input[read_base..(read_base + 8)]);
    proof {

        assert(input_u64@ == read_u64_bv(b0, b1, b2, b3, b4, b5, b6, b7));
        /* the word value under read_u64_bv's own grouping: read_u64's
           ensures plus the transparent definition give this tree; every
           bridge query below restates the same composition inline as its
           antecedent, so its consequent slots are usable int-land facts */
        assert(input_u64@ == ((((((b0 as u64) << 56) | ((b1 as u64) << 48)) | (((b2 as u64) << 40) | ((b3 as u64) << 32))) | ((((b4 as u64) << 24) | ((b5 as u64) << 16)) | (((b6 as u64) << 8) | (b7 as u64))))));
        /* the OR chain's associativity: the definition's grouping to the
           flat left-associative spelling the bridge queries restate (one
           bv query; the flat value is then an int-land fact) */
        assert((input_u64@ == (((((b0 as u64) << 56) | ((b1 as u64) << 48)) | (((b2 as u64) << 40) | ((b3 as u64) << 32))) | ((((b4 as u64) << 24) | ((b5 as u64) << 16)) | (((b6 as u64) << 8) | (b7 as u64))))) ==> ((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))))) by (bit_vector);
        assert(input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0)));
        /* the eight slot bridges: each query is self-contained (the word
           composition is the antecedent, restated inline) */
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 58) & 0x3F) == (((b0 as u64) >> 2))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 52) & 0x3F) == (((((b0 as u64) << 4) | ((b1 as u64) >> 4)) & 0x3F))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 46) & 0x3F) == (((((b1 as u64) << 2) | ((b2 as u64) >> 6)) & 0x3F))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 40) & 0x3F) == (((b2 as u64) & 0x3F))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 34) & 0x3F) == (((b3 as u64) >> 2))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 28) & 0x3F) == (((((b3 as u64) << 4) | ((b4 as u64) >> 4)) & 0x3F))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 22) & 0x3F) == (((((b4 as u64) << 2) | ((b5 as u64) >> 6)) & 0x3F))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> ((((((input_u64@) as u64) >> 16) & 0x3F) == (((b5 as u64) & 0x3F))))) by (bit_vector);
        /* the four shift-left model bridges: the spec-side u8 index
           expressions of the involved slots, cast against their u64 slot
           values (bv, guarded by the word composition) */
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> (((((((input_u64@) as u64) >> 52) & 0x3F) == ((((((b0 << 4) | (b1 >> 4)) & 0x3F))) as u64))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> (((((((input_u64@) as u64) >> 46) & 0x3F) == ((((((b1 << 2) | (b2 >> 6)) & 0x3F))) as u64))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> (((((((input_u64@) as u64) >> 28) & 0x3F) == ((((((b3 << 4) | (b4 >> 4)) & 0x3F))) as u64))))) by (bit_vector);
        assert((input_u64@ == (((b0 as u64) << 56) | ((b1 as u64) << 48) | ((b2 as u64) << 40) | ((b3 as u64) << 32) | ((b4 as u64) << 24) | ((b5 as u64) << 16) | ((b6 as u64) << 8) | ((b7 as u64) << 0))) ==> (((((((input_u64@) as u64) >> 22) & 0x3F) == ((((((b4 << 2) | (b5 >> 6)) & 0x3F))) as u64))))) by (bit_vector);
        /* the derived slot equalities, as int-land facts */
        assert(((((input_u64@) as u64) >> 58) & 0x3F) == (((b0 as u64) >> 2)));
        assert(((((input_u64@) as u64) >> 52) & 0x3F) == (((((b0 as u64) << 4) | ((b1 as u64) >> 4)) & 0x3F)));
        assert(((((input_u64@) as u64) >> 46) & 0x3F) == (((((b1 as u64) << 2) | ((b2 as u64) >> 6)) & 0x3F)));
        assert(((((input_u64@) as u64) >> 40) & 0x3F) == (((b2 as u64) & 0x3F)));
        assert(((((input_u64@) as u64) >> 34) & 0x3F) == (((b3 as u64) >> 2)));
        assert(((((input_u64@) as u64) >> 28) & 0x3F) == (((((b3 as u64) << 4) | ((b4 as u64) >> 4)) & 0x3F)));
        assert(((((input_u64@) as u64) >> 22) & 0x3F) == (((((b4 as u64) << 2) | ((b5 as u64) >> 6)) & 0x3F)));
        assert(((((input_u64@) as u64) >> 16) & 0x3F) == (((b5 as u64) & 0x3F)));
        /* the eight lookup index bounds (each masked slot value is < 64) */
        assert(((((input_u64@) as u64) >> 58) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 52) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 46) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 40) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 34) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 28) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 22) & 0x3F) < 64) by (bit_vector);
        assert(((((input_u64@) as u64) >> 16) & 0x3F) < 64) by (bit_vector);
    }
    /* Origin Rust (mod.rs:168-176): the eight symbol lookups of the u64 word.
       The inline lookup expressions are hoisted to named locals (the same
       expressions verbatim, LOW_SIX_BITS = 0x3F). */
    let idx0 = ((input_u64 >> 58) & LOW_SIX_BITS) as usize;
    let idx1 = ((input_u64 >> 52) & LOW_SIX_BITS) as usize;
    let idx2 = ((input_u64 >> 46) & LOW_SIX_BITS) as usize;
    let idx3 = ((input_u64 >> 40) & LOW_SIX_BITS) as usize;
    let idx4 = ((input_u64 >> 34) & LOW_SIX_BITS) as usize;
    let idx5 = ((input_u64 >> 28) & LOW_SIX_BITS) as usize;
    let idx6 = ((input_u64 >> 22) & LOW_SIX_BITS) as usize;
    let idx7 = ((input_u64 >> 16) & LOW_SIX_BITS) as usize;
    proof {

        assert(idx0@ == (((enc_idx0(b0)) as int)));
        assert(idx1@ == (((enc_idx1(b0, b1)) as int)));
        assert(idx2@ == (((enc_idx2(b1, b2)) as int)));
        assert(idx3@ == (((enc_idx3(b2)) as int)));
        assert(idx4@ == (((enc_idx0(b3)) as int)));
        assert(idx5@ == (((enc_idx1(b3, b4)) as int)));
        assert(idx6@ == (((enc_idx2(b4, b5)) as int)));
        assert(idx7@ == (((enc_idx3(b5)) as int)));
    }
    output[out_pos] = symbols[idx0];
    output[out_pos + 1] = symbols[idx1];
    output[out_pos + 2] = symbols[idx2];
    output[out_pos + 3] = symbols[idx3];
    output[out_pos + 4] = symbols[idx4];
    output[out_pos + 5] = symbols[idx5];
    output[out_pos + 6] = symbols[idx6];
    output[out_pos + 7] = symbols[idx7];
    proof {

        /* the group model at the written positions (g0 rides the 3-byte
           lattice; slots 4..7 step into group g0 + 1) */
        /* slot 0 */
        assert(((out_pos as int) + 0) - out0 == (4 * g0 + 0));
        assert((4 * g0 + 0) / 4 == g0 + 0);
        assert((4 * g0 + 0) % 4 == 0);
        assert((input_index as int) + 3 * (g0 + 0) == (read_base as int) + 0);
        assert(output@ [((out_pos as int) + 0)] == g_symbols[((enc_idx0(b0)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 0),
        ) == g_symbols[((enc_idx0(b0)) as int)]);
        assert(32 <= g_symbols[((enc_idx0(b0)) as int)] <= 126);
        /* slot 1 */
        assert(((out_pos as int) + 1) - out0 == (4 * g0 + 1));
        assert((4 * g0 + 1) / 4 == g0 + 0);
        assert((4 * g0 + 1) % 4 == 1);
        assert((input_index as int) + 3 * (g0 + 0) == (read_base as int) + 0);
        assert(output@ [((out_pos as int) + 1)] == g_symbols[((enc_idx1(b0, b1)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 1),
        ) == g_symbols[((enc_idx1(b0, b1)) as int)]);
        assert(32 <= g_symbols[((enc_idx1(b0, b1)) as int)] <= 126);
        /* slot 2 */
        assert(((out_pos as int) + 2) - out0 == (4 * g0 + 2));
        assert((4 * g0 + 2) / 4 == g0 + 0);
        assert((4 * g0 + 2) % 4 == 2);
        assert((input_index as int) + 3 * (g0 + 0) == (read_base as int) + 0);
        assert(output@ [((out_pos as int) + 2)] == g_symbols[((enc_idx2(b1, b2)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 2),
        ) == g_symbols[((enc_idx2(b1, b2)) as int)]);
        assert(32 <= g_symbols[((enc_idx2(b1, b2)) as int)] <= 126);
        /* slot 3 */
        assert(((out_pos as int) + 3) - out0 == (4 * g0 + 3));
        assert((4 * g0 + 3) / 4 == g0 + 0);
        assert((4 * g0 + 3) % 4 == 3);
        assert((input_index as int) + 3 * (g0 + 0) == (read_base as int) + 0);
        assert(output@ [((out_pos as int) + 3)] == g_symbols[((enc_idx3(b2)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 3),
        ) == g_symbols[((enc_idx3(b2)) as int)]);
        assert(32 <= g_symbols[((enc_idx3(b2)) as int)] <= 126);
        /* slot 4 */
        assert(((out_pos as int) + 4) - out0 == (4 * g0 + 4));
        assert((4 * g0 + 4) / 4 == g0 + 1);
        assert((4 * g0 + 4) % 4 == 0);
        assert((input_index as int) + 3 * (g0 + 1) == (read_base as int) + 3);
        assert(output@ [((out_pos as int) + 4)] == g_symbols[((enc_idx0(b3)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 4),
        ) == g_symbols[((enc_idx0(b3)) as int)]);
        assert(32 <= g_symbols[((enc_idx0(b3)) as int)] <= 126);
        /* slot 5 */
        assert(((out_pos as int) + 5) - out0 == (4 * g0 + 5));
        assert((4 * g0 + 5) / 4 == g0 + 1);
        assert((4 * g0 + 5) % 4 == 1);
        assert((input_index as int) + 3 * (g0 + 1) == (read_base as int) + 3);
        assert(output@ [((out_pos as int) + 5)] == g_symbols[((enc_idx1(b3, b4)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 5),
        ) == g_symbols[((enc_idx1(b3, b4)) as int)]);
        assert(32 <= g_symbols[((enc_idx1(b3, b4)) as int)] <= 126);
        /* slot 6 */
        assert(((out_pos as int) + 6) - out0 == (4 * g0 + 6));
        assert((4 * g0 + 6) / 4 == g0 + 1);
        assert((4 * g0 + 6) % 4 == 2);
        assert((input_index as int) + 3 * (g0 + 1) == (read_base as int) + 3);
        assert(output@ [((out_pos as int) + 6)] == g_symbols[((enc_idx2(b4, b5)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 6),
        ) == g_symbols[((enc_idx2(b4, b5)) as int)]);
        assert(32 <= g_symbols[((enc_idx2(b4, b5)) as int)] <= 126);
        /* slot 7 */
        assert(((out_pos as int) + 7) - out0 == (4 * g0 + 7));
        assert((4 * g0 + 7) / 4 == g0 + 1);
        assert((4 * g0 + 7) % 4 == 3);
        assert((input_index as int) + 3 * (g0 + 1) == (read_base as int) + 3);
        assert(output@ [((out_pos as int) + 7)] == g_symbols[((enc_idx3(b5)) as int)]);
        assert(enc_tail_byte(
            g_symbols,
            g_input,
            (input_index as int),
            ((out_pos as int) + 7),
        ) == g_symbols[((enc_idx3(b5)) as int)]);
        assert(32 <= g_symbols[((enc_idx3(b5)) as int)] <= 126);
        /* untouched outside the span */
        assert forall|j: int|

            ((0 <= j && j < (out_pos as int)) || (

                ((out_pos as int) + 8) <= j && j < g_out_old.len()

            )) ==> output@ [j] == g_out_old [j] by {
            assert(output@ [j] == output@ [j]);
        }
    }
    ()

}

/* ============================================================
 * Origin: general_purpose/mod.rs:167-223 -- one full iteration of the
 * 4-x-u64 fast loop as a single exec step: the four per-span helper calls
 * of one iteration, with their thirty-two output slots exported as ground
 * conjuncts (still no quantified position clause beyond the untouched-
 * outside clause, which is the cheap single-trigger shape). The loop
 * consumes this one ground contract, so its maintenance query carries a
 * single call state instead of four chained ones.
 * ============================================================ */
pub(crate) exec fn fast_step32(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    input_index: usize,
    read_base: usize,
    out_pos: usize,
) -> (r: ())
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        (input_index as int) % 3 == 0,
        (input_index as int) <= (read_base as int),
        (read_base as int) % 3 == 0,
        ((read_base as int) + 26) <= (input@.len() as int),
        ((out_pos as int) + 32) <= (output@.len() as int),
        (out_pos as int) == (input_index as int) / 3 * 4
            + 4 * (((read_base as int) - (input_index as int)) / 3),
    ensures
        final(output)@.len() == old(output)@.len(),
        final(output)@ [((out_pos as int) + 0)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 0),
        ) && 32 <= final(output)@ [((out_pos as int) + 0)] <= 126,
        final(output)@ [((out_pos as int) + 1)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 1),
        ) && 32 <= final(output)@ [((out_pos as int) + 1)] <= 126,
        final(output)@ [((out_pos as int) + 2)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 2),
        ) && 32 <= final(output)@ [((out_pos as int) + 2)] <= 126,
        final(output)@ [((out_pos as int) + 3)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 3),
        ) && 32 <= final(output)@ [((out_pos as int) + 3)] <= 126,
        final(output)@ [((out_pos as int) + 4)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 4),
        ) && 32 <= final(output)@ [((out_pos as int) + 4)] <= 126,
        final(output)@ [((out_pos as int) + 5)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 5),
        ) && 32 <= final(output)@ [((out_pos as int) + 5)] <= 126,
        final(output)@ [((out_pos as int) + 6)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 6),
        ) && 32 <= final(output)@ [((out_pos as int) + 6)] <= 126,
        final(output)@ [((out_pos as int) + 7)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 7),
        ) && 32 <= final(output)@ [((out_pos as int) + 7)] <= 126,
        final(output)@ [((out_pos as int) + 8)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 8),
        ) && 32 <= final(output)@ [((out_pos as int) + 8)] <= 126,
        final(output)@ [((out_pos as int) + 9)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 9),
        ) && 32 <= final(output)@ [((out_pos as int) + 9)] <= 126,
        final(output)@ [((out_pos as int) + 10)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 10),
        ) && 32 <= final(output)@ [((out_pos as int) + 10)] <= 126,
        final(output)@ [((out_pos as int) + 11)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 11),
        ) && 32 <= final(output)@ [((out_pos as int) + 11)] <= 126,
        final(output)@ [((out_pos as int) + 12)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 12),
        ) && 32 <= final(output)@ [((out_pos as int) + 12)] <= 126,
        final(output)@ [((out_pos as int) + 13)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 13),
        ) && 32 <= final(output)@ [((out_pos as int) + 13)] <= 126,
        final(output)@ [((out_pos as int) + 14)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 14),
        ) && 32 <= final(output)@ [((out_pos as int) + 14)] <= 126,
        final(output)@ [((out_pos as int) + 15)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 15),
        ) && 32 <= final(output)@ [((out_pos as int) + 15)] <= 126,
        final(output)@ [((out_pos as int) + 16)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 16),
        ) && 32 <= final(output)@ [((out_pos as int) + 16)] <= 126,
        final(output)@ [((out_pos as int) + 17)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 17),
        ) && 32 <= final(output)@ [((out_pos as int) + 17)] <= 126,
        final(output)@ [((out_pos as int) + 18)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 18),
        ) && 32 <= final(output)@ [((out_pos as int) + 18)] <= 126,
        final(output)@ [((out_pos as int) + 19)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 19),
        ) && 32 <= final(output)@ [((out_pos as int) + 19)] <= 126,
        final(output)@ [((out_pos as int) + 20)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 20),
        ) && 32 <= final(output)@ [((out_pos as int) + 20)] <= 126,
        final(output)@ [((out_pos as int) + 21)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 21),
        ) && 32 <= final(output)@ [((out_pos as int) + 21)] <= 126,
        final(output)@ [((out_pos as int) + 22)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 22),
        ) && 32 <= final(output)@ [((out_pos as int) + 22)] <= 126,
        final(output)@ [((out_pos as int) + 23)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 23),
        ) && 32 <= final(output)@ [((out_pos as int) + 23)] <= 126,
        final(output)@ [((out_pos as int) + 24)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 24),
        ) && 32 <= final(output)@ [((out_pos as int) + 24)] <= 126,
        final(output)@ [((out_pos as int) + 25)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 25),
        ) && 32 <= final(output)@ [((out_pos as int) + 25)] <= 126,
        final(output)@ [((out_pos as int) + 26)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 26),
        ) && 32 <= final(output)@ [((out_pos as int) + 26)] <= 126,
        final(output)@ [((out_pos as int) + 27)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 27),
        ) && 32 <= final(output)@ [((out_pos as int) + 27)] <= 126,
        final(output)@ [((out_pos as int) + 28)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 28),
        ) && 32 <= final(output)@ [((out_pos as int) + 28)] <= 126,
        final(output)@ [((out_pos as int) + 29)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 29),
        ) && 32 <= final(output)@ [((out_pos as int) + 29)] <= 126,
        final(output)@ [((out_pos as int) + 30)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 30),
        ) && 32 <= final(output)@ [((out_pos as int) + 30)] <= 126,
        final(output)@ [((out_pos as int) + 31)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 31),
        ) && 32 <= final(output)@ [((out_pos as int) + 31)] <= 126,
        forall|j: int|
            #![trigger final(output)@ [j]]
            ((0 <= j && j < (out_pos as int)) || (
                ((out_pos as int) + 32) <= j && j < old(output)@.len()
            )) ==> final(output)@ [j] == old(output)@ [j],
{
    proof {
        /* the span lattice over the iteration's four u64 reads */
        assert((((read_base as int) + 0)) - (input_index as int) == 3 * (((((read_base as int) - (input_index as int)) / 3) + 0)));
        assert((((read_base as int) + 0)) % 3 == 0);
        assert((((out_pos as int) + 0)) == (input_index as int) / 3 * 4 + 4 * (((((read_base as int) + 0)) - (input_index as int)) / 3));
        assert((input_index as int) <= (((read_base as int) + 0)));
        assert((((read_base as int) + 0)) + 8 <= input@.len() as int);
        assert(((((out_pos as int) + 0))) + 8 <= output@.len() as int);
        assert((((read_base as int) + 6)) - (input_index as int) == 3 * (((((read_base as int) - (input_index as int)) / 3) + 2)));
        assert((((read_base as int) + 6)) % 3 == 0);
        assert((((out_pos as int) + 8)) == (input_index as int) / 3 * 4 + 4 * (((((read_base as int) + 6)) - (input_index as int)) / 3));
        assert((input_index as int) <= (((read_base as int) + 6)));
        assert((((read_base as int) + 6)) + 8 <= input@.len() as int);
        assert(((((out_pos as int) + 8))) + 8 <= output@.len() as int);
        assert((((read_base as int) + 12)) - (input_index as int) == 3 * (((((read_base as int) - (input_index as int)) / 3) + 4)));
        assert((((read_base as int) + 12)) % 3 == 0);
        assert((((out_pos as int) + 16)) == (input_index as int) / 3 * 4 + 4 * (((((read_base as int) + 12)) - (input_index as int)) / 3));
        assert((input_index as int) <= (((read_base as int) + 12)));
        assert((((read_base as int) + 12)) + 8 <= input@.len() as int);
        assert(((((out_pos as int) + 16))) + 8 <= output@.len() as int);
        assert((((read_base as int) + 18)) - (input_index as int) == 3 * (((((read_base as int) - (input_index as int)) / 3) + 6)));
        assert((((read_base as int) + 18)) % 3 == 0);
        assert((((out_pos as int) + 24)) == (input_index as int) / 3 * 4 + 4 * (((((read_base as int) + 18)) - (input_index as int)) / 3));
        assert((input_index as int) <= (((read_base as int) + 18)));
        assert((((read_base as int) + 18)) + 8 <= input@.len() as int);
        assert(((((out_pos as int) + 24))) + 8 <= output@.len() as int);
        assert((read_base as int) + 26 <= input@.len() as int);
        assert((read_base as int) + 18 <= usize::MAX as int);
        assert((out_pos as int) + 24 <= output.len() as int);
    }
    fast_quad8(symbols, input, output, input_index, read_base + 0, out_pos + 0);
    fast_quad8(symbols, input, output, input_index, read_base + 6, out_pos + 8);
    fast_quad8(symbols, input, output, input_index, read_base + 12, out_pos + 16);
    fast_quad8(symbols, input, output, input_index, read_base + 18, out_pos + 24);
    proof {
        /* the thirty-two ground slots, restated on the iteration's final
           state (the untouched clauses of the later spans carry the
           earlier spans' bytes to this state) */
        assert(output@ [((out_pos as int) + 0)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 0),
        ) && 32 <= output@ [((out_pos as int) + 0)] <= 126);
        assert(output@ [((out_pos as int) + 1)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 1),
        ) && 32 <= output@ [((out_pos as int) + 1)] <= 126);
        assert(output@ [((out_pos as int) + 2)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 2),
        ) && 32 <= output@ [((out_pos as int) + 2)] <= 126);
        assert(output@ [((out_pos as int) + 3)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 3),
        ) && 32 <= output@ [((out_pos as int) + 3)] <= 126);
        assert(output@ [((out_pos as int) + 4)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 4),
        ) && 32 <= output@ [((out_pos as int) + 4)] <= 126);
        assert(output@ [((out_pos as int) + 5)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 5),
        ) && 32 <= output@ [((out_pos as int) + 5)] <= 126);
        assert(output@ [((out_pos as int) + 6)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 6),
        ) && 32 <= output@ [((out_pos as int) + 6)] <= 126);
        assert(output@ [((out_pos as int) + 7)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 7),
        ) && 32 <= output@ [((out_pos as int) + 7)] <= 126);
        assert(output@ [((out_pos as int) + 8)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 8),
        ) && 32 <= output@ [((out_pos as int) + 8)] <= 126);
        assert(output@ [((out_pos as int) + 9)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 9),
        ) && 32 <= output@ [((out_pos as int) + 9)] <= 126);
        assert(output@ [((out_pos as int) + 10)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 10),
        ) && 32 <= output@ [((out_pos as int) + 10)] <= 126);
        assert(output@ [((out_pos as int) + 11)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 11),
        ) && 32 <= output@ [((out_pos as int) + 11)] <= 126);
        assert(output@ [((out_pos as int) + 12)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 12),
        ) && 32 <= output@ [((out_pos as int) + 12)] <= 126);
        assert(output@ [((out_pos as int) + 13)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 13),
        ) && 32 <= output@ [((out_pos as int) + 13)] <= 126);
        assert(output@ [((out_pos as int) + 14)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 14),
        ) && 32 <= output@ [((out_pos as int) + 14)] <= 126);
        assert(output@ [((out_pos as int) + 15)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 15),
        ) && 32 <= output@ [((out_pos as int) + 15)] <= 126);
        assert(output@ [((out_pos as int) + 16)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 16),
        ) && 32 <= output@ [((out_pos as int) + 16)] <= 126);
        assert(output@ [((out_pos as int) + 17)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 17),
        ) && 32 <= output@ [((out_pos as int) + 17)] <= 126);
        assert(output@ [((out_pos as int) + 18)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 18),
        ) && 32 <= output@ [((out_pos as int) + 18)] <= 126);
        assert(output@ [((out_pos as int) + 19)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 19),
        ) && 32 <= output@ [((out_pos as int) + 19)] <= 126);
        assert(output@ [((out_pos as int) + 20)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 20),
        ) && 32 <= output@ [((out_pos as int) + 20)] <= 126);
        assert(output@ [((out_pos as int) + 21)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 21),
        ) && 32 <= output@ [((out_pos as int) + 21)] <= 126);
        assert(output@ [((out_pos as int) + 22)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 22),
        ) && 32 <= output@ [((out_pos as int) + 22)] <= 126);
        assert(output@ [((out_pos as int) + 23)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 23),
        ) && 32 <= output@ [((out_pos as int) + 23)] <= 126);
        assert(output@ [((out_pos as int) + 24)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 24),
        ) && 32 <= output@ [((out_pos as int) + 24)] <= 126);
        assert(output@ [((out_pos as int) + 25)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 25),
        ) && 32 <= output@ [((out_pos as int) + 25)] <= 126);
        assert(output@ [((out_pos as int) + 26)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 26),
        ) && 32 <= output@ [((out_pos as int) + 26)] <= 126);
        assert(output@ [((out_pos as int) + 27)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 27),
        ) && 32 <= output@ [((out_pos as int) + 27)] <= 126);
        assert(output@ [((out_pos as int) + 28)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 28),
        ) && 32 <= output@ [((out_pos as int) + 28)] <= 126);
        assert(output@ [((out_pos as int) + 29)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 29),
        ) && 32 <= output@ [((out_pos as int) + 29)] <= 126);
        assert(output@ [((out_pos as int) + 30)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 30),
        ) && 32 <= output@ [((out_pos as int) + 30)] <= 126);
        assert(output@ [((out_pos as int) + 31)] == enc_tail_byte(
            symbols@,
            input@,
            (input_index as int),
            ((out_pos as int) + 31),
        ) && 32 <= output@ [((out_pos as int) + 31)] <= 126);
        assert forall|j: int|
            ((0 <= j && j < (out_pos as int)) || (
                ((out_pos as int) + 32) <= j && j < old(output)@.len()
            )) ==> output@ [j] == old(output)@ [j] by {
            assert(output@ [j] == output@ [j]);
        }
    }
    ()
}

/* ============================================================
 * Origin: general_purpose/mod.rs:151-269 `encode_scalar_tail`
 * ============================================================ */

/// Upstream doc (mod.rs:149-150):
///   Scalar encode of `input[input_index..]` into `output[output_index..]`, resuming from a 3-byte
///   group boundary. Returns the total number of output bytes written.
/// Transcription notes:
/// - the resume boundary facts are exactly the upstream debug_asserts of encode_helper
///   (mod.rs:135-144): input_index % 3 == 0, output_index == input_index / 3 * 4,
///   input_index <= input.len(), and output room for the whole remaining unpadded
///   encoding (the last two debug_assert its "% 3" family implies).
/// - the encode_table parameter is monomorphized per the relax ledger (lib.rs item 3):
///   `encode_table: &[u8; 64]` -> `symbols: &[u8]` with the ValidAlphabetSymbols model
///   constraint (the table IS the symbols sequence, see build_encode_table in mod.rs).
/// - domain: the full one (any input length; see the file header note).
/* rlimit note (ledgered raise, this fn only): the fast-loop maintenance query
   needs rlimit 100 for the heaviest harness-panel SMT context, 80 for the
   shortest-length chain panels and 40 for the whole-tree driver under this
   toolchain build (default is 10); every sibling
   obligation in this file verifies at the default budget, and the two
   architectures that tried to split the query (four span calls consumed
   directly by the loop / per-span mid-state invariant asserts) stayed over
   budget at default; consumed single-step summary (fast_step32) is the
   minimal form found. */
#[verifier::rlimit(100)]
pub exec fn encode_scalar_tail(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    input_index: usize,
    output_index: usize,
) -> (r: usize)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        input_index % 3 == 0,
        output_index == input_index / 3 * 4,
        input_index <= input@.len(),
        output@.len()
            >= (output_index as int) + tail_unpadded_len(input@.len() - (input_index as int)),
    ensures
        r@ == (output_index as int) + tail_unpadded_len(
            input@.len() - (input_index as int),
        ),
        forall|j: int|
            (output_index as int) <= j < r@ ==> final(output)@ [j] == enc_tail_byte(
                symbols@,
                input@,
                (input_index as int),
                j,
            ),
        forall|j: int|
            #![trigger final(output)@ [j]]
            r@ <= j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j],
        forall|j: int|
            #![trigger final(output)@ [j]]
            (output_index as int) <= j < r@ ==> 32 <= final(output)@ [j] <= 126,
        final(output)@.len() == old(output)@.len(),
{
    let ghost g_symbols = symbols@;
    let ghost g_input = input@;
    let ghost g_out_old = old(output)@;
    /* Origin Rust: `mut input_index` / `mut output_index` fn params -> local mirrors */
    let mut ii: usize = input_index;
    let mut out_idx: usize = output_index;

    /* Origin Rust (mod.rs:161-163):
       // we read 8 bytes at a time (u64) but only actually consume 6 of those bytes. Thus, we need
       // 2 trailing bytes to be available to read..
       let last_fast_index = input.len().saturating_sub(BLOCKS_PER_FAST_LOOP * 6 + 2);
       -- saturating_sub expanded into an explicit saturation guard (relax ledger
          lib.rs item 4); BLOCKS_PER_FAST_LOOP * 6 + 2 == 26 */
    let last_fast_index: usize = if input.len() >= 26 {
        input.len() - 26
    } else {
        0
    };

    /* The live fast loop: entered for inputs longer than 26 bytes. The
       per-span helper closes each u64 read's eight slots; the loop side
       re-extends its region invariants through 32 ground slot facts and a
       slot-per-slot cascade (the loop consumes the helper's ground ensures
       conjuncts directly; the untouched-outside clause chains the earlier
       spans' facts across the later ones of the same iteration). */
    if last_fast_index > 0 {
        proof {
            assert((input.len() as int) >= 26);
            assert((input.len() as int) >= 27);
            assert((last_fast_index as int) == (input.len() as int) - 26);
        }
        /* Origin Rust (mod.rs:166-226): the 4-x-u64 fast loop, verbatim
           structure (input_index/output_index are the mirrored ii/out_idx;
           each upstream unrolled u64 block is the per-span helper call) */
        while ii <= last_fast_index
            invariant
                symbols@.len() == 64,
                g_symbols == symbols@,
                ValidAlphabetSymbols(g_symbols),
                g_input == input@,
                g_out_old == old(output)@,
                output@.len() == g_out_old.len(),
                (input_index as int) % 3 == 0,
                (input_index as int) <= g_input.len(),
                (output_index as int) == (input_index as int) / 3 * 4,
                (output_index as int) + tail_unpadded_len(
                    g_input.len() - (input_index as int),
                ) <= output@.len(),
                (g_input.len() as int) >= 27,
                (last_fast_index as int) == (g_input.len() as int) - 26,
                (ii as int) % 3 == 0,
                (input_index as int) <= (ii as int),
                ((ii as int) <= (last_fast_index as int) + 24) || (
                    (ii as int) == (input_index as int)
                ),
                (out_idx as int) == (output_index as int) + 4 * (((ii as int) - (input_index as int)) / 3),
                forall|j: int|
                    #![trigger output@ [j]] (
                    ((output_index as int) <= j < (out_idx as int) ==> output@ [j] == enc_tail_byte(
                        g_symbols,
                        g_input,
                        (input_index as int),
                        j,
                    ) && ((output_index as int) <= j < (out_idx as int) ==> 32 <= output@ [j] <= 126))
                        && ((out_idx as int) <= j < g_out_old.len() ==> output@ [j] == g_out_old [j])
                ),
                (out_idx as int) + tail_unpadded_len(
                    g_input.len() - (ii as int),
                ) <= output@.len(),
            decreases (last_fast_index as int) + 24 - (ii as int)
        {
            proof {
                /* the loop guard: a full 26-byte window remains in the input */
                assert((ii as int) <= (last_fast_index as int));
                assert(((ii as int) + 26) <= (g_input.len() as int));
                let n = g_input.len() - (ii as int);
                assert(n >= 26);
                assert(n / 3 >= 8);
                /* the output tail from ii covers at least eight full groups */
                assert(tail_unpadded_len(n) >= 32);
                assert(((out_idx as int) + 32) <= output@.len());
            }
            /* the four u64 spans of this iteration, anchored at the current
               bases */
            let pre_base = out_idx;
            proof {
                assert((pre_base as int) == (out_idx as int));
                assert(((ii as int) + 18) <= usize::MAX as int);
                assert(((pre_base as int) + 24) <= (output.len() as int));
                assert(((out_idx as int) + 32) <= (output.len() as int));
            }
            fast_step32(symbols, input, output, input_index, ii, pre_base);
            /* Origin Rust (mod.rs:224-225) */
            out_idx += BLOCKS_PER_FAST_LOOP * 8;
            ii += BLOCKS_PER_FAST_LOOP * 6;
            proof {
                /* 32 pattern-shaped slot facts: the four span contracts'
                   ground conjuncts, restated at the fresh window's offsets
                   (the untouched clauses of the later spans preserve the
                   earlier spans' bytes) */
                assert(output@ [((pre_base as int) + 0)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 0),
                ) && 32 <= output@ [((pre_base as int) + 0)] <= 126);
                assert(output@ [((pre_base as int) + 1)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 1),
                ) && 32 <= output@ [((pre_base as int) + 1)] <= 126);
                assert(output@ [((pre_base as int) + 2)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 2),
                ) && 32 <= output@ [((pre_base as int) + 2)] <= 126);
                assert(output@ [((pre_base as int) + 3)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 3),
                ) && 32 <= output@ [((pre_base as int) + 3)] <= 126);
                assert(output@ [((pre_base as int) + 4)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 4),
                ) && 32 <= output@ [((pre_base as int) + 4)] <= 126);
                assert(output@ [((pre_base as int) + 5)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 5),
                ) && 32 <= output@ [((pre_base as int) + 5)] <= 126);
                assert(output@ [((pre_base as int) + 6)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 6),
                ) && 32 <= output@ [((pre_base as int) + 6)] <= 126);
                assert(output@ [((pre_base as int) + 7)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 7),
                ) && 32 <= output@ [((pre_base as int) + 7)] <= 126);
                assert(output@ [((pre_base as int) + 8)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 8),
                ) && 32 <= output@ [((pre_base as int) + 8)] <= 126);
                assert(output@ [((pre_base as int) + 9)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 9),
                ) && 32 <= output@ [((pre_base as int) + 9)] <= 126);
                assert(output@ [((pre_base as int) + 10)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 10),
                ) && 32 <= output@ [((pre_base as int) + 10)] <= 126);
                assert(output@ [((pre_base as int) + 11)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 11),
                ) && 32 <= output@ [((pre_base as int) + 11)] <= 126);
                assert(output@ [((pre_base as int) + 12)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 12),
                ) && 32 <= output@ [((pre_base as int) + 12)] <= 126);
                assert(output@ [((pre_base as int) + 13)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 13),
                ) && 32 <= output@ [((pre_base as int) + 13)] <= 126);
                assert(output@ [((pre_base as int) + 14)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 14),
                ) && 32 <= output@ [((pre_base as int) + 14)] <= 126);
                assert(output@ [((pre_base as int) + 15)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 15),
                ) && 32 <= output@ [((pre_base as int) + 15)] <= 126);
                assert(output@ [((pre_base as int) + 16)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 16),
                ) && 32 <= output@ [((pre_base as int) + 16)] <= 126);
                assert(output@ [((pre_base as int) + 17)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 17),
                ) && 32 <= output@ [((pre_base as int) + 17)] <= 126);
                assert(output@ [((pre_base as int) + 18)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 18),
                ) && 32 <= output@ [((pre_base as int) + 18)] <= 126);
                assert(output@ [((pre_base as int) + 19)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 19),
                ) && 32 <= output@ [((pre_base as int) + 19)] <= 126);
                assert(output@ [((pre_base as int) + 20)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 20),
                ) && 32 <= output@ [((pre_base as int) + 20)] <= 126);
                assert(output@ [((pre_base as int) + 21)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 21),
                ) && 32 <= output@ [((pre_base as int) + 21)] <= 126);
                assert(output@ [((pre_base as int) + 22)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 22),
                ) && 32 <= output@ [((pre_base as int) + 22)] <= 126);
                assert(output@ [((pre_base as int) + 23)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 23),
                ) && 32 <= output@ [((pre_base as int) + 23)] <= 126);
                assert(output@ [((pre_base as int) + 24)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 24),
                ) && 32 <= output@ [((pre_base as int) + 24)] <= 126);
                assert(output@ [((pre_base as int) + 25)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 25),
                ) && 32 <= output@ [((pre_base as int) + 25)] <= 126);
                assert(output@ [((pre_base as int) + 26)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 26),
                ) && 32 <= output@ [((pre_base as int) + 26)] <= 126);
                assert(output@ [((pre_base as int) + 27)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 27),
                ) && 32 <= output@ [((pre_base as int) + 27)] <= 126);
                assert(output@ [((pre_base as int) + 28)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 28),
                ) && 32 <= output@ [((pre_base as int) + 28)] <= 126);
                assert(output@ [((pre_base as int) + 29)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 29),
                ) && 32 <= output@ [((pre_base as int) + 29)] <= 126);
                assert(output@ [((pre_base as int) + 30)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 30),
                ) && 32 <= output@ [((pre_base as int) + 30)] <= 126);
                assert(output@ [((pre_base as int) + 31)] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    ((pre_base as int) + 31),
                ) && 32 <= output@ [((pre_base as int) + 31)] <= 126);
                /* the fresh-window extension, slot by slot (the cascade
                   grounds every case of jj in the window on the facts
                   above; the else is unreachable arithmetic) */
                assert forall|jj: int|
                    ((pre_base as int) <= jj && jj < ((pre_base as int) + 32)) implies
                        output@ [jj]
                        == enc_tail_byte(g_symbols, g_input, (input_index as int), jj)
                        && 32 <= output@ [jj] <= 126 by {
                    if jj == ((pre_base as int)) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 1) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 2) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 3) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 4) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 5) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 6) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 7) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 8) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 9) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 10) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 11) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 12) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 13) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 14) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 15) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 16) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 17) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 18) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 19) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 20) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 21) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 22) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 23) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 24) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 25) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 26) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 27) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 28) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 29) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 30) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else if jj == ((pre_base as int) + 31) {
                        assert(output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126);
                    } else {
                        assert(false);
                    }
                }
                /* region extension over the past groups and the untouched
                   tail beyond the fresh window: two implies-shaped
                   quantifier claims, one trigger pattern each */
                assert forall|jj: int|
                    #![trigger output@ [jj]]
                    ((output_index as int) <= jj && jj < ((pre_base as int) + 32)) implies
                        output@ [jj] == enc_tail_byte(
                            g_symbols,
                            g_input,
                            (input_index as int),
                            jj,
                        ) && 32 <= output@ [jj] <= 126
                by {
                    assert(output@ [jj] == output@ [jj]);
                }
                assert forall|jj: int|
                    #![trigger output@ [jj]]
                    ((((pre_base as int) + 32) <= jj) && (jj < g_out_old.len())) implies
                        output@ [jj] == g_out_old [jj]
                by {
                    assert(output@ [jj] == output@ [jj]);
                }
            }
        }
        /* fast-loop exit: the slow loop resumes at ii; when the fast loop
           never entered, ii is still input_index (the region invariants
           carry unchanged) */
        proof {
            /* ii sits on the group lattice no higher than start_of_rem */
            assert(ii as int % 3 == 0);
            assert(g_input.len() as int >= 27);
            assert(((ii as int) <= (g_input.len() as int) - 2) || (
                (ii as int) == (input_index as int)
            ));
            assert((g_input.len() as int) - ((g_input.len() as int) % 3) >= (
                (g_input.len() as int) - 2
            ));
            assert((ii as int) <= (g_input.len() as int) - ((g_input.len() as int) % 3));
        }
    }

    /* Origin Rust (mod.rs:229-251): encode what's left after the fast loop
       (LOW_SIX_BITS_U8 hoisted above)
       let rem = input.len() % 3;
       let start_of_rem = input.len() - rem;
       // start at the first index not handled by fast loop, which may be 0.
       while input_index < start_of_rem { ... }
       -- the rem==2 / rem==1 tail branches are below; the machine desugaring
          follows the file conventions (assert bridges for % / by constants) */
    let rem = input.len() % 3;
    assert(rem as int == g_input.len() % 3);
    /* no underflow: rem == input.len() % 3 <= input.len() */
    let start_of_rem = input.len() - rem;
    assert(start_of_rem as int == g_input.len() - rem as int);
    assert(start_of_rem as int <= g_input.len());

    /* Origin Rust (mod.rs:238-251):
       while input_index < start_of_rem {
           let input_chunk = &input[input_index..(input_index + 3)];
           let output_chunk = &mut output[output_index..(output_index + 4)];
           output_chunk[0] = encode_table[(input_chunk[0] >> 2) as usize];
           output_chunk[1] = encode_table[((input_chunk[0] << 4 | input_chunk[1] >> 4)
               & LOW_SIX_BITS_U8) as usize];
           output_chunk[2] = encode_table[((input_chunk[1] << 2 | input_chunk[2] >> 6)
               & LOW_SIX_BITS_U8) as usize];
           output_chunk[3] = encode_table[(input_chunk[2] & LOW_SIX_BITS_U8) as usize];
           input_index += 3;
           output_index += 4;
       }
       -- sub-slicing transcribed as direct index reads (the rewrite family of
          decode_chunk_4 / the naive engine); the bit expressions are verbatim */
    while ii < start_of_rem
        invariant
            symbols@.len() == 64,
            g_symbols == symbols@,
            ValidAlphabetSymbols(g_symbols),
            g_input == input@,
            g_out_old == old(output)@,
            output@.len() == g_out_old.len(),
            (input_index as int) % 3 == 0,
            (input_index as int) <= g_input.len(),
            (output_index as int) == (input_index as int) / 3 * 4,
            (rem as int) == g_input.len() % 3,
            (start_of_rem as int) == g_input.len() - g_input.len() % 3,
            (ii as int) % 3 == 0,
            (input_index as int) <= (ii as int),
            (ii as int) <= (start_of_rem as int),
            (out_idx as int) == (output_index as int) + 4 * (((ii as int) - (input_index as int)) / 3),
            forall|j: int|
                (output_index as int) <= j < (out_idx as int) ==> output@ [j] == enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    j,
                ),
            forall|j: int|
                #![trigger output@ [j]]
                (output_index as int) <= j < (out_idx as int) ==> 32 <= output@ [j] <= 126,
            forall|j: int|
                (out_idx as int) <= j < g_out_old.len() ==> output@ [j] == g_out_old [j],
            (out_idx as int) + tail_unpadded_len(g_input.len() - (ii as int)) <= output@.len(),
        decreases (start_of_rem as int) - (ii as int)
    {
        proof {
            /* loop guard, machine to spec: a full 3-byte group is still available */
            assert(((ii as int) + 3) <= (start_of_rem as int));
            let n = g_input.len() - (ii as int);
            assert(n >= 3);
            /* room for this group's 4 output bytes */
            assert(tail_unpadded_len(n) >= 4);
            assert((out_idx as int) + 4 <= output@.len());
        }
        let b0 = input[ii];
        let b1 = input[ii + 1];
        let b2 = input[ii + 2];
        assert(b0 == g_input[(ii) as int]);
        assert(b1 == g_input[((ii as int) + 1) as int]);
        assert(b2 == g_input[((ii as int) + 2) as int]);
        /* Origin Rust (mod.rs:242-247): the four 6-bit index lookups, verbatim */
        let i0 = (b0 >> 2) as usize;
        let i1 = ((b0 << 4 | b1 >> 4) & LOW_SIX_BITS_U8) as usize;
        let i2 = ((b1 << 2 | b2 >> 6) & LOW_SIX_BITS_U8) as usize;
        let i3 = (b2 & LOW_SIX_BITS_U8) as usize;
        proof {
            assert((b0 >> 2) < 64) by (bit_vector);
            assert(((b0 << 4) | (b1 >> 4)) & 0x3F < 64) by (bit_vector);
            assert(((b1 << 2) | (b2 >> 6)) & 0x3F < 64) by (bit_vector);
            assert((b2 & 0x3F) < 64) by (bit_vector);
        }
        output[out_idx] = symbols[i0];
        output[out_idx + 1] = symbols[i1];
        output[out_idx + 2] = symbols[i2];
        output[out_idx + 3] = symbols[i3];
        proof {
            /* written bytes == the 6-bit group model at the base of this group */
            assert(output@[(out_idx as int)] == g_symbols[enc_idx0(b0) as int]);
            assert(output@[(out_idx as int) + 1] == g_symbols[enc_idx1(b0, b1) as int]);
            assert(output@[(out_idx as int) + 2] == g_symbols[enc_idx2(b1, b2) as int]);
            assert(output@[(out_idx as int) + 3] == g_symbols[enc_idx3(b2) as int]);
            /* model reduction: output position out_idx + k is group g, slot k */
            let out0 = (input_index as int) / 3 * 4;
            let g = ((ii as int) - (input_index as int)) / 3;
            assert((ii as int) == (input_index as int) + 3 * g);
            assert((out_idx as int) == out0 + 4 * g);
            assert(((ii as int) + 2) < g_input.len());
            assert((4 * g) / 4 == g);
            assert((4 * g) % 4 == 0);
            assert((4 * g + 1) / 4 == g);
            assert((4 * g + 1) % 4 == 1);
            assert((4 * g + 2) / 4 == g);
            assert((4 * g + 2) % 4 == 2);
            assert((4 * g + 3) / 4 == g);
            assert((4 * g + 3) % 4 == 3);
            assert(
                enc_tail_byte(g_symbols, g_input, (input_index as int), (out_idx as int))
                    == g_symbols[(b0 >> 2) as int]
            );
            assert(
                enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    (out_idx as int) + 1,
                ) == g_symbols[(((b0 << 4) | (b1 >> 4)) & 0x3F) as int]
            );
            assert(
                enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    (out_idx as int) + 2,
                ) == g_symbols[(((b1 << 2) | (b2 >> 6)) & 0x3F) as int]
            );
            assert(
                enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    (out_idx as int) + 3,
                ) == g_symbols[(b2 & 0x3F) as int]
            );
            /* printable ASCII straight from ValidAlphabetSymbols */
            assert(32 <= g_symbols[(b0 >> 2) as int] <= 126);
            assert(32 <= g_symbols[(((b0 << 4) | (b1 >> 4)) & 0x3F) as int] <= 126);
            assert(32 <= g_symbols[(((b1 << 2) | (b2 >> 6)) & 0x3F) as int] <= 126);
            assert(32 <= g_symbols[(b2 & 0x3F) as int] <= 126);
            /* region invariant at the end of this iteration */
            assert forall|jj: int|
                (output_index as int) <= jj < ((out_idx as int) + 4) ==> (output@ [jj]
                    == enc_tail_byte(g_symbols, g_input, (input_index as int), jj)
                    && 32 <= output@ [jj] <= 126) by {
                assert(output@ [jj] == output@ [jj]);
            }
        }
        /* Origin Rust (mod.rs:249-250) */
        ii += 3;
        out_idx += 4;
        /* headroom after the step: the remaining tail shrinks by exactly one group */
        proof {
            let n_prev = g_input.len() - ((ii as int) - 3);
            let n_rem = g_input.len() - (ii as int);
            assert(n_prev == n_rem + 3);
            assert(n_prev >= 3);
            assert(n_prev % 3 == n_rem % 3);
            assert(n_prev / 3 == n_rem / 3 + 1);
            assert(tail_unpadded_len(n_prev) == tail_unpadded_len(n_rem) + 4);
        }
    }

    /* loop exit: ii == start_of_rem (the loop walks whole 3-byte groups) */
    proof {
        assert(((start_of_rem as int) - (ii as int)) < 3);
        assert(((start_of_rem as int) - (ii as int)) % 3 == 0);
        assert((ii as int) == (start_of_rem as int));
        assert((g_input.len()) - (ii as int) == (rem as int));
    }

    /* Origin Rust (mod.rs:253-266):
       if rem == 2 {
           output[output_index] = encode_table[(input[start_of_rem] >> 2) as usize];
           output[output_index + 1] = encode_table[((input[start_of_rem] << 4
               | input[start_of_rem + 1] >> 4) & LOW_SIX_BITS_U8) as usize];
           output[output_index + 2] = encode_table[((input[start_of_rem + 1] << 2)
               & LOW_SIX_BITS_U8) as usize];
           output_index += 3;
       } else if rem == 1 { ... }
       -- verbatim; the sub-slicing reads become direct index reads as above */
    if rem == 2 {
        proof {
            assert((rem as int) == 2);
            assert(((start_of_rem as int) + 1) < g_input.len());
            let out0 = (input_index as int) / 3 * 4;
            let g = ((ii as int) - (input_index as int)) / 3;
            assert(3 * g == ((ii as int) - (input_index as int)));
            let base = (input_index as int) + 3 * g;
            assert(base == (start_of_rem as int));
            assert((out_idx as int) == (out0 + 4 * g));
            /* room: tail_unpadded_len(rem == 2) == 3 */
            assert(tail_unpadded_len((rem as int)) == 3);
            assert(((out_idx as int) + 3) <= output@.len());
        }
        let b0 = input[start_of_rem];
        let b1 = input[start_of_rem + 1];
        assert(b0 == g_input[(start_of_rem) as int]);
        assert(b1 == g_input[((start_of_rem as int) + 1) as int]);
        /* Origin Rust (mod.rs:254-259): the three writes, verbatim */
        let i0 = (b0 >> 2) as usize;
        let i1 = ((b0 << 4 | b1 >> 4) & LOW_SIX_BITS_U8) as usize;
        let i2 = ((b1 << 2) & LOW_SIX_BITS_U8) as usize;
        proof {
            assert((b0 >> 2) < 64) by (bit_vector);
            assert(((b0 << 4) | (b1 >> 4)) & 0x3F < 64) by (bit_vector);
            /* the third index models over the zero virtual neighbor byte:
               enc_idx2(b1, 0) == (b1 << 2) & 0x3F */
            assert(enc_idx2(b1, 0) == ((b1 << 2) & 0x3F)) by (bit_vector);
            assert(((b1 << 2) & 0x3F) < 64) by (bit_vector);
        }
        output[out_idx] = symbols[i0];
        output[out_idx + 1] = symbols[i1];
        output[out_idx + 2] = symbols[i2];
        proof {
            assert(output@.len() == g_out_old.len());
            assert(output@[(out_idx as int)] == g_symbols[enc_idx0(b0) as int]);
            assert(output@[(out_idx as int) + 1] == g_symbols[enc_idx1(b0, b1) as int]);
            assert(output@[(out_idx as int) + 2] == g_symbols[enc_idx2(b1, 0) as int]);
            let g = ((ii as int) - (input_index as int)) / 3;
            assert(
                enc_tail_byte(g_symbols, g_input, (input_index as int), (out_idx as int))
                    == g_symbols[(b0 >> 2) as int]
            );
            assert(
                enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    (out_idx as int) + 1,
                ) == g_symbols[(((b0 << 4) | (b1 >> 4)) & 0x3F) as int]
            );
            assert(
                enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    (out_idx as int) + 2,
                ) == g_symbols[enc_idx2(b1, 0) as int]
            );
            assert(32 <= g_symbols[(b0 >> 2) as int] <= 126);
            assert(32 <= g_symbols[(((b0 << 4) | (b1 >> 4)) & 0x3F) as int] <= 126);
            assert(32 <= g_symbols[((b1 << 2) & 0x3F) as int] <= 126);
            assert forall|jj: int|
                (output_index as int) <= jj < ((out_idx as int) + 3) ==> (output@ [jj]
                    == enc_tail_byte(g_symbols, g_input, (input_index as int), jj)
                    && 32 <= output@ [jj] <= 126) by {
                assert(output@ [jj] == output@ [jj]);
            }
        }
        /* Origin Rust (mod.rs:260) */
        out_idx += 3;
    } else if rem == 1 {
        proof {
            assert((rem as int) == 1);
            assert((start_of_rem as int) < g_input.len());
            let g = ((ii as int) - (input_index as int)) / 3;
            assert(3 * g == ((ii as int) - (input_index as int)));
            let base = (input_index as int) + 3 * g;
            assert(base == (start_of_rem as int));
            /* room: tail_unpadded_len(rem == 1) == 2 */
            assert(tail_unpadded_len((rem as int)) == 2);
            assert(((out_idx as int) + 2) <= output@.len());
        }
        let b0 = input[start_of_rem];
        assert(b0 == g_input[(start_of_rem) as int]);
        /* Origin Rust (mod.rs:262-264): the two writes, verbatim */
        let i0 = (b0 >> 2) as usize;
        let i1 = ((b0 << 4) & LOW_SIX_BITS_U8) as usize;
        proof {
            assert((b0 >> 2) < 64) by (bit_vector);
            /* the second index models over the zero virtual neighbor byte:
               enc_idx1(b0, 0) == (b0 << 4) & 0x3F */
            assert(enc_idx1(b0, 0) == ((b0 << 4) & 0x3F)) by (bit_vector);
            assert(((b0 << 4) & 0x3F) < 64) by (bit_vector);
        }
        output[out_idx] = symbols[i0];
        output[out_idx + 1] = symbols[i1];
        proof {
            assert(output@.len() == g_out_old.len());
            assert(output@[(out_idx as int)] == g_symbols[enc_idx0(b0) as int]);
            assert(output@[(out_idx as int) + 1] == g_symbols[enc_idx1(b0, 0) as int]);
            assert(
                enc_tail_byte(g_symbols, g_input, (input_index as int), (out_idx as int))
                    == g_symbols[(b0 >> 2) as int]
            );
            assert(
                enc_tail_byte(
                    g_symbols,
                    g_input,
                    (input_index as int),
                    (out_idx as int) + 1,
                ) == g_symbols[(((b0 << 4)) & 0x3F) as int]
            );
            assert(32 <= g_symbols[(b0 >> 2) as int] <= 126);
            assert(32 <= g_symbols[((b0 << 4) & 0x3F) as int] <= 126);
            assert forall|jj: int|
                (output_index as int) <= jj < ((out_idx as int) + 2) ==> (output@ [jj]
                    == enc_tail_byte(g_symbols, g_input, (input_index as int), jj)
                    && 32 <= output@ [jj] <= 126) by {
                assert(output@ [jj] == output@ [jj]);
            }
        }
        /* Origin Rust (mod.rs:265) */
        out_idx += 2;
    }

    /* total written == output_index + tail_unpadded_len(input.len() - input_index)
       (the fn's return is the write count, byte count model above) */
    proof {
        assert(output@.len() == g_out_old.len());
        let n = g_input.len() - (input_index as int);
        let g = ((ii as int) - (input_index as int)) / 3;
        assert((n % 3) == (rem as int));
        assert(n == 3 * g + (rem as int));
        assert((n / 3) == g);
        let extra: int = if (rem as int) == 2 {
            3
        } else if (rem as int) == 1 {
            2
        } else {
            0
        };
        assert(tail_unpadded_len(n) == 4 * g + extra);
        assert((out_idx as int) == (output_index as int) + 4 * g + extra);
        assert((out_idx as int) == (output_index as int) + tail_unpadded_len(n));
        assert forall|j: int|
            #![trigger output@ [j]]
            (output_index as int) <= j < (out_idx as int) implies 32 <= output@ [j] <= 126 by {
            assert(output@ [j] == output@ [j]);
        }
        assert(forall|j: int|
            (out_idx as int) <= j < g_out_old.len() ==> output@ [j] == g_out_old [j]);
        /* final(output)@.len() == old(output)@.len(): slice index assignment never
           changes the sequence length -- discharged by the built-in update axioms */
    }
    out_idx
}

/* ============================================================
 * Origin: general_purpose/mod.rs:127-147 `encode_helper`
 * ============================================================ */

/// Upstream doc (mod.rs:120-125):
///   Scalar base64 encode of `input` into `output`, returning the number of bytes written.
///
///   `simd_prefix` gets first crack at the input, returning `(input_consumed, output_written)`. It
///   must consume whole 3-byte groups: `input_consumed % 3 == 0`, `output_written == input_consumed /
///   3 * 4`, both in bounds, and only those `output_written` bytes are written. `(0, 0)` (pure scalar)
///   is always valid.
/// Transcription notes: the `simd_prefix` closure parameter is monomorphized to the
/// scalar engine's only possible value, the pure-scalar `(0, 0)`, which the upstream
/// doc itself states is always valid; with `input_consumed = 0`, `output_written = 0`:
/// the debug_assert!s (mod.rs:135-144) hold trivially (0 % 3 == 0; 0 == 0 / 3 * 4;
/// 0 <= input.len(); 0 <= output.len()), encode_scalar_tail resumes from the exact
/// encoding start. The domain is the full one and the output-room precondition is
/// that of encode_scalar_tail (see the file header and its contract).
pub exec fn encode_helper(symbols: &[u8], input: &[u8], output: &mut [u8]) -> (r: usize)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        output@.len() >= tail_unpadded_len(input@.len() as int),
    ensures
        r@ == tail_unpadded_len(input@.len() as int),
        forall|j: int|
            0 <= j < r@ ==> final(output)@ [j] == enc_tail_byte(symbols@, input@, 0, j),
        forall|j: int|
            #![trigger final(output)@ [j]]
            r@ <= j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j],
        forall|j: int|
            #![trigger final(output)@ [j]]
            0 <= j < r@ ==> 32 <= final(output)@ [j] <= 126,
        final(output)@.len() == old(output)@.len(),
{
    /* Origin Rust (mod.rs:133): let (input_index, output_index) = simd_prefix(input, output); */
    let input_index: usize = 0;
    let output_index: usize = 0;
    /* Origin Rust debug_assert family (mod.rs:135-144), trivially true at (0, 0) */
    let r = encode_scalar_tail(symbols, input, output, input_index, output_index);
    proof {
        assert((input_index as int) == 0);
        assert((output_index as int) == 0);
        assert(
            tail_unpadded_len(input@.len() - (input_index as int)) == tail_unpadded_len(
                (input@.len()) as int,
            )
        );
        assert(
            (output_index as int) + tail_unpadded_len(
                input@.len() - (input_index as int),
            ) == tail_unpadded_len((input@.len()) as int)
        );
    }
    r
}

} // verus!
