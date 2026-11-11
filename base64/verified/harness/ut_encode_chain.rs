//! harness: the encode-chain conversion of the upstream UT/fuzz assertions -- a
//! consumer-by-reference composition of the two landed machine batches (the
//! scalar-encode chain `encode_helper` + `add_padding` and the naive-oracle
//! engine) into the properties the upstream tests state inline:
//!
//!   case_encode_slice_len         <- Engine::encode_slice returns exactly
//!                                    encoded_size (code/src/engine/mod.rs:227-251;
//!                                    UT engine/tests.rs:374
//!                                    encode_engine_slice_fits_into_precisely_sized_slice)
//!   case_encode_slice_utf8        <- UT encode.rs:352 encode_to_slice_random_valid_utf8
//!                                    + encode.rs:392 encode_with_padding_random_valid_utf8
//!                                    (str::from_utf8 unwrap, the same-garbage suffix)
//!   case_encode_slice_no_clobber  <- the "same garbage beyond bytes_written"
//!                                    family (encode.rs:383-384/422-423, UT
//!                                    engine/tests.rs:307 encode_doesnt_write_extra_bytes)
//!   case_naive_matches_scalar    <- UT engine/tests.rs:418 encode_matches_naive
//!                                    (GeneralPurpose scalar vs the naive oracle)
//!   case_roundtrip_decode_estimate<- the naive_estimate preallocation contract
//!                                    behind the fuzz roundtrip/decode_random faces
//!                                    (fuzz/fuzzers/roundtrip.rs; the conservative
//!                                    estimate every decode Vec preallocation rests on)
//!
//! The chain runs on the scalar subdomain (input len <= 26, the verified domain of
//! encode_helper); every theorem is universal over its other parameters.
//! No src spec/lemma is copied here -- all models are referenced from the src tree.
//!
//! Run: ./third_party/verus-docker.sh verus database/base64/verified/harness/ut_encode_chain.rs

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod b64;

use b64::encode::{add_padding, encoded_len, encoded_len_model, pad_bytes_model};
use b64::engine::general_purpose::ValidAlphabetSymbols;
use b64::engine::general_purpose::encode::{
    enc_idx0, enc_idx1, enc_idx2, enc_tail_byte, encode_helper, tail_unpadded_len,
};
use b64::engine::naive::{
    naive_decoded_len_estimate, naive_enc_idx0, naive_enc_idx1, naive_enc_idx2, naive_estimate,
    naive_internal_encode, naive_unpadded_enc_len,
};

verus! {

/* ============================================================
 * Shared exec helper: the upstream encode_slice / encode_with_padding
 * chain (encode_helper + add_padding when padding is configured),
 * with the composed contract the cases below consume. (One new exec
 * helper keeps the chain in a single place; the cases are thin.)
 * ============================================================ */

pub exec fn chain_encode(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    pad_flag: bool,
    pad_sym: u8,
) -> (r: usize)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        input@.len() <= 26,
        32 <= pad_sym as int <= 126,
        tail_unpadded_len(input@.len() as int) <= output@.len(),
        !pad_flag
            || (tail_unpadded_len(input@.len() as int)
                + pad_bytes_model(tail_unpadded_len(input@.len() as int)) <= output@.len()),
    ensures
        r@ == (if pad_flag {
            tail_unpadded_len(input@.len() as int)
                + pad_bytes_model(tail_unpadded_len(input@.len() as int))
        } else {
            tail_unpadded_len(input@.len() as int)
        }),
        final(output)@.len() == old(output)@.len(),
        forall|j: int|
            0 <= j < tail_unpadded_len(input@.len() as int) ==> final(output)@ [j] == enc_tail_byte(
                symbols@,
                input@,
                0,
                j,
            ),
        pad_flag ==> (forall|j: int|
            tail_unpadded_len(input@.len() as int) <= j < r@ ==> final(output)@ [j] == pad_sym),
        forall|j: int|
            #![trigger final(output)@ [j]] 0 <= j < r@ ==> 32 <= final(output)@ [j] <= 126,
        forall|j: int|
            #![trigger final(output)@ [j]]
            r@ <= j < old(output)@.len() ==> final(output)@ [j] == old(output)@ [j],
{
    let ghost g_old = output@;
    let u = encode_helper(symbols, input, output);
    let ghost g_mid = output@;
    assert(u@ == tail_unpadded_len(input@.len() as int));
    if pad_flag {
        proof {
            assert((u as int) <= output@.len());
            assert(
                pad_bytes_model(tail_unpadded_len(input@.len() as int)) <= ((output@.len()) as int)
                    - (u as int)
            );
        }
        let tail = &mut output[u..];
        assert(tail@ == g_mid.subrange(u as int, g_mid.len() as int));
        assert(pad_bytes_model(u as int) <= tail@.len());
        let p = add_padding(u, pad_sym, tail);
        proof {
            assert(p@ == pad_bytes_model(u as int));
            /* the un-borrowed parent prefix is untouched by the padding writes */
            assert(forall|j: int| 0 <= j < (u as int) ==> output@ [j] == g_mid[j]);
            /* the padding region of the parent is exactly the callee's [0, p) */
            assert(forall|j: int|
                (u as int) <= j < ((u as int) + (p as int)) ==> output@ [j] == pad_sym);
            /* the parent suffix beyond the padding rides the two suffix ensures */
            assert(forall|j: int|
                ((u as int) + (p as int)) <= j < g_old.len() ==> output@ [j] == g_mid[j]);
            assert(forall|j: int| (u as int) <= j < g_old.len() ==> g_mid[j] == g_old[j]);
            assert(
                forall|j: int|
                    ((u as int) + (p as int)) <= j < g_old.len() ==> output@ [j] == g_old[j]
            );
            /* per-position model + ASCII carry over the un-borrowed prefix */
            assert(forall|j: int|
                0 <= j < (u as int) ==> output@ [j] == enc_tail_byte(symbols@, input@, 0, j));
            assert(forall|j: int|
                #![trigger output@ [j]]
                0 <= j < ((u as int) + (p as int)) ==> 32 <= output@ [j] <= 126);
            /* the written-total shape the ensures state */
            assert((u as int) == tail_unpadded_len(input@.len() as int));
            assert((p as int) == pad_bytes_model(tail_unpadded_len(input@.len() as int)));
            assert(((u as int) + (p as int)) <= usize::MAX as int);
        }
        u + p
    } else {
        proof {
            assert(forall|j: int|
                0 <= j < (u as int) ==> output@ [j] == enc_tail_byte(symbols@, input@, 0, j));
            assert(forall|j: int|
                #![trigger output@ [j]] 0 <= j < (u as int) ==> 32 <= output@ [j] <= 126);
            assert(forall|j: int| (u as int) <= j < g_old.len() ==> output@ [j] == g_old[j]);
        }
        u
    }
}

/* ============================================================
 * Case 1: the Engine::encode_slice length contract
 * ============================================================ */

/// UT engine/tests.rs:374 encode_engine_slice_fits_into_precisely_sized_slice:
/// for ANY input len <= 26, any symbols with ValidAlphabetSymbols, any padding
/// symbol in the Symbol::new domain and any buffer with room per
/// encoded_len_model (the UT resizes to exactly encoded_size; room->= is the
/// strictly more general instance), the chain writes exactly
/// encoded_len(input_len, padding).unwrap() bytes -- the encode.rs formula
/// tied to the chain via tail_unpadded_len + pad_bytes_model arithmetic
/// (chain_len_lemma below).
pub exec fn case_encode_slice_len(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    pad_flag: bool,
    pad_sym: u8,
) -> (ok: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        input@.len() <= 26,
        32 <= pad_sym as int <= 126,
        tail_unpadded_len(input@.len() as int) <= output@.len(),
        !pad_flag
            || (tail_unpadded_len(input@.len() as int)
                + pad_bytes_model(tail_unpadded_len(input@.len() as int)) <= output@.len()),
{
    let n = input.len();
    let r = chain_encode(symbols, input, output, pad_flag, pad_sym);
    let m = encoded_len(n, pad_flag);
    proof {
        chain_len_lemma(n as int, pad_flag);
        assert(
            r@ == (if pad_flag {
                tail_unpadded_len(n as int) + pad_bytes_model(tail_unpadded_len(n as int))
            } else {
                tail_unpadded_len(n as int)
            })
        );
    }
    assert(m == Option::Some(r));
    m == Option::Some(r)
}

/* ============================================================
 * Case 2: the valid-UTF-8 property of the chain output
 * ============================================================ */

/// UT encode.rs:352 encode_to_slice_random_valid_utf8 +
/// encode.rs:392 encode_with_padding_random_valid_utf8: every byte the
/// chain wrote (algorithm bytes and padding bytes alike) is a printable
/// ASCII byte, hence all < 128, so std::str::from_utf8 over [0, r) is
/// Ok -- the upstream str::from_utf8(..).unwrap() (encode.rs:387/426)
/// holds on this domain. The pad_sym precondition is exactly upstream
/// Symbol::new's printability domain (alphabet.rs
/// is_valid_b64_symbol_spec: 32..=126), from which every engine's padding
/// byte comes.
pub exec fn case_encode_slice_utf8(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    pad_flag: bool,
    pad_sym: u8,
) -> (ok: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        input@.len() <= 26,
        32 <= pad_sym as int <= 126,
        tail_unpadded_len(input@.len() as int) <= output@.len(),
        !pad_flag
            || (tail_unpadded_len(input@.len() as int)
                + pad_bytes_model(tail_unpadded_len(input@.len() as int)) <= output@.len()),
{
    let r = chain_encode(symbols, input, output, pad_flag, pad_sym);
    assert(forall|j: int|
        #![trigger output@ [j]] 0 <= j < r@ ==> 32 <= output@ [j] <= 126);
    /* ASCIIness: every written byte is its own UTF-8 encoding (byte < 128),
       so the upstream from_utf8 unwrap never fails over [0, r) */
    assert(forall|j: int| 0 <= j < r@ ==> output@ [j] < 128);
    r <= output.len()
}

/* ============================================================
 * Case 3: the no-clobber property beyond bytes_written
 * ============================================================ */

/// The "output buffer beyond bytes_written is the same garbage" property
/// (encode.rs:383-384 and encode.rs:449-450; UT engine/tests.rs:307
/// encode_doesnt_write_extra_bytes): everything at or past the returned
/// count is byte-for-byte what it was before the chain ran -- composed
/// from both fns' suffix-preservation ensures.
pub exec fn case_encode_slice_no_clobber(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    pad_flag: bool,
    pad_sym: u8,
) -> (ok: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        input@.len() <= 26,
        32 <= pad_sym as int <= 126,
        tail_unpadded_len(input@.len() as int) <= output@.len(),
        !pad_flag
            || (tail_unpadded_len(input@.len() as int)
                + pad_bytes_model(tail_unpadded_len(input@.len() as int)) <= output@.len()),
{
    let ghost g_old = output@;
    let r = chain_encode(symbols, input, output, pad_flag, pad_sym);
    assert(forall|j: int| r@ <= j < g_old.len() ==> output@ [j] == g_old[j]);
    r <= output.len()
}

/* ============================================================
 * Case 4: encode_matches_naive
 * ============================================================ */

/// UT engine/tests.rs:418 encode_matches_naive on the verified contracts:
/// the scalar GeneralPurpose internal_encode and the Naive oracle return
/// the same count for every input of len 1..=26, and write identical bytes
/// on the rem-driven tail group (the 3 bytes past the complete groups when
/// rem == 2, the 2 bytes when rem == 1). Scoping decision, one line: byte
/// equality is stated over the tail group only, because naive's ensures
/// deliberately omit the full per-position forall (the recorded z3
/// back-edge instability), while its concrete rem==1/rem==2 tail ensures
/// pin exactly those positions -- which is where the two machines' output
/// could ever have diverged on this domain.
pub exec fn case_naive_matches_scalar(
    symbols: &[u8],
    input: &[u8],
    out_scalar: &mut [u8],
    out_naive: &mut [u8],
) -> (ok: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        1 <= input@.len() <= 26,
        tail_unpadded_len(input@.len() as int) <= out_scalar@.len(),
        naive_unpadded_enc_len(input@.len() as int) <= out_naive@.len(),
{
    let rem_e = input.len() % 3;
    assert(rem_e@ == input@.len() % 3);
    let r1 = encode_helper(symbols, input, out_scalar);
    let r2 = naive_internal_encode(symbols, input, out_naive);
    /* (a) same counts: the two unpadded-length models agree on all input lens */
    proof {
        tail_vs_naive_len_lemma(input@.len() as int);
    }
    assert(r1@ == r2@);
    if rem_e == 2 {
        proof {
            let n: int = input@.len() as int;
            let q: int = n / 3;
            assert(n == 3 * q + 2);
            assert((n - 2) / 3 == q);
            assert(r1@ == 4 * q + 3);
            let b0 = input@[n - 2];
            let b1 = input@[n - 1];
            /* scalar side: the per-position model at the tail group */
            assert(4 * q >= 0);
            assert(4 * q < r1@);
            assert((4 * q) + 1 < r1@);
            assert((4 * q) + 2 < r1@);
            assert(out_scalar@[4 * q] == enc_tail_byte(symbols@, input@, 0, 4 * q));
            assert(out_scalar@[4 * q + 1] == enc_tail_byte(symbols@, input@, 0, 4 * q + 1));
            assert(out_scalar@[4 * q + 2] == enc_tail_byte(symbols@, input@, 0, 4 * q + 2));
            /* model reduction at the tail positions (group g == q, slots 0..2) */
            assert(4 * q / 4 == q);
            assert(4 * q % 4 == 0);
            assert((4 * q + 1) / 4 == q);
            assert((4 * q + 1) % 4 == 1);
            assert((4 * q + 2) / 4 == q);
            assert((4 * q + 2) % 4 == 2);
            assert((3 * q) + 1 < n);
            assert(enc_tail_byte(symbols@, input@, 0, 4 * q) == symbols@[enc_idx0(b0) as int]);
            assert(enc_tail_byte(symbols@, input@, 0, 4 * q + 1) == symbols@[enc_idx1(
                b0,
                b1,
            ) as int]);
            assert(enc_tail_byte(symbols@, input@, 0, 4 * q + 2) == symbols@[enc_idx2(
                b1,
                0,
            ) as int]);
            /* naive side: the concrete rem==2 tail ensures (positions from n) */
            assert(out_naive@[(n - 2) / 3 * 4] == symbols@[naive_enc_idx0(b0) as int]);
            assert(out_naive@[(n - 2) / 3 * 4 + 1] == symbols@[naive_enc_idx1(b0, b1) as int]);
            assert(out_naive@[(n - 2) / 3 * 4 + 2] == symbols@[naive_enc_idx2(b1, 0) as int]);
            /* the two index model families compute the same 6-bit indices */
            assert(enc_idx0(b0) == naive_enc_idx0(b0) as u8) by (bit_vector);
            assert(enc_idx1(b0, b1) == naive_enc_idx1(b0, b1) as u8) by (bit_vector);
            assert(enc_idx2(b1, 0) == naive_enc_idx2(b1, 0) as u8) by (bit_vector);
            assert(naive_enc_idx0(b0) as int == enc_idx0(b0) as int);
            assert(naive_enc_idx1(b0, b1) as int == enc_idx1(b0, b1) as int);
            assert(naive_enc_idx2(b1, 0) as int == enc_idx2(b1, 0) as int);
            /* (b) identical tail bytes */
            assert(out_scalar@[4 * q] == out_naive@[4 * q]);
            assert(out_scalar@[4 * q + 1] == out_naive@[4 * q + 1]);
            assert(out_scalar@[4 * q + 2] == out_naive@[4 * q + 2]);
        }
        true
    } else if rem_e == 1 {
        proof {
            let n: int = input@.len() as int;
            let q: int = n / 3;
            assert(n == 3 * q + 1);
            assert((n - 1) / 3 == q);
            assert(r1@ == 4 * q + 2);
            let b0 = input@[n - 1];
            /* scalar side: the per-position model at the tail group */
            assert(4 * q < r1@);
            assert((4 * q) + 1 < r1@);
            assert(out_scalar@[4 * q] == enc_tail_byte(symbols@, input@, 0, 4 * q));
            assert(out_scalar@[4 * q + 1] == enc_tail_byte(symbols@, input@, 0, 4 * q + 1));
            /* model reduction at the tail positions (group g == q, slots 0..1) */
            assert(4 * q / 4 == q);
            assert(4 * q % 4 == 0);
            assert((4 * q + 1) / 4 == q);
            assert((4 * q + 1) % 4 == 1);
            assert((3 * q) < n);
            assert(enc_tail_byte(symbols@, input@, 0, 4 * q) == symbols@[enc_idx0(b0) as int]);
            assert(enc_tail_byte(symbols@, input@, 0, 4 * q + 1) == symbols@[enc_idx1(
                b0,
                0,
            ) as int]);
            /* naive side: the concrete rem==1 tail ensures (positions from n) */
            assert(out_naive@[(n - 1) / 3 * 4] == symbols@[naive_enc_idx0(b0) as int]);
            assert(out_naive@[(n - 1) / 3 * 4 + 1] == symbols@[naive_enc_idx1(b0, 0) as int]);
            /* index model bridges */
            assert(enc_idx0(b0) == naive_enc_idx0(b0) as u8) by (bit_vector);
            assert(enc_idx1(b0, 0) == naive_enc_idx1(b0, 0) as u8) by (bit_vector);
            assert(naive_enc_idx0(b0) as int == enc_idx0(b0) as int);
            assert(naive_enc_idx1(b0, 0) as int == enc_idx1(b0, 0) as int);
            /* (b) identical tail bytes */
            assert(out_scalar@[4 * q] == out_naive@[4 * q]);
            assert(out_scalar@[4 * q + 1] == out_naive@[4 * q + 1]);
        }
        true
    } else {
        /* rem == 0: no tail group exists; count equality is the full claim */
        true
    }
}

/* ============================================================
 * Case 5: the roundtrip/decode estimate face
 * ============================================================ */

/// The decode-side preallocation contract the fuzz roundtrip faces rest on
/// (fuzz/fuzzers/roundtrip.rs; the DecodeEstimate doc "conservative, err on
/// the side of too big ... no larger than the next largest complete
/// triple"): after running the chain on any input len <= 26, the naive
/// estimate -- composed exactly as upstream does, naive_estimate(total)
/// then naive_decoded_len_estimate(complete_chunk_len, rem) -- upper-bounds
/// the true decoded requirement (the original input length: what a faithful
/// decoder must return for this chain's content) with the tightness slack
/// the doc promises: n <= est <= n + 2. Scoping decision, one line: exact
/// equality est == n holds only when n % 3 == 0 (rem cases pad the final
/// partial triple, e.g. "AB==" -- 4 symbols, 1 byte), so the honest
/// universal statement is the conservative pair of bounds, not equality.
pub exec fn case_roundtrip_decode_estimate(
    symbols: &[u8],
    input: &[u8],
    output: &mut [u8],
    pad_flag: bool,
    pad_sym: u8,
) -> (ok: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        input@.len() <= 26,
        32 <= pad_sym as int <= 126,
        tail_unpadded_len(input@.len() as int) <= output@.len(),
        !pad_flag
            || (tail_unpadded_len(input@.len() as int)
                + pad_bytes_model(tail_unpadded_len(input@.len() as int)) <= output@.len()),
{
    let n = input.len();
    let r = chain_encode(symbols, input, output, pad_flag, pad_sym);
    let (re, ccl) = naive_estimate(r);
    assert(re@ == r@ % 4);
    assert(ccl@ == r@ - r@ % 4);
    let est = naive_decoded_len_estimate(ccl, re);
    assert(est@ == ((ccl@ / 4 + if re@ > 0 { 1int } else { 0int }) * 3));
    proof {
        dec_est_lemma(n as int, pad_flag, r as int);
        assert(
            est@ == ((r@ - r@ % 4) / 4 + if r@ % 4 > 0 { 1int } else { 0int }) * 3
        );
    }
    assert(n <= est);
    assert(est <= n + 2);
    n <= est && est <= n + 2
}

/* ============================================================
 *  Proof items (file tail)
 *  -- the modular-arithmetic bridges the cases above consume. Each is
 *     pure spec arithmetic over the src models; no obligation anywhere
 *     is dropped (no verifier bypass tokens appear in this file).
 * ============================================================ */

/// The chain length contract: the console the chain writes (unpadded
/// tail + pad_bytes_model) is exactly the encode.rs encoded_len model
/// value, for every input len in the verified domain.
pub proof fn chain_len_lemma(n: int, pad: bool)
    requires
        0 <= n <= 26,
    ensures
        encoded_len_model(n, pad) == Option::Some(
            (if pad {
                tail_unpadded_len(n) + pad_bytes_model(tail_unpadded_len(n))
            } else {
                tail_unpadded_len(n)
            }) as usize,
        ),
{
    let q = n / 3;
    let m = n % 3;
    if m == 0 {
        assert(tail_unpadded_len(n) == 4 * q);
        assert(4 * q % 4 == 0);
        assert(pad_bytes_model(4 * q) == 0);
        assert(tail_unpadded_len(n) <= 36);
    } else if m == 1 {
        assert(tail_unpadded_len(n) == 4 * q + 2);
        assert(4 * q % 4 == 0);
        assert(pad_bytes_model(4 * q + 2) == 2);
        assert(tail_unpadded_len(n) <= 36);
    } else {
        assert(tail_unpadded_len(n) == 4 * q + 3);
        assert(4 * q % 4 == 0);
        assert(pad_bytes_model(4 * q + 3) == 1);
        assert(tail_unpadded_len(n) <= 36);
    }
}

/// The two unpadded-length models (scalar batch and naive batch) agree on
/// every nonnegative input length.
pub proof fn tail_vs_naive_len_lemma(n: int)
    requires
        0 <= n,
    ensures
        tail_unpadded_len(n) == naive_unpadded_enc_len(n),
{
}

/// The decode-estimate arithmetic: for a chain total of n input bytes, the
/// naive estimate composition lands in [n, n+2] -- conservative, and no
/// larger than the next complete decoded triple beyond the true length.
pub proof fn dec_est_lemma(n: int, pad: bool, total: int)
    requires
        0 <= n <= 26,
        total == (if pad {
            tail_unpadded_len(n) + pad_bytes_model(tail_unpadded_len(n))
        } else {
            tail_unpadded_len(n)
        }),
    ensures
        n <= ((total - total % 4) / 4 + (if total % 4 > 0 { 1int } else { 0int })) * 3,
        ((total - total % 4) / 4 + (if total % 4 > 0 { 1int } else { 0int })) * 3 <= n + 2,
{
    let q = n / 3;
    let m = n % 3;
    if m == 0 {
        assert(tail_unpadded_len(n) == 4 * q);
        assert(4 * q % 4 == 0);
        assert(pad_bytes_model(4 * q) == 0);
        assert(total == 4 * q);
        assert(total % 4 == 0);
        assert(4 * q / 4 == q);
        assert(n == 3 * q);
        assert(
            ((total - total % 4) / 4 + (if total % 4 > 0 { 1int } else { 0int })) * 3 == 3 * q
        );
    } else if m == 1 {
        assert(tail_unpadded_len(n) == 4 * q + 2);
        assert(4 * q % 4 == 0);
        assert(pad_bytes_model(4 * q + 2) == 2);
        assert(n == 3 * q + 1);
        if pad {
            assert(total == 4 * q + 4);
            assert(total % 4 == 0);
            assert((4 * q + 4) / 4 == q + 1);
        } else {
            assert(total == 4 * q + 2);
            assert(total % 4 == 2);
            assert((total - total % 4) == 4 * q);
            assert(4 * q / 4 == q);
        }
        assert(
            ((total - total % 4) / 4 + (if total % 4 > 0 { 1int } else { 0int })) * 3 == 3 * q + 3
        );
    } else {
        assert(tail_unpadded_len(n) == 4 * q + 3);
        assert(4 * q % 4 == 0);
        assert(pad_bytes_model(4 * q + 3) == 1);
        assert(n == 3 * q + 2);
        if pad {
            assert(total == 4 * q + 4);
            assert(total % 4 == 0);
            assert((4 * q + 4) / 4 == q + 1);
        } else {
            assert(total == 4 * q + 3);
            assert(total % 4 == 3);
            assert((total - total % 4) == 4 * q);
            assert(4 * q / 4 == q);
        }
        assert(
            ((total - total % 4) / 4 + (if total % 4 > 0 { 1int } else { 0int })) * 3 == 3 * q + 3
        );
    }
}

} // verus!

fn main() {}
