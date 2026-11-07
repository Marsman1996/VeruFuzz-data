//! base64ct codec driver mirror (the Encoding trait's standard members)
//!
//! Upstream: code/base64ct/src/encoding.rs (pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614)
//! The upstream tree is unmodified; this file is the verified-side copy.
//!
//! Transcription notes (the KVerus relax ledger; see out/bug-finder-summary.md):
//! - The `impl<T: Alphabet> Encoding for T` generics are monomorphized into `encode_std`/`decode_std` taking a
//!   `padded: bool` parameter for the standard members (the alphabet semantic model lives in alphabet/standard.rs,
//!   referenced by this file without copying). The other alphabets' drivers are isomorphic to these but
//!   are not transcribed here.
//! - Return types: upstream `decode`/`encode` return `Result<&[u8]/&str, _>` (a borrowed slice or str); the
//!   mirror returns `Result<usize, _>` (Ok carries the written length dlen/elen), so `Ok(dst[..n])`
//!   and `Ok(n)` correspond one to one; the str side's ASCII/UTF-8 validity is carried by harness witness theorems.
//! - Iterator loops such as `chunks_exact(4).zip(chunks_exact_mut(3))` are rewritten as index loops
//!   (the loop cadence is given by the upstream length prechecks).
//! - The `checked_mul`/`div_ceil` checked operations are rewritten as explicit branches (same semantics).
//! - `decode_in_place` (encoding.rs:106-170, unsafe raw-pointer in-place decoding) is not transcribed: the raw-pointer
//!   blocks plus an in-place read/write overlap-sequence proof are costly; its semantic difference from decode (it skips
//!   validate_last_block, as the upstream doc already notes) is recorded in the summary.
//! - The alloc paths `decode_vec`/`encode_string` (Vec/String) are not transcribed.

use vstd::prelude::*;

use super::alphabet::standard::b64_char_std;
use super::alphabet::standard::b64_encode_pos_std;
use super::alphabet::standard::lemma_enc_index;
use super::alphabet::standard::lemma_enc_tail1_pos_chars;
use super::alphabet::standard::lemma_enc_tail2_pos_chars;
use super::alphabet::standard::b64_dec_len_model_std;
use super::alphabet::standard::b64_decode_model_std;
use super::alphabet::standard::b64_decode_pos_std;
use super::alphabet::standard::b64_digit_std;
use super::alphabet::standard::b64_dec_bytes_std;
use super::alphabet::standard::b64_pad_ok_std;
use super::alphabet::standard::decode_6bits_std;
use super::alphabet::standard::decode_3bytes_std_at;
use super::alphabet::decode_pack_std;
use super::alphabet::standard::b64_enc_idx_std;
use super::alphabet::standard::b64_tailblock_zip_ok_std;
use super::alphabet::standard::b64_tailblock_zip_mismatch_exists_std;
use super::alphabet::standard::lemma_mismatch_at_implies_exists;
use super::alphabet::standard::b64_elen_model_std;
use super::alphabet::standard::b64_encode_model_std;
use super::alphabet::standard::b64_pad_count_std;
use super::alphabet::standard::b64_pad_err_std;
use super::alphabet::standard::decode_3bytes_std;
use super::alphabet::decode_eq_term;
use super::alphabet::standard::encode_3bytes_std;
use super::alphabet::standard::encode_3bytes_std_at;
use super::alphabet::standard::encode_6bits_std;
use super::alphabet::encode_pack_indices_std;
use super::errors::{Error, InvalidEncodingError, InvalidLengthError};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============================================================
 * Length models (encoded_len_inner / encoded_len / decoded_len)
 * ============================================================ */

/// Origin: encoding.rs:344-352 `decoded_len` -- the overflow-free implementation of `(3*n)/4`
/// Upstream doc (encoding.rs:339-343):
///   Get the length of the output from decoding the provided *unpadded*
///   Base64-encoded input.
///   Note that this function does not fully validate the Base64 is well-formed
///   and may return incorrect results for malformed Base64.
pub exec fn decoded_len(input_len: usize) -> (r: usize)
    ensures
        r as int == 3 * (input_len as int / 4) + (3 * (input_len as int % 4)) / 4,
        r as int == (3 * input_len as int) / 4,
{
    /* Origin Rust: let k = input_len / 4; let l = input_len - 4 * k;
       3 * k + (3 * l) / 4 */
    let k = input_len / 4;
    let l = input_len - 4 * k;
    3 * k + (3 * l) / 4
}

/// Origin: encoding.rs:362-377 `encoded_len_inner` (the checked operations expanded into explicit branches)
/// Upstream doc (encoding.rs:362-362):
///   Compute the encoded length for an `n`-byte input and whether the output is `padded`.
pub exec fn encoded_len_inner(n: usize, padded: bool) -> (r: Option<usize>)
    ensures
        // The upstream overflow criterion is based on the padded length 4*ceil(n/3) (multiply first, subtract later);
        // encoded_len's WARNING behavior (r == 0 beyond usize::MAX/4) rides on this criterion.
        (4 * ((n as int + 2) / 3) > usize::MAX as int) ==> (r == Option::None),
        (4 * ((n as int + 2) / 3) <= usize::MAX as int) ==> (r
            == Option::Some((b64_elen_model_std(n as int, padded) as int) as usize)),
{
    /* Origin Rust: n.div_ceil(3) -- overflow-free expansion: ceil(n/3) = n/3 + (n%3 != 0) */
    let full = n / 3;
    let has_tail = n % 3 != 0;
    let q = if has_tail {
        full + 1
    } else {
        full
    };
    /* Origin Rust: q.checked_mul(4) */
    if q > usize::MAX / 4 {
        return Option::None;
    }
    let len = 4 * q;
    /* Origin Rust: match ... { Some(len) if padded => Some(len),
       Some(len) => { let rem = n % 3; len.checked_sub(if rem == 0 {0} else {3 - rem}) } ... } */
    proof {
        // div_ceil expansion: ceil(n/3) = n/3 + (n%3 != 0), then reconcile against the model in the three n%3 cases
        let m = n % 3;
        if m == 0 {
            assert((n as int + 2) / 3 == n as int / 3);
            assert(q == n / 3);
            assert(b64_elen_model_std(n as int, padded) as int == 4 * q as int);
        } else if m == 1 {
            assert((n as int + 2) / 3 == n as int / 3 + 1);
            assert(q == n / 3 + 1);
            assert(b64_elen_model_std(n as int, true) as int == 4 * q as int);
            assert(b64_elen_model_std(n as int, false) as int == 4 * q as int - 2);
        } else {
            assert((n as int + 2) / 3 == n as int / 3 + 1);
            assert(q == n / 3 + 1);
            assert(b64_elen_model_std(n as int, true) as int == 4 * q as int);
            assert(b64_elen_model_std(n as int, false) as int == 4 * q as int - 1);
        }
    }
    if padded {
        proof {
            assert(4 * q <= usize::MAX);
        }
        Option::Some(len)
    } else {
        let rem = n % 3;
        let sub = if rem == 0 {
            0
        } else {
            3 - rem
        };
        proof {
            assert(sub <= 2);
            assert(len as int - sub as int >= 0);
        }
        Option::Some(len - sub)
    }
}

/// Origin: encoding.rs:250-252 `Encoding::encoded_len` (std monomorphized for the two padded cases)
/// Upstream doc (encoding.rs:58-60):
///   Get the length of Base64 produced by encoding the given bytes.
///   WARNING: this function will return `0` for lengths greater than `usize::MAX/4`!
pub exec fn encoded_len(n: usize, padded: bool) -> (r: usize)
    ensures
        (4 * ((n as int + 2) / 3) <= usize::MAX as int) ==> (r as int
            == b64_elen_model_std(n as int, padded) as int),
        (4 * ((n as int + 2) / 3) > usize::MAX as int) ==> (r == 0),
{
    /* Origin Rust: encoded_len_inner(bytes.len(), T::PADDED).unwrap_or(0) */
    match encoded_len_inner(n, padded) {
        Option::Some(v) => v,
        Option::None => 0,
    }
}

/* ============================================================
 * decode_padding (the padding pre-scan)
 * ============================================================ */

/// Origin: encoding.rs:264-297 `decode_padding`
/// (`is_pad_ct` is exactly decode_eq_term(0x3D, 1, _); the `[.., b0, b1]` pattern = the last-two-bytes branch)
/// Upstream doc (encoding.rs:255-263):
///   Validate padding is of the expected length compute unpadded length.
///   Note that this method does not explicitly check that the padded data
///   is valid in and of itself: that is performed by `validate_last_block` as a
///   final step.
///   Returns length-related errors eagerly as a [`Result`], and data-dependent
///   errors (i.e. malformed padding bytes) as `i16` to be combined with other
///   encoding-related errors prior to branching.
pub exec fn decode_padding_std(input: &[u8]) ->
    (r: Result<(usize, i16), InvalidEncodingError>)
    ensures
        input@.len() % 4 != 0 ==> r == Result::Err(InvalidEncodingError),
        input@.len() % 4 == 0 ==> (r.is_ok()
            && (r.get_Ok_0().0 as int == input@.len() as int
                - b64_pad_count_std(input@))
            && (r.get_Ok_0().1 as int == b64_pad_err_std(input@))),
{
    /* Origin Rust: if input.len() % 4 != 0 { return Err(InvalidEncodingError); } */
    let n = input.len();
    if n % 4 != 0 {
        return Result::Err(InvalidEncodingError);
    }
    /* Origin Rust: let unpadded_len = match *input {
          [.., b0, b1] => is_pad_ct(b0).checked_add(is_pad_ct(b1))..., _ => input.len() }
       -- with n%4==0, the [.., b0, b1] pattern hits iff n >= 4 */
    let mut unpadded_len = n;
    let mut pad_err: i16 = 0;
    if n >= 2 {
        /* Origin Rust: is_pad_ct(b0) (the second-to-last byte) */
        let c2v = decode_eq_term(0x3D, 1, input[n - 2]);
        /* Origin Rust: is_pad_ct(b1) (the last byte) */
        let c1v = decode_eq_term(0x3D, 1, input[n - 1]);
        let cnt = c2v + c1v;
        proof {
            assert(cnt >= 0 && cnt <= 2);
            assert(n >= 2);
        }
        unpadded_len = n - (cnt as usize);
        /* Origin Rust: let padding_len = input.len().checked_sub(unpadded_len) */
        let padding_len = n - unpadded_len;
        /* Origin Rust: let err = match *input {
              [.., b0] if padding_len == 1 => is_pad_ct(b0) ^ 1,
              [.., b0, b1] if padding_len == 2 => (is_pad_ct(b0) & is_pad_ct(b1)) ^ 1,
              _ => if padding_len == 0 { 0 } else { return Err(...) } } */
        if padding_len == 1 {
            pad_err = decode_eq_term(0x3D, 1, input[n - 1]) ^ 1;
        } else if padding_len == 2 {
            pad_err = (c2v & c1v) ^ 1;
        } else if padding_len != 0 {
            return Result::Err(InvalidEncodingError);
        }
        proof {
            // Reconcile against the spec: count == p1 + p2 (i.e. c2v + c1v); the three pad_err branch semantics.
            // Local bit facts: ^1 / & over {0,1} are one-step bit_vector proofs.
            let c2v0 = c2v;
            let c1v0 = c1v;
            assert((c2v0 == (0i16) || c2v0 == (1i16)));
            assert((c1v0 == (0i16) || c1v0 == (1i16)));
            assert(cnt as int == b64_pad_count_std(input@));
            assert(padding_len as int == cnt as int);
            if padding_len == 1 {
                // pad_err = is_pad(last) ^ 1
                assert((c1v0 == (0i16)) && (pad_err == (c1v0 ^ (1i16))) ==> (pad_err == (1i16))) by (bit_vector);
                assert((c1v0 == (1i16)) && (pad_err == (c1v0 ^ (1i16))) ==> (pad_err == (0i16))) by (bit_vector);
                assert(b64_pad_err_std(input@) == pad_err as int);
            } else if padding_len == 2 {
                assert((c2v0 == (1i16)) && (c1v0 == (1i16)) && (pad_err == ((c2v0 & c1v0) ^ (1i16))) ==> (pad_err == (0i16))) by (bit_vector);
                assert(b64_pad_err_std(input@) == 0);
            } else {
                assert(pad_err == 0);
                assert(b64_pad_err_std(input@) == 0);
            }
        }
    }
    Result::Ok((unpadded_len, pad_err))
}

/* ============================================================
 * The encode driver (standard alphabet x the two padded cases)
 * ============================================================ */

/// Origin: encoding.rs:185-232 `Encoding::encode` (generic monomorphized for std)
/// Upstream doc (encoding.rs:45-48):
///   Encode the input byte slice as Base64.
///   Writes the result into the provided destination slice, returning an
///   ASCII-encoded Base64 string value.
pub exec fn encode_std(src: &[u8], dst: &mut [u8], padded: bool) ->
    (r: Result<usize, InvalidLengthError>)
    ensures
        // (elen below abbreviates b64_elen_model_std(src@.len(), padded), written out at each use)
        (4 * ((src@.len() as int + 2) / 3) > usize::MAX as int) ==> (r
            == Result::Err(InvalidLengthError)),
        (b64_elen_model_std(src@.len() as int, padded) as int <= old(dst)@.len() as int
            && 4 * ((src@.len() as int + 2) / 3) <= usize::MAX as int) ==> (
            r == Result::Ok(
                (b64_elen_model_std(src@.len() as int, padded) as int) as usize,
            ) && (forall|j: int|
                0 <= j < b64_elen_model_std(src@.len() as int, padded) as int ==> final(dst)@[j]
                    == b64_encode_model_std(src@, padded)[j])
        ),
        (b64_elen_model_std(src@.len() as int, padded) as int
            <= 4 * ((src@.len() as int + 2) / 3)
            && 4 * ((src@.len() as int + 2) / 3) <= usize::MAX as int
            && b64_elen_model_std(src@.len() as int, padded) as int
                > old(dst)@.len() as int) ==> (r == Result::Err(InvalidLengthError)),
        // No write is triggered (every error path returns before any write)
        (r.is_err() && src@.len() > 0) ==> (old(dst)@ =~= final(dst)@),
{
    /* Origin Rust: let elen = match encoded_len_inner(src.len(), T::PADDED) {
       Some(v) => v, None => return Err(InvalidLengthError) } */
    let elen_m = encoded_len_inner(src.len(), padded);
    let elen: usize;
    if elen_m.is_none() {
        return Result::Err(InvalidLengthError);
    }
    match elen_m {
        Option::Some(v) => {
            elen = v;
        }
        Option::None => {
            return Result::Err(InvalidLengthError);
        }
    }
    /* Origin Rust: if elen > dst.len() { return Err(InvalidLengthError); } */
    if elen > dst.len() {
        return Result::Err(InvalidLengthError);
    }
    let ghost s = src@;
    let ghost n: int = src@.len() as int;
    let n_u = src.len();
    let k = n_u / 3;
    proof {
        // Before the loop: elen-model block-bound facts (4k upper-bounds the full-block zone)
        let t0 = n % 3;
        if padded {
            assert(b64_elen_model_std(n, padded) as int == 4 * ((n + 2) / 3));
        } else {
            assert(b64_elen_model_std(n, padded) as int
                >= 4 * (n / 3) && b64_elen_model_std(n, padded) as int
                <= 4 * (n / 3) + 3);
        }
        assert(4 * (n / 3) <= b64_elen_model_std(n, padded) as int);
        assert(4 * (k as int) <= elen as int);
    }
    let ghost dl = dst@.len();
    /* Origin Rust: let mut src_chunks = src.chunks_exact(3);
       let mut dst_chunks = dst.chunks_exact_mut(4);
       for (s, d) in (&mut src_chunks).zip(&mut dst_chunks) { Self::encode_3bytes(s, d); }
       -- the zip length is exactly min(len/3, elen/4) = len/3 full blocks, rewritten as an index loop */
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            s == src@,
            n_u == s.len(),
            k as int == s.len() as int / 3,
            n == s.len() as int,
            elen as int == b64_elen_model_std(n, padded) as int,
            dst@.len() == dl,
            elen <= dst@.len(),
            dst.len() as int >= elen as int,
            4 * (k as int) <= elen as int,
            elen as int >= 4 * (i as int),
            forall|j: int| 0 <= j < 4 * (i as int) ==> dst@[j]
                == b64_encode_model_std(s, padded)[j],
        decreases k - i
    {
        proof {
            assert(4 * (i as int) + 4 <= 4 * (k as int));
            assert(4 * (i as int) + 4 <= elen as int);
            assert(4 * (i as int) + 4 <= dst@.len());
            assert(4 * (i as int) + 4 <= usize::MAX as int);
            assert(3 * (i as int) + 3 <= n);
        }
        /* Origin Rust: Self::encode_3bytes(s, d) (once per full block) */
        let ghost pre_dst = dst@;
        encode_3bytes_std_at(src, 3 * i, dst, 4 * i);
        proof {
            // The write window [4i, 4i+4): the _at post (absolute j indices) x the pos model
            assert forall|j: int| 4 * (i as int) <= j < 4 * (i as int) + 4 implies
                dst@[j] == b64_encode_model_std(s, padded)[j] by {
                let oo = j - 4 * (i as int);
                assert(j % 4 == oo);
                assert(j / 4 == i as int);
                lemma_enc_index(s, padded, j);
                assert(j < 4 * (n / 3));
            // The model full-block branch vs encode_3bytes's ensures (the same idx function)
                assert(b64_encode_pos_std(s, padded, j)
                    == b64_char_std(b64_enc_idx_std(
                        s.subrange(3 * (j / 4), 3 * (j / 4) + 3),
                        j % 4,
                    )));
            }
            // Out-of-window frame: dst@ == pre_dst on [0, 4i)
            assert forall|j: int| 0 <= j < 4 * (i as int) implies
                dst@[j] == pre_dst[j] by {
                assert(j >= 0);
                assert(j < 4 * (i as int) + 4);
                assert(0 <= j);
                assert(j < dl);
            }
        }
        i += 1;
    }
    /* Origin Rust: let src_rem = src_chunks.remainder();
       if T::PADDED { ...tmp + mask fixes the '='... } else { ...tmp_in/tmp_out prefix copies... } */
    let t = n_u % 3;
    proof {
        if t == 0 {
            assert(n == 3 * (n / 3));
        } else if t == 1 {
            assert(n == 3 * (n / 3) + 1);
        } else {
            assert(n == 3 * (n / 3) + 2);
        }
        assert(3 * (k as int) + (t as int) == n);
    }
    if t == 1 {
        /* Origin Rust: let mut tmp = [0u8; 3]; tmp[..1].copy_from_slice(src_rem);
           Self::encode_3bytes(&tmp, dst_rem) -- the tail block is zero-padded before encoding */
        let mut tmp = [0u8; 3];
        tmp[0] = src[3 * k];
        proof {
            assert(tmp@.len() == 3);
            assert(tmp@[0] == s[3 * k]);
            assert(tmp@[1] == 0);
            assert(tmp@[2] == 0);
        }
        if padded {
            /* Origin Rust: let flag = src_rem.len() == 1; let mask = (flag as u8).wrapping_sub(1);
               dst_rem[2] = (dst_rem[2] & mask) | (PAD & !mask); dst_rem[3] = PAD
               -- flag is constantly true in this branch (mask == 0), transcribed equivalently as setting PAD directly.
               encode_3bytes is #[inline(always)]: its 4 character writes expand as the idx extraction +
               the per-character encode_6bits compose (same bytes, same positions) */
            let (i0, i1, i2, i3) = encode_pack_indices_std(&tmp);
            proof {
                assert(0 <= i0 <= 63);
                assert(0 <= i1 <= 63);
                assert(0 <= i2 <= 63);
                assert(0 <= i3 <= 63);
            }
            dst[4 * k] = encode_6bits_std(i0);
            dst[4 * k + 1] = encode_6bits_std(i1);
            dst[4 * k + 2] = 0x3D;
            dst[4 * k + 3] = 0x3D;
            proof {
                assert forall|j: int| 4 * k <= j < elen as int implies
                    dst@[j] == b64_encode_model_std(s, padded)[j] by {
                    lemma_enc_index(s, padded, j);
                    let o = j - 4 * k;
                    if o == 0 || o == 1 {
                        assert(b64_encode_pos_std(s, padded, j)
                            == b64_char_std(b64_enc_idx_std(tmp@, o)));
                    } else {
                        assert(b64_encode_pos_std(s, padded, j) == 0x3D);
                        assert(dst@[j] == 0x3D);
                    }
                }
            }
        } else {
            /* Origin Rust: let mut tmp_in = [0u8; 3]; let mut tmp_out = [0u8; 4];
               tmp_in[..src_rem.len()].copy_from_slice(src_rem);
               Self::encode_3bytes(&tmp_in, &mut tmp_out);
               dst_rem.copy_from_slice(&tmp_out[..dst_rem.len()]);
               -- the write set is exactly [4k, 4k+2)) */
            let (i0, i1, i2, i3) = encode_pack_indices_std(&tmp);
            proof {
                assert(0 <= i0 <= 63);
                assert(0 <= i1 <= 63);
            }
            dst[4 * k] = encode_6bits_std(i0);
            dst[4 * k + 1] = encode_6bits_std(i1);
            proof {
                assert forall|j: int| 4 * k <= j < 4 * k + 2 implies
                    dst@[j] == b64_encode_model_std(s, padded)[j] by {
                    lemma_enc_index(s, padded, j);
                    let o = j - 4 * k;
                    assert(b64_encode_pos_std(s, padded, j)
                        == b64_char_std(b64_enc_idx_std(tmp@, o)));
                }
                assert(elen as int == 4 * k + 2);
            }
        }
    } else if t == 2 {
        let mut tmp = [0u8; 3];
        tmp[0] = src[3 * k];
        tmp[1] = src[3 * k + 1];
        proof {
            assert(tmp@.len() == 3);
            assert(tmp@[0] == s[3 * k]);
            assert(tmp@[1] == s[3 * k + 1]);
            assert(tmp@[2] == 0);
        }
        if padded {
            /* Origin Rust: flag is constantly false -> mask == 0xFF: dst_rem[2] stays, dst_rem[3] = PAD */
            let (i0, i1, i2, i3) = encode_pack_indices_std(&tmp);
            proof {
                assert(0 <= i0 <= 63);
                assert(0 <= i1 <= 63);
                assert(0 <= i2 <= 63);
            }
            dst[4 * k] = encode_6bits_std(i0);
            dst[4 * k + 1] = encode_6bits_std(i1);
            dst[4 * k + 2] = encode_6bits_std(i2);
            dst[4 * k + 3] = 0x3D;
            proof {
                assert forall|j: int| 4 * k <= j < elen as int implies
                    dst@[j] == b64_encode_model_std(s, padded)[j] by {
                    lemma_enc_index(s, padded, j);
                    let o = j - 4 * k;
                    if o == 0 || o == 1 || o == 2 {
                        assert(b64_encode_pos_std(s, padded, j)
                            == b64_char_std(b64_enc_idx_std(tmp@, o)));
                    } else {
                        assert(b64_encode_pos_std(s, padded, j) == 0x3D);
                        assert(dst@[j] == 0x3D);
                    }
                }
            }
        } else {
            let (i0, i1, i2, i3) = encode_pack_indices_std(&tmp);
            proof {
                assert(0 <= i0 <= 63);
                assert(0 <= i1 <= 63);
                assert(0 <= i2 <= 63);
            }
            dst[4 * k] = encode_6bits_std(i0);
            dst[4 * k + 1] = encode_6bits_std(i1);
            dst[4 * k + 2] = encode_6bits_std(i2);
            proof {
                assert forall|j: int| 4 * k <= j < 4 * k + 3 implies
                    dst@[j] == b64_encode_model_std(s, padded)[j] by {
                    lemma_enc_index(s, padded, j);
                    let o = j - 4 * k;
                    assert(b64_encode_pos_std(s, padded, j)
                        == b64_char_std(b64_enc_idx_std(tmp@, o)));
                }
                assert(elen as int == 4 * k + 3);
            }
        }
    }
    proof {
        // Summary: the invariant (full blocks) + the tail (discharged in its branches) covers [0, elen)
        assert forall|j: int| 0 <= j < elen as int implies
            dst@[j] == b64_encode_model_std(s, padded)[j] by {
            lemma_enc_index(s, padded, j);
            if j < 4 * k {
                assert(b64_encode_pos_std(s, padded, j)
                    == b64_char_std(b64_enc_idx_std(
                        s.subrange(3 * (j / 4), 3 * (j / 4) + 3),
                        j % 4,
                    )));
            }
        }
    }
    Result::Ok(elen)
}


/* ============================================================
 * validate_last_block (the executable body of the canonical criterion)
 * ============================================================ */

/// Origin: encoding.rs:299-337 `validate_last_block` (monomorphized for std)
/// The non-short-circuit fold-zip comparison of the re-encoded tail decoded block vs the tail encoded block
/// Upstream doc (encoding.rs:299-300):
///   Validate that the last block of the decoded data round-trips back to the
///   encoded data.
pub exec fn validate_last_block_std(encoded: &[u8], decoded: &[u8], padded: bool) ->
    (r: Result<(), Error>)
    ensures
        r.is_ok() ==> ((encoded@.len() == 0
            && decoded@.len() == 0)
            || b64_tailblock_zip_ok_std(encoded@, decoded@, padded)),
        r.is_ok() ==> !b64_tailblock_zip_mismatch_exists_std(encoded@, decoded@, padded),
        (encoded@.len() == 0 && decoded@.len() == 0) ==> r.is_ok(),
        (!b64_tailblock_zip_mismatch_exists_std(encoded@, decoded@, padded)
            && (encoded@.len() > 0 || decoded@.len() > 0)) ==> r.is_ok(),
        r == Result::Err(Error::InvalidLength) ==> (decoded@.len() > 3),

{
    /* Origin Rust: if encoded.is_empty() && decoded.is_empty() { return Ok(()); } */
    if encoded.len() == 0 && decoded.len() == 0 {
        return Result::Ok(());
    }
    /* Origin Rust: fn last_block_start(bytes: &[u8], block_size: usize) -> usize {
       (bytes.len().saturating_sub(1) / block_size) * block_size }
       -- saturating_sub is expanded into explicit branches, semantics preserved */
    let ebs = if encoded.len() == 0 {
        0
    } else {
        ((encoded.len() - 1) / 4) * 4
    };
    let dbs = if decoded.len() == 0 {
        0
    } else {
        ((decoded.len() - 1) / 3) * 3
    };
    let ghost nenc = encoded@.len() as int;
    let ghost ndec = decoded@.len() as int;
    let ghost ebsg: int = if nenc == 0 {
        0
    } else {
        ((nenc - 1) / 4) * 4
    };
    let ghost dbsg: int = if ndec == 0 {
        0
    } else {
        ((ndec - 1) / 3) * 3
    };
    /* Origin Rust: let enc_block = encoded.get(last_block_start(encoded, 4)..)?;
       let dec_block = decoded.get(last_block_start(decoded, 3)..)?;
       -- get(..) is always Some here, so the slice is taken directly (the exec index is in range via the length facts) */
    let enc_block = &encoded[ebs..];
    let dec_block = &decoded[dbs..];
    /* Origin Rust: let mut buf = [0u8; 4]; let block = T::encode(dec_block, &mut buf)?; */
    let mut buf = [0u8; 4];
    let bslice: &mut [u8] = &mut buf;
    let elen_r = encode_std(dec_block, bslice, padded);
    let blen: usize;
    match elen_r {
        Result::Ok(v) => {
            blen = v;
        }
        Result::Err(_) => {
            proof {
                // encode can only fail via elen > buf(=4) or a 4*ceil(n/3) overflow => the dec block must be >= 4 bytes
                if dec_block.len() as int <= 3 {
                    assert(4 * ((dec_block.len() as int + 2) / 3) <= usize::MAX as int);
                    assert(b64_elen_model_std(dec_block.len() as int, padded) as int <= 4);
                    assert(b64_elen_model_std(dec_block.len() as int, padded) as int <= 4);
                    assert(elen_r.is_ok());
                    assert(false);
                }
                assert(decoded.len() >= 4);
            }
            return Result::Err(Error::InvalidLength); // From<InvalidLengthError> for Error
        }
    }
    proof {
        // The encode success basis: model elen = blen <= buf.len() = 4
        assert(blen as int == b64_elen_model_std(dec_block@.len() as int, padded) as int);
        assert(b64_encode_model_std(dec_block@, padded).len()
            == b64_elen_model_std(dec_block@.len() as int, padded));
        assert forall|j: int| 0 <= j < blen as int implies
            bslice@[j] == b64_encode_model_std(dec_block@, padded)[j] by {
            lemma_enc_index(dec_block@, padded, j);
        }
        assert forall|j: int| 0 <= j < blen as int implies
            bslice@[j]
                == b64_encode_pos_std(dec_block@, padded, j) by {}
    }
    /* Origin Rust: block.as_bytes().iter().zip(enc_block.iter())
       .fold(0, |acc, (a, b)| acc | (a ^ b)) == 0 */
    let zlen = if blen < enc_block.len() {
        blen
    } else {
        enc_block.len()
    };
    let mut acc: u8 = 0;
    let mut j: usize = 0;
    // GHOST bookkeeping (relax ledger: the counterexample witness position; a pure proof aid that never
    // enters the data plane -- the constant-time property of the upstream fold is unaffected, since a ghost compiles to nothing)
    let ghost mut jst: int = -1;
    proof {
        assert(bslice.len() == 4);
        assert(blen <= bslice.len());
    }
    while j < zlen
        invariant
            0 <= j <= zlen,
            zlen as int <= blen as int,
            zlen <= bslice.len(),
            zlen <= enc_block.len(),
            zlen as int <= enc_block@.len(),
            enc_block@ == encoded@.subrange(ebsg, nenc),
            blen as int <= bslice@.len(),
            (acc == 0) == (forall|q: int| 0 <= q < j as int ==> bslice@[q] == enc_block@[q]),
            (jst == -1 && acc == 0)
                || (0 <= jst < j as int
                    && bslice@[jst] != enc_block@[jst]),
        decreases zlen - j
    {
        proof {
            assert(j < zlen);
            assert(j < bslice.len());
            assert(j < enc_block.len());
        }
        let ai = bslice[j];
        let bi = enc_block[j];
        let x = ai ^ bi;
        let nacc = acc | x;
        proof {
            // Counterexample-position bookkeeping: the first mismatch location
            if ai != bi {
                if jst == -1 {
                    jst = j as int;
                }
            }
        }
        proof {
            // The zero property of u8 OR/XOR: `acc | x == 0 <==> acc == 0 && x == 0` (one bit-level step)
            let av = acc;
            let xv = x;
            let nv = nacc;
            assert((nv == (av | xv)) && (nv == (0u8)) ==> (av == (0u8)) && (xv == (0u8))) by (bit_vector);
            assert((nv == (av | xv)) && (av == (0u8)) && (xv == (0u8)) ==> (nv == (0u8))) by (bit_vector);
            assert(ai == bslice@[j as int]);
            assert(bi == enc_block@[j as int]);
            assert((x == ((ai ^ bi) as u8)) ==> ((x == (0u8)) <==> (ai == bi))) by (bit_vector);
        }
        acc = nacc;
        j += 1;
    }
    proof {
        assert((acc == 0) == (forall|q: int| 0 <= q < zlen as int ==> bslice@[q] == enc_block@[q]));
        assert(dec_block@ == decoded@.subrange(dbsg, ndec));
        assert(enc_block@ == encoded@.subrange(ebsg, nenc));
        assert(zlen as int <= b64_encode_model_std(dec_block@, padded).len() as int);
        assert(zlen as int <= nenc - ebsg);
        // The per-position iff bridge (shared by both directions; the counterexample side is grounded by the ghost witness jst)
        assert forall|j: int|
            0 <= j < b64_encode_model_std(dec_block@, padded).len() as int
                && 0 <= j < nenc - ebsg
            implies
            ((b64_encode_model_std(dec_block@, padded)[j] == encoded@ [ebsg + j])
                <==> (bslice@[j] == enc_block@[j])) by {
            lemma_enc_index(dec_block@, padded, j);
            assert(j < zlen as int);
            assert(enc_block@.len() as int == nenc - ebsg);
            assert(0 <= j && j< enc_block@.len());
            assert(enc_block@[j] == encoded@.subrange(ebsg, nenc)[j]);
        }
        assert(dec_block@.len() as int == ndec - dbsg);
        assert(b64_encode_model_std(decoded@.subrange(dbsg, ndec), padded)
            == b64_encode_model_std(dec_block@, padded));
    }
    /* Origin Rust: if ... == 0 { Ok(()) } else { Err(Error::InvalidEncoding) } */
    if acc == 0 {
        proof {
            assert(b64_encode_model_std(decoded@.subrange(dbsg, ndec), padded)
                == b64_encode_model_std(dec_block@, padded));
            assert forall|j: int|
                0 <= j < b64_encode_model_std(decoded@.subrange(dbsg, ndec), padded).len() as int
                    && 0 <= j < nenc - ebsg implies
                b64_encode_model_std(decoded@.subrange(dbsg, ndec), padded)[j]
                    == encoded@ [ebsg + j] by {
                lemma_enc_index(decoded@.subrange(dbsg, ndec), padded, j);
                assert(j < zlen as int);
                assert(bslice@[j] == enc_block@[j]);
                assert(b64_encode_model_std(dec_block@, padded)[j]
                    == b64_encode_pos_std(dec_block@, padded, j));
                assert(b64_encode_pos_std(dec_block@, padded, j) == bslice@[j]);
                assert(enc_block@[j] == encoded@.subrange(ebsg, nenc)[j]);
            }
        }
        return Result::Ok(());
    } else {
        proof {
            assert(b64_encode_model_std(decoded@.subrange(dbsg, ndec), padded)
                == b64_encode_model_std(dec_block@, padded));
            assert(0 <= jst < zlen as int);
            assert(0 <= jst
                < b64_encode_model_std(decoded@.subrange(dbsg, ndec), padded).len() as int);
            assert(0 <= jst < nenc - ebsg);
            assert(bslice@[jst] != enc_block@[jst]);
            lemma_enc_index(dec_block@, padded, jst);
            assert(b64_encode_pos_std(dec_block@, padded, jst) == bslice@[jst]);
            assert(b64_encode_model_std(dec_block@, padded)[jst]
                == bslice@[jst]);
            assert(enc_block@ == encoded@.subrange(ebsg, nenc));
            assert(enc_block@.len() as int == nenc - ebsg);
            assert(0 <= jst && jst < enc_block@.len());
            assert(encoded@.subrange(ebsg, nenc).len() as int == nenc - ebsg);
            assert(0 <= jst && jst < encoded@.subrange(ebsg, nenc).len());
            assert(enc_block@[jst] == encoded@.subrange(ebsg, nenc)[jst]);
            assert(encoded@.subrange(ebsg, nenc).len() == enc_block@.len());
            vstd::seq::lemma_seq_subrange_index(encoded@, ebsg, nenc, jst);
            assert(encoded@.subrange(ebsg, nenc)[jst] == encoded@ [ebsg + jst]);
            assert(b64_encode_model_std(dec_block@, padded)[jst]
                != encoded@ [ebsg + jst]);
            let dbsv = (if decoded@.len() == 0 {
                0
            } else {
                ((decoded@.len() as int - 1) / 3) * 3
            });
            let ebsv = (if encoded@.len() == 0 {
                0
            } else {
                ((encoded@.len() as int - 1) / 4) * 4
            });
            assert(dbsv == dbsg);
            assert(ebsv == ebsg);
            assert(decoded@.len() as int == ndec);
            assert(encoded@.len() as int == nenc);
            assert(
                jst < b64_elen_model_std(decoded@.subrange(dbsv, decoded@.len() as int).len() as int, padded) as int
            );
            assert(0 <= jst && jst < encoded@.len() as int - ebsv);
            assert(
                b64_encode_model_std(decoded@.subrange(dbsv, decoded@.len() as int), padded)[jst]
                    != encoded@ [ebsv + jst]
            );
            lemma_mismatch_at_implies_exists(encoded@, decoded@, padded, jst);
        }
        return Result::Err(Error::InvalidEncoding);
    }
}


/* ============================================================
 * The decode driver (standard alphabet x the two padded cases)
 * ============================================================ */

/// Origin: encoding.rs:64-102 `Encoding::decode` (generic monomorphized for std)
/// (below u = padded ? n - pad_count : n, and dl = decoded_len(u))
/// Upstream doc (encoding.rs:32-32):
///   Decode a Base64 string into the provided destination buffer.
pub exec fn decode_std(src: &[u8], dst: &mut [u8], padded: bool) -> (r: Result<usize, Error>)
    ensures
        (padded && (src@.len() as int % 4 != 0)) ==> (r == Result::Err(Error::InvalidEncoding)),
        (padded && src@.len() as int % 4 == 0 && !b64_pad_ok_std(src@)
            && b64_dec_len_model_std(if padded {
                src@.len() as int - b64_pad_count_std(src@)
            } else {
                src@.len() as int
            }) <= old(dst)@.len() as int) ==> (r
            == Result::Err(Error::InvalidEncoding)),
        (if padded {
            b64_pad_ok_std(src@)
        } else {
            true
        }) && (b64_dec_len_model_std(if padded {
            src@.len() as int - b64_pad_count_std(src@)
        } else {
            src@.len() as int
        }) > old(dst)@.len() as int) ==> (r == Result::Err(Error::InvalidLength)),
        (r.is_ok() && padded) ==> (src@.len() as int % 4 == 0 && b64_pad_ok_std(src@)),
        r.is_ok() ==> (b64_dec_len_model_std(if padded {
            src@.len() as int - b64_pad_count_std(src@)
        } else {
            src@.len() as int
        }) <= old(dst)@.len() as int),
        // The output-correctness face (as separate clauses):
        (r.is_ok()) ==> (r.get_Ok_0() == (b64_dec_len_model_std(if padded {
            src@.len() as int - b64_pad_count_std(src@)
        } else {
            src@.len() as int
        }) as int) as usize),
        // Note: the u%4!=1 face of decodes (an Ok exit can never reach rem==1) relies on the reverse
        // decomposition of the err convergence, not closed here; the Ok-side u%4 in {0,2,3}
        // is shown composed from the pad/character faces and the validate contract at the harness layer.
        // The sufficiency face (for error classification) -- canonical/content sufficiency is left open
        // (SMT counterexample-interface cost; recorded in the relax ledger, out/bug-finder-summary.md);
        // the pads/character/length faces are covered via the error-classification clauses and the err convergence path.
{
    /* Origin Rust: let (src_unpadded, mut err) = if T::PADDED { decode_padding... } else (src, 0) */
    let mut err: i16 = 0;
    let mut u: usize = 0;
    if padded {
        let rp = decode_padding_std(src);
        match rp {
            Result::Err(_) => {
                return Result::Err(Error::InvalidEncoding);
            }
            Result::Ok((u0, perr)) => {
                u = u0;
                err = perr;
            }
        }
    } else {
        u = src.len();
    }
    let ghost perr0: int = err as int;
    /* Origin Rust: let dlen = decoded_len(src_unpadded.len());
       if dlen > dst.len() { return Err(Error::InvalidLength); } */
    let dlen = decoded_len(u);
    if dlen > dst.len() {
        return Result::Err(Error::InvalidLength);
    }
    let ghost sv = src@;
    let ghost uv: int = u as int;
    let ghost dlenv: int = dlen as int;
    let ghost dl = dst@.len();
    let ghost ug = sv.subrange(0, uv);
    let k = u / 4;
    let ghost kg: int = k as int;
    let rem_u = u % 4;
    let ghost remg: int = rem_u as int;
    proof {
        assert(uv == if padded {
            sv.len() as int - b64_pad_count_std(sv)
        } else {
            sv.len() as int
        });
        assert(dlenv == b64_dec_len_model_std(uv));
        assert(ug.len() as int == uv);
        assert(remg == uv % 4);
        assert(4 * kg <= uv);
        assert(3 * kg + (3 * remg) / 4 == dlenv);
    }
    /* Origin Rust: for (s, d) in (&mut src_chunks).zip(&mut dst_chunks) { err |= Self::decode_3bytes(s, d); }
       -- the chunks_exact(4) x chunks_exact_mut(3) zip is rewritten as an index loop */
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            sv == src@,
            uv == (u as int),
            remg == uv % 4,
            kg == uv / 4,
            kg == k as int,
            ug == sv.subrange(0, uv),
            4 * kg <= uv,
            uv <= sv.len() as int,
            u <= src.len(),
            3 * kg <= dlenv,
            4 * kg + remg == uv,
            dlenv == b64_dec_len_model_std(uv),
            dlen as int == dlenv,
            dst@.len() == dl,
            dst.len() as int >= dlenv,
            0 <= err <= 1,
            perr0 == (if padded {
                b64_pad_err_std(sv)
            } else {
                0
            }),
            (err == 0) == (perr0 == 0
                && forall|b: int| #![trigger b64_digit_std(sv[4 * b])] 0 <= b < (i as int) ==> (
                    0 <= b64_digit_std(sv[4 * b]) && b64_digit_std(sv[4 * b]) <= 63
                        && 0 <= b64_digit_std(sv[4 * b + 1])
                        && b64_digit_std(sv[4 * b + 1]) <= 63
                        && 0 <= b64_digit_std(sv[4 * b + 2])
                        && b64_digit_std(sv[4 * b + 2]) <= 63
                        && 0 <= b64_digit_std(sv[4 * b + 3])
                        && b64_digit_std(sv[4 * b + 3]) <= 63)),
            forall|j: int|
                0 <= j < 3 * (i as int) && (b64_digit_std(sv[4 * (j / 3)])
                    != -1 && b64_digit_std(sv[4 * (j / 3) + 1]) != -1
                    && b64_digit_std(sv[4 * (j / 3) + 2]) != -1
                    && b64_digit_std(sv[4 * (j / 3) + 3]) != -1) ==> (dst@[j]
                == b64_decode_pos_std(ug, j)),
        decreases k - i
    {
        proof {
            assert((i as int) + 1 <= kg);
            assert(4 * ((i as int) + 1) <= 4 * kg && 4 * kg <= uv);
            assert(4 * (i as int) + 4 <= uv);
            assert(4 * (i as int) + 4 <= src.len() as int);
            assert(3 * ((i as int) + 1) <= 3 * kg && 3 * kg <= dlenv);
            assert(3 * (i as int) + 3 <= dlenv);
            assert(3 * (i as int) + 3 <= dst.len() as int);
        }
        let ghost pre_dst = dst@;
        let ghost perr_prev: i16 = err;
        let ev = decode_3bytes_std_at(src, 4 * i, dst, 3 * i);
        err = err | ev;
        proof {
            // The zero property of the bitwise OR (err, ev in {0,1})
            let av = perr_prev;
            assert((err == (av | ev)) && av >= (0i16) && av <= (1i16) && ev >= (0i16)
                && ev <= (1i16) ==> (err >= (0i16)) && (err <= (1i16))) by (bit_vector);
            assert(((err == (av | ev)) && av == (0i16) && ev == (0i16)) ==> (err == (0i16))) by (bit_vector);
            assert(((err == (av | ev)) && (av == (0i16)) && (ev == (1i16))) ==> (err == (1i16))) by (bit_vector);
            assert(((err == (av | ev)) && (av == (1i16)) && (ev >= (0i16))
                && (ev <= (1i16))) ==> (err == (1i16))) by (bit_vector);
            // The content bridge: the _at post vs the pos model (a fully valid block)
            assert forall|j: int|
                3 * (i as int) <= j < 3 * (i as int) + 3
                    && (b64_digit_std(sv[4 * (j / 3)])
                        != -1 && b64_digit_std(sv[4 * (j / 3) + 1]) != -1
                        && b64_digit_std(sv[4 * (j / 3) + 2]) != -1
                        && b64_digit_std(sv[4 * (j / 3) + 3]) != -1) implies
                dst@[j] == b64_decode_pos_std(ug, j) by {
                let b = (j as int) / 3;
                let oo = j - 3 * b;
                let dm = b64_dec_bytes_std(
                    b64_digit_std(sv[4 * b]),
                    b64_digit_std(sv[4 * b + 1]),
                    b64_digit_std(sv[4 * b + 2]),
                    b64_digit_std(sv[4 * b + 3]),
                );
                if oo == 0 {
                    assert(dst@[j] as int == dm.0);
                } else if oo == 1 {
                    assert(dst@[j] as int == dm.1);
                } else {
                    assert(dst@[j] as int == dm.2);
                }
            }
            // Frame: [0, 3i) unchanged
            assert forall|j: int|
                0 <= j < 3 * (i as int) implies dst@[j] == pre_dst[j] by {
                assert(j >= 0);
                assert(j < 3 * (i as int) + 3);
                assert(j < dl);
            }
        }
        i += 1;
    }
    /* Origin Rust: err |= !(src_rem.is_empty() || src_rem.len() >= 2) as i16;
       -- 0 for rem in {0,2,3}; 1 for rem == 1 */
    let rem = rem_u;
    let ghost mut rem1err: bool = false;
    if rem == 1 {
        let ghost prev_err1: i16 = err;
        err = err | 1;
        proof {
            assert(((err == ((prev_err1) | ((1i16)))) ==> (err != (0i16)))) by (bit_vector);
            rem1err = true;
        }
    }
    /* Origin Rust: let mut tmp_out = [0u8; 3]; let mut tmp_in = [b'A'; 4];
       tmp_in[..src_rem.len()].copy_from_slice(src_rem);
       err |= Self::decode_3bytes(&tmp_in, &mut tmp_out);
       dst_rem.copy_from_slice(&tmp_out[..dst_rem.len()]);
       -- the compose expansion: the 'A' padding is digit 0; the write set is exactly [3k, dlen) */
    let ghost mut remev: i16 = 0;
    if rem == 1 {
        err = err | 1;
    }
    if rem == 2 || rem == 3 {
        proof {
            assert(4 * kg + remg == uv);
            assert(4 * kg + remg <= src.len() as int);
            assert(3 * kg + (3 * remg) / 4 == dlenv);
            assert(4 * kg + 2 <= uv);
            assert(4 * kg + 1 < sv.len() as int);
            assert(3 * kg + 1 <= dlenv);
            if rem == 3 {
                assert(3 * kg + 2 <= dlenv);
            }
        }
        let c0v = decode_6bits_std(src[4 * k]);
        let c1v = decode_6bits_std(src[4 * k + 1]);
        let (c2v, c3v);
        if rem == 3 {
            c2v = decode_6bits_std(src[4 * k + 2]);
            c3v = decode_6bits_std(0x41);
        } else {
            c2v = decode_6bits_std(0x41);
            c3v = decode_6bits_std(0x41);
        }
        let ghost perr2_prev: i16 = err;
        let (ev, d0v, d1v, d2v) = decode_pack_std(c0v, c1v, c2v, c3v);
        err = err | ev;
        proof {
            remev = ev;
            let av = perr2_prev;
            assert((err == ((av | ev))) && av >= (0i16) && av <= (1i16) && ev >= (0i16)
                && ev <= (1i16) ==> (err >= (0i16)) && (err <= (1i16))) by (bit_vector);
            assert(((err == ((av | ev))) && av == (0i16) && ev == (0i16)) ==> (err == (0i16))) by (bit_vector);
            assert(((err == ((av | ev))) && (av == (0i16)) && (ev == (1i16))) ==> (err == (1i16))) by (bit_vector);
            assert(((err == ((av | ev))) && (av == (1i16)) && (ev >= (0i16))
                && (ev <= (1i16))) ==> (err == (1i16))) by (bit_vector);
            assert(c0v == b64_digit_std(sv[4 * kg]));
            assert(c1v == b64_digit_std(sv[4 * kg + 1]));
            if rem == 3 {
                assert(c2v == b64_digit_std(sv[4 * kg + 2]));
                assert(c3v == 0);
            } else {
                assert(c2v == 0);
                assert(c3v == 0);
            }
        }
        if rem == 2 {
            dst[3 * k] = d0v;
            proof {
                assert(dlenv == 3 * kg + 1);
                if b64_digit_std(sv[4 * kg]) != -1 && b64_digit_std(sv[4 * kg + 1]) != -1 {
                    assert(0 <= b64_digit_std(sv[4 * kg]));
                    assert(0 <= b64_digit_std(sv[4 * kg + 1]));
                    assert(c2v == 0 && c3v == 0);
                    assert(dst@[3 * kg] as int
                        == b64_dec_bytes_std(
                            b64_digit_std(sv[4 * kg]),
                            b64_digit_std(sv[4 * kg + 1]),
                            0,
                            0,
                        ).0);
                    assert(dst@[3 * kg]
                        == b64_dec_bytes_std(
                            b64_digit_std(sv[4 * kg]),
                            b64_digit_std(sv[4 * kg + 1]),
                            0,
                            0,
                        ).0 as u8);
                    assert(dst@[3 * kg] == b64_decode_pos_std(ug, 3 * kg));
                }
            }
        } else {
            dst[3 * k] = d0v;
            dst[3 * k + 1] = d1v;
            proof {
                assert(dlenv == 3 * kg + 2);
                if b64_digit_std(sv[4 * kg]) != -1
                    && b64_digit_std(sv[4 * kg + 1]) != -1
                    && b64_digit_std(sv[4 * kg + 2]) != -1
                {
                    assert(c3v == 0);
                    assert(dst@[3 * kg] as int
                        == b64_dec_bytes_std(
                            b64_digit_std(sv[4 * kg]),
                            b64_digit_std(sv[4 * kg + 1]),
                            b64_digit_std(sv[4 * kg + 2]),
                            0,
                        ).0);
                    assert(dst@[3 * kg + 1] as int
                        == b64_dec_bytes_std(
                            b64_digit_std(sv[4 * kg]),
                            b64_digit_std(sv[4 * kg + 1]),
                            b64_digit_std(sv[4 * kg + 2]),
                            0,
                        ).1);
                    assert(dst@[3 * kg] == b64_decode_pos_std(ug, 3 * kg));
                    assert(dst@[3 * kg + 1] == b64_decode_pos_std(ug, 3 * kg + 1));
                }
            }
        }
    }
    /* Origin Rust: if err == 0 { validate_last_block::<T>(src.as_ref(), dst)?; Ok(dst) }
       else { Err(Error::InvalidEncoding) } */
    if err != 0 {
        return Result::Err(Error::InvalidEncoding);
    }
    let rv = validate_last_block_std(src, &dst[..dlen], padded);
    match rv {
        Result::Ok(()) => {
            return Result::Ok(dlen);
        }
        Result::Err(e) => {
            return Result::Err(e);
        }
    }
}

} // verus!
