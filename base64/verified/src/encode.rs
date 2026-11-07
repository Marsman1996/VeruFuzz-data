//! `encode.rs` mirror -- aggregation of the verified items from code/src/encode.rs
//!   (the full encoded_len contract / the three add_padding contract forms /
//!    encode_with_padding / EncodeSliceError)

use vstd::prelude::*;

verus! {

/* ============================================================
 * Spec model
 * ============================================================ */

/// Closed-form model of encoded_len (the semantic authority of the upstream doc contract)
pub open spec fn encoded_len_model(bytes_len: int, padding: bool) -> Option<usize> {
    let rem = bytes_len % 3;
    let complete_chunk_output = 4 * (bytes_len / 3);
    let raw = if rem > 0 {
        if padding {
            complete_chunk_output + 4
        } else if rem == 1 {
            complete_chunk_output + 2
        } else {
            complete_chunk_output + 3
        }
    } else {
        complete_chunk_output
    };
    if bytes_len < 0 || raw > usize::MAX as int {
        Option::None
    } else {
        Option::Some(raw as usize)
    }
}

/// Pad-count model of add_padding: (4 - n%4)%4
pub open spec fn pad_bytes_model(unpadded_output_len: int) -> int {
    (4 - unpadded_output_len % 4) % 4
}

/* ============================================================
 * Origin: encode.rs:101-129 `encoded_len` (const fn, full contract)
 * ============================================================ */

/// Upstream doc (encode.rs:95-99):
///   Calculate the base64 encoded length for a given input length, optionally including any
///   appropriate padding bytes.
///   Returns `None` if the encoded length can't be represented in `usize`. This will happen for
///   input lengths in approximately the top quarter of the range of `usize`.
pub exec fn encoded_len(bytes_len: usize, padding: bool) -> (r: Option<usize>)
    ensures r == encoded_len_model(bytes_len as int, padding),
{
    /* Origin Rust
       let rem = bytes_len % 3;
       let complete_input_chunks = bytes_len / 3;
       let complete_chunk_output = if let Some(complete_chunk_output) =
           complete_input_chunks.checked_mul(4) { complete_chunk_output }
           else { return None; }; */
    let rem = bytes_len % 3;
    let complete_input_chunks = bytes_len / 3;
    if complete_input_chunks > usize::MAX / 4 {
        /* Origin Rust: return None; (multiplication overflow domain) */
        assert(4 * (bytes_len as int / 3) > usize::MAX as int);
        return Option::None;
    }
    let complete_chunk_output = complete_input_chunks * 4;
    assert(complete_chunk_output@ == 4 * (bytes_len as int / 3));

    /* Origin Rust
       if rem > 0 {
           if padding { complete_chunk_output.checked_add(4) }
           else {
               let encoded_rem = match rem { 1 => 2, _ => 3, };
               complete_chunk_output.checked_add(encoded_rem) } }
       else { Some(complete_chunk_output) } */
    if rem > 0 {
        if padding {
            if complete_chunk_output > usize::MAX - 4 {
                assert(4 * (bytes_len as int / 3) + 4 > usize::MAX as int);
                return Option::None;
            }
            proof {
                assert(complete_chunk_output@ + 4 <= usize::MAX as int);
            }
            Option::Some(complete_chunk_output + 4)
        } else {
            let encoded_rem: usize = if rem == 1 { 2 } else { 3 };
            if complete_chunk_output > usize::MAX - encoded_rem {
                assert(4 * (bytes_len as int / 3) + encoded_rem as int > usize::MAX as int);
                return Option::None;
            }
            proof {
                assert(complete_chunk_output@ + encoded_rem@ <= usize::MAX as int);
            }
            Option::Some(complete_chunk_output + encoded_rem)
        }
    } else {
        Option::Some(complete_chunk_output)
    }
}

/* ============================================================
 * Origin: encode.rs:136-146 `add_padding`
 * doc: "`output` is the slice where padding should be written, of length at least 2."
 * (pad_bytes can reach 3 -- 4 - (1%4) -- so the doc's "at least 2" is mathematically
 *  insufficient; three contract forms below. Withdrawn-FP ruling (2026-11-04): the gap
 *  is real math but harmless in practice -- all 8 upstream call sites pass pad_bytes <= 2
 *  (PR rust-base64#317 closed), so no finding is filed; see the form notes below.)
 * ============================================================ */

/// Form 1: L0 verbatim transcription (no precondition on output's length).
/// Expected error (obligation anchor): unpadded_output_len % 4 == 1 (pad_bytes == 3)
/// with output.len() < 3 panics out of bounds at `output[i]` -- the formal shape of the
/// doc-precondition gap (withdrawn FP, see the banner note above).
/// Expected error: index out of bounds (Expected x1)
/// Upstream doc (encode.rs:131-135):
///   Write padding characters.
///   `unpadded_output_len` is the size of the unpadded but base64 encoded data.
///   `output` is the slice where padding should be written, of length at least 2.
///   Returns the number of padding bytes written.
pub exec fn add_padding_upstream(
    unpadded_output_len: usize,
    padding: u8,
    output: &mut [u8],
) -> (r: usize)
    ensures
        r@ == pad_bytes_model(unpadded_output_len as int),
        r <= 3,
{
    /* Origin Rust: let pad_bytes = (4 - (unpadded_output_len % 4)) % 4; */
    let m = unpadded_output_len % 4;
    assert(m == unpadded_output_len as int % 4);
    let d = 4 - m; /* n%4 in 0..3 => no underflow */
    let pad_bytes = d % 4;
    assert(pad_bytes == (4 - unpadded_output_len as int % 4) % 4);
    /* Origin Rust: for i in 0..pad_bytes { output[i] = padding.as_u8(); }
       -- the loop is rewritten into the spec-equivalent guard form (bridging the machine
          guard to the spec model needs unstable word_axioms instantiation; equivalence rests on the pad_bytes == model assertion already proven above) */
    let mut i: usize = 0;
    while i < pad_bytes
        invariant
            0 <= (i as int) <= (pad_bytes as int) <= 3,
            (pad_bytes as int) == pad_bytes_model(unpadded_output_len as int),
            forall|j: int| 0 <= j < (i as int) ==> output@.len() > j && output@[j] == padding,
        decreases (pad_bytes as int) - (i as int)
    {
        output[i] = padding;   // <-- EXPECTED anchor (under the doc precondition, index out of bounds is reachable)
        i += 1;
    }
    assert(pad_bytes == (4 - unpadded_output_len as int % 4) % 4);
    assert(pad_bytes as int == pad_bytes_model(unpadded_output_len as int));
    pad_bytes
}

/// Form 2: the contract version under the upstream doc precondition (output.len() >= 2).
/// Effect (the formal shape of the doc-precondition gap -- math only, withdrawn FP): the
/// documented precondition does not discharge the out-of-bounds obligation -- unpadded_output_len % 4 == 1 gives pad_bytes == 3 > 2.
/// Expected error: index out of bounds (Expected x1, doc-precondition anchor)
/// Upstream doc (encode.rs:131-135):
///   Write padding characters.
///   `unpadded_output_len` is the size of the unpadded but base64 encoded data.
///   `output` is the slice where padding should be written, of length at least 2.
///   Returns the number of padding bytes written.
pub exec fn add_padding_documented(
    unpadded_output_len: usize,
    padding: u8,
    output: &mut [u8],
) -> (r: usize)
    requires
        output@.len() >= 2, /* doc: "of length at least 2" */
    ensures
        r@ == pad_bytes_model(unpadded_output_len as int),
        r <= 3,
{
    /* Origin Rust: let pad_bytes = (4 - (unpadded_output_len % 4)) % 4; */
    let m = unpadded_output_len % 4;
    assert(m == unpadded_output_len as int % 4);
    let d = 4 - m; /* n%4 in 0..3 => no underflow */
    let pad_bytes = d % 4;
    assert(pad_bytes == (4 - unpadded_output_len as int % 4) % 4);
    /* Origin Rust: for i in 0..pad_bytes { output[i] = padding.as_u8(); }
       -- the loop is rewritten into the spec-equivalent guard form (same rationale
          as the forms 1/2 note above) */
    let mut i: usize = 0;
    while i < pad_bytes
        invariant
            0 <= (i as int) <= (pad_bytes as int) <= 3,
            (pad_bytes as int) == pad_bytes_model(unpadded_output_len as int),
            forall|j: int| 0 <= j < (i as int) ==> output@.len() > j && output@[j] == padding,
        decreases (pad_bytes as int) - (i as int)
    {
        output[i] = padding;   // <-- doc-precondition anchor (withdrawn F1): pad_bytes==3 && len==2 reaches out of bounds
        i += 1;
    }
    assert(pad_bytes == (4 - unpadded_output_len as int % 4) % 4);
    assert(pad_bytes as int == pad_bytes_model(unpadded_output_len as int));
    pad_bytes
}

/// Form 3: the correct precondition (output holds the whole padding) -> 0 errors, every obligation discharged
/// Upstream doc (encode.rs:131-135):
///   Write padding characters.
///   `unpadded_output_len` is the size of the unpadded but base64 encoded data.
///   `output` is the slice where padding should be written, of length at least 2.
///   Returns the number of padding bytes written.
pub exec fn add_padding(
    unpadded_output_len: usize,
    padding: u8,
    output: &mut [u8],
) -> (r: usize)
    requires
        pad_bytes_model(unpadded_output_len as int) <= output@.len(),
    ensures
        r@ == pad_bytes_model(unpadded_output_len as int),
        r <= 3,
        forall|j: int| #![auto] #![trigger final(output)@[j]]
            0 <= j < r@ ==> final(output)@[j] == padding,
        forall|j: int| #![auto] #![trigger final(output)@[j]] #![trigger old(output)@[j]]
            r@ <= j < old(output)@.len() ==> final(output)@[j] == old(output)@[j],
{
    /* Origin Rust: let pad_bytes = (4 - (unpadded_output_len % 4)) % 4; */
    let m = unpadded_output_len % 4;
    assert(m == unpadded_output_len as int % 4);
    let d = 4 - m; /* n%4 in 0..3 => no underflow */
    let pad_bytes = d % 4;
    assert(pad_bytes == (4 - unpadded_output_len as int % 4) % 4);
    /* Origin Rust: for i in 0..pad_bytes { output[i] = padding.as_u8(); }
       -- the loop is rewritten into the spec-equivalent guard form (same rationale as the forms 1/2 note above) */
    let mut i: usize = 0;
    while i < pad_bytes
        invariant
            0 <= (i as int) <= (pad_bytes as int) <= 3,
            (pad_bytes as int) == pad_bytes_model(unpadded_output_len as int),
            (pad_bytes as int) <= output@.len(),
            forall|j: int| 0 <= j < (i as int) ==> output@[j] == padding,
            forall|j: int|
                (i as int) <= j < old(output)@.len() ==> output@[j] == old(output)@[j],
        decreases (pad_bytes as int) - (i as int)
    {
        output[i] = padding;
        i += 1;
    }
    assert((i as int) == pad_bytes as int);
    assert(pad_bytes as int == pad_bytes_model(unpadded_output_len as int));
    assert((pad_bytes as int) <= output@.len());
    pad_bytes
}

/* ============================================================
 * Origin: encode.rs:149-164 `EncodeSliceError`
 * ============================================================ */

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum EncodeSliceError {
    OutputSliceTooSmall,
}

/* ============================================================
 * Origin: encode.rs:68-93 `encode_with_padding`
 * -- not transcribed separately: its semantics = internal_encode (the
 *    encode_scalar_tail of engine/general_purpose/mod.rs)
 *    + add_padding (form 3 in this file -- every obligation discharged, 0 errors)
 *    + the checked_add non-trigger precondition (on the encoded_size contract,
 *    b64+pad == encoded_size == output.len() <= isize::MAX, so the machine addition
 *    never overflows). The harness encode chain composes the 'tail + add_padding'
 *    segments directly, bypassing the word_axioms instantiation gap of the usize sum
 *    (recorded in out/bug-finder-summary.md).
 * ============================================================ */

} // verus!
