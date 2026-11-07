//! `decode.rs` mirror -- aggregation of the verified items from code/src/decode.rs
//!   (the DecodeError / DecodeSliceError types + the decoded_len_estimate delegation)

use vstd::prelude::*;
use super::engine::general_purpose::decode::estimate_decoded_len;

verus! {

/// Origin: decode.rs:10 `DecodeError` (each variant's offset/byte semantics as upstream)
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DecodeError {
    InvalidByte(usize, u8),
    InvalidLength(usize),
    InvalidLastSymbol {
        offset: usize,
        symbol: u8,
        symbol_value: u8,
    },
    InvalidPadding,
}

/// Origin: decode.rs:91 `DecodeSliceError`
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DecodeSliceError {
    DecodeError(DecodeError),
    OutputSliceTooSmall,
}

/// Origin: decode.rs:189 `decoded_len_estimate`
/// Doc example: estimate(1..=4) == 3, estimate(5) == 6
/// Upstream doc (decode.rs:170-174):
///   Returns a conservative estimate of the decoded size of `encoded_len` base64 symbols (rounded up
///   to the next group of 3 decoded bytes).
///   The resulting length will be a safe choice for the size of a decode buffer, but may have up to
///   2 trailing bytes that won't end up being needed.
pub exec fn decoded_len_estimate(encoded_len: usize) -> (r: usize)
    ensures
        r@ == (encoded_len as int / 4 + if encoded_len as int % 4 > 0 { 1int } else { 0int }) * 3,
        0 < encoded_len && encoded_len <= 4 ==> r@ == 3,
        encoded_len == 0 ==> r@ == 0,
{
    /* Origin Rust: STANDARD.internal_decoded_len_estimate(encoded_len).decoded_len_estimate()
       -- machine-levelized into the GeneralPurposeEstimate::new delegation (engine/general_purpose/decode.rs) */
    let (rem, conservative) = estimate_decoded_len(encoded_len);
    /* Origin Rust: .decoded_len_estimate() == conservative_decoded_len */
    assert(conservative@ == (encoded_len as int / 4 + if encoded_len as int % 4 > 0 { 1int } else { 0int }) * 3);
    conservative
}

} // verus!
