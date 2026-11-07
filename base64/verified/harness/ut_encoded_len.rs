//! harness: tests/encode.rs:49-76 (the three encoded_len tests)
//! + the characterization lemma of estimate_short_lengths
//!   (src/engine/general_purpose/decode.rs:379) + src/encode.rs:183 sample cases.
//!
//! Run: verus database/base64/verified/harness/ut_encoded_len.rs

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod b64;

use b64::encode::encoded_len;
use b64::decode::decoded_len_estimate;

verus! {

/// UT encoded_len_unpadded (tests/encode.rs:49): 0,1,2,3,4, without padding
pub exec fn case_unpadded(n: usize, r: Option<usize>) -> (b: bool)
    requires
        n == 0 && r == Option::Some(0usize)
            || n == 1 && r == Option::Some(2usize)
            || n == 2 && r == Option::Some(3usize)
            || n == 3 && r == Option::Some(4usize)
            || n == 4 && r == Option::Some(6usize),
{
    encoded_len(n, false) == r
}

/// UT encoded_len_padded (tests/encode.rs:61): 0..4, with padding
pub exec fn case_padded(n: usize, r: Option<usize>) -> (b: bool)
    requires
        n == 0 && r == Option::Some(0usize)
            || n == 1 && r == Option::Some(4usize)
            || n == 2 && r == Option::Some(4usize)
            || n == 3 && r == Option::Some(4usize)
            || n == 4 && r == Option::Some(8usize),
{
    encoded_len(n, true) == r
}

/// UT encoded_size_correct_standard (src/encode.rs:183) samples: 54->72, 57->76, 58->80
pub exec fn case_padded_wide(n: usize, r: Option<usize>) -> (b: bool)
    requires
        n == 54 && r == Option::Some(72usize)
            || n == 57 && r == Option::Some(76usize)
            || n == 58 && r == Option::Some(80usize),
{
    encoded_len(n, true) == r
}

/// UT encoded_size_overflow (src/encode.rs:233 / tests/encode.rs:72):
/// usize::MAX returns None even with padding (the doc contract "can't be represented in usize")
pub exec fn case_overflow(n: usize, r: Option<usize>) -> (b: bool)
    requires
        n == usize::MAX,
        r == Option::None,
{
    encoded_len(n, true) == r && encoded_len(n, false) == Option::None
}

/// UT estimate_short_lengths (engine/general_purpose/decode.rs:379)
/// + decoded_len_estimate doc examples (decode.rs:176-187)
pub exec fn case_estimate(n: usize, r: usize) -> (b: bool)
    requires
        n == 0 && r == 0
            || (n == 1 || n == 2 || n == 3 || n == 4) && r == 3
            || n == 5 && r == 6,
{
    decoded_len_estimate(n) == r
}

/// For any input len <= 24, encoded_len(n, pad) when Some satisfies >= n+2 and < 33
/// (the encode_slice buffer upper-bound use; a fuzz_style L1 property)
pub exec fn case_bound_24(n: usize, pad: bool) -> (ok: bool)
    requires
        n <= 24,
{
    let r = encoded_len(n, pad);
    match r {
        Option::Some(v) => (n + 2 <= v) && (v < 33),
        Option::None => true,
    }
}

} // verus!

fn main() {}
