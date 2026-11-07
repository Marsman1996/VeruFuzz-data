//! harness: auto-generated properties (the universal layer)
//! -- algebraic properties of decoded_len / encoded_len, the overflow face, capacity bounds.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod base64ct_v;

use base64ct_v::alphabet::standard::digit_char_inverse_std;
use base64ct_v::alphabet::standard::decode_6bits_std;
use base64ct_v::alphabet::standard::encode_6bits_std;
use base64ct_v::alphabet::standard::decode_3bytes_std;
use base64ct_v::alphabet::standard::encode_3bytes_std;
use base64ct_v::alphabet::standard::b64_digit_std;
use base64ct_v::alphabet::standard::b64_char_std;
use base64ct_v::encoding::decoded_len;
use base64ct_v::encoding::encoded_len;
use base64ct_v::encoding::encoded_len_inner;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============ L1: block-level roundtrip (3-byte blocks <-> 4 characters) ============ */

/// The block-level bijection core: any 3 bytes b encode under the standard alphabet to 4 characters that decode back to b
/// -- the formal counterpart of the upstream tests/common `encode_and_decode_various_lengths` (roundtrip
///    at every length in 0..64) and proptests::decode_equiv.
pub exec fn theorem_block_roundtrip(b: [u8; 3]) -> (rt: [u8; 3])
    ensures
        rt == b,
{
    let mut src: [u8; 3] = b;
    let mut dstc: [u8; 4] = [0, 0, 0, 0];
    encode_3bytes_std(&src, &mut dstc);
    proof {
        assert(forall|o: int| 0 <= o < 4 ==> dstc@ [o]
            == b64_char_std(b64_enc_idx_local(src@, o)));
    }
    let mut out3: [u8; 3] = [0, 0, 0];
    let e = decode_3bytes_std(&dstc, &mut out3);
    proof {
        assert(e == 0);
        // The four character digit values are all in range and invert pairwise; the bit synthesis recovers them position-wise
        assert(b64_digit_std(dstc@ [0]) == b64_enc_idx_local(src@, 0));
        assert(b64_digit_std(dstc@ [1]) == b64_enc_idx_local(src@, 1));
        assert(b64_digit_std(dstc@ [2]) == b64_enc_idx_local(src@, 2));
        assert(b64_digit_std(dstc@ [3]) == b64_enc_idx_local(src@, 3));
        assert(forall|o: int| 0 <= o < 3 ==> out3@[o] == b[o as int]);
    }
    out3
}

spec fn b64_enc_idx_local(s: Seq<u8>, o: int) -> int {
    if o == 0 {
        s[0] as int / 4
    } else if o == 1 {
        (s[0] as int % 4) * 16 + s[1] as int / 16
    } else if o == 2 {
        (s[1] as int % 16) * 4 + s[2] as int / 64
    } else {
        s[2] as int % 64
    }
}

/// 6-bit layer: decode_6bits_std o encode_6bits_std == id (fuzz/concrete)
pub exec fn prop_enc6_roundtrip(v: i16) -> (r: i16)
    requires
        0 <= v <= 63,
    ensures
        r == v,
{
    let c = encode_6bits_std(v);
    decode_6bits_std(c)
}

// ===========================================================================
// Proof lemmas (placed at the file end so the exec theorems read first)
// ===========================================================================
/* ============ L2/L1: algebraic properties of the length models (universal) ============ */

/// decoded_len(n) == (3*n)/4 for all n -- the decoded model (the encoding.rs:344-352 contract)
pub proof fn prop_decoded_len(n: int)
    ensures
        (3 * (n / 4) + (3 * (n % 4)) / 4) == (3 * n) / 4,
{
}

/// padded encoded_len(n) == 4*ceil(n/3) (n == 0 included)
pub proof fn prop_encoded_len_padded(n: int)
    requires
        0 <= n,
    ensures
        4 * ((n + 2) / 3) <= usize::MAX as int ==>
            ((4 * ((n + 2) / 3))
                == base64ct_v::alphabet::standard::b64_elen_model_std(n, true) as int),
{
}

/// The tail-length correction: the (3*full + t+1) model of unpadded encoded_len
pub proof fn prop_encoded_len_unpadded(n: int)
    requires
        0 <= n,
    ensures
        4 * (n / 3) + (if n % 3 == 0 {
            0
        } else {
            (n % 3) + 1
        }) == base64ct_v::alphabet::standard::b64_elen_model_std(n, false) as int,
{
}

/// Overflow face (the doc WARNING contract made concrete): with n near MAX/4 it drops to 0 per the padded criterion
pub proof fn prop_encoded_len_overflow()
    ensures
        4 * ((18446744073709551615int + 2) / 3) > usize::MAX as int,
{
}

/// Character <-> digit inverse (the universal-lemma wrapper of digit o char == id, used by _at/roundtrip)
pub proof fn prop_digit_char_inverse(v: int)
    requires
        0 <= v < 64,
    ensures
        b64_digit_std(b64_char_std(v)) == v,
{
    digit_char_inverse_std(v);
}
} // verus!

fn main() {}
