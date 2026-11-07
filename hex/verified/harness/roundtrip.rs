//! harness: universal property (fuzz style) + L1 properties
//! Roundtrip contract-level universal property: for any input byte string,
//! encode -> decode necessarily returns the original value.
//! This is the main property of the hex encode/decode pair (the main L1
//! "test-property formalization" property, equivalent to the upstream-style
//! fuzz harness assertion of the "compress -> decompress identity" kind).
//! Reference-style organization: `#[path]` includes verified/src/lib.rs; every
//! lemma call goes to the shared items on the src side.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod hexlib;

use hexlib::*;
use hexlib::lip_none;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------- Main roundtrip theorem ----------

/// Universal property (exec witness form): for any input,
/// decode(encode(input)) == Ok(input) -- the encode/decode roundtrip identity
/// (lowercase).
/// The upstream has no fuzz harness; this is the auto-generated
/// fuzz-style harness assertion.
pub exec fn theorem_roundtrip(input: &[u8]) -> (r: Result<Vec<u8>, FromHexError>)
    ensures
        r.is_ok(),
        r.get_Ok_0()@ == input@[..],
{
    let h = encode(input);
    proof {
        lemma_encoded_all_valid(input@, false);
        assert(first_invalid_pair(h@) == -1);
        // decoded_seq(encode_seq(s)) == s (digit recombination identity)
        assert(decoded_seq(encode_seq(input@, false)).len() == input@.len());
        assert forall|j: int| 0 <= j < input@.len() implies
            decoded_seq(encode_seq(input@, false))[j] == input@ [j] by {
            let b = input@ [j];
            hex_digit_inverse((b / 16) as u8, false);
            hex_digit_inverse((b % 16) as u8, false);
            assert((b / 16) * 16 + (b % 16) == b);
        }
    }
    let r = decode(&h);
    proof {
        assert(first_invalid_pair(h@) == -1);
        assert(h@.len() % 2 == 0);
        let dv = decoded_seq(h@);
        // decoded_seq(encode_seq) == the original sequence (proved above)
        assert(dv == input@);
    }
    r
}

/// Roundtrip example witnesses (UT-style instantiation with concrete
/// inputs): "kiwi" and foobar
exec fn roundtrip_examples()
{
    let kiwi: [u8; 4] = [0x6b, 0x69, 0x77, 0x69];
    let r = theorem_roundtrip(&kiwi);
    assert(r.is_ok());
    assert((r.get_Ok_0())@ == seq![0x6b, 0x69, 0x77, 0x69]);

    let foobar: [u8; 6] = [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72];
    let r2 = theorem_roundtrip(&foobar);
    assert((r2.get_Ok_0())@ == seq![0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72]);
}

// ===========================================================================
// Proof lemmas (moved to the file end; only the order changed)
// ===========================================================================

/// Inverse property of hex_char: a valid nibble goes through the table back
/// to its digit value (positions swapped back)
pub proof fn hex_digit_inverse(nib: u8, upper: bool)
    requires nib < 16
    ensures hex_digit_val(hex_char(nib, upper)) == nib
{
    if nib < 10 {
    } else if upper {
    } else {
    }
}

/// The encode_seq output consists entirely of valid pairs (hence
/// first_invalid == -1)
pub proof fn lemma_encoded_all_valid(s: Seq<u8>, upper: bool)
    ensures first_invalid_pair(encode_seq(s, upper)) == -1
{
    assert(encode_seq(s, upper).len() % 2 == 0);
    assert forall|j: int| 0 <= j < s.len() implies valid_pair(encode_seq(s, upper), j) by {
        let b = s[j];
        hex_digit_inverse((b / 16) as u8, upper);
        hex_digit_inverse((b % 16) as u8, upper);
        assert(encode_seq(s, upper)[2 * j] == hex_char(b / 16, upper));
        assert(encode_seq(s, upper)[2 * j + 1] == hex_char(b % 16, upper));
    }
    lip_none(encode_seq(s, upper));
}

} // verus!

fn main() {}
