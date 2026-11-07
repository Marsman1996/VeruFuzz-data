//! harness: fuzz-style universal properties (spec_encode_decode / spec_decode_encode)
//! mirroring the assertions of the upstream fuzz_targets/spec_encode_decode.rs and
//! spec_decode_encode.rs: for any input x, decode(encode(x)) == Ok(x); under a canonical
//! encoding the reverse also holds (HEXLOWER/HEXUPPER have no pad/wrap/ignore/translate
//! and ctb is always true => is_canonical). Reference-style organization: `#[path]` pulls in verified/src/lib.rs, whose spec is not duplicated.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod data_encoding;

use data_encoding::*;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/// Roundtrip main theorem (exec witness form, the upstream fuzz assertion "decode(encode(x)) == x"):
/// for any input, the HEXLOWER/HEXUPPER family gives decode(encode(input)) == Ok(input).
pub exec fn theorem_roundtrip(input: &[u8], upper: bool)
    -> (r: Result<Vec<u8>, DecodeError>)
    requires input.len() <= usize::MAX / 2
    ensures
        r.is_Ok()
            && (forall|j: int| 0 <= j < input@.len() ==> r.get_Ok_0()@ [j] == input@ [j])
{
    let enc_out = encode_hex(input, upper);
    proof {
        lemma_encode_bytes_valid(input@, upper);
        let eo = enc_out@;
        assert(eo == encode_seq(input@, upper));
        assert(eo.len() == 2 * input@.len());
        lip_none(eo, upper, 0);
        assert(first_invalid(eo, upper) == -1);
        lemma_decode_encode_inverse_model(input@, upper);
    }
    let dec = decode_hex(&enc_out, upper);
    proof {
        assert(dec.get_Ok_0()@.len() == input@.len());
        assert(dec.get_Ok_0()@ == input@) by {
            assert(dec.get_Ok_0()@ == decode_seq(enc_out@, upper));
            assert(decode_seq(enc_out@, upper) == input@);
        }
    }
    dec
}

/// Reverse direction (spec_decode_encode; the canonical condition holds naturally for the hex family):
/// a valid input s => encode(decode(s)) == s
pub exec fn theorem_canonical_reverse(input: &[u8], upper: bool) -> (r: Vec<u8>)
    requires
        input.len() % 2 == 0,
        input.len() <= usize::MAX / 2,
        first_invalid(input@, upper) == -1,
    ensures r@ == input@
{
    let dec = decode_hex(input, upper);
    proof {
        assert(dec.get_Ok_0()@.len() == input@.len() / 2);
        assert(dec.get_Ok_0()@ == decode_seq(input@, upper));
    }
    let decoded = match dec {
        Result::Ok(v) => v,
        Result::Err(e) => {
            proof { assert(!dec.is_Ok()); assert(dec.is_Ok()); }
            unreachable!()
        }
    };
    proof {
        assert(decoded@ == decode_seq(input@, upper));
        encode_of_decode_identity(input@, upper);
        // encode_seq(decode_seq(s)) == s and the exec output agrees with its model
    }
    let e2 = encode_hex(&decoded, upper);
    proof {
        assert(e2@ == encode_seq(decoded@, upper));
        assert(encode_seq(decode_seq(input@, upper), upper) == input@);
        assert(e2@ == input@);
    }
    e2
}

/// first_invalid == -1 => all bytes are valid (the converse of lip_none)
pub open spec fn valid_from_k(s: Seq<u8>, upper: bool, k: int) -> bool {
    forall|j: int| k <= j < s.len() ==> hex_val(s[j], upper) != INVALID
}


// ===========================================================================
// Proof lemmas (the digit inverse, the decode-after-encode model identity, the
// lip_none converse pair, and the canonical-reverse model identity)
// ===========================================================================
/// Digit invertibility: val after sym recovers the digit (V(S(i)) == i, the
/// hex-alphabet special case of the upstream lib.rs:996-998 correctness condition)
pub proof fn hex_digit_inverse(v: u8, upper: bool)
    requires v < 16
    ensures hex_val(hex_sym(v, upper), upper) == v
{
    if v < 10 {
        let sym = hex_sym(v, upper);
        assert(sym == (0x30 + v as int) as u8);
        assert(0x30 <= sym <= 0x39);
        assert(hex_val(sym, upper) == ((sym as int) - 0x30) as u8);
        assert(sym as int - 0x30 == v as int);
    } else if upper {
        let sym = hex_sym(v, upper);
        assert(sym == (0x41 + (v as int - 10)) as u8);
        assert(0x41 <= sym <= 0x46);
        assert(hex_val(sym, upper) == ((sym as int) - 0x41 + 10) as u8);
        assert(sym as int - 0x41 + 10 == v as int);
    } else {
        let sym = hex_sym(v, upper);
        assert(sym == (0x61 + (v as int - 10)) as u8);
        assert(0x61 <= sym <= 0x66);
        assert(hex_val(sym, upper) == ((sym as int) - 0x61 + 10) as u8);
        assert(sym as int - 0x61 + 10 == v as int);
    }
}

/// decode after encode is the identity at the model level: decode_seq(encode_seq(s)) == s
pub proof fn lemma_decode_encode_inverse_model(s: Seq<u8>, upper: bool)
    ensures decode_seq(encode_seq(s, upper), upper) == s
{
    let e = encode_seq(s, upper);
    assert(e.len() == 2 * s.len());
    assert(s.len() >= 0);
    assert(decode_seq(e, upper).len() == e.len() / 2);
    assert(decode_seq(e, upper).len() == s.len());
    assert forall|j: int| 0 <= j < s.len() implies decode_seq(e, upper)[j] == s[j] by {
        let b = s[j];
        let nh = (b as int / 16) as u8;
        let nl = (b as int % 16) as u8;
        assert(nh < 16 && nl < 16);
        hex_digit_inverse(nh, upper);
        hex_digit_inverse(nl, upper);
        assert(e[2 * j] == hex_sym(nh, upper));
        assert(e[2 * j + 1] == hex_sym(nl, upper));
        assert(hex_val(e[2 * j], upper) == nh);
        assert(hex_val(e[2 * j + 1], upper) == nl);
        assert(decode_seq(e, upper)[j]
            == ((hex_val(e[2 * j], upper) as int) * 16 + hex_val(e[2 * j + 1], upper) as int) as u8);
        assert((nh as int) * 16 + nl as int == b as int);
    }
}

pub proof fn lip_none_converse(s: Seq<u8>, upper: bool)
    requires
        s.len() >= 0,
        first_invalid(s, upper) == -1,
    ensures valid_all_until(s, upper, s.len() as int)
{
    lip_none_converse_from(s, upper, 0);
}

/// first_invalid_from(k) == -1 => valid from k on (structural induction)
pub proof fn lip_none_converse_from(s: Seq<u8>, upper: bool, k: int)
    requires
        0 <= k,
        first_invalid_from(s, upper, k) == -1,
    ensures valid_from_k(s, upper, k),
    decreases s.len() - k
{
    if k >= s.len() {
        assert forall|j: int| k <= j < s.len() implies hex_val(s[j], upper) != INVALID by {}
    } else {
        assert(first_invalid_from(s, upper, k + 1) == -1);
        lip_none_converse_from(s, upper, k + 1);
        assert forall|j: int| k <= j < s.len() implies hex_val(s[j], upper) != INVALID by {}
    }
}

pub proof fn encode_of_decode_identity(s: Seq<u8>, upper: bool)
    requires
        s.len() % 2 == 0,
        first_invalid(s, upper) == -1,
    ensures encode_seq(decode_seq(s, upper), upper) == s
{
    assert(s.len() >= 0);
    lip_none_converse(s, upper);
    let d = decode_seq(s, upper);
    assert(d.len() == s.len() / 2);
    assert(encode_seq(d, upper).len() == s.len());
    assert forall|j: int| 0 <= j < s.len() implies encode_seq(d, upper)[j] == s[j] by {
        let pair = j / 2;
        let hi = hex_val(s[2 * pair], upper);
        let lo = hex_val(s[2 * pair + 1], upper);
        assert(hi != INVALID && lo != INVALID);
        assert(hi < 16 && lo < 16);
        assert(d[pair] == ((hi as int) * 16 + lo as int) as u8);
        if j % 2 == 0 {
            let nib = (d[pair] as int / 16) as u8;
            assert(nib == hi);
            hex_digit_inverse(nib, upper);
            assert(encode_seq(d, upper)[j] == hex_sym(nib, upper));
            assert(hex_sym(nib, upper) == s[j]);
        } else {
            let nib = (d[pair] as int % 16) as u8;
            assert(nib == lo);
            hex_digit_inverse(nib, upper);
            assert(encode_seq(d, upper)[j] == hex_sym(nib, upper));
            assert(hex_sym(nib, upper) == s[j]);
        }
    }
}
}
fn main() {}
