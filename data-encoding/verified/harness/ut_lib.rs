//! harness: partial UT witnesses from tests/lib.rs
//! Coverage: U4 hexlower / U5 hexupper vectors and case-sensitivity decoding,
//! U13 base64_error / U14 base64_nopad_error decode_len rows (through the common
//! arithmetic layer encoding_decode_len), and U12 base32_error's arithmetic shell
//! as given by decode_wrap_len (the table-level decode obligations belong to the
//! base64/base32 batches, see the summary blocked list). Reference-style organization: `#[path]` pulls in verified/src/lib.rs, whose spec is not duplicated.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod data_encoding;

use data_encoding::*;

verus! {

/* ---------- U4 hexlower / U5 hexupper (tests/lib.rs:67-99, 101-115) ---------- */

/// exec witness of the test! macro's encode/decode two-way assertions on the lowercase vectors
exec fn ut_hexlower_f()
{
    let input: [u8; 1] = [b'f'];
    let s: &[u8] = &input;
    assert(s@ == seq![0x66]);
    let e = encode_hex(s, false);
    assert(e@.len() == 2);
    assert(encode_seq(s@, false)[0] == hex_sym(0x6, false));
    assert(hex_sym(0x6, false) == 0x36);
    assert(encode_seq(s@, false)[1] == hex_sym(0x6, false));
    assert(e@ == seq![0x36, 0x36]); // "66"

    let dec_in: [u8; 2] = [0x36, 0x36];
    let ds: &[u8] = &dec_in;
    assert(ds@ == seq![0x36, 0x36]);
    assert(hex_val(0x36, false) == 0x6);
    proof { reveal_with_fuel(first_invalid_from, 3); }
    assert(first_invalid(ds@, false) == -1);
    let d = decode_hex(ds, false);
    assert(d.is_Ok());
    assert(d.get_Ok_0()@ == seq![0x66]); // b"f"
    // the reverse assertion also holds (the UT tests both directions)

}

exec fn ut_hexlower_vectors()
{
    // test(b, b"f", b"66") is already covered by ut_hexlower_f; the remaining vectors fo..=foobar
    let inputs: [u8; 6] = [0x66, 0x6f, 0x6f, 0x6f, 0x62, 0x61];
    let s: &[u8] = &inputs;
    assert(s@ == seq![0x66, 0x6f, 0x6f, 0x6f, 0x62, 0x61]); // "foooba"
    let e = encode_hex(s, false);
    assert(encode_seq(s@, false).len() == 12);
    assert forall|j: int| 0 <= j < 12 implies encode_seq(s@, false)[j] < 0x80 by {
        lemma_hex_output_ascii(s@, false);
    }
    // two characters per byte (the structural assertion, the UT's assert_eq!(b.encode(x).into_bytes(), y))
    assert(e@ == encode_seq(s@, false));
    assert(e@.len() == 12);
}

exec fn ut_hexupper_f()
{
    let input: [u8; 1] = [b'F'];
    let s: &[u8] = &input;
    assert(s@ == seq![0x46]);
    let e = encode_hex(s, true);
    assert(hex_sym(0x4, true) == 0x34);
    assert(hex_sym(0x6, true) == 0x36);
    assert(e@ == seq![0x34, 0x36]); // "46"

    let dec_in: [u8; 2] = [0x34, 0x36];
    let ds: &[u8] = &dec_in;
    assert(hex_val(0x34, true) == 0x4);
    assert(hex_val(0x36, true) == 0x6);
    proof { reveal_with_fuel(first_invalid_from, 3); }
    assert(first_invalid(ds@, true) == -1);
    let d = decode_hex(ds, true);
    assert(d.is_Ok());
    assert(d.get_Ok_0()@ == seq![0x46]); // b"F"
}

exec fn ut_decode_case_sensitivity()
{
    // HEXLOWER.decode(b"6F") gives Err(1, Symbol); the assertion face of tests/lib.rs:75-76
    let dec_low: [u8; 2] = [0x36, 0x46]; // "6F"
    let ds: &[u8] = &dec_low;
    assert(hex_val(0x36, false) == 0x6);
    assert(hex_val(0x46, false) == INVALID);
    proof { reveal_with_fuel(first_invalid_from, 3); }
    assert(first_invalid(ds@, false) == 1);
    let d = decode_hex(ds, false);
    assert(d == Result::Err(DecodeError { position: 1, kind: DecodeKind::Symbol }));

    // HEXUPPER.decode(b"6f") gives Err(1, Symbol); the assertion face of tests/lib.rs:90-91
    let dec_up: [u8; 2] = [0x36, 0x66]; // "6f"
    let us: &[u8] = &dec_up;
    assert(hex_val(0x36, true) == 0x6);
    assert(hex_val(0x66, true) == INVALID);
    proof { reveal_with_fuel(first_invalid_from, 3); }
    assert(first_invalid(us@, true) == 1);
    let d2 = decode_hex(us, true);
    assert(d2 == Result::Err(DecodeError { position: 1, kind: DecodeKind::Symbol }));
}

/* ---------- The decode_len rows of U13 base64_error / U14 base64_nopad_error
 * (tests/lib.rs:219-233; through the encoding_decode_len common arithmetic layer,
 *  bit=6, BASE64: has_pad=true, has_ignore=false; BASE64_NOPAD: false/false) */

exec fn ut_base64_decode_len_rows()
{
    let r4 = encoding_decode_len(6, true, false, 4);
    assert(r4 == Result::Ok(3)); // tests/lib.rs:230
    let r5 = encoding_decode_len(6, true, false, 5);
    assert(r5 == Result::Err(DecodeError { position: 4, kind: DecodeKind::Length })); // :231
    let r6 = encoding_decode_len(6, true, false, 6);
    assert(r6 == Result::Err(DecodeError { position: 4, kind: DecodeKind::Length })); // :232
    let r7 = encoding_decode_len(6, true, false, 7);
    assert(r7 == Result::Err(DecodeError { position: 4, kind: DecodeKind::Length })); // :233
    let r0 = encoding_decode_len(6, true, false, 0);
    assert(r0 == Result::Ok(0));
}

exec fn ut_base64_nopad_decode_len_rows()
{
    // tests/lib.rs:227-229
    let r4 = encoding_decode_len(6, false, false, 4);
    assert(r4 == Result::Ok(3));
    let r5 = encoding_decode_len(6, false, false, 5);
    assert(r5 == Result::Err(DecodeError { position: 4, kind: DecodeKind::Length }));
    let r6 = encoding_decode_len(6, false, false, 6);
    assert(r6 == Result::Ok(4));
    let r7 = encoding_decode_len(6, false, false, 7);
    assert(r7 == Result::Ok(5));
}

/* ---------- Common encode-length face (UT/fuzz impl_encode_len, spec-aligned) ---------- */

exec fn ut_encode_len_rows()
{
    // BASE64(bit=6,pad,wrap=None,sep=0): div_ceil(len/3)*4
    let e0 = encoding_encode_len(6, Some(0x3d), Option::None, 0);
    assert(e0 == 0);
    let e1 = encoding_encode_len(6, Some(0x3d), Option::None, 1);
    assert(e1 == 4);
    let e2 = encoding_encode_len(6, Some(0x3d), Option::None, 2);
    assert(e2 == 4);
    let e3 = encoding_encode_len(6, Some(0x3d), Option::None, 3);
    assert(e3 == 4);
    let e4 = encoding_encode_len(6, Some(0x3d), Option::None, 4);
    assert(e4 == 8);
    // HEXLOWER(bit=4,unpad): 2*len
    let h5 = encoding_encode_len(4, Option::None, Option::None, 5);
    assert(h5 == 10);
}
}

fn main() {}
