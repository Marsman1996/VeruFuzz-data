//! harness: verification of the slice-class UTs of code/src/lib.rs mod test
//! (U1/U2/U11)
//! Per the inventory: U1 test_encode_to_slice, U2 test_decode_to_slice,
//! U11 test_from_hex_array. Reference-style organization: `#[path]` includes
//! verified/src/lib.rs;
//! the spec/lemmas exist only once on the src side (called here, never
//! copied).
//! All constants inside the UTs are let-bound first (with this Verus build,
//! the inline literal b"..." views have no element axioms;
//! after the local binding the per-element axioms are available).
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod hexlib;

use hexlib::*;
use hexlib::{lip_exact, lip_none};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------- U1: test_encode_to_slice (lib.rs:457-481) ----------

/// kiwi <-> "6b697769", lowercase version
exec fn ut1_encode_to_slice()
{
    let inp: [u8; 4] = [0x6b, 0x69, 0x77, 0x69]; // b"kiwi"
    let mut output_1: [u8; 8] = [0; 8];
    let r1 = encode_to_slice(&inp, &mut output_1);
    assert(r1.is_ok()); // the unwrap never fires: the lengths always match
    assert(inp@ == seq![0x6b, 0x69, 0x77, 0x69]);
    assert(encode_seq(inp@, false).len() == 8);
    assert(encode_seq(inp@, false)[0] == 0x36);
    assert(encode_seq(inp@, false)[1] == 0x62);
    assert(encode_seq(inp@, false)[2] == 0x36);
    assert(encode_seq(inp@, false)[3] == 0x39);
    assert(encode_seq(inp@, false)[4] == 0x37);
    assert(encode_seq(inp@, false)[5] == 0x37);
    assert(encode_seq(inp@, false)[6] == 0x36);
    assert(encode_seq(inp@, false)[7] == 0x39);
    assert(output_1@ == seq![0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39]);
}

/// kiwi <-> "6B697769", uppercase version
exec fn ut1_encode_to_slice_upper()
{
    let inp: [u8; 4] = [0x6b, 0x69, 0x77, 0x69]; // b"kiwi"
    let mut output_1: [u8; 8] = [0; 8];
    let r2 = encode_to_slice_upper(&inp, &mut output_1);
    assert(r2.is_ok());
    assert(encode_seq(inp@, true).len() == 8);
    assert(encode_seq(inp@, true)[0] == 0x36);
    assert(encode_seq(inp@, true)[1] == 0x42);
    assert(encode_seq(inp@, true)[2] == 0x36);
    assert(encode_seq(inp@, true)[3] == 0x39);
    assert(encode_seq(inp@, true)[4] == 0x37);
    assert(encode_seq(inp@, true)[5] == 0x37);
    assert(encode_seq(inp@, true)[6] == 0x36);
    assert(encode_seq(inp@, true)[7] == 0x39);
    assert(output_1@ == seq![0x36, 0x42, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39]);
}

/// kiwis <-> "6b69776973" / "6B69776973" (lib.rs:465-469)
exec fn ut1_encode_to_slice_kiwis()
{
    let inp: [u8; 5] = [0x6b, 0x69, 0x77, 0x69, 0x73]; // b"kiwis"
    let mut output_2: [u8; 10] = [0; 10];
    let r1 = encode_to_slice(&inp, &mut output_2);
    assert(r1.is_ok());
    assert(inp@ == seq![0x6b, 0x69, 0x77, 0x69, 0x73]);
    assert(encode_seq(inp@, false).len() == 10);
    assert(encode_seq(inp@, false)[0] == 0x36);
    assert(encode_seq(inp@, false)[1] == 0x62);
    assert(encode_seq(inp@, false)[2] == 0x36);
    assert(encode_seq(inp@, false)[3] == 0x39);
    assert(encode_seq(inp@, false)[4] == 0x37);
    assert(encode_seq(inp@, false)[5] == 0x37);
    assert(encode_seq(inp@, false)[6] == 0x36);
    assert(encode_seq(inp@, false)[7] == 0x39);
    assert(encode_seq(inp@, false)[8] == 0x37);
    assert(encode_seq(inp@, false)[9] == 0x33);
    assert(output_2@ == seq![0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39, 0x37, 0x33]);
    let r2 = encode_to_slice_upper(&inp, &mut output_2);
    assert(r2.is_ok());
    assert(encode_seq(inp@, true).len() == 10);
    assert(encode_seq(inp@, true)[0] == 0x36);
    assert(encode_seq(inp@, true)[1] == 0x42);
    assert(encode_seq(inp@, true)[2] == 0x36);
    assert(encode_seq(inp@, true)[3] == 0x39);
    assert(encode_seq(inp@, true)[4] == 0x37);
    assert(encode_seq(inp@, true)[5] == 0x37);
    assert(encode_seq(inp@, true)[6] == 0x36);
    assert(encode_seq(inp@, true)[7] == 0x39);
    assert(encode_seq(inp@, true)[8] == 0x37);
    assert(encode_seq(inp@, true)[9] == 0x33);
    assert(output_2@ == seq![0x36, 0x42, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39, 0x37, 0x33]);
}

/// output length 100 != 5*2 -> InvalidStringLength (lib.rs:471-480)
exec fn ut1_encode_to_slice_len_err()
{
    let inp: [u8; 5] = [0x6b, 0x69, 0x77, 0x69, 0x73];
    let mut output_3: [u8; 100] = [0; 100];
    let r1 = encode_to_slice(&inp, &mut output_3);
    assert(r1 == Result::Err(FromHexError::InvalidStringLength));
    let r2 = encode_to_slice_upper(&inp, &mut output_3);
    assert(r2 == Result::Err(FromHexError::InvalidStringLength));
}

// ---------- U2: test_decode_to_slice (lib.rs:483-499) ----------

/// "6b697769" -> kiwi (source of is_ok: all pairs valid =>
/// first_invalid == -1)
exec fn ut2_decode_to_slice()
{
    let inp: [u8; 8] = [0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39]; // b"6b697769"
    let mut output_1: [u8; 4] = [0; 4];
    let r1 = decode_to_slice(&inp, &mut output_1);
    assert(inp@ == seq![0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39]);
    assert forall|j: int| 0 <= j < 4 implies valid_pair(inp@, j) by {}
    proof {
        lip_none(inp@);
        assert(first_invalid_pair(inp@) == -1);
    }
    assert(r1.is_ok());
    assert(inp@.len() / 2 == 4);
    assert(decoded_seq(inp@).len() == 4);
    assert(decoded_seq(inp@)[0] == 0x6b);
    assert(decoded_seq(inp@)[1] == 0x69);
    assert(decoded_seq(inp@)[2] == 0x77);
    assert(decoded_seq(inp@)[3] == 0x69);
    assert(output_1@ == seq![0x6b, 0x69, 0x77, 0x69]); // "kiwi"
}

/// "6b69776973" -> kiwis
exec fn ut2_decode_to_slice_kiwis()
{
    let inp: [u8; 10] = [0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39, 0x37, 0x33]; // b"6b69776973"
    let mut output_2: [u8; 5] = [0; 5];
    let r2 = decode_to_slice(&inp, &mut output_2);
    assert(inp@ == seq![0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39, 0x37, 0x33]);
    assert forall|j: int| 0 <= j < 5 implies valid_pair(inp@, j) by {}
    proof {
        lip_none(inp@);
        assert(first_invalid_pair(inp@) == -1);
    }
    assert(r2.is_ok());
    assert(inp@.len() / 2 == 5);
    assert(decoded_seq(inp@).len() == 5);
    assert(decoded_seq(inp@)[0] == 0x6b);
    assert(decoded_seq(inp@)[1] == 0x69);
    assert(decoded_seq(inp@)[2] == 0x77);
    assert(decoded_seq(inp@)[3] == 0x69);
    assert(decoded_seq(inp@)[4] == 0x73);
    assert(output_2@ == seq![0x6b, 0x69, 0x77, 0x69, 0x73]); // "kiwis"
}

/// odd length "6" -> OddLength (lib.rs:493-499)
exec fn ut2_decode_to_slice_odd()
{
    let inp: [u8; 1] = [0x36];
    let mut output_3: [u8; 4] = [0; 4];
    let r3 = decode_to_slice(&inp, &mut output_3);
    assert(inp@.len() % 2 != 0);
    assert(r3 == Result::Err(FromHexError::OddLength));
}

// ---------- U11: test_from_hex_array (lib.rs:564-575) ----------

/// 12 characters -> [u8;6] Ok == foobar; the same input -> [u8;5]
/// Err(InvalidStringLength)
exec fn ut11_from_hex_array()
{
    let inp: [u8; 12] = [0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]; // b"666f6f626172"
    let ghost s = inp@;
    let r_ok = from_hex_array::<6usize>(&inp);
    assert(s == seq![0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]);
    assert forall|j: int| 0 <= j < 6 implies valid_pair(s, j) by {}
    proof {
        lip_none(s);
        assert(first_invalid_pair(s) == -1);
    }
    assert(s.len() / 2 == 6);
    assert(r_ok.is_ok());
    assert(decoded_seq(s).len() == 6);
    assert(decoded_seq(s)[0] == 0x66);
    assert(decoded_seq(s)[1] == 0x6f);
    assert(decoded_seq(s)[2] == 0x6f);
    assert(decoded_seq(s)[3] == 0x62);
    assert(decoded_seq(s)[4] == 0x61);
    assert(decoded_seq(s)[5] == 0x72);
    assert((r_ok.get_Ok_0())@ == seq![0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72]);

    let r_len = from_hex_array::<5usize>(&inp);
    assert(s.len() / 2 != 5usize as int);
    assert(r_len == Result::Err(FromHexError::InvalidStringLength));
}

} // verus!

fn main() {}
