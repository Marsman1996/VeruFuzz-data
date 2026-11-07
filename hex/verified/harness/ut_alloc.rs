//! harness: verification of the alloc-class UTs of code/src/lib.rs mod test
//! (U3-U10)
//! Per the inventory: U3 test_encode, U4 test_decode, U5/U6 from_hex okay
//! (str/bytes shapes), U7 invalid_length, U8 invalid_char (exact variant +
//! fields),
//! U9 empty, U10 whitespace. Reference-style organization: `#[path]`
//! includes verified/src/lib.rs.
//! Note: the upstream generics Vec::from_hex / T: AsRef are monomorphized to
//! &[u8] (see src/lib.rs ledger item 1);
//! the str/bytes shapes of U5/U6 are isomorphic under the mirror and are
//! covered jointly.
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod hexlib;

use hexlib::*;
use hexlib::{lip_exact, lip_none};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------- U3: test_encode (lib.rs:501-505) ----------
exec fn ut3_encode()
{
    /* assert_eq!(encode("foobar"), "666f6f626172"); */
    let inp: [u8; 6] = [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72]; // b"foobar"
    let v = encode(&inp);
    assert(v@.len() == 12);
    assert(encode_seq(inp@, false).len() == 12);
    assert(encode_seq(inp@, false)[0] == 0x36);
    assert(encode_seq(inp@, false)[1] == 0x36);
    assert(encode_seq(inp@, false)[2] == 0x36);
    assert(encode_seq(inp@, false)[3] == 0x66);
    assert(encode_seq(inp@, false)[4] == 0x36);
    assert(encode_seq(inp@, false)[5] == 0x66);
    assert(encode_seq(inp@, false)[6] == 0x36);
    assert(encode_seq(inp@, false)[7] == 0x32);
    assert(encode_seq(inp@, false)[8] == 0x36);
    assert(encode_seq(inp@, false)[9] == 0x31);
    assert(encode_seq(inp@, false)[10] == 0x37);
    assert(encode_seq(inp@, false)[11] == 0x32);
    assert(v@ == seq![0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]);
}

// ---------- U4: test_decode (lib.rs:507-514) + U5/U6 from_hex okay
//            (mixed-case input) ----------
exec fn ut4_decode_and_from_hex_ok()
{
    /* assert_eq!(decode("666f6f626172"), Ok(b"foobar"));
       U5: Vec::from_hex("666f6f626172" / "666F6F626172") both yield b"foobar" */
    let inp: [u8; 12] = [0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32];
    let r = decode(&inp);
    assert(inp@ == seq![0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]);
    assert forall|j: int| 0 <= j < 6 implies valid_pair(inp@, j) by {}
    proof {
        lip_none(inp@);
        assert(first_invalid_pair(inp@) == -1);
    }
    assert(r.is_ok());
    assert(decoded_seq(inp@).len() == 6);
    assert(decoded_seq(inp@)[0] == 0x66);
    assert(decoded_seq(inp@)[1] == 0x6f);
    assert(decoded_seq(inp@)[2] == 0x6f);
    assert(decoded_seq(inp@)[3] == 0x62);
    assert(decoded_seq(inp@)[4] == 0x61);
    assert(decoded_seq(inp@)[5] == 0x72);
    assert((r.get_Ok_0())@ == seq![0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72]);

    // U5 uppercase shape: the FromHex documentation contract -- upper and
    // lower case may be mixed
    let inpu: [u8; 12] = [0x36, 0x36, 0x36, 0x46, 0x36, 0x46, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]; // b"666F6F626172"
    let ru = vec_from_hex(&inpu);
    assert forall|j: int| 0 <= j < 6 implies valid_pair(inpu@, j) by {}
    proof {
        lip_none(inpu@);
        assert(first_invalid_pair(inpu@) == -1);
    }
    assert((ru.get_Ok_0())@ == seq![0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72]);
}

// ---------- U7: test_invalid_length (lib.rs:530-538) ----------
exec fn ut7_invalid_length()
{
    /* Vec::from_hex("1") / "666f6f6261721" -> Err(OddLength) */
    let a: [u8; 1] = [0x31];
    let ra = vec_from_hex(&a);
    assert(a@.len() % 2 != 0);
    assert(ra == Result::Err(FromHexError::OddLength));

    let b: [u8; 13] = [0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32, 0x31];
    let rb = vec_from_hex(&b);
    assert(b@.len() % 2 != 0);
    assert(rb == Result::Err(FromHexError::OddLength));
}

// ---------- U8: test_invalid_char (lib.rs:540-547) ----------
exec fn ut8_invalid_char()
{
    /* Vec::from_hex("66ag") -> Err(InvalidHexCharacter { c: 'g', index: 3 }) */
    let inp: [u8; 4] = [0x36, 0x36, 0x61, 0x67]; // b"66ag"
    let r = vec_from_hex(&inp);
    assert(inp@ == seq![0x36, 0x36, 0x61, 0x67]);
    assert(valid_pair(inp@, 0));
    assert(!valid_pair(inp@, 1)); // pair 1 = ('a','g'): g is invalid
    proof {
        lip_exact(inp@, 1);
        assert(first_invalid_pair(inp@) == 1);
    }
    assert(r == Result::Err(
        FromHexError::InvalidHexCharacter { c: 'g', index: 3 },
    ));
}

// ---------- U9: test_empty (lib.rs:549-553) ----------
exec fn ut9_empty()
{
    /* Vec::from_hex("") -> Ok(vec![]) */
    let inp: [u8; 0] = [];
    let r = vec_from_hex(&inp);
    assert(inp@.len() == 0);
    assert(inp@.len() % 2 == 0);
    proof {
        lip_none(inp@);
        assert(first_invalid_pair(inp@) == -1);
    }
    assert(r.is_ok());
    assert((r.get_Ok_0())@.len() == 0);
}

// ---------- U10: test_from_hex_whitespace (lib.rs:555-562) ----------
exec fn ut10_from_hex_whitespace()
{
    /* Vec::from_hex("666f 6f62617") -> Err(InvalidHexCharacter { c: ' ', index: 4 }) */
    let inp: [u8; 12] = [0x36, 0x36, 0x36, 0x66, 0x20, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37];
    let r = vec_from_hex(&inp);
    assert(inp@ == seq![0x36, 0x36, 0x36, 0x66, 0x20, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37]);
    assert(valid_pair(inp@, 0));
    assert(valid_pair(inp@, 1)); // pair 1 = ('6','f') is valid
    assert(!valid_pair(inp@, 2)); // pair 2 = (' ', '6') is invalid
    proof {
        lip_exact(inp@, 2);
        assert(first_invalid_pair(inp@) == 2);
    }
    assert(r == Result::Err(
        FromHexError::InvalidHexCharacter { c: ' ', index: 4 },
    ));
}

} // verus!

fn main() {}
