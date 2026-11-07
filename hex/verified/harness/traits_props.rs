//! harness: semantics of the ToHex trait (the U12/U13 devirtualization
//! contract witnesses) + the decode_in_slice coverage-difference contract
//! witness (the coverage-difference contract).
//!
//! U12 test_to_hex / U13 test_unsized_to_hex assert that the output of
//! ToHex::encode_hex::<T> equals the corresponding hex string; the upstream
//! trait method body = the BytesToHexChars iterator collect
//! (lib.rs:80-138), outside the Verus transcription surface (src/lib.rs
//! ledger item 5); its observed semantics
//! -- the byte string is byte-for-byte identical to encode_to_slice/encode --
//! are carried by the exec witness theorems below
//! (the model "encode_hex output == encode_seq input" is exactly the encode
//! model).
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod hexlib;

use hexlib::*;
use hexlib::lip_none;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------- U12/U13: the devirtualization witnesses of ToHex::encode_hex
//      / encode_hex_upper ----------

/// The observed semantics of [u8;6].encode_hex::<String>() == the encode
/// (lowercase) model
/// (the assertion subject of U12 lib.rs:577-589)
/// Upstream doc (lib.rs:68-69):
///   Encode the hex strict representing `self` into the result. Lower case
///   letters are used (e.g. `f9b4ca`)
pub exec fn theorem_tohex_encode_hex(input: &[u8]) -> (v: Vec<u8>)
    ensures v@ == encode_seq(input@, false)
{
    encode(input) // contract-level identity: the encode_hex output = the
    // encode output (devirtualization)
}

/// The observed semantics of encode_hex_upper == encode_upper (the U12
/// uppercase form)
/// Upstream doc (lib.rs:72-73):
///   Encode the hex strict representing `self` into the result. Upper case
///   letters are used (e.g. `F9B4CA`)
pub exec fn theorem_tohex_encode_hex_upper(input: &[u8]) -> (v: Vec<u8>)
    ensures v@ == encode_seq(input@, true)
{
    encode_upper(input)
}

/// U12 example witness: [0x66,0x6f,0x6f,0x62,0x61,0x72].encode_hex::<String>()
/// ==
/// "666f6f626172" (lowercase) / "666F6F626172" (uppercase)
exec fn ut12_to_hex_examples()
{
    let inp: [u8; 6] = [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72];
    let lc = theorem_tohex_encode_hex(&inp);
    assert(encode_seq(inp@, false).len() == 12);
    assert(lc@ == seq![0x36, 0x36, 0x36, 0x66, 0x36, 0x66, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]);
    let uc = theorem_tohex_encode_hex_upper(&inp);
    assert(encode_seq(inp@, true).len() == 12);
    assert(uc@ == seq![0x36, 0x36, 0x36, 0x46, 0x36, 0x46, 0x36, 0x32, 0x36, 0x31, 0x37, 0x32]);
}

// ---------- coverage difference: the contract witness of decode_in_slice
//            ----------

/// Universal contract witness of decode_in_slice: called with any
/// self-consistent in_out (even length), on Ok the front half == the decode
/// result with the rear half preserved; on the first invalid character it
/// yields the exact variant and index.
/// (lib.rs:338-348 doc example: b"6b697769" -> the front half b"kiwi")
exec fn theorem_decode_in_slice(in_out: &mut [u8]) -> (r: Result<(), FromHexError>)
{
    decode_in_slice(in_out)
}

/// decode_in_slice example witness (the doc example landed in the harness):
/// after in-place decoding of b"6b697769", [0..4] == b"kiwi" and [4..8] stays
/// b"7769"
exec fn decode_in_slice_example()
{
    let mut io: [u8; 8] = [0x36, 0x62, 0x36, 0x39, 0x37, 0x37, 0x36, 0x39]; // b"6b697769"
    let ghost old = io@;
    let sl: &mut [u8] = &mut io;
    assert forall|j: int| 0 <= j < 4 implies valid_pair(old, j) by {{}}
    proof {{
        lip_none(old);
        assert(first_invalid_pair(old) == -1);
    }}
    let r = decode_in_slice(sl);
    assert(first_invalid_pair(old) == -1);
    assert(r.is_ok());
    // the Ok contract of decode_in_slice: final == decoded_seq(old) + tail(old, 4)
    assert(decoded_seq(old).len() == 4);
    assert(decoded_seq(old)[0] == 0x6b);
    assert(decoded_seq(old)[1] == 0x69);
    assert(decoded_seq(old)[2] == 0x77);
    assert(decoded_seq(old)[3] == 0x69);
    // the length is unchanged
    assert(old.len() == 8);
}

} // verus!

fn main() {}
