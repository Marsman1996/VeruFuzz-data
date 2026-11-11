// Assertion-theorem harness for the verified punycode vector corpus.
//
// Upstream pin: 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (servo/rust-url,
// SUBDIR=idna). Consumption: includes verified/src/punycode.rs via #[path]
// as a module; no spec or proof content is copied here.
//
// The theorems below witness the full upstream test corpus of
// tests/punycode_tests.json (25 vectors, including the empty string) as a
// triple round trip per vector:
//   1. the exec decode_bytes over the encoded bytes returns the decoded
//      chars (tied through decode_model completeness),
//   2. the exec encode_chars over the decoded chars returns the encoded
//      chars (tied through encode_model),
//   3. both int-code models evaluate the pair by computation
//      (assert_by_compute on the model itself).
//
// The vectors are the punycode.js test corpus (MIT licensed, copied by
// upstream into punycode_tests.json); non-ASCII characters are spelled with
// ASCII escapes.
//
// Blocked (recorded in the ledger): the issue-870 vector of
// tests/bad_punycode_tests.json (encode must return None on a roughly
// 1880-code-point input whose deltas overflow the u32 delta channel). Its
// None verdict is a theorem of the model (the overflow guards of
// enc_outer_model return None), but the evaluator cannot digest a literal
// sequence of that size, and a general overflow lemma would need a
// cumulative-delta bound argument reserved for a follow-up batch.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/punycode.rs"]
mod punycode_v;

use punycode_v::codes_of;
use punycode_v::decode_bytes;
use punycode_v::decode_model;
use punycode_v::encode_chars;
use punycode_v::encode_model;
use punycode_v::encode_model_codes;
use punycode_v::lemma_codes_of_index;
use punycode_v::lemma_codes_of_len;

verus! {


/* ----------- vector 0: These tests are copied from https://github.com/mathiasbynens/punycode.js/blob/main/tests/tests.js , used under the MIT license. ----------- */
/// The decoded ground string of vector 0 (code points: empty).
fn dv_0() -> (r: Vec<char>)
    ensures
        r@.len() == 0,
        r@ == seq![],
{
    let mut r: Vec<char> = Vec::new();
    r
}

/// The encoded ground bytes of vector 0.
fn ev_0() -> (r: Vec<u8>)
    ensures
        r@.len() == 0,
        r@ == seq![],
{
    let mut r: Vec<u8> = Vec::new();
    r
}

/// Vector 0 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_0() -> (r: bool)
    ensures
        r,
{
    let dv = dv_0();
    let sd: &[char] = dv.as_slice();
    let ev = ev_0();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![])) by {
            assert(se@ == seq![]);
            assert_by_compute(decode_model(seq![])
                == Option::Some(seq![]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![]) by {
            lemma_codes_of_len(sd@);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![]);
        }
        assert(encode_model(sd@) == Option::Some(seq![])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![])
                == Option::Some(seq![])) by {
                assert_by_compute(encode_model_codes(seq![])
                    == Option::Some(seq![]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq![]);
    true
}


/* ----------- vector 1: a single basic code point ----------- */
/// The decoded ground string of vector 1 (code points: 0042 0061 0063 0068).
fn dv_1() -> (r: Vec<char>)
    ensures
        r@.len() == 4,
        r@ == seq!['B', 'a', 'c', 'h'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('B');
    r.push('a');
    r.push('c');
    r.push('h');
    r
}

/// The encoded ground bytes of vector 1.
fn ev_1() -> (r: Vec<u8>)
    ensures
        r@.len() == 5,
        r@ == seq![b'B', b'a', b'c', b'h', b'-'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'B');
    r.push(b'a');
    r.push(b'c');
    r.push(b'h');
    r.push(b'-');
    r
}

/// Vector 1 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_1() -> (r: bool)
    ensures
        r,
{
    let dv = dv_1();
    let sd: &[char] = dv.as_slice();
    let ev = ev_1();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![66, 97, 99, 104])) by {
            assert(se@ == seq![b'B', b'a', b'c', b'h', b'-']);
            assert_by_compute(decode_model(seq![b'B', b'a', b'c', b'h', b'-'])
                == Option::Some(seq![66, 97, 99, 104]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![66, 97, 99, 104]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 66);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 97);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 99);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 104);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![66, 97, 99, 104]);
        }
        assert(encode_model(sd@) == Option::Some(seq![66, 97, 99, 104, 45])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![66, 97, 99, 104])
                == Option::Some(seq![66, 97, 99, 104, 45])) by {
                assert_by_compute(encode_model_codes(seq![66, 97, 99, 104])
                    == Option::Some(seq![66, 97, 99, 104, 45]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['B', 'a', 'c', 'h', '-']);
    true
}


/* ----------- vector 2: a single non-ASCII character ----------- */
/// The decoded ground string of vector 2 (code points: 00FC).
fn dv_2() -> (r: Vec<char>)
    ensures
        r@.len() == 1,
        r@ == seq!['\u{fc}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{fc}');
    r
}

/// The encoded ground bytes of vector 2.
fn ev_2() -> (r: Vec<u8>)
    ensures
        r@.len() == 3,
        r@ == seq![b't', b'd', b'a'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b't');
    r.push(b'd');
    r.push(b'a');
    r
}

/// Vector 2 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_2() -> (r: bool)
    ensures
        r,
{
    let dv = dv_2();
    let sd: &[char] = dv.as_slice();
    let ev = ev_2();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![252])) by {
            assert(se@ == seq![b't', b'd', b'a']);
            assert_by_compute(decode_model(seq![b't', b'd', b'a'])
                == Option::Some(seq![252]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![252]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 252);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![252]);
        }
        assert(encode_model(sd@) == Option::Some(seq![116, 100, 97])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![252])
                == Option::Some(seq![116, 100, 97])) by {
                assert_by_compute(encode_model_codes(seq![252])
                    == Option::Some(seq![116, 100, 97]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['t', 'd', 'a']);
    true
}


/* ----------- vector 3: multiple non-ASCII characters ----------- */
/// The decoded ground string of vector 3 (code points: 00FC 00EB 00E4 00F6 2665).
fn dv_3() -> (r: Vec<char>)
    ensures
        r@.len() == 5,
        r@ == seq!['\u{fc}', '\u{eb}', '\u{e4}', '\u{f6}', '\u{2665}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{fc}');
    r.push('\u{eb}');
    r.push('\u{e4}');
    r.push('\u{f6}');
    r.push('\u{2665}');
    r
}

/// The encoded ground bytes of vector 3.
fn ev_3() -> (r: Vec<u8>)
    ensures
        r@.len() == 12,
        r@ == seq![b'4', b'c', b'a', b'n', b'8', b'a', b'v', b'2', b'0', b'0', b'9', b'b'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'4');
    r.push(b'c');
    r.push(b'a');
    r.push(b'n');
    r.push(b'8');
    r.push(b'a');
    r.push(b'v');
    r.push(b'2');
    r.push(b'0');
    r.push(b'0');
    r.push(b'9');
    r.push(b'b');
    r
}

/// Vector 3 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_3() -> (r: bool)
    ensures
        r,
{
    let dv = dv_3();
    let sd: &[char] = dv.as_slice();
    let ev = ev_3();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![252, 235, 228, 246, 9829])) by {
            assert(se@ == seq![b'4', b'c', b'a', b'n', b'8', b'a', b'v', b'2', b'0', b'0', b'9', b'b']);
            assert_by_compute(decode_model(seq![b'4', b'c', b'a', b'n', b'8', b'a', b'v', b'2', b'0', b'0', b'9', b'b'])
                == Option::Some(seq![252, 235, 228, 246, 9829]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![252, 235, 228, 246, 9829]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 252);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 235);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 228);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 246);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 9829);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![252, 235, 228, 246, 9829]);
        }
        assert(encode_model(sd@) == Option::Some(seq![52, 99, 97, 110, 56, 97, 118, 50, 48, 48, 57, 98])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![252, 235, 228, 246, 9829])
                == Option::Some(seq![52, 99, 97, 110, 56, 97, 118, 50, 48, 48, 57, 98])) by {
                assert_by_compute(encode_model_codes(seq![252, 235, 228, 246, 9829])
                    == Option::Some(seq![52, 99, 97, 110, 56, 97, 118, 50, 48, 48, 57, 98]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['4', 'c', 'a', 'n', '8', 'a', 'v', '2', '0', '0', '9', 'b']);
    true
}


/* ----------- vector 4: mix of ASCII and non-ASCII characters ----------- */
/// The decoded ground string of vector 4 (code points: 0062 00FC 0063 0068 0065 0072).
fn dv_4() -> (r: Vec<char>)
    ensures
        r@.len() == 6,
        r@ == seq!['b', '\u{fc}', 'c', 'h', 'e', 'r'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('b');
    r.push('\u{fc}');
    r.push('c');
    r.push('h');
    r.push('e');
    r.push('r');
    r
}

/// The encoded ground bytes of vector 4.
fn ev_4() -> (r: Vec<u8>)
    ensures
        r@.len() == 9,
        r@ == seq![b'b', b'c', b'h', b'e', b'r', b'-', b'k', b'v', b'a'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'b');
    r.push(b'c');
    r.push(b'h');
    r.push(b'e');
    r.push(b'r');
    r.push(b'-');
    r.push(b'k');
    r.push(b'v');
    r.push(b'a');
    r
}

/// Vector 4 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_4() -> (r: bool)
    ensures
        r,
{
    let dv = dv_4();
    let sd: &[char] = dv.as_slice();
    let ev = ev_4();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![98, 252, 99, 104, 101, 114])) by {
            assert(se@ == seq![b'b', b'c', b'h', b'e', b'r', b'-', b'k', b'v', b'a']);
            assert_by_compute(decode_model(seq![b'b', b'c', b'h', b'e', b'r', b'-', b'k', b'v', b'a'])
                == Option::Some(seq![98, 252, 99, 104, 101, 114]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![98, 252, 99, 104, 101, 114]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 98);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 252);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 99);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 104);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 101);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 114);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![98, 252, 99, 104, 101, 114]);
        }
        assert(encode_model(sd@) == Option::Some(seq![98, 99, 104, 101, 114, 45, 107, 118, 97])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![98, 252, 99, 104, 101, 114])
                == Option::Some(seq![98, 99, 104, 101, 114, 45, 107, 118, 97])) by {
                assert_by_compute(encode_model_codes(seq![98, 252, 99, 104, 101, 114])
                    == Option::Some(seq![98, 99, 104, 101, 114, 45, 107, 118, 97]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['b', 'c', 'h', 'e', 'r', '-', 'k', 'v', 'a']);
    true
}


/* ----------- vector 5: long string with both ASCII and non-ASCII characters ----------- */
/// The decoded ground string of vector 5 (code points: 0057 0069 006C 006C 0073 0074 0020 0064 0075 0020 0064 0069 0065 0020 0042 006C 00FC 0074 0068 0065 0020 0064 0065 0073 0020 0066 0072 00FC 0068 0065 006E 002C 0020 0064 0069 0065 0020 0046 0072 00FC 0063 0068 0074 0065 0020 0064 0065 0073 0020 0073 0070 00E4 0074 0065 0072 0065 006E 0020 004A 0061 0068 0072 0065 0073).
fn dv_5() -> (r: Vec<char>)
    ensures
        r@.len() == 64,
        r@ == seq!['W', 'i', 'l', 'l', 's', 't', ' ', 'd', 'u', ' ', 'd', 'i', 'e', ' ', 'B', 'l', '\u{fc}', 't', 'h', 'e', ' ', 'd', 'e', 's', ' ', 'f', 'r', '\u{fc}', 'h', 'e', 'n', ',', ' ', 'd', 'i', 'e', ' ', 'F', 'r', '\u{fc}', 'c', 'h', 't', 'e', ' ', 'd', 'e', 's', ' ', 's', 'p', '\u{e4}', 't', 'e', 'r', 'e', 'n', ' ', 'J', 'a', 'h', 'r', 'e', 's'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('W');
    r.push('i');
    r.push('l');
    r.push('l');
    r.push('s');
    r.push('t');
    r.push(' ');
    r.push('d');
    r.push('u');
    r.push(' ');
    r.push('d');
    r.push('i');
    r.push('e');
    r.push(' ');
    r.push('B');
    r.push('l');
    r.push('\u{fc}');
    r.push('t');
    r.push('h');
    r.push('e');
    r.push(' ');
    r.push('d');
    r.push('e');
    r.push('s');
    r.push(' ');
    r.push('f');
    r.push('r');
    r.push('\u{fc}');
    r.push('h');
    r.push('e');
    r.push('n');
    r.push(',');
    r.push(' ');
    r.push('d');
    r.push('i');
    r.push('e');
    r.push(' ');
    r.push('F');
    r.push('r');
    r.push('\u{fc}');
    r.push('c');
    r.push('h');
    r.push('t');
    r.push('e');
    r.push(' ');
    r.push('d');
    r.push('e');
    r.push('s');
    r.push(' ');
    r.push('s');
    r.push('p');
    r.push('\u{e4}');
    r.push('t');
    r.push('e');
    r.push('r');
    r.push('e');
    r.push('n');
    r.push(' ');
    r.push('J');
    r.push('a');
    r.push('h');
    r.push('r');
    r.push('e');
    r.push('s');
    r
}

/// The encoded ground bytes of vector 5.
fn ev_5() -> (r: Vec<u8>)
    ensures
        r@.len() == 70,
        r@ == seq![b'W', b'i', b'l', b'l', b's', b't', b' ', b'd', b'u', b' ', b'd', b'i', b'e', b' ', b'B', b'l', b't', b'h', b'e', b' ', b'd', b'e', b's', b' ', b'f', b'r', b'h', b'e', b'n', b',', b' ', b'd', b'i', b'e', b' ', b'F', b'r', b'c', b'h', b't', b'e', b' ', b'd', b'e', b's', b' ', b's', b'p', b't', b'e', b'r', b'e', b'n', b' ', b'J', b'a', b'h', b'r', b'e', b's', b'-', b'x', b'9', b'e', b'9', b'6', b'l', b'k', b'a', b'l'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'W');
    r.push(b'i');
    r.push(b'l');
    r.push(b'l');
    r.push(b's');
    r.push(b't');
    r.push(b' ');
    r.push(b'd');
    r.push(b'u');
    r.push(b' ');
    r.push(b'd');
    r.push(b'i');
    r.push(b'e');
    r.push(b' ');
    r.push(b'B');
    r.push(b'l');
    r.push(b't');
    r.push(b'h');
    r.push(b'e');
    r.push(b' ');
    r.push(b'd');
    r.push(b'e');
    r.push(b's');
    r.push(b' ');
    r.push(b'f');
    r.push(b'r');
    r.push(b'h');
    r.push(b'e');
    r.push(b'n');
    r.push(b',');
    r.push(b' ');
    r.push(b'd');
    r.push(b'i');
    r.push(b'e');
    r.push(b' ');
    r.push(b'F');
    r.push(b'r');
    r.push(b'c');
    r.push(b'h');
    r.push(b't');
    r.push(b'e');
    r.push(b' ');
    r.push(b'd');
    r.push(b'e');
    r.push(b's');
    r.push(b' ');
    r.push(b's');
    r.push(b'p');
    r.push(b't');
    r.push(b'e');
    r.push(b'r');
    r.push(b'e');
    r.push(b'n');
    r.push(b' ');
    r.push(b'J');
    r.push(b'a');
    r.push(b'h');
    r.push(b'r');
    r.push(b'e');
    r.push(b's');
    r.push(b'-');
    r.push(b'x');
    r.push(b'9');
    r.push(b'e');
    r.push(b'9');
    r.push(b'6');
    r.push(b'l');
    r.push(b'k');
    r.push(b'a');
    r.push(b'l');
    r
}

/// Vector 5 round trips, decode leg: the exec decode_bytes over the
/// encoded bytes returns the decoded chars (tied through decode_model).
pub exec fn witness_vec_5_decode() -> (r: bool)
    ensures
        r,
{

    let dv = dv_5();
    let sd: &[char] = dv.as_slice();
    let ev = ev_5();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 252, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 252, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 252, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 228, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115])) by {
            assert(se@ == seq![b'W', b'i', b'l', b'l', b's', b't', b' ', b'd', b'u', b' ', b'd', b'i', b'e', b' ', b'B', b'l', b't', b'h', b'e', b' ', b'd', b'e', b's', b' ', b'f', b'r', b'h', b'e', b'n', b',', b' ', b'd', b'i', b'e', b' ', b'F', b'r', b'c', b'h', b't', b'e', b' ', b'd', b'e', b's', b' ', b's', b'p', b't', b'e', b'r', b'e', b'n', b' ', b'J', b'a', b'h', b'r', b'e', b's', b'-', b'x', b'9', b'e', b'9', b'6', b'l', b'k', b'a', b'l']);
            assert_by_compute(decode_model(seq![b'W', b'i', b'l', b'l', b's', b't', b' ', b'd', b'u', b' ', b'd', b'i', b'e', b' ', b'B', b'l', b't', b'h', b'e', b' ', b'd', b'e', b's', b' ', b'f', b'r', b'h', b'e', b'n', b',', b' ', b'd', b'i', b'e', b' ', b'F', b'r', b'c', b'h', b't', b'e', b' ', b'd', b'e', b's', b' ', b's', b'p', b't', b'e', b'r', b'e', b'n', b' ', b'J', b'a', b'h', b'r', b'e', b's', b'-', b'x', b'9', b'e', b'9', b'6', b'l', b'k', b'a', b'l'])
                == Option::Some(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 252, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 252, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 252, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 228, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    true
}

/// Vector 5 round trips, encode leg: the exec encode_chars over the decoded
/// chars returns the encoded chars (tied through encode_model).
pub exec fn witness_vec_5_encode() -> (r: bool)
    ensures
        r,
{
    let dv = dv_5();
    let sd: &[char] = dv.as_slice();
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 252, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 252, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 252, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 228, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 87);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 105);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 108);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 108);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 115);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 116);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 32);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 100);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 117);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 32);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 100);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 105);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 101);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 32);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 66);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 108);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 252);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 116);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 104);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 101);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 32);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 100);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 101);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 115);
            lemma_codes_of_index(sd@, 24);
            assert(codes_of(sd@)[24] == 32);
            lemma_codes_of_index(sd@, 25);
            assert(codes_of(sd@)[25] == 102);
            lemma_codes_of_index(sd@, 26);
            assert(codes_of(sd@)[26] == 114);
            lemma_codes_of_index(sd@, 27);
            assert(codes_of(sd@)[27] == 252);
            lemma_codes_of_index(sd@, 28);
            assert(codes_of(sd@)[28] == 104);
            lemma_codes_of_index(sd@, 29);
            assert(codes_of(sd@)[29] == 101);
            lemma_codes_of_index(sd@, 30);
            assert(codes_of(sd@)[30] == 110);
            lemma_codes_of_index(sd@, 31);
            assert(codes_of(sd@)[31] == 44);
            lemma_codes_of_index(sd@, 32);
            assert(codes_of(sd@)[32] == 32);
            lemma_codes_of_index(sd@, 33);
            assert(codes_of(sd@)[33] == 100);
            lemma_codes_of_index(sd@, 34);
            assert(codes_of(sd@)[34] == 105);
            lemma_codes_of_index(sd@, 35);
            assert(codes_of(sd@)[35] == 101);
            lemma_codes_of_index(sd@, 36);
            assert(codes_of(sd@)[36] == 32);
            lemma_codes_of_index(sd@, 37);
            assert(codes_of(sd@)[37] == 70);
            lemma_codes_of_index(sd@, 38);
            assert(codes_of(sd@)[38] == 114);
            lemma_codes_of_index(sd@, 39);
            assert(codes_of(sd@)[39] == 252);
            lemma_codes_of_index(sd@, 40);
            assert(codes_of(sd@)[40] == 99);
            lemma_codes_of_index(sd@, 41);
            assert(codes_of(sd@)[41] == 104);
            lemma_codes_of_index(sd@, 42);
            assert(codes_of(sd@)[42] == 116);
            lemma_codes_of_index(sd@, 43);
            assert(codes_of(sd@)[43] == 101);
            lemma_codes_of_index(sd@, 44);
            assert(codes_of(sd@)[44] == 32);
            lemma_codes_of_index(sd@, 45);
            assert(codes_of(sd@)[45] == 100);
            lemma_codes_of_index(sd@, 46);
            assert(codes_of(sd@)[46] == 101);
            lemma_codes_of_index(sd@, 47);
            assert(codes_of(sd@)[47] == 115);
            lemma_codes_of_index(sd@, 48);
            assert(codes_of(sd@)[48] == 32);
            lemma_codes_of_index(sd@, 49);
            assert(codes_of(sd@)[49] == 115);
            lemma_codes_of_index(sd@, 50);
            assert(codes_of(sd@)[50] == 112);
            lemma_codes_of_index(sd@, 51);
            assert(codes_of(sd@)[51] == 228);
            lemma_codes_of_index(sd@, 52);
            assert(codes_of(sd@)[52] == 116);
            lemma_codes_of_index(sd@, 53);
            assert(codes_of(sd@)[53] == 101);
            lemma_codes_of_index(sd@, 54);
            assert(codes_of(sd@)[54] == 114);
            lemma_codes_of_index(sd@, 55);
            assert(codes_of(sd@)[55] == 101);
            lemma_codes_of_index(sd@, 56);
            assert(codes_of(sd@)[56] == 110);
            lemma_codes_of_index(sd@, 57);
            assert(codes_of(sd@)[57] == 32);
            lemma_codes_of_index(sd@, 58);
            assert(codes_of(sd@)[58] == 74);
            lemma_codes_of_index(sd@, 59);
            assert(codes_of(sd@)[59] == 97);
            lemma_codes_of_index(sd@, 60);
            assert(codes_of(sd@)[60] == 104);
            lemma_codes_of_index(sd@, 61);
            assert(codes_of(sd@)[61] == 114);
            lemma_codes_of_index(sd@, 62);
            assert(codes_of(sd@)[62] == 101);
            lemma_codes_of_index(sd@, 63);
            assert(codes_of(sd@)[63] == 115);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 252, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 252, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 252, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 228, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115]);
        }
        assert(encode_model(sd@) == Option::Some(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115, 45, 120, 57, 101, 57, 54, 108, 107, 97, 108])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 252, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 252, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 252, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 228, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115])
                == Option::Some(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115, 45, 120, 57, 101, 57, 54, 108, 107, 97, 108])) by {
                assert_by_compute(encode_model_codes(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 252, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 252, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 252, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 228, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115])
                    == Option::Some(seq![87, 105, 108, 108, 115, 116, 32, 100, 117, 32, 100, 105, 101, 32, 66, 108, 116, 104, 101, 32, 100, 101, 115, 32, 102, 114, 104, 101, 110, 44, 32, 100, 105, 101, 32, 70, 114, 99, 104, 116, 101, 32, 100, 101, 115, 32, 115, 112, 116, 101, 114, 101, 110, 32, 74, 97, 104, 114, 101, 115, 45, 120, 57, 101, 57, 54, 108, 107, 97, 108]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['W', 'i', 'l', 'l', 's', 't', ' ', 'd', 'u', ' ', 'd', 'i', 'e', ' ', 'B', 'l', 't', 'h', 'e', ' ', 'd', 'e', 's', ' ', 'f', 'r', 'h', 'e', 'n', ',', ' ', 'd', 'i', 'e', ' ', 'F', 'r', 'c', 'h', 't', 'e', ' ', 'd', 'e', 's', ' ', 's', 'p', 't', 'e', 'r', 'e', 'n', ' ', 'J', 'a', 'h', 'r', 'e', 's', '-', 'x', '9', 'e', '9', '6', 'l', 'k', 'a', 'l']);
    true
}


/* ----------- vector 6: Arabic (Egyptian) ----------- */
/// The decoded ground string of vector 6 (code points: 0644 064A 0647 0645 0627 0628 062A 0643 0644 0645 0648 0634 0639 0631 0628 064A 061F).
fn dv_6() -> (r: Vec<char>)
    ensures
        r@.len() == 17,
        r@ == seq!['\u{644}', '\u{64a}', '\u{647}', '\u{645}', '\u{627}', '\u{628}', '\u{62a}', '\u{643}', '\u{644}', '\u{645}', '\u{648}', '\u{634}', '\u{639}', '\u{631}', '\u{628}', '\u{64a}', '\u{61f}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{644}');
    r.push('\u{64a}');
    r.push('\u{647}');
    r.push('\u{645}');
    r.push('\u{627}');
    r.push('\u{628}');
    r.push('\u{62a}');
    r.push('\u{643}');
    r.push('\u{644}');
    r.push('\u{645}');
    r.push('\u{648}');
    r.push('\u{634}');
    r.push('\u{639}');
    r.push('\u{631}');
    r.push('\u{628}');
    r.push('\u{64a}');
    r.push('\u{61f}');
    r
}

/// The encoded ground bytes of vector 6.
fn ev_6() -> (r: Vec<u8>)
    ensures
        r@.len() == 22,
        r@ == seq![b'e', b'g', b'b', b'p', b'd', b'a', b'j', b'6', b'b', b'u', b'4', b'b', b'x', b'f', b'g', b'e', b'h', b'f', b'v', b'w', b'x', b'n'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'e');
    r.push(b'g');
    r.push(b'b');
    r.push(b'p');
    r.push(b'd');
    r.push(b'a');
    r.push(b'j');
    r.push(b'6');
    r.push(b'b');
    r.push(b'u');
    r.push(b'4');
    r.push(b'b');
    r.push(b'x');
    r.push(b'f');
    r.push(b'g');
    r.push(b'e');
    r.push(b'h');
    r.push(b'f');
    r.push(b'v');
    r.push(b'w');
    r.push(b'x');
    r.push(b'n');
    r
}

/// Vector 6 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_6() -> (r: bool)
    ensures
        r,
{
    let dv = dv_6();
    let sd: &[char] = dv.as_slice();
    let ev = ev_6();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![1604, 1610, 1607, 1605, 1575, 1576, 1578, 1603, 1604, 1605, 1608, 1588, 1593, 1585, 1576, 1610, 1567])) by {
            assert(se@ == seq![b'e', b'g', b'b', b'p', b'd', b'a', b'j', b'6', b'b', b'u', b'4', b'b', b'x', b'f', b'g', b'e', b'h', b'f', b'v', b'w', b'x', b'n']);
            assert_by_compute(decode_model(seq![b'e', b'g', b'b', b'p', b'd', b'a', b'j', b'6', b'b', b'u', b'4', b'b', b'x', b'f', b'g', b'e', b'h', b'f', b'v', b'w', b'x', b'n'])
                == Option::Some(seq![1604, 1610, 1607, 1605, 1575, 1576, 1578, 1603, 1604, 1605, 1608, 1588, 1593, 1585, 1576, 1610, 1567]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![1604, 1610, 1607, 1605, 1575, 1576, 1578, 1603, 1604, 1605, 1608, 1588, 1593, 1585, 1576, 1610, 1567]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 1604);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 1610);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 1607);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 1605);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 1575);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 1576);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 1578);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 1603);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 1604);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 1605);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 1608);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 1588);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 1593);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 1585);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 1576);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 1610);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 1567);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![1604, 1610, 1607, 1605, 1575, 1576, 1578, 1603, 1604, 1605, 1608, 1588, 1593, 1585, 1576, 1610, 1567]);
        }
        assert(encode_model(sd@) == Option::Some(seq![101, 103, 98, 112, 100, 97, 106, 54, 98, 117, 52, 98, 120, 102, 103, 101, 104, 102, 118, 119, 120, 110])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![1604, 1610, 1607, 1605, 1575, 1576, 1578, 1603, 1604, 1605, 1608, 1588, 1593, 1585, 1576, 1610, 1567])
                == Option::Some(seq![101, 103, 98, 112, 100, 97, 106, 54, 98, 117, 52, 98, 120, 102, 103, 101, 104, 102, 118, 119, 120, 110])) by {
                assert_by_compute(encode_model_codes(seq![1604, 1610, 1607, 1605, 1575, 1576, 1578, 1603, 1604, 1605, 1608, 1588, 1593, 1585, 1576, 1610, 1567])
                    == Option::Some(seq![101, 103, 98, 112, 100, 97, 106, 54, 98, 117, 52, 98, 120, 102, 103, 101, 104, 102, 118, 119, 120, 110]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['e', 'g', 'b', 'p', 'd', 'a', 'j', '6', 'b', 'u', '4', 'b', 'x', 'f', 'g', 'e', 'h', 'f', 'v', 'w', 'x', 'n']);
    true
}


/* ----------- vector 7: Chinese (simplified) ----------- */
/// The decoded ground string of vector 7 (code points: 4ED6 4EEC 4E3A 4EC0 4E48 4E0D 8BF4 4E2D 6587).
fn dv_7() -> (r: Vec<char>)
    ensures
        r@.len() == 9,
        r@ == seq!['\u{4ed6}', '\u{4eec}', '\u{4e3a}', '\u{4ec0}', '\u{4e48}', '\u{4e0d}', '\u{8bf4}', '\u{4e2d}', '\u{6587}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{4ed6}');
    r.push('\u{4eec}');
    r.push('\u{4e3a}');
    r.push('\u{4ec0}');
    r.push('\u{4e48}');
    r.push('\u{4e0d}');
    r.push('\u{8bf4}');
    r.push('\u{4e2d}');
    r.push('\u{6587}');
    r
}

/// The encoded ground bytes of vector 7.
fn ev_7() -> (r: Vec<u8>)
    ensures
        r@.len() == 24,
        r@ == seq![b'i', b'h', b'q', b'w', b'c', b'r', b'b', b'4', b'c', b'v', b'8', b'a', b'8', b'd', b'q', b'g', b'0', b'5', b'6', b'p', b'q', b'j', b'y', b'e'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'i');
    r.push(b'h');
    r.push(b'q');
    r.push(b'w');
    r.push(b'c');
    r.push(b'r');
    r.push(b'b');
    r.push(b'4');
    r.push(b'c');
    r.push(b'v');
    r.push(b'8');
    r.push(b'a');
    r.push(b'8');
    r.push(b'd');
    r.push(b'q');
    r.push(b'g');
    r.push(b'0');
    r.push(b'5');
    r.push(b'6');
    r.push(b'p');
    r.push(b'q');
    r.push(b'j');
    r.push(b'y');
    r.push(b'e');
    r
}

/// Vector 7 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_7() -> (r: bool)
    ensures
        r,
{
    let dv = dv_7();
    let sd: &[char] = dv.as_slice();
    let ev = ev_7();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![20182, 20204, 20026, 20160, 20040, 19981, 35828, 20013, 25991])) by {
            assert(se@ == seq![b'i', b'h', b'q', b'w', b'c', b'r', b'b', b'4', b'c', b'v', b'8', b'a', b'8', b'd', b'q', b'g', b'0', b'5', b'6', b'p', b'q', b'j', b'y', b'e']);
            assert_by_compute(decode_model(seq![b'i', b'h', b'q', b'w', b'c', b'r', b'b', b'4', b'c', b'v', b'8', b'a', b'8', b'd', b'q', b'g', b'0', b'5', b'6', b'p', b'q', b'j', b'y', b'e'])
                == Option::Some(seq![20182, 20204, 20026, 20160, 20040, 19981, 35828, 20013, 25991]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![20182, 20204, 20026, 20160, 20040, 19981, 35828, 20013, 25991]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 20182);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 20204);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 20026);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 20160);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 20040);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 19981);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 35828);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 20013);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 25991);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![20182, 20204, 20026, 20160, 20040, 19981, 35828, 20013, 25991]);
        }
        assert(encode_model(sd@) == Option::Some(seq![105, 104, 113, 119, 99, 114, 98, 52, 99, 118, 56, 97, 56, 100, 113, 103, 48, 53, 54, 112, 113, 106, 121, 101])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![20182, 20204, 20026, 20160, 20040, 19981, 35828, 20013, 25991])
                == Option::Some(seq![105, 104, 113, 119, 99, 114, 98, 52, 99, 118, 56, 97, 56, 100, 113, 103, 48, 53, 54, 112, 113, 106, 121, 101])) by {
                assert_by_compute(encode_model_codes(seq![20182, 20204, 20026, 20160, 20040, 19981, 35828, 20013, 25991])
                    == Option::Some(seq![105, 104, 113, 119, 99, 114, 98, 52, 99, 118, 56, 97, 56, 100, 113, 103, 48, 53, 54, 112, 113, 106, 121, 101]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['i', 'h', 'q', 'w', 'c', 'r', 'b', '4', 'c', 'v', '8', 'a', '8', 'd', 'q', 'g', '0', '5', '6', 'p', 'q', 'j', 'y', 'e']);
    true
}


/* ----------- vector 8: Chinese (traditional) ----------- */
/// The decoded ground string of vector 8 (code points: 4ED6 5011 7232 4EC0 9EBD 4E0D 8AAA 4E2D 6587).
fn dv_8() -> (r: Vec<char>)
    ensures
        r@.len() == 9,
        r@ == seq!['\u{4ed6}', '\u{5011}', '\u{7232}', '\u{4ec0}', '\u{9ebd}', '\u{4e0d}', '\u{8aaa}', '\u{4e2d}', '\u{6587}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{4ed6}');
    r.push('\u{5011}');
    r.push('\u{7232}');
    r.push('\u{4ec0}');
    r.push('\u{9ebd}');
    r.push('\u{4e0d}');
    r.push('\u{8aaa}');
    r.push('\u{4e2d}');
    r.push('\u{6587}');
    r
}

/// The encoded ground bytes of vector 8.
fn ev_8() -> (r: Vec<u8>)
    ensures
        r@.len() == 27,
        r@ == seq![b'i', b'h', b'q', b'w', b'c', b't', b'v', b'z', b'c', b'9', b'1', b'f', b'6', b'5', b'9', b'd', b'r', b's', b's', b'3', b'x', b'8', b'b', b'o', b'0', b'y', b'b'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'i');
    r.push(b'h');
    r.push(b'q');
    r.push(b'w');
    r.push(b'c');
    r.push(b't');
    r.push(b'v');
    r.push(b'z');
    r.push(b'c');
    r.push(b'9');
    r.push(b'1');
    r.push(b'f');
    r.push(b'6');
    r.push(b'5');
    r.push(b'9');
    r.push(b'd');
    r.push(b'r');
    r.push(b's');
    r.push(b's');
    r.push(b'3');
    r.push(b'x');
    r.push(b'8');
    r.push(b'b');
    r.push(b'o');
    r.push(b'0');
    r.push(b'y');
    r.push(b'b');
    r
}

/// Vector 8 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_8() -> (r: bool)
    ensures
        r,
{
    let dv = dv_8();
    let sd: &[char] = dv.as_slice();
    let ev = ev_8();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![20182, 20497, 29234, 20160, 40637, 19981, 35498, 20013, 25991])) by {
            assert(se@ == seq![b'i', b'h', b'q', b'w', b'c', b't', b'v', b'z', b'c', b'9', b'1', b'f', b'6', b'5', b'9', b'd', b'r', b's', b's', b'3', b'x', b'8', b'b', b'o', b'0', b'y', b'b']);
            assert_by_compute(decode_model(seq![b'i', b'h', b'q', b'w', b'c', b't', b'v', b'z', b'c', b'9', b'1', b'f', b'6', b'5', b'9', b'd', b'r', b's', b's', b'3', b'x', b'8', b'b', b'o', b'0', b'y', b'b'])
                == Option::Some(seq![20182, 20497, 29234, 20160, 40637, 19981, 35498, 20013, 25991]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![20182, 20497, 29234, 20160, 40637, 19981, 35498, 20013, 25991]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 20182);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 20497);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 29234);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 20160);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 40637);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 19981);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 35498);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 20013);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 25991);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![20182, 20497, 29234, 20160, 40637, 19981, 35498, 20013, 25991]);
        }
        assert(encode_model(sd@) == Option::Some(seq![105, 104, 113, 119, 99, 116, 118, 122, 99, 57, 49, 102, 54, 53, 57, 100, 114, 115, 115, 51, 120, 56, 98, 111, 48, 121, 98])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![20182, 20497, 29234, 20160, 40637, 19981, 35498, 20013, 25991])
                == Option::Some(seq![105, 104, 113, 119, 99, 116, 118, 122, 99, 57, 49, 102, 54, 53, 57, 100, 114, 115, 115, 51, 120, 56, 98, 111, 48, 121, 98])) by {
                assert_by_compute(encode_model_codes(seq![20182, 20497, 29234, 20160, 40637, 19981, 35498, 20013, 25991])
                    == Option::Some(seq![105, 104, 113, 119, 99, 116, 118, 122, 99, 57, 49, 102, 54, 53, 57, 100, 114, 115, 115, 51, 120, 56, 98, 111, 48, 121, 98]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['i', 'h', 'q', 'w', 'c', 't', 'v', 'z', 'c', '9', '1', 'f', '6', '5', '9', 'd', 'r', 's', 's', '3', 'x', '8', 'b', 'o', '0', 'y', 'b']);
    true
}


/* ----------- vector 9: Czech ----------- */
/// The decoded ground string of vector 9 (code points: 0050 0072 006F 010D 0070 0072 006F 0073 0074 011B 006E 0065 006D 006C 0075 0076 00ED 010D 0065 0073 006B 0079).
fn dv_9() -> (r: Vec<char>)
    ensures
        r@.len() == 22,
        r@ == seq!['P', 'r', 'o', '\u{10d}', 'p', 'r', 'o', 's', 't', '\u{11b}', 'n', 'e', 'm', 'l', 'u', 'v', '\u{ed}', '\u{10d}', 'e', 's', 'k', 'y'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('P');
    r.push('r');
    r.push('o');
    r.push('\u{10d}');
    r.push('p');
    r.push('r');
    r.push('o');
    r.push('s');
    r.push('t');
    r.push('\u{11b}');
    r.push('n');
    r.push('e');
    r.push('m');
    r.push('l');
    r.push('u');
    r.push('v');
    r.push('\u{ed}');
    r.push('\u{10d}');
    r.push('e');
    r.push('s');
    r.push('k');
    r.push('y');
    r
}

/// The encoded ground bytes of vector 9.
fn ev_9() -> (r: Vec<u8>)
    ensures
        r@.len() == 30,
        r@ == seq![b'P', b'r', b'o', b'p', b'r', b'o', b's', b't', b'n', b'e', b'm', b'l', b'u', b'v', b'e', b's', b'k', b'y', b'-', b'u', b'y', b'b', b'2', b'4', b'd', b'm', b'a', b'4', b'1', b'a'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'P');
    r.push(b'r');
    r.push(b'o');
    r.push(b'p');
    r.push(b'r');
    r.push(b'o');
    r.push(b's');
    r.push(b't');
    r.push(b'n');
    r.push(b'e');
    r.push(b'm');
    r.push(b'l');
    r.push(b'u');
    r.push(b'v');
    r.push(b'e');
    r.push(b's');
    r.push(b'k');
    r.push(b'y');
    r.push(b'-');
    r.push(b'u');
    r.push(b'y');
    r.push(b'b');
    r.push(b'2');
    r.push(b'4');
    r.push(b'd');
    r.push(b'm');
    r.push(b'a');
    r.push(b'4');
    r.push(b'1');
    r.push(b'a');
    r
}

/// Vector 9 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_9() -> (r: bool)
    ensures
        r,
{
    let dv = dv_9();
    let sd: &[char] = dv.as_slice();
    let ev = ev_9();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![80, 114, 111, 269, 112, 114, 111, 115, 116, 283, 110, 101, 109, 108, 117, 118, 237, 269, 101, 115, 107, 121])) by {
            assert(se@ == seq![b'P', b'r', b'o', b'p', b'r', b'o', b's', b't', b'n', b'e', b'm', b'l', b'u', b'v', b'e', b's', b'k', b'y', b'-', b'u', b'y', b'b', b'2', b'4', b'd', b'm', b'a', b'4', b'1', b'a']);
            assert_by_compute(decode_model(seq![b'P', b'r', b'o', b'p', b'r', b'o', b's', b't', b'n', b'e', b'm', b'l', b'u', b'v', b'e', b's', b'k', b'y', b'-', b'u', b'y', b'b', b'2', b'4', b'd', b'm', b'a', b'4', b'1', b'a'])
                == Option::Some(seq![80, 114, 111, 269, 112, 114, 111, 115, 116, 283, 110, 101, 109, 108, 117, 118, 237, 269, 101, 115, 107, 121]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![80, 114, 111, 269, 112, 114, 111, 115, 116, 283, 110, 101, 109, 108, 117, 118, 237, 269, 101, 115, 107, 121]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 80);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 114);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 111);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 269);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 112);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 114);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 111);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 115);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 116);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 283);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 110);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 101);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 109);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 108);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 117);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 118);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 237);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 269);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 101);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 115);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 107);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 121);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![80, 114, 111, 269, 112, 114, 111, 115, 116, 283, 110, 101, 109, 108, 117, 118, 237, 269, 101, 115, 107, 121]);
        }
        assert(encode_model(sd@) == Option::Some(seq![80, 114, 111, 112, 114, 111, 115, 116, 110, 101, 109, 108, 117, 118, 101, 115, 107, 121, 45, 117, 121, 98, 50, 52, 100, 109, 97, 52, 49, 97])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![80, 114, 111, 269, 112, 114, 111, 115, 116, 283, 110, 101, 109, 108, 117, 118, 237, 269, 101, 115, 107, 121])
                == Option::Some(seq![80, 114, 111, 112, 114, 111, 115, 116, 110, 101, 109, 108, 117, 118, 101, 115, 107, 121, 45, 117, 121, 98, 50, 52, 100, 109, 97, 52, 49, 97])) by {
                assert_by_compute(encode_model_codes(seq![80, 114, 111, 269, 112, 114, 111, 115, 116, 283, 110, 101, 109, 108, 117, 118, 237, 269, 101, 115, 107, 121])
                    == Option::Some(seq![80, 114, 111, 112, 114, 111, 115, 116, 110, 101, 109, 108, 117, 118, 101, 115, 107, 121, 45, 117, 121, 98, 50, 52, 100, 109, 97, 52, 49, 97]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['P', 'r', 'o', 'p', 'r', 'o', 's', 't', 'n', 'e', 'm', 'l', 'u', 'v', 'e', 's', 'k', 'y', '-', 'u', 'y', 'b', '2', '4', 'd', 'm', 'a', '4', '1', 'a']);
    true
}


/* ----------- vector 10: Hebrew ----------- */
/// The decoded ground string of vector 10 (code points: 05DC 05DE 05D4 05D4 05DD 05E4 05E9 05D5 05D8 05DC 05D0 05DE 05D3 05D1 05E8 05D9 05DD 05E2 05D1 05E8 05D9 05EA).
fn dv_10() -> (r: Vec<char>)
    ensures
        r@.len() == 22,
        r@ == seq!['\u{5dc}', '\u{5de}', '\u{5d4}', '\u{5d4}', '\u{5dd}', '\u{5e4}', '\u{5e9}', '\u{5d5}', '\u{5d8}', '\u{5dc}', '\u{5d0}', '\u{5de}', '\u{5d3}', '\u{5d1}', '\u{5e8}', '\u{5d9}', '\u{5dd}', '\u{5e2}', '\u{5d1}', '\u{5e8}', '\u{5d9}', '\u{5ea}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{5dc}');
    r.push('\u{5de}');
    r.push('\u{5d4}');
    r.push('\u{5d4}');
    r.push('\u{5dd}');
    r.push('\u{5e4}');
    r.push('\u{5e9}');
    r.push('\u{5d5}');
    r.push('\u{5d8}');
    r.push('\u{5dc}');
    r.push('\u{5d0}');
    r.push('\u{5de}');
    r.push('\u{5d3}');
    r.push('\u{5d1}');
    r.push('\u{5e8}');
    r.push('\u{5d9}');
    r.push('\u{5dd}');
    r.push('\u{5e2}');
    r.push('\u{5d1}');
    r.push('\u{5e8}');
    r.push('\u{5d9}');
    r.push('\u{5ea}');
    r
}

/// The encoded ground bytes of vector 10.
fn ev_10() -> (r: Vec<u8>)
    ensures
        r@.len() == 28,
        r@ == seq![b'4', b'd', b'b', b'c', b'a', b'g', b'd', b'a', b'h', b'y', b'm', b'b', b'x', b'e', b'k', b'h', b'e', b'h', b'6', b'e', b'0', b'a', b'7', b'f', b'e', b'i', b'0', b'b'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'4');
    r.push(b'd');
    r.push(b'b');
    r.push(b'c');
    r.push(b'a');
    r.push(b'g');
    r.push(b'd');
    r.push(b'a');
    r.push(b'h');
    r.push(b'y');
    r.push(b'm');
    r.push(b'b');
    r.push(b'x');
    r.push(b'e');
    r.push(b'k');
    r.push(b'h');
    r.push(b'e');
    r.push(b'h');
    r.push(b'6');
    r.push(b'e');
    r.push(b'0');
    r.push(b'a');
    r.push(b'7');
    r.push(b'f');
    r.push(b'e');
    r.push(b'i');
    r.push(b'0');
    r.push(b'b');
    r
}

/// Vector 10 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_10() -> (r: bool)
    ensures
        r,
{
    let dv = dv_10();
    let sd: &[char] = dv.as_slice();
    let ev = ev_10();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![1500, 1502, 1492, 1492, 1501, 1508, 1513, 1493, 1496, 1500, 1488, 1502, 1491, 1489, 1512, 1497, 1501, 1506, 1489, 1512, 1497, 1514])) by {
            assert(se@ == seq![b'4', b'd', b'b', b'c', b'a', b'g', b'd', b'a', b'h', b'y', b'm', b'b', b'x', b'e', b'k', b'h', b'e', b'h', b'6', b'e', b'0', b'a', b'7', b'f', b'e', b'i', b'0', b'b']);
            assert_by_compute(decode_model(seq![b'4', b'd', b'b', b'c', b'a', b'g', b'd', b'a', b'h', b'y', b'm', b'b', b'x', b'e', b'k', b'h', b'e', b'h', b'6', b'e', b'0', b'a', b'7', b'f', b'e', b'i', b'0', b'b'])
                == Option::Some(seq![1500, 1502, 1492, 1492, 1501, 1508, 1513, 1493, 1496, 1500, 1488, 1502, 1491, 1489, 1512, 1497, 1501, 1506, 1489, 1512, 1497, 1514]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![1500, 1502, 1492, 1492, 1501, 1508, 1513, 1493, 1496, 1500, 1488, 1502, 1491, 1489, 1512, 1497, 1501, 1506, 1489, 1512, 1497, 1514]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 1500);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 1502);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 1492);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 1492);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 1501);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 1508);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 1513);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 1493);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 1496);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 1500);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 1488);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 1502);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 1491);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 1489);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 1512);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 1497);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 1501);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 1506);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 1489);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 1512);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 1497);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 1514);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![1500, 1502, 1492, 1492, 1501, 1508, 1513, 1493, 1496, 1500, 1488, 1502, 1491, 1489, 1512, 1497, 1501, 1506, 1489, 1512, 1497, 1514]);
        }
        assert(encode_model(sd@) == Option::Some(seq![52, 100, 98, 99, 97, 103, 100, 97, 104, 121, 109, 98, 120, 101, 107, 104, 101, 104, 54, 101, 48, 97, 55, 102, 101, 105, 48, 98])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![1500, 1502, 1492, 1492, 1501, 1508, 1513, 1493, 1496, 1500, 1488, 1502, 1491, 1489, 1512, 1497, 1501, 1506, 1489, 1512, 1497, 1514])
                == Option::Some(seq![52, 100, 98, 99, 97, 103, 100, 97, 104, 121, 109, 98, 120, 101, 107, 104, 101, 104, 54, 101, 48, 97, 55, 102, 101, 105, 48, 98])) by {
                assert_by_compute(encode_model_codes(seq![1500, 1502, 1492, 1492, 1501, 1508, 1513, 1493, 1496, 1500, 1488, 1502, 1491, 1489, 1512, 1497, 1501, 1506, 1489, 1512, 1497, 1514])
                    == Option::Some(seq![52, 100, 98, 99, 97, 103, 100, 97, 104, 121, 109, 98, 120, 101, 107, 104, 101, 104, 54, 101, 48, 97, 55, 102, 101, 105, 48, 98]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['4', 'd', 'b', 'c', 'a', 'g', 'd', 'a', 'h', 'y', 'm', 'b', 'x', 'e', 'k', 'h', 'e', 'h', '6', 'e', '0', 'a', '7', 'f', 'e', 'i', '0', 'b']);
    true
}


/* ----------- vector 11: Hindi (Devanagari) ----------- */
/// The decoded ground string of vector 11 (code points: 092F 0939 0932 094B 0917 0939 093F 0928 094D 0926 0940 0915 094D 092F 094B 0902 0928 0939 0940 0902 092C 094B 0932 0938 0915 0924 0947 0939 0948 0902).
fn dv_11() -> (r: Vec<char>)
    ensures
        r@.len() == 30,
        r@ == seq!['\u{92f}', '\u{939}', '\u{932}', '\u{94b}', '\u{917}', '\u{939}', '\u{93f}', '\u{928}', '\u{94d}', '\u{926}', '\u{940}', '\u{915}', '\u{94d}', '\u{92f}', '\u{94b}', '\u{902}', '\u{928}', '\u{939}', '\u{940}', '\u{902}', '\u{92c}', '\u{94b}', '\u{932}', '\u{938}', '\u{915}', '\u{924}', '\u{947}', '\u{939}', '\u{948}', '\u{902}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{92f}');
    r.push('\u{939}');
    r.push('\u{932}');
    r.push('\u{94b}');
    r.push('\u{917}');
    r.push('\u{939}');
    r.push('\u{93f}');
    r.push('\u{928}');
    r.push('\u{94d}');
    r.push('\u{926}');
    r.push('\u{940}');
    r.push('\u{915}');
    r.push('\u{94d}');
    r.push('\u{92f}');
    r.push('\u{94b}');
    r.push('\u{902}');
    r.push('\u{928}');
    r.push('\u{939}');
    r.push('\u{940}');
    r.push('\u{902}');
    r.push('\u{92c}');
    r.push('\u{94b}');
    r.push('\u{932}');
    r.push('\u{938}');
    r.push('\u{915}');
    r.push('\u{924}');
    r.push('\u{947}');
    r.push('\u{939}');
    r.push('\u{948}');
    r.push('\u{902}');
    r
}

/// The encoded ground bytes of vector 11.
fn ev_11() -> (r: Vec<u8>)
    ensures
        r@.len() == 44,
        r@ == seq![b'i', b'1', b'b', b'a', b'a', b'7', b'e', b'c', b'i', b'9', b'g', b'l', b'r', b'd', b'9', b'b', b'2', b'a', b'e', b'1', b'b', b'j', b'0', b'h', b'f', b'c', b'g', b'g', b'6', b'i', b'y', b'a', b'f', b'8', b'o', b'0', b'a', b'1', b'd', b'i', b'g', b'0', b'c', b'd'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'i');
    r.push(b'1');
    r.push(b'b');
    r.push(b'a');
    r.push(b'a');
    r.push(b'7');
    r.push(b'e');
    r.push(b'c');
    r.push(b'i');
    r.push(b'9');
    r.push(b'g');
    r.push(b'l');
    r.push(b'r');
    r.push(b'd');
    r.push(b'9');
    r.push(b'b');
    r.push(b'2');
    r.push(b'a');
    r.push(b'e');
    r.push(b'1');
    r.push(b'b');
    r.push(b'j');
    r.push(b'0');
    r.push(b'h');
    r.push(b'f');
    r.push(b'c');
    r.push(b'g');
    r.push(b'g');
    r.push(b'6');
    r.push(b'i');
    r.push(b'y');
    r.push(b'a');
    r.push(b'f');
    r.push(b'8');
    r.push(b'o');
    r.push(b'0');
    r.push(b'a');
    r.push(b'1');
    r.push(b'd');
    r.push(b'i');
    r.push(b'g');
    r.push(b'0');
    r.push(b'c');
    r.push(b'd');
    r
}

/// Vector 11 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_11() -> (r: bool)
    ensures
        r,
{
    let dv = dv_11();
    let sd: &[char] = dv.as_slice();
    let ev = ev_11();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![2351, 2361, 2354, 2379, 2327, 2361, 2367, 2344, 2381, 2342, 2368, 2325, 2381, 2351, 2379, 2306, 2344, 2361, 2368, 2306, 2348, 2379, 2354, 2360, 2325, 2340, 2375, 2361, 2376, 2306])) by {
            assert(se@ == seq![b'i', b'1', b'b', b'a', b'a', b'7', b'e', b'c', b'i', b'9', b'g', b'l', b'r', b'd', b'9', b'b', b'2', b'a', b'e', b'1', b'b', b'j', b'0', b'h', b'f', b'c', b'g', b'g', b'6', b'i', b'y', b'a', b'f', b'8', b'o', b'0', b'a', b'1', b'd', b'i', b'g', b'0', b'c', b'd']);
            assert_by_compute(decode_model(seq![b'i', b'1', b'b', b'a', b'a', b'7', b'e', b'c', b'i', b'9', b'g', b'l', b'r', b'd', b'9', b'b', b'2', b'a', b'e', b'1', b'b', b'j', b'0', b'h', b'f', b'c', b'g', b'g', b'6', b'i', b'y', b'a', b'f', b'8', b'o', b'0', b'a', b'1', b'd', b'i', b'g', b'0', b'c', b'd'])
                == Option::Some(seq![2351, 2361, 2354, 2379, 2327, 2361, 2367, 2344, 2381, 2342, 2368, 2325, 2381, 2351, 2379, 2306, 2344, 2361, 2368, 2306, 2348, 2379, 2354, 2360, 2325, 2340, 2375, 2361, 2376, 2306]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![2351, 2361, 2354, 2379, 2327, 2361, 2367, 2344, 2381, 2342, 2368, 2325, 2381, 2351, 2379, 2306, 2344, 2361, 2368, 2306, 2348, 2379, 2354, 2360, 2325, 2340, 2375, 2361, 2376, 2306]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 2351);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 2361);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 2354);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 2379);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 2327);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 2361);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 2367);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 2344);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 2381);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 2342);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 2368);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 2325);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 2381);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 2351);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 2379);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 2306);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 2344);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 2361);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 2368);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 2306);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 2348);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 2379);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 2354);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 2360);
            lemma_codes_of_index(sd@, 24);
            assert(codes_of(sd@)[24] == 2325);
            lemma_codes_of_index(sd@, 25);
            assert(codes_of(sd@)[25] == 2340);
            lemma_codes_of_index(sd@, 26);
            assert(codes_of(sd@)[26] == 2375);
            lemma_codes_of_index(sd@, 27);
            assert(codes_of(sd@)[27] == 2361);
            lemma_codes_of_index(sd@, 28);
            assert(codes_of(sd@)[28] == 2376);
            lemma_codes_of_index(sd@, 29);
            assert(codes_of(sd@)[29] == 2306);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![2351, 2361, 2354, 2379, 2327, 2361, 2367, 2344, 2381, 2342, 2368, 2325, 2381, 2351, 2379, 2306, 2344, 2361, 2368, 2306, 2348, 2379, 2354, 2360, 2325, 2340, 2375, 2361, 2376, 2306]);
        }
        assert(encode_model(sd@) == Option::Some(seq![105, 49, 98, 97, 97, 55, 101, 99, 105, 57, 103, 108, 114, 100, 57, 98, 50, 97, 101, 49, 98, 106, 48, 104, 102, 99, 103, 103, 54, 105, 121, 97, 102, 56, 111, 48, 97, 49, 100, 105, 103, 48, 99, 100])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![2351, 2361, 2354, 2379, 2327, 2361, 2367, 2344, 2381, 2342, 2368, 2325, 2381, 2351, 2379, 2306, 2344, 2361, 2368, 2306, 2348, 2379, 2354, 2360, 2325, 2340, 2375, 2361, 2376, 2306])
                == Option::Some(seq![105, 49, 98, 97, 97, 55, 101, 99, 105, 57, 103, 108, 114, 100, 57, 98, 50, 97, 101, 49, 98, 106, 48, 104, 102, 99, 103, 103, 54, 105, 121, 97, 102, 56, 111, 48, 97, 49, 100, 105, 103, 48, 99, 100])) by {
                assert_by_compute(encode_model_codes(seq![2351, 2361, 2354, 2379, 2327, 2361, 2367, 2344, 2381, 2342, 2368, 2325, 2381, 2351, 2379, 2306, 2344, 2361, 2368, 2306, 2348, 2379, 2354, 2360, 2325, 2340, 2375, 2361, 2376, 2306])
                    == Option::Some(seq![105, 49, 98, 97, 97, 55, 101, 99, 105, 57, 103, 108, 114, 100, 57, 98, 50, 97, 101, 49, 98, 106, 48, 104, 102, 99, 103, 103, 54, 105, 121, 97, 102, 56, 111, 48, 97, 49, 100, 105, 103, 48, 99, 100]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['i', '1', 'b', 'a', 'a', '7', 'e', 'c', 'i', '9', 'g', 'l', 'r', 'd', '9', 'b', '2', 'a', 'e', '1', 'b', 'j', '0', 'h', 'f', 'c', 'g', 'g', '6', 'i', 'y', 'a', 'f', '8', 'o', '0', 'a', '1', 'd', 'i', 'g', '0', 'c', 'd']);
    true
}


/* ----------- vector 12: Japanese (kanji and hiragana) ----------- */
/// The decoded ground string of vector 12 (code points: 306A 305C 307F 3093 306A 65E5 672C 8A9E 3092 8A71 3057 3066 304F 308C 306A 3044 306E 304B).
fn dv_12() -> (r: Vec<char>)
    ensures
        r@.len() == 18,
        r@ == seq!['\u{306a}', '\u{305c}', '\u{307f}', '\u{3093}', '\u{306a}', '\u{65e5}', '\u{672c}', '\u{8a9e}', '\u{3092}', '\u{8a71}', '\u{3057}', '\u{3066}', '\u{304f}', '\u{308c}', '\u{306a}', '\u{3044}', '\u{306e}', '\u{304b}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{306a}');
    r.push('\u{305c}');
    r.push('\u{307f}');
    r.push('\u{3093}');
    r.push('\u{306a}');
    r.push('\u{65e5}');
    r.push('\u{672c}');
    r.push('\u{8a9e}');
    r.push('\u{3092}');
    r.push('\u{8a71}');
    r.push('\u{3057}');
    r.push('\u{3066}');
    r.push('\u{304f}');
    r.push('\u{308c}');
    r.push('\u{306a}');
    r.push('\u{3044}');
    r.push('\u{306e}');
    r.push('\u{304b}');
    r
}

/// The encoded ground bytes of vector 12.
fn ev_12() -> (r: Vec<u8>)
    ensures
        r@.len() == 38,
        r@ == seq![b'n', b'8', b'j', b'o', b'k', b'5', b'a', b'y', b'5', b'd', b'z', b'a', b'b', b'd', b'5', b'b', b'y', b'm', b'9', b'f', b'0', b'c', b'm', b'5', b'6', b'8', b'5', b'r', b'r', b'j', b'e', b't', b'r', b'6', b'p', b'd', b'x', b'a'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'n');
    r.push(b'8');
    r.push(b'j');
    r.push(b'o');
    r.push(b'k');
    r.push(b'5');
    r.push(b'a');
    r.push(b'y');
    r.push(b'5');
    r.push(b'd');
    r.push(b'z');
    r.push(b'a');
    r.push(b'b');
    r.push(b'd');
    r.push(b'5');
    r.push(b'b');
    r.push(b'y');
    r.push(b'm');
    r.push(b'9');
    r.push(b'f');
    r.push(b'0');
    r.push(b'c');
    r.push(b'm');
    r.push(b'5');
    r.push(b'6');
    r.push(b'8');
    r.push(b'5');
    r.push(b'r');
    r.push(b'r');
    r.push(b'j');
    r.push(b'e');
    r.push(b't');
    r.push(b'r');
    r.push(b'6');
    r.push(b'p');
    r.push(b'd');
    r.push(b'x');
    r.push(b'a');
    r
}

/// Vector 12 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_12() -> (r: bool)
    ensures
        r,
{
    let dv = dv_12();
    let sd: &[char] = dv.as_slice();
    let ev = ev_12();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![12394, 12380, 12415, 12435, 12394, 26085, 26412, 35486, 12434, 35441, 12375, 12390, 12367, 12428, 12394, 12356, 12398, 12363])) by {
            assert(se@ == seq![b'n', b'8', b'j', b'o', b'k', b'5', b'a', b'y', b'5', b'd', b'z', b'a', b'b', b'd', b'5', b'b', b'y', b'm', b'9', b'f', b'0', b'c', b'm', b'5', b'6', b'8', b'5', b'r', b'r', b'j', b'e', b't', b'r', b'6', b'p', b'd', b'x', b'a']);
            assert_by_compute(decode_model(seq![b'n', b'8', b'j', b'o', b'k', b'5', b'a', b'y', b'5', b'd', b'z', b'a', b'b', b'd', b'5', b'b', b'y', b'm', b'9', b'f', b'0', b'c', b'm', b'5', b'6', b'8', b'5', b'r', b'r', b'j', b'e', b't', b'r', b'6', b'p', b'd', b'x', b'a'])
                == Option::Some(seq![12394, 12380, 12415, 12435, 12394, 26085, 26412, 35486, 12434, 35441, 12375, 12390, 12367, 12428, 12394, 12356, 12398, 12363]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![12394, 12380, 12415, 12435, 12394, 26085, 26412, 35486, 12434, 35441, 12375, 12390, 12367, 12428, 12394, 12356, 12398, 12363]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 12394);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 12380);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 12415);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 12435);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 12394);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 26085);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 26412);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 35486);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 12434);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 35441);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 12375);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 12390);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 12367);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 12428);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 12394);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 12356);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 12398);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 12363);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![12394, 12380, 12415, 12435, 12394, 26085, 26412, 35486, 12434, 35441, 12375, 12390, 12367, 12428, 12394, 12356, 12398, 12363]);
        }
        assert(encode_model(sd@) == Option::Some(seq![110, 56, 106, 111, 107, 53, 97, 121, 53, 100, 122, 97, 98, 100, 53, 98, 121, 109, 57, 102, 48, 99, 109, 53, 54, 56, 53, 114, 114, 106, 101, 116, 114, 54, 112, 100, 120, 97])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![12394, 12380, 12415, 12435, 12394, 26085, 26412, 35486, 12434, 35441, 12375, 12390, 12367, 12428, 12394, 12356, 12398, 12363])
                == Option::Some(seq![110, 56, 106, 111, 107, 53, 97, 121, 53, 100, 122, 97, 98, 100, 53, 98, 121, 109, 57, 102, 48, 99, 109, 53, 54, 56, 53, 114, 114, 106, 101, 116, 114, 54, 112, 100, 120, 97])) by {
                assert_by_compute(encode_model_codes(seq![12394, 12380, 12415, 12435, 12394, 26085, 26412, 35486, 12434, 35441, 12375, 12390, 12367, 12428, 12394, 12356, 12398, 12363])
                    == Option::Some(seq![110, 56, 106, 111, 107, 53, 97, 121, 53, 100, 122, 97, 98, 100, 53, 98, 121, 109, 57, 102, 48, 99, 109, 53, 54, 56, 53, 114, 114, 106, 101, 116, 114, 54, 112, 100, 120, 97]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['n', '8', 'j', 'o', 'k', '5', 'a', 'y', '5', 'd', 'z', 'a', 'b', 'd', '5', 'b', 'y', 'm', '9', 'f', '0', 'c', 'm', '5', '6', '8', '5', 'r', 'r', 'j', 'e', 't', 'r', '6', 'p', 'd', 'x', 'a']);
    true
}


/* ----------- vector 13: Korean (Hangul syllables) ----------- */
/// The decoded ground string of vector 13 (code points: C138 ACC4 C758 BAA8 B4E0 C0AC B78C B4E4 C774 D55C AD6D C5B4 B97C C774 D574 D55C B2E4 BA74 C5BC B9C8 B098 C88B C744 AE4C).
fn dv_13() -> (r: Vec<char>)
    ensures
        r@.len() == 24,
        r@ == seq!['\u{c138}', '\u{acc4}', '\u{c758}', '\u{baa8}', '\u{b4e0}', '\u{c0ac}', '\u{b78c}', '\u{b4e4}', '\u{c774}', '\u{d55c}', '\u{ad6d}', '\u{c5b4}', '\u{b97c}', '\u{c774}', '\u{d574}', '\u{d55c}', '\u{b2e4}', '\u{ba74}', '\u{c5bc}', '\u{b9c8}', '\u{b098}', '\u{c88b}', '\u{c744}', '\u{ae4c}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{c138}');
    r.push('\u{acc4}');
    r.push('\u{c758}');
    r.push('\u{baa8}');
    r.push('\u{b4e0}');
    r.push('\u{c0ac}');
    r.push('\u{b78c}');
    r.push('\u{b4e4}');
    r.push('\u{c774}');
    r.push('\u{d55c}');
    r.push('\u{ad6d}');
    r.push('\u{c5b4}');
    r.push('\u{b97c}');
    r.push('\u{c774}');
    r.push('\u{d574}');
    r.push('\u{d55c}');
    r.push('\u{b2e4}');
    r.push('\u{ba74}');
    r.push('\u{c5bc}');
    r.push('\u{b9c8}');
    r.push('\u{b098}');
    r.push('\u{c88b}');
    r.push('\u{c744}');
    r.push('\u{ae4c}');
    r
}

/// The encoded ground bytes of vector 13.
fn ev_13() -> (r: Vec<u8>)
    ensures
        r@.len() == 69,
        r@ == seq![b'9', b'8', b'9', b'a', b'o', b'm', b's', b'v', b'i', b'5', b'e', b'8', b'3', b'd', b'b', b'1', b'd', b'2', b'a', b'3', b'5', b'5', b'c', b'v', b'1', b'e', b'0', b'v', b'a', b'k', b'1', b'd', b'w', b'r', b'v', b'9', b'3', b'd', b'5', b'x', b'b', b'h', b'1', b'5', b'a', b'0', b'd', b't', b'3', b'0', b'a', b'5', b'j', b'p', b's', b'd', b'8', b'7', b'9', b'c', b'c', b'm', b'6', b'f', b'e', b'a', b'9', b'8', b'c'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'9');
    r.push(b'8');
    r.push(b'9');
    r.push(b'a');
    r.push(b'o');
    r.push(b'm');
    r.push(b's');
    r.push(b'v');
    r.push(b'i');
    r.push(b'5');
    r.push(b'e');
    r.push(b'8');
    r.push(b'3');
    r.push(b'd');
    r.push(b'b');
    r.push(b'1');
    r.push(b'd');
    r.push(b'2');
    r.push(b'a');
    r.push(b'3');
    r.push(b'5');
    r.push(b'5');
    r.push(b'c');
    r.push(b'v');
    r.push(b'1');
    r.push(b'e');
    r.push(b'0');
    r.push(b'v');
    r.push(b'a');
    r.push(b'k');
    r.push(b'1');
    r.push(b'd');
    r.push(b'w');
    r.push(b'r');
    r.push(b'v');
    r.push(b'9');
    r.push(b'3');
    r.push(b'd');
    r.push(b'5');
    r.push(b'x');
    r.push(b'b');
    r.push(b'h');
    r.push(b'1');
    r.push(b'5');
    r.push(b'a');
    r.push(b'0');
    r.push(b'd');
    r.push(b't');
    r.push(b'3');
    r.push(b'0');
    r.push(b'a');
    r.push(b'5');
    r.push(b'j');
    r.push(b'p');
    r.push(b's');
    r.push(b'd');
    r.push(b'8');
    r.push(b'7');
    r.push(b'9');
    r.push(b'c');
    r.push(b'c');
    r.push(b'm');
    r.push(b'6');
    r.push(b'f');
    r.push(b'e');
    r.push(b'a');
    r.push(b'9');
    r.push(b'8');
    r.push(b'c');
    r
}

/// Vector 13 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_13() -> (r: bool)
    ensures
        r,
{
    let dv = dv_13();
    let sd: &[char] = dv.as_slice();
    let ev = ev_13();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![49464, 44228, 51032, 47784, 46304, 49324, 46988, 46308, 51060, 54620, 44397, 50612, 47484, 51060, 54644, 54620, 45796, 47732, 50620, 47560, 45208, 51339, 51012, 44620])) by {
            assert(se@ == seq![b'9', b'8', b'9', b'a', b'o', b'm', b's', b'v', b'i', b'5', b'e', b'8', b'3', b'd', b'b', b'1', b'd', b'2', b'a', b'3', b'5', b'5', b'c', b'v', b'1', b'e', b'0', b'v', b'a', b'k', b'1', b'd', b'w', b'r', b'v', b'9', b'3', b'd', b'5', b'x', b'b', b'h', b'1', b'5', b'a', b'0', b'd', b't', b'3', b'0', b'a', b'5', b'j', b'p', b's', b'd', b'8', b'7', b'9', b'c', b'c', b'm', b'6', b'f', b'e', b'a', b'9', b'8', b'c']);
            assert_by_compute(decode_model(seq![b'9', b'8', b'9', b'a', b'o', b'm', b's', b'v', b'i', b'5', b'e', b'8', b'3', b'd', b'b', b'1', b'd', b'2', b'a', b'3', b'5', b'5', b'c', b'v', b'1', b'e', b'0', b'v', b'a', b'k', b'1', b'd', b'w', b'r', b'v', b'9', b'3', b'd', b'5', b'x', b'b', b'h', b'1', b'5', b'a', b'0', b'd', b't', b'3', b'0', b'a', b'5', b'j', b'p', b's', b'd', b'8', b'7', b'9', b'c', b'c', b'm', b'6', b'f', b'e', b'a', b'9', b'8', b'c'])
                == Option::Some(seq![49464, 44228, 51032, 47784, 46304, 49324, 46988, 46308, 51060, 54620, 44397, 50612, 47484, 51060, 54644, 54620, 45796, 47732, 50620, 47560, 45208, 51339, 51012, 44620]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![49464, 44228, 51032, 47784, 46304, 49324, 46988, 46308, 51060, 54620, 44397, 50612, 47484, 51060, 54644, 54620, 45796, 47732, 50620, 47560, 45208, 51339, 51012, 44620]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 49464);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 44228);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 51032);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 47784);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 46304);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 49324);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 46988);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 46308);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 51060);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 54620);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 44397);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 50612);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 47484);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 51060);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 54644);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 54620);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 45796);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 47732);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 50620);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 47560);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 45208);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 51339);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 51012);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 44620);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![49464, 44228, 51032, 47784, 46304, 49324, 46988, 46308, 51060, 54620, 44397, 50612, 47484, 51060, 54644, 54620, 45796, 47732, 50620, 47560, 45208, 51339, 51012, 44620]);
        }
        assert(encode_model(sd@) == Option::Some(seq![57, 56, 57, 97, 111, 109, 115, 118, 105, 53, 101, 56, 51, 100, 98, 49, 100, 50, 97, 51, 53, 53, 99, 118, 49, 101, 48, 118, 97, 107, 49, 100, 119, 114, 118, 57, 51, 100, 53, 120, 98, 104, 49, 53, 97, 48, 100, 116, 51, 48, 97, 53, 106, 112, 115, 100, 56, 55, 57, 99, 99, 109, 54, 102, 101, 97, 57, 56, 99])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![49464, 44228, 51032, 47784, 46304, 49324, 46988, 46308, 51060, 54620, 44397, 50612, 47484, 51060, 54644, 54620, 45796, 47732, 50620, 47560, 45208, 51339, 51012, 44620])
                == Option::Some(seq![57, 56, 57, 97, 111, 109, 115, 118, 105, 53, 101, 56, 51, 100, 98, 49, 100, 50, 97, 51, 53, 53, 99, 118, 49, 101, 48, 118, 97, 107, 49, 100, 119, 114, 118, 57, 51, 100, 53, 120, 98, 104, 49, 53, 97, 48, 100, 116, 51, 48, 97, 53, 106, 112, 115, 100, 56, 55, 57, 99, 99, 109, 54, 102, 101, 97, 57, 56, 99])) by {
                assert_by_compute(encode_model_codes(seq![49464, 44228, 51032, 47784, 46304, 49324, 46988, 46308, 51060, 54620, 44397, 50612, 47484, 51060, 54644, 54620, 45796, 47732, 50620, 47560, 45208, 51339, 51012, 44620])
                    == Option::Some(seq![57, 56, 57, 97, 111, 109, 115, 118, 105, 53, 101, 56, 51, 100, 98, 49, 100, 50, 97, 51, 53, 53, 99, 118, 49, 101, 48, 118, 97, 107, 49, 100, 119, 114, 118, 57, 51, 100, 53, 120, 98, 104, 49, 53, 97, 48, 100, 116, 51, 48, 97, 53, 106, 112, 115, 100, 56, 55, 57, 99, 99, 109, 54, 102, 101, 97, 57, 56, 99]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['9', '8', '9', 'a', 'o', 'm', 's', 'v', 'i', '5', 'e', '8', '3', 'd', 'b', '1', 'd', '2', 'a', '3', '5', '5', 'c', 'v', '1', 'e', '0', 'v', 'a', 'k', '1', 'd', 'w', 'r', 'v', '9', '3', 'd', '5', 'x', 'b', 'h', '1', '5', 'a', '0', 'd', 't', '3', '0', 'a', '5', 'j', 'p', 's', 'd', '8', '7', '9', 'c', 'c', 'm', '6', 'f', 'e', 'a', '9', '8', 'c']);
    true
}


/* ----------- vector 14: Russian (Cyrillic) ----------- */
/// The decoded ground string of vector 14 (code points: 043F 043E 0447 0435 043C 0443 0436 0435 043E 043D 0438 043D 0435 0433 043E 0432 043E 0440 044F 0442 043F 043E 0440 0443 0441 0441 043A 0438).
fn dv_14() -> (r: Vec<char>)
    ensures
        r@.len() == 28,
        r@ == seq!['\u{43f}', '\u{43e}', '\u{447}', '\u{435}', '\u{43c}', '\u{443}', '\u{436}', '\u{435}', '\u{43e}', '\u{43d}', '\u{438}', '\u{43d}', '\u{435}', '\u{433}', '\u{43e}', '\u{432}', '\u{43e}', '\u{440}', '\u{44f}', '\u{442}', '\u{43f}', '\u{43e}', '\u{440}', '\u{443}', '\u{441}', '\u{441}', '\u{43a}', '\u{438}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{43f}');
    r.push('\u{43e}');
    r.push('\u{447}');
    r.push('\u{435}');
    r.push('\u{43c}');
    r.push('\u{443}');
    r.push('\u{436}');
    r.push('\u{435}');
    r.push('\u{43e}');
    r.push('\u{43d}');
    r.push('\u{438}');
    r.push('\u{43d}');
    r.push('\u{435}');
    r.push('\u{433}');
    r.push('\u{43e}');
    r.push('\u{432}');
    r.push('\u{43e}');
    r.push('\u{440}');
    r.push('\u{44f}');
    r.push('\u{442}');
    r.push('\u{43f}');
    r.push('\u{43e}');
    r.push('\u{440}');
    r.push('\u{443}');
    r.push('\u{441}');
    r.push('\u{441}');
    r.push('\u{43a}');
    r.push('\u{438}');
    r
}

/// The encoded ground bytes of vector 14.
fn ev_14() -> (r: Vec<u8>)
    ensures
        r@.len() == 32,
        r@ == seq![b'b', b'1', b'a', b'b', b'f', b'a', b'a', b'e', b'p', b'd', b'r', b'n', b'n', b'b', b'g', b'e', b'f', b'b', b'a', b'd', b'o', b't', b'c', b'w', b'a', b't', b'm', b'q', b'2', b'g', b'4', b'l'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'b');
    r.push(b'1');
    r.push(b'a');
    r.push(b'b');
    r.push(b'f');
    r.push(b'a');
    r.push(b'a');
    r.push(b'e');
    r.push(b'p');
    r.push(b'd');
    r.push(b'r');
    r.push(b'n');
    r.push(b'n');
    r.push(b'b');
    r.push(b'g');
    r.push(b'e');
    r.push(b'f');
    r.push(b'b');
    r.push(b'a');
    r.push(b'd');
    r.push(b'o');
    r.push(b't');
    r.push(b'c');
    r.push(b'w');
    r.push(b'a');
    r.push(b't');
    r.push(b'm');
    r.push(b'q');
    r.push(b'2');
    r.push(b'g');
    r.push(b'4');
    r.push(b'l');
    r
}

/// Vector 14 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_14() -> (r: bool)
    ensures
        r,
{
    let dv = dv_14();
    let sd: &[char] = dv.as_slice();
    let ev = ev_14();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![1087, 1086, 1095, 1077, 1084, 1091, 1078, 1077, 1086, 1085, 1080, 1085, 1077, 1075, 1086, 1074, 1086, 1088, 1103, 1090, 1087, 1086, 1088, 1091, 1089, 1089, 1082, 1080])) by {
            assert(se@ == seq![b'b', b'1', b'a', b'b', b'f', b'a', b'a', b'e', b'p', b'd', b'r', b'n', b'n', b'b', b'g', b'e', b'f', b'b', b'a', b'd', b'o', b't', b'c', b'w', b'a', b't', b'm', b'q', b'2', b'g', b'4', b'l']);
            assert_by_compute(decode_model(seq![b'b', b'1', b'a', b'b', b'f', b'a', b'a', b'e', b'p', b'd', b'r', b'n', b'n', b'b', b'g', b'e', b'f', b'b', b'a', b'd', b'o', b't', b'c', b'w', b'a', b't', b'm', b'q', b'2', b'g', b'4', b'l'])
                == Option::Some(seq![1087, 1086, 1095, 1077, 1084, 1091, 1078, 1077, 1086, 1085, 1080, 1085, 1077, 1075, 1086, 1074, 1086, 1088, 1103, 1090, 1087, 1086, 1088, 1091, 1089, 1089, 1082, 1080]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![1087, 1086, 1095, 1077, 1084, 1091, 1078, 1077, 1086, 1085, 1080, 1085, 1077, 1075, 1086, 1074, 1086, 1088, 1103, 1090, 1087, 1086, 1088, 1091, 1089, 1089, 1082, 1080]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 1087);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 1086);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 1095);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 1077);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 1084);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 1091);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 1078);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 1077);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 1086);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 1085);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 1080);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 1085);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 1077);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 1075);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 1086);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 1074);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 1086);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 1088);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 1103);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 1090);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 1087);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 1086);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 1088);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 1091);
            lemma_codes_of_index(sd@, 24);
            assert(codes_of(sd@)[24] == 1089);
            lemma_codes_of_index(sd@, 25);
            assert(codes_of(sd@)[25] == 1089);
            lemma_codes_of_index(sd@, 26);
            assert(codes_of(sd@)[26] == 1082);
            lemma_codes_of_index(sd@, 27);
            assert(codes_of(sd@)[27] == 1080);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![1087, 1086, 1095, 1077, 1084, 1091, 1078, 1077, 1086, 1085, 1080, 1085, 1077, 1075, 1086, 1074, 1086, 1088, 1103, 1090, 1087, 1086, 1088, 1091, 1089, 1089, 1082, 1080]);
        }
        assert(encode_model(sd@) == Option::Some(seq![98, 49, 97, 98, 102, 97, 97, 101, 112, 100, 114, 110, 110, 98, 103, 101, 102, 98, 97, 100, 111, 116, 99, 119, 97, 116, 109, 113, 50, 103, 52, 108])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![1087, 1086, 1095, 1077, 1084, 1091, 1078, 1077, 1086, 1085, 1080, 1085, 1077, 1075, 1086, 1074, 1086, 1088, 1103, 1090, 1087, 1086, 1088, 1091, 1089, 1089, 1082, 1080])
                == Option::Some(seq![98, 49, 97, 98, 102, 97, 97, 101, 112, 100, 114, 110, 110, 98, 103, 101, 102, 98, 97, 100, 111, 116, 99, 119, 97, 116, 109, 113, 50, 103, 52, 108])) by {
                assert_by_compute(encode_model_codes(seq![1087, 1086, 1095, 1077, 1084, 1091, 1078, 1077, 1086, 1085, 1080, 1085, 1077, 1075, 1086, 1074, 1086, 1088, 1103, 1090, 1087, 1086, 1088, 1091, 1089, 1089, 1082, 1080])
                    == Option::Some(seq![98, 49, 97, 98, 102, 97, 97, 101, 112, 100, 114, 110, 110, 98, 103, 101, 102, 98, 97, 100, 111, 116, 99, 119, 97, 116, 109, 113, 50, 103, 52, 108]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['b', '1', 'a', 'b', 'f', 'a', 'a', 'e', 'p', 'd', 'r', 'n', 'n', 'b', 'g', 'e', 'f', 'b', 'a', 'd', 'o', 't', 'c', 'w', 'a', 't', 'm', 'q', '2', 'g', '4', 'l']);
    true
}


/* ----------- vector 15: Spanish ----------- */
/// The decoded ground string of vector 15 (code points: 0050 006F 0072 0071 0075 00E9 006E 006F 0070 0075 0065 0064 0065 006E 0073 0069 006D 0070 006C 0065 006D 0065 006E 0074 0065 0068 0061 0062 006C 0061 0072 0065 006E 0045 0073 0070 0061 00F1 006F 006C).
fn dv_15() -> (r: Vec<char>)
    ensures
        r@.len() == 40,
        r@ == seq!['P', 'o', 'r', 'q', 'u', '\u{e9}', 'n', 'o', 'p', 'u', 'e', 'd', 'e', 'n', 's', 'i', 'm', 'p', 'l', 'e', 'm', 'e', 'n', 't', 'e', 'h', 'a', 'b', 'l', 'a', 'r', 'e', 'n', 'E', 's', 'p', 'a', '\u{f1}', 'o', 'l'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('P');
    r.push('o');
    r.push('r');
    r.push('q');
    r.push('u');
    r.push('\u{e9}');
    r.push('n');
    r.push('o');
    r.push('p');
    r.push('u');
    r.push('e');
    r.push('d');
    r.push('e');
    r.push('n');
    r.push('s');
    r.push('i');
    r.push('m');
    r.push('p');
    r.push('l');
    r.push('e');
    r.push('m');
    r.push('e');
    r.push('n');
    r.push('t');
    r.push('e');
    r.push('h');
    r.push('a');
    r.push('b');
    r.push('l');
    r.push('a');
    r.push('r');
    r.push('e');
    r.push('n');
    r.push('E');
    r.push('s');
    r.push('p');
    r.push('a');
    r.push('\u{f1}');
    r.push('o');
    r.push('l');
    r
}

/// The encoded ground bytes of vector 15.
fn ev_15() -> (r: Vec<u8>)
    ensures
        r@.len() == 45,
        r@ == seq![b'P', b'o', b'r', b'q', b'u', b'n', b'o', b'p', b'u', b'e', b'd', b'e', b'n', b's', b'i', b'm', b'p', b'l', b'e', b'm', b'e', b'n', b't', b'e', b'h', b'a', b'b', b'l', b'a', b'r', b'e', b'n', b'E', b's', b'p', b'a', b'o', b'l', b'-', b'f', b'm', b'd', b'5', b'6', b'a'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'P');
    r.push(b'o');
    r.push(b'r');
    r.push(b'q');
    r.push(b'u');
    r.push(b'n');
    r.push(b'o');
    r.push(b'p');
    r.push(b'u');
    r.push(b'e');
    r.push(b'd');
    r.push(b'e');
    r.push(b'n');
    r.push(b's');
    r.push(b'i');
    r.push(b'm');
    r.push(b'p');
    r.push(b'l');
    r.push(b'e');
    r.push(b'm');
    r.push(b'e');
    r.push(b'n');
    r.push(b't');
    r.push(b'e');
    r.push(b'h');
    r.push(b'a');
    r.push(b'b');
    r.push(b'l');
    r.push(b'a');
    r.push(b'r');
    r.push(b'e');
    r.push(b'n');
    r.push(b'E');
    r.push(b's');
    r.push(b'p');
    r.push(b'a');
    r.push(b'o');
    r.push(b'l');
    r.push(b'-');
    r.push(b'f');
    r.push(b'm');
    r.push(b'd');
    r.push(b'5');
    r.push(b'6');
    r.push(b'a');
    r
}

/// Vector 15 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_15() -> (r: bool)
    ensures
        r,
{
    let dv = dv_15();
    let sd: &[char] = dv.as_slice();
    let ev = ev_15();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![80, 111, 114, 113, 117, 233, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 241, 111, 108])) by {
            assert(se@ == seq![b'P', b'o', b'r', b'q', b'u', b'n', b'o', b'p', b'u', b'e', b'd', b'e', b'n', b's', b'i', b'm', b'p', b'l', b'e', b'm', b'e', b'n', b't', b'e', b'h', b'a', b'b', b'l', b'a', b'r', b'e', b'n', b'E', b's', b'p', b'a', b'o', b'l', b'-', b'f', b'm', b'd', b'5', b'6', b'a']);
            assert_by_compute(decode_model(seq![b'P', b'o', b'r', b'q', b'u', b'n', b'o', b'p', b'u', b'e', b'd', b'e', b'n', b's', b'i', b'm', b'p', b'l', b'e', b'm', b'e', b'n', b't', b'e', b'h', b'a', b'b', b'l', b'a', b'r', b'e', b'n', b'E', b's', b'p', b'a', b'o', b'l', b'-', b'f', b'm', b'd', b'5', b'6', b'a'])
                == Option::Some(seq![80, 111, 114, 113, 117, 233, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 241, 111, 108]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![80, 111, 114, 113, 117, 233, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 241, 111, 108]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 80);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 111);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 114);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 113);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 117);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 233);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 110);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 111);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 112);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 117);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 101);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 100);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 101);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 110);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 115);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 105);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 109);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 112);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 108);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 101);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 109);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 101);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 110);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 116);
            lemma_codes_of_index(sd@, 24);
            assert(codes_of(sd@)[24] == 101);
            lemma_codes_of_index(sd@, 25);
            assert(codes_of(sd@)[25] == 104);
            lemma_codes_of_index(sd@, 26);
            assert(codes_of(sd@)[26] == 97);
            lemma_codes_of_index(sd@, 27);
            assert(codes_of(sd@)[27] == 98);
            lemma_codes_of_index(sd@, 28);
            assert(codes_of(sd@)[28] == 108);
            lemma_codes_of_index(sd@, 29);
            assert(codes_of(sd@)[29] == 97);
            lemma_codes_of_index(sd@, 30);
            assert(codes_of(sd@)[30] == 114);
            lemma_codes_of_index(sd@, 31);
            assert(codes_of(sd@)[31] == 101);
            lemma_codes_of_index(sd@, 32);
            assert(codes_of(sd@)[32] == 110);
            lemma_codes_of_index(sd@, 33);
            assert(codes_of(sd@)[33] == 69);
            lemma_codes_of_index(sd@, 34);
            assert(codes_of(sd@)[34] == 115);
            lemma_codes_of_index(sd@, 35);
            assert(codes_of(sd@)[35] == 112);
            lemma_codes_of_index(sd@, 36);
            assert(codes_of(sd@)[36] == 97);
            lemma_codes_of_index(sd@, 37);
            assert(codes_of(sd@)[37] == 241);
            lemma_codes_of_index(sd@, 38);
            assert(codes_of(sd@)[38] == 111);
            lemma_codes_of_index(sd@, 39);
            assert(codes_of(sd@)[39] == 108);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![80, 111, 114, 113, 117, 233, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 241, 111, 108]);
        }
        assert(encode_model(sd@) == Option::Some(seq![80, 111, 114, 113, 117, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 111, 108, 45, 102, 109, 100, 53, 54, 97])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![80, 111, 114, 113, 117, 233, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 241, 111, 108])
                == Option::Some(seq![80, 111, 114, 113, 117, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 111, 108, 45, 102, 109, 100, 53, 54, 97])) by {
                assert_by_compute(encode_model_codes(seq![80, 111, 114, 113, 117, 233, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 241, 111, 108])
                    == Option::Some(seq![80, 111, 114, 113, 117, 110, 111, 112, 117, 101, 100, 101, 110, 115, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 104, 97, 98, 108, 97, 114, 101, 110, 69, 115, 112, 97, 111, 108, 45, 102, 109, 100, 53, 54, 97]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['P', 'o', 'r', 'q', 'u', 'n', 'o', 'p', 'u', 'e', 'd', 'e', 'n', 's', 'i', 'm', 'p', 'l', 'e', 'm', 'e', 'n', 't', 'e', 'h', 'a', 'b', 'l', 'a', 'r', 'e', 'n', 'E', 's', 'p', 'a', 'o', 'l', '-', 'f', 'm', 'd', '5', '6', 'a']);
    true
}


/* ----------- vector 16: Vietnamese ----------- */
/// The decoded ground string of vector 16 (code points: 0054 1EA1 0069 0073 0061 006F 0068 1ECD 006B 0068 00F4 006E 0067 0074 0068 1EC3 0063 0068 1EC9 006E 00F3 0069 0074 0069 1EBF 006E 0067 0056 0069 1EC7 0074).
fn dv_16() -> (r: Vec<char>)
    ensures
        r@.len() == 31,
        r@ == seq!['T', '\u{1ea1}', 'i', 's', 'a', 'o', 'h', '\u{1ecd}', 'k', 'h', '\u{f4}', 'n', 'g', 't', 'h', '\u{1ec3}', 'c', 'h', '\u{1ec9}', 'n', '\u{f3}', 'i', 't', 'i', '\u{1ebf}', 'n', 'g', 'V', 'i', '\u{1ec7}', 't'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('T');
    r.push('\u{1ea1}');
    r.push('i');
    r.push('s');
    r.push('a');
    r.push('o');
    r.push('h');
    r.push('\u{1ecd}');
    r.push('k');
    r.push('h');
    r.push('\u{f4}');
    r.push('n');
    r.push('g');
    r.push('t');
    r.push('h');
    r.push('\u{1ec3}');
    r.push('c');
    r.push('h');
    r.push('\u{1ec9}');
    r.push('n');
    r.push('\u{f3}');
    r.push('i');
    r.push('t');
    r.push('i');
    r.push('\u{1ebf}');
    r.push('n');
    r.push('g');
    r.push('V');
    r.push('i');
    r.push('\u{1ec7}');
    r.push('t');
    r
}

/// The encoded ground bytes of vector 16.
fn ev_16() -> (r: Vec<u8>)
    ensures
        r@.len() == 44,
        r@ == seq![b'T', b'i', b's', b'a', b'o', b'h', b'k', b'h', b'n', b'g', b't', b'h', b'c', b'h', b'n', b'i', b't', b'i', b'n', b'g', b'V', b'i', b't', b'-', b'k', b'j', b'c', b'r', b'8', b'2', b'6', b'8', b'q', b'y', b'x', b'a', b'f', b'd', b'2', b'f', b'1', b'b', b'9', b'g'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'T');
    r.push(b'i');
    r.push(b's');
    r.push(b'a');
    r.push(b'o');
    r.push(b'h');
    r.push(b'k');
    r.push(b'h');
    r.push(b'n');
    r.push(b'g');
    r.push(b't');
    r.push(b'h');
    r.push(b'c');
    r.push(b'h');
    r.push(b'n');
    r.push(b'i');
    r.push(b't');
    r.push(b'i');
    r.push(b'n');
    r.push(b'g');
    r.push(b'V');
    r.push(b'i');
    r.push(b't');
    r.push(b'-');
    r.push(b'k');
    r.push(b'j');
    r.push(b'c');
    r.push(b'r');
    r.push(b'8');
    r.push(b'2');
    r.push(b'6');
    r.push(b'8');
    r.push(b'q');
    r.push(b'y');
    r.push(b'x');
    r.push(b'a');
    r.push(b'f');
    r.push(b'd');
    r.push(b'2');
    r.push(b'f');
    r.push(b'1');
    r.push(b'b');
    r.push(b'9');
    r.push(b'g');
    r
}

/// Vector 16 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_16() -> (r: bool)
    ensures
        r,
{
    let dv = dv_16();
    let sd: &[char] = dv.as_slice();
    let ev = ev_16();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![84, 7841, 105, 115, 97, 111, 104, 7885, 107, 104, 244, 110, 103, 116, 104, 7875, 99, 104, 7881, 110, 243, 105, 116, 105, 7871, 110, 103, 86, 105, 7879, 116])) by {
            assert(se@ == seq![b'T', b'i', b's', b'a', b'o', b'h', b'k', b'h', b'n', b'g', b't', b'h', b'c', b'h', b'n', b'i', b't', b'i', b'n', b'g', b'V', b'i', b't', b'-', b'k', b'j', b'c', b'r', b'8', b'2', b'6', b'8', b'q', b'y', b'x', b'a', b'f', b'd', b'2', b'f', b'1', b'b', b'9', b'g']);
            assert_by_compute(decode_model(seq![b'T', b'i', b's', b'a', b'o', b'h', b'k', b'h', b'n', b'g', b't', b'h', b'c', b'h', b'n', b'i', b't', b'i', b'n', b'g', b'V', b'i', b't', b'-', b'k', b'j', b'c', b'r', b'8', b'2', b'6', b'8', b'q', b'y', b'x', b'a', b'f', b'd', b'2', b'f', b'1', b'b', b'9', b'g'])
                == Option::Some(seq![84, 7841, 105, 115, 97, 111, 104, 7885, 107, 104, 244, 110, 103, 116, 104, 7875, 99, 104, 7881, 110, 243, 105, 116, 105, 7871, 110, 103, 86, 105, 7879, 116]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![84, 7841, 105, 115, 97, 111, 104, 7885, 107, 104, 244, 110, 103, 116, 104, 7875, 99, 104, 7881, 110, 243, 105, 116, 105, 7871, 110, 103, 86, 105, 7879, 116]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 84);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 7841);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 105);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 115);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 97);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 111);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 104);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 7885);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 107);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 104);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 244);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 110);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 103);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 116);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 104);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 7875);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 99);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 104);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 7881);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 110);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 243);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 105);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 116);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 105);
            lemma_codes_of_index(sd@, 24);
            assert(codes_of(sd@)[24] == 7871);
            lemma_codes_of_index(sd@, 25);
            assert(codes_of(sd@)[25] == 110);
            lemma_codes_of_index(sd@, 26);
            assert(codes_of(sd@)[26] == 103);
            lemma_codes_of_index(sd@, 27);
            assert(codes_of(sd@)[27] == 86);
            lemma_codes_of_index(sd@, 28);
            assert(codes_of(sd@)[28] == 105);
            lemma_codes_of_index(sd@, 29);
            assert(codes_of(sd@)[29] == 7879);
            lemma_codes_of_index(sd@, 30);
            assert(codes_of(sd@)[30] == 116);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![84, 7841, 105, 115, 97, 111, 104, 7885, 107, 104, 244, 110, 103, 116, 104, 7875, 99, 104, 7881, 110, 243, 105, 116, 105, 7871, 110, 103, 86, 105, 7879, 116]);
        }
        assert(encode_model(sd@) == Option::Some(seq![84, 105, 115, 97, 111, 104, 107, 104, 110, 103, 116, 104, 99, 104, 110, 105, 116, 105, 110, 103, 86, 105, 116, 45, 107, 106, 99, 114, 56, 50, 54, 56, 113, 121, 120, 97, 102, 100, 50, 102, 49, 98, 57, 103])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![84, 7841, 105, 115, 97, 111, 104, 7885, 107, 104, 244, 110, 103, 116, 104, 7875, 99, 104, 7881, 110, 243, 105, 116, 105, 7871, 110, 103, 86, 105, 7879, 116])
                == Option::Some(seq![84, 105, 115, 97, 111, 104, 107, 104, 110, 103, 116, 104, 99, 104, 110, 105, 116, 105, 110, 103, 86, 105, 116, 45, 107, 106, 99, 114, 56, 50, 54, 56, 113, 121, 120, 97, 102, 100, 50, 102, 49, 98, 57, 103])) by {
                assert_by_compute(encode_model_codes(seq![84, 7841, 105, 115, 97, 111, 104, 7885, 107, 104, 244, 110, 103, 116, 104, 7875, 99, 104, 7881, 110, 243, 105, 116, 105, 7871, 110, 103, 86, 105, 7879, 116])
                    == Option::Some(seq![84, 105, 115, 97, 111, 104, 107, 104, 110, 103, 116, 104, 99, 104, 110, 105, 116, 105, 110, 103, 86, 105, 116, 45, 107, 106, 99, 114, 56, 50, 54, 56, 113, 121, 120, 97, 102, 100, 50, 102, 49, 98, 57, 103]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['T', 'i', 's', 'a', 'o', 'h', 'k', 'h', 'n', 'g', 't', 'h', 'c', 'h', 'n', 'i', 't', 'i', 'n', 'g', 'V', 'i', 't', '-', 'k', 'j', 'c', 'r', '8', '2', '6', '8', 'q', 'y', 'x', 'a', 'f', 'd', '2', 'f', '1', 'b', '9', 'g']);
    true
}


/* ----------- vector 17: (unnamed) ----------- */
/// The decoded ground string of vector 17 (code points: 0033 5E74 0042 7D44 91D1 516B 5148 751F).
fn dv_17() -> (r: Vec<char>)
    ensures
        r@.len() == 8,
        r@ == seq!['3', '\u{5e74}', 'B', '\u{7d44}', '\u{91d1}', '\u{516b}', '\u{5148}', '\u{751f}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('3');
    r.push('\u{5e74}');
    r.push('B');
    r.push('\u{7d44}');
    r.push('\u{91d1}');
    r.push('\u{516b}');
    r.push('\u{5148}');
    r.push('\u{751f}');
    r
}

/// The encoded ground bytes of vector 17.
fn ev_17() -> (r: Vec<u8>)
    ensures
        r@.len() == 24,
        r@ == seq![b'3', b'B', b'-', b'w', b'w', b'4', b'c', b'5', b'e', b'1', b'8', b'0', b'e', b'5', b'7', b'5', b'a', b'6', b'5', b'l', b's', b'y', b'2', b'b'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'3');
    r.push(b'B');
    r.push(b'-');
    r.push(b'w');
    r.push(b'w');
    r.push(b'4');
    r.push(b'c');
    r.push(b'5');
    r.push(b'e');
    r.push(b'1');
    r.push(b'8');
    r.push(b'0');
    r.push(b'e');
    r.push(b'5');
    r.push(b'7');
    r.push(b'5');
    r.push(b'a');
    r.push(b'6');
    r.push(b'5');
    r.push(b'l');
    r.push(b's');
    r.push(b'y');
    r.push(b'2');
    r.push(b'b');
    r
}

/// Vector 17 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_17() -> (r: bool)
    ensures
        r,
{
    let dv = dv_17();
    let sd: &[char] = dv.as_slice();
    let ev = ev_17();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![51, 24180, 66, 32068, 37329, 20843, 20808, 29983])) by {
            assert(se@ == seq![b'3', b'B', b'-', b'w', b'w', b'4', b'c', b'5', b'e', b'1', b'8', b'0', b'e', b'5', b'7', b'5', b'a', b'6', b'5', b'l', b's', b'y', b'2', b'b']);
            assert_by_compute(decode_model(seq![b'3', b'B', b'-', b'w', b'w', b'4', b'c', b'5', b'e', b'1', b'8', b'0', b'e', b'5', b'7', b'5', b'a', b'6', b'5', b'l', b's', b'y', b'2', b'b'])
                == Option::Some(seq![51, 24180, 66, 32068, 37329, 20843, 20808, 29983]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![51, 24180, 66, 32068, 37329, 20843, 20808, 29983]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 51);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 24180);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 66);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 32068);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 37329);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 20843);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 20808);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 29983);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![51, 24180, 66, 32068, 37329, 20843, 20808, 29983]);
        }
        assert(encode_model(sd@) == Option::Some(seq![51, 66, 45, 119, 119, 52, 99, 53, 101, 49, 56, 48, 101, 53, 55, 53, 97, 54, 53, 108, 115, 121, 50, 98])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![51, 24180, 66, 32068, 37329, 20843, 20808, 29983])
                == Option::Some(seq![51, 66, 45, 119, 119, 52, 99, 53, 101, 49, 56, 48, 101, 53, 55, 53, 97, 54, 53, 108, 115, 121, 50, 98])) by {
                assert_by_compute(encode_model_codes(seq![51, 24180, 66, 32068, 37329, 20843, 20808, 29983])
                    == Option::Some(seq![51, 66, 45, 119, 119, 52, 99, 53, 101, 49, 56, 48, 101, 53, 55, 53, 97, 54, 53, 108, 115, 121, 50, 98]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['3', 'B', '-', 'w', 'w', '4', 'c', '5', 'e', '1', '8', '0', 'e', '5', '7', '5', 'a', '6', '5', 'l', 's', 'y', '2', 'b']);
    true
}


/* ----------- vector 18: (unnamed) ----------- */
/// The decoded ground string of vector 18 (code points: 5B89 5BA4 5948 7F8E 6075 002D 0077 0069 0074 0068 002D 0053 0055 0050 0045 0052 002D 004D 004F 004E 004B 0045 0059 0053).
fn dv_18() -> (r: Vec<char>)
    ensures
        r@.len() == 24,
        r@ == seq!['\u{5b89}', '\u{5ba4}', '\u{5948}', '\u{7f8e}', '\u{6075}', '-', 'w', 'i', 't', 'h', '-', 'S', 'U', 'P', 'E', 'R', '-', 'M', 'O', 'N', 'K', 'E', 'Y', 'S'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{5b89}');
    r.push('\u{5ba4}');
    r.push('\u{5948}');
    r.push('\u{7f8e}');
    r.push('\u{6075}');
    r.push('-');
    r.push('w');
    r.push('i');
    r.push('t');
    r.push('h');
    r.push('-');
    r.push('S');
    r.push('U');
    r.push('P');
    r.push('E');
    r.push('R');
    r.push('-');
    r.push('M');
    r.push('O');
    r.push('N');
    r.push('K');
    r.push('E');
    r.push('Y');
    r.push('S');
    r
}

/// The encoded ground bytes of vector 18.
fn ev_18() -> (r: Vec<u8>)
    ensures
        r@.len() == 40,
        r@ == seq![b'-', b'w', b'i', b't', b'h', b'-', b'S', b'U', b'P', b'E', b'R', b'-', b'M', b'O', b'N', b'K', b'E', b'Y', b'S', b'-', b'p', b'c', b'5', b'8', b'a', b'g', b'8', b'0', b'a', b'8', b'q', b'a', b'i', b'0', b'0', b'g', b'7', b'n', b'9', b'n'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'-');
    r.push(b'w');
    r.push(b'i');
    r.push(b't');
    r.push(b'h');
    r.push(b'-');
    r.push(b'S');
    r.push(b'U');
    r.push(b'P');
    r.push(b'E');
    r.push(b'R');
    r.push(b'-');
    r.push(b'M');
    r.push(b'O');
    r.push(b'N');
    r.push(b'K');
    r.push(b'E');
    r.push(b'Y');
    r.push(b'S');
    r.push(b'-');
    r.push(b'p');
    r.push(b'c');
    r.push(b'5');
    r.push(b'8');
    r.push(b'a');
    r.push(b'g');
    r.push(b'8');
    r.push(b'0');
    r.push(b'a');
    r.push(b'8');
    r.push(b'q');
    r.push(b'a');
    r.push(b'i');
    r.push(b'0');
    r.push(b'0');
    r.push(b'g');
    r.push(b'7');
    r.push(b'n');
    r.push(b'9');
    r.push(b'n');
    r
}

/// Vector 18 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_18() -> (r: bool)
    ensures
        r,
{
    let dv = dv_18();
    let sd: &[char] = dv.as_slice();
    let ev = ev_18();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![23433, 23460, 22856, 32654, 24693, 45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83])) by {
            assert(se@ == seq![b'-', b'w', b'i', b't', b'h', b'-', b'S', b'U', b'P', b'E', b'R', b'-', b'M', b'O', b'N', b'K', b'E', b'Y', b'S', b'-', b'p', b'c', b'5', b'8', b'a', b'g', b'8', b'0', b'a', b'8', b'q', b'a', b'i', b'0', b'0', b'g', b'7', b'n', b'9', b'n']);
            assert_by_compute(decode_model(seq![b'-', b'w', b'i', b't', b'h', b'-', b'S', b'U', b'P', b'E', b'R', b'-', b'M', b'O', b'N', b'K', b'E', b'Y', b'S', b'-', b'p', b'c', b'5', b'8', b'a', b'g', b'8', b'0', b'a', b'8', b'q', b'a', b'i', b'0', b'0', b'g', b'7', b'n', b'9', b'n'])
                == Option::Some(seq![23433, 23460, 22856, 32654, 24693, 45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![23433, 23460, 22856, 32654, 24693, 45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 23433);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 23460);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 22856);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 32654);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 24693);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 45);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 119);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 105);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 116);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 104);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 45);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 83);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 85);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 80);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 69);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 82);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 45);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 77);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 79);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 78);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 75);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 69);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 89);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 83);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![23433, 23460, 22856, 32654, 24693, 45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83]);
        }
        assert(encode_model(sd@) == Option::Some(seq![45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83, 45, 112, 99, 53, 56, 97, 103, 56, 48, 97, 56, 113, 97, 105, 48, 48, 103, 55, 110, 57, 110])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![23433, 23460, 22856, 32654, 24693, 45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83])
                == Option::Some(seq![45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83, 45, 112, 99, 53, 56, 97, 103, 56, 48, 97, 56, 113, 97, 105, 48, 48, 103, 55, 110, 57, 110])) by {
                assert_by_compute(encode_model_codes(seq![23433, 23460, 22856, 32654, 24693, 45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83])
                    == Option::Some(seq![45, 119, 105, 116, 104, 45, 83, 85, 80, 69, 82, 45, 77, 79, 78, 75, 69, 89, 83, 45, 112, 99, 53, 56, 97, 103, 56, 48, 97, 56, 113, 97, 105, 48, 48, 103, 55, 110, 57, 110]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['-', 'w', 'i', 't', 'h', '-', 'S', 'U', 'P', 'E', 'R', '-', 'M', 'O', 'N', 'K', 'E', 'Y', 'S', '-', 'p', 'c', '5', '8', 'a', 'g', '8', '0', 'a', '8', 'q', 'a', 'i', '0', '0', 'g', '7', 'n', '9', 'n']);
    true
}


/* ----------- vector 19: (unnamed) ----------- */
/// The decoded ground string of vector 19 (code points: 0048 0065 006C 006C 006F 002D 0041 006E 006F 0074 0068 0065 0072 002D 0057 0061 0079 002D 305D 308C 305E 308C 306E 5834 6240).
fn dv_19() -> (r: Vec<char>)
    ensures
        r@.len() == 25,
        r@ == seq!['H', 'e', 'l', 'l', 'o', '-', 'A', 'n', 'o', 't', 'h', 'e', 'r', '-', 'W', 'a', 'y', '-', '\u{305d}', '\u{308c}', '\u{305e}', '\u{308c}', '\u{306e}', '\u{5834}', '\u{6240}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('H');
    r.push('e');
    r.push('l');
    r.push('l');
    r.push('o');
    r.push('-');
    r.push('A');
    r.push('n');
    r.push('o');
    r.push('t');
    r.push('h');
    r.push('e');
    r.push('r');
    r.push('-');
    r.push('W');
    r.push('a');
    r.push('y');
    r.push('-');
    r.push('\u{305d}');
    r.push('\u{308c}');
    r.push('\u{305e}');
    r.push('\u{308c}');
    r.push('\u{306e}');
    r.push('\u{5834}');
    r.push('\u{6240}');
    r
}

/// The encoded ground bytes of vector 19.
fn ev_19() -> (r: Vec<u8>)
    ensures
        r@.len() == 40,
        r@ == seq![b'H', b'e', b'l', b'l', b'o', b'-', b'A', b'n', b'o', b't', b'h', b'e', b'r', b'-', b'W', b'a', b'y', b'-', b'-', b'f', b'c', b'4', b'q', b'u', b'a', b'0', b'5', b'a', b'u', b'w', b'b', b'3', b'6', b'7', b'4', b'v', b'f', b'r', b'0', b'b'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'H');
    r.push(b'e');
    r.push(b'l');
    r.push(b'l');
    r.push(b'o');
    r.push(b'-');
    r.push(b'A');
    r.push(b'n');
    r.push(b'o');
    r.push(b't');
    r.push(b'h');
    r.push(b'e');
    r.push(b'r');
    r.push(b'-');
    r.push(b'W');
    r.push(b'a');
    r.push(b'y');
    r.push(b'-');
    r.push(b'-');
    r.push(b'f');
    r.push(b'c');
    r.push(b'4');
    r.push(b'q');
    r.push(b'u');
    r.push(b'a');
    r.push(b'0');
    r.push(b'5');
    r.push(b'a');
    r.push(b'u');
    r.push(b'w');
    r.push(b'b');
    r.push(b'3');
    r.push(b'6');
    r.push(b'7');
    r.push(b'4');
    r.push(b'v');
    r.push(b'f');
    r.push(b'r');
    r.push(b'0');
    r.push(b'b');
    r
}

/// Vector 19 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_19() -> (r: bool)
    ensures
        r,
{
    let dv = dv_19();
    let sd: &[char] = dv.as_slice();
    let ev = ev_19();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 12381, 12428, 12382, 12428, 12398, 22580, 25152])) by {
            assert(se@ == seq![b'H', b'e', b'l', b'l', b'o', b'-', b'A', b'n', b'o', b't', b'h', b'e', b'r', b'-', b'W', b'a', b'y', b'-', b'-', b'f', b'c', b'4', b'q', b'u', b'a', b'0', b'5', b'a', b'u', b'w', b'b', b'3', b'6', b'7', b'4', b'v', b'f', b'r', b'0', b'b']);
            assert_by_compute(decode_model(seq![b'H', b'e', b'l', b'l', b'o', b'-', b'A', b'n', b'o', b't', b'h', b'e', b'r', b'-', b'W', b'a', b'y', b'-', b'-', b'f', b'c', b'4', b'q', b'u', b'a', b'0', b'5', b'a', b'u', b'w', b'b', b'3', b'6', b'7', b'4', b'v', b'f', b'r', b'0', b'b'])
                == Option::Some(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 12381, 12428, 12382, 12428, 12398, 22580, 25152]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 12381, 12428, 12382, 12428, 12398, 22580, 25152]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 72);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 101);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 108);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 108);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 111);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 45);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 65);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 110);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 111);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 116);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 104);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 101);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 114);
            lemma_codes_of_index(sd@, 13);
            assert(codes_of(sd@)[13] == 45);
            lemma_codes_of_index(sd@, 14);
            assert(codes_of(sd@)[14] == 87);
            lemma_codes_of_index(sd@, 15);
            assert(codes_of(sd@)[15] == 97);
            lemma_codes_of_index(sd@, 16);
            assert(codes_of(sd@)[16] == 121);
            lemma_codes_of_index(sd@, 17);
            assert(codes_of(sd@)[17] == 45);
            lemma_codes_of_index(sd@, 18);
            assert(codes_of(sd@)[18] == 12381);
            lemma_codes_of_index(sd@, 19);
            assert(codes_of(sd@)[19] == 12428);
            lemma_codes_of_index(sd@, 20);
            assert(codes_of(sd@)[20] == 12382);
            lemma_codes_of_index(sd@, 21);
            assert(codes_of(sd@)[21] == 12428);
            lemma_codes_of_index(sd@, 22);
            assert(codes_of(sd@)[22] == 12398);
            lemma_codes_of_index(sd@, 23);
            assert(codes_of(sd@)[23] == 22580);
            lemma_codes_of_index(sd@, 24);
            assert(codes_of(sd@)[24] == 25152);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 12381, 12428, 12382, 12428, 12398, 22580, 25152]);
        }
        assert(encode_model(sd@) == Option::Some(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 45, 102, 99, 52, 113, 117, 97, 48, 53, 97, 117, 119, 98, 51, 54, 55, 52, 118, 102, 114, 48, 98])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 12381, 12428, 12382, 12428, 12398, 22580, 25152])
                == Option::Some(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 45, 102, 99, 52, 113, 117, 97, 48, 53, 97, 117, 119, 98, 51, 54, 55, 52, 118, 102, 114, 48, 98])) by {
                assert_by_compute(encode_model_codes(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 12381, 12428, 12382, 12428, 12398, 22580, 25152])
                    == Option::Some(seq![72, 101, 108, 108, 111, 45, 65, 110, 111, 116, 104, 101, 114, 45, 87, 97, 121, 45, 45, 102, 99, 52, 113, 117, 97, 48, 53, 97, 117, 119, 98, 51, 54, 55, 52, 118, 102, 114, 48, 98]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['H', 'e', 'l', 'l', 'o', '-', 'A', 'n', 'o', 't', 'h', 'e', 'r', '-', 'W', 'a', 'y', '-', '-', 'f', 'c', '4', 'q', 'u', 'a', '0', '5', 'a', 'u', 'w', 'b', '3', '6', '7', '4', 'v', 'f', 'r', '0', 'b']);
    true
}


/* ----------- vector 20: (unnamed) ----------- */
/// The decoded ground string of vector 20 (code points: 3072 3068 3064 5C4B 6839 306E 4E0B 0032).
fn dv_20() -> (r: Vec<char>)
    ensures
        r@.len() == 8,
        r@ == seq!['\u{3072}', '\u{3068}', '\u{3064}', '\u{5c4b}', '\u{6839}', '\u{306e}', '\u{4e0b}', '2'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{3072}');
    r.push('\u{3068}');
    r.push('\u{3064}');
    r.push('\u{5c4b}');
    r.push('\u{6839}');
    r.push('\u{306e}');
    r.push('\u{4e0b}');
    r.push('2');
    r
}

/// The encoded ground bytes of vector 20.
fn ev_20() -> (r: Vec<u8>)
    ensures
        r@.len() == 19,
        r@ == seq![b'2', b'-', b'u', b'9', b't', b'l', b'z', b'r', b'9', b'7', b'5', b'6', b'b', b't', b'3', b'u', b'c', b'0', b'v'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'2');
    r.push(b'-');
    r.push(b'u');
    r.push(b'9');
    r.push(b't');
    r.push(b'l');
    r.push(b'z');
    r.push(b'r');
    r.push(b'9');
    r.push(b'7');
    r.push(b'5');
    r.push(b'6');
    r.push(b'b');
    r.push(b't');
    r.push(b'3');
    r.push(b'u');
    r.push(b'c');
    r.push(b'0');
    r.push(b'v');
    r
}

/// Vector 20 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_20() -> (r: bool)
    ensures
        r,
{
    let dv = dv_20();
    let sd: &[char] = dv.as_slice();
    let ev = ev_20();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![12402, 12392, 12388, 23627, 26681, 12398, 19979, 50])) by {
            assert(se@ == seq![b'2', b'-', b'u', b'9', b't', b'l', b'z', b'r', b'9', b'7', b'5', b'6', b'b', b't', b'3', b'u', b'c', b'0', b'v']);
            assert_by_compute(decode_model(seq![b'2', b'-', b'u', b'9', b't', b'l', b'z', b'r', b'9', b'7', b'5', b'6', b'b', b't', b'3', b'u', b'c', b'0', b'v'])
                == Option::Some(seq![12402, 12392, 12388, 23627, 26681, 12398, 19979, 50]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![12402, 12392, 12388, 23627, 26681, 12398, 19979, 50]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 12402);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 12392);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 12388);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 23627);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 26681);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 12398);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 19979);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 50);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![12402, 12392, 12388, 23627, 26681, 12398, 19979, 50]);
        }
        assert(encode_model(sd@) == Option::Some(seq![50, 45, 117, 57, 116, 108, 122, 114, 57, 55, 53, 54, 98, 116, 51, 117, 99, 48, 118])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![12402, 12392, 12388, 23627, 26681, 12398, 19979, 50])
                == Option::Some(seq![50, 45, 117, 57, 116, 108, 122, 114, 57, 55, 53, 54, 98, 116, 51, 117, 99, 48, 118])) by {
                assert_by_compute(encode_model_codes(seq![12402, 12392, 12388, 23627, 26681, 12398, 19979, 50])
                    == Option::Some(seq![50, 45, 117, 57, 116, 108, 122, 114, 57, 55, 53, 54, 98, 116, 51, 117, 99, 48, 118]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['2', '-', 'u', '9', 't', 'l', 'z', 'r', '9', '7', '5', '6', 'b', 't', '3', 'u', 'c', '0', 'v']);
    true
}


/* ----------- vector 21: (unnamed) ----------- */
/// The decoded ground string of vector 21 (code points: 004D 0061 006A 0069 3067 004B 006F 0069 3059 308B 0035 79D2 524D).
fn dv_21() -> (r: Vec<char>)
    ensures
        r@.len() == 13,
        r@ == seq!['M', 'a', 'j', 'i', '\u{3067}', 'K', 'o', 'i', '\u{3059}', '\u{308b}', '5', '\u{79d2}', '\u{524d}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('M');
    r.push('a');
    r.push('j');
    r.push('i');
    r.push('\u{3067}');
    r.push('K');
    r.push('o');
    r.push('i');
    r.push('\u{3059}');
    r.push('\u{308b}');
    r.push('5');
    r.push('\u{79d2}');
    r.push('\u{524d}');
    r
}

/// The encoded ground bytes of vector 21.
fn ev_21() -> (r: Vec<u8>)
    ensures
        r@.len() == 26,
        r@ == seq![b'M', b'a', b'j', b'i', b'K', b'o', b'i', b'5', b'-', b'7', b'8', b'3', b'g', b'u', b'e', b'6', b'q', b'z', b'0', b'7', b'5', b'a', b'z', b'm', b'5', b'e'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'M');
    r.push(b'a');
    r.push(b'j');
    r.push(b'i');
    r.push(b'K');
    r.push(b'o');
    r.push(b'i');
    r.push(b'5');
    r.push(b'-');
    r.push(b'7');
    r.push(b'8');
    r.push(b'3');
    r.push(b'g');
    r.push(b'u');
    r.push(b'e');
    r.push(b'6');
    r.push(b'q');
    r.push(b'z');
    r.push(b'0');
    r.push(b'7');
    r.push(b'5');
    r.push(b'a');
    r.push(b'z');
    r.push(b'm');
    r.push(b'5');
    r.push(b'e');
    r
}

/// Vector 21 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_21() -> (r: bool)
    ensures
        r,
{
    let dv = dv_21();
    let sd: &[char] = dv.as_slice();
    let ev = ev_21();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![77, 97, 106, 105, 12391, 75, 111, 105, 12377, 12427, 53, 31186, 21069])) by {
            assert(se@ == seq![b'M', b'a', b'j', b'i', b'K', b'o', b'i', b'5', b'-', b'7', b'8', b'3', b'g', b'u', b'e', b'6', b'q', b'z', b'0', b'7', b'5', b'a', b'z', b'm', b'5', b'e']);
            assert_by_compute(decode_model(seq![b'M', b'a', b'j', b'i', b'K', b'o', b'i', b'5', b'-', b'7', b'8', b'3', b'g', b'u', b'e', b'6', b'q', b'z', b'0', b'7', b'5', b'a', b'z', b'm', b'5', b'e'])
                == Option::Some(seq![77, 97, 106, 105, 12391, 75, 111, 105, 12377, 12427, 53, 31186, 21069]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![77, 97, 106, 105, 12391, 75, 111, 105, 12377, 12427, 53, 31186, 21069]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 77);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 97);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 106);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 105);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 12391);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 75);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 111);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 105);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 12377);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 12427);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 53);
            lemma_codes_of_index(sd@, 11);
            assert(codes_of(sd@)[11] == 31186);
            lemma_codes_of_index(sd@, 12);
            assert(codes_of(sd@)[12] == 21069);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![77, 97, 106, 105, 12391, 75, 111, 105, 12377, 12427, 53, 31186, 21069]);
        }
        assert(encode_model(sd@) == Option::Some(seq![77, 97, 106, 105, 75, 111, 105, 53, 45, 55, 56, 51, 103, 117, 101, 54, 113, 122, 48, 55, 53, 97, 122, 109, 53, 101])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![77, 97, 106, 105, 12391, 75, 111, 105, 12377, 12427, 53, 31186, 21069])
                == Option::Some(seq![77, 97, 106, 105, 75, 111, 105, 53, 45, 55, 56, 51, 103, 117, 101, 54, 113, 122, 48, 55, 53, 97, 122, 109, 53, 101])) by {
                assert_by_compute(encode_model_codes(seq![77, 97, 106, 105, 12391, 75, 111, 105, 12377, 12427, 53, 31186, 21069])
                    == Option::Some(seq![77, 97, 106, 105, 75, 111, 105, 53, 45, 55, 56, 51, 103, 117, 101, 54, 113, 122, 48, 55, 53, 97, 122, 109, 53, 101]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['M', 'a', 'j', 'i', 'K', 'o', 'i', '5', '-', '7', '8', '3', 'g', 'u', 'e', '6', 'q', 'z', '0', '7', '5', 'a', 'z', 'm', '5', 'e']);
    true
}


/* ----------- vector 22: (unnamed) ----------- */
/// The decoded ground string of vector 22 (code points: 30D1 30D5 30A3 30FC 0064 0065 30EB 30F3 30D0).
fn dv_22() -> (r: Vec<char>)
    ensures
        r@.len() == 9,
        r@ == seq!['\u{30d1}', '\u{30d5}', '\u{30a3}', '\u{30fc}', 'd', 'e', '\u{30eb}', '\u{30f3}', '\u{30d0}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{30d1}');
    r.push('\u{30d5}');
    r.push('\u{30a3}');
    r.push('\u{30fc}');
    r.push('d');
    r.push('e');
    r.push('\u{30eb}');
    r.push('\u{30f3}');
    r.push('\u{30d0}');
    r
}

/// The encoded ground bytes of vector 22.
fn ev_22() -> (r: Vec<u8>)
    ensures
        r@.len() == 17,
        r@ == seq![b'd', b'e', b'-', b'j', b'g', b'4', b'a', b'v', b'h', b'b', b'y', b'1', b'n', b'o', b'c', b'0', b'd'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'd');
    r.push(b'e');
    r.push(b'-');
    r.push(b'j');
    r.push(b'g');
    r.push(b'4');
    r.push(b'a');
    r.push(b'v');
    r.push(b'h');
    r.push(b'b');
    r.push(b'y');
    r.push(b'1');
    r.push(b'n');
    r.push(b'o');
    r.push(b'c');
    r.push(b'0');
    r.push(b'd');
    r
}

/// Vector 22 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_22() -> (r: bool)
    ensures
        r,
{
    let dv = dv_22();
    let sd: &[char] = dv.as_slice();
    let ev = ev_22();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![12497, 12501, 12451, 12540, 100, 101, 12523, 12531, 12496])) by {
            assert(se@ == seq![b'd', b'e', b'-', b'j', b'g', b'4', b'a', b'v', b'h', b'b', b'y', b'1', b'n', b'o', b'c', b'0', b'd']);
            assert_by_compute(decode_model(seq![b'd', b'e', b'-', b'j', b'g', b'4', b'a', b'v', b'h', b'b', b'y', b'1', b'n', b'o', b'c', b'0', b'd'])
                == Option::Some(seq![12497, 12501, 12451, 12540, 100, 101, 12523, 12531, 12496]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![12497, 12501, 12451, 12540, 100, 101, 12523, 12531, 12496]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 12497);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 12501);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 12451);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 12540);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 100);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 101);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 12523);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 12531);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 12496);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![12497, 12501, 12451, 12540, 100, 101, 12523, 12531, 12496]);
        }
        assert(encode_model(sd@) == Option::Some(seq![100, 101, 45, 106, 103, 52, 97, 118, 104, 98, 121, 49, 110, 111, 99, 48, 100])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![12497, 12501, 12451, 12540, 100, 101, 12523, 12531, 12496])
                == Option::Some(seq![100, 101, 45, 106, 103, 52, 97, 118, 104, 98, 121, 49, 110, 111, 99, 48, 100])) by {
                assert_by_compute(encode_model_codes(seq![12497, 12501, 12451, 12540, 100, 101, 12523, 12531, 12496])
                    == Option::Some(seq![100, 101, 45, 106, 103, 52, 97, 118, 104, 98, 121, 49, 110, 111, 99, 48, 100]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['d', 'e', '-', 'j', 'g', '4', 'a', 'v', 'h', 'b', 'y', '1', 'n', 'o', 'c', '0', 'd']);
    true
}


/* ----------- vector 23: (unnamed) ----------- */
/// The decoded ground string of vector 23 (code points: 305D 306E 30B9 30D4 30FC 30C9 3067).
fn dv_23() -> (r: Vec<char>)
    ensures
        r@.len() == 7,
        r@ == seq!['\u{305d}', '\u{306e}', '\u{30b9}', '\u{30d4}', '\u{30fc}', '\u{30c9}', '\u{3067}'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('\u{305d}');
    r.push('\u{306e}');
    r.push('\u{30b9}');
    r.push('\u{30d4}');
    r.push('\u{30fc}');
    r.push('\u{30c9}');
    r.push('\u{3067}');
    r
}

/// The encoded ground bytes of vector 23.
fn ev_23() -> (r: Vec<u8>)
    ensures
        r@.len() == 15,
        r@ == seq![b'd', b'9', b'j', b'u', b'a', b'u', b'4', b'1', b'a', b'w', b'c', b'z', b'c', b'z', b'p'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'd');
    r.push(b'9');
    r.push(b'j');
    r.push(b'u');
    r.push(b'a');
    r.push(b'u');
    r.push(b'4');
    r.push(b'1');
    r.push(b'a');
    r.push(b'w');
    r.push(b'c');
    r.push(b'z');
    r.push(b'c');
    r.push(b'z');
    r.push(b'p');
    r
}

/// Vector 23 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_23() -> (r: bool)
    ensures
        r,
{
    let dv = dv_23();
    let sd: &[char] = dv.as_slice();
    let ev = ev_23();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![12381, 12398, 12473, 12500, 12540, 12489, 12391])) by {
            assert(se@ == seq![b'd', b'9', b'j', b'u', b'a', b'u', b'4', b'1', b'a', b'w', b'c', b'z', b'c', b'z', b'p']);
            assert_by_compute(decode_model(seq![b'd', b'9', b'j', b'u', b'a', b'u', b'4', b'1', b'a', b'w', b'c', b'z', b'c', b'z', b'p'])
                == Option::Some(seq![12381, 12398, 12473, 12500, 12540, 12489, 12391]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![12381, 12398, 12473, 12500, 12540, 12489, 12391]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 12381);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 12398);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 12473);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 12500);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 12540);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 12489);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 12391);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![12381, 12398, 12473, 12500, 12540, 12489, 12391]);
        }
        assert(encode_model(sd@) == Option::Some(seq![100, 57, 106, 117, 97, 117, 52, 49, 97, 119, 99, 122, 99, 122, 112])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![12381, 12398, 12473, 12500, 12540, 12489, 12391])
                == Option::Some(seq![100, 57, 106, 117, 97, 117, 52, 49, 97, 119, 99, 122, 99, 122, 112])) by {
                assert_by_compute(encode_model_codes(seq![12381, 12398, 12473, 12500, 12540, 12489, 12391])
                    == Option::Some(seq![100, 57, 106, 117, 97, 117, 52, 49, 97, 119, 99, 122, 99, 122, 112]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['d', '9', 'j', 'u', 'a', 'u', '4', '1', 'a', 'w', 'c', 'z', 'c', 'z', 'p']);
    true
}


/* ----------- vector 24: ASCII string that breaks the existing rules for host-name labels (It's not a realistic example for IDNA, because IDNA never encodes pure ASCII labels.) ----------- */
/// The decoded ground string of vector 24 (code points: 002D 003E 0020 0024 0031 002E 0030 0030 0020 003C 002D).
fn dv_24() -> (r: Vec<char>)
    ensures
        r@.len() == 11,
        r@ == seq!['-', '>', ' ', '$', '1', '.', '0', '0', ' ', '<', '-'],
{
    let mut r: Vec<char> = Vec::new();
    r.push('-');
    r.push('>');
    r.push(' ');
    r.push('$');
    r.push('1');
    r.push('.');
    r.push('0');
    r.push('0');
    r.push(' ');
    r.push('<');
    r.push('-');
    r
}

/// The encoded ground bytes of vector 24.
fn ev_24() -> (r: Vec<u8>)
    ensures
        r@.len() == 12,
        r@ == seq![b'-', b'>', b' ', b'$', b'1', b'.', b'0', b'0', b' ', b'<', b'-', b'-'],
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'-');
    r.push(b'>');
    r.push(b' ');
    r.push(b'$');
    r.push(b'1');
    r.push(b'.');
    r.push(b'0');
    r.push(b'0');
    r.push(b' ');
    r.push(b'<');
    r.push(b'-');
    r.push(b'-');
    r
}

/// Vector 24 round trips: decode gives the decoded chars, encode gives
/// the encoded chars, and both models evaluate the pair by computation.
pub exec fn witness_vec_24() -> (r: bool)
    ensures
        r,
{
    let dv = dv_24();
    let sd: &[char] = dv.as_slice();
    let ev = ev_24();
    let se: &[u8] = ev.as_slice();
    // leg 1: exec decode and its model computation
    let dec = decode_bytes(se);
    proof {
        assert(decode_model(se@) == Option::Some(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45])) by {
            assert(se@ == seq![b'-', b'>', b' ', b'$', b'1', b'.', b'0', b'0', b' ', b'<', b'-', b'-']);
            assert_by_compute(decode_model(seq![b'-', b'>', b' ', b'$', b'1', b'.', b'0', b'0', b' ', b'<', b'-', b'-'])
                == Option::Some(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45]));
        }
    }
    assert(dec.is_some());
    assert((dec->0)@ == dv@);
    // leg 2: exec encode and its model computation
    let enc = encode_chars(sd);
    proof {
        assert(codes_of(sd@) == seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45]) by {
            lemma_codes_of_len(sd@);
            lemma_codes_of_index(sd@, 0);
            assert(codes_of(sd@)[0] == 45);
            lemma_codes_of_index(sd@, 1);
            assert(codes_of(sd@)[1] == 62);
            lemma_codes_of_index(sd@, 2);
            assert(codes_of(sd@)[2] == 32);
            lemma_codes_of_index(sd@, 3);
            assert(codes_of(sd@)[3] == 36);
            lemma_codes_of_index(sd@, 4);
            assert(codes_of(sd@)[4] == 49);
            lemma_codes_of_index(sd@, 5);
            assert(codes_of(sd@)[5] == 46);
            lemma_codes_of_index(sd@, 6);
            assert(codes_of(sd@)[6] == 48);
            lemma_codes_of_index(sd@, 7);
            assert(codes_of(sd@)[7] == 48);
            lemma_codes_of_index(sd@, 8);
            assert(codes_of(sd@)[8] == 32);
            lemma_codes_of_index(sd@, 9);
            assert(codes_of(sd@)[9] == 60);
            lemma_codes_of_index(sd@, 10);
            assert(codes_of(sd@)[10] == 45);
            vstd::seq::lemma_seq_ext_equal(codes_of(sd@), seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45]);
        }
        assert(encode_model(sd@) == Option::Some(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45, 45])) by {
            reveal(encode_model);
            assert(sd@.len() as int <= 0xFFFF_FFFF);
            assert(encode_model_codes(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45])
                == Option::Some(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45, 45])) by {
                assert_by_compute(encode_model_codes(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45])
                    == Option::Some(seq![45, 62, 32, 36, 49, 46, 48, 48, 32, 60, 45, 45]));
            }
        }
    }
    assert(enc.is_some());
    assert((enc->0)@ == seq!['-', '>', ' ', '$', '1', '.', '0', '0', ' ', '<', '-', '-']);
    true
}

}

fn main() {}
