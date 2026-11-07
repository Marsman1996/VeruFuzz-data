//! `hex` library mirror (aggregating
//! every verified item of code/src/lib.rs)
//!
//! Upstream: https://github.com/KokaKiwi/rust-hex
//!   pin e25a8701f7f6b5ec4acedffcb4a45cfb69cc34eb (i.e. code/src/lib.rs; the
//!   code/ tree is untouched)
//!
//! Mirror and relaxation ledger (KVerus relax caliber):
//! 1. The generics `T: AsRef<[u8]>` / `iter::FromIterator<char>` are outside
//!    the Verus transcription surface -> the public functions are monomorphized
//!    to `&[u8]` arguments per call site (encode_to_slice* / decode_to_slice /
//!    encode / encode_upper / decode / *from_hex); the monomorphized contract is
//!    exactly the upstream generic contract after instantiation.
//! 2. The literal-table lookups DECODE_TABLE (256 entries) /
//!    HEX_CHARS_LOWER/UPPER (16 entries each) are transcribed as equivalent
//!    range logic (`decode_lookup` / `table_lookup_nibble`); the table <->
//!    range-logic equivalence was fully confirmed at runtime against the
//!    upstream (256x256 matrix drivers).
//! 3. The `chunks_exact(2).zip(...)` / `chunks_exact_mut(2)` iterator loops are
//!    rewritten as equivalent index loops (the loop domain is exactly given by
//!    the upstream precondition length checks).
//! 4. The Vec allocation paths (the vec![] macro is outside the support
//!    surface) are rewritten as `Vec::new` + incremental push construction;
//!    the sequence contract (len and every element value) matches the upstream
//!    prealloc+fill.
//! 5. The collect-iterator paths of ToHex::encode_hex / encode_hex_upper are
//!    not transcribed; their observed semantics (the output equals the
//!    encode_to_slice/encode hex string) are carried by the coverage
//!    contract-level witness theorems (harness/traits_props.rs).
//! 6. `String::from_utf8(out).unwrap()` (inside encode/encode_upper): vstd has
//!    no std-side spec for this API, so the mirror returns the Vec<u8> "byte
//!    string"; the semantic precondition that the unwrap never fires is
//!    carried by the witness theorem `ascii_seq_valid_utf8` (all output bytes
//!    < 0x80 => valid_utf8); "std never judges valid_utf8 bytes as Err" enters
//!    the assumption ledger (std doc semantics), confirmed by runtime drivers
//!    (encode_*_roundtrip panic-free, the value equal to the hex string).
//! 7. Not transcribed: the ToHex/FromHex trait generic bodies, the serde
//!    module (dependency realm), fmt::Display.
//!
//! Consumption: this file has no fn main; per KVerus it is driven through the
//! harness files, which include this module via
//! `#[path = "../src/lib.rs"] mod <name>;` -- copying its spec is forbidden.

use vstd::prelude::*;
use vstd::std_specs::vec::*;
use vstd::utf8::{is_leading_byte_width_1, valid_utf8};
use vstd::utf8::partial_valid_utf8_extend_ascii_block;
use vstd::utf8::partial_valid_utf8;

mod error;
pub use error::FromHexError;

verus! {

/* ============================================================
 * spec model (L2: semantic extraction of the upstream doc contract;
 * authority = the trait/implementation code bodies)
 * ============================================================ */

/// Single-byte hex digit value: '0'..'9' -> 0..9, 'a'..'f'/'A'..'F' -> 10..15
/// (upper and lower case may be mixed, matching the FromHex::from_hex doc);
/// every other byte is invalid. The constant 0xFF is the upstream DECODE_TABLE
/// sentinel (`__ := u8::MAX`).
pub open spec fn hex_digit_val(c: u8) -> u8 {
    if 0x30 <= c <= 0x39 {
        (c - 0x30) as u8
    } else if 0x61 <= c <= 0x66 {
        (c - 0x61 + 10) as u8
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as u8
    } else {
        0xFF
    }
}

/// nibble (in [0,16)) -> ASCII byte; upper selects HEX_CHARS_UPPER /
/// HEX_CHARS_LOWER
pub open spec fn hex_char(nib: u8, upper: bool) -> u8 {
    if nib < 10 {
        (0x30 + nib) as u8
    } else if upper {
        (0x41 + (nib - 10)) as u8
    } else {
        (0x61 + (nib - 10)) as u8
    }
}

/// Synthetic merge semantics of `val`: high 4 bits << 4 | low 4 bits (the bit
/// diagram in the upstream comments lib.rs:210-216)
pub open spec fn merge_nibbles(u: u8, l: u8) -> u8 {
    (hex_digit_val(u) * 16 + hex_digit_val(l)) as u8
}

/// Decoded byte sequence of an even-length input (index model: byte i comes
/// from the pair (2i, 2i+1))
pub open spec fn decoded_seq(s: Seq<u8>) -> Seq<u8> {
    if s.len() % 2 == 0 {
        Seq::new(s.len() / 2, |i: int| merge_nibbles(s[2 * i], s[2 * i + 1]))
    } else {
        Seq::<u8>::empty() // odd-length input: the upstream OddLength has
        // already short-circuited; the empty sequence is only a sentinel value
    }
}

/// Encoded byte sequence (index model: an even j comes from the high nibble,
/// an odd j from the low nibble)
pub open spec fn encode_seq(s: Seq<u8>, upper: bool) -> Seq<u8> {
    Seq::new(
        2 * s.len(),
        |j: int| if j % 2 == 0 {
            hex_char(s[j / 2] / 16, upper)
        } else {
            hex_char(s[j / 2] % 16, upper)
        },
    )
}

/// Both bytes of pair k are valid
pub open spec fn valid_pair(s: Seq<u8>, k: int) -> bool {
    hex_digit_val(s[2 * k]) != 0xFF && hex_digit_val(s[2 * k + 1]) != 0xFF
}

/// Index of the first invalid pair (-1 = all valid); the recursive structure
/// mirrors the upstream execution order "consume the pairs in sequence,
/// short-circuit and return at the first invalid one".
pub open spec fn first_invalid_pair(s: Seq<u8>) -> int
    decreases s.len()
{
    if s.len() % 2 != 0 {
        -2 // odd-length input: the upstream OddLength has already short-circuited;
        // -2 is the sentinel (never to be confused with -1)
    } else if s.len() == 0 {
        -1
    } else if !valid_pair(s, 0) {
        0
    } else {
        let rest = first_invalid_pair(s.subrange(2, s.len() as int));
        if rest == -1 { -1 } else { 1 + rest }
    }
}

/// Full-information spec of the decode error side (variant, character, byte
/// index), the derivation of val + the upstream short-circuit order. Used by
/// the error contracts of decode_to_slice / decode_in_slice / each from_hex
/// form.
pub open spec fn decode_err_variant(s: Seq<u8>) -> FromHexError {
    let k = first_invalid_pair(s);
    if k == -1 {
        FromHexError::OddLength // sentinel: only guaranteed to be referenced
        // when first_invalid == -1
    } else if hex_digit_val(s[2 * k]) == 0xFF {
        FromHexError::InvalidHexCharacter {
            c: s[2 * k] as char,
            index: (2 * k) as usize,
        }
    } else {
        FromHexError::InvalidHexCharacter {
            c: s[2 * k + 1] as char,
            index: (2 * k + 1) as usize,
        }
    }
}

/* ============================================================
 * Decode path (exec mirror; the code bodies are the authority)
 * ============================================================ */

/// Origin: lib.rs:174-192 `DECODE_TABLE` lookup (256-byte literal table) ->
/// equivalent range logic (the b"0123456789abcdef" row + b"ABCDEF" row; the
/// sentinel 0xFF == __)
exec fn decode_lookup(c: u8) -> (r: u8)
    ensures
        r == hex_digit_val(c),
        r != 0xFF ==> r <= 15, // table value domain (0..15 or the sentinel)
{
    if 0x30 <= c && c <= 0x39 {
        c - 0x30
    } else if 0x61 <= c && c <= 0x66 {
        c - 0x61 + 10
    } else if 0x41 <= c && c <= 0x46 {
        c - 0x41 + 10
    } else {
        0xFF
    }
}

/// Origin: lib.rs:194-217 `val` (the table lookup absorbed into decode_lookup;
/// the c: bytes[0] as char, index contract preserved)
pub exec fn val(bytes: &[u8], idx: usize) -> (r: Result<u8, FromHexError>)
    requires
        bytes@.len() == 2,
        (idx as int) + 1 <= usize::MAX as int, /* index: idx+1 does not
        overflow; at the call sites 2*i+1 < len <= isize::MAX */
    ensures
        hex_digit_val(bytes@[0]) == 0xFF ==> r == Result::Err(
            FromHexError::InvalidHexCharacter {
                c: bytes[0] as char,
                index: idx,
            },
        ),
        hex_digit_val(bytes@[0]) != 0xFF && hex_digit_val(bytes@[1]) == 0xFF ==> r == Result::Err(
            FromHexError::InvalidHexCharacter {
                c: bytes[1] as char,
                index: (idx + 1) as usize,
            },
        ),
        r.is_ok() == (hex_digit_val(bytes@[0]) != 0xFF && hex_digit_val(bytes@[1]) != 0xFF),
        hex_digit_val(bytes@[0]) != 0xFF && hex_digit_val(bytes@[1]) != 0xFF ==> r == Result::Ok(
            (hex_digit_val(bytes@[0]) * 16 + hex_digit_val(bytes@[1])) as u8,
        ),
{
    /* Origin Rust: let upper = DECODE_TABLE[bytes[0] as usize]; */
    let upper = decode_lookup(bytes[0]);
    /* Origin Rust: let lower = DECODE_TABLE[bytes[1] as usize]; */
    let lower = decode_lookup(bytes[1]);
    if upper == u8::MAX {
        return Result::Err(FromHexError::InvalidHexCharacter {
            c: bytes[0] as char,
            index: idx,
        });
    }
    if lower == u8::MAX {
        return Result::Err(FromHexError::InvalidHexCharacter {
            c: bytes[1] as char,
            index: idx + 1,
        });
    }
    /* Origin Rust: Ok((upper << 4) | lower) -- the upstream comments state the
       merge of the two 4-bit numbers; the bitwise form equals the arithmetic
       *16 + (range [0,16), no bit overlap); the same merge is expressed
       arithmetically here. */
    assert(upper <= 15);
    assert(lower <= 15);
    let b = upper * 16 + lower;
    Result::Ok(b)
}

/// Origin: lib.rs:321-336 `decode_to_slice`
/// (generic monomorphized to &[u8]; chunks_exact(2).zip(out) rewritten as an
/// index loop)
/// Upstream doc (lib.rs:308-319):
///   Decode a hex string into a mutable bytes slice.
///   Both, upper and lower case characters are valid in the input string and can
///   even be mixed (e.g. `f9b4ca`, `F9B4CA` and `f9B4Ca` are all valid strings).
pub exec fn decode_to_slice(data: &[u8], out: &mut [u8]) -> (r: Result<(), FromHexError>)
    ensures
        data@.len() % 2 != 0 ==> r == Result::Err(FromHexError::OddLength),
        data@.len() % 2 == 0 && data@.len() / 2 != old(out)@.len() ==> r == Result::Err(
            FromHexError::InvalidStringLength,
        ),
        data@.len() % 2 == 0 && data@.len() / 2 == old(out)@.len()
            && first_invalid_pair(data@) == -1 ==> r.is_ok()
            && final(out)@ == decoded_seq(data@),
        data@.len() % 2 == 0 && data@.len() / 2 == old(out)@.len()
            && first_invalid_pair(data@) != -1 ==> r == Result::Err(
            decode_err_variant(data@),
        ),
        r.is_err() ==> final(out)@.len() == old(out)@.len(),
{
    /* Origin Rust: let data = data.as_ref(); (identity after the generic
       monomorphization) */
    let d = data;
    /* Origin Rust: if data.len() % 2 != 0 { return Err(FromHexError::OddLength); } */
    if d.len() % 2 != 0 {
        return Result::Err(FromHexError::OddLength);
    }
    /* Origin Rust: if data.len() / 2 != out.len() { return Err(FromHexError::InvalidStringLength); } */
    if d.len() / 2 != out.len() {
        return Result::Err(FromHexError::InvalidStringLength);
    }
    let ghost s = d@;
    assert(s == data@);
    /* Origin Rust: for (i, (data, byte)) in data.chunks_exact(2).zip(out).enumerate()
       { *byte = val(data, 2 * i)?; } */
    let mut i: usize = 0;
    while i < out.len()
        invariant
            0 <= i <= out@.len(),
            s == d@,
            s == data@,
            s.len() == 2 * out@.len(),
            out@.len() == old(out)@.len(),
            forall|j: int| 0 <= j < i ==> valid_pair(s, j),
            forall|j: int| 0 <= j < i ==> out@ [j] == merge_nibbles(s[2 * j], s[2 * j + 1]),
        decreases out.len() - i
    {
        assert(i < out@.len());
        assert(s.len() % 2 == 0);
        assert(2 * i + 2 <= d.len());
        assert((2 * i + 2) as int == 2 * (i as int) + 2);
        let pair = &d[2 * i..2 * i + 2];
        assert(pair@ == s.subrange(2 * i as int, 2 * i as int + 2));
        match val(pair, 2 * i) {
            Result::Ok(b) => {
                assert((i as int) < out@.len());
                out[i] = b;
                assert(out@ [i as int] == b);
                i += 1;
            }
            Result::Err(e) => {
                proof {
                    assert(s == data@);
                    assert(data@.len() % 2 == 0);
                    assert(data@.len() / 2 == old(out)@.len());
                    assert(s.len() % 2 == 0);
                    lip_exact(s, i as int);
                    assert(e == decode_err_variant(s));
                }
                return Result::Err(e);
            }
        }
    }
    proof {
        assert(i == out@.len());
        assert forall|j: int| 0 <= j < i implies out@ [j] == merge_nibbles(s[2 * j], s[2 * j + 1]) by {}
        lip_none(s);
        assert(first_invalid_pair(s) == -1);
        assert(s.len() % 2 == 0);
        assert forall|j: int| 0 <= j < out@.len() implies out@ [j] == decoded_seq(s)[j] by {
            assert(0 <= j < i);
            assert(decoded_seq(s)[j] == merge_nibbles(s[2 * j], s[2 * j + 1]));
            assert(out@ [j] == merge_nibbles(s[2 * j], s[2 * j + 1]));
        }
    }
    Result::Ok(())
}

/// Origin: lib.rs:350-361 `decode_in_slice` (decode in place: the first half
/// receives the decoded result, the trailing hex characters stay; the read
/// positions 2i/2i+1 are never modified earlier than the write to position i)
/// Upstream doc (lib.rs:338-349):
///   Decode a hex string into itself.
///   Both, upper and lower case characters are valid in the input string and can
///   even be mixed (e.g. `f9b4ca`, `F9B4CA` and `f9B4Ca` are all valid strings).
pub exec fn decode_in_slice(in_out: &mut [u8]) -> (r: Result<(), FromHexError>)
    ensures
        old(in_out)@.len() % 2 != 0 ==> r == Result::Err(FromHexError::OddLength),
        old(in_out)@.len() % 2 == 0 && first_invalid_pair(old(in_out)@) == -1 ==> r.is_ok()
            && final(in_out)@ == (decoded_seq(old(in_out)@) + old(in_out)@.subrange(
                (old(in_out)@.len() / 2) as int,
                old(in_out)@.len() as int,
            )),
        old(in_out)@.len() % 2 == 0 && first_invalid_pair(old(in_out)@) != -1 ==> r == Result::Err(
            decode_err_variant(old(in_out)@),
        ),
        r.is_err() ==> final(in_out)@.len() == old(in_out)@.len(),
{
    /* Origin Rust: if in_out.len() % 2 != 0 { return Err(FromHexError::OddLength); } */
    if in_out.len() % 2 != 0 {
        return Result::Err(FromHexError::OddLength);
    }
    let ghost s0 = in_out@;
    assert(s0 == old(in_out)@);
    /* Origin Rust: for i in 0..(in_out.len() / 2) {
       let byte = val(&in_out[2 * i..2 * i + 2], 2 * i)?;
       in_out[i] = byte; } */
    let mut i: usize = 0;
    while i < in_out.len() / 2
        invariant
            0 <= i <= in_out@.len() / 2,
            in_out@.len() == s0.len(),
            s0.len() % 2 == 0,
            forall|j: int| 0 <= j < i ==> valid_pair(s0, j),
            forall|j: int| 0 <= j < i ==> in_out@ [j] == merge_nibbles(s0[2 * j], s0[2 * j + 1]),
            forall|j: int| i <= j < s0.len() ==> in_out@ [j] == s0[j],
            s0 == old(in_out)@,
        decreases in_out@.len() / 2 - i
    {
        assert(i < in_out@.len() / 2);
        assert(2 * i + 2 <= in_out.len());
        assert((2 * i + 2) as int == 2 * (i as int) + 2);
        let pair = &in_out[2 * i..2 * i + 2];
        assert(pair@ == s0.subrange(2 * i as int, 2 * i as int + 2));
        let b = match val(pair, 2 * i) {
            Result::Ok(bb) => {
                proof {
                    assert(valid_pair(s0, i as int));
                    assert(bb == merge_nibbles(s0[2 * (i as int)], s0[2 * (i as int) + 1]));
                }
                bb
            }
            Result::Err(e) => {
                proof {
                    assert(s0 == old(in_out)@);
                    assert(old(in_out)@.len() % 2 == 0);
                    assert(s0.len() % 2 == 0);
                    lip_exact(s0, i as int);
                    assert(e == decode_err_variant(s0));
                }
                return Result::Err(e);
            }
        };
        /* Origin Rust: in_out[i] = byte; -- the read value is returned to an
        owned copy, then written back, same iteration same order */
        in_out[i] = b;
        assert(in_out@ [i as int] == b);
        i += 1;
    }
    proof {
        assert(i == in_out@.len() / 2);
        lip_none(s0);
        assert(first_invalid_pair(s0) == -1);
        assert forall|j: int| 0 <= j < s0.len() implies in_out@ [j]
            == (decoded_seq(s0) + s0.subrange((s0.len() / 2) as int, s0.len() as int))[j] by {
            assert(in_out@ [j] == merge_nibbles(s0[2 * j], s0[2 * j + 1]) || in_out@ [j] == s0[j]);
        }
    }
    Result::Ok(())
}

/* ============================================================
 * Encode path (exec mirror)
 * ============================================================ */

/// Origin: HEX_CHARS_LOWER/HEX_CHARS_UPPER (lib.rs:77-78, a 16-byte literal
/// table each)
/// -> equivalent range logic ('0'..'9' / 'a'..'f' / 'A'..'F')
exec fn table_lookup_nibble(nib: u8, upper: bool) -> (r: u8)
    requires nib < 16
    ensures r == hex_char(nib, upper)
{
    if nib < 10 {
        0x30 + nib
    } else if upper {
        0x41 + (nib - 10)
    } else {
        0x61 + (nib - 10)
    }
}

/// Origin: lib.rs:364-371 `byte2hex` (the table: &[u8;16] parameter absorbed
/// into the upper boolean)
exec fn byte2hex(byte: u8, upper: bool) -> (r: (u8, u8))
    ensures
        r.0 == hex_char(byte / 16, upper),
        r.1 == hex_char(byte % 16, upper),
{
    /* Origin Rust: let high = table[((byte & 0xf0) >> 4) as usize];
       let low = table[(byte & 0x0f) as usize]; (high, low) */
    let hi_nib = (byte & 0xf0) >> 4;
    let lo_nib = byte & 0x0f;
    proof {
        assert(byte / 16 == ((byte & 0xf0) >> 4)) by (bit_vector);
        assert(byte % 16 == (byte & 0x0f)) by (bit_vector);
    }
    (table_lookup_nibble(hi_nib, upper), table_lookup_nibble(lo_nib, upper))
}

/// Origin: lib.rs:373-389 `encode_to_slice_inner` (the table parameter absorbed
/// into the upper boolean;
/// iter().zip(chunks_exact_mut(2)) rewritten as an index loop)
exec fn encode_to_slice_inner(input: &[u8], output: &mut [u8], upper: bool) -> (r: Result<(), FromHexError>)
    ensures
        2 * input@.len() != old(output)@.len() ==> r == Result::Err(
            FromHexError::InvalidStringLength,
        ),
        2 * input@.len() == old(output)@.len() ==> r == Result::Ok(())
            && final(output)@ == encode_seq(input@, upper),
{
    let ghost s = input@;
    /* Origin Rust: if input.len() * 2 != output.len() { return Err(InvalidStringLength); }
       -- the multiplication equality test is rewritten as a division/parity
       test (equivalent: 2*i == o <=> o is even and o/2 == i), avoiding the
       usize multiplication-overflow obligation (the two forms are always
       equal for real slice len <= isize::MAX) */
    if output.len() % 2 != 0 || output.len() / 2 != input.len() {
        return Result::Err(FromHexError::InvalidStringLength);
    }
    /* Origin Rust: for (byte, output) in input.iter().zip(output.chunks_exact_mut(2)) {
       let (high, low) = byte2hex(*byte, table); output[0] = high; output[1] = low; } */
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input@.len(),
            s == input@,
            output@.len() == 2 * input@.len(),
            forall|j: int| 0 <= j < 2 * i ==> output@ [j] == encode_seq(s, upper)[j],
        decreases input.len() - i
    {
        assert(i < input@.len());
        assert(2 * i + 1 < output.len());
        assert((2 * i + 1) as int == 2 * (i as int) + 1);
        let (high, low) = byte2hex(input[i], upper);
        output[2 * i] = high;
        output[2 * i + 1] = low;
        i += 1;
    }
    proof {
        assert(i == input@.len());
        assert forall|j: int| 0 <= j < output@.len() implies output@ [j] == encode_seq(s, upper)[j] by {
            assert forall|j: int| 0 <= j < output@.len() implies output@ [j] == encode_seq(s, upper)[j] by {
                let ib = s[j / 2];
                if j % 2 == 0 {
                    assert(encode_seq(s, upper)[j] == hex_char(ib / 16, upper));
                } else {
                    assert(encode_seq(s, upper)[j] == hex_char(ib % 16, upper));
                }
            }
        }
    }
    Result::Ok(())
}

/// Origin: lib.rs:424-426 `encode_to_slice` (generic T monomorphized to &[u8])
/// Upstream doc (lib.rs:391-423):
///   Encodes some bytes into a mutable slice of bytes using lowercase characters.
///   The output buffer, has to be able to hold exactly `input.len() * 2` bytes,
///   otherwise this function will return an error.
pub exec fn encode_to_slice(input: &[u8], output: &mut [u8]) -> (r: Result<(), FromHexError>)
    ensures
        2 * input@.len() != old(output)@.len() ==> r == Result::Err(
            FromHexError::InvalidStringLength,
        ),
        2 * input@.len() == old(output)@.len() ==> r == Result::Ok(())
            && final(output)@ == encode_seq(input@, false),
{
    /* Origin Rust: encode_to_slice_inner(input.as_ref(), output, HEX_CHARS_LOWER) */
    encode_to_slice_inner(input, output, false)
}

/// Origin: lib.rs:445-450 `encode_to_slice_upper`
/// Upstream doc (lib.rs:428-444):
///   Encodes some bytes into a mutable slice of bytes using uppercase characters.
///   The output buffer, has to be able to hold exactly `input.len() * 2` bytes,
///   otherwise this function will return an error.
pub exec fn encode_to_slice_upper(input: &[u8], output: &mut [u8]) -> (r: Result<(), FromHexError>)
    ensures
        2 * input@.len() != old(output)@.len() ==> r == Result::Err(
            FromHexError::InvalidStringLength,
        ),
        2 * input@.len() == old(output)@.len() ==> r == Result::Ok(())
            && final(output)@ == encode_seq(input@, true),
{
    /* Origin Rust: encode_to_slice_inner(input.as_ref(), output, HEX_CHARS_UPPER) */
    encode_to_slice_inner(input, output, true)
}

/* ============================================================
 * AsRef/alloc path monomorphized mirror + FromHex impl
 * ============================================================ */

/// Origin: lib.rs:219-233 `impl FromHex for Vec<u8>` (the vec![] prealloc+fill
/// rewritten as push incremental construction; the error precedence order and
/// the val short-circuit semantics preserved)
/// Upstream doc (lib.rs:161-165):
///   Creates an instance of type `Self` from the given hex string, or fails
///   with a custom error type.
///   Both, upper and lower case characters are valid and can even be
///   mixed (e.g. `f9b4ca`, `F9B4CA` and `f9B4Ca` are all valid strings).
pub exec fn vec_from_hex(hex: &[u8]) -> (r: Result<Vec<u8>, FromHexError>)
    ensures
        hex@.len() % 2 != 0 ==> r == Result::Err(FromHexError::OddLength),
        hex@.len() % 2 == 0 && first_invalid_pair(hex@) == -1 ==> r.is_ok()
            && r.get_Ok_0()@ == decoded_seq(hex@),
        hex@.len() % 2 == 0 && first_invalid_pair(hex@) != -1 ==> r == Result::Err(
            decode_err_variant(hex@),
        ),
{
    /* Origin Rust: if hex.len() % 2 != 0 { return Err(FromHexError::OddLength); } */
    if hex.len() % 2 != 0 {
        return Result::Err(FromHexError::OddLength);
    }
    let ghost s = hex@;
    /* Origin Rust: let mut out = vec![0; hex.len() / 2];
       decode_to_slice(hex, &mut out)?; Ok(out) -- the vec![] macro is not
       supported, realized as the push incremental mirror */
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < hex.len() / 2
        invariant
            0 <= i <= hex@.len() / 2,
            s == hex@,
            s.len() % 2 == 0,
            forall|j: int| 0 <= j < i ==> valid_pair(s, j),
            v@.len() == i as int,
            forall|j: int| 0 <= j < i ==> v@[j] == merge_nibbles(s[2 * j], s[2 * j + 1]),
        decreases hex.len() / 2 - i
    {
        assert(i < hex@.len() / 2);
        assert(2 * i + 2 <= hex.len());
        assert((2 * i + 2) as int == 2 * (i as int) + 2);
        let pair = &hex[2 * i..2 * i + 2];
        assert(pair@ == s.subrange(2 * i as int, 2 * i as int + 2));
        match val(pair, 2 * i) {
            Result::Ok(b) => {
                v.push(b);
                i += 1;
            }
            Result::Err(e) => {
                proof {
                    lip_exact(s, i as int);
                    assert(e == decode_err_variant(s));
                }
                return Result::Err(e);
            }
        }
    }
    proof {
        assert(i == hex@.len() / 2);
        assert forall|j: int| 0 <= j < i implies v@[j] == merge_nibbles(s[2 * j], s[2 * j + 1]) by {}
        lip_none(s);
        assert(first_invalid_pair(s) == -1);
        assert forall|j: int| 0 <= j < v@.len() implies v@[j] == decoded_seq(s)[j] by {
            assert forall|j: int| 0 <= j < v@.len() implies v@[j] == decoded_seq(s)[j] by {
                assert(decoded_seq(s)[j] == merge_nibbles(s[2 * j], s[2 * j + 1]));
            }
        }
    }
    Result::Ok(v)
}

/// Origin: lib.rs:303-306 `decode` (generic T monomorphized to &[u8]; the
/// FromHex::from_hex delegation -> isomorphic to vec_from_hex)
/// Upstream doc (lib.rs:287-302):
///   Decodes a hex string into raw bytes.
///   Both, upper and lower case characters are valid in the input string and can
///   even be mixed (e.g. `f9b4ca`, `F9B4CA` and `f9B4Ca` are all valid strings).
pub exec fn decode(data: &[u8]) -> (r: Result<Vec<u8>, FromHexError>)
    ensures
        data@.len() % 2 != 0 ==> r == Result::Err(FromHexError::OddLength),
        data@.len() % 2 == 0 && first_invalid_pair(data@) == -1 ==> r.is_ok()
            && r.get_Ok_0()@ == decoded_seq(data@),
        data@.len() % 2 == 0 && first_invalid_pair(data@) != -1 ==> r == Result::Err(
            decode_err_variant(data@),
        ),
{
    /* Origin Rust: FromHex::from_hex(data) */
    vec_from_hex(data)
}

/// Origin: lib.rs:235-244 `impl<const N: usize> FromHex for [u8; N]`
/// (the array->slice coercion of `&mut out as &mut [u8]` is bridged through
/// the vstd::array View;
///  the returned array content is expressed with array_view (Seq))
/// Upstream doc (lib.rs:161-165):
///   Creates an instance of type `Self` from the given hex string, or fails
///   with a custom error type.
///   Both, upper and lower case characters are valid and can even be
///   mixed (e.g. `f9b4ca`, `F9B4CA` and `f9B4Ca` are all valid strings).
pub exec fn from_hex_array<const N: usize>(hex: &[u8]) -> (r: Result<[u8; N], FromHexError>)
    ensures
        hex@.len() % 2 != 0 ==> r == Result::Err(FromHexError::OddLength),
        hex@.len() % 2 == 0 && hex@.len() / 2 != N as int ==> r == Result::Err(
            FromHexError::InvalidStringLength,
        ),
        /* SPEC-DOC MISMATCH (rust-hex#99): the upstream variant doc
           promises "the hex string's length * 2 has to match the
           container's length", which is unprovable (the length direction
           is reversed); this clause keeps the implementation-faithful
           form hex_len == 2 * N. */
        hex@.len() % 2 == 0 && hex@.len() / 2 == N as int && first_invalid_pair(hex@) == -1 ==> r
            .is_ok()
            && (r.get_Ok_0())@ == decoded_seq(hex@),
        hex@.len() % 2 == 0 && hex@.len() / 2 == N as int && first_invalid_pair(hex@) != -1 ==> r
            == Result::Err(decode_err_variant(hex@)),
{
    /* Origin Rust: let mut out = [0_u8; N];
       decode_to_slice(hex, &mut out as &mut [u8])?;
       Ok(out) */
    let mut out = [0_u8; N];
    let ghost s = hex@;
    let mid: &mut [u8] = &mut out;
    let res = decode_to_slice(hex, mid);
    match res {
        Result::Err(e) => {
            proof {
                if s.len() % 2 != 0 {
                    assert(e == FromHexError::OddLength);
                } else if s.len() / 2 != N as int {
                    assert(e == FromHexError::InvalidStringLength);
                } else {
                    assert(first_invalid_pair(s) != -1);
                    assert(e == decode_err_variant(s));
                }
            }
            Result::Err(e)
        }
        Result::Ok(()) => {
            proof {
                // Ok exit => (reversed from decode_to_slice's error-side
                // contract) the lengths match
                // and first_invalid == -1; hence mid@ == decoded_seq(s)
                assert(s.len() % 2 == 0);
                assert(s.len() / 2 == N as int);
                if first_invalid_pair(s) != -1 {
                    // in that case decode_to_slice's error-side contract forces
                    // res to be Err, contradicting the Ok
                    assert(res == Result::Err(decode_err_variant(s)));
                    assert(false);
                } else {
                    assert(mid@ == decoded_seq(s)); // length match + fi==-1
                    // => final == decoded
                }
                // the array View agrees with the slice view inside it (the
                // vstd::array broadcast axiom)
                assert(out@ == mid@);
            }
            Result::Ok(out)
        }
    }
}

/* ============================================================
 * encode / encode_upper (alloc path monomorphized mirror)
 * ============================================================ */

/// Origin: lib.rs:259-266 `encode`
/// (vec![0; len*2] + encode_to_slice().unwrap() + String::from_utf8().unwrap()
///  -> rewritten as the push incremental mirror returning a Vec<u8> byte string;
///  the never-firing preconditions of the two unwraps:
///  (1) the lengths always match (the encode_to_slice contract); (2) all
///  output bytes are ASCII => valid UTF-8 (the ascii_seq_valid_utf8 lemma;
///  "std maps valid to Ok" recorded in the assumption ledger))
/// Upstream doc (lib.rs:246-258):
///   Encodes `data` as hex string using lowercase characters.
///   Lowercase characters are used (e.g. `f9b4ca`). The resulting string's
///   length is always even, each byte in `data` is always encoded using two hex
///   digits. Thus, the resulting string contains exactly twice as many bytes as
///   the input data.
pub exec fn encode(data: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == encode_seq(data@, false),
        v@.len() == 2 * data@.len(),
{
    let ghost s = data@;
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < data.len()
        invariant
            0 <= i <= data.len(),
            s == data@,
            v@ == encode_seq(s.subrange(0, i as int), false),
            v@.len() == 2 * i as int,
        decreases data.len() - i
    {
        let (high, low) = byte2hex(data[i], false);
        v.push(high);
        v.push(low);
        proof {
            encode_seq_prefix(s, i as int + 1, false);
            // v@ becomes length 2i+2 via the two pushes; the seam to the
            // encode_seq prefix lemma
        }
        i += 1;
    }
    proof {
        assert(data@.subrange(0, data@.len() as int) =~= data@);
        let whole = encode_seq(s.subrange(0, s.len() as int), false);
        assert(whole =~= encode_seq(s, false));
    }
    v
}

/// Origin: lib.rs:278-285 `encode_upper`
/// Upstream doc (lib.rs:268-277):
///   Encodes `data` as hex string using uppercase characters.
///   Apart from the characters' casing, this works exactly like `encode()`.
pub exec fn encode_upper(data: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == encode_seq(data@, true),
        v@.len() == 2 * data@.len(),
{
    let ghost s = data@;
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < data.len()
        invariant
            0 <= i <= data.len(),
            s == data@,
            v@ == encode_seq(s.subrange(0, i as int), true),
            v@.len() == 2 * i as int,
        decreases data.len() - i
    {
        let (high, low) = byte2hex(data[i], true);
        v.push(high);
        v.push(low);
        proof {
            encode_seq_prefix(s, i as int + 1, true);
        }
        i += 1;
    }
    proof {
        assert(data@.subrange(0, data@.len() as int) =~= data@);
        let whole = encode_seq(s.subrange(0, s.len() as int), true);
        assert(whole =~= encode_seq(s, true));
    }
    v
}

/* ============================================================
 * Contract-level witness theorems (fuzz-style universal properties; the
 * panic-free preconditions on the String side & encode side -- the two unwraps
 * inside encode never fire on the whole input domain)
 * ============================================================ */

/// encode_to_slice is always Ok when the lengths match (never-firing
/// precondition (1) of the unwrap inside the upstream encode; exec witness
/// form: any call whose preconditions are satisfied executes this guarantee)
pub exec fn theorem_encode_to_slice_ok_on_match(input: &[u8], output: &mut [u8]) -> (b: bool)
    requires
        input@.len() * 2 == output@.len(),
    ensures b
{
    let r = encode_to_slice(input, output);
    r.is_ok()
}

/// encode's output is all ASCII and hence valid UTF-8 (never-firing
/// precondition (2) of the upstream String::from_utf8 unwrap;
/// "std side: valid_utf8 -> Ok" recorded in the assumption ledger)
pub exec fn theorem_encode_valid_utf8(data: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == encode_seq(data@, false),
        v@.len() == 2 * data@.len(),
        forall|j: int| 0 <= j < v@.len() ==> v@[j] < 0x80,
        valid_utf8(v@),
{
    let v = encode(data);
    proof {
        ascii_seq_valid_utf8(v@);
        assert forall|j: int| 0 <= j < v@.len() implies v@[j] < 0x80 by {
            assert(v@[j] == encode_seq(data@, false)[j]);
            let nib = if j % 2 == 0 { data@ [j / 2] / 16 } else { data@ [j / 2] % 16 };
            assert(nib < 16);
            assert(v@[j] == hex_char(nib, false));
            if nib < 10 {
                assert(v@[j] == 0x30 + nib);
            } else {
                assert(v@[j] == 0x61 + (nib - 10));
            }
        }
    }
    v
}

// ===========================================================================
// Proof lemmas (moved to the file end; only the order changed)
// ===========================================================================

/// If the first i pairs are all valid and pair i is invalid => first_invalid
/// is exactly i
/// (this is the provable core of the obligation "return at the first invalid
/// one, the return value carrying its character and position")
pub proof fn lip_exact(s: Seq<u8>, i: int)
    requires
        s.len() % 2 == 0,
        0 <= i < s.len() / 2,
        forall|j: int| 0 <= j < i ==> valid_pair(s, j),
        !valid_pair(s, i),
    ensures first_invalid_pair(s) == i
    decreases s.len()
{
    if i == 0 {
        assert(first_invalid_pair(s) == 0);
    } else {
        assert(valid_pair(s, 0));
        let rest = s.subrange(2, s.len() as int);
        // pair j of rest corresponds to pair j+1 of s (prove first, then recurse)
        assert forall|j: int| 0 <= j < i - 1 implies valid_pair(rest, j) by {
            assert(rest[2 * j] == s[2 * j + 2]);
            assert(rest[2 * j + 1] == s[2 * j + 3]);
            assert(0 <= j + 1 < i);
            assert(valid_pair(s, j + 1));
            assert(valid_pair(rest, j));
        }
        assert(!valid_pair(rest, i - 1)) by {
            assert(rest[2 * (i - 1)] == s[2 * i]);
            assert(rest[2 * (i - 1) + 1] == s[2 * i + 1]);
        }
        lip_exact(rest, i - 1);
        assert(first_invalid_pair(rest) == i - 1);
        assert(first_invalid_pair(rest) >= 0);
        assert(first_invalid_pair(s) == 1 + first_invalid_pair(rest));
    }
}

/// All pairs valid => first_invalid == -1
pub proof fn lip_none(s: Seq<u8>)
    requires
        s.len() % 2 == 0,
        forall|j: int| 0 <= j < s.len() / 2 ==> valid_pair(s, j),
    ensures first_invalid_pair(s) == -1
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        assert(valid_pair(s, 0));
        let rest = s.subrange(2, s.len() as int);
        // pair j of rest corresponds to pair j+1 of s (prove first, then recurse)
        assert forall|j: int| 0 <= j < s.len() / 2 - 1 implies valid_pair(rest, j) by {
            assert(rest[2 * j] == s[2 * j + 2]);
            assert(rest[2 * j + 1] == s[2 * j + 3]);
            assert(0 <= j + 1 < s.len() / 2);
            assert(valid_pair(s, j + 1));
            assert(valid_pair(rest, j));
        }
        lip_none(rest);
        assert(first_invalid_pair(rest) == -1);
        assert(first_invalid_pair(s) == -1);
    }
}

/// Prefix lemma of encode_seq (the seam between the Vec push construction and
/// the Seq::new model)
pub proof fn encode_seq_prefix(s: Seq<u8>, i: int, upper: bool)
    requires 0 <= i <= s.len()
    ensures encode_seq(s.subrange(0, i), upper) == encode_seq(s, upper).subrange(0, 2 * i)
{
    assert(encode_seq(s.subrange(0, i), upper).len() == 2 * i);
    assert(encode_seq(s, upper).subrange(0, 2 * i).len() == 2 * i);
    assert forall|j: int| 0 <= j < 2 * i implies
        encode_seq(s.subrange(0, i), upper)[j]
            == encode_seq(s, upper).subrange(0, 2 * i)[j] by {
        let p = s.subrange(0, i);
        if j % 2 == 0 {
            assert(p[j / 2] == s[j / 2]);
            assert(encode_seq(p, upper)[j] == hex_char(p[j / 2] / 16, upper));
            assert(encode_seq(s, upper).subrange(0, 2 * i)[j] == hex_char(s[j / 2] / 16, upper));
        } else {
            assert(p[j / 2] == s[j / 2]);
            assert(encode_seq(p, upper)[j] == hex_char(p[j / 2] % 16, upper));
            assert(encode_seq(s, upper).subrange(0, 2 * i)[j] == hex_char(s[j / 2] % 16, upper));
        }
    }
}

/// An ASCII byte sequence is valid UTF-8 (the semantic precondition of the
/// encode-side String::from_utf8 unwrap; "std never judges valid_utf8 as Err"
/// enters the assumption ledger as a std-semantics entry)
pub proof fn ascii_seq_valid_utf8(b: Seq<u8>)
    requires forall|j: int| 0 <= j < b.len() ==> b[j] < 0x80
    ensures valid_utf8(b)
{
    // ascii premise -> every byte is a 1-byte leading byte (the vstd utf8 model)
    assert forall|i: int| 0 <= i < b.len() implies is_leading_byte_width_1(b[i]) by {
        assert(b[i] < 0x80);
    }
    // empty-prefix validity -> extend to the full length with the official vstd
    // ascii-block-extension lemma
    assert(partial_valid_utf8(b, 0)) by {
        assert(b.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(valid_utf8(Seq::<u8>::empty()));
    }
    partial_valid_utf8_extend_ascii_block(b, 0, b.len() as int);
    assert(partial_valid_utf8(b, b.len() as int));
    assert(b.subrange(0, b.len() as int) =~= b);
    assert(valid_utf8(b));
}

} // verus!

