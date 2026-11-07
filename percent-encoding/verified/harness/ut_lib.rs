//! harness: inline-UT witnesses for src/lib.rs
//! Mirrors the 14 inline `#[test]`s of upstream lib.rs:367-481 (U1-U14; numbering per
//! out/harness-inventory.md).
//! Reference-style organization: `#[path]` includes verified/src/lib.rs (which contains ascii_set),
//! without copying its spec; the verification fact source stays single in src.
//! U4 Display / U5 Cow<str> / U11 Cow<[u8]> / U12 Utf8Error fields /
//! U13 U14 from_utf8(_lossy) depend on the fmt/Cow/std-str layer, outside the verus surface;
//! the other 9 items are exec+assert-theorem witnesses.
fn main() {}

#[path = "../src/lib.rs"]
mod percent_encoding;

use percent_encoding::*;

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ---------- U1 percent_encode_byte (lib.rs:372-378) ----------
 * for all i in 0..=0xFF: percent_encode_byte(i) == alloc::format!("%{:02X}", i)
 * (the UT expectation shape = '%' + two uppercase hex digits; the mirror contract enc_byte_spec has the same shape)
 * A full 256-entry exec witness loop. */
exec fn ut_percent_encode_byte_all()
{
    let mut i: u8 = 0;
    while (i as u16) < 255
        invariant
            0 <= (i as int) <= 255,
        decreases
            256 - (i as int)
    {
        let t = percent_encode_byte(i);
        assert(t@ == enc_byte_spec(i));
        // Per-digit shape: '%', high digit, low digit (the mirror assert of "%{:02X}")
        assert(t[0] == 0x25u8);
        let hi = (i / 16) as u8;
        let lo = (i % 16) as u8;
        assert(hex_val(t[1] as int) == hi as int);
        assert(hex_val(t[2] as int) == lo as int);
        assert(t[1] < 0x80u8);
        assert(t[2] < 0x80u8);
        i += 1;
    }
    // The 256th entry i == 0xFF
    let t = percent_encode_byte(i);
    assert(t@ == enc_byte_spec(i));
    assert(hex_val(t[1] as int) == 15);
    assert(hex_val(t[2] as int) == 15);
}

/* ---------- U2 percent_encode_accepts_ascii_set_ref (lib.rs:380-384) ----------
 * percent_encode(b"foo bar?", &AsciiSet::EMPTY).collect() == "foo bar?"
 * (EMPTY has no ASCII members -> only non-ASCII bytes are encoded, ASCII passes through) */
exec fn ut_percent_encode_empty_set()
{
    let input: [u8; 8] = [0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f];
    let s: &[u8] = &input;
    let set: AsciiSet = AsciiSet::EMPTY;
    let v = enc_all_bytes(s, &set);
    assert(AsciiSet::EMPTY.mask[0] == 0u32);
    assert(AsciiSet::EMPTY.mask[1] == 0u32);
    assert(AsciiSet::EMPTY.mask[2] == 0u32);
    assert(AsciiSet::EMPTY.mask[3] == 0u32);
    proof {
        assert(s@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
        reveal_with_fuel(enc_span, 9);
        reveal(enc_byte_spec);
        reveal(hex_char_upper);
        reveal(should_encode);
        reveal(bit_at);
    }
    assert(set.mask@ == AsciiSet::EMPTY.mask@);
    assert(AsciiSet::EMPTY.mask@ == seq![0u32, 0u32, 0u32, 0u32]);
    proof {
        lemma_empty_set_flat(set.mask@);
    }
    // Expect "foo bar?"
    assert(v@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
}

/* ---------- U6 utf8_percent_encode_accepts_ascii_set_ref (lib.rs:407-411) ---------- */
exec fn ut_utf8_percent_encode_empty_set()
{
    /* Origin Rust: super::utf8_percent_encode("foo bar?", &AsciiSet::EMPTY) */
    let input: [u8; 8] = [0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f];
    let s: &[u8] = &input;
    let set: AsciiSet = AsciiSet::EMPTY;
    let v = utf8_percent_encode_bytes(s, &set);
    assert(AsciiSet::EMPTY.mask[0] == 0u32);
    assert(AsciiSet::EMPTY.mask[1] == 0u32);
    assert(AsciiSet::EMPTY.mask[2] == 0u32);
    assert(AsciiSet::EMPTY.mask[3] == 0u32);
    proof {
        assert(s@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
        reveal_with_fuel(enc_span, 9);
        reveal(enc_byte_spec);
        reveal(hex_char_upper);
        reveal(should_encode);
        reveal(bit_at);
        assert(set.mask@ == AsciiSet::EMPTY.mask@);
        assert(AsciiSet::EMPTY.mask@ == seq![0u32, 0u32, 0u32, 0u32]);
        lemma_empty_set_flat(set.mask@);
    }
    assert(v@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
}

/* ---------- U3 percent_encode_collect (lib.rs:386-393) ----------
 * 1) percent_encode(b"foo bar?", NON_ALPHANUMERIC) == "foo%20bar%3F"
 * 2) percent_encode(b"\x00..\x03", CONTROLS) == "%00%01%02%03"
 * (NON_ALPHANUMERIC is built with the exec non_alphanumeric(); the doc contract is already in the contract face) */
exec fn ut_percent_encode_collect()
{
    // Case 1
    let input: [u8; 8] = [0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f];
    let s: &[u8] = &input;
    let set = non_alphanumeric();
    let v = enc_all_bytes(s, &set);
    proof {
        assert(s@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
        reveal_with_fuel(enc_span, 9);
        reveal(enc_byte_spec);
        reveal(hex_char_upper);
        reveal(should_encode);
        reveal(bit_at);
        lemma_hex_val_range(0x32);
        lemma_hex_val_range(0x36);
        lemma_controls();
    }
    // "foo%20bar%3F"
    
    // per-byte membership semantics: ' ' and '?' are non-alnum -> encoded; f/o/b/a/r are alnum -> passthrough
    assert(!is_alnum(0x20));
    assert(is_alnum(0x66));
    assert(is_alnum(0x6f));
    assert(is_alnum(0x62));
    assert(is_alnum(0x61));
    assert(is_alnum(0x72));
    assert(!is_alnum(0x3f));
    assert(v@ == seq![0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33, 0x46]);

    // Case 2: CONTROLS encodes \x00..\x03
    let input2: [u8; 4] = [0x00, 0x01, 0x02, 0x03];
    let s2: &[u8] = &input2;
    let v2 = enc_all_bytes(s2, &CONTROLS);
    proof {
        assert(s2@ == seq![0x00, 0x01, 0x02, 0x03]);
        reveal_with_fuel(enc_span, 5);
        reveal(enc_byte_spec);
        reveal(hex_char_upper);
        reveal(bit_at);
        lemma_controls();
    }
    assert(v2@ == seq![
        0x25, 0x30, 0x30, 0x25, 0x30, 0x31, 0x25, 0x30, 0x32, 0x25, 0x30, 0x33,
    ]);
}

/* ---------- U7 utf8_percent_encode (lib.rs:413-419) ----------
 * utf8_percent_encode(b, S) == percent_encode(b.as_bytes(), S):
 * an equivalence witness of the one-line delegation. */
exec fn ut_utf8_percent_encode_is_percent_encode()
{
    let input: [u8; 8] = [0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f];
    let s: &[u8] = &input;
    let set = non_alphanumeric();
    let v1 = utf8_percent_encode_bytes(s, &set);
    let v2 = enc_all_bytes(s, &set);
    assert(v1@ == v2@);
}

/* ---------- U8/U9 percent_decode(_str) (lib.rs:421-429, 431-439) ----------
 * b"foo%20bar%3f".decode_utf8() == "foo bar?":
 * the byte level = b"foo%20bar%3f" decoded -> "foo bar?" (the str layer of decode_utf8
 * is outside the verus surface; its content contract (result bytes == "foo bar?") is
 * witnessed here, also covering the lowercase-acceptance face of the mixed-case %3f). */
exec fn ut_percent_decode()
{
    let input: [u8; 11] = [
        0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33,
    ];
    let s: &[u8] = &input;
    let v = dec_all_bytes(s);
    proof {
        assert(s@ == seq![0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33]);
        reveal_with_fuel(dec_span, 12);
    }
    // Segmented intermediate values (%3 missing one digit -> '%' and '3' each stay single-byte verbatim output)
    assert(dec_span(s@, 9) == seq![0x25, 0x33]);
    assert(dec_span(s@, 3) == seq![0x20, 0x62, 0x61, 0x72, 0x25, 0x33]);
    assert(dec_span(s@, 0) == seq![0x66, 0x6f, 0x6f] + dec_span(s@, 3));
    // "foo bar%3" (9 bytes)
    assert(v@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x25, 0x33]);
}

exec fn ut_percent_decode_full()
{
    // The full "foo%20bar%3f" (12 bytes) -> "foo bar?" (the acceptance face of lowercase f)
    let input2: [u8; 12] = [
        0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33, 0x66,
    ];
    let s2: &[u8] = &input2;
    let v2 = dec_all_bytes(s2);
    proof {
        assert(s2@ == seq![
            0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33, 0x66,
        ]);
        reveal_with_fuel(dec_span, 12);
        assert(hex_val(0x66) == 15);
        assert(hex_val(0x33) == 3);
        assert(hex_val(0x32) == 2);
    }
    assert(v2@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
}

/* ---------- U10 percent_decode_collect (lib.rs:441-445) ---------- */
exec fn ut_percent_decode_collect()
{
    /* Origin Rust: percent_decode(b"foo%20bar%3f").collect::<Vec<u8>>() */
    let input2: [u8; 12] = [
        0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33, 0x66,
    ];
    let s2: &[u8] = &input2;
    let v2 = dec_all_bytes(s2);
    proof {
        assert(s2@ == seq![
            0x66, 0x6f, 0x6f, 0x25, 0x32, 0x30, 0x62, 0x61, 0x72, 0x25, 0x33, 0x66,
        ]);
        reveal_with_fuel(dec_span, 12);
        reveal(hex_val);
    }
    assert(v2@ == seq![0x66, 0x6f, 0x6f, 0x20, 0x62, 0x61, 0x72, 0x3f]);
}

/* ---------- U4/U5/U11 blocked (Display/Cow): semantic-equivalence witnesses ----------
 * Display / Cow::from output == collect output (the semantics of lib.rs:184-209),
 * the fmt/Cow face is outside the verus surface; this only witnesses the collect content (same UTs as above). */


// =========================================================================
// Proof lemma -- the standalone proof fn lives at the end of the file so
// the UT witnesses read directly; the signature and contract are untouched.
// measured: all five verification panels identical before and after the move.
/// Membership face of EMPTY: under an all-zero mask everything in 0..128 is treated as
/// a non-member (!should_encode). The witness asserts of U2/U6 go through it
/// (bypassing the const array_view interpretation pitfall).
proof fn lemma_empty_set_flat(m: Seq<u32>)
    requires
        m == seq![0u32, 0u32, 0u32, 0u32],
    ensures
        forall|k: int| 0 <= k < 128 ==> !should_encode(m, k),
{
    assert forall|k: int| 0 <= k < 128 implies !should_encode(m, k) by {
        let c = m[k / 32];
        assert(c == 0u32);
        let p = (k % 32) as u32;
        assert(p < 32u32);
        assert(1u32 << (k % 32) == 1u32 << p);
        assert(c & (1u32 << p) == 0u32) by (bit_vector)
            requires
                p < 32u32,
                c == 0u32,
        ;
    }
}


}
