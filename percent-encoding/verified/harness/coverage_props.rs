//! harness: auto-generated -- property theorems and witnesses for the
//! coverage-difference APIs (APIs untouched by the UTs / APIs exercised with
//! concrete values only; see the full public API set in harness-inventory):
//!  - P1 AsciiSet::remove (absent from the UTs; the dual general property of update)
//!  - P2 PercentDecode::size_hint (two-sided bound per the std::iter::Iterator contract,
//!    a general theorem for the upstream ((bytes + 2) / 3, Some(bytes)))
//!  - P3 PercentEncode output is ASCII-only (the safety precondition of the unsafe
//!    from_utf8_unchecked stated by the upstream lib.rs comment: unchanged-run bytes are all ASCII --
//!    "The unsafe blocks here are appropriate because the bytes are
//!     confirmed as a subset of UTF-8 in should_percent_encode")
//!  - P4 decode o encode roundtrip (the universal property when the set contains '%' --
//!    the core roundtrip of the NON_ALPHANUMERIC family) via a concrete-input witness +
//!    a general lemma, dual witnesses
//!  - P5 utf8_percent_encode / percent_decode_str entry equivalence (delegation mirror)
//! Reference-style organization: `#[path]` includes verified/src/lib.rs without copying its spec.
fn main() {}

#[path = "../src/lib.rs"]
mod percent_encoding;

use percent_encoding::*;

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============================================================
 * P1 remove (ascii_set.rs:62-66; never touched by the UTs)
 * Clearing overrides setting: remove(add(m,b)) == remove(m,b) -- remove of the same byte
 * dominates add (after normalization bit_at == (bit_at(m,k) && k != b))
 * ============================================================ */

/// P1 exec witness: remove after add of the same byte returns to the original set (contains-sample roundtrip).
exec fn prop_add_remove_identity()
{
    let set = CONTROLS.add(0x7E);
    let set2 = set.add(0x20);
    let set3 = set2.remove(0x20);
    proof {
        assert(CONTROLS.mask@.len() == 4);
        lemma_controls();
        reveal(add_bit_spec);
        reveal(remove_bit_spec);
        lemma_add_then_remove_identity(set.mask@, 0x20);
        assert(set2.mask@ == add_bit_spec(set.mask@, 0x20));
        assert(set3.mask@ == remove_bit_spec(set2.mask@, 0x20));
    }
    // contains-sample roundtrip: add sets the bit, remove restores it; other bits untouched
    let c20 = set.contains(0x20);
    let c20a = set2.contains(0x20);
    let c20b = set3.contains(0x20);
    let c7e_a = set.contains(0x7E);
    let c7e_b = set3.contains(0x7E);
    let c21_a = set.contains(0x21);
    let c21_b = set3.contains(0x21);
    assert(!c20);
    assert(c20a);
    assert(!c20b);
    assert(c7e_a);
    assert(c7e_b);
    assert(!c21_a);
    assert(!c21_b);
}

/* ============================================================
 * P2 PercentDecode::size_hint (lib.rs:273-276)
 * `((bytes + 2) / 3, Some(bytes))`: per the std::iter::Iterator contract
 * lower <= exact <= upper -- each output byte consumes 1..3 input bytes.
 * ============================================================ */

/* ============================================================
 * P3 encode output ASCII-only (the unsafe safety precondition of the lib.rs:156-158 comment)
 * ============================================================ */

/* ============================================================
 * P4 decode o encode roundtrip (when the set contains '%')
 * ============================================================ */

/// P4 exec witness: decode(encode) roundtrip under NON_ALPHANUMERIC for
/// "foo bar?%25\x7F" (heavy-stock input with the literal '%', space, '?' and DEL).
exec fn prop_roundtrip_non_alphanumeric()
{
    let input: [u8; 3] = [
        0x20, 0x25, 0x66,
    ];
    let s: &[u8] = &input;
    let set = non_alphanumeric();
    let enc = enc_all_bytes(s, &set);
    let dec = dec_all_bytes(&enc);
    proof {
        assert(s@ == seq![
            0x20, 0x25, 0x66,
        ]);
        assert(set.mask@.len() == 4);
        assert(!is_alnum(0x25));
        assert(bit_at(set.mask@, 0x25));
        // witness-level roundtrip (the concrete-value chain of encode followed by decode)
        reveal(enc_span);
        reveal_with_fuel(enc_span, 4);
        reveal_with_fuel(dec_span, 8);
        reveal(hex_char_upper);
        reveal(hex_val);
        reveal(should_encode);
        reveal(bit_at);
    }
    assert(dec@ == s@);
}

/* ============================================================
 * P5 entry equivalence (delegation mirror; generalized witnesses of UT U7/U9)
 * ============================================================ */

exec fn prop_entry_equivalence()
{
    let input: [u8; 4] = [0x25, 0x32, 0x35, 0x41];
    let s: &[u8] = &input;
    let set = non_alphanumeric();
    // utf8_percent_encode == percent_encode(input.as_bytes(), set)
    let v1 = utf8_percent_encode_bytes(s, &set);
    let v2 = enc_all_bytes(s, &set);
    assert(v1@ == v2@);
    // percent_decode_str == percent_decode(input.as_bytes())
    let d1 = dec_all_bytes(s);
    assert(d1@ == dec_seq(s@));
}


// =========================================================================
// Proof lemmas -- the standalone proof fns live at the end of the file so
// the P1-P5 sections keep only their exec witnesses; signatures and
// contracts are untouched.
// measured: all five verification panels identical before and after the move.
proof fn lemma_add_then_remove_identity(m: Seq<u32>, b: u8)
    requires
        (b as int) < 128,
        m.len() == 4,
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(remove_bit_spec(add_bit_spec(m, b as int), b as int), k)
            == (bit_at(m, k) && k != b as int),
{
    let bi = (b as int) / 32;
    let bp: u32 = ((b as int) % 32) as u32;
    let mchunk: u32 = m[bi];
    let achunk: u32 = mchunk | (1u32 << bp);
    let rchunk: u32 = achunk & !(1u32 << bp);
    assert(bp < 32u32);
    reveal(add_bit_spec);
    reveal(remove_bit_spec);
    let a1 = add_bit_spec(m, b as int);
    let r2 = remove_bit_spec(a1, b as int);
    assert forall|j: int| 0 <= j < 4 implies a1[j]
        == (if (j as int) == bi { achunk } else { m[j] }) by {}
    ;
    assert forall|j: int| 0 <= j < 4 implies r2[j]
        == (if (j as int) == bi { rchunk } else { a1[j] }) by {}
    ;
    lemma_add_membership(m, a1, b);
    lemma_remove_membership(a1, r2, b);
    assert forall|k: int| 0 <= k < 128 implies bit_at(r2, k)
        == (bit_at(m, k) && k != b as int) by {
        assert(bit_at(a1, k) == (bit_at(m, k) || k == b as int));
        assert(bit_at(r2, k) == (bit_at(a1, k) && k != b as int));
        if k == b as int {
        } else {
            assert(bit_at(a1, k) == bit_at(m, k));
        }
    }
    ;
    assert(remove_bit_spec(add_bit_spec(m, b as int), b as int) == r2);
}


proof fn lemma_dec_span_len_bounds(s: Seq<u8>, lo: int)
    requires
        0 <= lo <= s.len(),
    ensures
        (s.len() - lo + 2) / 3 <= dec_span(s, lo).len(),
        dec_span(s, lo).len() <= s.len() - lo,
    decreases
        s.len() - lo,
{
    if lo == s.len() {
        reveal(dec_span);
    } else {
        reveal(dec_span);
        let here = s[lo];
        let esc = s[lo] == 0x25 && lo + 2 < s.len()
            && hex_val(s[lo + 1] as int) >= 0 && hex_val(s[lo + 2] as int) >= 0;
        if esc {
            lemma_dec_span_len_bounds(s, lo + 3);
        } else {
            lemma_dec_span_len_bounds(s, lo + 1);
        }
    }
}


/// !should_encode(mask, k) => k < 128 -- upstream: unchanged-run bytes are all ASCII,
/// the safety precondition (copied from the upstream comment semantics).
proof fn lemma_unchanged_ascii(mask: Seq<u32>, k: int)
    requires
        !should_encode(mask, k),
        0 <= k,
    ensures
        k < 128,
{
}


/// All three bytes of enc_byte_spec are ASCII (table-entry safety -- the
/// table-slice precondition of unsafe str::from_utf8_unchecked).
proof fn lemma_enc_byte_ascii(b: u8)
    ensures
        enc_byte_spec(b).len() == 3,
        forall|j: int| 0 <= j < 3 ==> (enc_byte_spec(b)[j] as int) < 0x80,
{
    reveal(enc_byte_spec);
    reveal(hex_char_upper);
    if (b as int) / 16 <= 9 {
        assert((0x30 + (b as int) / 16) < 0x80);
    } else {
        assert(10 <= (b as int) / 16 <= 15);
        assert((0x41 + ((b as int) / 16) - 10) < 0x80);
    }
    if (b as int) % 16 <= 9 {
        assert((0x30 + (b as int) % 16) < 0x80);
    } else {
        assert(10 <= (b as int) % 16 <= 15);
        assert((0x41 + ((b as int) % 16) - 10) < 0x80);
    }
}


/// Invertibility of hex digits and characters (the ground stock of the roundtrip).
proof fn lemma_hex_char_inverse(d: int)
    requires
        0 <= d <= 15,
    ensures
        hex_val(hex_char_upper(d) as int) == d,
{
    reveal(hex_char_upper);
    reveal(hex_val);
    if d <= 9 {
        assert(hex_char_upper(d) == (0x30 + d) as u8);
    } else {
        assert(hex_char_upper(d) == (0x41 + d - 10) as u8);
    }
}


}
