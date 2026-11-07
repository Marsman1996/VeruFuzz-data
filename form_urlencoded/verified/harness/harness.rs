//! form_urlencoded **harness zone** -- the auto-generated coverage harnesses
//! (H2/H3/H4, transcribed from the src section D block, obligation bodies verbatim).
//! Reference-style structure: `#[path = "../src/lib.rs"] mod formlib;` -- directly
//! references the src-side verified spec models (section A), the exec transcriptions
//! (section B) and the shared lemmas (section E), **duplicating no fact source
//! (this file only carries the UT assertion/property bodies; every referenced name
//! resolves through `use formlib::*`).
//! Minimal adjustments recorded (src semantics unchanged, each noted):
//!   - src/lib.rs's skip lemmas `parse_scan_skip` / `emit_pair_scan_skip` went
//!     private to `pub` (the H3 lemma/roundtrip proofs call them; relaxing the
//!     visibility changes no semantics);
//!   - the standalone driver `fn main() {}` at the src/lib.rs tail stays in place
//!     (after the mod import it is module-level, no clash with this file's root driver).
//!
//! Run: VERUS_Z3_PATH=<z3> <verus> database/form_urlencoded/verified/harness/harness.rs
//! Reading: apart from the F1 expected error pulled in by the integral re-verification
//! of the formlib module (the for_suffix_upstream panic! anchor in src/lib.rs),
//! everything else verifies.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod formlib;

use formlib::*;

verus! {

// ================= Section D migration block: the auto-generated coverage harnesses
// (moved verbatim from src/lib.rs section D; names point into the formlib module) =================
/// H2: the rustdoc embedded example (lib.rs:334-341, expected values transcribed byte
///      by byte).
/// Shape: UT exemplar -> exec + exact literal ensures. An obligation failing means
/// class 2 (doc inconsistent with the implementation).
/// Upstream doc (lib.rs:332-343):
///   If this serializer was constructed with a string, take and return that string.
///   Panics if called more than once.
pub exec fn doc_example_new_append_pair_finish() -> (result: Vec<u8>)
    ensures
        result@ ==
            seq![b'f', b'o', b'o', b'=',
                 b'b', b'a', b'r', b'+', b'%', 0x32, 0x36, b'+', b'b', b'a', b'z',
                 b'&',
                 b's', b'a', b'i', b's', b'o', b'n', b'=',
                 b'%', b'C', b'3', b'%', b'8', b'9', b't', b'%', b'C', b'3', b'%', b'A', b'9',
                 b'%', b'2', b'B', b'h', b'i', b'v', b'e', b'r'],
{
    // Origin Rust: Serializer::new(String::new())(lib.rs:336;
    //   new == for_suffix(target, 0), 0 <= len always => no panic-branch obligation)
    let mut s: Vec<u8> = Vec::new();
    assert(s@ == Seq::<u8>::empty());

    // Origin Rust: .append_pair("foo", "bar & baz")(lib.rs:337)
    let mut name1: Vec<u8> = Vec::new();
    name1.push(b'f'); name1.push(b'o'); name1.push(b'o');
    assert(name1@ == seq![b'f', b'o', b'o']);
    let mut value1: Vec<u8> = Vec::new();
    value1.push(b'b'); value1.push(b'a'); value1.push(b'r'); value1.push(b' ');
    value1.push(b'&'); value1.push(b' '); value1.push(b'b'); value1.push(b'a'); value1.push(b'z');
    assert(value1@ == seq![b'b', b'a', b'r', b' ', b'&', b' ', b'b', b'a', b'z']);

    proof { reveal_with_fuel(encode_len, 24); }
    assert(encoded(name1@) == seq![b'f', b'o', b'o']);
    assert(encoded(value1@) == seq![b'b', b'a', b'r', b'+', b'%', 0x32, 0x36, b'+', b'b', b'a', b'z']);

    append_pair_exec(&mut s, 0, &name1, &value1);
    assert(s@ == seq![b'f', b'o', b'o', b'=',
                      b'b', b'a', b'r', b'+', b'%', 0x32, 0x36, b'+', b'b', b'a', b'z']);

    // Origin Rust: .append_pair("saison", "Été+hiver")(lib.rs:338)
    let mut name2: Vec<u8> = Vec::new();
    name2.push(b's'); name2.push(b'a'); name2.push(b'i'); name2.push(b's');
    name2.push(b'o'); name2.push(b'n');
    assert(name2@ == seq![b's', b'a', b'i', b's', b'o', b'n']);
    // UTF-8 bytes of "Été+hiver": 0xC3 0x89 0x74 0xC3 0xA9 0x2B 0x68 0x69 0x76 0x65 0x72
    let mut value2: Vec<u8> = Vec::new();
    value2.push(0xC3); value2.push(0x89); value2.push(b't'); value2.push(0xC3); value2.push(0xA9);
    value2.push(0x2B); value2.push(b'h'); value2.push(b'i'); value2.push(b'v');
    value2.push(b'e'); value2.push(b'r');
    assert(value2@ == seq![0xC3, 0x89, b't', 0xC3, 0xA9, 0x2B, b'h', b'i', b'v', b'e', b'r']);

    assert(encoded(name2@) == seq![b's', b'a', b'i', b's', b'o', b'n']);
    assert(encoded(value2@) ==
        seq![b'%', b'C', b'3', b'%', b'8', b'9', b't', b'%', b'C', b'3', b'%', b'A', b'9',
             b'%', b'2', b'B', b'h', b'i', b'v', b'e', b'r']);

    append_pair_exec(&mut s, 0, &name2, &value2);
    assert(s@ ==
        seq![b'f', b'o', b'o', b'=',
             b'b', b'a', b'r', b'+', b'%', 0x32, 0x36, b'+', b'b', b'a', b'z',
             b'&',
             b's', b'a', b'i', b's', b'o', b'n', b'=',
             b'%', b'C', b'3', b'%', b'8', b'9', b't', b'%', b'C', b'3', b'%', b'A', b'9',
             b'%', b'2', b'B', b'h', b'i', b'v', b'e', b'r']);
    // Origin Rust: .finish() (lib.rs:339) -- under the this-target model, target is s itself
    s
}

/// H4: separator semantics + append_key_only (the "append_separator_only" of the task
/// brief does not exist in the pin source; the real counterparts are the public
/// append_key_only (lib.rs:269) and the private append_separator_if_needed (lib.rs:352).
/// Exemplar: the url/tests/unit.rs:452-459 external UT (transcribed byte by byte).
pub exec fn url_ut_test_form_serialize_example() -> (result: Vec<u8>)
    ensures
        result@ ==
            seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
                 b'&', b'b', b'a', b'r', b'=',
                 b'&', b'f', b'o', b'o', b'=', b'%', b'2', b'3',
                 b'&', b'j', b's', b'o', b'n'],
{
    let mut s: Vec<u8> = Vec::new();
    let mut nfoo: Vec<u8> = Vec::new();
    nfoo.push(b'f'); nfoo.push(b'o'); nfoo.push(b'o');
    let mut nbar: Vec<u8> = Vec::new();
    nbar.push(b'b'); nbar.push(b'a'); nbar.push(b'r');
    let mut vea: Vec<u8> = Vec::new();     // "é&" (UTF-8 bytes below)
    vea.push(0xC3); vea.push(0xA9); vea.push(0x26);
    let vempty: Vec<u8> = Vec::new();      // ""
    let mut vhash: Vec<u8> = Vec::new();   // "#"
    vhash.push(b'#');
    let mut kjson: Vec<u8> = Vec::new();   // "json"
    kjson.push(b'j'); kjson.push(b's'); kjson.push(b'o'); kjson.push(b'n');

    proof { reveal_with_fuel(encode_len, 24); }
    assert(vea@ == seq![0xC3, 0xA9, 0x26]);
    assert(encoded(vea@) == seq![b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6']);
    assert(encoded(nfoo@) == seq![b'f', b'o', b'o']);
    assert(nbar@ == seq![b'b', b'a', b'r']);
    assert(encoded(nbar@) == seq![b'b', b'a', b'r']);
    assert(vempty@ == Seq::<u8>::empty());
    assert(encoded(vempty@) == Seq::<u8>::empty());
    assert(encoded(vhash@) == seq![b'%', 0x32, 0x33]);
    assert(encoded(kjson@) == seq![b'j', b's', b'o', b'n']);

    // ---- append_pair("foo", "é&"): empty target => no separator ----
    append_pair_exec(&mut s, 0, &nfoo, &vea);
    assert(s@ == seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6']);
    // ---- append_pair("foo", ""): non-empty => separator appended; explicit
    //      empty-value concat bridge ----
    proof {
        let x2 = s@ + seq![0x26u8] + encoded(nbar@) + seq![0x3Du8];
        assert(x2 ==
            seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
                 b'&', b'b', b'a', b'r', b'=']);
        assert(x2 + encoded(vempty@) =~= x2);
        assert(x2 + encoded(vempty@) == x2);
    }
    append_pair_exec(&mut s, 0, &nbar, &vempty);
    assert(s@ ==
        seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
             b'&', b'b', b'a', b'r', b'=']);
    // ---- append_pair("foo", "#") ----
    proof {
        let x3 = s@ + seq![0x26u8] + encoded(nfoo@) + seq![0x3Du8] + encoded(vhash@);
        assert(x3 ==
            seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
                 b'&', b'b', b'a', b'r', b'=', b'&', b'f', b'o', b'o', b'=', b'%', b'2', b'3']);
    }
    append_pair_exec(&mut s, 0, &nfoo, &vhash);
    assert(s@ ==
        seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
             b'&', b'b', b'a', b'r', b'=', b'&', b'f', b'o', b'o', b'=', b'%', b'2', b'3']);
    // ---- append_key_only("json") ----
    proof {
        let x4 = s@ + seq![0x26u8] + encoded(kjson@);
        assert(x4 ==
            seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
                 b'&', b'b', b'a', b'r', b'=', b'&', b'f', b'o', b'o', b'=', b'%', b'2', b'3',
                 b'&', b'j', b's', b'o', b'n']);
    }
    append_key_only_exec(&mut s, 0, &kjson);
    assert(s@ ==
        seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6',
             b'&', b'b', b'a', b'r', b'=', b'&', b'f', b'o', b'o', b'=', b'%', b'2', b'3',
             b'&', b'j', b's', b'o', b'n']);
    s
}


/// H3: the rustdoc example (lib.rs:36-37): `%23first=%25try%25` -> `[("#first", "%try%")]`
/// Shape: UT exemplar -> exec + exact literal ensures (verified through the full
/// section B parse transcription chain of formlib); the semantic computation is
/// given stepwise by parse_doc_example_lemma.
/// Upstream doc (lib.rs:31-37):
///   Convert a byte string in the `application/x-www-form-urlencoded` syntax
///   into a iterator of (name, value) pairs.
///   Use `parse(input.as_bytes())` to parse a `&str` string.
///   The names and values are percent-decoded. For instance, `%23first=%25try%25` will be
///   converted to `[("#first", "%try%")]`.
pub exec fn parse_doc_example_exec() -> (result: Vec<(Vec<u8>, Vec<u8>)>)
    ensures pairs_view(result@) ==
        seq![(seq![0x23, 0x66, 0x69, 0x72, 0x73, 0x74],   // "#first"
              seq![0x25, 0x74, 0x72, 0x79, 0x25])]        // "%try%"
{
    // %23first=%25try%25
    let mut input: Vec<u8> = Vec::new();
    input.push(b'%'); input.push(0x32); input.push(0x33); input.push(b'f'); input.push(b'i');
    input.push(b'r'); input.push(b's'); input.push(b't'); input.push(b'=');
    input.push(b'%'); input.push(0x32); input.push(0x35); input.push(b't'); input.push(b'r');
    input.push(b'y'); input.push(b'%'); input.push(0x32); input.push(0x35);
    assert(input@ == seq![0x25, 0x32, 0x33, 0x66, 0x69, 0x72, 0x73, 0x74, 0x3D,
                          0x25, 0x32, 0x35, 0x74, 0x72, 0x79, 0x25, 0x32, 0x35]);
    proof { parse_doc_example_lemma(); }
    let result = parse_all(&input);
    result
}



// ===========================================================================
// Proof lemmas (H4 separator universal, the H3 semantic-computation lemma, the
// H2/H3 roundtrip exemplar and the H3 byte-level inverse; moved to the end of
// the file so the exec transcriptions read directly -- only the order changed,
// signatures and contracts untouched)
// ===========================================================================
/// H4 universal: the separator property of append_separator_if_needed (any s/start):
/// all old bytes preserved; exactly one '&' appended only when the existing content
/// exceeds start.
proof fn separator_universal(s: Seq<u8>, start: int)
    requires 0 <= start <= s.len()
    ensures
        append_sep(s, start).len() as int == s.len() as int + (if s.len() as int > start { 1int } else { 0int }),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] append_sep(s, start)[k] == s[k],
{
}

/// H3 semantic computation lemma: `parse("%23first=%25try%25") == [("#first", "%try%")]`.
proof fn parse_doc_example_lemma()
    ensures parse_seq(seq![0x25, 0x32, 0x33, 0x66, 0x69, 0x72, 0x73, 0x74, 0x3D,
                           0x25, 0x32, 0x35, 0x74, 0x72, 0x79, 0x25, 0x32, 0x35])
        == seq![(seq![0x23, 0x66, 0x69, 0x72, 0x73, 0x74],
                 seq![0x25, 0x74, 0x72, 0x79, 0x25])]
{
    let inp = seq![0x25, 0x32, 0x33, 0x66, 0x69, 0x72, 0x73, 0x74, 0x3D,
                   0x25, 0x32, 0x35, 0x74, 0x72, 0x79, 0x25, 0x32, 0x35];
    reveal_with_fuel(decode, 16);
    reveal_with_fuel(parse_scan, 2);
    assert(inp.len() == 18);
    assert(forall|j: int| 0 <= j < 18 ==> #[trigger] inp[j] != 0x26);
    parse_scan_skip(inp, 0, 18, 0);
    // final segment: from == len, seg_start == 0
    assert(parse_scan(inp, 18, 0) == emit_seg(inp, 0, 18));
    assert(emit_seg(inp, 0, 18) == emit_pair_scan(inp, 0, 0, 18));
    // '=' at 8; no '=' within [0, 8)
    assert(inp[8] == 0x3D);
    assert(forall|j: int| 0 <= j < 8 ==> #[trigger] inp[j] != 0x3D);
    emit_pair_scan_skip(inp, 0, 0, 8, 18);
    reveal_with_fuel(emit_pair_scan, 2);
    let name8 = Seq::new(8 as nat, |j: int| inp[0 + j]);
    let val9 = Seq::new(9 as nat, |j: int| inp[9 + j]);
    assert(emit_pair_scan(inp, 0, 8, 18) == seq![(decode(name8, 0), decode(val9, 0))]);
    assert(name8 =~= seq![0x25, 0x32, 0x33, 0x66, 0x69, 0x72, 0x73, 0x74]);
    assert(val9 =~= seq![0x25, 0x32, 0x35, 0x74, 0x72, 0x79, 0x25, 0x32, 0x35]);
    assert(decode(name8, 0) == seq![0x23, 0x66, 0x69, 0x72, 0x73, 0x74]);
    assert(decode(val9, 0) == seq![0x25, 0x74, 0x72, 0x79, 0x25]);
}

/// H2/H3 roundtrip exemplar (url/tests/unit.rs:436-449, first pair taken):
/// serialize(("foo", "é&")) == "foo=%C3%A9%26", parse back to ("foo", "é&").
/// Spec-layer byte-wise machine decision (in steps, borrowing formlib::parse_scan_skip /
/// formlib::emit_pair_scan_skip to compress the SMT load).
proof fn roundtrip_single_pair()
    ensures parse_seq(serialize_pair(seq![b'f', b'o', b'o'], seq![0xC3, 0xA9, 0x26]))
        == seq![(seq![b'f', b'o', b'o'], seq![0xC3, 0xA9, 0x26])]
{
    let name = seq![b'f', b'o', b'o'];
    let value = seq![0xC3, 0xA9, 0x26]; // "é&"
    let out = serialize_pair(name, value);
    reveal_with_fuel(encode_len, 12);
    reveal_with_fuel(decode, 12);
    reveal_with_fuel(parse_scan, 2);
    reveal_with_fuel(emit_pair_scan, 2);
    let outl = seq![b'f', b'o', b'o', b'=', b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6'];
    assert(out == outl);
    assert(outl.len() == 13);
    assert(forall|j: int| 0 <= j < 13 ==> #[trigger] outl[j] != 0x26);
    parse_scan_skip(outl, 0, 13, 0);
    assert(parse_seq(outl) == parse_scan(outl, 13, 0));
    assert(parse_scan(outl, 13, 0) == emit_seg(outl, 0, 13));
    assert(emit_seg(outl, 0, 13) == emit_pair_scan(outl, 0, 0, 13));
    assert(outl[3] == 0x3D);
    assert(forall|j: int| 0 <= j < 3 ==> #[trigger] outl[j] != 0x3D);
    emit_pair_scan_skip(outl, 0, 0, 3, 13);
    reveal_with_fuel(emit_pair_scan, 2);
    let name3 = Seq::new(3 as nat, |j: int| outl[0 + j]);
    let val9 = Seq::new(9 as nat, |j: int| outl[4 + j]);
    assert(emit_pair_scan(outl, 0, 3, 13) == seq![(decode(name3, 0), decode(val9, 0))]);
    assert(name3 =~= name);
    assert(val9 =~= seq![b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6']);
    assert(decode(name, 0) == name);
    assert(decode(seq![b'%', b'C', b'3', b'%', b'A', b'9', b'%', b'2', b'6'], 0) == value);
    assert(parse_seq(out) == seq![(name, value)]);
}

/// H3 universal byte-level inverse (any u8 b): decode(encode(b)) == [b].
/// Every byte of the serializer output parses losslessly (encoding unambiguity).
proof fn decode_encode_inverse(b: u8)
    ensures decode(encode_byte(b), 0) == seq![b]
{
    reveal_with_fuel(decode, 4);
    if unchanged(b) {
        // an unchanged byte is neither '%' nor '+', passes through literally
        assert(b != 0x25);
        assert(b != 0x2B);
        assert(decode(seq![b], 1) == Seq::<u8>::empty());
        assert(decode(seq![b], 0) == seq![b]);
    } else if b == b' ' {
        assert(decode(seq![b'+'], 1) == Seq::<u8>::empty());
        assert(decode(seq![b'+'], 0) == seq![0x20u8]);
    } else {
        let hi = hex_digit(b as int / 16);
        let lo = hex_digit(b as int % 16);
        assert(hex_val(hi) == b as int / 16);
        assert(hex_val(lo) == b as int % 16);
        assert(hex_val(hi) >= 0);
        assert(hex_val(lo) >= 0);
        assert(decode(seq![b'%', hi, lo], 3) == Seq::<u8>::empty());
        assert(decode(seq![b'%', hi, lo], 0) == seq![b]);
    }
}
}

fn main() {}
