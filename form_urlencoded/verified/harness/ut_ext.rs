//! form_urlencoded **harness zone** -- coverage-delta batch (2026-11-02)
//! upstream UT exemplars (ut_ext series), transcribing the external tests of
//! url/tests/unit.rs that use the form_urlencoded generic / coverage-delta
//! APIs, expected values transcribed byte by byte.
//! Reference-style structure: `#[path = "../src/lib.rs"] mod formlib;`, referencing
//! the src-side fact sources only;
//! this file duplicates no src-side spec/lemma (the extend/clear join properties
//! live in coverage_props.rs; sibling files do not include each other, avoiding
//! double counting the formlib/F1 anchor),
//! the in-exemplar semantic computation is given stepwise in local proof blocks.
//!
//! Exemplar list (upstream basis):
//!   UT-1 url/tests/unit.rs:436-450 test_form_urlencoded -- extend_pairs (generic)
//!       + finish; expected "foo=%C3%A9%26&bar=&foo=%23" (byte by byte).
//!   UT-2 the roundtrip half of the same test -- parse(encode) == the original pair
//!       list.
//!   UT-3 the half-variant of url/tests/unit.rs:453-461 test_form_serialize was
//!       covered in the early batch (harness.rs H4); here we add the
//!       extend_keys_only (generic) exemplar (no direct upstream UT; property
//!       anchor coverage_props P5-3; the exemplar takes non-empty keys).
//!   UT-4 byte_serialize/size_hint exemplars (multi-run chunking + empty-string edge).
//! Run: verus database/form_urlencoded/verified/harness/ut_ext.rs
//! Reading: apart from the F1 expected error pulled in by the integral re-verification
//! of the formlib module (src/lib.rs), everything else verifies.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod formlib;

use formlib::*;

verus! {

// ================= UT-1/UT-2 input construction =================

/// "foo"
fn v_foo() -> (r: Vec<u8>)
    ensures r@ == seq![b'f', b'o', b'o']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'f');
    r.push(b'o');
    r.push(b'o');
    r
}

/// UTF-8 bytes of "é&"
fn v_e9_amp() -> (r: Vec<u8>)
    ensures r@ == seq![0xC3, 0xA9, 0x26]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(0xC3);
    r.push(0xA9);
    r.push(0x26);
    r
}

/// "bar"
fn v_bar() -> (r: Vec<u8>)
    ensures r@ == seq![b'b', b'a', b'r']
{
    let mut r: Vec<u8> = Vec::new();
    r.push(b'b');
    r.push(b'a');
    r.push(b'r');
    r
}

/// "#"
fn v_hash() -> (r: Vec<u8>)
    ensures r@ == seq![0x23]
{
    let mut r: Vec<u8> = Vec::new();
    r.push(0x23);
    r
}

/// Expected string: the serializer output "foo=%C3%A9%26&bar=&foo=%23"
pub open spec fn ut1_expected() -> Seq<u8> {
    seq![b'f', b'o', b'o', b'=',
         0x25, b'C', 0x33, 0x25, b'A', 0x39, 0x25, 0x32, 0x36,
         0x26,
         b'b', b'a', b'r', b'=',
         0x26,
         b'f', b'o', b'o', b'=',
         0x25, 0x32, 0x33]
}

// ================= UT-1 test_form_urlencoded serialization half (unit.rs:442-445) =================

/// url/tests/unit.rs:442-445:
/// `Serializer::new(String::new()).extend_pairs(pairs).finish()`
/// where pairs = [("foo", "é&"), ("bar", ""), ("foo", "#")]
/// == "foo=%C3%A9%26&bar=&foo=%23"
pub exec fn ut_extend_pairs_form_urlencoded() -> (r: Vec<u8>)
    ensures r@ == ut1_expected()
{
    let mut pairs: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    pairs.push((v_foo(), v_e9_amp()));
    pairs.push((v_bar(), Vec::new()));
    pairs.push((v_foo(), v_hash()));
    let mut st = SerializerByte::new(Vec::new());
    st.extend_pairs(&pairs);
    let r = st.finish();
    proof {
        // pairs_view bridge: the carrier pairs view == the literal pair table used by the lemma
        assert(pairs@.len() == 3);
        pairs_view_point(pairs@, 0);
        pairs_view_point(pairs@, 1);
        pairs_view_point(pairs@, 2);
        assert(pairs_view(pairs@).len() == 3);
        assert(pairs_view(pairs@) == seq![
            (seq![b'f', b'o', b'o'], seq![0xC3, 0xA9, 0x26]),
            (seq![b'b', b'a', b'r'], Seq::<u8>::empty()),
            (seq![b'f', b'o', b'o'], seq![0x23])]);
        ut_extend_pairs_lemma();
    }
    r
}

// ================= UT-2 test_form_urlencoded roundtrip half (unit.rs:446-449) =================

/// url/tests/unit.rs:446-449:
/// `form_urlencoded::parse(encoded.as_bytes()).collect::<Vec<_>>()` == the original pairs.
pub exec fn ut_parse_roundtrip_form_urlencoded() -> (r: Vec<(Vec<u8>, Vec<u8>)>)
    ensures pairs_view(r@)
        == seq![(seq![b'f', b'o', b'o'], seq![0xC3, 0xA9, 0x26]),
                (seq![b'b', b'a', b'r'], Seq::<u8>::empty()),
                (seq![b'f', b'o', b'o'], seq![0x23])]
{
    // "foo=%C3%A9%26&bar=&foo=%23" (26 bytes, the UT-1 serializer output)
    let mut input: Vec<u8> = Vec::new();
    input.push(b'f');
    input.push(b'o');
    input.push(b'o');
    input.push(b'=');
    input.push(0x25);
    input.push(b'C');
    input.push(0x33);
    input.push(0x25);
    input.push(b'A');
    input.push(0x39);
    input.push(0x25);
    input.push(0x32);
    input.push(0x36);
    input.push(0x26);
    input.push(b'b');
    input.push(b'a');
    input.push(b'r');
    input.push(b'=');
    input.push(0x26);
    input.push(b'f');
    input.push(b'o');
    input.push(b'o');
    input.push(b'=');
    input.push(0x25);
    input.push(0x32);
    input.push(0x33);
    assert(input@ == ut1_expected());
    assert(input@.len() == 26);
    proof { ut_parse_roundtrip_lemma(); }
    parse_all(&input)
}

// ================= UT-3: the extend_keys_only generic exemplar =================

/// extend_keys_only exemplar (no direct upstream UT; property anchor coverage_props P5-3,
/// exemplar domain takes non-empty keys per that precondition): keys = ["json", "a b"] =>
/// "json&a+b" (' ' -> '+'; both separator bases are non-empty).
pub exec fn ut_extend_keys_only_two() -> (r: Vec<u8>)
    ensures r@ == seq![b'j', b's', b'o', b'n', 0x26, b'a', b'+', b'b']
{
    let mut key1: Vec<u8> = Vec::new();
    key1.push(b'j');
    key1.push(b's');
    key1.push(b'o');
    key1.push(b'n');
    let mut key2: Vec<u8> = Vec::new();
    key2.push(b'a');
    key2.push(b' ');
    key2.push(b'b');
    let mut keys: Vec<Vec<u8>> = Vec::new();
    keys.push(key1);
    keys.push(key2);
    let mut st = SerializerByte::new(Vec::new());
    st.extend_keys_only(&keys);
    let r = st.finish();
    proof {
        // keys_view bridge: the carrier keys view == the literal table used by the lemma
        assert(keys@.len() == 2);
        keys_view_point(keys@, 0);
        keys_view_point(keys@, 1);
        assert(keys_view(keys@).len() == 2);
        assert(keys_view(keys@).index(0) == seq![b'j', b's', b'o', b'n']);
        assert(keys_view(keys@).index(1) == seq![b'a', 0x20, b'b']);
        assert(keys_view(keys@) == seq![seq![b'j', b's', b'o', b'n'], seq![b'a', 0x20, b'b']]);
        ut_extend_keys_only_lemma();
    }
    r
}

// ================= UT-4: byte_serialize/size_hint exemplars =================

/// Non-empty input: fresh position 0 => size_hint == (1, Some(len)) (multi-run chunked
/// input "ab c": 3 pieces -- run "ab", the ' ' single-byte piece, run "c").
pub exec fn ut_size_hint_nonempty() -> (hi: Option<usize>)
    ensures
        hi == Some(4),
        piece_count_all(seq![b'a', b'b', 0x20, b'c']) == 3,
{
    let mut bytes: Vec<u8> = Vec::new();
    bytes.push(b'a');
    bytes.push(b'b');
    bytes.push(0x20);
    bytes.push(b'c');
    assert(bytes@ == seq![b'a', b'b', 0x20, b'c']);
    proof {
        // piece computation: "ab" run, plus single-byte piece, "c" run <=> starts {0, 2, 3}
        reveal_with_fuel(piece_total, 5);
        assert(chunk_start(seq![b'a', b'b', 0x20, b'c'], 0));
        assert(!unchanged(0x20));
        assert(!chunk_start(seq![b'a', b'b', 0x20, b'c'], 1));
        assert(chunk_start(seq![b'a', b'b', 0x20, b'c'], 2));
        assert(chunk_start(seq![b'a', b'b', 0x20, b'c'], 3));
    }
    let (lo, hi) = byte_serialize_size_hint(&bytes, 0);
    assert(lo == 1);
    hi
}

/// Empty-input boundary: fresh position 0 == len => size_hint == (0, Some(0)) (0 pieces).
pub exec fn ut_size_hint_empty() -> (hi: Option<usize>)
    ensures
        hi == Some(0),
        piece_count_all(Seq::<u8>::empty()) == 0,
{
    let bytes: Vec<u8> = Vec::new();
    assert(bytes@ == Seq::<u8>::empty());
    proof { reveal_with_fuel(piece_total, 1); }
    let (lo, hi) = byte_serialize_size_hint(&bytes, 0);
    assert(lo == 0);
    hi
}


// ===========================================================================
// Proof lemmas (UT-1/UT-2/UT-3 semantic-computation lemmas and their fixed-point
// step helpers; moved to the end of the file so the exec exemplars read directly
// -- only the order changed, signatures and contracts untouched)
// ===========================================================================
/// Semantic computation: extend_pairs_spec({}, 0, [(foo,é&),(bar,{}),(foo,#)])
/// == "foo=%C3%A9%26&bar=&foo=%23".
/// One fixed-point step per level (avoiding one big fuel reveal): the fold's head step
/// == append the first pair, then fold the tail table.
proof fn ext_pairs_step(s: Seq<u8>, start: int, pairs: Seq<(Seq<u8>, Seq<u8>)>)
    requires pairs.len() > 0
    ensures extend_pairs_spec(s, start, pairs)
        == extend_pairs_spec(append_pair_spec(s, start, pairs[0].0, pairs[0].1), start,
            pairs.subrange(1, pairs.len() as int))
{
    reveal_with_fuel(extend_pairs_spec, 1);
}

proof fn ut_extend_pairs_lemma()
    ensures extend_pairs_spec(Seq::<u8>::empty(), 0,
        seq![(seq![b'f', b'o', b'o'], seq![0xC3, 0xA9, 0x26]),
             (seq![b'b', b'a', b'r'], Seq::<u8>::empty()),
             (seq![b'f', b'o', b'o'], seq![0x23])])
        == ut1_expected()
{
    let foo = seq![b'f', b'o', b'o'];
    let ea = seq![0xC3, 0xA9, 0x26];
    let bar = seq![b'b', b'a', b'r'];
    let h23 = seq![0x23];
    let p0: (Seq<u8>, Seq<u8>) = (foo, ea);
    let p1: (Seq<u8>, Seq<u8>) = (bar, Seq::<u8>::empty());
    let p2: (Seq<u8>, Seq<u8>) = (foo, h23);
    let P = seq![p0, p1, p2];
    assert(P.index(0) == p0);
    assert(P.index(1) == p1);
    assert(P.index(2) == p2);
    // encode literals (encode_len reveal depth = len+1; fuel given in full)
    reveal_with_fuel(encode_len, 7);
    assert(encoded(foo) == foo);
    assert(encoded(ea) == seq![0x25, b'C', 0x33, 0x25, b'A', 0x39, 0x25, 0x32, 0x36]);
    reveal_with_fuel(encode_len, 4);
    assert(encoded(bar) == bar);
    reveal_with_fuel(encode_len, 4);
    assert(encoded(h23) == seq![0x25, 0x32, 0x33]);
    // stepwise valuation (one reveal per step, small-blob concatenation asserts)
    reveal_with_fuel(append_pair_spec, 1);
    reveal_with_fuel(append_sep, 1);
    let s1 = append_pair_spec(Seq::<u8>::empty(), 0, p0.0, p0.1);
    assert(s1 == seq![b'f', b'o', b'o', 0x3D,
        0x25, b'C', 0x33, 0x25, b'A', 0x39, 0x25, 0x32, 0x36]);
    let s2 = append_pair_spec(s1, 0, p1.0, p1.1);
    assert(s2 == seq![b'f', b'o', b'o', 0x3D,
        0x25, b'C', 0x33, 0x25, b'A', 0x39, 0x25, 0x32, 0x36,
        0x26, b'b', b'a', b'r', 0x3D]);
    let s3 = append_pair_spec(s2, 0, p2.0, p2.1);
    assert(s3 == ut1_expected());
    // equation-by-equation join with the fold (head-step lemma + subrange head element)
    let P1 = P.subrange(1, 3);
    subrange_head_tail(P, 1, 3);
    assert(P1.index(0) == p1);
    let P2 = P1.subrange(1, 2);
    subrange_head_tail(P1, 1, 2);
    assert(P2.index(0) == p2);
    ext_pairs_step(Seq::<u8>::empty(), 0, P);
    ext_pairs_step(s1, 0, P1);
    ext_pairs_step(s2, 0, P2);
    reveal_with_fuel(extend_pairs_spec, 1);
    assert(P2.subrange(1, 1).len() == 0);
}

/// Semantic computation: parse("foo=%C3%A9%26&bar=&foo=%23") == the original pair list.
proof fn ut_parse_roundtrip_lemma()
    ensures parse_seq(ut1_expected())
        == seq![(seq![b'f', b'o', b'o'], seq![0xC3, 0xA9, 0x26]),
                (seq![b'b', b'a', b'r'], Seq::<u8>::empty()),
                (seq![b'f', b'o', b'o'], seq![0x23])]
{
    let inp = ut1_expected();
    assert(inp.len() == 26);
    assert(inp[13] == 0x26);
    assert(inp[18] == 0x26);
    // '&' appears only at the two structural separators (everything else is %-escaped)
    assert(forall|j: int| 0 <= j < 13 ==> #[trigger] inp[j] != 0x26);
    assert(forall|j: int| 14 <= j < 18 ==> #[trigger] inp[j] != 0x26);
    assert(forall|j: int| 19 <= j < 26 ==> #[trigger] inp[j] != 0x26);
    reveal_with_fuel(parse_scan, 2);
    parse_scan_skip(inp, 0, 13, 0);
    parse_scan_skip(inp, 14, 18, 14);
    parse_scan_skip(inp, 19, 26, 19);
    // emit_seg of the three sequences plus the trailing empty sequence
    assert(parse_seq(inp)
        == emit_seg(inp, 0, 13) + emit_seg(inp, 14, 18) + emit_seg(inp, 19, 26));
    assert(emit_seg(inp, 0, 13) == emit_pair_scan(inp, 0, 0, 13));
    assert(emit_seg(inp, 14, 18) == emit_pair_scan(inp, 14, 14, 18));
    assert(emit_seg(inp, 19, 26) == emit_pair_scan(inp, 19, 19, 26));
    // '=' only at the structural positions (3 / 17 / 22); name/value decode literal, segment by segment
    assert(inp[3] == 0x3D);
    assert(inp[17] == 0x3D);
    assert(inp[22] == 0x3D);
    emit_pair_scan_skip(inp, 0, 0, 3, 13);
    emit_pair_scan_skip(inp, 14, 14, 17, 18);
    emit_pair_scan_skip(inp, 19, 19, 22, 26);
    reveal_with_fuel(emit_pair_scan, 2);
    let n1 = Seq::new(3 as nat, |j: int| inp[0 + j]);
    let v1 = Seq::new(9 as nat, |j: int| inp[4 + j]);
    let n2 = Seq::new(3 as nat, |j: int| inp[14 + j]);
    let v2 = Seq::new(0 as nat, |j: int| inp[18 + j]);
    let n3 = Seq::new(3 as nat, |j: int| inp[19 + j]);
    let v3 = Seq::new(3 as nat, |j: int| inp[23 + j]);
    assert(emit_pair_scan(inp, 0, 3, 13) == seq![(decode(n1, 0), decode(v1, 0))]);
    assert(emit_pair_scan(inp, 14, 17, 18) == seq![(decode(n2, 0), decode(v2, 0))]);
    assert(emit_pair_scan(inp, 19, 22, 26) == seq![(decode(n3, 0), decode(v3, 0))]);
    assert(n1 =~= seq![b'f', b'o', b'o']);
    assert(v1 =~= seq![0x25, b'C', 0x33, 0x25, b'A', 0x39, 0x25, 0x32, 0x36]);
    assert(n2 =~= seq![b'b', b'a', b'r']);
    assert(v2 =~= Seq::<u8>::empty());
    assert(n3 =~= seq![b'f', b'o', b'o']);
    assert(v3 =~= seq![0x25, 0x32, 0x33]);
    // decode literals: "foo" unescaped; "%C3%A9%26" a folded triplet; "bar"/""/foo; "%23"
    reveal_with_fuel(decode, 10);
    assert(decode(n1, 0) == seq![b'f', b'o', b'o']);
    assert(decode(v1, 0) == seq![0xC3, 0xA9, 0x26]);
    assert(decode(n2, 0) == seq![b'b', b'a', b'r']);
    assert(decode(v2, 0) == Seq::<u8>::empty());
    assert(decode(n3, 0) == seq![b'f', b'o', b'o']);
    assert(decode(v3, 0) == seq![0x23]);
}

/// One fixed-point step (the keys version corresponding to ext_pairs_step).
proof fn ext_keys_step(s: Seq<u8>, start: int, keys: Seq<Seq<u8>>)
    requires keys.len() > 0
    ensures extend_keys_only_spec(s, start, keys)
        == extend_keys_only_spec(append_key_only_spec(s, start, keys[0]), start,
            keys.subrange(1, keys.len() as int))
{
    reveal_with_fuel(extend_keys_only_spec, 1);
}

proof fn ut_extend_keys_only_lemma()
    ensures extend_keys_only_spec(Seq::<u8>::empty(), 0,
            seq![seq![b'j', b's', b'o', b'n'], seq![b'a', 0x20, b'b']])
        == seq![b'j', b's', b'o', b'n', 0x26, b'a', b'+', b'b']
{
    let k1 = seq![b'j', b's', b'o', b'n'];
    let k2 = seq![b'a', 0x20, b'b'];
    let K = seq![k1, k2];
    assert(K.index(0) == k1);
    assert(K.index(1) == k2);
    // encode literals (encode_len reveal depth = len+1)
    reveal_with_fuel(encode_len, 6);
    assert(encoded(k1) == k1);
    reveal_with_fuel(encode_len, 5);
    assert(encoded(k2) == seq![b'a', b'+', b'b']);  // ' ' -> '+'
    // two-step fold valuation
    reveal_with_fuel(append_key_only_spec, 1);
    reveal_with_fuel(append_sep, 1);
    let s1 = append_key_only_spec(Seq::<u8>::empty(), 0, k1);
    assert(s1 == k1);   // fresh: append_sep skips vacuously
    let s2 = append_key_only_spec(s1, 0, k2);
    assert(s2 == seq![b'j', b's', b'o', b'n', 0x26, b'a', b'+', b'b']);
    // join with the fold equations
    let K1 = K.subrange(1, 2);
    subrange_head_tail(K, 1, 2);
    assert(K1.index(0) == k2);
    ext_keys_step(Seq::<u8>::empty(), 0, K);
    ext_keys_step(s1, 0, K1);
    reveal_with_fuel(extend_keys_only_spec, 1);
    assert(K1.subrange(1, 1).len() == 0);
}
}

fn main() {}
