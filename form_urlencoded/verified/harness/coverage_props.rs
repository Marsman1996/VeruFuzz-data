//! form_urlencoded **harness zone** -- the coverage-delta batch (2026-11-02)
//! generic properties (auto-generated, P5 series). This file writes
//! property assertions for the API face the early 2026-10-29 batch left
//! uncovered: the byte_serialize size_hint bounds / clear erase-restore /
//! extend_pairs / extend_keys_only pure-serialization equivalence /
//! Parse::into_owned payload indistinguishability / the finish
//! state-machine chain / construction-path controls / the encode None identity.
//! Reference-style structure: `#[path = "../src/lib.rs"] mod formlib;` --
//! references only the src-zone spec models, the section F state-machine carrier
//! and the shared lemmas, duplicating no fact source; the local minor lemmas of
//! this file (subrange_prefix_of_concat / serialize_all) support the harness-side
//! assertions, duplicating no src-side spec.
//!
//! Run: verus database/form_urlencoded/verified/harness/coverage_props.rs
//! Reading: apart from the F1 expected error pulled in by the integral re-verification
//! of the formlib module (the for_suffix_upstream panic! anchor in src/lib.rs),
//! everything else verifies.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod formlib;

use formlib::*;

verus! {

// ================= P5-1: the byte_serialize::size_hint bounds (lemmas at the
//     file tail) =================

// ================= P5-2: the clear erase-restore property =================

/// UT-exemplar-style universal: for any name/value, a fresh serializer that
/// appends one pair then clear returns to the empty payload.
/// Upstream doc (lib.rs:238-240):
///   Remove any existing name/value pair.
///   Panics if called after `.finish()`.
pub exec fn clear_removes_all_appended_pairs(name: &Vec<u8>, value: &Vec<u8>)
    -> (r: Vec<u8>)
    ensures r@ == Seq::<u8>::empty()
{
    let mut st = SerializerByte::new(Vec::new());
    assert(st.payload@ == Seq::<u8>::empty());
    st.append_pair(name, value);
    proof { clear_restores_constructor_suffix(Seq::<u8>::empty(), name@, value@); }
    st.clear();
    let r = st.payload.clone();
    r
}

// ================= P5-3: extend_pairs / extend_keys_only pure-serialization equivalence =================

/// Each pair purely serialized and joined with '&' (the expected output for a fresh target).
pub open spec fn serialize_all(pairs: Seq<(Seq<u8>, Seq<u8>)>) -> Seq<u8>
    decreases pairs.len()
{
    if pairs.len() == 0 {
        Seq::empty()
    } else if pairs.len() == 1 {
        serialize_pair(pairs[0].0, pairs[0].1)
    } else {
        serialize_pair(pairs[0].0, pairs[0].1) + seq![0x26u8]
            + serialize_all(pairs.subrange(1, pairs.len() as int))
    }
}

/// Each key purely encoded and joined with '&' (the expected output for a fresh target).
pub open spec fn serialize_keys_all(keys: Seq<Seq<u8>>) -> Seq<u8>
    decreases keys.len()
{
    if keys.len() == 0 {
        Seq::empty()
    } else if keys.len() == 1 {
        encoded(keys[0])
    } else {
        encoded(keys[0]) + seq![0x26u8] + serialize_keys_all(keys.subrange(1, keys.len() as int))
    }
}

// ================= P5-4: Parse::into_owned / ParseIntoOwned payload indistinguishability =================

/// Universal (any input byte string): the byte payloads of
/// `parse(input).into_owned().collect` and `parse(input).collect` are one-to-one
/// identical (Cow::into_owned only changes ownership, never content; both carrier
/// sides' ensures point at the same parse_seq(input@)).
/// Upstream doc (lib.rs:96-96):
///   Return a new iterator that yields pairs of `String` instead of pairs of `Cow<str>`.
pub exec fn into_owned_parity(input: &[u8]) -> (a: Vec<(Vec<u8>, Vec<u8>)>)
    ensures
        pairs_view(a@) == parse_seq(input@),
{
    let b = parse_all(input);
    let a = parse_into_owned_all(input);
    // bidirectional parity (the in-body assertions are the obligations): both ensures
    // point at parse_seq(input@)
    assert(pairs_view(a@) == parse_seq(input@));
    assert(pairs_view(b@) == parse_seq(input@));
    a
}

// ================= P5-5: the finish state-machine chain =================

/// Universal (any name/value), from the doc (lib.rs:332): the return of
/// new + append_pair + finish == the pure serialization of that pair.
/// Upstream doc (lib.rs:332-343):
///   If this serializer was constructed with a string, take and return that string.
///   Panics if called more than once.
pub exec fn new_append_finish_serializes_pair(name: &Vec<u8>, value: &Vec<u8>)
    -> (r: Vec<u8>)
    ensures r@ == serialize_pair(name@, value@)
{
    let mut st = SerializerByte::new(Vec::new());
    st.append_pair(name, value);
    let r = st.finish();
    proof {
        // fresh target => append_sep skips vacuously => append_pair_spec == serialize_pair
        reveal_with_fuel(append_pair_spec, 1);
        reveal_with_fuel(append_sep, 1);
    }
    r
}

// ================= P5-6: the encode None branch and default construction =================

/// From the doc (lib.rs:246) plus the file-header ruling: a freshly constructed
/// serializer's encoding is always None, so encode's None branch (lib.rs:396
/// `input.as_bytes()`) is the byte identity.
/// Upstream doc (lib.rs:246-246):
///   Set the character encoding to be used for names and values before percent-encoding.
pub exec fn default_encoding_none_branch_identity(input: &Vec<u8>) -> (r: bool)
    ensures r == true
{
    let st = SerializerByte::new(Vec::new()); // ensures !st.encoding_set(lib.rs:234)
    assert(!st.encoding_set);
    let input_sl: &[u8] = input;
    let out = encode_none(st.encoding_set, input_sl);
    assert(out@ == input@); // the None-branch identity (lib.rs:396; the in-body assertion is the obligation)
    true
}

// ================= P5-7: construction-path controls (new == for_suffix(target, 0)) =================

/// Doc lib.rs:213-215: `new` is exactly `for_suffix(target, 0)`; the two
/// construction paths agree on the whole carrier quadruple (universal over the
/// payload; the in-body assertions are the already-checked obligations).
/// Upstream doc (lib.rs:209-212):
///   Create a new `application/x-www-form-urlencoded` serializer for the given target.
///   If the target is non-empty,
///   its content is assumed to already be in `application/x-www-form-urlencoded` syntax.
pub exec fn new_eq_for_suffix_zero_construction(payload: &Vec<u8>) -> (r: bool)
    ensures r == true
{
    let a = SerializerByte::new(payload.clone());
    let b = SerializerByte::for_suffix(payload.clone(), 0);
    assert(a.payload@ == b.payload@);       // both paths return the same construction-point payload
    assert(a.start_position == b.start_position);
    assert(a.target_present == b.target_present);
    assert(a.encoding_set == b.encoding_set);
    true
}


// ===========================================================================
// Proof lemmas (P5-1 size_hint bounds, P5-2 clear restore, P5-3 fold join;
// moved to the end of the file so the exec/spec definitions read directly --
// only the order changed, signatures and contracts untouched)
// ===========================================================================
/// Piece-count basic bound: the number of pieces within [i, len) is in [0, len-i].
proof fn piece_total_bounds(s: Seq<u8>, i: int)
    requires 0 <= i <= s.len()
    ensures 0 <= piece_total(s, i) <= s.len() - i
    decreases s.len() - i
{
    if i < s.len() {
        reveal_with_fuel(piece_total, 1);
        piece_total_bounds(s, i + 1);
    }
}

/// L1 property: the size_hint (lib.rs:165-171) lower bound 1 and upper bound len
/// envelope exactly the number of pieces next() actually yields from construction
/// on; with empty input (0, Some(0)) matches 0 pieces.
proof fn size_hint_envelopes_piece_count(s: Seq<u8>)
    ensures
        s.len() > 0 ==> 1 <= piece_count_all(s) <= s.len(),
        s.len() == 0 ==> piece_count_all(s) == 0,
{
    if s.len() > 0 {
        reveal_with_fuel(piece_total, 1);
        assert(chunk_start(s, 0)); // i == 0 => a piece start (lib.rs:139 split_first)
        piece_total_bounds(s, 1);
        assert(piece_count_all(s) >= 1);
    } else {
        reveal_with_fuel(piece_total, 1);
        assert(piece_total(s, 0) == 0);
    }
}

/// Local minor lemma of this file: the first |a| elements of (a + b) are exactly a.
proof fn subrange_prefix_of_concat(a: Seq<u8>, b: Seq<u8>)
    ensures (a + b).subrange(0, a.len() as int) == a
{
    assert((a + b).subrange(0, a.len() as int).len() == a.len());
    assert forall|k: int| 0 <= k < a.len() implies #[trigger]
        (a + b).subrange(0, a.len() as int).index(k) == a.index(k) by {
        assert((a + b).index(k) == a.index(k));
    }
}

/// Generic property: for any prefix at a legal for_suffix construction point, clear
/// after append_pair restores the construction-point content (every appended pair
/// is withdrawn).
proof fn clear_restores_constructor_suffix(prefix: Seq<u8>, name: Seq<u8>, value: Seq<u8>)
    requires prefix.len() >= 0
    ensures clear_spec(append_pair_spec(prefix, prefix.len() as int, name, value), prefix.len() as int)
        == prefix
{
    let start: int = prefix.len() as int;
    reveal_with_fuel(append_sep, 1);
    assert(append_sep(prefix, start) == prefix); // prefix.len() > start is false => no '&' appended
    reveal_with_fuel(append_pair_spec, 1);
    let appended = prefix + encoded(name) + seq![0x3Du8] + encoded(value);
    assert(append_pair_spec(prefix, start, name, value) == appended);
    assert(appended.len() > start); // even empty encodes still contain the structural '='
    assert(clear_spec(appended, start) == appended.subrange(0, start));
    assert(appended
        == prefix + (encoded(name) + seq![0x3Du8] + encoded(value)));
    subrange_prefix_of_concat(prefix, encoded(name) + seq![0x3Du8] + encoded(value));
}

/// Generalized intermediate step: folding pairs over any base payload s <=> the
/// necessary separator plus each pair purely serialized and joined with
/// '&' (an empty pair table appends nothing at all, not even a separator).
proof fn extend_pairs_gen(s: Seq<u8>, pairs: Seq<(Seq<u8>, Seq<u8>)>)
    ensures
        extend_pairs_spec(s, 0, pairs)
            == s + (if s.len() > 0 && pairs.len() > 0 { seq![0x26u8] } else { Seq::<u8>::empty() })
                + serialize_all(pairs),
    decreases pairs.len()
{
    if pairs.len() == 0 {
        reveal_with_fuel(extend_pairs_spec, 1);
        assert(serialize_all(pairs).len() == 0);
    } else {
        reveal_with_fuel(extend_pairs_spec, 1);
        reveal_with_fuel(append_pair_spec, 1);
        reveal_with_fuel(append_sep, 1);
        let sep = if s.len() > 0 { seq![0x26u8] } else { Seq::<u8>::empty() };
        let sp0 = serialize_pair(pairs[0].0, pairs[0].1);
        // append_pair_spec(s, 0, .) == s + sep + sp0 (append_sep: '&' only when s non-empty)
        assert(append_pair_spec(s, 0, pairs[0].0, pairs[0].1) == s + sep + sp0);
        let s1 = s + sep + sp0;
        extend_pairs_gen(s1, pairs.subrange(1, pairs.len() as int));
        assert(s1.len() > 0); // serialize_pair contains the structural '=' => the new base is non-empty
        let rest = pairs.subrange(1, pairs.len() as int);
        let inner = serialize_all(rest);
        assert(rest.len() == pairs.len() - 1);
        assert(serialize_all(pairs) == sp0 + (if rest.len() > 0 {
            seq![0x26u8] + inner
        } else {
            Seq::<u8>::empty()
        }));
    }
}

/// L2 property (doc lib.rs:279-281 "This simply calls append_pair repeatedly."):
/// on a fresh target extend_pairs(pairs) == each pair purely serialized joined with '&'.
proof fn extend_pairs_fresh_serialize_all(pairs: Seq<(Seq<u8>, Seq<u8>)>)
    ensures extend_pairs_spec(Seq::<u8>::empty(), 0, pairs) == serialize_all(pairs)
    decreases pairs.len()
{
    extend_pairs_gen(Seq::<u8>::empty(), pairs);
    assert(serialize_all(Seq::<(Seq<u8>, Seq<u8>)>::empty()).len() == 0);
    if pairs.len() > 0 {
        reveal_with_fuel(extend_pairs_spec, 1);
        reveal_with_fuel(append_pair_spec, 1);
        reveal_with_fuel(append_sep, 1);
    }
}

proof fn extend_keys_only_gen(s: Seq<u8>, keys: Seq<Seq<u8>>)
    requires forall|j: int| 0 <= j < keys.len() ==> #[trigger] keys[j].len() > 0
    ensures
        extend_keys_only_spec(s, 0, keys)
            == s + (if s.len() > 0 && keys.len() > 0 { seq![0x26u8] } else { Seq::<u8>::empty() })
                + serialize_keys_all(keys),
    decreases keys.len()
{
    if keys.len() == 0 {
        reveal_with_fuel(extend_keys_only_spec, 1);
        assert(serialize_keys_all(keys).len() == 0);
    } else {
        reveal_with_fuel(extend_keys_only_spec, 1);
        reveal_with_fuel(append_key_only_spec, 1);
        reveal_with_fuel(append_sep, 1);
        let sep = if s.len() > 0 { seq![0x26u8] } else { Seq::<u8>::empty() };
        assert(append_key_only_spec(s, 0, keys[0]) == s + sep + encoded(keys[0]));
        let s1 = s + sep + encoded(keys[0]);
        assert(keys[0].len() > 0); // precondition: key non-empty => encoded non-empty => s1 non-empty
        assert(s1.len() > 0);
        extend_keys_only_gen(s1, keys.subrange(1, keys.len() as int));
        let rest = keys.subrange(1, keys.len() as int);
        let inner = serialize_keys_all(rest);
        assert(rest.len() == keys.len() - 1);
        assert(serialize_keys_all(keys) == encoded(keys[0]) + (if rest.len() > 0 {
            seq![0x26u8] + inner
        } else {
            Seq::<u8>::empty()
        }));
    }
}

/// L2 property (doc lib.rs:309-311 "This simply calls append_key_only repeatedly."):
/// on a fresh target extend_keys_only(keys) == each key purely encoded joined with '&'.
proof fn extend_keys_only_fresh_serialize_keys_all(keys: Seq<Seq<u8>>)
    requires forall|j: int| 0 <= j < keys.len() ==> #[trigger] keys[j].len() > 0
    ensures extend_keys_only_spec(Seq::<u8>::empty(), 0, keys) == serialize_keys_all(keys)
    decreases keys.len()
{
    extend_keys_only_gen(Seq::<u8>::empty(), keys);
    assert(serialize_keys_all(Seq::<Seq<u8>>::empty()).len() == 0);
    if keys.len() > 0 {
        reveal_with_fuel(extend_keys_only_spec, 1);
        reveal_with_fuel(append_key_only_spec, 1);
        reveal_with_fuel(append_sep, 1);
    }
}
}

fn main() {}
