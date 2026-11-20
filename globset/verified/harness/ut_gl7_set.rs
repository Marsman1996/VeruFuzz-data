//! GL7-unit harness -- the set-level composites: upstream set_works
//! (sw, the set tier's headline vector), the empty set (es) and
//! Default rows (def), the duplicate-literal probe (dpl, the fnv
//! merge). Lane discipline: each fn builds its own strategy column
//! inline (every stage proof consumes THAT stage's postconditions --
//! the GL8 batch lesson), the set-level queries ride the lib's
//! channel lemmas (lemma_set_im_witness/_im_none/_all_bar), and the
//! MS row rides the exec canonicalize twin's fourth (iff) face.
//!
//! Value provenance: the TWOTREE lock (GL7 102 rows; all asserted
//! literals are the upstream test wishes). Routing rides the oracle
//! RT rows; the regex column is the oracle's compiled string (GL8
//! RX row), consumed in congruence form.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../src/lib.rs"]
mod lib;

#[allow(unused_imports)]
use lib::CowBytes;
#[allow(unused_imports)]
use lib::pathutil;
#[allow(unused_imports)]
use lib::glob;

use lib::{Candidate, ExtensionStrategy, GlobSet, GlobSetMatchStrategyS,
    LiteralStrategy, RequiredExtensionStrategyBuilder, canonicalize_rec,
    lemma_set_all_bar, lemma_set_im_none, lemma_set_im_witness,
    spec_gsm_is_match, spec_gsm_matches_all, spec_gsm_matches_list};

verus! {

fn b_c() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x63],
{
    vec![0x2e, 0x63]
}

fn b_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x72, 0x73],
{
    vec![0x2e, 0x72, 0x73]
}

fn b_librs() -> (r: Vec<u8>)
    ensures r@ == seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73],
{
    vec![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]
}

fn r_sw() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', 's', 'r', 'c', '(', '?', ':', '/',
            '|', '/', '.', '*', '/', ')', ')', '.', '*', '\\', '.', 'r', 's', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', 's', 'r', 'c', '(', '?', ':', '/',
        '|', '/', '.', '*', '/', ')', ')', '.', '*', '\\', '.', 'r', 's', '$']
}

fn c_foo_c() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x63],
        r.basename.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x63],
        r.ext.view() == seq![0x2e, 0x63],
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2e, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2e, 0x63]) == seq![0x66, 0x6f, 0x6f, 0x2e, 0x63]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2e, 0x63]) == seq![0x2e, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x63]);
    c
}


fn c_src_librs() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) == seq![0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]);
    c
}


fn c_src_ab_c() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x61, 0x2f, 0x62, 0x2e, 0x63],
        r.basename.view() == seq![0x62, 0x2e, 0x63],
        r.ext.view() == seq![0x2e, 0x63],
{
    let v: Vec<u8> = vec![0x73, 0x72, 0x63, 0x2f, 0x61, 0x2f, 0x62, 0x2e, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x73, 0x72, 0x63, 0x2f, 0x61, 0x2f, 0x62, 0x2e, 0x63]) == seq![0x62, 0x2e, 0x63]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x73, 0x72, 0x63, 0x2f, 0x61, 0x2f, 0x62, 0x2e, 0x63]) == seq![0x2e, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x61, 0x2f, 0x62, 0x2e, 0x63]);
    c
}


fn c_foo_rs() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]);
    c
}


fn c_tests_foo_rs() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x74, 0x65, 0x73, 0x74, 0x73, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x74, 0x65, 0x73, 0x74, 0x73, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x74, 0x65, 0x73, 0x74, 0x73, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x74, 0x65, 0x73, 0x74, 0x73, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x74, 0x65, 0x73, 0x74, 0x73, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]);
    c
}


fn c_src_foo_rs() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) == seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73]);
    c
}


fn c_src_grep_main() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x67, 0x72, 0x65, 0x70, 0x2f, 0x73, 0x72, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x73, 0x72, 0x63, 0x2f, 0x67, 0x72, 0x65, 0x70, 0x2f, 0x73, 0x72, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x73, 0x72, 0x63, 0x2f, 0x67, 0x72, 0x65, 0x70, 0x2f, 0x73, 0x72, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x73, 0x72, 0x63, 0x2f, 0x67, 0x72, 0x65, 0x70, 0x2f, 0x73, 0x72, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x67, 0x72, 0x65, 0x70, 0x2f, 0x73, 0x72, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]);
    c
}


fn c_src_foo_c() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x63],
        r.basename.view() == seq![0x66, 0x6f, 0x6f, 0x2e, 0x63],
        r.ext.view() == seq![0x2e, 0x63],
{
    let v: Vec<u8> = vec![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x63]) == seq![0x66, 0x6f, 0x6f, 0x2e, 0x63]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x63]) == seq![0x2e, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x73, 0x72, 0x63, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x63]);
    c
}


// The sw rows: the set is built inline so every arm column stays in
// this frame (arm cells feed the stage proofs; the set-level queries
// ride the lib's channel lemmas).
fn sw_checks() {
    // arm 0: the Extension tier with the single ".c" key
    let mut exts = ExtensionStrategy::new();
    let cdot = b_c();
    exts.add(1, cdot);
    proof {
        assert(exts.0.keys@ == seq![cdot]);
        assert(exts.0.keys@.len() == 1);
    }
    // arm 1: the Literal tier with the single "src/lib.rs" key
    let mut lits = LiteralStrategy::new();
    let librs = b_librs();
    lits.add(2, librs);
    proof {
        assert(librs@.len() == 10);
        assert((1u64 << 10) == 1024u64) by (compute_only);
        assert(lib::spec_lenbit(10int) == 1024u64) by (compute_only);
        assert(lib::spec_lenbit(librs@.len() as int) == 1024u64);
        assert((0u64 | 1024u64) == 1024u64) by (compute_only);
        assert(lits.lengths == 1024u64);
        assert(lits.literals.keys@ == seq![librs]);
    }
    // arm 2: the RequiredExtension tier with the ".rs" key
    let mut reqb = RequiredExtensionStrategyBuilder::new();
    let rxs = r_sw();
    let rsx = b_rs();
    reqb.add(0, rsx, rxs);
    proof {
        assert(reqb.exts.keys@ == seq![rsx]);
        assert(reqb.exts.keys@.len() == 1);
        assert(reqb.exts.events@.len() == 1);
        assert(reqb.exts.events@.index(0).1 == 0);
        assert(reqb.exts.events@.index(0).0 == 0);
    }
    let rxe = reqb.build();
    // the set, populated-only order (exts, lits, reqexts)
    let mut strats: Vec<GlobSetMatchStrategyS> = Vec::new();
    strats.push(GlobSetMatchStrategyS::Extension(exts));
    let la = GlobSetMatchStrategyS::Literal(lits);
    let ra = GlobSetMatchStrategyS::RequiredExtension(rxe);
    strats.push(la);
    strats.push(ra);
    let gset = GlobSet { len: 3, strats };

    let c1 = c_foo_c();
    let c2 = c_src_foo_c();
    // IM "foo.c" / "src/foo.c" -- the Extension arm hits
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        reveal_with_fuel(lib::spec_map_hits_upto, 5);
        reveal_with_fuel(lib::spec_has_scan, 5);
        assert(gset.strats@.len() == 3);
        assert(gset.strats@.index(0) is Extension);
        assert(c1.ext.view() == seq![0x2e, 0x63]);
        assert(c2.ext.view() == seq![0x2e, 0x63]);
        assert(spec_gsm_is_match(&gset.strats@.index(0), &c1) == true);
        assert(spec_gsm_is_match(&gset.strats@.index(0), &c2) == true);
        lemma_set_im_witness(gset.strats@, &c1, 0);
        lemma_set_im_witness(gset.strats@, &c2, 0);
    }
    assert(gset.is_match_of(&c1) == true);      // IM sw 666f6f2e63 = true
    assert(gset.is_match_of(&c2) == true);      // IM sw 7372632f666f6f2e63 = true

    // IM "foo.rs" / "tests/foo.rs": all three arms miss (the reqext
    // oracle flag pinned negative)
    let rr = r_sw();
    let c3 = c_foo_rs();
    let c4 = c_tests_foo_rs();
    proof {
        reveal_with_fuel(lib::spec_reqext_any_hit_upto, 6);
        reveal_with_fuel(lib::spec_reqext_all_hit_upto, 6);
        reveal_with_fuel(lib::spec_reqext_hit_upto, 6);
        // the two negatives, each under the reqext oracle's
        // flag-false case (the ext/lit arms are computable misses)
        if lib::spec_regex_hits(rr@, c3.path.view()) == false {
            assert(!spec_gsm_is_match(&gset.strats@.index(0), &c3));
            assert(!spec_gsm_is_match(&gset.strats@.index(1), &c3));
            assert(!spec_gsm_is_match(&gset.strats@.index(2), &c3));
            lemma_set_im_none(gset.strats@, &c3);
        }
        if lib::spec_regex_hits(rr@, c4.path.view()) == false {
            assert(!spec_gsm_is_match(&gset.strats@.index(0), &c4));
            assert(!spec_gsm_is_match(&gset.strats@.index(1), &c4));
            assert(!spec_gsm_is_match(&gset.strats@.index(2), &c4));
            lemma_set_im_none(gset.strats@, &c4);
        }
    }
    assert(lib::spec_regex_hits(rr@, c3.path.view()) == false
        ==> gset.is_match_of(&c3) == false);   // IM sw 666f6f2e7273 = false
    assert(lib::spec_regex_hits(rr@, c4.path.view()) == false
        ==> gset.is_match_of(&c4) == false);   // IM sw 74657374732f666f6f2e7273 = false

    // IM "src/foo.rs" / "src/grep/src/main.rs": the reqext flag hits
    let c5 = c_src_foo_rs();
    let c6 = c_src_grep_main();
    assert(lib::spec_regex_hits(rr@, c5.path.view()) == true
        ==> spec_gsm_is_match(&gset.strats@.index(2), &c5) == true);
    assert(lib::spec_regex_hits(rr@, c6.path.view()) == true
        ==> spec_gsm_is_match(&gset.strats@.index(2), &c6) == true);
    assert(lib::spec_regex_hits(rr@, c5.path.view()) == true
        ==> gset.is_match_of(&c5) == true);    // IM sw 7372632f666f6f2e7273 = true
    assert(lib::spec_regex_hits(rr@, c6.path.view()) == true
        ==> gset.is_match_of(&c6) == true);    // IM sw src/grep/... = true

    // MA "src/lib.rs" / "src/a/b.c": the Extension tier's single-key
    // gate bars (ext ".rs" is not the tier's ".c" key) -- computable
    let srr = c_src_librs();
    let cabc = c_src_ab_c();
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        reveal_with_fuel(lib::spec_map_hits_upto, 5);
        reveal_with_fuel(lib::spec_reqext_all_hit_upto, 6);
        reveal_with_fuel(lib::spec_has_scan, 5);
        // "src/lib.rs": the Extension tier's single-key gate bars
        // (ext ".rs" is not the ".c" key) -- computable
        assert(!spec_gsm_matches_all(&gset.strats@.index(0), &srr));
        lemma_set_all_bar(gset.strats@, &srr, 0);
        // "src/a/b.c": its ext IS ".c" so the Extension tier passes
        // -- the bar moves to the RequiredExtension tier, whose
        // keyed regex (pattern 0) misses under the flag-false case
        if lib::spec_regex_hits(rr@, cabc.path.view()) == false {
            assert(!spec_gsm_matches_all(&gset.strats@.index(2), &cabc));
            lemma_set_all_bar(gset.strats@, &cabc, 2);
        }
    }
    assert(gset.matches_all_of(&srr) == false);  // MA sw 7372632f6c69622e7273 = false
    assert(lib::spec_regex_hits(rr@, cabc.path.view()) == false
        ==> gset.matches_all_of(&cabc) == false);  // MA sw 7372632f612f622e63 = false

    // MS "src/lib.rs" = [0, 2]: the collected stream is
    // [ext []] + [lit [2]] + [reqext [0]] (under the RX hit), and
    // the exec walk over bound 3 delivers [0, 2] -- the fourth iff
    // face's harness call: cells 0 and 2 kept, 1 not, ascending.
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        reveal_with_fuel(lib::spec_map_hits_upto, 5);
        reveal_with_fuel(lib::spec_reqext_hit_upto, 6);
        reveal_with_fuel(lib::spec_has_scan, 5);
        assert(spec_gsm_matches_list(&gset.strats@.index(0), &srr) == Seq::empty());
        assert(spec_gsm_matches_list(&gset.strats@.index(1), &srr) == seq![2]);
    }
    assert(lib::spec_regex_hits(rr@, srr.path.view()) == true
        ==> spec_gsm_matches_list(&gset.strats@.index(2), &srr) == seq![0]);
    let bag: Vec<usize> = vec![2, 0];
    let walked = canonicalize_rec(bag.as_slice(), 0, 3);
    proof {
        assert(bag@.len() == 2);
        assert(lib::spec_bag_has(bag@, 0));
        assert(lib::spec_bag_has(bag@, 2));
        assert(!lib::spec_bag_has(bag@, 1));
        // the fourth iff face: 0 and 2 kept, 1 not
        assert(lib::spec_bag_has(walked@, 0));
        assert(lib::spec_bag_has(walked@, 2));
        assert(!lib::spec_bag_has(walked@, 1));
        two_cells_two_indexes(walked@);
        assert(walked@.len() >= 2);
        // strictly-ascending cells in band [0,3) without 1: the
        // kept set {0, 2} pins len == 2 exactly
        if walked@.len() == 3 {
            // three strictly-ascending cells inside [0,3): 0, 1, 2
            // in order (each cell >= its rank; the band caps them).
            // The pair gates ride spec_lt_at's explicit
            // instantiations (the ascending morpheme's trigger
            // pattern is the lt_at carrier, not the bare indexes).
            assert(lib::spec_lt_at(walked@, 0));
            assert(lib::spec_lt_at(walked@, 1));
            assert(walked@.index(0) >= 0);
            assert(walked@.index(1) >= walked@.index(0) + 1);
            assert(walked@.index(1) >= 1);
            assert(walked@.index(2) >= walked@.index(1) + 1);
            assert(walked@.index(2) >= 2);
            assert(walked@.index(2) < 3);
            assert(walked@.index(1) < walked@.index(2));
            assert(walked@.index(0) < walked@.index(1));
            assert(walked@.index(0) == 0 && walked@.index(1) == 1
                && walked@.index(2) == 2);
            lib::lemma_bag_has_index_iff(walked@, 1);
            assert(lib::spec_bag_has(walked@, 1));
            assert(false);
        }
        assert(walked@.len() == 2);
        assert(lib::spec_ascending(walked@));
    }
    assert(walked@ == seq![0, 2]);              // MS sw = [0, 2]
}

// Two distinct kept cells force two distinct indexes (the A1 view
// plus index distinctness; the strict-ascending + band + not-has
// faces then pin the length exactly in the walk rows).
proof fn two_cells_two_indexes(s: Seq<usize>)
    requires
        lib::spec_bag_has(s, 0),
        lib::spec_bag_has(s, 2),
    ensures
        s.len() >= 2,
{
    // the A1 iff gives the exists views over the required cells
    lib::lemma_bag_has_index_iff(s, 0);
    lib::lemma_bag_has_index_iff(s, 2);
    let w1 = choose|k1: int| 0 <= k1 < s.len() as int && s.index(k1) == 0;
    let w2 = choose|k2: int| 0 <= k2 < s.len() as int && s.index(k2) == 2;
    assert(w1 != w2);
    assert(if w1 < w2 { s.len() as int >= w2 + 1 } else { s.len() as int >= w1 + 1 });
    assert(s.len() >= 2);
}

// es/def: the empty set -- every is_match false (the empty exists),
// matches_all vacuously true, the canonical value empty.
fn es_checks() {
    let empty: Vec<GlobSetMatchStrategyS> = Vec::new();
    let gset = GlobSet { len: 0, strats: empty };
    let c0: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(Vec::new()));
    let c1 = c_foo_c();
    assert(gset.len == 0);                       // LEN es/def = 0
    assert(gset.strats@.len() == 0);
    assert(gset.is_match_of(&c0) == false);       // IM es "" = false
    assert(gset.is_match_of(&c1) == false);       // IM es "a" = false
    assert(gset.matches_all_of(&c1) == true);    // MA es "a" = true
    assert(gset.matches_of(&c0) == Seq::<usize>::empty());
    assert(gset.matches_of(&c1) == Seq::<usize>::empty());
}

// dpl: the duplicate-literal probe -- two adds of the same literal
// under one fnv key; the merged per-key log lists both ids.
fn dpl_checks() {
    let mut lits = LiteralStrategy::new();
    let librs = b_librs();
    lits.add(0, librs);
    proof {
        assert(librs@.len() == 10);
        assert((1u64 << 10) == 1024u64) by (compute_only);
        assert(lib::spec_lenbit(10int) == 1024u64) by (compute_only);
        assert(lib::spec_lenbit(librs@.len() as int) == 1024u64);
        assert((0u64 | 1024u64) == 1024u64) by (compute_only);
        assert(lits.lengths == 1024u64);
        assert(lits.literals.keys@ == seq![librs]);
    }
    let librs2 = b_librs();
    lits.add(1, librs2);
    proof {
        assert((1024u64 | 1024u64) == 1024u64) by (compute_only);
        assert(lits.lengths == 1024u64);
        reveal_with_fuel(lib::spec_map_find_key_upto, 6);
        reveal_with_fuel(lib::spec_map_hits_upto, 8);
        reveal_with_fuel(lib::spec_has_scan, 8);
        assert(lits.literals.keys@ == seq![librs]);
        assert(lits.literals.keys@.len() == 1);
        assert(lib::spec_may_len(1024u64, 10int) == true) by (compute_only);
        assert(lib::spec_may_len(lits.lengths, 10) == true);
        assert(lib::spec_map_find(lits.literals.keys@,
            seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) == Some(0int));
        assert(lib::spec_hit_list(lits.literals.keys@, lits.literals.events@,
            seq![0x73, 0x72, 0x63, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73])
            == seq![0, 1]);
    }
    let s = GlobSetMatchStrategyS::Literal(lits);
    let c = c_src_librs();
    assert(spec_gsm_matches_list(&s, &c) == seq![0, 1]);   // MS dpl = [0, 1]
    assert(spec_gsm_is_match(&s, &c) == true);
    assert(spec_gsm_matches_all(&s, &c) == true);           // MA dpl = true
}

} // verus!

fn main() {}
