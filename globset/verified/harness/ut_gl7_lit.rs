//! GL7-unit harness -- the set tier's literal-family vectors (KAT
//! form): upstream matches_all_literals (mla/mlb),
//! matches_all_basename_literals (mbla/mblb), plus the GL8
//! BasenameLiteral empty-basename guard rows (the lib's
//! lemma_baselit_empty_basename_guard exercised on the GL6-anchored
//! `foo/..` candidate).
//!
//! Value provenance: the GL7/GL8 TWOTREE lock (oracle==mirror==
//! upstream test literals). Routing rides the oracle RT rows; the
//! classification tie itself lives at the GL4 extractor units.
//! The lane discipline: every builder mutation is followed
//! immediately by its own proof block consuming THAT stage's
//! postconditions (the GL8 batch lesson: consolidated end-of-loop
//! proofs lose the mid-stage ensures instantiation).

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

use lib::{Candidate, GlobSetMatchStrategyS, LiteralStrategy,
    lemma_baselit_empty_basename_guard, spec_gsm_is_match, spec_gsm_list_nonempty_iff,
    spec_gsm_matches_all, spec_gsm_matches_list};

verus! {

fn b_abc() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x62, 0x63],
{
    vec![0x61, 0x62, 0x63]
}

fn b_def() -> (r: Vec<u8>)
    ensures r@ == seq![0x64, 0x65, 0x66],
{
    vec![0x64, 0x65, 0x66]
}

fn b_a_c() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x2e, 0x63],
{
    vec![0x61, 0x2e, 0x63]
}

fn c_abc() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x62, 0x63],
        r.basename.view() == seq![0x61, 0x62, 0x63],
{
    let v: Vec<u8> = vec![0x61, 0x62, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x62, 0x63])
            == seq![0x61, 0x62, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x62, 0x63]);
    c
}

fn c_def() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x64, 0x65, 0x66],
        r.basename.view() == seq![0x64, 0x65, 0x66],
{
    let v: Vec<u8> = vec![0x64, 0x65, 0x66];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x64, 0x65, 0x66])
            == seq![0x64, 0x65, 0x66]) by (compute_only);
    }
    assert(c.path.view() == seq![0x64, 0x65, 0x66]);
    c
}

fn c_foo_abc() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x62, 0x63],
        r.basename.view() == seq![0x61, 0x62, 0x63],
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x62, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x62, 0x63])
            == seq![0x61, 0x62, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x62, 0x63]);
    c
}

fn c_foo_ac() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63],
        r.basename.view() == seq![0x61, 0x2e, 0x63],
        r.ext.view() == seq![0x2e, 0x63],
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63])
            == seq![0x61, 0x2e, 0x63]) by (compute_only);
        assert(lib::spec_cand_ext(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63])
            == seq![0x2e, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63]);
    c
}

fn c_foo_dotdot() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e],
        r.basename.view() == Seq::<u8>::empty(),
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e])
            == Seq::<u8>::empty()) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e]);
    c
}

// mla: [Literal("abc"), Literal("def")] -- the two-key literal
// column; matches_all's singleton gate is barred.
fn mla_checks() {
    let mut lits = LiteralStrategy::new();
    let abc = b_abc();
    lits.add(0, abc);
    proof {
        assert(abc@.len() == 3);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_lenbit(abc@.len() as int) == 8u64);
        assert((0u64 | 8u64) == 8u64) by (compute_only);
        assert(lits.lengths == 8u64);
        assert(lits.literals.keys@ == seq![abc]);
        assert(lits.literals.keys@.len() == 1);
    }
    let def = b_def();
    lits.add(1, def);
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_has_scan, 4);
        assert(def@.len() == 3);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_lenbit(def@.len() as int) == 8u64);
        assert((8u64 | 8u64) == 8u64) by (compute_only);
        assert(lits.lengths == 8u64);
        assert(lits.literals.keys@ == seq![abc, def]);
        assert(lits.literals.keys@.len() == 2);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_may_len(8u64, 3int) == true) by (compute_only);
        assert(lib::spec_may_len(lits.lengths, 3) == true);
        assert(lib::spec_map_find(lits.literals.keys@, seq![0x61, 0x62, 0x63])
            == Some(0int));
        assert(lib::spec_map_find(lits.literals.keys@, seq![0x64, 0x65, 0x66])
            == Some(1int));
        assert(lib::spec_hit_list(lits.literals.keys@, lits.literals.events@,
            seq![0x61, 0x62, 0x63]) == seq![0]);
        assert(lib::spec_hit_list(lits.literals.keys@, lits.literals.events@,
            seq![0x64, 0x65, 0x66]) == seq![1]);
    }
    let s = GlobSetMatchStrategyS::Literal(lits);
    let c1 = c_abc();
    let c2 = c_def();
    assert(spec_gsm_is_match(&s, &c1) == true);
    assert(spec_gsm_is_match(&s, &c2) == true);
    assert(spec_gsm_matches_all(&s, &c1) == false);  // MA mla 616263 = false
    assert(spec_gsm_matches_all(&s, &c2) == false);  // MA mla 646566 = false
    assert(spec_gsm_matches_list(&s, &c1) == seq![0]);
    assert(spec_gsm_matches_list(&s, &c2) == seq![1]);
    assert(spec_gsm_list_nonempty_iff(&s, &c1));
}

// mlb: [Literal("abc")] -- the single-key column.
fn mlb_checks() {
    let mut lits = LiteralStrategy::new();
    let abc = b_abc();
    lits.add(0, abc);
    proof {
        assert(abc@.len() == 3);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_lenbit(abc@.len() as int) == 8u64);
        assert((0u64 | 8u64) == 8u64) by (compute_only);
        assert(lits.lengths == 8u64);
        assert(lits.literals.keys@ == seq![abc]);
        assert(lits.literals.keys@.len() == 1);
        assert(lib::spec_may_len(8u64, 3int) == true) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_has_scan, 4);
        assert(lib::spec_may_len(lits.lengths, 3) == true);
        assert(lib::spec_map_find(lits.literals.keys@, seq![0x61, 0x62, 0x63])
            == Some(0int));
        assert(lib::spec_hit_list(lits.literals.keys@, lits.literals.events@,
            seq![0x61, 0x62, 0x63]) == seq![0]);
    }
    let s = GlobSetMatchStrategyS::Literal(lits);
    let c = c_abc();
    assert(spec_gsm_matches_all(&s, &c) == true);        // MA mlb 616263 = true
    assert(spec_gsm_is_match(&s, &c) == true);
    assert(spec_gsm_matches_list(&s, &c) == seq![0]);
    assert(spec_gsm_list_nonempty_iff(&s, &c));
}

// mbla/mblb: the basename-literal buckets.
fn mbla_checks() {
    let mut lits2 = LiteralStrategy::new();
    let abc = b_abc();
    lits2.add(0, abc);
    proof {
        assert(abc@.len() == 3);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_lenbit(abc@.len() as int) == 8u64);
        assert((0u64 | 8u64) == 8u64) by (compute_only);
        assert(lits2.lengths == 8u64);
        assert(lits2.literals.keys@ == seq![abc]);
    }
    let acel = b_a_c();
    lits2.add(1, acel);
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_has_scan, 4);
        assert(lits2.literals.keys@ == seq![abc, acel]);
        assert(lits2.literals.keys@.len() == 2);
        assert(lib::spec_map_find(lits2.literals.keys@, seq![0x61, 0x62, 0x63])
            == Some(0int));
        assert(lib::spec_map_find(lits2.literals.keys@, seq![0x61, 0x2e, 0x63])
            == Some(1int));
        assert(lib::spec_hit_list(lits2.literals.keys@, lits2.literals.events@,
            seq![0x61, 0x62, 0x63]) == seq![0]);
        assert(lib::spec_hit_list(lits2.literals.keys@, lits2.literals.events@,
            seq![0x61, 0x2e, 0x63]) == seq![1]);
    }
    let s2 = GlobSetMatchStrategyS::BasenameLiteral(lits2);
    let cab = c_foo_abc();
    let cac = c_foo_ac();
    proof {
        assert(cab.basename.view() == seq![0x61, 0x62, 0x63]);
        assert(cab.basename.view().len() == 3);
        assert(lib::spec_may_len(8u64, 3int) == true) by (compute_only);
        assert(acel@.len() == 3);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_lenbit(acel@.len() as int) == 8u64);
        assert((8u64 | 8u64) == 8u64) by (compute_only);
        assert(lits2.lengths == 8u64);
        assert(lib::spec_may_len(8u64, 3int) == true) by (compute_only);
        assert(lib::spec_may_len(lits2.lengths, 3) == true);
        assert(lib::spec_map_find(lits2.literals.keys@, cab.basename.view())
            == Some(0int));
        assert(lib::spec_map_find(lits2.literals.keys@, cac.basename.view())
            == Some(1int));
    }
    assert(spec_gsm_is_match(&s2, &cab) == true);     // IM mbla 666f6f2f616263 = true
    assert(spec_gsm_is_match(&s2, &cac) == true);     // IM mbla 666f6f2f612e63 = true
    assert(spec_gsm_matches_all(&s2, &cab) == false); // MA mbla 666f6f2f616263 = false
    assert(spec_gsm_matches_all(&s2, &cac) == false); // MA mbla 666f6f2f612e63 = false
    assert(spec_gsm_matches_list(&s2, &cab) == seq![0]);
    assert(spec_gsm_matches_list(&s2, &cac) == seq![1]);

    // mblb: the single basename literal -> the gate passes
    let mut lits1 = LiteralStrategy::new();
    let acel2 = b_a_c();
    lits1.add(0, acel2);
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_has_scan, 4);
        assert(acel2@.len() == 3);
        assert(lib::spec_lenbit(3int) == 8u64) by (compute_only);
        assert(lib::spec_lenbit(acel2@.len() as int) == 8u64);
        assert((0u64 | 8u64) == 8u64) by (compute_only);
        assert(lits1.lengths == 8u64);
        assert(lits1.literals.keys@ == seq![acel2]);
        assert(lits1.literals.keys@.len() == 1);
        assert(lib::spec_may_len(8u64, 3int) == true) by (compute_only);
        assert(lib::spec_may_len(lits1.lengths, 3) == true);
        assert(lib::spec_map_find(lits1.literals.keys@, seq![0x61, 0x2e, 0x63])
            == Some(0int));
        assert(lib::spec_hit_list(lits1.literals.keys@, lits1.literals.events@,
            seq![0x61, 0x2e, 0x63]) == seq![0]);
    }
    let s1 = GlobSetMatchStrategyS::BasenameLiteral(lits1);
    let cb = c_foo_ac();
    assert(spec_gsm_matches_all(&s1, &cb) == true);      // MA mblb 666f6f2f612e63 = true
    assert(spec_gsm_is_match(&s1, &cb) == true);
    assert(spec_gsm_matches_list(&s1, &cb) == seq![0]);
}

// The GL8 guard rows: the `foo/..` candidate (empty basename) under
// the mbla pair -- the dispatch's load-bearing
// `!candidate.basename.is_empty()` guard (lib.rs:726-731's arm; the
// guard theorem consumed here, GL6's `**/..` x "foo/.." anchors).
fn baselit_guard_checks() {
    let mut lits2 = LiteralStrategy::new();
    let abc = b_abc();
    lits2.add(0, abc);
    let acel = b_a_c();
    lits2.add(1, acel);
    let s2 = GlobSetMatchStrategyS::BasenameLiteral(lits2);
    let c = c_foo_dotdot();
    proof {
        lemma_baselit_empty_basename_guard(&s2, &c);
    }
    assert(spec_gsm_is_match(&s2, &c) == false);          // IM false by the GUARD
    assert(spec_gsm_matches_all(&s2, &c) == false);      // MA false by the GUARD
    assert(spec_gsm_matches_list(&s2, &c) == Seq::empty());   // MS []
    assert(spec_gsm_list_nonempty_iff(&s2, &c));
}

} // verus!

fn main() {}
