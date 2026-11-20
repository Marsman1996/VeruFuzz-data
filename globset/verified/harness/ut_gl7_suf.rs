//! GL7-unit harness -- the set tier's suffix-lane vectors: the
//! upstream matches_all_suffix rows (msu, this arm) plus the
//! duplicate-suffix probes dpb ("ab" -- the null probe) and dpb2
//! ("as" -- the GL8 additive row that touches the suffix lane; the
//! upstream matches_all_suffix counterexample shape "as" reused
//! over a DUP column).
//!
//! Value provenance: the TWOTREE lock (GL7 102 rows + GL8 additive
//! dpb2/rq2; ALL-MATCH 110).

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

use lib::{Candidate, GlobSetMatchStrategyS, MultiStrategyBuilder, spec_gsm_is_match,
    spec_gsm_list_nonempty_iff, spec_gsm_matches_all, spec_gsm_matches_list};

verus! {

fn b_s() -> (r: Vec<u8>)
    ensures r@ == seq![0x73],
{
    vec![0x73]
}

fn b_main_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
{
    vec![0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]
}

fn c_main_path() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x2f, 0x62, 0x2f, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x61, 0x2f, 0x62, 0x2f, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x2f, 0x62, 0x2f, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x61, 0x2f, 0x62, 0x2f, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x2f, 0x62, 0x2f, 0x63, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]);
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


fn c_abp() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x62],
        r.basename.view() == seq![0x61, 0x62],
        r.ext.view() == Seq::<u8>::empty(),
{
    let v: Vec<u8> = vec![0x61, 0x62];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x62]) == seq![0x61, 0x62]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x61, 0x62]) == Seq::<u8>::empty()) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x62]);
    c
}


fn c_asp() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x73],
        r.basename.view() == seq![0x61, 0x73],
        r.ext.view() == Seq::<u8>::empty(),
{
    let v: Vec<u8> = vec![0x61, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x73]) == seq![0x61, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x61, 0x73]) == Seq::<u8>::empty()) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x73]);
    c
}


// msu's suffix arm: [Suf("s"), Suf("/main.rs")]; longest caps the
// window at 8 (the end-capped pane).
fn msu_suffix_checks() {
    let mut builder = MultiStrategyBuilder::new();
    builder.add(1, b_s());
    builder.add(2, b_main_rs());
    proof {
        assert(builder.map@ == seq![1, 2]);
        assert(builder.longest == 8);
    }
    let sx = builder.suffix();
    proof {
        reveal_with_fuel(lib::spec_suf_count_upto, 7);
        reveal_with_fuel(lib::spec_suf_hits_upto, 7);
        assert(sx.lits@.len() == 2);
        assert(sx.map@ == seq![1, 2]);
        assert(sx.longest == 8);
        assert(sx.lits@.index(0)@ == seq![0x73]);
        assert(sx.lits@.index(1)@ == seq![0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]);
        // the windows (compute on the pure literals; the candidate
        // bridges via the path postconditions)
        assert(lib::spec_window(seq![0x61u8, 0x2fu8, 0x62u8, 0x2fu8, 0x63u8,
            0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8], 8, true)
            == seq![0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8]) by (compute_only);
        assert(lib::spec_window(seq![0x66u8, 0x6fu8, 0x6fu8, 0x2eu8, 0x72u8, 0x73u8], 8, true)
            == seq![0x66u8, 0x6fu8, 0x6fu8, 0x2eu8, 0x72u8, 0x73u8]) by (compute_only);
        assert(lib::spec_window(seq![0x61u8, 0x73u8], 8, true)
            == seq![0x61u8, 0x73u8]) by (compute_only);
        // the hit/miss facts over the suffix panes: the tail-8 pane
        // "/main.rs" ends in "s" and IS the "/main.rs" literal
        assert(seq![0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8].subrange(7, 8)
            == seq![0x73u8]) by (compute_only);
        assert(seq![0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8].subrange(0, 8)
            == seq![0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8]) by (compute_only);
        assert(lib::spec_suf_hit(sx.lits@,
            seq![0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8], 0));
        assert(lib::spec_suf_hit(sx.lits@,
            seq![0x2fu8, 0x6du8, 0x61u8, 0x69u8, 0x6eu8, 0x2eu8, 0x72u8, 0x73u8], 1));
        assert(seq![0x66u8, 0x6fu8, 0x6fu8, 0x2eu8, 0x72u8, 0x73u8].subrange(5, 6)
            == seq![0x73u8]) by (compute_only);
        assert(lib::spec_suf_hit(sx.lits@, seq![0x66u8, 0x6fu8, 0x6fu8, 0x2eu8, 0x72u8, 0x73u8], 0));
        assert(!lib::spec_suf_hit(sx.lits@, seq![0x66u8, 0x6fu8, 0x6fu8, 0x2eu8, 0x72u8, 0x73u8], 1));
        assert(seq![0x61u8, 0x73u8].subrange(1, 2)
            == seq![0x73u8]) by (compute_only);
        assert(lib::spec_suf_hit(sx.lits@, seq![0x61u8, 0x73u8], 0));
        assert(!lib::spec_suf_hit(sx.lits@, seq![0x61u8, 0x73u8], 1));
    }
    let s = GlobSetMatchStrategyS::Suffix(sx);
    let c_main = c_main_path();
    let c_foo = c_foo_rs();
    let c_as = c_asp();
    assert(spec_gsm_matches_all(&s, &c_main) == true);
    assert(spec_gsm_is_match(&s, &c_main) == true);
    assert(spec_gsm_matches_list(&s, &c_main) == seq![1, 2]);
    assert(spec_gsm_is_match(&s, &c_foo) == true);
    assert(spec_gsm_matches_all(&s, &c_foo) == false);   // the arm's msu row (1 of 2)
    assert(spec_gsm_matches_list(&s, &c_foo) == seq![1]);
    assert(spec_gsm_is_match(&s, &c_as) == true);
    assert(spec_gsm_matches_all(&s, &c_as) == false);    // the arm's msu row (1 of 2)
    assert(spec_gsm_matches_list(&s, &c_as) == seq![1]);
    assert(spec_gsm_list_nonempty_iff(&s, &c_as));
}

// dpb: [Suf("s"), Suf("s")] over "ab" -- the pane never ends in "s"
// (the null duplicate probe; GL7's registered "intent unreached" row).
fn dpb_checks() {
    let mut builder = MultiStrategyBuilder::new();
    builder.add(0, b_s());
    builder.add(1, b_s());
    proof {
        assert(builder.map@ == seq![0, 1]);
        assert(builder.longest == 1);
    }
    let sx = builder.suffix();
    proof {
        reveal_with_fuel(lib::spec_suf_count_upto, 7);
        reveal_with_fuel(lib::spec_suf_hits_upto, 7);
        assert(sx.map@ == seq![0, 1]);
        assert(sx.longest == 1);
        assert(sx.lits@.index(0)@ == seq![0x73]);
        assert(sx.lits@.index(1)@ == seq![0x73]);
        assert(lib::spec_window(seq![0x61u8, 0x62u8], 1, true)
            == seq![0x62u8]) by (compute_only);
        assert(seq![0x62u8].subrange(0, 1) == seq![0x62u8]) by (compute_only);
        assert(sx.lits@.index(0)@ == seq![0x73]);
        assert(sx.lits@.index(0)@.len() == 1);
        assert(sx.lits@.index(0)@.index(0) == 0x73u8);
        assert(seq![0x62u8].index(0) == 0x62u8);
        vstd::seq::lemma_seq_subrange_index(seq![0x62u8], 0, 1, 0);
        assert(seq![0x62u8].subrange(0, 1).index(0) == seq![0x62u8].index(0));
        assert(!lib::spec_suf_hit(sx.lits@, seq![0x62u8], 0));
        assert(!lib::spec_suf_hit(sx.lits@, seq![0x62u8], 1));
    }
    let s = GlobSetMatchStrategyS::Suffix(sx);
    let c = c_abp();
    assert(spec_gsm_is_match(&s, &c) == false);        // IM dpb 6162 = false
    assert(spec_gsm_matches_all(&s, &c) == false);    // MA dpb 6162 = false
    assert(spec_gsm_matches_list(&s, &c) == Seq::empty());   // MS dpb 6162 = []
    assert(spec_gsm_list_nonempty_iff(&s, &c));
}

// dpb2 (GL8 additive): the same duplicate column over "as" -- both
// ids report, matches_all counts two-of-two (the probe's intended
// geometry, now reached).
fn dpb2_checks() {
    let mut builder = MultiStrategyBuilder::new();
    builder.add(0, b_s());
    builder.add(1, b_s());
    let sx = builder.suffix();
    proof {
        reveal_with_fuel(lib::spec_suf_count_upto, 7);
        reveal_with_fuel(lib::spec_suf_hits_upto, 7);
        assert(sx.map@ == seq![0, 1]);
        assert(sx.longest == 1);
        assert(sx.lits@.index(0)@ == seq![0x73]);
        assert(sx.lits@.index(1)@ == seq![0x73]);
        assert(lib::spec_window(seq![0x61u8, 0x73u8], 1, true)
            == seq![0x73u8]) by (compute_only);
        assert(seq![0x73u8].subrange(0, 1) == seq![0x73u8]) by (compute_only);
        assert(lib::spec_suf_hit(sx.lits@, seq![0x73u8], 0));
        assert(lib::spec_suf_hit(sx.lits@, seq![0x73u8], 1));
    }
    let s = GlobSetMatchStrategyS::Suffix(sx);
    let c = c_asp();
    assert(spec_gsm_is_match(&s, &c) == true);         // IM dpb2 6173 = true
    assert(spec_gsm_matches_all(&s, &c) == true);      // MA dpb2 6173 = true
    assert(spec_gsm_matches_list(&s, &c) == seq![0, 1]);  // MS dpb2 6173 = [0, 1]
    assert(spec_gsm_list_nonempty_iff(&s, &c));
}

} // verus!

fn main() {}
