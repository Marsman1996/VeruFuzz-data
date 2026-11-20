//! GL7-unit harness -- the set tier's prefix-lane vectors: the
//! upstream matches_all_prefix rows (mp) and the duplicate-prefix
//! probe (dpa) in their KAT form.
//!
//! Value provenance: the GL7 TWOTREE lock (oracle==mirror== upstream
//! test literals for mp; the dpa rows are the upstream-empirical
//! probe locks, GL7 notes' suspects ledger). Routing rides the
//! oracle RT rows.
//!
//! Rows (oracle run.txt):
//!   mp  [Pre("a"), Pre("ab"), Pre("ab/c")] :
//!       MA "ab/c/def"=true, "ab/cd"=true, "abc"=false,
//!          "ab/x"=false, "a"=false
//!   dpa [Pre("a"), Pre("a")] :
//!       IM "ab"=true, MS=[0, 1], MA "ab"=true  (the per-pattern-id
//!       duplicate granularity the AC contract pins)

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

fn b_a() -> (r: Vec<u8>)
    ensures r@ == seq![0x61],
{
    vec![0x61]
}

fn b_ab() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x62],
{
    vec![0x61, 0x62]
}

fn b_ab_c() -> (r: Vec<u8>)
    ensures r@ == seq![0x61, 0x62, 0x2f, 0x63],
{
    vec![0x61, 0x62, 0x2f, 0x63]
}


// The candidate helpers (the GL6 Owned-vec pattern, one helper per
// row; the construction-adjacent body asserts pin the path view,
// the constructor's mode/field postconditions carry it out).
fn c_ab_c_def() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x62, 0x2f, 0x63, 0x2f, 0x64, 0x65, 0x66],
        r.basename.view() == seq![0x64, 0x65, 0x66],
{
    let v: Vec<u8> = vec![0x61, 0x62, 0x2f, 0x63, 0x2f, 0x64, 0x65, 0x66];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x62, 0x2f, 0x63, 0x2f, 0x64, 0x65, 0x66])
            == seq![0x64, 0x65, 0x66]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x62, 0x2f, 0x63, 0x2f, 0x64, 0x65, 0x66]);
    c
}

fn c_ab_cd() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x62, 0x2f, 0x63, 0x64],
        r.basename.view() == seq![0x63, 0x64],
{
    let v: Vec<u8> = vec![0x61, 0x62, 0x2f, 0x63, 0x64];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x62, 0x2f, 0x63, 0x64])
            == seq![0x63, 0x64]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x62, 0x2f, 0x63, 0x64]);
    c
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

fn c_ab_x() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x62, 0x2f, 0x78],
        r.basename.view() == seq![0x78],
{
    let v: Vec<u8> = vec![0x61, 0x62, 0x2f, 0x78];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x62, 0x2f, 0x78])
            == seq![0x78]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x62, 0x2f, 0x78]);
    c
}

fn c_a() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61],
        r.basename.view() == seq![0x61],
{
    let v: Vec<u8> = vec![0x61];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61]) == seq![0x61]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61]);
    c
}

fn c_ab() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x62],
        r.basename.view() == seq![0x61, 0x62],
{
    let v: Vec<u8> = vec![0x61, 0x62];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x62])
            == seq![0x61, 0x62]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x62]);
    c
}

// mp: three escalating prefixes; longest caps the window at 4
// ("ab/c"), so the count-each gate reads the window's starts-pair
// column (upstream matches_all_prefix).
fn mp_checks() {
    let mut builder = MultiStrategyBuilder::new();
    builder.add(0, b_a());
    builder.add(1, b_ab());
    builder.add(2, b_ab_c());
    proof {
        assert(builder.map@ == seq![0, 1, 2]);
        assert(builder.longest == 4);
        assert(builder.literals@.len() == 3);
    }
    let px = builder.prefix();
    proof {
        reveal_with_fuel(lib::spec_pre_count_upto, 7);
        reveal_with_fuel(lib::spec_pre_hits_upto, 7);
        assert(px.lits@.len() == 3);
        assert(px.map@ == seq![0, 1, 2]);
    }
    let s = GlobSetMatchStrategyS::Prefix(px);
    let c_full = c_ab_c_def();
    let c_cd = c_ab_cd();
    let c_abc = c_abc();
    let c_abx = c_ab_x();
    let c_a = c_a();
    proof {
        // the grounding rows (p_scan's ladder, over the helper-bound
        // literal paths; windows by compute, cells, and per-hit facts)
        assert(px.lits@.index(0)@ == seq![0x61]);
        assert(px.lits@.index(1)@ == seq![0x61, 0x62]);
        assert(px.lits@.index(2)@ == seq![0x61, 0x62, 0x2f, 0x63]);
        assert(c_full.path.view() == seq![0x61, 0x62, 0x2f, 0x63, 0x2f, 0x64, 0x65, 0x66]);
        assert(c_cd.path.view() == seq![0x61, 0x62, 0x2f, 0x63, 0x64]);
        assert(c_abc.path.view() == seq![0x61, 0x62, 0x63]);
        assert(c_abx.path.view() == seq![0x61, 0x62, 0x2f, 0x78]);
        assert(c_a.path.view() == seq![0x61]);
        // windows (the pure spec rows compute)
        assert(lib::spec_window(seq![0x61, 0x62, 0x2f, 0x63, 0x2f, 0x64, 0x65, 0x66], 4, false)
            == seq![0x61, 0x62, 0x2f, 0x63]) by (compute_only);
        assert(lib::spec_window(c_full.path.view(), 4, false) == seq![0x61, 0x62, 0x2f, 0x63]);
        assert(lib::spec_window(seq![0x61, 0x62, 0x2f, 0x63, 0x64], 4, false)
            == seq![0x61, 0x62, 0x2f, 0x63]) by (compute_only);
        assert(lib::spec_window(c_cd.path.view(), 4, false) == seq![0x61, 0x62, 0x2f, 0x63]);
        assert(lib::spec_window(seq![0x61, 0x62, 0x63], 4, false)
            == seq![0x61, 0x62, 0x63]) by (compute_only);
        assert(lib::spec_window(c_abc.path.view(), 4, false) == seq![0x61, 0x62, 0x63]);
        assert(lib::spec_window(seq![0x61, 0x62, 0x2f, 0x78], 4, false)
            == seq![0x61, 0x62, 0x2f, 0x78]) by (compute_only);
        assert(lib::spec_window(c_abx.path.view(), 4, false) == seq![0x61, 0x62, 0x2f, 0x78]);
        assert(lib::spec_window(seq![0x61], 4, false) == seq![0x61]) by (compute_only);
        assert(lib::spec_window(c_a.path.view(), 4, false) == seq![0x61]);
        // "ab/c..." window hits all three
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8].subrange(0, 1) == seq![0x61u8]) by (compute_only);
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8].subrange(0, 2) == seq![0x61, 0x62]) by (compute_only);
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8].subrange(0, 4)
            == seq![0x61, 0x62, 0x2f, 0x63]) by (compute_only);
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8], 0));
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8], 1));
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8], 2));
        // "abc": prefix pair hits, the "/c" literal cannot
        assert(seq![0x61u8, 0x62u8, 0x63u8].subrange(0, 1) == seq![0x61u8]) by (compute_only);
        assert(seq![0x61u8, 0x62u8, 0x63u8].subrange(0, 2) == seq![0x61, 0x62]) by (compute_only);
        assert(px.lits@.index(2)@.len() > seq![0x61u8, 0x62u8, 0x63u8].len());
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x63u8], 0));
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x63u8], 1));
        assert(!lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x63u8], 2));
        // "ab/x": same shape
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8].subrange(0, 1) == seq![0x61u8]) by (compute_only);
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8].subrange(0, 2) == seq![0x61, 0x62]) by (compute_only);
        assert(px.lits@.index(2)@.len() == seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8].len());
        assert(px.lits@.index(2)@ == seq![0x61u8, 0x62u8, 0x2fu8, 0x63u8]);
        assert(px.lits@.index(2)@.index(3) == 0x63u8);
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8].index(3) == 0x78u8);
        vstd::seq::lemma_seq_subrange_index(seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8], 0, 4, 3);
        assert(seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8].subrange(0, 4).index(3)
            == seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8].index(3));
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8], 0));
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8], 1));
        assert(!lib::spec_pre_hit(px.lits@, seq![0x61u8, 0x62u8, 0x2fu8, 0x78u8], 2));
        // "a": only the head literal fits
        assert(seq![0x61u8].subrange(0, 1) == seq![0x61u8]) by (compute_only);
        assert(px.lits@.index(0)@ == seq![0x61]);
        assert(px.lits@.index(0)@.len() == 1);
        assert(px.lits@.index(1)@.len() > seq![0x61u8].len());
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8], 0));
        assert(!lib::spec_pre_hit(px.lits@, seq![0x61u8], 1));
        assert(!lib::spec_pre_hit(px.lits@, seq![0x61u8], 2));
    }
    assert(spec_gsm_matches_all(&s, &c_full) == true);  // MA mp 61622f632f646566 = true
    assert(spec_gsm_matches_all(&s, &c_cd) == true);    // MA mp 61622f6364 = true
    assert(spec_gsm_matches_all(&s, &c_abc) == false); // MA mp 616263 = false
    assert(spec_gsm_matches_all(&s, &c_abx) == false); // MA mp 61622f78 = false
    assert(spec_gsm_matches_all(&s, &c_a) == false);   // MA mp 61 = false
    assert(spec_gsm_is_match(&s, &c_abc) == true);     // "a"/"ab" hit the window
    assert(spec_gsm_is_match(&s, &c_a) == true);
    assert(spec_gsm_matches_list(&s, &c_a) == seq![0]);
    assert(spec_gsm_matches_list(&s, &c_abc) == seq![0, 1]);
    assert(spec_gsm_matches_list(&s, &c_full) == seq![0, 1, 2]);
    assert(spec_gsm_list_nonempty_iff(&s, &c_abc));
}

// dpa: the duplicate-prefix probe -- two copies of "a" both enter
// the column; the per-pattern-id scan reports each separately
// (upstream-empirical, the GL7 suspects ledger's signature row).
fn dpa_checks() {
    let mut builder = MultiStrategyBuilder::new();
    builder.add(0, b_a());
    builder.add(1, b_a());
    proof {
        assert(builder.map@ == seq![0, 1]);
        assert(builder.longest == 1);
    }
    let px = builder.prefix();
    proof {
        reveal_with_fuel(lib::spec_pre_count_upto, 7);
        reveal_with_fuel(lib::spec_pre_hits_upto, 7);
        assert(px.map@ == seq![0, 1]);
    }
    let s = GlobSetMatchStrategyS::Prefix(px);
    let c = c_ab();
    proof {
        // the grounding rows over the capped window "a"
        assert(c.path.view() == seq![0x61, 0x62]);
        assert(lib::spec_window(seq![0x61, 0x62], 1, false) == seq![0x61]) by (compute_only);
        assert(lib::spec_window(c.path.view(), 1, false) == seq![0x61]);
        assert(px.lits@.index(0)@ == seq![0x61]);
        assert(px.lits@.index(1)@ == seq![0x61]);
        assert(seq![0x61u8].subrange(0, 1) == seq![0x61u8]) by (compute_only);
        assert(px.lits@.index(0)@ == seq![0x61]);
        assert(px.lits@.index(0)@.len() == 1);
        assert(px.lits@.index(1)@ == seq![0x61]);
        assert(px.lits@.index(1)@.len() == 1);
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8], 0));
        assert(lib::spec_pre_hit(px.lits@, seq![0x61u8], 1));
    }
    assert(spec_gsm_is_match(&s, &c) == true);         // IM dpa 6162 = true
    assert(spec_gsm_matches_all(&s, &c) == true);      // MA dpa 6162 = true
    assert(spec_gsm_matches_list(&s, &c) == seq![0, 1]);  // MS dpa 6162 = [0, 1]
    assert(spec_gsm_list_nonempty_iff(&s, &c));
}

} // verus!

fn main() {}
