//! GL7-unit harness -- the set tier's extension vectors: upstream
//! matches_all_extensions (mea/meb) in KAT form.
//!
//! Value provenance: the GL7 TWOTREE lock (oracle==mirror== the
//! upstream test literals). Routing rides the oracle RT rows.

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

use lib::{Candidate, ExtensionStrategy, GlobSetMatchStrategyS, spec_gsm_is_match,
    spec_gsm_list_nonempty_iff, spec_gsm_matches_all, spec_gsm_matches_list};

verus! {

// The extension byte columns.
fn b_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x72, 0x73],
{
    vec![0x2e, 0x72, 0x73]
}

fn b_c() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x63],
{
    vec![0x2e, 0x63]
}

fn c_foo_a_rs() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x61, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x72, 0x73]) == seq![0x61, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x72, 0x73]);
    c
}


fn c_foo_a_c() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63],
        r.basename.view() == seq![0x61, 0x2e, 0x63],
        r.ext.view() == seq![0x2e, 0x63],
{
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63]) == seq![0x61, 0x2e, 0x63]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63]) == seq![0x2e, 0x63]) by (compute_only);
    }
    assert(c.path.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x61, 0x2e, 0x63]);
    c
}


// mea: [Ext(".rs"), Ext(".c")] -- two distinct extension keys; the
// matches_all singleton gate is barred (upstream
// matches_all_extensions first half).
fn mea_checks() {
    let mut es = ExtensionStrategy::new();
    let rs = b_rs();
    es.add(0, rs);
    proof {
        assert(es.0.keys@ == seq![rs]);
        assert(es.0.keys@.len() == 1);
    }
    let cdot = b_c();
    es.add(1, cdot);
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_has_scan, 4);
        assert(es.0.keys@ == seq![rs, cdot]);
        assert(es.0.keys@.len() == 2);
        assert(lib::spec_map_find(es.0.keys@, seq![0x2e, 0x72, 0x73]) == Some(0int));
        assert(lib::spec_map_find(es.0.keys@, seq![0x2e, 0x63]) == Some(1int));
        assert(lib::spec_hit_list(es.0.keys@, es.0.events@, seq![0x2e, 0x72, 0x73])
            == seq![0]);
        assert(lib::spec_hit_list(es.0.keys@, es.0.events@, seq![0x2e, 0x63])
            == seq![1]);
    }
    let s = GlobSetMatchStrategyS::Extension(es);
    let crs = c_foo_a_rs();
    let cc = c_foo_a_c();
    assert(spec_gsm_matches_all(&s, &crs) == false);  // MA mea 666f6f2f612e7273 = false
    assert(spec_gsm_matches_all(&s, &cc) == false);    // MA mea 666f6f2f612e63 = false
    assert(spec_gsm_is_match(&s, &crs) == true);       // IM mea 666f6f2f612e7273 = true
    assert(spec_gsm_is_match(&s, &cc) == true);       // IM mea 666f6f2f612e63 = true
    assert(spec_gsm_matches_list(&s, &crs) == seq![0]);
    assert(spec_gsm_matches_list(&s, &cc) == seq![1]);
    assert(spec_gsm_list_nonempty_iff(&s, &crs));
    assert(spec_gsm_list_nonempty_iff(&s, &cc));
}

// meb: [Ext(".rs"), Ext(".rs")] -- both patterns route to the same
// extension (sources "**/*.rs" vs "*.rs"); the merged single-key
// column passes the singleton gate (upstream
// matches_all_extensions second half).
fn meb_checks() {
    let mut es = ExtensionStrategy::new();
    let rs = b_rs();
    es.add(0, rs);
    proof {
        assert(es.0.keys@ == seq![rs]);
        assert(es.0.keys@.len() == 1);
    }
    let rs2 = b_rs();
    es.add(1, rs2);
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_has_scan, 4);
        assert(es.0.keys@ == seq![rs]);
        assert(es.0.keys@.len() == 1);
        assert(lib::spec_map_find(es.0.keys@, seq![0x2e, 0x72, 0x73]) == Some(0int));
        assert(lib::spec_hit_list(es.0.keys@, es.0.events@, seq![0x2e, 0x72, 0x73])
            == seq![0, 1]);
    }
    let s = GlobSetMatchStrategyS::Extension(es);
    let c = c_foo_a_rs();
    assert(spec_gsm_matches_all(&s, &c) == true);      // MA meb 666f6f2f612e7273 = true
    assert(spec_gsm_is_match(&s, &c) == true);
    assert(spec_gsm_matches_list(&s, &c) == seq![0, 1]);
    assert(spec_gsm_list_nonempty_iff(&s, &c));
}

} // verus!

fn main() {}
