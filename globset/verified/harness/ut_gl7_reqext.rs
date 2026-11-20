//! GL7-unit harness -- the set tier's RequiredExtension vectors:
//! upstream matches_all_required_extensions (mre, this arm), the
//! cross-key probe rq (["x/m*.a", "y/n*.b"] -- the GL7 suspects #1
//! geometry; under the PR3613 guard the two-key store answers
//! false upfront while matches still reports the hitting key's
//! id), the duplicate-key probe rqa, and the GL8 ext-empty row
//! rq2 ("noext": the candidate.ext empty short-circuit,
//! lib.rs:917-919/935-938's own gate).
//!
//! Value provenance: the TWOTREE lock (GL7 102 + GL8 rq2). The
//! regex columns are the ORACLE's compiled strings (the GL8 RX
//! rows); the HIT values are the runtime leg's lock, consumed in
//! CONGRUENCE form (antecedent-implication asserts over the
//! uninterpreted oracle face spec_regex_hits -- the GL4 contract for
//! oracle-loaded rows).

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

use lib::{Candidate, GlobSetMatchStrategyS, RequiredExtensionStrategyBuilder,
    spec_gsm_is_match, spec_gsm_list_nonempty_iff, spec_gsm_matches_all,
    spec_gsm_matches_list};

verus! {

// The extension byte columns and the regex columns (RX rows, the
// oracle's own compiled strings).
fn b_rs() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x72, 0x73],
{
    vec![0x2e, 0x72, 0x73]
}

fn b_a() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x61],
{
    vec![0x2e, 0x61]
}

fn b_b() -> (r: Vec<u8>)
    ensures r@ == seq![0x2e, 0x62],
{
    vec![0x2e, 0x62]
}

fn rx_mre_m() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|',
            '.', '*', '/', ')', ')', 'm', '.', '*', '\\', '.', 'r', 's', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|',
        '.', '*', '/', ')', ')', 'm', '.', '*', '\\', '.', 'r', 's', '$']
}

fn rx_mre_a() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', 'a', '/', '.', '*', '\\', '.', 'r', 's', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', 'a', '/', '.', '*', '\\', '.', 'r', 's', '$']
}

fn rx_rq_x() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', 'x', '/', 'm', '.', '*', '\\', '.', 'a', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', 'x', '/', 'm', '.', '*', '\\', '.', 'a', '$']
}

fn rx_rq_y() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', 'y', '/', 'n', '.', '*', '\\', '.', 'b', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', 'y', '/', 'n', '.', '*', '\\', '.', 'b', '$']
}

fn c_amain() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x61, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x61, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x2f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]);
    c
}


fn c_mainrs() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x72, 0x73]);
    c
}


fn c_alib() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x61, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73],
        r.basename.view() == seq![0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73],
        r.ext.view() == seq![0x2e, 0x72, 0x73],
{
    let v: Vec<u8> = vec![0x61, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x61, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) == seq![0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x61, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.path.view() == seq![0x61, 0x2f, 0x6c, 0x69, 0x62, 0x2e, 0x72, 0x73]);
    c
}


fn c_xmta() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x78, 0x2f, 0x6d, 0x74, 0x2e, 0x61],
        r.basename.view() == seq![0x6d, 0x74, 0x2e, 0x61],
        r.ext.view() == seq![0x2e, 0x61],
{
    let v: Vec<u8> = vec![0x78, 0x2f, 0x6d, 0x74, 0x2e, 0x61];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x78, 0x2f, 0x6d, 0x74, 0x2e, 0x61]) == seq![0x6d, 0x74, 0x2e, 0x61]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x78, 0x2f, 0x6d, 0x74, 0x2e, 0x61]) == seq![0x2e, 0x61]) by (compute_only);
    }
    assert(c.path.view() == seq![0x78, 0x2f, 0x6d, 0x74, 0x2e, 0x61]);
    c
}


fn c_ynzb() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x79, 0x2f, 0x6e, 0x7a, 0x2e, 0x62],
        r.basename.view() == seq![0x6e, 0x7a, 0x2e, 0x62],
        r.ext.view() == seq![0x2e, 0x62],
{
    let v: Vec<u8> = vec![0x79, 0x2f, 0x6e, 0x7a, 0x2e, 0x62];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x79, 0x2f, 0x6e, 0x7a, 0x2e, 0x62]) == seq![0x6e, 0x7a, 0x2e, 0x62]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x79, 0x2f, 0x6e, 0x7a, 0x2e, 0x62]) == seq![0x2e, 0x62]) by (compute_only);
    }
    assert(c.path.view() == seq![0x79, 0x2f, 0x6e, 0x7a, 0x2e, 0x62]);
    c
}


fn c_noext() -> (r: Candidate<'static>)
    ensures
        r.path.view() == seq![0x6e, 0x6f, 0x65, 0x78, 0x74],
        r.basename.view() == seq![0x6e, 0x6f, 0x65, 0x78, 0x74],
        r.ext.view() == Seq::<u8>::empty(),
{
    let v: Vec<u8> = vec![0x6e, 0x6f, 0x65, 0x78, 0x74];
    let c = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(lib::spec_cand_basename(seq![0x6e, 0x6f, 0x65, 0x78, 0x74]) == seq![0x6e, 0x6f, 0x65, 0x78, 0x74]) by (compute_only);
        assert(lib::spec_cand_ext(seq![0x6e, 0x6f, 0x65, 0x78, 0x74]) == Seq::<u8>::empty()) by (compute_only);
    }
    assert(c.path.view() == seq![0x6e, 0x6f, 0x65, 0x78, 0x74]);
    c
}


// mre's reqext arm: entries {1: RX_m, 2: RX_a} both under the ".rs"
// key (upstream matches_all_required_extensions). The conjunctive
// congruence rows pin the KEYED enumeration: matches_all walks ONLY
// the ".rs" entries (the candidate's own ext).
fn mre_arm_checks() {
    let mut b = RequiredExtensionStrategyBuilder::new();
    let rm = rx_mre_m();
    let ra = rx_mre_a();
    let ext1 = b_rs();
    b.add(1, ext1, rm);
    proof {
        assert(b.exts.keys@ == seq![ext1]);
        assert(b.exts.keys@.len() == 1);
        assert(b.exts.events@.len() == 1);
        assert(b.exts.events@.index(0).1 == 1);
    }
    let ext2 = b_rs();
    b.add(2, ext2, ra);
    proof {
        assert(b.exts.events@.len() == 2);
        assert(b.exts.events@.index(1).1 == 2);
        assert(b.exts.events@.index(0).1 == 1);
        reveal_with_fuel(lib::spec_reqext_hit_upto, 7);
        reveal_with_fuel(lib::spec_reqext_any_hit_upto, 7);
        reveal_with_fuel(lib::spec_reqext_all_hit_upto, 7);
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        assert(b.exts.keys@ == seq![ext1]);
        assert(b.exts.keys@.len() == 1);
        assert(b.regexes@.len() == 2);
        assert(b.exts.events@.len() == 2);
        assert(b.exts.events@.index(1).1 == 2);
        assert(b.exts.events@.index(0).1 == 1);
        assert(b.exts.events@.index(0).0 == 0);
        assert(b.exts.events@.index(1).0 == 0);
        assert(b.regexes@.index(0)@ == rm@);
        assert(b.regexes@.index(1)@ == ra@);
        assert(lib::spec_map_find(b.exts.keys@, seq![0x2e, 0x72, 0x73]) == Some(0int));
    }
    let rxe = b.build();
    let s = GlobSetMatchStrategyS::RequiredExtension(rxe);
    let c_main = c_amain();
    let c_top = c_mainrs();
    let c_lib = c_alib();
    // "a/main.rs": BOTH keyed patterns hit -> the conjunction passes
    assert(lib::spec_regex_hits(rm@, c_main.path.view()) == true
        && lib::spec_regex_hits(ra@, c_main.path.view()) == true
        ==> spec_gsm_matches_all(&s, &c_main) == true);
    assert(lib::spec_regex_hits(rm@, c_main.path.view()) == true
        && lib::spec_regex_hits(ra@, c_main.path.view()) == true
        ==> spec_gsm_is_match(&s, &c_main) == true);
    assert(lib::spec_regex_hits(rm@, c_main.path.view()) == true
        && lib::spec_regex_hits(ra@, c_main.path.view()) == true
        ==> spec_gsm_matches_list(&s, &c_main) == seq![1, 2]);
    // "main.rs": the keyed any accepts (RX_m alone), the conjunction
    // fails (RX_a misses): matches_all false per upstream's own row
    assert(lib::spec_regex_hits(rm@, c_top.path.view()) == true
        && lib::spec_regex_hits(ra@, c_top.path.view()) == false
        ==> spec_gsm_matches_all(&s, &c_top) == false);
    assert(lib::spec_regex_hits(rm@, c_top.path.view()) == true
        && lib::spec_regex_hits(ra@, c_top.path.view()) == false
        ==> spec_gsm_is_match(&s, &c_top) == true);
    assert(lib::spec_regex_hits(rm@, c_top.path.view()) == true
        && lib::spec_regex_hits(ra@, c_top.path.view()) == false
        ==> spec_gsm_matches_list(&s, &c_top) == seq![1]);
    // "a/lib.rs": the mirror case (RX_m misses, RX_a hits)
    assert(lib::spec_regex_hits(rm@, c_lib.path.view()) == false
        && lib::spec_regex_hits(ra@, c_lib.path.view()) == true
        ==> spec_gsm_matches_all(&s, &c_lib) == false);
    assert(lib::spec_regex_hits(rm@, c_lib.path.view()) == false
        && lib::spec_regex_hits(ra@, c_lib.path.view()) == true
        ==> spec_gsm_matches_list(&s, &c_lib) == seq![2]);
    // the all-miss conjunct: the any over an empty hit set is false
    assert(lib::spec_regex_hits(rm@, c_lib.path.view()) == false
        && lib::spec_regex_hits(ra@, c_lib.path.view()) == false
        ==> !spec_gsm_is_match(&s, &c_lib));
}

// rq: the CROSS-KEY probe -- the GL7 suspects #1 geometry in its
// verified form: the candidate "x/mt.a" carries ext ".a"; the
// store holds two ext buckets (".a" and ".b"), so the PR3613
// guard answers false for matches_all regardless of the regex
// oracle's answers, while matches_list still reports the ".a"
// bucket's hitting id [0] (mirror row "y/nz.b" the same with the
// keys swapped).
fn rq_cross_key_checks() {
    let mut b = RequiredExtensionStrategyBuilder::new();
    let rx = rx_rq_x();
    let ry = rx_rq_y();
    let rxa = rx_rq_x();
    let ryb = rx_rq_y();
    let ea = b_a();
    b.add(0, ea, rx);
    proof {
        assert(b.exts.keys@ == seq![ea]);
        assert(b.exts.events@.len() == 1);
        assert(b.exts.events@.index(0).1 == 0);
    }
    let eb = b_b();
    let ry1 = rx_rq_y();
    b.add(1, eb, ry1);
    proof {
        assert(b.exts.events@.len() == 2);
        assert(b.exts.events@.index(1).1 == 1);
        assert(b.exts.events@.index(0).1 == 0);
        reveal_with_fuel(lib::spec_reqext_hit_upto, 7);
        reveal_with_fuel(lib::spec_reqext_any_hit_upto, 7);
        reveal_with_fuel(lib::spec_reqext_all_hit_upto, 7);
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        assert(b.exts.keys@ == seq![ea, eb]);
        assert(b.exts.keys@.len() == 2);
        assert(b.exts.events@.len() == 2);
        assert(b.exts.events@.index(1).1 == 1);
        assert(b.exts.events@.index(0).1 == 0);
        assert(b.exts.events@.index(0).0 == 0);
        assert(b.exts.events@.index(1).0 == 1);
        assert(b.regexes@.index(0)@ == rxa@);
        assert(b.regexes@.index(1)@ == ryb@);
        assert(lib::spec_map_find(b.exts.keys@, seq![0x2e, 0x61]) == Some(0int));
        assert(lib::spec_map_find(b.exts.keys@, seq![0x2e, 0x62]) == Some(1int));
    }
    let rxe = b.build();
    let s = GlobSetMatchStrategyS::RequiredExtension(rxe);
    let c = c_xmta();
    let rxg = rx_rq_x();
    let ryg = rx_rq_y();
    // the suspects-#1 row, PR3613 guard re-anchored: the two-key
    // store answers false upfront (the guard), even with the ".a"
    // pattern's regex CONFIRMED hitting -- the pre-patch face
    // (the keyed walk over the ".a" key alone answering true) is
    // the F1 defect the PR's guard retires
    assert(lib::spec_regex_hits(rxg@, c.path.view()) == true
        && lib::spec_regex_hits(ryg@, c.path.view()) == false
        ==> spec_gsm_matches_all(&s, &c) == false);
    assert(lib::spec_regex_hits(rxg@, c.path.view()) == true
        && lib::spec_regex_hits(ryg@, c.path.view()) == false
        ==> spec_gsm_is_match(&s, &c) == true);
    assert(lib::spec_regex_hits(rxg@, c.path.view()) == true
        && lib::spec_regex_hits(ryg@, c.path.view()) == false
        ==> spec_gsm_matches_list(&s, &c) == seq![0]);
    // the mirror row: "y/nz.b" (ext ".b"), guard false the same way
    let c2 = c_ynzb();
    assert(lib::spec_regex_hits(ryg@, c2.path.view()) == true
        && lib::spec_regex_hits(rxg@, c2.path.view()) == false
        ==> spec_gsm_matches_all(&s, &c2) == false);
    assert(lib::spec_regex_hits(ryg@, c2.path.view()) == true
        && lib::spec_regex_hits(rxg@, c2.path.view()) == false
        ==> spec_gsm_matches_list(&s, &c2) == seq![1]);
}

// rqa: the DUPLICATE-KEY probe -- two copies of the same (ext,
// regex) row: both ids enter under ".a", matches_all counts
// two-of-two, matches_list reports both ids.
fn rqa_dup_key_checks() {
    let mut b = RequiredExtensionStrategyBuilder::new();
    let rx1 = rx_rq_x();
    let rx2 = rx_rq_x();
    let ea = b_a();
    b.add(0, ea, rx1);
    proof {
        assert(b.exts.events@.len() == 1);
        assert(b.exts.events@.index(0).1 == 0);
    }
    let ea2 = b_a();
    b.add(1, ea2, rx2);
    proof {
        assert(b.exts.events@.len() == 2);
        assert(b.exts.events@.index(1).1 == 1);
        assert(b.exts.events@.index(0).1 == 0);
        reveal_with_fuel(lib::spec_reqext_hit_upto, 7);
        reveal_with_fuel(lib::spec_reqext_any_hit_upto, 7);
        reveal_with_fuel(lib::spec_reqext_all_hit_upto, 7);
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        assert(b.exts.keys@ == seq![ea]);
        assert(b.exts.keys@.len() == 1);
        assert(b.exts.events@.len() == 2);
        assert(b.exts.events@.index(1).1 == 1);
        assert(b.exts.events@.index(0).1 == 0);
        assert(b.exts.events@.index(0).0 == 0);
        assert(b.exts.events@.index(1).0 == 0);
        assert(b.regexes@.index(0)@ == rx1@);
        assert(b.regexes@.index(1)@ == rx2@);
        assert(lib::spec_map_find(b.exts.keys@, seq![0x2e, 0x61]) == Some(0int));
    }
    let rxe = b.build();
    let s = GlobSetMatchStrategyS::RequiredExtension(rxe);
    let c = c_xmta();
    let rxq = rx_rq_x();
    assert(lib::spec_regex_hits(rxq@, c.path.view()) == true
        ==> spec_gsm_matches_all(&s, &c) == true);
    assert(lib::spec_regex_hits(rxq@, c.path.view()) == true
        ==> spec_gsm_is_match(&s, &c) == true);
    assert(lib::spec_regex_hits(rxq@, c.path.view()) == true
        ==> spec_gsm_matches_list(&s, &c) == seq![0, 1]);
    assert(lib::spec_regex_hits(rxq@, c.path.view()) == true
        ==> spec_gsm_list_nonempty_iff(&s, &c));
    // PR3613 twin consumption row: the unconditional soundness
    // direction (Part H2 th_reqext_guard_true_sound) on the
    // single-bucket true case -- patched truth forces the
    // whole-map enumeration, i.e. BOTH keyed regexes hit
    assert(lib::spec_reqext_store_wf(
        rxe.exts.keys@, rxe.exts.events@, rxe.regexes@)) by {
        assert(rxe.regexes@.len() == 2 && rxe.exts.events@.len() == 2);
        assert(rxe.exts.events@.index(0).0 == 0
            && rxe.exts.events@.index(1).0 == 0);
        assert(rxe.exts.keys@.len() == 1);
    }
    assert(lib::spec_regex_hits(rxq@, c.path.view()) == true
        ==> lib::spec_reqext_matches_all_enum(
            rxe.exts.keys@, rxe.exts.events@, rxe.regexes@,
            c.ext.view(), c.path.view()) == true);
}

// rq2: the ext-empty gate (GL8 additive row) -- "noext" has no dot:
// is_match/matches_all/matches_list all take the empty gate (NO
// regex consultation; the congruence quantifies over the oracle's
// answers to prove exactly that).
fn rq2_noext_checks() {
    let mut b = RequiredExtensionStrategyBuilder::new();
    let rxq = rx_rq_x();
    let rya = rx_rq_y();
    b.add(0, b_a(), rxq);
    b.add(1, b_b(), rya);
    let rxe = b.build();
    let s = GlobSetMatchStrategyS::RequiredExtension(rxe);
    let c = c_noext();
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        // c.ext is EMPTY (the noext candidate): no key can match an
        // empty extension, so the keyed lookups all return None
        assert(c.ext.view() == Seq::<u8>::empty());
        assert(lib::spec_map_find(b.exts.keys@, c.ext.view()) is None);
    }
    assert(spec_gsm_is_match(&s, &c) == false);     // IM rq2 6e6f657874 = false
    assert(spec_gsm_matches_all(&s, &c) == false); // MA rq2 6e6f657874 = false
    assert(spec_gsm_matches_list(&s, &c) == Seq::empty());  // MS = []
    assert(spec_gsm_list_nonempty_iff(&s, &c));
    // regardless of the regex oracle's answers (the gate precedes
    // any consultation)
    let rx2 = rx_rq_x();
    let ry2 = rx_rq_y();
    assert(lib::spec_regex_hits(rx2@, c.path.view()) == true
        && lib::spec_regex_hits(ry2@, c.path.view()) == true
        ==> spec_gsm_is_match(&s, &c) == false);
}

} // verus!

fn main() {}
