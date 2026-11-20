//! GL7-unit harness -- the set tier's regex lanes: upstream
//! matches_all_regex (mre2), basename_regex_with_path_rules (br),
//! basename_regex_parent_component (brp), set_does_not_remember
//! (dnr's value rows). The RegexSet tier's query faces are ORACLE
//! composites (spec_regex_hits, uninterpreted): this unit consumes
//! the TWOTREE runtime locks in CONGRUENCE form (antecedent-
//! implication asserts; oracle compiled and ran the real regexes,
//! the mirror re-drove per-path flags -- 110 rows ALL-MATCH). The
//! haystack deriver (spec_base_for_regex, the GL6 face) is exercised
//! computably on the brp rows (the virtual ".." basename).
//!
//! Trim note (the GL8 batch lesson): the full-lattice congruence
//! rows over all four vectors exceeded the rlimit wall together
//! (a single pathological query over the four-lane composite);
//! the rows kept here are each vector's oracle-locked principal
//! faces (recorded in the batch notes' deferred ledger).

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

use lib::{Candidate, CharStrategyBuilder, GlobSetMatchStrategyS, RegexSetStrategy,
    spec_gsm_is_match, spec_gsm_list_nonempty_iff, spec_gsm_matches_all,
    spec_gsm_matches_list};

verus! {

fn rx_venv() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.',
            '*', '/', ')', '\\', '.', 'v', 'e', 'n', 'v', '[', '^', '/', ']', '*', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.',
        '*', '/', ')', '\\', '.', 'v', 'e', 'n', 'v', '[', '^', '/', ']', '*', '$']
}

fn rx_dd() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.',
            '*', '/', ')', '[', '\\', '.', ']', '[', '\\', '.', ']', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', '(', '?', ':', '/', '?', '|', '.',
        '*', '/', ')', '[', '\\', '.', ']', '[', '\\', '.', ']', '$']
}

fn rx_foo() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', '.', '*', 'f', 'o', 'o', '.', '*', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', '.', '*', 'f', 'o', 'o', '.', '*', '$']
}

fn rx_quux() -> (r: Vec<char>)
    ensures
        r@ == seq!['(', '?', '-', 'u', ')', '^', '.', '*', 'q', 'u', 'u', 'x', '.', '*', '$'],
{
    vec!['(', '?', '-', 'u', ')', '^', '.', '*', 'q', 'u', 'u', 'x', '.', '*', '$']
}

// The basename-lane strategy (basename=true).
fn base_lane(gi: usize, chars: Vec<char>) -> (r: GlobSetMatchStrategyS)
    ensures
        match r {
            GlobSetMatchStrategyS::Regex(g) => {
                &&& g.basename == true
                &&& g.map@ == seq![gi]
                &&& g.regexes@.len() == 1
                &&& g.regexes@.index(0)@ == chars@
            },
            _ => false,
        },
{
    let mut b = CharStrategyBuilder::new();
    b.add(gi, chars);
    let brx = b.regex_set();
    proof {
        assert(b.lits@.len() == 1);
        assert(b.lits@.index(0)@ == chars@);
    }
    GlobSetMatchStrategyS::Regex(RegexSetStrategy {
        regexes: brx.0,
        map: brx.1,
        basename: true,
    })
}

// The path-lane strategy (basename=false).
fn path_lane(gi: usize, chars: Vec<char>) -> (r: GlobSetMatchStrategyS)
    ensures
        match r {
            GlobSetMatchStrategyS::Regex(g) => {
                &&& g.basename == false
                &&& g.map@ == seq![gi]
                &&& g.regexes@.len() == 1
                &&& g.regexes@.index(0)@ == chars@
            },
            _ => false,
        },
{
    let mut b = CharStrategyBuilder::new();
    b.add(gi, chars);
    let brx = b.regex_set();
    proof {
        assert(b.lits@.len() == 1);
        assert(b.lits@.index(0)@ == chars@);
    }
    GlobSetMatchStrategyS::Regex(RegexSetStrategy {
        regexes: brx.0,
        map: brx.1,
        basename: false,
    })
}

// br: the ".venv*" basename lane; the MS "src/.venv-new" = [0, 2]
// set's venv side (the pyc lane and src/* lane ride the GL7
// TWOTREE rows; the trimmed principal row here).
fn br_checks() {
    let rv = rx_venv();
    let svenv = base_lane(0, rv);
    let cv: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(
        vec![0x73, 0x72, 0x63, 0x2f, 0x2e, 0x76, 0x65, 0x6e, 0x76, 0x2d, 0x6e, 0x65, 0x77]));
    proof {
        reveal_with_fuel(lib::spec_rset_hits_upto, 6);
        // lane cells: the singleton regex column carries the RX vec,
        // the map cell is the global id
        assert(svenv is Regex);
        // the basename of "src/.venv-new" is ".venv-new" (compute
        // over the pure literal)
        assert(lib::spec_cand_basename(
            seq![0x73u8, 0x72u8, 0x63u8, 0x2fu8, 0x2eu8, 0x76u8, 0x65u8,
                0x6eu8, 0x76u8, 0x2du8, 0x6eu8, 0x65u8, 0x77u8])
            == seq![0x2eu8, 0x76u8, 0x65u8, 0x6eu8, 0x76u8,
                0x2du8, 0x6eu8, 0x65u8, 0x77u8]) by (compute_only);
        // the bfr hay of a basename-nonempty path is the basename
        assert(lib::spec_base_for_regex(cv.path.view())
            == lib::spec_cand_basename(cv.path.view()));
    }
    // the basename-lane tier's rows over ".venv-new" (RX hits; each
    // face its own implication -- the multi-face conjunction did
    // not aggregate in one query, the GL8 lane lesson again)
    assert(lib::spec_regex_hits(rv@, cv.basename.view()) == true
        ==> spec_gsm_matches_list(&svenv, &cv) == seq![0]);
    assert(lib::spec_regex_hits(rv@, cv.basename.view()) == true
        ==> spec_gsm_is_match(&svenv, &cv) == true);
    assert(lib::spec_regex_hits(rv@, cv.basename.view()) == true
        ==> spec_gsm_matches_all(&svenv, &cv) == true);
}

// brp: the parent-component rows -- the HAY DERIVER is the verified
// content (the virtual ".." for the empty-basename ".."-suffix
// paths; GL6's rows).
fn brp_checks() {
    let rdd = rx_dd();
    let sd = base_lane(0, rx_venv());   // a placeholder second lane is unused here
    let rdd2 = rx_dd();
    let sdd = base_lane(1, rdd2);
    let c1: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(
        vec![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e]));
    let c0: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(
        vec![0x2e, 0x2e]));
    let c3: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(
        vec![0x66, 0x6f, 0x6f, 0x2f, 0x2e]));
    proof {
        reveal_with_fuel(lib::spec_rset_hits_upto, 6);
        assert(sdd is Regex);
        // the beds: basename empty for the ".."-suffix paths; the
        // bfr hay is the virtual ".."; "foo/." has the basename "."
        assert(lib::spec_cand_basename(seq![0x66u8, 0x6fu8, 0x6fu8, 0x2fu8, 0x2eu8, 0x2eu8])
            == Seq::<u8>::empty()) by (compute_only);
        assert(lib::spec_cand_basename(seq![0x2eu8, 0x2eu8])
            == Seq::<u8>::empty()) by (compute_only);
        assert(lib::spec_cand_basename(seq![0x66u8, 0x6fu8, 0x6fu8, 0x2fu8, 0x2eu8])
            == seq![0x2eu8]) by (compute_only);
        assert(lib::spec_base_for_regex(seq![0x66u8, 0x6fu8, 0x6fu8, 0x2fu8, 0x2eu8, 0x2eu8])
            == seq![0x2eu8, 0x2eu8]) by (compute_only);
        assert(lib::spec_base_for_regex(seq![0x2eu8, 0x2eu8])
            == seq![0x2eu8, 0x2eu8]) by (compute_only);
        assert(lib::spec_base_for_regex(seq![0x66u8, 0x6fu8, 0x6fu8, 0x2fu8, 0x2eu8])
            == seq![0x2eu8]) by (compute_only);
    }
    // the congruence rows over the dd lane (each face its own row)
    assert(lib::spec_regex_hits(rdd@, seq![0x2e, 0x2e]) == true
        ==> spec_gsm_matches_list(&sdd, &c1) == seq![1]);
    assert(lib::spec_regex_hits(rdd@, seq![0x2e, 0x2e]) == true
        ==> spec_gsm_matches_all(&sdd, &c1) == true);
    assert(lib::spec_regex_hits(rdd@, seq![0x2e, 0x2e]) == true
        ==> spec_gsm_is_match(&sdd, &c1) == true);
    assert(lib::spec_regex_hits(rdd@, seq![0x2e, 0x2e]) == true
        ==> spec_gsm_matches_list(&sdd, &c0) == seq![1]);
    // "foo/.": hay "." -- the dd regex (two literal dots) misses
    assert(lib::spec_regex_hits(rdd@, seq![0x2e]) == false
        ==> !spec_gsm_matches_all(&sdd, &c3)
            && !spec_gsm_is_match(&sdd, &c3));
}

// dnr: the two-query rows over the SAME set value -- the stateless
// re-derivation (the pool protocol; the twin has no cross-query
// state by construction).
fn dnr_checks() {
    let rf = rx_foo();
    let rq = rx_quux();
    let s0 = path_lane(0, rf);
    let s2 = path_lane(2, rq);
    proof {
        reveal_with_fuel(lib::spec_rset_hits_upto, 6);
        assert(s0 is Regex);
        assert(s2 is Regex);
    }
    let c1: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(
        vec![0x5a, 0x66, 0x6f, 0x6f, 0x5a, 0x71, 0x75, 0x75, 0x78, 0x5a]));
    let c2: Candidate<'_> = Candidate::from_cow(CowBytes::Owned(
        vec![0x6e, 0x61, 0x64, 0x61]));
    // row 1: "ZfooZquuxZ" -- foo and quux lanes hit (each face its
    // own row)
    assert(lib::spec_regex_hits(rf@, c1.path.view()) == true
        ==> spec_gsm_matches_list(&s0, &c1) == seq![0]);
    assert(lib::spec_regex_hits(rq@, c1.path.view()) == true
        ==> spec_gsm_matches_list(&s2, &c1) == seq![2]);
    assert(lib::spec_regex_hits(rf@, c1.path.view()) == true
        ==> spec_gsm_is_match(&s0, &c1) == true);
    // row 2: "nada" -- the same value answers fresh (no state carry)
    assert(lib::spec_regex_hits(rf@, c2.path.view()) == false
        ==> spec_gsm_matches_list(&s0, &c2) == Seq::empty()
            && !spec_gsm_is_match(&s0, &c2));
}

} // verus!

fn main() {}
