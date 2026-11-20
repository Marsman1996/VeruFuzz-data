//! GL6 harness -- the ExtensionStrategy tier (upstream lib.rs:786-822,
//! KAT backbone lib.rs:1375-1376's ext rows plus the GM9 corners the
//! Candidate ext column carries: an ext map keyed by the DOT-INCLUSIVE
//! extension bytes).
//!
//! Upstream row content (resized to strategy form):
//!   "é.py" (index 8): candidate ext ".py" present in the map;
//!   ".rs" (GM9: dotfile leads its own ext family),
//!   "..rs" -> ".rs",
//!   "foo" (no dot) -> the empty-ext guard returns false,
//!   "foo/bar" (basename without dot) -> false,
//!   duplicates: same ext added twice merges [0, 1];
//!   matches_all (lib.rs:805-807): singleton map true, the two-key map
//!     false, empty-ext candidate false; byte-unequal exts miss.
//!
//! Grounding shape: candidates ride Owned vec! inputs (view pins
//! directly); model folding rides literal-arg compute stones and the
//! reveal fuel lanes, per ut_gl6_cand / ut_gl6_litf.

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

use lib::{Candidate, ExtensionStrategy, spec_cand_ext};

verus! {

fn ext_lit(s: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == s@,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> out@.index(k) == s@.index(k),
        decreases s.len() - i,
    {
        out.push(s[i]);
        i += 1;
    }
    out
}

// -------------------------------------------------------------------------
// Row 1: the singleton ext map -- one stored ext, the ext-bearing
// candidate matches; matches_all holds on the singleton.
// -------------------------------------------------------------------------

fn ext_singleton_rs() {
    let mut m = ExtensionStrategy::new();
    let rs_ext: Vec<u8> = vec![0x2e, 0x72, 0x73];
    m.add(0, rs_ext);
    // ".rs" file: GM9's dotfile row
    let v: Vec<u8> = vec![0x2e, 0x72, 0x73];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_ext(seq![0x2e, 0x72, 0x73]) == seq![0x2e, 0x72, 0x73]) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    assert(c.ext.view() == seq![0x2e, 0x72, 0x73]);
    let hit: bool = m.is_match(&c);
    assert(hit);
    let all: bool = m.matches_all(&c);
    assert(all);
    // matches_into extends with the singleton's own index list
    let mut out: Vec<usize> = Vec::new();
    m.matches_into(&c, &mut out);
    assert(out@ == seq![0usize]);
}

// -------------------------------------------------------------------------
// Row 2: the empty-ext guard (lib.rs:799-800 / 815-816): candidates
// without an extension never reach the map.
// -------------------------------------------------------------------------

fn ext_guard_no_dot() {
    let mut m = ExtensionStrategy::new();
    m.add(0, vec![0x2e, 0x72, 0x73]);
    // "foo": no embedded dot -> ext empty -> guarded false
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f];
    let c1: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f]) == Seq::empty()) by (compute_only);
    }
    assert(c1.ext.view() == Seq::empty());
    let hit1: bool = m.is_match(&c1);
    assert(!hit1);
    let mut out1: Vec<usize> = Vec::new();
    m.matches_into(&c1, &mut out1);
    assert(out1@ == Seq::empty());
    // "foo/bar": basename "bar" without dot -> same guard
    let vb: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72];
    let c2: Candidate = Candidate::from_cow(CowBytes::Owned(vb));
    proof {
        assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
            == Seq::empty()) by (compute_only);
    }
    assert(c2.ext.view() == Seq::empty());
    let hit2: bool = m.is_match(&c2);
    assert(!hit2);
}

// -------------------------------------------------------------------------
// Row 3: "..rs" -> ".rs" (GM9's liberal column: the extension includes
// the final dot, wherever it sits).
// -------------------------------------------------------------------------

fn ext_dotdot_rs() {
    let mut m = ExtensionStrategy::new();
    let rs_ext: Vec<u8> = vec![0x2e, 0x72, 0x73];
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    m.add(0, rs_ext);
    let v: Vec<u8> = vec![0x2e, 0x2e, 0x72, 0x73];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_ext(seq![0x2e, 0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
        assert(lib::spec_map_has(m.0.keys@, seq![0x2e, 0x72, 0x73]));
    }
    assert(c.ext.view() == seq![0x2e, 0x72, 0x73]);
    let hit: bool = m.is_match(&c);
    assert(hit);
}

// -------------------------------------------------------------------------
// Row 4: the non-ASCII basename row (upstream's é.py corpus row): the
// ext column of "é.py" is ".py".
// -------------------------------------------------------------------------

fn ext_e_py() {
    let mut m = ExtensionStrategy::new();
    let py_ext: Vec<u8> = vec![0x2e, 0x70, 0x79];
    proof {
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    m.add(8, py_ext);
    let v: Vec<u8> = vec![0xc3, 0xa9, 0x2e, 0x70, 0x79];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_ext(seq![0xc3, 0xa9, 0x2e, 0x70, 0x79])
            == seq![0x2e, 0x70, 0x79]) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
        assert(lib::spec_map_has(m.0.keys@, seq![0x2e, 0x70, 0x79]));
    }
    assert(c.ext.view() == seq![0x2e, 0x70, 0x79]);
    let hit: bool = m.is_match(&c);
    assert(hit);
    let mut out: Vec<usize> = Vec::new();
    m.matches_into(&c, &mut out);
    assert(out@ == seq![8usize]);
}

// -------------------------------------------------------------------------
// Row 5: duplicates merge in push order (the or_insert arm).
// -------------------------------------------------------------------------

fn ext_duplicates() {
    let mut m = ExtensionStrategy::new();
    let cext: Vec<u8> = vec![0x2e, 0x63];
    m.add(0, cext);
    let cext2: Vec<u8> = vec![0x2e, 0x63];
    proof {
        assert(cext2@ == seq![0x2e, 0x63]);
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
    }
    m.add(1, cext2);
    let n_keys: usize = m.0.len();
    assert(n_keys == 1);
    let v: Vec<u8> = vec![0x61, 0x2e, 0x63];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_ext(seq![0x61, 0x2e, 0x63]) == seq![0x2e, 0x63]) by (compute_only);
    }
    assert(c.ext.view() == seq![0x2e, 0x63]);
    let hit: bool = m.is_match(&c);
    assert(hit);
    let mut out: Vec<usize> = Vec::new();
    m.matches_into(&c, &mut out);
    assert(out@ == seq![0usize, 1usize]);
    // two adds, one distinct key: matches_all's singleton gate holds
    let all: bool = m.matches_all(&c);
    assert(all);
}

// -------------------------------------------------------------------------
// Row 6: the two-key map kills the singleton gate (matches_all false
// even for a matching candidate), and byte-unequal exts miss.
// -------------------------------------------------------------------------

fn ext_two_keys() {
    let mut m = ExtensionStrategy::new();
    m.add(0, vec![0x2e, 0x63]);
    m.add(1, vec![0x2e, 0x70, 0x79]);
    let v: Vec<u8> = vec![0x61, 0x2e, 0x63];
    let c1: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_ext(seq![0x61, 0x2e, 0x63]) == seq![0x2e, 0x63]) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 8);
        reveal_with_fuel(lib::spec_map_hits_upto, 8);
        // the merged column keeps ".c"'s entry (foreign stability),
        // whose nonempty hit list forces the find to be Some
        assert(lib::spec_hit_list(m.0.keys@, m.0.events@, seq![0x2e, 0x63])
            == seq![0usize]);
        assert(lib::spec_map_find(m.0.keys@, seq![0x2e, 0x63]) is Some);
        assert(lib::spec_map_has(m.0.keys@, seq![0x2e, 0x63]));
    }
    assert(c1.ext.view() == seq![0x2e, 0x63]);
    let hit1: bool = m.is_match(&c1);
    assert(hit1);
    let n_keys: usize = m.0.len();
    let all1: bool = m.matches_all(&c1);
    assert(!all1);
    // the stored-but-other candidate still matches its own key
    let v2: Vec<u8> = vec![0x61, 0x2e, 0x70, 0x79];
    let c2: Candidate = Candidate::from_cow(CowBytes::Owned(v2));
    proof {
        assert(spec_cand_ext(seq![0x61, 0x2e, 0x70, 0x79])
            == seq![0x2e, 0x70, 0x79]) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 6);
        reveal_with_fuel(lib::spec_map_hits_upto, 6);
        assert(lib::spec_map_has(m.0.keys@, seq![0x2e, 0x70, 0x79]));
    }
    assert(c2.ext.view() == seq![0x2e, 0x70, 0x79]);
    let hit2: bool = m.is_match(&c2);
    assert(hit2);
    // ".rs" is in no column here
    let v3: Vec<u8> = vec![0x61, 0x2e, 0x72, 0x73];
    let c3: Candidate = Candidate::from_cow(CowBytes::Owned(v3));
    proof {
        assert(spec_cand_ext(seq![0x61, 0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
        let rs_seq: Seq<u8> = seq![0x2e, 0x72, 0x73];
        let c_seq: Seq<u8> = seq![0x2e, 0x63];
        let py_seq: Seq<u8> = seq![0x2e, 0x70, 0x79];
        assert(rs_seq != c_seq);
        assert(rs_seq != py_seq);
        reveal_with_fuel(lib::spec_map_find_key_upto, 6);
        assert(!lib::spec_map_has(m.0.keys@, rs_seq));
    }
    assert(c3.ext.view() == seq![0x2e, 0x72, 0x73]);
    let hit3: bool = m.is_match(&c3);
    assert(!hit3);
}

} // verus!

fn main() {}
