//! GL6 harness -- the LiteralStrategy tier: the mod-64 length bitmask
//! (upstream lib.rs:1361-1391, the literal_length_filter regression
//! resized to strategy theorem form).
//!
//! Upstream rows (lib.rs:1362-1390; values verbatim):
//!   lengths = [0, 1, 63, 64, 65, 127, 128, 129] -- "a"-repeats, all
//!     match and return their own index;
//!   plus "é.py" (index 8) and "foo\*bar" (backslash_escape parses the
//!     literal "foo*bar", index 9);
//!   negatives [2, 62, 66, 126, 130] do NOT match;
//!   duplicates: the same 65-length literal added twice --
//!     matches_all true, matches [0, 1], is_match("a") false,
//!     matches_all("a") false, is_match(b*65) false.
//! Residue view: the corpus mask keeps residue bits {0, 1, 5, 7, 63};
//! every negative length sits on a residue outside that set.
//!
//! Lane design (the GL6 fold discipline): the mask is a pure bit-or
//! chain -- the full 10-add corpus folds a literal mask constant with
//! zero map involvement; the negatives ride that bit lane directly.
//! The per-key positive rows and merge rows live in small per-family
//! corpora (column sizes where the add-effects fold has proven stable
//! -- see the mount probe); each row is the upstream assertion's
//! content on a set containing exactly the relevant keys.

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

use lib::{
    Candidate, LiteralStrategy, spec_may_len, spec_lenbit, spec_lit_is_match,
    lemma_len_filter_never_rejects,
};

verus! {

// The repeated-literal carrier: n copies of byte b (the corpus "a"-runs
// and the duplicates b-run).
fn rep(n: usize, b: u8) -> (r: Vec<u8>)
    ensures
        r@.len() == n,
        forall|k: int| 0 <= k < n ==> r@.index(k) == b,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> out@.index(k) == b,
        decreases n - i,
    {
        out.push(b);
        i += 1;
    }
    out
}

// The two extra corpus literals (exec bytes): "é.py" (5 bytes, two of
// them the two-byte UTF-8 of U+00E9) and "foo*bar" (the
// backslash_escape parse product of "foo\*bar").

fn lit_e_py() -> (r: Vec<u8>)
    ensures
        r@ == seq![0xc3, 0xa9, 0x2e, 0x70, 0x79],
{
    vec![0xc3, 0xa9, 0x2e, 0x70, 0x79]
}

fn lit_foo_star_bar() -> (r: Vec<u8>)
    ensures
        r@ == seq![0x66, 0x6f, 0x6f, 0x2a, 0x62, 0x61, 0x72],
{
    vec![0x66, 0x6f, 0x6f, 0x2a, 0x62, 0x61, 0x72]
}

// -------------------------------------------------------------------------
// Lane 1: the full-corpus mask (10 adds; the residue bits land on
// {0, 1, 5, 7, 63}). The chain of add-postconditions is pure bit-or,
// so the final mask value folds to a literal with no map folding; the
// six negative lengths of the upstream row ride this bit lane and need
// nothing else (is_match false follows from the length-gate false).
// Mask bits: 1<<0 | 1<<1 | 1<<5 | 1<<7 | 1<<63.
// -------------------------------------------------------------------------

fn lit_mask_corpus() {
    let mut s = LiteralStrategy::new();
    // named corpus literals (residues 0, 1, 63, 0, 1, 63, 0, 1, 5, 7)
    let l0 = rep(0, 0x61);
    s.add(0, l0);
    proof {
        assert(l0@.len() == 0);
        assert(lib::spec_lenbit(0int) == 1u64) by (compute_only);
        assert(lib::spec_lenbit(l0@.len() as int) == 1u64);
    }
    proof {
        assert((0u64 | 1u64) == 1u64) by (compute_only);
    }
    assert(s.lengths == 1u64);
    let l1 = rep(1, 0x61);
    s.add(1, l1);
    proof {
        assert(l1@.len() == 1);
        assert(lib::spec_lenbit(1int) == 2u64) by (compute_only);
        assert(lib::spec_lenbit(l1@.len() as int) == 2u64);
    }
    proof {
        assert((1u64 | 2u64) == 3u64) by (compute_only);
    }
    assert(s.lengths == 3u64);
    let l2 = rep(63, 0x61);
    s.add(2, l2);
    proof {
        assert(l2@.len() == 63);
        assert(lib::spec_lenbit(63int) == 0x8000000000000000u64) by (compute_only);
        assert(lib::spec_lenbit(l2@.len() as int) == 0x8000000000000000u64);
    }
    proof {
        assert((3u64 | 0x8000000000000000u64) == 0x8000000000000003u64) by (compute_only);
    }
    assert(s.lengths == 0x8000000000000003u64);
    let l3 = rep(64, 0x61);
    s.add(3, l3);
    proof {
        assert(l3@.len() == 64);
        assert(lib::spec_lenbit(64int) == 1u64) by (compute_only);
        assert(lib::spec_lenbit(l3@.len() as int) == 1u64);
    }
    let l4 = rep(65, 0x61);
    s.add(4, l4);
    proof {
        assert(l4@.len() == 65);
        assert(lib::spec_lenbit(65int) == 2u64) by (compute_only);
        assert(lib::spec_lenbit(l4@.len() as int) == 2u64);
    }
    let l5 = rep(127, 0x61);
    s.add(5, l5);
    proof {
        assert(l5@.len() == 127);
        assert(lib::spec_lenbit(127int) == 0x8000000000000000u64) by (compute_only);
        assert(lib::spec_lenbit(l5@.len() as int) == 0x8000000000000000u64);
    }
    let l6 = rep(128, 0x61);
    s.add(6, l6);
    proof {
        assert(l6@.len() == 128);
        assert(lib::spec_lenbit(128int) == 1u64) by (compute_only);
        assert(lib::spec_lenbit(l6@.len() as int) == 1u64);
    }
    let l7 = rep(129, 0x61);
    s.add(7, l7);
    proof {
        assert(l7@.len() == 129);
        assert(lib::spec_lenbit(129int) == 2u64) by (compute_only);
        assert(lib::spec_lenbit(l7@.len() as int) == 2u64);
    }
    let l8 = lit_e_py();
    s.add(8, l8);
    proof {
        assert(l8@.len() == 5);
        assert(lib::spec_lenbit(5int) == 32u64) by (compute_only);
        assert(lib::spec_lenbit(l8@.len() as int) == 32u64);
    }
    let l9 = lit_foo_star_bar();
    s.add(9, l9);
    proof {
        assert(l9@.len() == 7);
        assert(lib::spec_lenbit(7int) == 128u64) by (compute_only);
        assert(lib::spec_lenbit(l9@.len() as int) == 128u64);
    }
    // the composed mask value folds on the compute lane (literal or-chain)
    proof {
        assert(
            ((((((((((0u64 | 1u64) | 2u64) | 0x8000000000000000u64) | 1u64)
                | 2u64) | 0x8000000000000000u64) | 1u64) | 2u64) | 32u64)
                | 128u64) == 0x80000000000000a3u64
        ) by (compute_only);
    }
    assert(s.lengths == 0x80000000000000a3u64);
    // upstream rows: the six out-of-mask lengths never may-match, so
    // is_match is false for every "a"-run of those lengths
    proof {
        assert(!lib::spec_may_len(0x80000000000000a3u64, 2int)) by (compute_only);
        assert(!lib::spec_may_len(0x80000000000000a3u64, 62int)) by (compute_only);
        assert(!lib::spec_may_len(0x80000000000000a3u64, 66int)) by (compute_only);
        assert(!lib::spec_may_len(0x80000000000000a3u64, 126int)) by (compute_only);
        assert(!lib::spec_may_len(0x80000000000000a3u64, 130int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 0int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 1int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 63int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 64int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 65int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 127int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 128int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 129int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 5int)) by (compute_only);
        assert(lib::spec_may_len(0x80000000000000a3u64, 7int)) by (compute_only);
    }
    let m2: bool = s.is_match(&rep(2, 0x61));
    assert(!m2);
    let m62: bool = s.is_match(&rep(62, 0x61));
    assert(!m62);
    let m66: bool = s.is_match(&rep(66, 0x61));
    assert(!m66);
    let m126: bool = s.is_match(&rep(126, 0x61));
    assert(!m126);
    let m130: bool = s.is_match(&rep(130, 0x61));
    assert(!m130);
    let ml0: bool = s.may_match_length(0);
    assert(ml0);
    let ml1: bool = s.may_match_length(1);
    assert(ml1);
    let ml63: bool = s.may_match_length(63);
    assert(ml63);
    let ml64: bool = s.may_match_length(64);
    assert(ml64);
    let ml65: bool = s.may_match_length(65);
    assert(ml65);
}

// -------------------------------------------------------------------------
// Lane 2: the positive rows (each upstream "matches its own index"
// row on a minimal containing corpus; the added key's own-row content
// and the still-singleton map keep the fold at the sizes the
// add-effects fold handles).
// -------------------------------------------------------------------------

fn lit_pos_len0() {
    let mut s = LiteralStrategy::new();
    let lit = rep(0, 0x61);
    let q = rep(0, 0x61);
    proof {
        assert(q@.len() == 0);
        assert(lit@.len() == 0);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(0int) == 1u64) by (compute_only);
        assert((0u64 | 1u64) == 1u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(0, lit);
    proof {
        assert(lib::spec_may_len(1u64, 0int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 0int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    assert(s.lengths == 1u64);
    let hit: bool = s.is_match(&q);
    assert(hit);
    let got: Option<Vec<usize>> = s.literals.get(&q);
    assert(got is Some);
    let v: Vec<usize> = match got {
        Some(vv) => vv,
        None => Vec::new(),
    };
    assert(v@ == seq![0usize]);
}

fn lit_pos_len1() {
    let mut s = LiteralStrategy::new();
    let lit = rep(1, 0x61);
    let q = rep(1, 0x61);
    proof {
        assert(q@.len() == 1);
        assert(lit@.len() == 1);
        assert(forall|k: int| 0 <= k < 1 ==> q@.index(k) == 0x61);
        assert(forall|k: int| 0 <= k < 1 ==> lit@.index(k) == 0x61);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(1int) == 2u64) by (compute_only);
        assert((0u64 | 2u64) == 2u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(0, lit);
    proof {
        assert(lib::spec_may_len(2u64, 1int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 1int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    assert(s.lengths == 2u64);
    let hit: bool = s.is_match(&q);
    assert(hit);
}

fn lit_pos_len63() {
    let mut s = LiteralStrategy::new();
    let lit = rep(63, 0x61);
    let q = rep(63, 0x61);
    proof {
        assert(q@.len() == 63);
        assert(lit@.len() == 63);
        assert(forall|k: int| 0 <= k < 63 ==> q@.index(k) == 0x61);
        assert(forall|k: int| 0 <= k < 63 ==> lit@.index(k) == 0x61);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(63int) == 0x8000000000000000u64) by (compute_only);
        assert(lib::spec_lenbit(lit@.len() as int) == 0x8000000000000000u64);
        assert((0u64 | 0x8000000000000000u64) == 0x8000000000000000u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(0, lit);
    assert(s.lengths == 0x8000000000000000u64);
    proof {
        assert(lib::spec_may_len(0x8000000000000000u64, 63int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 63int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    let hit: bool = s.is_match(&q);
    assert(hit);
}

fn lit_pos_len64() {
    let mut s = LiteralStrategy::new();
    let lit = rep(64, 0x61);
    let q = rep(64, 0x61);
    proof {
        assert(q@.len() == 64);
        assert(lit@.len() == 64);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(64int) == 1u64) by (compute_only);
        assert(lib::spec_lenbit(lit@.len() as int) == 1u64);
        assert((0u64 | 1u64) == 1u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(0, lit);
    assert(s.lengths == 1u64);
    proof {
        assert(lib::spec_may_len(1u64, 64int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 64int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    let hit: bool = s.is_match(&q);
    assert(hit);
}

fn lit_pos_len65() {
    let mut s = LiteralStrategy::new();
    let lit = rep(65, 0x61);
    let q = rep(65, 0x61);
    proof {
        assert(q@.len() == 65);
        assert(lit@.len() == 65);
        assert(forall|k: int| 0 <= k < 65 ==> q@.index(k) == 0x61);
        assert(forall|k: int| 0 <= k < 65 ==> lit@.index(k) == 0x61);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(65int) == 2u64) by (compute_only);
        assert(lib::spec_lenbit(lit@.len() as int) == 2u64);
        assert((0u64 | 2u64) == 2u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(0, lit);
    assert(s.lengths == 2u64);
    proof {
        assert(lib::spec_may_len(2u64, 65int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 65int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    let hit: bool = s.is_match(&q);
    assert(hit);
    let b = rep(65, 0x62);
    // residue 1 passes the length gate (the collision face), and the
    // miss is a byte-content miss on the map column -- upstream's own
    // b*65 row rides both facts
    proof {
        assert(lib::spec_may_len(2u64, 65int)) by (compute_only);
        assert(b@.len() == 65);
        assert(q@.index(0) == 0x61);
        assert(b@.index(0) == 0x62);
        assert(b@ != q@);
        assert(!lib::spec_map_has(s.literals.keys@, b@));
    }
    let miss: bool = s.is_match(&b);
    assert(!miss);
}

fn lit_pos_epy() {
    let mut s = LiteralStrategy::new();
    let lit = lit_e_py();
    let q = lit_e_py();
    proof {
        assert(q@ == seq![0xc3, 0xa9, 0x2e, 0x70, 0x79]);
        assert(lit@ == seq![0xc3, 0xa9, 0x2e, 0x70, 0x79]);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(5int) == 32u64) by (compute_only);
        assert(lib::spec_lenbit(lit@.len() as int) == 32u64);
        assert((0u64 | 32u64) == 32u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(8, lit);
    assert(s.lengths == 32u64);
    proof {
        assert(lib::spec_may_len(32u64, 5int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 5int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    let hit: bool = s.is_match(&q);
    assert(hit);
}

fn lit_pos_fsb() {
    let mut s = LiteralStrategy::new();
    let lit = lit_foo_star_bar();
    let q = lit_foo_star_bar();
    proof {
        assert(q@ == seq![0x66, 0x6f, 0x6f, 0x2a, 0x62, 0x61, 0x72]);
        assert(lit@ == seq![0x66, 0x6f, 0x6f, 0x2a, 0x62, 0x61, 0x72]);
        assert(q@ == lit@);
        assert(lib::spec_lenbit(7int) == 128u64) by (compute_only);
        assert(lib::spec_lenbit(lit@.len() as int) == 128u64);
        assert((0u64 | 128u64) == 128u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 3);
        reveal_with_fuel(lib::spec_map_hits_upto, 3);
    }
    s.add(9, lit);
    assert(s.lengths == 128u64);
    proof {
        assert(lib::spec_may_len(128u64, 7int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 7int));
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    let hit: bool = s.is_match(&q);
    assert(hit);
}

// -------------------------------------------------------------------------
// Lane 3: the duplicates row (upstream lib.rs:1380-1390): the same
// 65-length literal added twice -- matches_all true, matches [0, 1],
// the "a" probe false on both is_match and matches_all, and a
// different 65-byte literal false.
// -------------------------------------------------------------------------

fn lit_duplicates() {
    let mut s = LiteralStrategy::new();
    let a65a = rep(65, 0x61);
    let a65b = rep(65, 0x61);
    proof {
        assert(a65a@ == a65b@);
        assert(a65a@.len() == 65);
        assert(lib::spec_lenbit(65int) == 2u64) by (compute_only);
        assert((0u64 | 2u64) == 2u64) by (compute_only);
        assert((2u64 | 2u64) == 2u64) by (compute_only);
        reveal_with_fuel(lib::spec_map_find_key_upto, 5);
        reveal_with_fuel(lib::spec_map_hits_upto, 5);
    }
    s.add(0, a65a);
    assert(s.lengths == 2u64);
    let k1 = rep(65, 0x61);
    proof {
        assert(k1@ == a65a@);
    }
    s.add(1, k1);
    assert(s.lengths == 2u64);
    // singleton key column; both indexes stack on the one entry
    let n_keys: usize = s.literals.len();
    assert(n_keys == 1);
    let q = rep(65, 0x61);
    proof {
        reveal_with_fuel(lib::spec_map_hits_upto, 4);
        reveal_with_fuel(lib::spec_map_find_key_upto, 4);
    }
    proof {
        assert(q@ == a65a@);
        assert(lib::spec_may_len(2u64, 65int)) by (compute_only);
        assert(lib::spec_may_len(s.lengths, 65int));
        assert(lib::spec_map_find(s.literals.keys@, q@) is Some);
        assert(lib::spec_map_has(s.literals.keys@, q@));
    }
    let hit: bool = s.is_match(&q);
    assert(hit);
    let all: bool = s.matches_all(&q);
    assert(all);
    let mut out: Vec<usize> = Vec::new();
    s.matches_into(&q, &mut out);
    assert(out@ == seq![0usize, 1usize]);
    // "a": the map misses (bit 1 is set, so the length gate alone
    // cannot explain the miss -- upstream's own row)
    let qa = rep(1, 0x61);
    proof {
        assert(lib::spec_may_len(2u64, 1int)) by (compute_only);
        assert(qa@.len() == 1);
        assert(qa@.index(0) == 0x61);
        assert(qa@ != s.literals.keys@.index(0)@);
        assert(!lib::spec_map_has(s.literals.keys@, qa@));
    }
    let miss1: bool = s.is_match(&qa);
    assert(!miss1);
    let all1: bool = s.matches_all(&qa);
    assert(!all1);
    // b*65: same class of miss, discriminating on bytes
    let qb = rep(65, 0x62);
    proof {
        assert(lib::spec_may_len(2u64, 65int)) by (compute_only);
        assert(qb@.len() == 65);
        assert(qb@.index(0) == 0x62);
        assert(qb@ != s.literals.keys@.index(0)@);
        assert(!lib::spec_map_has(s.literals.keys@, qb@));
    }
    let miss2: bool = s.is_match(&qb);
    assert(!miss2);
}

// -------------------------------------------------------------------------
// Lane 4: the never-rejects theorem pinned at the corpus lengths and
// residues (the mod-64 soundness family -- GL6's namesake content).
// -------------------------------------------------------------------------

proof fn len_sound_pins() {
    // a mask with residue-r set never rejects a length at residue r
    let m0: u64 = 1u64 << 0;
    let m1: u64 = 1u64 << 1;
    let m63: u64 = 1u64 << 63;
    lemma_len_filter_never_rejects(0u64, 0, 0);
    lemma_len_filter_never_rejects(0u64, 1, 1);
    lemma_len_filter_never_rejects(0u64, 63, 63);
    // the long three: full wraps plus residue
    lemma_len_filter_never_rejects(0u64, 64, 64);
    lemma_len_filter_never_rejects(0u64, 65, 65);
    lemma_len_filter_never_rejects(0u64, 127, 127);
    lemma_len_filter_never_rejects(0u64, 128, 128);
    lemma_len_filter_never_rejects(0u64, 129, 129);
    // collision tolerance: a 65-length literal also opens the door to
    // 1-length queries (and vice versa), still never rejecting own
    lib::lemma_len_filter_never_rejects_res(0u64, 65, 1);
    lib::lemma_len_filter_never_rejects_res(0u64, 1, 65);
    lib::lemma_len_filter_never_rejects_res(0u64, 129, 1);
    assert(spec_lenbit(65int) == spec_lenbit(1int)) by (compute_only);
    assert(spec_lenbit(128int) == spec_lenbit(0int)) by (compute_only);
    assert(spec_lenbit(127int) == spec_lenbit(63int)) by (compute_only);
}

} // verus!

fn main() {}
