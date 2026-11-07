//! slab 0.4.12 x Verus -- the UT assertion-exemplar harness
//! (reference-style; the two-zone coordination rule)
//! Upstream tokio-rs/slab @ 7d1d8ab0 (src/lib.rs line numbers cited per
//! annotation; inventory in DB/out/harness-inventory.md).
//!
//! Ownership criterion: this file is the "test/property transcription" -- the
//! pure-UT assertion transcription blocks of the upstream tests/slab.rs
//! (witness_insert_get_remove_one = tests/slab.rs:11-25, witness_try_remove =
//! :701-709, witness_retain = :222-249 replayed); the library-proper side
//! (the get2_mut F1 obligation anchor, the get2_mut_fixed repair
//! counter-proof, the witness_double_remove_docpanic documented-panic
//! call-site obligation, the witness_boundary_none_fixed control, the
//! f1_reachability_witness reachability witness) stays in verified/src/lib.rs.
//!
//! Reference-style structure: this file references, via
//! `#[path="../src/lib.rs"] mod slab_src;`, the representation layer, the
//! spec model, the counting and vacant-chain lemmas, and the API
//! transcriptions of verified/src/lib.rs (the verified fact source stays the
//! single src copy, not duplicated; the needed EntryExec/SlabExec/occ_at/
//! occ_cnt_prefix/drop_cnt_prefix/even_keep/odd_occ and the new/insert/
//! try_remove/remove/retain_even methods are already pub or pub-fielded in
//! src -- no visibility adjustments).
//!
//! Running discipline: running verus on this file = a full re-verification of
//! the referenced src module (including its expected errors = the F1
//! diagnostics + the 1 documented-panic call site, see the src file header
//! and the issue report; the obligations match a standalone src run, the
//! line numbers being src line numbers) + this file's 3 UT witnesses. This
//! file's own lemmas expect **0 errors** (all three blocks verified on
//! re-runs).

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[path = "../src/lib.rs"]
mod slab_src;

use vstd::prelude::*;
use vstd::seq::Seq;

use crate::slab_src::{
    EntryExec, SlabExec, occ_at, occ_cnt_prefix, drop_cnt_prefix, even_keep, odd_occ,
};

// =====================================================================
// key UT assertions -> witnesses/proof obligations (an upstream
// tests/slab.rs transcription)
// (moved from verified/src/lib.rs in the two-zone split; get2_mut's Some
// normal-path assertion lives in the runtime driver -- its F1-failed ensures
// cannot serve in caller proofs; tested empirically by f1_runtime_repro.)
// =====================================================================

verus! {

/// witness: the key assertions of tests/slab.rs:11-25 (insert_get_remove_one):
/// the insert->get mapping, remove returning the value, contains/length flips.
pub exec fn witness_insert_get_remove_one() -> (ok: bool)
    ensures ok,
{
    let mut s = SlabExec::<u64>::new();
    assert(s.len == 0); // UT:13 assert!(slab.is_empty())
    let key = s.insert(10); // UT:15
    assert(key == 0);
    assert(s.len == 1); // UT:19 assert!(!slab.is_empty())
    assert(s.entries@[key as int] == EntryExec::Occupied(10)); // UT:17-18
    let removed = s.remove(key); // UT:22
    assert(removed == 10); // UT:22 assert_eq!(slab.remove(key), 10)
    assert(s.len == 0); // UT:23-24
    assert(!occ_at(s.entries@, key as int)); // UT:24 get(key).is_none()
    true
}

/// witness: the key assertions of tests/slab.rs:701-709 (try_remove).
pub exec fn witness_try_remove() -> (ok: bool)
    ensures ok,
{
    let mut s = SlabExec::<u64>::new();
    let key = s.insert(1); // UT:704
    let a = s.try_remove(key); // UT:706
    assert(a == Some(1));
    let b = s.try_remove(key); // UT:707
    assert(b matches None);
    assert(s.len == 0);
    true
}

/// witness: the key assertions of tests/slab.rs:222-249 (retain): filtering,
/// key1 preserved (static) + the exact len; the slots failing the predicate
/// are dropped. The precondition state is built directly (two pushes) to
/// avoid the cross-step alias-expansion bookkeeping of the insert call chain.
/// UT:238-246 (after retain, insert reuses the dropped key2 slot, later keys
/// follow) was tested empirically by the "retain" branch of the runtime
/// driver f1_runtime_repro.rs: key == 1 == key2, and the next insert
/// yields 2.
pub exec fn witness_retain() -> (ok: bool)
    ensures ok,
{
    let mut v: Vec<EntryExec<u64>> = Vec::new();
    v.push(EntryExec::Occupied(0u64)); // UT:225 insert(0)
    let ghost es1 = v@; // es1 == empty.push(Occ(0))
    v.push(EntryExec::Occupied(1u64)); // UT:226 insert(1)
    let ghost pre_es = v@; // pre_es == es1.push(Occ(1))
    let mut s = SlabExec { entries: v, len: 2, next: 2 };
    proof {
        let ghost es0: Seq<EntryExec<u64>> = Seq::empty();
        vstd::seq::lemma_seq_push_len(es0, EntryExec::Occupied(0u64));
        assert(es1.len() == 1);
        vstd::seq::lemma_seq_push_index_same(es0, EntryExec::Occupied(0u64), 0int);
        vstd::seq::lemma_seq_push_index_same(es1, EntryExec::Occupied(1u64), 1int);
        vstd::seq::lemma_seq_push_index_different(es1, EntryExec::Occupied(1u64), 0int);
        reveal_with_fuel(occ_cnt_prefix, 4);
        assert(pre_es.index(0int) == EntryExec::Occupied(0));
        assert(pre_es.index(1int) == EntryExec::Occupied(1));
    }
    s.retain_even(); // UT:228-231 retain(|key, x| *x % 2 == 0)
    proof {
        // slot 0 is even (kept), slot 1 odd (dropped) -- instantiating the two
        // quantified postconditions and the exact count
        assert(pre_es.index(0int) matches EntryExec::Occupied(_));
        assert(even_keep(pre_es.index(0int)));
        assert(odd_occ(pre_es.index(1int)));
        reveal_with_fuel(drop_cnt_prefix, 3);
        assert(drop_cnt_prefix(pre_es, 2int) == 1);
        assert(s.len@ == 2 - 1);
    }
    assert(s.len == 1); // UT:233
    // UT:234 assert_eq!(slab[key1], 0) -- the key is preserved (a rustdoc promise)
    assert(s.entries@[0int] == EntryExec::Occupied(0));
    // UT:235 assert!(!slab.contains(key2)) (key2 = 1)
    assert(!occ_at(s.entries@, 1int));
    true
}

} // verus!

fn main() {}
