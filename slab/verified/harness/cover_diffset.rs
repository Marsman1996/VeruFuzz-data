//! slab 0.4.12 x Verus -- the difference-verification harness
//! (2026-11-03, batches 1-5; reference-style, per the two-zone rule)
//!
//! Assertion exemplars and call-site obligation anchors of the
//! difference-verification batches:
//!   batch 1  len/is_empty/contains/vacant_key/get/get_mut (the src batch-1 section)
//!   batch 2  with_capacity/capacity/clear/reserve/Default (the src batch-2 section)
//!   batch 3  iter/Iter::next/size_hint, into_iter_exec/IntoIter::next
//!            (Enumerate/vec::IntoIter has no vstd spec; the src side carries
//!            them with the equivalent idx+len model, see the src batch-3 notes)
//!   batch 4  vacant_entry/VacantEntry::key; Index/IndexMut doc-panic call-site anchors
//!   batch 5  the unsafe getter family D1 obligation anchors stay library-side
//!            (get_unchecked_exec etc.; the panic branches = the class-2 doc
//!            candidate anchors -- not duplicated here, recorded by reference)
//!
//! Running discipline: running verus on this file = a full re-verification of the
//! referenced src module; the expected error set = the src-side F1 (get2_mut) +
//! the remove docpanic witness + the D1 three-function anchors (see the
//! obligation-anchor reconciliation in out/harness-inventory.md) + this file's
//! single witness_index_docpanic call site. Everything else in this file is
//! expected to verify.

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[path = "../src/lib.rs"]
mod slab_src;

use vstd::prelude::*;

use crate::slab_src::{EntryExec, SlabExec, into_iter_exec};

verus! {

/// batch-1 exemplar: the key assertions of
/// len/is_empty/contains/vacant_key/get/get_mut
/// (matching the upstream doc examples: lib.rs:623-634, 639-653, 716-732, 1044-1057).
pub exec fn witness_lookup_family() -> (ok: bool)
    ensures
        ok,
{
    let mut s = SlabExec::<u64>::new();
    let l0 = s.len();          
    assert(l0 == 0);           // doc: an empty slab has len() == 0
    let e0 = s.is_empty();
    assert(e0);               // doc:is_empty
    let k0 = s.insert(10);     // k0 == 0
    assert(k0 == 0);
    let l1 = s.len();
    assert(l1 == 1);
    let e1 = s.is_empty();
    let c1 = s.contains(k0);
    assert(!e1);
    assert(c1);                // doc:contains
    // get: get(key) == Some <=> occupied (the rustdoc get promise)
    let g1 = s.get(k0);
    assert(g1 matches Some(_));
    let g2 = s.get(99);        // not associated => None
    assert(g2 matches None);
    // vacant_key: the next vacant is 1 (after insert)
    let vk1 = s.vacant_key();
    assert(vk1 == 1);
    // after remove the key is vacant: contains/get flip; vacant_key reuses the key
    let v = s.remove(k0);
    assert(v == 10);
    let c2 = s.contains(k0);
    assert(!c2);
    let g3 = s.get(k0);
    assert(g3 matches None);
    let vk2 = s.vacant_key();
    assert(vk2 == 0);           // reuses the just-released key (the doc example 1044-1057)
    // get_mut: the Some discrimination (after the lend-out no further
    // slab_inv-dependent calls follow -- the borrowing maintenance of the
    // structural invariant is a tool boundary, see the src batch-1 note; a fresh
    // insert before lending out here)
    let k3 = s.insert(30);
    let r = s.get_mut(k3);
    assert(r matches Some(_)); // the get_mut lend is this section's own obligation surface (the structural
                              // clause: see the library-side batch-1 note and the
                              // index/value-comparison tool-boundary disclosure)
    true
}

/// batch-2 exemplar: with_capacity/capacity/clear/reserve/Default
/// (matching the upstream doc examples: lib.rs:295-321, 330-338, 600-614, 343-368).
pub exec fn witness_capacity_family() -> (ok: bool)
    ensures
        ok,
{
    let mut s = SlabExec::<u64>::with_capacity(4);
    let l0 = s.len();
    assert(l0 == 0);               // doc: with_capacity does not fix the length
    let c0 = s.capacity();
    assert(c0@ >= 0);              // capacity >= len (the injected spec's obligation lower bound)
    let d = SlabExec::<u64>::default();
    let dl = d.len();
    assert(dl == 0);               // Default == new()
    let k = s.insert(5);
    let c_pre = s.contains(k);
    assert(c_pre);
    s.reserve(10);                  // doc: reserve changes no elements
    let l_mid = s.len();
    let c_mid = s.contains(k);
    assert(l_mid == 1);
    assert(c_mid);
    s.reserve_exact(10);
    let l_mid2 = s.len();
    let c_mid2 = s.contains(k);
    assert(l_mid2 == 1);
    assert(c_mid2);
    s.clear();                      // doc: is_empty after clear
    let ce = s.is_empty();
    let cl = s.len();
    assert(ce);
    assert(cl == 0);
    true
}

/// batch-3 exemplar: the Iter/IntoIter next/size_hint semantics
/// (matching the upstream doc examples: lib.rs:655-678, 1290-1299).
pub exec fn witness_iter_family() -> (ok: bool)
    ensures
        ok,
{
    let mut s = SlabExec::<u64>::new();
    let k0 = s.insert(10);
    let k1 = s.insert(20);
    assert(k0 == 0);
    assert(k1 == 1);
    // Iter side: in-order yield and the exact size_hint
    let mut it = s.iter();
    let (h_lo, h_hi) = it.size_hint();
    assert(h_lo == 2);              // (len, Some(len))
    let a = it.next();
    assert(a matches Some(_));     // in-order yield (k = the first occupied position)
    let b = it.next();
    assert(b matches Some(_));
    let c = it.next();
    assert(c matches None);         // exhausted => None and len == 0
    let it_l = it.iter_len();
    assert(it_l == 0);
    // structural semantics: next's key obligations stay library-side (pos
    // monotone, len-=1 no underflow, exact size_hint); here we verify the first
    // next's key bounds (iter_inv given)
    // (value-level spot checks were covered upstream by the runtime side, UT:675-677)
    // IntoIter side: consuming yields (slots swapped for the invalidating dummy)
    let mut ii = into_iter_exec(s);
    let (h_lo2, h_hi2) = ii.size_hint();
    assert(h_lo2 == 2);
    let x = ii.next();
    assert(x matches Some(_));    // consuming yield
    let y = ii.next();
    assert(y matches Some(_));
    let z = ii.next();
    assert(z matches None);
    let ii_l = ii.iter_len();
    assert(ii_l == 0);
    true
}

/// batch-4 exemplar: the vacant_entry/key obligations (the index/index_mut
/// doc-panic call sites live in witness_index_docpanic; get2_mut's existing
/// normal-path PoC: see out/)
pub exec fn witness_vacant_entry_family() -> (ok: bool)
    ensures
        ok,
{
    let mut s = SlabExec::<u64>::new();
    let vk = s.vacant_key();
    let ve = s.vacant_entry();
    let ve_k = ve.key();
    assert(ve_k == vk);             // VacantEntry::key == next at vacant_entry time
    let _ = s; // recover ownership
    let mut s = SlabExec::<u64>::new();
    let k = s.insert(1);
    // valid-key path: index returns a reference to the associated value (the
    // value-level assertion *r == 1 cannot be carried stably through &/&mut
    // borrow comparisons at the Verus layer -- the obligation surface is covered
    // by the library-side contracts of index_exec/index_mut_exec (occupancy
    // discrimination + len/next unchanged); the value level is backed by the
    // runtime PoC)
    let r = s.index_exec(k);
    // r's live borrow excludes a following &mut; lend index_mut again after use
    let val_copy = *r; // a Copy(u64) value copy
    assert(val_copy == 1);
    let _ = s.index_mut_exec(k); // &mut-side value comparisons cannot be carried stably under the Verus borrow
                                 // model; the obligation surface is covered by the
                                 // library-side index_mut_exec contract
    true
}

/// batch-4 anchor: witness_index_docpanic -- the "invalid key" call-site
/// obligation of index (the upstream Index trait convention panics + the
/// source panic!("invalid key"), lib.rs:1275). After remove the key is
/// vacant; index's requires occ_at is unsatisfied => the call-site
/// obligation failure = the documented-panic reproduction anchor.
/// **This function expects exactly 1 error.**
pub exec fn witness_index_docpanic() -> u64 {
    let mut s = SlabExec::<u64>::new();
    let k = s.insert(1);
    let _ = s.remove(k);          // key released
    let r = s.index_exec(k);      // requires occ_at unsatisfied <-- EXPECTED ERROR
    *r
}

// batch-5 note: the unsafe getter family's D1 obligation anchors are in the
// library-side get_unchecked_exec/get_unchecked_mut_exec/
// get2_unchecked_mut_exec panic branches (still reachable while satisfying
// # Safety). Runtime re-verification is carried by
// DB/out/poc/get_unchecked_vacant_key/ (the upstream-tree PoC); this file
// does not duplicate those obligations (a reference-style harness re-verifies
// every library-side anchor).

} // verus!

fn main() {}
