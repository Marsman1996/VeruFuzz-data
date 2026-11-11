//! bit-vec 0.10.1 x Verus -- coverage diff-set batch B harness
//! (insert/remove closure + capacity family).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here.
//! Coverage (out/harness-inventory.md diff-set batch B):
//!   - insert / remove (per-bit ensures: left bits keep, the op bit,
//!     right bits shift one across the within-block rewrite and the
//!     block cascade; upstream doc examples)
//!   - insert at block edges (0, tail-bit, full-block boundary)
//!   - remove at block edges (top bit of a block, block-boundary pop)
//!   - capacity / with_capacity / reserve / reserve_exact / push_within_capacity
//!     (the injected capacity model; the bits tier covers the length)
//!
//! The err-branch example of push_within_capacity (a push rejected at
//! exact capacity) needs the allocator's exact allocation, which the
//! injected capacity model leaves uninterpreted; only the ok-branch
//! (spare capacity provable from the >= 32 * storage blocks tier) is
//! machine-checked here.

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitvec_lib;

verus! {

use bitvec_lib::BitVec;
use bitvec_lib::bit_at;
use bitvec_lib::spec_bit_capacity;

// ---------------------------------------------------------------------------
// insert / remove: upstream doc examples as per-bit theorems
// ---------------------------------------------------------------------------

/// the doc example shape, built through push then insert(1, false)
fn ut_insert_doc_example()
{
    let mut b = bitvec_lib::new();
    b.push(true);
    b.push(true);
    b.insert(1, false);
    // b == [true, false, true]
    assert(b.nbits == 3);
    assert(bit_at(b.storage@, b.nbits, 0) == true);
    assert(bit_at(b.storage@, b.nbits, 1) == false);
    assert(bit_at(b.storage@, b.nbits, 2) == true) by {
        // the shifted tier: position 2 reads the old bit 1
        assert(bit_at(b.storage@, b.nbits, ((1usize) + 1) as usize)
            == bit_at(b.storage@, b.nbits, 2));
    }
}

/// the doc example shape, built through from_elem then insert(1, false)
fn ut_insert_doc_example_literal()
{
    let mut b = BitVec::from_elem(2, true);
    b.insert(1, false);
    assert(b.nbits == 3);
    assert(bit_at(b.storage@, b.nbits, 0) == true);
    assert(bit_at(b.storage@, b.nbits, 1) == false);
    assert(bit_at(b.storage@, b.nbits, 2) == true) by {
        // the shifted tier: position 2 reads the old bit 1
        assert(bit_at(b.storage@, b.nbits, ((1usize) + 1) as usize)
            == bit_at(b.storage@, b.nbits, 2));
    }
}

/// insert at 0 over a full 32-bit block (the fresh-block path)
fn ut_insert_head_full_block()
{
    let mut b = BitVec::from_elem(32, false);
    b.insert(0, true);
    assert(b.nbits == 33);
    assert forall|j: usize| j < 33 implies bit_at(b.storage@, b.nbits, j)
        == (j == 0) by {
        if j == 0 {
            assert(bit_at(b.storage@, b.nbits, 0) == true);
        } else {
            // the shifted tier: bit j reads the old bit j - 1 (all false)
            let i1 = (j - 1) as usize;
            assert((i1 as int) + 1 == (j as int));
            assert((((i1) + 1) as usize) == j);
            assert(bit_at(b.storage@, b.nbits, j) == false);
            assert(bit_at(b.storage@, b.nbits, j) == (j == 0));
        }
    }
}

/// insert at the block tail (b == 31, the intra-block top shift)
fn ut_insert_tail_bit()
{
    let mut b = BitVec::from_elem(31, true);
    b.insert(31, false);
    assert(b.nbits == 32);
    assert forall|j: usize| j < 32 implies bit_at(b.storage@, b.nbits, j)
        == (j != 31) by { };
}

/// insert across a block boundary (position 32 of a 2-block vector:
/// the bit inserted at 31 cascades the second block)
fn ut_insert_cascade_block()
{
    let mut b = BitVec::from_elem(64, false);
    b.set(31, true);
    b.insert(32, true);
    assert(b.nbits == 65);
    assert forall|j: usize| j < 65 implies bit_at(b.storage@, b.nbits, j)
        == (j == 31 || j == 32) by {
        if j == 32 {
            assert(bit_at(b.storage@, b.nbits, 32) == true);
        } else if j > 32 {
            // the shifted tier: bit j reads the old bit j - 1 (false here)
            let i1 = (j - 1) as usize;
            assert(bit_at(b.storage@, b.nbits, (i1 + 1) as usize)
                == bit_at(b.storage@, b.nbits, j));
        }
    }
}

/// upstream remove doc example (lib.rs:1955-1969):
///   b.push(true); b.push(false); b.push(false); b.push(true);
///   assert!(!b.remove(1));
///   assert!(b.eq_vec(&[true, false, true]));
fn ut_remove_doc_example()
{
    let mut b = bitvec_lib::new();
    b.push(true);
    b.push(false);
    b.push(false);
    b.push(true);
    let r = b.remove(1);
    assert(!r);
    assert(b.nbits == 3);
    assert(bit_at(b.storage@, b.nbits, 0) == true);
    assert(bit_at(b.storage@, b.nbits, 1) == false);
    assert(bit_at(b.storage@, b.nbits, 2) == true);
}

/// remove at 0 of a full block (the base-block top squeezed out)
fn ut_remove_head_full_block()
{
    let mut b = BitVec::from_elem(32, true);
    b.set(0, false);
    let r = b.remove(0);
    assert(r == false);
    assert(b.nbits == 31);
    assert forall|j: usize| j < 31 implies bit_at(b.storage@, b.nbits, j) == true by { };
}

/// remove at the block tail (a block pop on the storage side): squeezing
/// out the single false bit at 31 leaves 32 true bits
fn ut_remove_tail_boundary()
{
    let mut b = BitVec::from_elem(33, true);
    b.set(31, false);
    let r = b.remove(31);
    assert(r == false);
    assert(b.nbits == 32);
    assert forall|j: usize| j < 32 implies
        bit_at(b.storage@, b.nbits, j) == true by {
        if j < 31 {
            // the kept tier: bit j is the old bit j
        } else {
            // the shifted tier: remove's plain-j trigger fires directly
            // and the old bit at j + 1 is true by the from_elem pattern
        }
    }
}

/// remove at the top bit of the first block (bit 31 incoming to the base
/// rewrite as the carry from the second block)
fn ut_remove_top_bit_carry()
{
    let mut b = BitVec::from_elem(64, false);
    b.set(32, true);
    b.set(31, true);
    let r = b.remove(31);
    assert(r == true);
    assert(b.nbits == 63);
    assert forall|j: usize| j < 63 implies bit_at(b.storage@, b.nbits, j)
        == (j == 31) by { };
}

// ---------------------------------------------------------------------------
// capacity family (the injected capacity model)
// ---------------------------------------------------------------------------

/// the doc tier: capacity covers the current length in bits
fn ut_capacity_covers_len()
{
    let b = BitVec::from_elem(10, true);
    let cap = b.capacity();
    assert(cap >= 10);
    assert(cap == spec_bit_capacity(&b));
}

/// the reserve doc example: len and the bit pattern survive (the
/// allocation-layer growth itself is carried by the injected model
/// disclosure, out of the entries view)
fn ut_reserve_keeps_bits()
{
    let mut b = BitVec::from_elem(3, false);
    b.set(0, true);
    b.reserve(10);
    assert(b.nbits == 3);
    assert forall|j: usize| j < 3 implies
        bit_at(b.storage@, b.nbits, j) == (j == 0) by { };
}

/// reserve_exact: the same entries-view tier as reserve
fn ut_reserve_exact_keeps_bits()
{
    let mut b = BitVec::from_elem(3, false);
    b.set(2, true);
    b.reserve_exact(10);
    assert(b.nbits == 3);
    assert forall|j: usize| j < 3 implies
        bit_at(b.storage@, b.nbits, j) == (j == 2) by { };
}

/// with_capacity: an empty vector on the entries view
fn ut_with_capacity_empty()
{
    let b = BitVec::with_capacity(64);
    assert(b.nbits == 0);
    assert(b.storage@.len() == 0);
}

/// push_within_capacity ok-branch: spare capacity is provable for any
/// vector that is not on a 32-bit block boundary of its capacity (a
/// from_elem build leaves at least 32 * storage blocks of capacity)
fn ut_push_within_capacity_ok()
{
    let mut b = BitVec::from_elem(5, true);
    // the ok-branch hypothesis: 5 is below the bits capacity tier
    let cap = b.capacity();
    assert(b.storage@.len() == 1);
    assert((32 * (1 as int)) <= usize::MAX as int);
    assert((cap as int) >= 32);
    assert(b.nbits == 5);
    let r = b.push_within_capacity(false);
    assert(r is Ok);
    assert(b.nbits == 6);
    assert(bit_at(b.storage@, b.nbits, 5) == false);
    assert(bit_at(b.storage@, b.nbits, (b.nbits - 1) as usize) == false);
    assert forall|j: usize| j < 6 implies
        bit_at(b.storage@, b.nbits, j) == (j != 5) by { }
}

} // verus!

fn main() {}
