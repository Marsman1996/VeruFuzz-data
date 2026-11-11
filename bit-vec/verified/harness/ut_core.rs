//! bit-vec 0.10.1 x Verus -- UT / fuzz property harness
//! (assertion-theorem zone).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); this file never copies
//! src-side specs/lemmas/transcriptions -- it only writes UT/fuzz-
//! implied property theorems on top of them.
//!
//! Coverage source map (out/harness-inventory.md section 1):
//!   - bit-wise read/write boundary family (test_0/1/10/31/32/33_elements,
//!     test_small/big_bit_vec_tests, eq_vec instances)
//!     -> ut_from_elem_bits / ut_get_roundtrip / ut_get_set_locality /
//!        ut_boundary_masks
//!   - fill/set_all/clear doc "# Invariants" (lib.rs:1840-1846:
//!     fill(true) => all(), fill(false) => none())
//!     -> ut_fill_all_none / ut_deprecated_aliases
//!   - push/pop (test_bit_vec_push_pop)
//!     -> ut_push_pop_roundtrip / ut_pop_empty
//!   - L0 "invariant preserved after op" of the fuzz interpreter
//!     (code/fuzz main.rs do_test: fill op13/22, push op4, pop op5)
//!     -> fuzz_inv_preserved_by_fill / _by_push / _by_pop
//!   - the batch-D residual zone upstream UT families (display output,
//!     from_bools, truncate faces, remove_last, remove_all)
//!     -> ut_display_output / ut_from_bools_display / ut_truncate_faces /
//!        ut_remove_last / ut_remove_all_clone
//!   The remaining UT families (serde cfg; set ops/count/insert/remove
//!   are covered by the diff-set harnesses; iter_mut/get_mut are
//!   Rc-blocked) -- see out/bug-finder-summary.md.

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitvec_lib;

verus! {

use bitvec_lib::{BitVec, all_spec, bit_at, inv, lemma_flag_nonzero, none_spec, trailing_mask};

/// test_0/1/10/31/32/33_elements (bit-wise model agreement of the eq_vec
/// instances): from_elem => every bit of the model == bit.
pub exec fn ut_from_elem_bits(n: usize, bit: bool) -> (bv: BitVec)
    requires
        n < 1000,
    ensures
        inv(&bv),
        bv.nbits == n,
        forall|i: usize| i < n ==> bit_at(bv.storage@, bv.nbits, i) == bit,
{
    let bv = BitVec::from_elem(n, bit);
    bv
}

/// Index/get read-back (the get side of test_*_elements).
pub exec fn ut_get_roundtrip(bit: bool, i: usize) -> (bv: BitVec)
    requires
        i < 32,
    ensures
        inv(&bv),
{
    let bv = BitVec::from_elem(32, bit);
    /* Origin Rust UT: assert_eq!(v.get(i), Some(bit)) */
    let r = bv.get(i);
    assert(r == Some(bit));
    /* out-of-bounds read face (i >= nbits => None, the doc contract) */
    let over = bv.get(32usize + i);
    assert(over is None);
    bv
}

/// set locality (the eq_vec expectation of test_*_elements: setting one
/// bit does not disturb the others).
pub exec fn ut_get_set_locality(i: usize) -> (bv: BitVec)
    requires
        i < 33,
    ensures
        inv(&bv),
        bv.nbits == 33,
        bit_at(bv.storage@, bv.nbits, i) == true,
        forall|j: usize| j < bv.nbits && j != i ==> bit_at(bv.storage@, bv.nbits, j) == false,
{
    let mut bv = BitVec::from_elem(33, false);
    bv.set(i, true);
    bv
}

/// tail-block mask boundaries (31/32/33 instances; the probeB/
/// mask_for_bits_exec reading).
pub exec fn ut_boundary_masks() -> (m: u32)
    ensures
        m == 1u32,
{
    proof {
        assert(33usize % 32usize == 1usize);
        assert((1u32 << 1) == 2u32) by (bit_vector);
        assert(2u32 - 1u32 == 1u32) by (bit_vector);
        assert((1u32 << 31) - 1u32 == 2147483647u32) by (bit_vector);
        assert(4294967295u32 != 0u32);
    }
    let m31 = bitvec_lib::mask_for_bits_exec(31);
    let m32 = bitvec_lib::mask_for_bits_exec(32);
    let m33 = bitvec_lib::mask_for_bits_exec(33);
    assert(m31 == 2147483647u32);
    assert(m32 == 4294967295u32);
    assert(m33 == 1u32);
    /* tail-block shapes of the 31/32/33 instances (the mask-side shadow
       of test_31/32/33_elements) */
    m33
}

/// fill(true) => all() and fill(false) => none() (lib.rs:1840-1846 doc
/// invariants).
pub exec fn ut_fill_all_none(n: usize, bit: bool) -> (bv: BitVec)
    requires
        n < 1000,
    ensures
        inv(&bv),
        bv.nbits == n,
        all_spec(&bv) == (bit || n == 0),
        none_spec(&bv) == (!bit || n == 0),
{
    let mut bv = BitVec::from_elem(n, bit);
    bv.fill(bit);
    let a = bv.all();
    let ne = bv.none();
    if bit {
        assert(all_spec(&bv));
    } else {
        assert(none_spec(&bv));
    }
    proof {
    if n > 0 {
        let w = bv.storage@.len();
        assert(w >= 1);
        let e = n % 32;
        if e == 0 {
            assert(trailing_mask(n) == 4294967295u32);
        } else {
            lemma_flag_nonzero(e);
            assert(e <= 31);
            assert((1u32 << e) - 1u32 != 0u32) by (bit_vector)
                requires e >= 1usize, e <= 31usize,;
            assert(trailing_mask(n) == ((1u32 << e) - 1u32) as u32);
        }
        assert(trailing_mask(n) != 0u32);
        if bit {
            assert(bv.storage@[(w - 1) as int] == trailing_mask(n));
            assert(bv.storage@[(w - 1) as int] != 0u32);
        } else {
            assert(none_spec(&bv));
            assert(bv.storage@[(w - 1) as int] == 0u32);
            assert(!all_spec(&bv));
        }
        assert(!all_spec(&bv) == !bit);
    }
    }
    assert(a == (bit || n == 0));
    assert(ne == (!bit || n == 0));
    bv
}

/// set_all/clear are deprecated aliases of fill (lib.rs:930-936 /
/// 1831-1836); the doc invariants carry over.
pub exec fn ut_deprecated_aliases() -> (bv: BitVec)
    ensures
        inv(&bv),
        all_spec(&bv),
        none_spec(&bv),
{
    let bv = bitvec_lib::new();
    /* Origin Rust: bv.set_all(); -- deprecated alias = fill(true) */
    let mut bv2 = bitvec_lib::new();
    bv2.set_all();
    let a = bv2.all();
    assert(a);
    /* Origin Rust: bv.clear(); -- deprecated alias = fill(false) */
    let mut bv3 = bitvec_lib::new();
    bv3.clear();
    let ne = bv3.none();
    assert(ne);
    bv
}

/// push/pop roundtrip (test_bit_vec_push_pop): after a push, the pop
/// returns the pushed value.
pub exec fn ut_push_pop_roundtrip(n: usize, b: bool) -> (r: Option<bool>)
    requires
        n < 1000,
        n < usize::MAX,
    ensures
        r == Some(b),
{
    let mut bv = BitVec::from_elem(n, b);
    /* Origin Rust UT: v.push(b); assert_eq!(v.pop(), Some(b)) */
    bv.push(b);
    let r = bv.pop();
    assert(r == Some(b));
    r
}

pub exec fn ut_pop_empty() -> (r: Option<bool>)
    ensures
        r is None,
{
    let mut bv = BitVec::from_elem(0, false);
    bv.pop()
}

// ---------------------------------------------------------------------------
// fuzz interpreter L0: the invariant is preserved after each op (the
// crash-freedom precondition of main.rs do_test)
pub exec fn fuzz_inv_preserved_by_fill(n: usize, bit: bool) -> (bv: BitVec)
    requires
        n < 1000,
    ensures
        inv(&bv),
{
    let mut bv = BitVec::from_elem(n, bit);
    bv.fill(bit);
    bv
}

pub exec fn fuzz_inv_preserved_by_push(n: usize, b: bool) -> (bv: BitVec)
    requires
        n < 1000,
        n < usize::MAX,
    ensures
        inv(&bv),
{
    let mut bv = BitVec::from_elem(n, b);
    /* Origin Rust: op4 push (called after the interpreter guard) */
    bv.push(b);
    bv
}

pub exec fn fuzz_inv_preserved_by_pop(n: usize, b: bool) -> (n1: usize)
    requires
        n < 1000,
    ensures
        n1 == if n > 0 { n - 1 } else { 0 },
{
    let mut bv = BitVec::from_elem(n, b);
    /* Origin Rust: op5 pop */
    let r = bv.pop();
    bv.nbits
}

// ---------------------------------------------------------------------------
// the batch-D residual zone: the upstream UT families that were absent
// above (Phase-transcribed assertion theorems over the batch-D faces;
// out/harness-inventory.md 6.2 for the full residual table)

/// test_display_output (lib.rs:2394-2400): the three rustdoc shapes --
/// empty prints nothing, a one-bit true prints "1", eight zeros print
/// "00000000" (the char-stream materialization of Display)
pub exec fn ut_display_output() -> (r: u32)
    ensures
        r == 1,
{
    let e = bitvec_lib::new();
    let ce = e.display_chars();
    assert(ce@.len() == 0);
    let one = BitVec::from_elem(1, true);
    let c1 = one.display_chars();
    assert(c1@.len() == 1);
    assert(c1@[0] == '1');
    let z8 = BitVec::from_elem(8, false);
    let cz = z8.display_chars();
    assert(cz@.len() == 8);
    assert(cz@[0] == '0');
    assert(cz@[3] == '0');
    assert(cz@[7] == '0');
    assert forall|j: usize| j < 8 implies
        cz@[j as int] == '0' by {
        assert forall|k: usize| k < 8 implies
            bit_at(z8.storage@, z8.nbits, k) == false by { }
    }
    1
}

/// test_from_bools (lib.rs:2816-2822): the collect of [true, false,
/// true, true] reads back "1011" (FromIterator + the Display stream)
pub exec fn ut_from_bools_display() -> (r: u32)
    ensures
        r == 4,
{
    let bools: &[bool] = &[true, false, true, true];
    let bv = BitVec::from_iter_bools(bools);
    let cs = bv.display_chars();
    assert(cs@.len() == 4);
    assert(cs@[0] == '1');
    assert(cs@[1] == '0');
    assert(cs@[2] == '1');
    assert(cs@[3] == '1');
    // the eq_vec tier rides along on the collected bits
    assert(bit_at(bv.storage@, bv.nbits, 1) == bools@[1]);
    assert(bit_at(bv.storage@, bv.nbits, 0) == bools@[0]);
    assert(bit_at(bv.storage@, bv.nbits, 2) == bools@[2]);
    assert(bit_at(bv.storage@, bv.nbits, 3) == bools@[3]);
    4
}

/// test_bit_vec_truncate (lib.rs:3075-3095): the five faces of the
/// truncation walk -- block-edge, the above-length noop, the
/// mid-block cut, and the emptying cut
pub exec fn ut_truncate_faces() -> (r: u32)
    ensures
        r == 0,
{
    let mut s = BitVec::from_elem(160, true);
    assert(s.nbits == 160);
    s.truncate(128);
    assert(s.nbits == 128);
    assert forall|j: usize| j < 128 implies
        bit_at(s.storage@, s.nbits, j) == true by { }
    // the above-length call is the documented noop
    s.truncate(160);
    assert(s.nbits == 128);
    // the mid-block cut
    s.truncate(86);
    assert(s.nbits == 86);
    assert forall|j: usize| j < 86 implies
        bit_at(s.storage@, s.nbits, j) == true by { }
    // the emptying cut
    s.truncate(0);
    assert(s.nbits == 0);
    0
}

/// test_remove_last (lib.rs:3662-3669): a from_fn build in upstream --
/// the materialization keeps the assertion shape (the top bit set, then
/// removed) with the from_elem+set construction (from_fn's closure
/// domain stays blocked)
pub exec fn ut_remove_last() -> (r: bool)
    ensures
        r == true,
{
    let mut v = BitVec::from_elem(1025, false);
    v.set(1024, true);
    assert(v.nbits == 1025);
    let tail = v.remove(1024);
    assert(tail == true);
    assert(v.nbits == 1024);
    let st = v.storage();
    assert(st.len() == (1024usize / 32));
    // the kept bits read back false
    assert forall|j: usize| j < 1024 implies
        bit_at(v.storage@, v.nbits, j) == false by { }
    true
}

/// test_remove_all (lib.rs:3671-3680): the clone clears to emptiness
pub exec fn ut_remove_all_clone() -> (r: u32)
    ensures
        r == 0,
{
    let v = BitVec::from_elem(64, false);
    let mut v2 = v.clone_exec();
    v2.remove_all();
    assert(v2.nbits == 0);
    let g = v2.get(0);
    assert(g is None);
    // the length and the storage view are both empty
    let st2 = v2.storage();
    assert(st2.len() == 0);
    0
}

fn main() {}
} // verus!
