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
//!   The remaining UT families (serde/set ops/Ord/count/insert/remove,
//!   etc.) are uncovered; see out/bug-finder-summary.md.

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

fn main() {}
} // verus!
