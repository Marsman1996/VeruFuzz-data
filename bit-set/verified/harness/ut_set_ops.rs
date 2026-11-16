//! bit-set 0.11.1 x Verus -- UT harness, batch H3 (set_ops).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here, except small harness-local
//! byte-bridge and count helpers (the H1 fixed-position pattern).
//!
//! Coverage (upstream set/tests/set.rs, batch H3 -- the UTs whose
//! obligations close on the src set-op contracts directly):
//!   test_bit_set_subset / test_bit_set_is_disjoint /
//!   test_bit_set_union_with / test_bit_set_intersect_with /
//!   test_bit_set_difference_with / test_bit_set_symmetric_difference_with /
//!   test_bit_set_frombit_vec_init / test_bit_vec_masking /
//!   test_truncate / test_bit_set_shrink_to_fit_new / test_bit_set_shrink_to_fit
//!
//! Face ruling (recorded in out/harness-inventory.md and the batch
//! notes): the capacity-value / `capacity > old_cap` sub-asserts of the
//! shrink UTs are allocator-runtime faces (spec_bit_capacity only pins
//! the free-of-resize direction); the post-shrink_to_fit `count()`
//! sub-asserts ride a contract tail gap (the shrink ensures binds
//! membership only below the old universe; the final universe/pad
//! region is not pinned), recorded as-is, not re-proven here.

#![feature(allocator_api)] // needed by the referenced src assume_specification signature
#![verifier::timeout(240)] // the crate-root timeout face (moved from src/lib.rs)

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitset_lib;

verus! {

use bitset_lib::set::{BitSet, bs_at, bs_count, bs_inv, bs_max_nb, lemma_count_two_ranges};
use bitset_lib::bitvec_lib::{BitVec, bit_at, count_bits, from_bytes_bit, lemma_count_const,
    lemma_count_range_const, lemma_count_split, popc};

// ---------------------------------------------------------------------------
// harness-local byte bridges (the H1 kit: from_bytes postcondition plus
// the byte-mask definition, pinned per byte value; positions spelled by
// the 8-way ladder so every call site instantiates the member predicate)
// ---------------------------------------------------------------------------

/// popc of the zero word is zero (the recursion chain unrolls in the
/// lemma body; the caller only carries the zero-value atom).
pub proof fn zero_prefix(w: u32, k: usize)
    requires
        k <= 32usize,
        w == 0u32,
    ensures
        popc(w, k) == 0int,
    decreases
        k,
{
    if k == 0 {
        assert(popc(w, 0usize) == 0int);
    } else {
        assert((w & (1u32 << ((k - 1) as u32))) == 0u32) by (bit_vector)
            requires w == 0u32;
        zero_prefix(w, (k - 1) as usize);
        assert((w & (1u32 << ((k - 1) as u32))) == 0u32);
        assert(popc(w, k) == popc(w, (k - 1) as usize) + 0int);
    }
}

/// the member bridge at one fixed position of a byte-built set (the
/// from_bytes postcondition instance plus the bit-mask definition).
pub proof fn lemma_byte_member(bs: &BitSet, bytes: &[u8], i: usize)
    requires
        bs_inv(bs),
        i < bs.bit_vec.nbits,
        (bs.bit_vec.nbits as int) == 8 * (bytes@.len() as int),
        bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        bit_at(bs.bit_vec.storage@, bs.bit_vec.nbits, i)
            == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8),
{
    assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
    assert(from_bytes_bit(bytes@, i)
        == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
}

/// the zero-byte face: a set built from a single zero byte carries no
/// member at any position (H1 helper, harness-local).
pub proof fn lemma_zero_byte_memberless(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bs.bit_vec.nbits as int) == 8 * (bytes@.len() as int),
        bytes@.len() == 1int,
        bytes@[0] == 0u8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|t: usize| !bs_at(bs, t),
{
    assert forall|t: usize| !bs_at(bs, t) by {
        if (t as int) < 8int {
            assert(bs_at(bs, t) == from_bytes_bit(bytes@, t));
            assert(from_bytes_bit(bytes@, t)
                == ((bytes@[(t / 8) as int] & (1u8 << (7 - (t % 8)))) != 0u8));
            assert((t / 8) as int == 0int) by (nonlinear_arith)
                requires (t as int) < 8int;
            assert(bytes@[(t / 8) as int] == 0u8);
            // the zero byte conjoined with any bit mask stays zero
            assert((0u8 & (1u8 << (7 - (t % 8)))) == 0u8) by (bit_vector);
        } else {
            assert(bs_at(bs, t) == (t < bs.bit_vec.nbits
                && bit_at(bs.bit_vec.storage@, bs.bit_vec.nbits, t)));
        }
    }
}

// ---------------------------------------------------------------------------
// the 8-way position ladder for a one-byte set: each branch pins the
// skolem position so the byte mask folds to a fixed-shift constant,
// which the blast decides. One lemma per byte value used by the batch.
// ---------------------------------------------------------------------------

/// 0b10100010 carries byte bits {7, 5, 1} -> member positions {0, 2, 6}.
pub proof fn lemma_face_a2(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b10100010u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i) == (i == 0 || i == 2 || i == 6),
{
    let w: u8 = bytes@[0];
    assert(w == 0b10100010u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i) == (i == 0 || i == 2 || i == 6) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10100010u32;
            }
        }
    }
}

/// 0b01100010 carries byte bits {6, 5, 1} -> member positions {1, 2, 6}.
pub proof fn lemma_face_62(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b01100010u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i) == (i == 1 || i == 2 || i == 6),
{
    let w: u8 = bytes@[0];
    assert(w == 0b01100010u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i) == (i == 1 || i == 2 || i == 6) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01100010u32;
            }
        }
    }
}

/// 0b01000000 carries byte bit {6} -> member position {1}.
pub proof fn lemma_face_40(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b01000000u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i) == (i == 1),
{
    let w: u8 = bytes@[0];
    assert(w == 0b01000000u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i) == (i == 1) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01000000u32;
            }
        }
    }
}

/// 0b00110000 carries byte bits {5, 4} -> member positions {2, 3}.
pub proof fn lemma_face_30(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b00110000u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i) == (i == 2 || i == 3),
{
    let w: u8 = bytes@[0];
    assert(w == 0b00110000u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i) == (i == 2 || i == 3) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b00110000u32;
            }
        }
    }
}

/// 0b10000100 carries byte bits {7, 2} -> member positions {0, 5}.
pub proof fn lemma_face_84(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b10000100u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i) == (i == 0 || i == 5),
{
    let w: u8 = bytes@[0];
    assert(w == 0b10000100u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i) == (i == 0 || i == 5) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b10000100u32;
            }
        }
    }
}

/// 0b11100010 carries byte bits {7, 6, 5, 1} -> member positions
/// {0, 1, 2, 6}.
pub proof fn lemma_face_e2(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b11100010u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i)
            == (i == 0 || i == 1 || i == 2 || i == 6),
{
    let w: u8 = bytes@[0];
    assert(w == 0b11100010u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i)
        == (i == 0 || i == 1 || i == 2 || i == 6) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b11100010u32;
            }
        }
    }
}

/// 0b01101010 carries byte bits {6, 5, 3, 1} -> member positions
/// {1, 2, 4, 6}.
pub proof fn lemma_face_6a(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        (bytes@.len() as int) == 1,
        bytes@[0] == 0b01101010u8,
        bs.bit_vec.nbits == 8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| #[trigger] bs_at(bs, i)
            == (i == 1 || i == 2 || i == 4 || i == 6),
{
    let w: u8 = bytes@[0];
    assert(w == 0b01101010u8);
    assert forall|i: usize| #[trigger] bs_at(bs, i)
        == (i == 1 || i == 2 || i == 4 || i == 6) by {
        if (i as int) < 8int {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(from_bytes_bit(bytes@, i)
                == ((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
            assert((i / 8) as int == 0int) by (nonlinear_arith)
                requires (i as int) < 8int;
            assert(bytes@[(i / 8) as int] == w);
            assert(bs_at(bs, i) == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            if i == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else if i == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else if i == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else if i == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else if i == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else if i == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else if i == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            } else {
                assert(i == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) == 0u8) by (bit_vector)
                    requires (w as u32) == 0b01101010u32;
            }
        }
    }
}

/// the all-0xFF bytes face: every in-universe position is a member.
pub proof fn lemma_all_ff_face(bs: &BitSet, bytes: &[u8])
    requires
        bs_inv(bs),
        1 <= bytes.len(),
        (bs.bit_vec.nbits as int) == 8 * (bytes.len() as int),
        forall|k: usize| k < bytes.len() ==> bytes@[k as int] == 0b11111111u8,
        forall|i: usize| i < bs.bit_vec.nbits
            ==> #[trigger] bs_at(bs, i) == from_bytes_bit(bytes@, i),
    ensures
        forall|i: usize| bs_at(bs, i) == ((i as int) < 8 * (bytes.len() as int)),
{
    assert forall|i: usize| bs_at(bs, i) == ((i as int) < 8 * (bytes.len() as int)) by {
        if (i as int) < 8 * (bytes.len() as int) {
            assert(bs_at(bs, i) == from_bytes_bit(bytes@, i));
            assert(((i / 8) as int) < (bytes.len() as int)) by (nonlinear_arith)
                requires
                    (i as int) >= 0,
                    (i as int) < 8 * (bytes.len() as int),
                    (bytes.len() as int) >= 1,
            ;
            let w: u8 = bytes@[(i / 8) as int];
            assert(w == 0b11111111u8);
            assert(from_bytes_bit(bytes@, i)
                == ((w & (1u8 << (7 - (i % 8)))) != 0u8));
            // every 8-bit mask of the all-ones byte is nonzero (branch on
            // i % 8 so the shift folds to a fixed-position constant)
            if (i % 8) == 0 {
                assert(7 - (i % 8) == 7usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 7)) != 0u8));
                assert((w & (1u8 << 7)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else if (i % 8) == 1 {
                assert(7 - (i % 8) == 6usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 6)) != 0u8));
                assert((w & (1u8 << 6)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else if (i % 8) == 2 {
                assert(7 - (i % 8) == 5usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 5)) != 0u8));
                assert((w & (1u8 << 5)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else if (i % 8) == 3 {
                assert(7 - (i % 8) == 4usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 4)) != 0u8));
                assert((w & (1u8 << 4)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else if (i % 8) == 4 {
                assert(7 - (i % 8) == 3usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 3)) != 0u8));
                assert((w & (1u8 << 3)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else if (i % 8) == 5 {
                assert(7 - (i % 8) == 2usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 2)) != 0u8));
                assert((w & (1u8 << 2)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else if (i % 8) == 6 {
                assert(7 - (i % 8) == 1usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 1)) != 0u8));
                assert((w & (1u8 << 1)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            } else {
                assert((i % 8) == 7usize);
                assert(7 - (i % 8) == 0usize);
                assert(bs_at(bs, i) == ((w & (1u8 << 0)) != 0u8));
                assert((w & (1u8 << 0)) != 0u8) by (bit_vector)
                    requires (w as u32) == 0b11111111u32;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// UT bodies (one exec fn per upstream #[test])
// ---------------------------------------------------------------------------

/// upstream test_bit_set_subset (tests/set.rs:197-221): ten subset
/// queries over the insert/remove mutation sequence.
pub exec fn ut_subset() -> (r: u64)
    ensures
        r == 10u64,
{
    let mut set1 = BitSet::new();
    let mut set2 = BitSet::new();

    // 1. {} is a subset of {}
    let r1 = set1.is_subset(&set2);
    assert(r1 == true);

    set2.insert(100);
    // 2. {} is a subset of {100}
    let r2 = set1.is_subset(&set2);
    assert(r2 == true);

    set2.insert(200);
    // 3. {} is a subset of {100, 200}
    let r3 = set1.is_subset(&set2);
    assert(r3 == true);

    set1.insert(200);
    // 4. {200} is a subset of {100, 200}
    proof {
        assert forall|j: usize| j < set1.bit_vec.nbits
            implies (bs_at(&set1, j) ==> bs_at(&set2, j)) by { }
    }
    let r4 = set1.is_subset(&set2);
    assert(r4 == true);

    set1.insert(300);
    // 5. {200, 300} is NOT a subset of {100, 200}: witness 300
    proof {
        assert(bs_at(&set1, 300));
        assert(!bs_at(&set2, 300));
    }
    let r5 = set1.is_subset(&set2);
    assert(r5 == false);

    set2.insert(300);
    // 6. {200, 300} is a subset of {100, 200, 300}
    proof {
        assert forall|j: usize| j < set1.bit_vec.nbits
            implies (bs_at(&set1, j) ==> bs_at(&set2, j)) by { }
    }
    let r6 = set1.is_subset(&set2);
    assert(r6 == true);

    set2.insert(400);
    // 7. {200, 300} is a subset of {100, 200, 300, 400}
    proof {
        assert forall|j: usize| j < set1.bit_vec.nbits
            implies (bs_at(&set1, j) ==> bs_at(&set2, j)) by { }
    }
    let r7 = set1.is_subset(&set2);
    assert(r7 == true);

    set2.remove(100);
    // 8. {200, 300} is a subset of {200, 300, 400}
    proof {
        assert forall|j: usize| j < set1.bit_vec.nbits
            implies (bs_at(&set1, j) ==> bs_at(&set2, j)) by { }
    }
    let r8 = set1.is_subset(&set2);
    assert(r8 == true);

    set2.remove(300);
    // 9. {200, 300} is NOT a subset of {200, 400}: witness 300
    proof {
        assert(bs_at(&set1, 300));
        assert(!bs_at(&set2, 300));
    }
    let r9 = set1.is_subset(&set2);
    assert(r9 == false);

    set1.remove(300);
    // 10. {200} is a subset of {200, 400}
    proof {
        assert forall|j: usize| j < set1.bit_vec.nbits
            implies (bs_at(&set1, j) ==> bs_at(&set2, j)) by { }
    }
    let r10 = set1.is_subset(&set2);
    assert(r10 == true);

    10u64
}

/// upstream test_bit_set_is_disjoint (tests/set.rs:223-239): the
/// byte-built disjoint matrix, both directions, including the empty set.
pub exec fn ut_is_disjoint() -> (r: u64)
    ensures
        r == 8u64,
{
    let bytes_a: &[u8] = &[0b10100010];
    let bytes_b: &[u8] = &[0b01000000];
    let bytes_d: &[u8] = &[0b00110000];
    let a = BitSet::from_bytes(bytes_a); // {0, 2, 6}
    let b = BitSet::from_bytes(bytes_b); // {1}
    let c = BitSet::new();
    let d = BitSet::from_bytes(bytes_d); // {2, 3}
    proof {
        lemma_face_a2(&a, bytes_a);
        lemma_face_40(&b, bytes_b);
        lemma_face_30(&d, bytes_d);
        // the shared member 2 witnesses both non-disjoint directions
        assert(bs_at(&a, 2));
        assert(bs_at(&d, 2));
        assert forall|j: usize| !(bs_at(&a, j) && bs_at(&b, j)) by { }
        assert forall|j: usize| !(bs_at(&a, j) && bs_at(&c, j)) by { }
        assert forall|j: usize| !(bs_at(&b, j) && bs_at(&a, j)) by { }
        assert forall|j: usize| !(bs_at(&b, j) && bs_at(&c, j)) by { }
        assert forall|j: usize| !(bs_at(&c, j) && bs_at(&a, j)) by { }
        assert forall|j: usize| !(bs_at(&c, j) && bs_at(&b, j)) by { }
    }
    let rd1 = a.is_disjoint(&d);
    assert(rd1 == false);
    let rd2 = d.is_disjoint(&a);
    assert(rd2 == false);
    let rb1 = a.is_disjoint(&b);
    assert(rb1 == true);
    let rb2 = a.is_disjoint(&c);
    assert(rb2 == true);
    let rb3 = b.is_disjoint(&a);
    assert(rb3 == true);
    let rb4 = b.is_disjoint(&c);
    assert(rb4 == true);
    let rc1 = c.is_disjoint(&a);
    assert(rc1 == true);
    let rc2 = c.is_disjoint(&b);
    assert(rc2 == true);
    8u64
}

/// upstream test_bit_set_union_with (tests/set.rs:241-260): the grow
/// face against a byte-built expectation, plus the standard both-ways
/// count face.
pub exec fn ut_union_with() -> (r: u64)
    ensures
        r == 3u64,
{
    // part 1: a should grow to include the larger elements
    let mut a = BitSet::new();
    a.insert(0);
    let ghost pa = a;
    let mut b = BitSet::new();
    b.insert(5);
    let ghost pb = b;
    let bytes_e: &[u8] = &[0b10000100];
    let expected = BitSet::from_bytes(bytes_e); // {0, 5}
    a.union_with(&b);
    proof {
        lemma_face_84(&expected, bytes_e);
        assert(a.bit_vec.nbits == 6usize);
        // the union row spelled at the skolem position against the two
        // frozen insert faces, then the padded equality face
        assert forall|j: usize| #[trigger] bs_at(&a, j) == (j == 0 || j == 5) by {
            if (j as int) < 6int {
                assert(bs_at(&pa, j) == (j == 0));
                assert(bs_at(&pb, j) == (j == 5));
                assert(bs_at(&a, j) == (bs_at(&pa, j) || bs_at(&pb, j)));
            } else {
                assert(bs_at(&a, j) == false);
                assert(!(j == 0 || j == 5));
            }
        }
        assert forall|j: usize| j < bs_max_nb(&a, &expected)
            implies (bs_at(&a, j) == bs_at(&expected, j)) by {
            if (j as int) < 8int {
                assert(bs_at(&a, j) == (j == 0 || j == 5));
                assert(bs_at(&expected, j) == (j == 0 || j == 5));
            }
        }
    }
    let e1 = a.eq(&expected);
    assert(e1 == true);

    // part 2: the standard face, both directions
    let bytes_a: &[u8] = &[0b10100010];
    let bytes_b: &[u8] = &[0b01100010];
    let mut a2 = BitSet::from_bytes(bytes_a); // {0, 2, 6}
    let mut b2 = BitSet::from_bytes(bytes_b); // {1, 2, 6}
    let c2 = a2.clone();
    proof {
        // pin the two byte faces on the pre-union values
        lemma_face_a2(&a2, bytes_a);
        lemma_face_62(&b2, bytes_b);
    }
    let ghost pa2 = a2;
    let ghost pb2 = b2;
    a2.union_with(&b2);
    let cnt_a = a2.count();
    proof {
        // {0, 1, 2, 6}: the two-range count face over the 8-bit universe
        let s = a2.bit_vec.storage@;
        let n = a2.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&a2, j) == (j < 3 || j == 6) by {
            if (j as int) < 8int {
                assert(bs_at(&pa2, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&pb2, j) == (j == 1 || j == 2 || j == 6));
                assert(bs_at(&a2, j) == (bs_at(&pa2, j) || bs_at(&pb2, j)));
            } else {
                assert(bs_at(&a2, j) == false);
                assert(!(j < 3 || j == 6));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p < 3 || p == 6) by {
            if (p as int) < 8int {
                assert(bs_at(&a2, p) == bit_at(s, n, p));
                assert(bs_at(&a2, p) == (p < 3 || p == 6));
            }
        }
        assert forall|p: usize| 3 <= p && p < 6 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 7 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 0usize, 3usize, 6usize, 7usize);
        assert(count_bits(s, n, 0usize, n) == 4int);
        assert(bs_count(&a2) == 4int);
    }
    assert(cnt_a == 4usize);
    b2.union_with(&c2);
    let cnt_b = b2.count();
    proof {
        let s = b2.bit_vec.storage@;
        let n = b2.bit_vec.nbits;
        assert(n == 8usize);
        // b2 = {1, 2, 6} union c2 = clone of {0, 2, 6}
        assert forall|j: usize| #[trigger] bs_at(&b2, j) == (j < 3 || j == 6) by {
            if (j as int) < 8int {
                assert(bs_at(&pb2, j) == (j == 1 || j == 2 || j == 6));
                assert(bs_at(&c2, j) == bs_at(&pa2, j));
                assert(bs_at(&pa2, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&b2, j) == (bs_at(&pb2, j) || bs_at(&c2, j)));
            } else {
                assert(bs_at(&b2, j) == false);
                assert(!(j < 3 || j == 6));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p < 3 || p == 6) by {
            if (p as int) < 8int {
                assert(bs_at(&b2, p) == bit_at(s, n, p));
                assert(bs_at(&b2, p) == (p < 3 || p == 6));
            }
        }
        assert forall|p: usize| 3 <= p && p < 6 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 7 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 0usize, 3usize, 6usize, 7usize);
        assert(count_bits(s, n, 0usize, n) == 4int);
        assert(bs_count(&b2) == 4int);
    }
    assert(cnt_b == 4usize);
    3u64
}

/// upstream test_bit_set_intersect_with (tests/set.rs:262-290): the
/// zero-byte, uninitialized-bits and standard intersection faces. The
/// two downstream is_empty sub-asserts (the self-side zero folds after
/// the second intersect of each zero-layout part) closed in batch H4
/// via the src-side final-side twin rows (see the unfreeze notes in
/// the body).
pub exec fn ut_intersect_with() -> (r: u64)
    ensures
        r == 4u64,
{
    let bytes_a: &[u8] = &[0b10100010];
    let bytes_z: &[u8] = &[0b00000000];

    // part 1: explicitly 0'ed bits
    let mut a = BitSet::from_bytes(bytes_a);
    let mut b0 = BitSet::from_bytes(bytes_z);
    let ghost pa = a;
    proof { lemma_zero_byte_memberless(&b0, bytes_z); }
    let c = a.clone();
    a.intersect_with(&b0);
    proof {
        assert forall|j: usize| !bs_at(&a, j) by {
            if true {
                assert(bs_at(&b0, j) == false);
                assert(bs_at(&a, j) == (bs_at(&pa, j) && bs_at(&b0, j)));
            }
        }
    }
    let ie1 = a.is_empty();
    assert(ie1 == true);
    let ghost pb0 = b0;
    b0.intersect_with(&c);
    proof {
        // unfrozen (batch H4): the src-side twin row (explicit trigger
        // on the final-side membership term) instantiates at the
        // driven skolem, so the pre-state zero face closes the
        // conjunction below the shared universe.
        assert forall|j: usize| !bs_at(&b0, j) by {
            assert(bs_at(&b0, j) == (bs_at(&pb0, j) && bs_at(&c, j)));
        }
    }
    let ie2 = b0.is_empty();
    assert(ie2 == true);

    // part 2: uninitialized bits behave like 0's
    let mut a2 = BitSet::from_bytes(bytes_a);
    let mut b2 = BitSet::new();
    let ghost pa2 = a2;
    let c2 = a2.clone();
    a2.intersect_with(&b2);
    proof {
        assert forall|j: usize| !bs_at(&a2, j) by {
            if true {
                assert(bs_at(&b2, j) == false);
                assert(bs_at(&a2, j) == (bs_at(&pa2, j) && bs_at(&b2, j)));
            }
        }
    }
    let ie3 = a2.is_empty();
    assert(ie3 == true);
    let ghost pb2 = b2;
    b2.intersect_with(&c2);
    proof {
        // unfrozen (batch H4): same twin-row fold -- the zero here is
        // the uninitialized-universe face of BitSet::new (nbits 0).
        assert forall|j: usize| !bs_at(&b2, j) by {
            assert(bs_at(&b2, j) == (bs_at(&pb2, j) && bs_at(&c2, j)));
        }
    }
    let ie4 = b2.is_empty();
    assert(ie4 == true);

    // part 3: the standard face, both directions
    let bytes_b: &[u8] = &[0b01100010];
    let mut a3 = BitSet::from_bytes(bytes_a); // {0, 2, 6}
    let mut b3 = BitSet::from_bytes(bytes_b); // {1, 2, 6}
    let c3 = a3.clone();
    proof {
        lemma_face_a2(&a3, bytes_a);
        lemma_face_62(&b3, bytes_b);
    }
    let ghost pa3 = a3;
    let ghost pb3 = b3;
    a3.intersect_with(&b3);
    let cnt_a = a3.count();
    proof {
        // {2, 6}: the two-range count face
        let s = a3.bit_vec.storage@;
        let n = a3.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&a3, j) == (j == 2 || j == 6) by {
            if (j as int) < 8int {
                assert(bs_at(&pa3, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&pb3, j) == (j == 1 || j == 2 || j == 6));
                assert(bs_at(&a3, j) == (bs_at(&pa3, j) && bs_at(&pb3, j)));
            } else {
                assert(bs_at(&a3, j) == false);
                assert(!(j == 2 || j == 6));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p == 2 || p == 6) by {
            if (p as int) < 8int {
                assert(bs_at(&a3, p) == bit_at(s, n, p));
                assert(bs_at(&a3, p) == (p == 2 || p == 6));
            }
        }
        assert forall|p: usize| 3 <= p && p < 6 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 7 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 2usize, 3usize, 6usize, 7usize);
        assert(count_bits(s, n, 0usize, n) == 2int);
        assert(bs_count(&a3) == 2int);
    }
    assert(cnt_a == 2usize);
    b3.intersect_with(&c3);
    let cnt_b = b3.count();
    proof {
        // {2, 6} again: b3 = {1, 2, 6} & c3 = {0, 2, 6}
        let s = b3.bit_vec.storage@;
        let n = b3.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&b3, j) == (j == 2 || j == 6) by {
            if (j as int) < 8int {
                assert(bs_at(&pb3, j) == (j == 1 || j == 2 || j == 6));
                assert(bs_at(&c3, j) == bs_at(&pa3, j));
                assert(bs_at(&pa3, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&b3, j) == (bs_at(&pb3, j) && bs_at(&c3, j)));
            } else {
                assert(bs_at(&b3, j) == false);
                assert(!(j == 2 || j == 6));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p == 2 || p == 6) by {
            if (p as int) < 8int {
                assert(bs_at(&b3, p) == bit_at(s, n, p));
                assert(bs_at(&b3, p) == (p == 2 || p == 6));
            }
        }
        assert forall|p: usize| 3 <= p && p < 6 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 7 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 2usize, 3usize, 6usize, 7usize);
        assert(count_bits(s, n, 0usize, n) == 2int);
        assert(bs_count(&b3) == 2int);
    }
    assert(cnt_b == 2usize);
    4u64
}

/// upstream test_bit_set_difference_with (tests/set.rs:292-314): the
/// zero-bits, uninitialized-bits and standard difference faces. The
/// two zero-self is_empty sub-asserts closed in batch H4 via the
/// src-side final-side twin rows (see the unfreeze notes in the
/// body).
pub exec fn ut_difference_with() -> (r: u64)
    ensures
        r == 2u64,
{
    let bytes_z: &[u8] = &[0b00000000];
    let bytes_a: &[u8] = &[0b10100010];
    let bytes_f: &[u8] = &[0b11111111];

    // part 1: explicitly 0'ed bits
    let mut a = BitSet::from_bytes(bytes_z);
    let b = BitSet::from_bytes(bytes_a);
    let ghost pa = a;
    proof { lemma_zero_byte_memberless(&a, bytes_z); }
    a.difference_with(&b);
    proof {
        // unfrozen (batch H4): the difference twin row instantiates at
        // the driven skolem; the zero-byte memberless face of the old
        // self swallows the conjunction.
        assert forall|j: usize| !bs_at(&a, j) by {
            assert(bs_at(&a, j) == (bs_at(&pa, j) && !bs_at(&b, j)));
        }
    }
    let ie1 = a.is_empty();
    assert(ie1 == true);

    // part 2: uninitialized bits behave like 0's
    let mut a2 = BitSet::new();
    let b2 = BitSet::from_bytes(bytes_f);
    let ghost pa2 = a2;
    a2.difference_with(&b2);
    proof {
        // unfrozen (batch H4): same twin-row fold -- the old self is
        // the uninitialized (nbits 0) universe here.
        assert forall|j: usize| !bs_at(&a2, j) by {
            assert(bs_at(&a2, j) == (bs_at(&pa2, j) && !bs_at(&b2, j)));
        }
    }
    let ie2 = a2.is_empty();
    assert(ie2 == true);

    // part 3: the standard face, both directions
    let bytes_b: &[u8] = &[0b01100010];
    let mut a3 = BitSet::from_bytes(bytes_a); // {0, 2, 6}
    let mut b3 = BitSet::from_bytes(bytes_b); // {1, 2, 6}
    let c3 = a3.clone();
    proof {
        lemma_face_a2(&a3, bytes_a);
        lemma_face_62(&b3, bytes_b);
    }
    let ghost pa3 = a3;
    let ghost pb3 = b3;
    a3.difference_with(&b3);
    let cnt_a = a3.count();
    proof {
        // {0}: the single-member count face
        let s = a3.bit_vec.storage@;
        let n = a3.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&a3, j) == (j == 0) by {
            if (j as int) < 8int {
                assert(bs_at(&pa3, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&pb3, j) == (j == 1 || j == 2 || j == 6));
                assert(bs_at(&a3, j) == (bs_at(&pa3, j) && !bs_at(&pb3, j)));
            } else {
                assert(bs_at(&a3, j) == false);
                assert(!(j == 0));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p == 0) by {
            if (p as int) < 8int {
                assert(bs_at(&a3, p) == bit_at(s, n, p));
                assert(bs_at(&a3, p) == (p == 0));
            }
        }
        assert forall|p: usize| 1 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 0usize, 1usize, 1usize, 1usize);
        assert(count_bits(s, n, 0usize, n) == 1int);
        assert(bs_count(&a3) == 1int);
    }
    assert(cnt_a == 1usize);
    b3.difference_with(&c3);
    let cnt_b = b3.count();
    proof {
        // {1}: b3 - c3 = {1, 2, 6} - {0, 2, 6}
        let s = b3.bit_vec.storage@;
        let n = b3.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&b3, j) == (j == 1) by {
            if (j as int) < 8int {
                assert(bs_at(&pb3, j) == (j == 1 || j == 2 || j == 6));
                assert(bs_at(&c3, j) == bs_at(&pa3, j));
                assert(bs_at(&pa3, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&b3, j) == (bs_at(&pb3, j) && !bs_at(&c3, j)));
            } else {
                assert(bs_at(&b3, j) == false);
                assert(!(j == 1));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p == 1) by {
            if (p as int) < 8int {
                assert(bs_at(&b3, p) == bit_at(s, n, p));
                assert(bs_at(&b3, p) == (p == 1));
            }
        }
        assert forall|p: usize| 2 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 1usize, 2usize, 2usize, 2usize);
        assert(count_bits(s, n, 0usize, n) == 1int);
        assert(bs_count(&b3) == 1int);
    }
    assert(cnt_b == 1usize);
    2u64
}

/// upstream test_bit_set_symmetric_difference_with
/// (tests/set.rs:316-343): the grow face against a byte-built
/// expectation, the memberless no-op face, and the standard face.
pub exec fn ut_symmetric_difference_with() -> (r: u64)
    ensures
        r == 4u64,
{
    // part 1: a should grow to include the larger elements
    let mut a = BitSet::new();
    a.insert(0);
    a.insert(1);
    let ghost pa = a;
    let mut b = BitSet::new();
    b.insert(1);
    b.insert(5);
    let ghost pb = b;
    let bytes_e: &[u8] = &[0b10000100];
    let expected = BitSet::from_bytes(bytes_e); // {0, 5}
    a.symmetric_difference_with(&b);
    proof {
        lemma_face_84(&expected, bytes_e);
        assert(a.bit_vec.nbits == 6usize);
        // {0, 1} XOR {1, 5} = {0, 5} over the 6-bit universe
        assert forall|j: usize| #[trigger] bs_at(&a, j) == (j == 0 || j == 5) by {
            if (j as int) < 6int {
                assert(bs_at(&pa, j) == (j == 0 || j == 1));
                assert(bs_at(&pb, j) == (j == 1 || j == 5));
                assert(bs_at(&a, j) == (bs_at(&pa, j) != bs_at(&pb, j)));
            } else {
                assert(bs_at(&a, j) == false);
                assert(!(j == 0 || j == 5));
            }
        }
        assert forall|j: usize| j < bs_max_nb(&a, &expected)
            implies (bs_at(&a, j) == bs_at(&expected, j)) by {
            if (j as int) < 8int {
                assert(bs_at(&a, j) == (j == 0 || j == 5));
                assert(bs_at(&expected, j) == (j == 0 || j == 5));
            }
        }
    }
    let e1 = a.eq(&expected);
    assert(e1 == true);

    // part 2: XOR with the empty set is unchanged
    let bytes_a: &[u8] = &[0b10100010];
    let mut a2 = BitSet::from_bytes(bytes_a); // {0, 2, 6}
    let b2 = BitSet::new();
    let c2 = a2.clone();
    proof {
        lemma_face_a2(&a2, bytes_a);
    }
    let ghost pa2 = a2;
    a2.symmetric_difference_with(&b2);
    proof {
        assert forall|j: usize| #[trigger] bs_at(&a2, j) == (j == 0 || j == 2 || j == 6) by {
            if (j as int) < 8int {
                assert(bs_at(&pa2, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&b2, j) == false);
                assert(bs_at(&a2, j) == (bs_at(&pa2, j) != bs_at(&b2, j)));
            } else {
                assert(bs_at(&a2, j) == false);
                assert(!(j == 0 || j == 2 || j == 6));
            }
        }
        assert forall|j: usize| j < bs_max_nb(&a2, &c2)
            implies (bs_at(&a2, j) == bs_at(&c2, j)) by {
            if (j as int) < 8int {
                assert(bs_at(&a2, j) == (j == 0 || j == 2 || j == 6));
                assert(bs_at(&c2, j) == (j == 0 || j == 2 || j == 6));
            }
        }
    }
    let e2 = a2.eq(&c2);
    assert(e2 == true);

    // part 3: the standard face, both directions
    let bytes_x: &[u8] = &[0b11100010];
    let bytes_y: &[u8] = &[0b01101010];
    let mut a3 = BitSet::from_bytes(bytes_x); // {0, 1, 2, 6}
    let mut b3 = BitSet::from_bytes(bytes_y); // {1, 2, 4, 6}
    let c3 = a3.clone();
    proof {
        lemma_face_e2(&a3, bytes_x);
        lemma_face_6a(&b3, bytes_y);
    }
    let ghost pa3 = a3;
    let ghost pb3 = b3;
    a3.symmetric_difference_with(&b3);
    let cnt_a = a3.count();
    proof {
        // {0, 4}
        let s = a3.bit_vec.storage@;
        let n = a3.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&a3, j) == (j == 0 || j == 4) by {
            if (j as int) < 8int {
                assert(bs_at(&pa3, j) == (j == 0 || j == 1 || j == 2 || j == 6));
                assert(bs_at(&pb3, j) == (j == 1 || j == 2 || j == 4 || j == 6));
                assert(bs_at(&a3, j) == (bs_at(&pa3, j) != bs_at(&pb3, j)));
            } else {
                assert(bs_at(&a3, j) == false);
                assert(!(j == 0 || j == 4));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p == 0 || p == 4) by {
            if (p as int) < 8int {
                assert(bs_at(&a3, p) == bit_at(s, n, p));
                assert(bs_at(&a3, p) == (p == 0 || p == 4));
            }
        }
        assert forall|p: usize| 1 <= p && p < 4 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 5 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 0usize, 1usize, 4usize, 5usize);
        assert(count_bits(s, n, 0usize, n) == 2int);
        assert(bs_count(&a3) == 2int);
    }
    assert(cnt_a == 2usize);
    b3.symmetric_difference_with(&c3);
    let cnt_b = b3.count();
    proof {
        // {0, 4} again: {1, 2, 4, 6} XOR {0, 1, 2, 6}
        let s = b3.bit_vec.storage@;
        let n = b3.bit_vec.nbits;
        assert(n == 8usize);
        assert forall|j: usize| #[trigger] bs_at(&b3, j) == (j == 0 || j == 4) by {
            if (j as int) < 8int {
                assert(bs_at(&pb3, j) == (j == 1 || j == 2 || j == 4 || j == 6));
                assert(bs_at(&c3, j) == bs_at(&pa3, j));
                assert(bs_at(&pa3, j) == (j == 0 || j == 1 || j == 2 || j == 6));
                assert(bs_at(&b3, j) == (bs_at(&pb3, j) != bs_at(&c3, j)));
            } else {
                assert(bs_at(&b3, j) == false);
                assert(!(j == 0 || j == 4));
            }
        }
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(s, n, p) == (p == 0 || p == 4) by {
            if (p as int) < 8int {
                assert(bs_at(&b3, p) == bit_at(s, n, p));
                assert(bs_at(&b3, p) == (p == 0 || p == 4));
            }
        }
        assert forall|p: usize| 1 <= p && p < 4 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 5 <= p && p < 8 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 0usize, 1usize, 4usize, 5usize);
        assert(count_bits(s, n, 0usize, n) == 2int);
        assert(bs_count(&b3) == 2int);
    }
    assert(cnt_b == 2usize);
    4u64
}

/// upstream test_bit_set_frombit_vec_init (tests/set.rs:63-75): the
/// from_elem mask face at the length boundary, for both bool fills.
pub exec fn from_elem_roundtrip_check(l: usize, fill: bool) -> (r: bool)
    requires
        2 <= l,
        l <= usize::MAX - 1,
    ensures
        r == fill,
{
    let bv = BitVec::from_elem(l, fill);
    let bs = BitSet::from_bit_vec(bv);
    let c1 = bs.contains(1);
    assert(c1 == fill);
    let c2 = bs.contains(l - 1);
    assert(c2 == fill);
    let c3 = bs.contains(l);
    assert(c3 == false);
    fill
}

/// upstream test_bit_set_frombit_vec_init (tests/set.rs:63-75): the
/// 2 x 3 matrix over lengths [10, 64, 100] and fills [true, false].
pub exec fn ut_frombit_vec_init() -> (r: u64)
    ensures
        r == 6u64,
{
    let r1 = from_elem_roundtrip_check(10usize, true);
    assert(r1 == true);
    let r2 = from_elem_roundtrip_check(64usize, true);
    assert(r2 == true);
    let r3 = from_elem_roundtrip_check(100usize, true);
    assert(r3 == true);
    let r4 = from_elem_roundtrip_check(10usize, false);
    assert(r4 == false);
    let r5 = from_elem_roundtrip_check(64usize, false);
    assert(r5 == false);
    let r6 = from_elem_roundtrip_check(100usize, false);
    assert(r6 == false);
    6u64
}

/// upstream test_bit_vec_masking (tests/set.rs:77-88): the 140-bit
/// all-ones mask, then insert past the universe: the grown gap stays
/// memberless while the new bit lands.
pub exec fn ut_bit_vec_masking() -> (r: u64)
    ensures
        r == 7u64,
{
    let bv = BitVec::from_elem(140, true);
    let mut bs = BitSet::from_bit_vec(bv);
    let c139 = bs.contains(139);
    assert(c139 == true);
    let c140 = bs.contains(140);
    assert(c140 == false);
    let was = bs.insert(150);
    assert(was == true);
    proof {
        // the insert face over the grown 151-bit universe: the old
        // mask below 140, the grown gap [140, 150) memberless, the new
        // bit at 150
        assert forall|j: usize| #[trigger] bs_at(&bs, j)
            == ((j as int) < 140int || j == 150) by { }
        assert(!bs_at(&bs, 140));
        assert(!bs_at(&bs, 149));
        assert(bs_at(&bs, 150));
        assert(!bs_at(&bs, 151));
    }
    // drive the four boundary reads through the contract directly
    let c140b = bs.contains(140);
    assert(c140b == false);
    let c149 = bs.contains(149);
    assert(c149 == false);
    let c150 = bs.contains(150);
    assert(c150 == true);
    let c151 = bs.contains(151);
    assert(c151 == false);
    7u64
}

/// upstream test_truncate (tests/set.rs:492-514): the six-0xFF-byte
/// universe ratchets down through truncate, each step equal to the
/// byte-prefix set and counted.
pub exec fn ut_truncate() -> (r: u64)
    ensures
        r == 10u64,
{
    let bytes6: &[u8] = &[0b11111111, 0b11111111, 0b11111111,
        0b11111111, 0b11111111, 0b11111111];
    let bytes5: &[u8] = &[0b11111111, 0b11111111, 0b11111111,
        0b11111111, 0b11111111];
    let bytes4: &[u8] = &[0b11111111, 0b11111111, 0b11111111, 0b11111111];
    let bytes1: &[u8] = &[0b11111111];
    let bytes0: &[u8] = &[];
    let mut s = BitSet::from_bytes(bytes6);
    proof { lemma_all_ff_face(&s, bytes6); }

    // step 1: truncate(5 * 8) -- equals the 5-byte prefix, 40 members
    s.truncate(40);
    let e5 = BitSet::from_bytes(bytes5);
    let eq1 = s.eq(&e5);
    let cnt1 = s.count();
    proof {
        assert(s.bit_vec.nbits == 40usize);
        lemma_all_ff_face(&e5, bytes5);
        assert forall|j: usize| #[trigger] bs_at(&s, j)
            == ((j as int) < 40int) by { }
        assert forall|j: usize| j < bs_max_nb(&s, &e5)
            implies (bs_at(&s, j) == bs_at(&e5, j)) by { }
        let st = s.bit_vec.storage@;
        let n = s.bit_vec.nbits;
        assert forall|p: usize| (p as int) < 40int
            ==> bit_at(st, n, p) by {
            if (p as int) < 40int {
                assert(bs_at(&s, p) == ((p as int) < 40int));
                assert(bs_at(&s, p) == bit_at(st, n, p));
            }
        }
        lemma_count_const(st, n, true);
        assert(count_bits(st, n, 0usize, n) == 40int);
        assert(bs_count(&s) == 40int);
    }
    assert(eq1 == true);
    assert(cnt1 == 40usize);

    // step 2: truncate(4 * 8)
    s.truncate(32);
    let e4 = BitSet::from_bytes(bytes4);
    let eq2 = s.eq(&e4);
    let cnt2 = s.count();
    proof {
        assert(s.bit_vec.nbits == 32usize);
        lemma_all_ff_face(&e4, bytes4);
        assert forall|j: usize| #[trigger] bs_at(&s, j)
            == ((j as int) < 32int) by { }
        assert forall|j: usize| j < bs_max_nb(&s, &e4)
            implies (bs_at(&s, j) == bs_at(&e4, j)) by { }
        let st = s.bit_vec.storage@;
        let n = s.bit_vec.nbits;
        assert forall|p: usize| (p as int) < 32int
            ==> bit_at(st, n, p) by {
            if (p as int) < 32int {
                assert(bs_at(&s, p) == ((p as int) < 32int));
                assert(bs_at(&s, p) == bit_at(st, n, p));
            }
        }
        lemma_count_const(st, n, true);
        assert(count_bits(st, n, 0usize, n) == 32int);
        assert(bs_count(&s) == 32int);
    }
    assert(eq2 == true);
    assert(cnt2 == 32usize);

    // step 3: truncating to a size > len is a noop
    s.truncate(40);
    let eq3 = s.eq(&e4);
    let cnt3 = s.count();
    proof {
        assert(s.bit_vec.nbits == 32usize);
        assert forall|j: usize| #[trigger] bs_at(&s, j)
            == ((j as int) < 32int) by { }
        assert forall|j: usize| j < bs_max_nb(&s, &e4)
            implies (bs_at(&s, j) == bs_at(&e4, j)) by { }
        let st = s.bit_vec.storage@;
        let n = s.bit_vec.nbits;
        assert forall|p: usize| (p as int) < 32int
            ==> bit_at(st, n, p) by {
            if (p as int) < 32int {
                assert(bs_at(&s, p) == ((p as int) < 32int));
                assert(bs_at(&s, p) == bit_at(st, n, p));
            }
        }
        lemma_count_const(st, n, true);
        assert(count_bits(st, n, 0usize, n) == 32int);
        assert(bs_count(&s) == 32int);
    }
    assert(eq3 == true);
    assert(cnt3 == 32usize);

    // step 4: truncate(8)
    s.truncate(8);
    let e1 = BitSet::from_bytes(bytes1);
    let eq4 = s.eq(&e1);
    let cnt4 = s.count();
    proof {
        assert(s.bit_vec.nbits == 8usize);
        lemma_all_ff_face(&e1, bytes1);
        assert forall|j: usize| #[trigger] bs_at(&s, j)
            == ((j as int) < 8int) by { }
        assert forall|j: usize| j < bs_max_nb(&s, &e1)
            implies (bs_at(&s, j) == bs_at(&e1, j)) by { }
        let st = s.bit_vec.storage@;
        let n = s.bit_vec.nbits;
        assert forall|p: usize| (p as int) < 8int
            ==> bit_at(st, n, p) by {
            if (p as int) < 8int {
                assert(bs_at(&s, p) == ((p as int) < 8int));
                assert(bs_at(&s, p) == bit_at(st, n, p));
            }
        }
        lemma_count_const(st, n, true);
        assert(count_bits(st, n, 0usize, n) == 8int);
        assert(bs_count(&s) == 8int);
    }
    assert(eq4 == true);
    assert(cnt4 == 8usize);

    // step 5: truncate(0) -- the empty set
    s.truncate(0);
    let e0 = BitSet::from_bytes(bytes0);
    let eq5 = s.eq(&e0);
    let cnt5 = s.count();
    proof {
        assert(s.bit_vec.nbits == 0usize);
        assert forall|j: usize| #[trigger] bs_at(&s, j)
            == ((j as int) < 0int) by { }
        assert forall|j: usize| j < bs_max_nb(&s, &e0)
            implies (bs_at(&s, j) == bs_at(&e0, j)) by { }
        let st = s.bit_vec.storage@;
        let n = s.bit_vec.nbits;
        assert(count_bits(st, n, 0usize, n) == 0int);
        assert(bs_count(&s) == 0int);
    }
    assert(eq5 == true);
    assert(cnt5 == 0usize);
    10u64
}

/// upstream test_bit_set_shrink_to_fit_new (tests/set.rs:373-393): the
/// empty-set and single-member bookkeeping faces across both shrinks.
/// The four capacity sub-asserts (upstream tests/set.rs:380/383/388/392)
/// are allocator-runtime faces (recorded as
/// out of scope in the batch notes); everything else closes, riding the
/// batch-H3 append rows of shrink_to_fit (the kept-length bound pins
/// the post-shrink universe, the full-range member row preserves the
/// predicate everywhere).
pub exec fn ut_shrink_to_fit_new() -> (r: u64)
    ensures
        r == 7u64,
{
    let mut a = BitSet::new();
    let cnt1 = a.count();
    assert(cnt1 == 0usize);
    // upstream: assert_eq!(a.capacity(), 0) -- allocator-runtime face,
    // out of scope for the verifier layer (spec_bit_capacity only
    // carries the free-of-resize direction; batch note).
    let ghost pe = a;
    a.shrink_to_fit();
    // the pre-state universe is empty (0 blocks), so the kept-length
    // row pins the post-state universe to 0: the set stayed empty
    let cnt2 = a.count();
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert((pe.bit_vec.nbits as int) == 0);
        assert((pe.bit_vec.storage@.len() as int) == 0);
        assert((n as int) <= 32 * (pe.bit_vec.storage@.len() as int));
        assert(n == 0usize);
        assert(count_bits(s, n, 0usize, n) == 0int);
        assert(bs_count(&a) == 0int);
    }
    assert(cnt2 == 0usize);
    // upstream: assert_eq!(a.capacity(), 0) (tests/set.rs:383) --
    // allocator face, out of scope.
    let ncc1 = a.contains(1);
    assert(ncc1 == false);
    a.insert(3);
    let cc1 = a.contains(3);
    assert(cc1 == true);
    let cnt3 = a.count();
    proof {
        // {3} over the 4-bit universe
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert(n == 4usize);
        assert forall|j: usize| #[trigger] bs_at(&a, j) == (j == 3) by { }
        assert forall|p: usize| (p as int) < 4int
            ==> bit_at(s, n, p) == (p == 3) by {
            if (p as int) < 4int {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == (p == 3));
            }
        }
        assert forall|p: usize| 0 <= p && p < 3 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 3usize, 4usize, 4usize, 4usize);
        assert(count_bits(s, n, 0usize, n) == 1int);
        assert(bs_count(&a) == 1int);
    }
    assert(cnt3 == 1usize);
    // upstream: assert!(a.capacity() > 0) (tests/set.rs:388) --
    // allocator face, out of scope.
    let ghost pa = a;
    a.shrink_to_fit();
    // the member survives the shrink; the post-shrink universe is the
    // one kept block (n == 32: the block count only drops), so the
    // count face re-derives over it
    let cc2 = a.contains(3);
    assert(cc2 == true);
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert((pa.bit_vec.storage@.len() as int) == 1);
        assert((n as int) <= 32 * (pa.bit_vec.storage@.len() as int));
        assert(bs_at(&a, 3));
        assert((n as int) >= 4int);
        assert(n % 32 == 0);
        assert(n == 32usize);
        assert forall|j: usize| #[trigger] bs_at(&a, j) == (j == 3) by {
            if true {
                assert(bs_at(&pa, j) == (j == 3));
                assert(bs_at(&a, j) == bs_at(&pa, j));
            }
        }
        assert forall|p: usize| (p as int) < 32int
            ==> bit_at(s, n, p) == (p == 3) by {
            if (p as int) < 32int {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == (p == 3));
            }
        }
        assert forall|p: usize| 0 <= p && p < 3 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 4 <= p && p < 32 ==> !bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 3usize, 4usize, 4usize, 4usize);
        assert(count_bits(s, n, 0usize, n) == 1int);
        assert(bs_count(&a) == 1int);
    }
    let cnt4 = a.count();
    assert(cnt4 == 1usize);
    // upstream: assert!(a.capacity() > 0) (tests/set.rs:392) --
    // allocator face, out of scope.
    7u64
}

/// upstream test_bit_set_shrink_to_fit (tests/set.rs:395-456): the
/// multi-member bookkeeping faces across four shrink chapters and a
/// make_empty reset. The seven capacity sub-asserts
/// (upstream tests/set.rs:399/404/416/421/430/438/448) are
/// allocator-runtime faces (out of scope, batch note); every
/// count/contains sub-assert
/// closes, riding the batch-H3 append rows of shrink_to_fit.
pub exec fn ut_shrink_to_fit() -> (r: u64)
    ensures
        r == 35u64,
{
    let mut a = BitSet::new();
    let cnt1 = a.count();
    assert(cnt1 == 0usize);
    // upstream: assert_eq!(a.capacity(), 0) (tests/set.rs:399) --
    // allocator face, out of scope.
    a.insert(259);
    a.insert(98);
    a.insert(3);
    let cnt2 = a.count();
    proof {
        // {3, 98, 259} over the 260-bit universe: three single-member
        // ranges assembled through the split lemmas
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert(n == 260usize);
        assert forall|j: usize| #[trigger] bs_at(&a, j)
            == (j == 3 || j == 98 || j == 259) by { }
        assert forall|p: usize| (p as int) < 260int
            ==> bit_at(s, n, p) == (p == 3 || p == 98 || p == 259) by {
            if (p as int) < 260int {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == (p == 3 || p == 98 || p == 259));
            }
        }
        assert forall|p: usize| 0 <= p && p < 3 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 3 <= p && p < 4 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 4 <= p && p < 98 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 98 <= p && p < 99 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 99 <= p && p < 259 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 259 <= p && p < 260 ==> bit_at(s, n, p) by { }
        lemma_count_range_const(s, n, 0usize, 3usize, false);
        lemma_count_range_const(s, n, 3usize, 4usize, true);
        lemma_count_range_const(s, n, 4usize, 98usize, false);
        lemma_count_range_const(s, n, 98usize, 99usize, true);
        lemma_count_range_const(s, n, 99usize, 259usize, false);
        lemma_count_range_const(s, n, 259usize, 260usize, true);
        lemma_count_split(s, n, 99usize, 259usize, 260usize);
        lemma_count_split(s, n, 98usize, 99usize, 260usize);
        lemma_count_split(s, n, 4usize, 98usize, 260usize);
        lemma_count_split(s, n, 3usize, 4usize, 260usize);
        lemma_count_split(s, n, 0usize, 3usize, 260usize);
        assert(count_bits(s, n, 0usize, n) == 3int);
        assert(bs_count(&a) == 3int);
    }
    assert(cnt2 == 3usize);
    // upstream: assert!(a.capacity() > 0) -- allocator face, out of scope.
    let ncc1 = a.contains(1);
    assert(ncc1 == false);
    let cc259 = a.contains(259);
    assert(cc259 == true);
    let cc98 = a.contains(98);
    assert(cc98 == true);
    let cc3 = a.contains(3);
    assert(cc3 == true);

    // chapter 1: the first shrink keeps all three members and the count
    let ghost pa = a;
    a.shrink_to_fit();
    let ncc2 = a.contains(1);
    assert(ncc2 == false);
    let cc259b = a.contains(259);
    assert(cc259b == true);
    let cc98b = a.contains(98);
    assert(cc98b == true);
    let cc3b = a.contains(3);
    assert(cc3b == true);
    let cnt3 = a.count();
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        // universe: 9 blocks before, membership at 259 above, the
        // kept-length row caps n at 9 * 32 = 288, and n is a whole
        // block count -- so the trailing pad region [260, n) is the
        // false tail of the member face
        assert((pa.bit_vec.storage@.len() as int) == 9);
        assert((n as int) <= 32 * (pa.bit_vec.storage@.len() as int));
        assert(bs_at(&a, 259));
        assert((n as int) >= 260int);
        assert forall|j: usize| #[trigger] bs_at(&a, j)
            == (j == 3 || j == 98 || j == 259) by {
            if true {
                assert(bs_at(&pa, j) == (j == 3 || j == 98 || j == 259));
                assert(bs_at(&a, j) == bs_at(&pa, j));
            }
        }
        assert forall|p: usize| (p as int) < (n as int)
            ==> bit_at(s, n, p) == (p == 3 || p == 98 || p == 259) by {
            if (p as int) < (n as int) {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == (p == 3 || p == 98 || p == 259));
            }
        }
        assert forall|p: usize| 0 <= p && p < 3 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 3 <= p && p < 4 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 4 <= p && p < 98 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 98 <= p && p < 99 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 99 <= p && p < 259 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 259 <= p && p < 260 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 260 <= p && p < n ==> !bit_at(s, n, p) by { }
        lemma_count_range_const(s, n, 0usize, 3usize, false);
        lemma_count_range_const(s, n, 3usize, 4usize, true);
        lemma_count_range_const(s, n, 4usize, 98usize, false);
        lemma_count_range_const(s, n, 98usize, 99usize, true);
        lemma_count_range_const(s, n, 99usize, 259usize, false);
        lemma_count_range_const(s, n, 259usize, 260usize, true);
        lemma_count_range_const(s, n, 260usize, n, false);
        lemma_count_split(s, n, 259usize, 260usize, n);
        lemma_count_split(s, n, 99usize, 259usize, n);
        lemma_count_split(s, n, 98usize, 99usize, n);
        lemma_count_split(s, n, 4usize, 98usize, n);
        lemma_count_split(s, n, 3usize, 4usize, n);
        lemma_count_split(s, n, 0usize, 3usize, n);
        assert(count_bits(s, n, 0usize, n) == 3int);
        assert(bs_count(&a) == 3int);
    }
    assert(cnt3 == 3usize);
    // upstream: assert!(a.capacity() > 0) (tests/set.rs:416) --
    // allocator face, out of scope.
    // upstream: capacity < old_cap after the next chapter (421) -- out of scope.

    let rem = a.remove(259);
    assert(rem == true);
    // chapter 2: the second shrink over the {3, 98} residue
    let ghost pb = a;
    a.shrink_to_fit();
    let ncc3 = a.contains(1);
    assert(ncc3 == false);
    let ncc259 = a.contains(259);
    assert(ncc259 == false);
    let cc98c = a.contains(98);
    assert(cc98c == true);
    let cc3c = a.contains(3);
    assert(cc3c == true);
    let cnt4 = a.count();
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert((n as int) <= 32 * (pb.bit_vec.storage@.len() as int));
        assert(bs_at(&a, 98));
        assert((n as int) >= 99int);
        assert forall|j: usize| #[trigger] bs_at(&a, j) == (j == 3 || j == 98) by {
            if true {
                assert(bs_at(&pb, j) == (j == 3 || j == 98));
                assert(bs_at(&a, j) == bs_at(&pb, j));
            }
        }
        assert forall|p: usize| (p as int) < (n as int)
            ==> bit_at(s, n, p) == (p == 3 || p == 98) by {
            if (p as int) < (n as int) {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == (p == 3 || p == 98));
            }
        }
        assert forall|p: usize| 0 <= p && p < 3 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 3 <= p && p < 4 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 4 <= p && p < 98 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 98 <= p && p < 99 ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 99 <= p && p < n ==> !bit_at(s, n, p) by { }
        lemma_count_range_const(s, n, 0usize, 3usize, false);
        lemma_count_range_const(s, n, 3usize, 4usize, true);
        lemma_count_range_const(s, n, 4usize, 98usize, false);
        lemma_count_range_const(s, n, 98usize, 99usize, true);
        lemma_count_range_const(s, n, 99usize, n, false);
        lemma_count_split(s, n, 98usize, 99usize, n);
        lemma_count_split(s, n, 4usize, 98usize, n);
        lemma_count_split(s, n, 3usize, 4usize, n);
        lemma_count_split(s, n, 0usize, 3usize, n);
        assert(count_bits(s, n, 0usize, n) == 2int);
        assert(bs_count(&a) == 2int);
    }
    assert(cnt4 == 2usize);

    // make_empty: capacity preserved (allocator face), members cleared
    a.make_empty();
    let cnt5 = a.count();
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        // make_empty keeps the universe; the memberless face gives the
        // all-false cover over it
        assert(bs_at(&a, 98) == false) by { }
        assert forall|j: usize| #[trigger] bs_at(&a, j) == false by { }
        assert forall|p: usize| (p as int) < (n as int)
            ==> !bit_at(s, n, p) by {
            if (p as int) < (n as int) {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == false);
            }
        }
        lemma_count_const(s, n, false);
        assert(count_bits(s, n, 0usize, n) == 0int);
        assert(bs_count(&a) == 0int);
    }
    assert(cnt5 == 0usize);
    let ncc4 = a.contains(1);
    assert(ncc4 == false);
    let ncc259b = a.contains(259);
    assert(ncc259b == false);
    let ncc98 = a.contains(98);
    assert(ncc98 == false);
    let ncc3 = a.contains(3);
    assert(ncc3 == false);

    // insert(512): the fresh lone member grows the universe to 513
    proof {
        assert((a.bit_vec.nbits as int) < 512int);
    }
    a.insert(512);
    // upstream: assert!(a.capacity() > 0) (tests/set.rs:438) --
    // allocator face, out of scope.
    proof {
        assert(a.bit_vec.nbits == 513usize);
    }
    let cnt6 = a.count();
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert forall|j: usize| #[trigger] bs_at(&a, j) == (j == 512) by { }
        assert forall|p: usize| (p as int) < 513int
            ==> bit_at(s, n, p) == (p == 512) by {
            if (p as int) < 513int {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == (p == 512));
            }
        }
        assert forall|p: usize| 0 <= p && p < 512 ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 512 <= p && p < 513 ==> bit_at(s, n, p) by { }
        lemma_count_two_ranges(s, n, 0usize, 0usize, 512usize, 513usize);
        assert(count_bits(s, n, 0usize, n) == 1int);
        assert(bs_count(&a) == 1int);
    }
    assert(cnt6 == 1usize);
    let cc512 = a.contains(512);
    assert(cc512 == true);
    let ncc5 = a.contains(1);
    assert(ncc5 == false);
    let ncc259c = a.contains(259);
    assert(ncc259c == false);
    let ncc98b = a.contains(98);
    assert(ncc98b == false);
    let ncc3b = a.contains(3);
    assert(ncc3b == false);

    let rem2 = a.remove(512);
    assert(rem2 == true);
    // chapter 4: the final shrink of the empty universe
    let ghost pc = a;
    a.shrink_to_fit();
    // upstream: capacity == 0 (allocator face) -- out of scope; the
    // count and the six non-members close on the append rows
    let cnt7 = a.count();
    proof {
        let s = a.bit_vec.storage@;
        let n = a.bit_vec.nbits;
        assert forall|j: usize| #[trigger] bs_at(&a, j) == false by {
            if true {
                assert(bs_at(&pc, j) == false);
                assert(bs_at(&a, j) == bs_at(&pc, j));
            }
        }
        assert forall|p: usize| (p as int) < (n as int)
            ==> !bit_at(s, n, p) by {
            if (p as int) < (n as int) {
                assert(bs_at(&a, p) == bit_at(s, n, p));
                assert(bs_at(&a, p) == false);
            }
        }
        lemma_count_const(s, n, false);
        assert(count_bits(s, n, 0usize, n) == 0int);
        assert(bs_count(&a) == 0int);
    }
    assert(cnt7 == 0usize);
    let ncc512 = a.contains(512);
    assert(ncc512 == false);
    let ncc1f = a.contains(1);
    assert(ncc1f == false);
    let ncc259d = a.contains(259);
    assert(ncc259d == false);
    let ncc98c = a.contains(98);
    assert(ncc98c == false);
    let ncc3c = a.contains(3);
    assert(ncc3c == false);
    let ncc0 = a.contains(0);
    assert(ncc0 == false);
    35u64
}

} // verus!

fn main() {}
