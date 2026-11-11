//! bit-vec 0.10.1 x Verus -- coverage diff-set batch A harness
//! (popcount family + byte family).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here.
//! Coverage (out/harness-inventory.md diff-set batch A):
//!   - count_ones / count_zeros (popcount through the bit-level count
//!     model; upstream examples at both 100-bit shapes)
//!   - to_bytes / from_bytes (first bit becomes the high-order bit of
//!     the first byte; each byte's most significant bits come first)
//!   - to_bytes -> from_bytes roundtrip on the bit view

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitvec_lib;

verus! {

use bitvec_lib::{BitVec, bit_u8, bit_at, from_bytes_bit, count_ones_spec,
    lemma_count_const, lemma_count_const_except};

/// Upstream doc example (lib.rs:1290-1297): from_elem(100, true) has 100
/// ones; after set(50, false), 99.
pub exec fn ut_count_ones_from_elem100() -> (r: u64)
    ensures
        r == 99,
{
    let mut bv = BitVec::from_elem(100, true);
    let c0 = bv.count_ones();
    assert(c0 as int == 100) by {
        lemma_count_const(bv.storage@, 100, true);
    }
    bv.set(50, false);
    let c1 = bv.count_ones();
    assert(c1 as int == 99) by {
        lemma_count_const_except(bv.storage@, 100, 50, true);
    }
    c1
}

/// Upstream doc example (lib.rs:1312-1320): from_elem(100, false) has 100
/// zeros; after set(50, true), 99.
pub exec fn ut_count_zeros_from_elem100() -> (r: u64)
    ensures
        r == 99,
{
    let mut bv = BitVec::from_elem(100, false);
    let z0 = bv.count_zeros();
    assert(z0 as int == 100) by {
        lemma_count_const(bv.storage@, 100, false);
    }
    bv.set(50, true);
    let z1 = bv.count_zeros();
    assert(z1 as int == 99) by {
        lemma_count_const_except(bv.storage@, 100, 50, false);
    }
    z1
}

/// Popcounts on a small hand-built state (1 block, 5 used bits, one set).
pub exec fn ut_count_ones_handbuilt()
{
    let mut bv = BitVec::from_elem(5, false);
    bv.set(2, true);
    let ones = bv.count_ones();
    let zeros = bv.count_zeros();
    assert(ones as int == 1) by {
        lemma_count_const_except(bv.storage@, 5, 2, false);
    }
    assert(zeros as int == 4) by {
        assert(count_ones_spec(&bv) == 1);
    }
}

pub exec fn ut_to_bytes_doc()
{
    let mut bv = BitVec::from_elem(3, true);
    bv.set(1, false);
    let bytes = bv.to_bytes();
    assert(bytes@.len() == 1) by { }
    // the first bit becomes the high-order bit of the first byte
    assert(bit_u8(bytes@[0 as int], (7 - (0 as int))) == true);
    assert(bit_u8(bytes@[0], 7) == true);
    assert(bit_u8(bytes@[0 as int], (7 - (1 as int))) == false);
    assert(bit_u8(bytes@[0], 6) == false);
    assert(bit_u8(bytes@[0 as int], (7 - (2 as int))) == true);
    assert(bit_u8(bytes@[0], 5) == true);

    let mut bv9 = BitVec::from_elem(9, false);
    bv9.set(2, true);
    bv9.set(8, true);
    let bytes9 = bv9.to_bytes();
    assert(bytes9@.len() == 2) by { }
    assert(bit_u8(bytes9@[0 as int], (7 - (2 as int))) == true);
    assert(bit_u8(bytes9@[0], 5) == true);
    assert(bit_u8(bytes9@[1 as int], (7 - (0 as int))) == true);
    assert(bit_u8(bytes9@[1], 7) == true);
    assert(bit_u8(bytes9@[1 as int], (7 - (1 as int))) == false);
    assert(bit_u8(bytes9@[1], 6) == false);
}

/// Upstream doc example (lib.rs:481-490): each byte's most significant
/// bits come first.
pub exec fn ut_from_bytes_doc()
{
    let bytes: &[u8] = &[0b10100000, 0b00010010];
    let bv = BitVec::from_bytes(bytes);
    let n = bv.len();
    assert(n == 16) by { }
    // bit 0: the high bit of the first byte 0b10100000 (set)
    let g0 = bv.get(0);
    assert(g0 == Some(true)) by {
        assert(bytes@[0 as int] == 0b10100000);
        assert(from_bytes_bit(bytes@, 0)
            == ((bytes@[(0usize / 8) as int] & (1u8 << (7 - (0usize % 8)))) != 0u8));
        assert((1u8 << (7 - (0usize % 8))) == 128u8) by (bit_vector);
        assert((0b10100000u8 & 128u8) != 0u8) by (bit_vector);
    }
    // bit 1: clear
    let g1 = bv.get(1);
    assert(g1 == Some(false)) by {
        assert(bytes@[0 as int] == 0b10100000);
        assert(from_bytes_bit(bytes@, 1)
            == ((bytes@[(1usize / 8) as int] & (1u8 << (7 - (1usize % 8)))) != 0u8));
        assert((1u8 << (7 - (1usize % 8))) == 64u8) by (bit_vector);
        assert((0b10100000u8 & 64u8) == 0u8) by (bit_vector);
    }
    // bit 2: set (the third bit of 101...)
    let g2 = bv.get(2);
    assert(g2 == Some(true)) by {
        assert(bytes@[0 as int] == 0b10100000);
        assert(from_bytes_bit(bytes@, 2)
            == ((bytes@[(2usize / 8) as int] & (1u8 << (7 - (2usize % 8)))) != 0u8));
        assert((1u8 << (7 - (2usize % 8))) == 32u8) by (bit_vector);
        assert((0b10100000u8 & 32u8) != 0u8) by (bit_vector);
    }
    // bit 11: the 1 of the second byte 0b00010010 (byte bit 4)
    let g11 = bv.get(11);
    assert(g11 == Some(true)) by {
        assert(bytes@[1 as int] == 0b00010010);
        assert(from_bytes_bit(bytes@, 11)
            == ((bytes@[(11usize / 8) as int] & (1u8 << (7 - (11usize % 8)))) != 0u8));
        assert((1u8 << (7 - (11usize % 8))) == 16u8) by (bit_vector);
        assert((0b00010010u8 & 16u8) != 0u8) by (bit_vector);
    }
    // bit 14: the 1 of 0010 (byte bit 1)
    let g14 = bv.get(14);
    assert(g14 == Some(true)) by {
        assert(bytes@[1 as int] == 0b00010010);
        assert(from_bytes_bit(bytes@, 14)
            == ((bytes@[(14usize / 8) as int] & (1u8 << (7 - (14usize % 8)))) != 0u8));
        assert((1u8 << (7 - (14usize % 8))) == 2u8) by (bit_vector);
        assert((0b00010010u8 & 2u8) != 0u8) by (bit_vector);
    }
}

/// to_bytes -> from_bytes roundtrip: the packed bytes decode back to the
/// same bit values (bitwise, over all used positions).
pub exec fn ut_byte_roundtrip()
{
    let mut bv = BitVec::from_elem(13, false);
    bv.set(0, true);
    bv.set(4, true);
    bv.set(12, true);
    let packed = bv.to_bytes();
    assert(packed@.len() == 2) by { }
    let packed_slice: &[u8] = &packed;
    let back = BitVec::from_bytes(packed_slice);
    let nback = back.len();
    assert(nback == 16) by {
        assert(packed_slice@.len() == 2);
    }
    // bitwise equality of the decode against the source over the 13 used
    // positions (the two packed bytes decode to 16 bits; positions past 13
    // are the padded zeros)
    assert forall|i: usize| i < 13 implies
        bit_at(back.storage@, 16, i) == bit_at(bv.storage@, 13, i) by {
        let j = i / 8;
        let q = i % 8;
        assert(i == 8 * j + q);
        // from_bytes def view on the packed slice
        assert(from_bytes_bit(packed_slice@, i)
            == ((packed_slice@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8));
        // to_bytes side: byte j bit 7-q mirrors source bit 8j+q
        assert(bit_u8(packed@[j as int], (7 - (q as int)))
            == bit_at(bv.storage@, 13, (8 * j + q) as usize)) by {
            assert((8 * j + q) < 13) by {
                assert(i < 13);
                assert(i == 8 * j + q);
            }
        }
        // bit_u8 def view on the packed word
        assert(bit_u8(packed@[j as int], (7 - (q as int)))
            == (((packed@[j as int] & (1u8 << ((7 - (q as int)) as u8))) != 0u8)));
        // bridge the two byte-bit mask forms (same mask value)
        assert((7 - (i % 8)) == (7 - (q as int)));
        assert((1u8 << (7 - (i % 8))) == (1u8 << ((7 - (q as int)) as u8)));
    }
}

} // verus!

fn main() {}
