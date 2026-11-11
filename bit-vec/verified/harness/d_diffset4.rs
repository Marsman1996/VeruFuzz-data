//! bit-vec 0.10.1 x Verus -- coverage diff-set batch C harness
//! (the borrow family + the movers).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here.
//! Coverage (out/harness-inventory.md diff-set batch C):
//!   - iter / Iter::next / nth / next_back / size_hint (the cursor
//!     materialization: per-bit readout order, the exhaustion tier)
//!   - into_iter (the shared-borrow adapter + the owned IntoIter::next)
//!   - blocks / Blocks::next / next_back / size_hint (the block borrow)
//!   - Index<usize> (the get/unwrap semantics bridge)
//!   - append (doc-example shape: len 16 back, other emptied, both
//!     per-bit tiers)
//!   - split_off (the doc example: split at 2 of 4 bits; plus the
//!     tail-coincident slack shape storage.len == blocks_for_bits + 1
//!     the faithful transcription carries, runtime-confirmed in
//!     out/poc/splitoff-slack-block)
//!   - grow (the doc example, per-bit tiers) / shrink_to_fit

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitvec_lib;

verus! {

use bitvec_lib::BitVec;
use bitvec_lib::bit_at;
use bitvec_lib::blocks_for_bits;
use bitvec_lib::from_bytes_bit;

// ---------------------------------------------------------------------------
// the borrow family
// ---------------------------------------------------------------------------

/// per-position readout order: next walks the bit sequence from 0
fn ut_iter_reads_in_order()
{
    let mut b = BitVec::from_elem(4, true);
    b.set(0, false);
    b.set(2, true);
    let mut it = b.iter();
    let x0 = it.next();
    assert(x0 == Some(false)); // bit_at(0)
    let x1 = it.next();
    assert(x1 == Some(true)); // bit_at(1)
    let x2 = it.next();
    assert(x2 == Some(true)); // bit_at(2)
    let x3 = it.next();
    assert(x3 == Some(true)); // bit_at(3)
}

/// the exhaustion tier: after nbits reads, next yields None
fn ut_iter_exhausts_when_full()
{
    let b = BitVec::from_elem(3, true);
    let mut it = b.iter();
    assert(it.pos == 0);
    assert(it.end == 3);
    let _ = it.next();
    assert(it.pos == 1);
    let _ = it.next();
    assert(it.pos == 2);
    let _ = it.next();
    assert(it.pos == 3);
    assert(it.pos == it.end);
    let dn = it.next();
    assert(dn matches None);
}

/// nth skips n entries and reads the position bit
fn ut_iter_nth()
{
    let mut b = BitVec::from_elem(40, false);
    b.set(10, true);
    let mut it = b.iter();
    // nth(0) == next(): the first position readout
    let r0 = it.next();
    assert(r0 == Some(false));
    assert(it.pos == 1);
    // nth(9) lands on position 10, the set bit
    let r9 = it.nth(9);
    assert((1 + 9) < 40);
    assert(r9 is Some);
    assert(it.pos == 11);
    assert(r9 == Some(true));
    // the exhaustion end: nth past the top yields None and saturates
    let dn = it.nth(31);
    assert(dn matches None);
    assert(it.pos == 40);
}

/// next_back reads the top unreturned position
fn ut_iter_next_back()
{
    let mut b = BitVec::from_elem(35, false);
    b.set(33, true);
    let mut it = b.iter();
    let r = it.next_back();
    assert(r == Some(bit_at(b.storage@, b.nbits, 34)));
    let r2 = it.next_back();
    assert(r2 == Some(true)); // bit_at(33), the single one bit
}

/// size_hint: the remaining tier
fn ut_iter_size_hint()
{
    let bv = BitVec::from_elem(35, true);
    let mut it = bv.iter();
    let sh = it.size_hint();
    assert(sh.0 == 35);
    it.next();
    let sh2 = it.size_hint();
    assert(sh2.0 == 34);
}

/// the shared-borrow into_iter adapter of &BitVec
fn ut_into_iter_shared()
{
    let b = BitVec::from_elem(2, true);
    let mut it = bitvec_lib::bitvec_ref_into_iter(&b);
    let x0 = it.next();
    assert(x0 == Some(true)); // bit_at(0)
    let x1 = it.next();
    assert(x1 == Some(true)); // bit_at(1)
    let dn = it.next();
    assert(dn matches None);
}

/// the owned IntoIterator: the handover keeps the content sequence
fn ut_into_iter_owned()
{
    let mut b = BitVec::from_elem(5, false);
    b.set(2, true);
    let mut it = bitvec_lib::bitvec_into_iter(b); // the owned handover
    assert(it.pos == 0);
    assert(it.end == 5);
    let x0 = it.next();
    assert(x0 == Some(false)); // bit_at(0)
    let x1 = it.next();
    assert(x1 == Some(false)); // bit_at(1)
    let x2 = it.next();
    assert(x2 == Some(true)); // bit_at(2), the single one bit
    let sh = it.size_hint();
    assert(sh.0 == 2);
    let x3 = it.next();
    assert(x3 == Some(false)); // bit_at(3)
}

/// the block-level borrow: the storage stream in order, the exhaustion
fn ut_blocks_stream()
{
    let mut b = BitVec::from_elem(33, true);
    b.set(32, true);
    let mut blk = b.blocks();
    assert(blk.pos == 0);
    assert(blk.end == 2);
    let w0 = blk.next();
    assert(w0 == Some(b.storage@[0]));
    assert(blk.pos == 1);
    let w1 = blk.next();
    assert(w1 == Some(b.storage@[1]));
    assert(blk.pos == 2);
    let dn = blk.next();
    assert(dn matches None);
    assert(blk.pos == 2);
}

/// blocks: size_hint and next_back
fn ut_blocks_hint_next_back()
{
    let b = BitVec::from_elem(64, true);
    let mut blk = b.blocks();
    let sh = blk.size_hint();
    assert(sh.0 == 2);
    let wb = blk.next_back();
    assert(wb == Some(b.storage@[1]));
    let sh2 = blk.size_hint();
    assert(sh2.0 == 1);
}

/// the Index bridge: index_exec reads the get/unwrap tier
fn ut_index_exec()
{
    let mut b = BitVec::from_elem(5, false);
    b.set(3, true);
    let r = b.index_exec(3);
    assert(r == true);
    assert(r == bit_at(b.storage@, b.nbits, 3));
    let r0 = b.index_exec(0);
    assert(r0 == false);
    assert(r0 == bit_at(b.storage@, b.nbits, 0));
}

/// Index is the get doc example's array-indexing tier: bv[1] == true
/// over a one-byte pattern
fn ut_index_doc_example()
{
    let bytes: &[u8] = &[0b01110100];
    let bv = BitVec::from_bytes(bytes);
    assert(bv.nbits == 8);
    let r = bv.index_exec(1);
    assert(r == true) by {
        assert(bytes@[0 as int] == 0b01110100);
        assert(from_bytes_bit(bytes@, 1)
            == ((bytes@[(1usize / 8) as int] & (1u8 << (7 - (1usize % 8)))) != 0u8));
        assert((1u8 << (7 - (1usize % 8))) == 64u8) by (bit_vector);
        assert((0b01110100u8 & 64u8) != 0u8) by (bit_vector);
        assert(bit_at(bv.storage@, bv.nbits, 1) == true);
    }
    let r7 = bv.index_exec(7);
    assert(r7 == false) by {
        assert(bytes@[0 as int] == 0b01110100);
        assert(from_bytes_bit(bytes@, 7)
            == ((bytes@[(7usize / 8) as int] & (1u8 << (7 - (7usize % 8)))) != 0u8));
        assert((1u8 << (7 - (7usize % 8))) == 1u8) by (bit_vector);
        assert((0b01110100u8 & 1u8) == 0u8) by (bit_vector);
        assert(bit_at(bv.storage@, bv.nbits, 7) == false);
    }
}

/// the iter doc example tier: the one bits of a two-byte pattern, read
/// out in the sequence order
fn ut_iter_doc_pattern()
{
    let bytes: &[u8] = &[0b01110100, 0b10010010];
    let bv = BitVec::from_bytes(bytes);
    assert(bv.nbits == 16);
    // bit 1 of 0b01110100: set
    assert(bit_at(bv.storage@, bv.nbits, 1) == true) by {
        assert(bytes@[0 as int] == 0b01110100);
        assert(from_bytes_bit(bytes@, 1)
            == ((bytes@[(1usize / 8) as int] & (1u8 << (7 - (1usize % 8)))) != 0u8));
        assert((1u8 << (7 - (1usize % 8))) == 64u8) by (bit_vector);
        assert((0b01110100u8 & 64u8) != 0u8) by (bit_vector);
    }
    // bit 0 of 0b01110100: clear
    assert(bit_at(bv.storage@, bv.nbits, 0) == false) by {
        assert(bytes@[0 as int] == 0b01110100);
        assert(from_bytes_bit(bytes@, 0)
            == ((bytes@[(0usize / 8) as int] & (1u8 << (7 - (0usize % 8)))) != 0u8));
        assert((1u8 << (7 - (0usize % 8))) == 128u8) by (bit_vector);
        assert((0b01110100u8 & 128u8) == 0u8) by (bit_vector);
    }
    // bit 8, the high bit of 0b10010010: set
    assert(bit_at(bv.storage@, bv.nbits, 8) == true) by {
        assert(bytes@[1 as int] == 0b10010010);
        assert(from_bytes_bit(bytes@, 8)
            == ((bytes@[(8usize / 8) as int] & (1u8 << (7 - (8usize % 8)))) != 0u8));
        assert((1u8 << (7 - (8usize % 8))) == 128u8) by (bit_vector);
        assert((0b10010010u8 & 128u8) != 0u8) by (bit_vector);
    }
    // bit 14 of the second byte: set
    assert(bit_at(bv.storage@, bv.nbits, 14) == true) by {
        assert(bytes@[1 as int] == 0b10010010);
        assert(from_bytes_bit(bytes@, 14)
            == ((bytes@[(14usize / 8) as int] & (1u8 << (7 - (14usize % 8)))) != 0u8));
        assert((1u8 << (7 - (14usize % 8))) == 2u8) by (bit_vector);
        assert((0b10010010u8 & 2u8) != 0u8) by (bit_vector);
    }
    // next: positions 0 then 1 read back their bits
    let mut it = bv.iter();
    let n0 = it.next();
    assert(n0 == Some(false)); // bit_at(0) == false
    let n1 = it.next();
    assert(n1 == Some(true)); // bit_at(1) == true
}

// ---------------------------------------------------------------------------
// the movers
// ---------------------------------------------------------------------------


/// the append doc-example shapes: 16 bits back, other emptied; the
/// per-bit kept/appended tiers land at the boundary
fn ut_append_doc_shapes()
{
    let mut a = BitVec::from_elem(5, true);
    let mut b = BitVec::from_elem(11, false);
    let ghost pre_a = a.storage@;
    let ghost pre_b = b.storage@;
    a.append(&mut b);
    assert(a.nbits == 16);
    assert(b.nbits == 0);
    assert(b.storage@.len() == 0);
    // boundary reads: the last kept bit, the first and last appended bits
    assert(bit_at(a.storage@, a.nbits, 4) == true) by {
        assert(bit_at(a.storage@, a.nbits, 4) == bit_at(pre_a, 5, 4)); // kept
        assert(bit_at(pre_a, 5, 4) == true); // from_elem fill
    }
    assert(bit_at(a.storage@, a.nbits, (5 + 0) as usize) == false) by {
        assert(bit_at(a.storage@, a.nbits, (5 + 0) as usize)
            == bit_at(pre_b, 11, 0)); // appended tier
        assert(bit_at(pre_b, 11, 0) == false); // from_elem fill
    }
    assert(bit_at(a.storage@, a.nbits, (5 + 10) as usize) == false) by {
        assert(bit_at(a.storage@, a.nbits, (5 + 10) as usize)
            == bit_at(pre_b, 11, 10)); // appended tier
        assert(bit_at(pre_b, 11, 10) == false);
    }
}

/// the split_off doc example: split at 2 of [T,F,F,T]
fn ut_split_off_doc_example()
{
    let mut a = bitvec_lib::new();
    a.push(true);
    a.push(false);
    a.push(false);
    a.push(true);
    let b = a.split_off(2);
    assert(a.nbits == 2);
    assert(b.nbits == 2);
    assert(bit_at(a.storage@, a.nbits, 0) == true);
    assert(bit_at(a.storage@, a.nbits, 1) == false);
    assert(bit_at(b.storage@, b.nbits, 0) == false);
    assert(bit_at(b.storage@, b.nbits, 1) == true);
}

/// the tail-coincident slack shape: 34 bits split at 2 leaves the
/// returned vector with one surplus trailing zero block (the faithful
/// transcription's explicit slack clauses, runtime-confirmed)
fn ut_split_off_slack_shape()
{
    let mut a = BitVec::from_elem(34, true);
    let ghost pre_a = a.storage@;
    let b = a.split_off(2);
    assert(a.nbits == 2);
    assert(b.nbits == 32);
    assert(blocks_for_bits(32) == 1);
    // the faithful two-shape length clause: within blocks_for_bits..+1
    assert(b.storage@.len() >= 1);
    assert(b.storage@.len() <= 2);
    // in either shape the payload bits read back old bits 2..34
    assert(bit_at(b.storage@, b.nbits, 0) == true) by {
        assert(bit_at(pre_a, 34, 2) == true); // from_elem fill
    }
    assert(bit_at(b.storage@, b.nbits, 31) == true) by {
        assert(bit_at(pre_a, 34, 33) == true);
    }
    // the slack-zero conditional clause, instantiated for the top shape
    assert(b.storage@.len() == 2
        ==> b.storage@[(b.storage@.len() - 1) as int] == 0u32);
}

/// the grow doc example (lib.rs:1701-1709): 8 bits of 0b01001011,
/// grown by 2 ones -> len 10, the kept prefix and the grown tail
fn ut_grow_doc_example()
{
    let bytes: &[u8] = &[0b01001011];
    let mut bv = BitVec::from_bytes(bytes);
    assert(bv.nbits == 8);
    let ghost pre_s = bv.storage@;
    let ghost pre_n = bv.nbits;
    // the old bit 1 (the 64 of 0b01001011) is set
    assert(bit_at(pre_s, pre_n, 1) == true) by {
        assert(bytes@[0 as int] == 0b01001011);
        assert(from_bytes_bit(bytes@, 1)
            == ((bytes@[(1usize / 8) as int] & (1u8 << (7 - (1usize % 8)))) != 0u8));
        assert((1u8 << (7 - (1usize % 8))) == 64u8) by (bit_vector);
        assert((0b01001011u8 & 64u8) != 0u8) by (bit_vector);
    }
    // the old bit 3 (the 16) is clear
    assert(bit_at(pre_s, pre_n, 3) == false) by {
        assert(bytes@[0 as int] == 0b01001011);
        assert(from_bytes_bit(bytes@, 3)
            == ((bytes@[(3usize / 8) as int] & (1u8 << (7 - (3usize % 8)))) != 0u8));
        assert((1u8 << (7 - (3usize % 8))) == 16u8) by (bit_vector);
        assert((0b01001011u8 & 16u8) == 0u8) by (bit_vector);
    }
    bv.grow(2, true);
    assert(bv.nbits == 10);
    // the kept prefix survives at its old positions
    assert(bit_at(bv.storage@, bv.nbits, 1) == true);
    assert(bit_at(bv.storage@, bv.nbits, 3) == false);
    // the grown tail reads the value
    assert(bit_at(bv.storage@, bv.nbits, 8) == true);
    assert(bit_at(bv.storage@, bv.nbits, 9) == true);
}

/// grow at a block boundary: the fresh block carries full ones
fn ut_grow_block_boundary()
{
    let mut bv = BitVec::from_elem(32, false);
    bv.set(31, true);
    bv.grow(1, true);
    assert(bv.nbits == 33);
    assert(bit_at(bv.storage@, bv.nbits, 31) == true);
    assert(bit_at(bv.storage@, bv.nbits, 32) == true);
}

/// shrink_to_fit: the view-invariant tier (len, blocks, every bit)
fn ut_shrink_to_fit_keeps_view()
{
    let mut bv = BitVec::from_elem(7, true);
    bv.set(2, false);
    let ghost pre = bv.storage@;
    bv.shrink_to_fit();
    assert(bv.nbits == 7);
    assert(bv.storage@ == pre);
    assert(bit_at(bv.storage@, bv.nbits, 2) == false);
    assert(bit_at(bv.storage@, bv.nbits, 0) == true);
}

} // verus!

fn main() {}
