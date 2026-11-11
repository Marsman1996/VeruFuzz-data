//! bit-vec 0.10.1 x Verus -- coverage diff-set batch D harness
//! (the cold-borrow faces, the unsafe contract domain, and the std
//! trait periphery).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here.
//! Coverage (out/harness-inventory.md diff-set batch D):
//!   - storage() (the cold slice borrow: view identity + read-back)
//!   - storage_mut() (the unsafe borrow: the value-identity contract
//!     at return; the caller-side cfg(test) faces are not taken)
//!   - set_len() (the unsafe one-field effect under the capacity-bound
//!     Safety contract)
//!   - clone / clone_from (the Vec::clone view transfer)
//!   - eq (PartialEq shapes: the length short-circuit and the
//!     block-boundary pair; block values ground through the fill+set
//!     explicit-update chains)
//!   - cmp / partial_cmp (the lexicographic tier: the recursive walk is
//!     fed by reveal_with_fuel plus per-position prefix facts; the long
//!     cross-block prefix goes through the frame lemma)
//!   - display_chars (the Display char stream)
//!   - hash_feed (the nbits-then-blocks delegation feed)
//!   - extend_bools / from_iter_bools (the FromIterator loop)

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitvec_lib;

verus! {

use bitvec_lib::BitVec;
use bitvec_lib::BvOrd;
use bitvec_lib::bit_at;
use bitvec_lib::bit_char;
use bitvec_lib::hash_feed;
use bitvec_lib::inv;
use bitvec_lib::lex_bit;
use bitvec_lib::from_bytes_bit;
use bitvec_lib::lemma_cmp_first_diff;
use bitvec_lib::spec_bit_capacity;
use bitvec_lib::spec_bv_cmp;
use bitvec_lib::spec_cmp_from;

// ---------------------------------------------------------------------------
// the cold-borrow faces
// ---------------------------------------------------------------------------

/// storage(): the slice view is the storage view
fn ut_storage_cold_borrow()
{
    let mut bv = BitVec::from_elem(33, false);
    bv.set(33 - 1, true);
    let s = bv.storage();
    assert(s@ == bv.storage@);
    assert(s.len() == 2);
    // the set tail bit is readable through the slice face
    let last = s[1];
    assert((last & (1u32 << 0)) != 0u32);
}

/// storage_mut(): the borrowed Vec still carries the pre-call entries
/// (the old-state identity is the callee's contract; the post-borrow
/// state is the caller's domain -- the probe B finding)
fn ut_storage_mut_contract()
{
    let mut bv = BitVec::from_elem(64, true);
    let ghost pre = bv.storage@;
    {
        let r = bv.storage_mut();
        assert(r@ == pre);
        assert(r@.len() == 2);
    }
}

// ---------------------------------------------------------------------------
// the unsafe contract domain
// ---------------------------------------------------------------------------

/// set_len(): shrinking keeps the entry sequence, drops the length
fn ut_set_len_shrink()
{
    let mut bv = BitVec::from_elem(33, false);
    bv.set(31, true);
    let ghost pre = bv.storage@;
    // Safety: 5 stays within the bits capacity (the storage of two
    // blocks covers 64 bits on the std cap >= len tier, the batch-B
    // ut_capacity_covers_len pattern)
    let cap = bv.capacity();
    assert(bv.storage@.len() == 2);
    assert((32 * (2 as int)) <= usize::MAX as int);
    assert((cap as int) >= 64);
    assert(5 <= cap);
    assert(cap == spec_bit_capacity(&bv));
    bv.set_len(5);
    assert(bv.storage@ == pre);
    assert(bv.nbits == 5);
}

/// set_len(): shrinking to the zero length (Safety: 0 is within any
/// capacity) keeps the storage entries
fn ut_set_len_zero()
{
    let mut bv = BitVec::from_elem(4, true);
    let ghost pre = bv.storage@;
    bv.set_len(0);
    assert(bv.storage@ == pre);
    assert(bv.nbits == 0);
}

// ---------------------------------------------------------------------------
// Clone faces
// ---------------------------------------------------------------------------

/// clone: the view transfer tiers (entries, length, bits)
fn ut_clone_view_transfer()
{
    let mut bv = BitVec::from_elem(40, false);
    bv.set(7, true);
    let c = bv.clone_exec();
    assert(c.storage@ == bv.storage@);
    assert(c.nbits == 40);
    assert(bit_at(c.storage@, c.nbits, 7) == true);
    assert(bit_at(c.storage@, c.nbits, 8) == false);
}

/// clone_from: the overwrite equality
fn ut_clone_from_overwrite()
{
    let mut a = BitVec::from_elem(10, false);
    a.set(3, true);
    let b = BitVec::from_elem(10, true);
    a.clone_from_exec(&b);
    assert(a.storage@ == b.storage@);
    assert(a.nbits == b.nbits);
    assert(bit_at(a.storage@, a.nbits, 3) == true);
}

// ---------------------------------------------------------------------------
// PartialEq shapes
// ---------------------------------------------------------------------------

/// differing sizes short-circuit false (test_equal_differing_sizes)
fn ut_eq_differing_sizes()
{
    let v0 = BitVec::from_elem(10, false);
    let v1 = BitVec::from_elem(11, false);
    let r = v0.eq_exec(&v1);
    assert(!r);
}

/// equal after symmetric writes (test_equal_sneaky_small; the block
/// values ground through the fill+set explicit update chain)
fn ut_eq_sneaky_small()
{
    let mut a = BitVec::from_elem(1, false);
    a.fill(false);
    a.set(0, true);
    let mut b = BitVec::from_elem(1, true);
    b.fill(false);
    b.set(0, true);
    proof {
        // both tail blocks: the none_spec zero, then the bit-0 update
        assert(1u32 << 0usize == 1u32) by (bit_vector);
        assert(0u32 | 1u32 == 1u32) by (bit_vector);
        assert(a.storage@.len() == 1);
        assert(b.storage@.len() == 1);
        assert(a.storage@[0 as int] == 1u32);
        assert(b.storage@[0 as int] == 1u32);
    }
    let r = a.eq_exec(&b);
    assert(r);
    // the bit tier rides along (the r ==> direction)
    assert(bit_at(a.storage@, a.nbits, 0) == bit_at(b.storage@, b.nbits, 0));
}

/// equal across a block boundary, then unequal after one more write
/// (test_equal_sneaky_big shape; blocks ground via fill+set)
fn ut_eq_block_boundary()
{
    let mut a = BitVec::from_elem(33, false);
    a.fill(false);
    a.set(32, true);
    let mut b = BitVec::from_elem(33, false);
    b.fill(false);
    b.set(32, true);
    proof {
        assert(1u32 << 0usize == 1u32) by (bit_vector);
        assert(0u32 | 1u32 == 1u32) by (bit_vector);
        assert(a.storage@.len() == 2);
        assert(b.storage@.len() == 2);
        assert(a.storage@[0 as int] == 0u32);
        assert(b.storage@[0 as int] == 0u32);
        assert(a.storage@[1 as int] == 1u32);
        assert(b.storage@[1 as int] == 1u32);
    }
    let r = a.eq_exec(&b);
    assert(r);
    // a one-bit difference flips the result
    b.set(0, true);
    proof {
        assert(b.storage@[0 as int] == 1u32);
    }
    let r2 = a.eq_exec(&b);
    assert(!r2);
}

// ---------------------------------------------------------------------------
// Ord / PartialOrd: the lexicographic tier
// ---------------------------------------------------------------------------

/// the equal reading (test_bit_vec_lt's a >= b && b >= a start)
fn ut_cmp_equal()
{
    let a = BitVec::from_elem(2, false);
    let b = BitVec::from_elem(2, false);
    let r = a.cmp_exec(&b);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 0) == false);
        assert(bit_at(a.storage@, a.nbits, 1) == false);
        assert(bit_at(b.storage@, b.nbits, 1) == false);
        assert(lex_bit(a.storage@, 0int) == lex_bit(b.storage@, 0int));
        assert(lex_bit(a.storage@, 1int) == lex_bit(b.storage@, 1int));
    }
    assert(spec_bv_cmp(&a, &b) == 0int);
    assert(r matches BvOrd::Equal);
    let p = a.partial_cmp_exec(&b);
    assert(p matches Some(o) ==> o is Equal);
}

/// the first differing position decides (test_bit_vec_lt shapes)
fn ut_cmp_first_diff_decides()
{
    let mut a = BitVec::from_elem(3, false);
    let mut b = BitVec::from_elem(3, false);
    b.set(1, true);
    // a < b: the first difference at 1 favors b
    let r = a.cmp_exec(&b);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 1) == true);
        assert(bit_at(a.storage@, a.nbits, 1) == false);
        assert(lex_bit(a.storage@, 0int) == lex_bit(b.storage@, 0int));
        assert(lex_bit(b.storage@, 1int) == true);
        assert(lex_bit(a.storage@, 1int) == false);
    }
    assert(r matches BvOrd::Less);
    let p = a.partial_cmp_exec(&b);
    assert(p matches Some(o) ==> o is Less);
    // b's difference is earlier than a's later single catch: b stays up
    a.set(2, true);
    let r2 = a.cmp_exec(&b);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 1) == true);
        assert(bit_at(a.storage@, a.nbits, 1) == false);
        assert(lex_bit(a.storage@, 0int) == lex_bit(b.storage@, 0int));
        assert(lex_bit(b.storage@, 1int) == true);
        assert(lex_bit(a.storage@, 1int) == false);
    }
    assert(r2 matches BvOrd::Less);
    // a catches up at 1 and passes at 2: the walk finds position 2
    a.set(1, true);
    let r3 = a.cmp_exec(&b);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 0) == false);
        assert(bit_at(a.storage@, a.nbits, 1) == true);
        assert(bit_at(b.storage@, b.nbits, 1) == true);
        assert(bit_at(a.storage@, a.nbits, 2) == true);
        assert(bit_at(b.storage@, b.nbits, 2) == false);
        assert(lex_bit(a.storage@, 0int) == lex_bit(b.storage@, 0int));
        assert(lex_bit(a.storage@, 1int) == lex_bit(b.storage@, 1int));
        assert(lex_bit(a.storage@, 2int) == true);
        assert(lex_bit(b.storage@, 2int) == false);
    }
    assert(r3 matches BvOrd::Greater);
    // b takes position 0: the first difference moves to the front
    let mut b2 = b;
    b2.set(0, true);
    let r4 = a.cmp_exec(&b2);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(b2.storage@, b2.nbits, 0) == true);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(lex_bit(b2.storage@, 0int) == true);
        assert(lex_bit(a.storage@, 0int) == false);
    }
    assert(r4 matches BvOrd::Less);
}

/// the length tie decides after the equal prefix (test_ord tail)
fn ut_cmp_length_tie()
{
    let a = BitVec::from_elem(2, false);
    let b = BitVec::from_elem(3, false);
    // [0,0] < [0,0,0]: the prefix walk is equal, the lengths decide
    let r0 = a.cmp_exec(&b);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(bit_at(b.storage@, b.nbits, 0) == false);
        assert(bit_at(a.storage@, a.nbits, 1) == false);
        assert(bit_at(b.storage@, b.nbits, 1) == false);
        assert(lex_bit(a.storage@, 0int) == lex_bit(b.storage@, 0int));
        assert(lex_bit(a.storage@, 1int) == lex_bit(b.storage@, 1int));
    }
    assert(r0 matches BvOrd::Less);
    // the prefix bits on the longer side keep the longer greater
    let mut b2 = BitVec::from_elem(3, false);
    b2.set(0, true);
    let rb2 = a.cmp_exec(&b2);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
        assert(bit_at(b2.storage@, b2.nbits, 0) == true);
        assert(bit_at(a.storage@, a.nbits, 0) == false);
        assert(lex_bit(b2.storage@, 0int) == true);
        assert(lex_bit(a.storage@, 0int) == false);
    }
    assert(rb2 matches BvOrd::Less);
    // equal lengths, both all-zero: Equal again
    let rself = a.cmp_exec(&a);
    proof {
        reveal_with_fuel(spec_cmp_from, 6);
    }
    assert(rself matches BvOrd::Equal);
}

/// a difference across the block boundary decides (the cross-block
/// walk; block values ground through the fill+set chains so the long
/// prefix closes by congruence, and the first-difference lemma carries
/// the walk to position 32)
fn ut_cmp_across_blocks()
{
    let mut a = BitVec::from_elem(64, false);
    a.fill(false);
    let mut b = BitVec::from_elem(64, false);
    b.fill(false);
    a.set(33, true);
    b.set(32, true);
    proof {
        // the ground block values: none_spec zeros, then the updates
        assert(1u32 << 0usize == 1u32) by (bit_vector);
        assert(1u32 << 1usize == 2u32) by (bit_vector);
        assert(0u32 | 1u32 == 1u32) by (bit_vector);
        assert(0u32 | 2u32 == 2u32) by (bit_vector);
        assert(a.storage@.len() == 2);
        assert(b.storage@.len() == 2);
        assert(a.storage@[0 as int] == 0u32);
        assert(b.storage@[0 as int] == 0u32);
        assert(a.storage@[1 as int] == 2u32);
        assert(b.storage@[1 as int] == 1u32);
    }
    // b > a: the first difference is at 32, and b holds that bit
    // (position 32 is the first slot of the second block -- the walk
    // crosses the block boundary to find it)
    let rba = b.cmp_exec(&a);
    proof {
        assert forall|k: int| 0 <= k < 32 implies
            lex_bit(b.storage@, k) == lex_bit(a.storage@, k) by { }
        assert(bit_at(b.storage@, b.nbits, 32) == true);
        assert(bit_at(a.storage@, a.nbits, 32) == false);
        assert(lex_bit(b.storage@, 32int) == true);
        assert(lex_bit(a.storage@, 32int) == false);
        lemma_cmp_first_diff(b.storage@, a.storage@, 64, 64, 32);
        assert(spec_cmp_from(b.storage@, a.storage@, 0int, 64, 64) == 1int);
    }
    assert(spec_bv_cmp(&b, &a) == 1int);
    assert(rba matches BvOrd::Greater);
    let rab = a.cmp_exec(&b);
    proof {
        assert forall|k: int| 0 <= k < 32 implies
            lex_bit(a.storage@, k) == lex_bit(b.storage@, k) by { }
        assert(lex_bit(a.storage@, 32int) == false);
        assert(lex_bit(b.storage@, 32int) == true);
        lemma_cmp_first_diff(a.storage@, b.storage@, 64, 64, 32);
        assert(spec_cmp_from(a.storage@, b.storage@, 0int, 64, 64) == -1int);
    }
    assert(spec_bv_cmp(&a, &b) == -1int);
    assert(rab matches BvOrd::Less);
}

// ---------------------------------------------------------------------------
// Display and Hash
// ---------------------------------------------------------------------------

/// the Display char stream of an unaligned byte load
/// (test_display_output content shape)
fn ut_display_stream_unaligned()
{
    let bytes: &[u8] = &[0b10110110];
    let bv = BitVec::from_bytes(bytes);
    let cs = bv.display_chars();
    proof {
        // the from_bytes bit model on the literal byte (high bit first)
        assert(bytes@[0 as int] == 0b10110110u8);
        assert((1u8 << (7 - (0usize % 8))) == 128u8) by (bit_vector);
        assert((1u8 << (7 - (1usize % 8))) == 64u8) by (bit_vector);
        assert((1u8 << (7 - (2usize % 8))) == 32u8) by (bit_vector);
        assert((1u8 << (7 - (3usize % 8))) == 16u8) by (bit_vector);
        assert((1u8 << (7 - (4usize % 8))) == 8u8) by (bit_vector);
        assert((1u8 << (7 - (5usize % 8))) == 4u8) by (bit_vector);
        assert((1u8 << (7 - (6usize % 8))) == 2u8) by (bit_vector);
        assert((1u8 << (7 - (7usize % 8))) == 1u8) by (bit_vector);
        assert((0b10110110u8 & 128u8) != 0u8) by (bit_vector);
        assert((0b10110110u8 & 64u8) == 0u8) by (bit_vector);
        assert((0b10110110u8 & 32u8) != 0u8) by (bit_vector);
        assert((0b10110110u8 & 16u8) != 0u8) by (bit_vector);
        assert((0b10110110u8 & 8u8) == 0u8) by (bit_vector);
        assert((0b10110110u8 & 4u8) != 0u8) by (bit_vector);
        assert((0b10110110u8 & 2u8) != 0u8) by (bit_vector);
        assert((0b10110110u8 & 1u8) == 0u8) by (bit_vector);
        assert forall|j: usize| j < 8 implies
            bit_at(bv.storage@, bv.nbits, j)
                == (((bytes@[(j / 8) as int] & (1u8 << (7 - (j % 8)))) != 0u8)) by {
            assert(bit_at(bv.storage@, bv.nbits, j) == from_bytes_bit(bytes@, j));
        }
    }
    assert(cs@.len() == 8);
    assert(cs@[0] == '1');
    assert(cs@[1] == '0');
    assert(cs@[2] == '1');
    assert(cs@[3] == '1');
    assert(cs@[4] == '0');
    assert(cs@[5] == '1');
    assert(cs@[6] == '1');
    assert(cs@[7] == '0');
}

/// the per-tier char family agrees with the bit family
fn ut_display_bit_char_family()
{
    let mut bv = BitVec::from_elem(35, false);
    bv.set(34, true);
    let cs = bv.display_chars();
    assert(cs@.len() == 35);
    assert(cs@[34] == '1');
    assert(cs@[33] == '0');
    // the spec family over every position
    assert forall|j: usize| j < 35 implies
        cs@[j as int] == bit_char(bit_at(bv.storage@, bv.nbits, j)) by { }
}

/// the Hash feed: nbits first, then every block in order
/// (block values ground through the fill+set update chain)
fn ut_hash_feed_order()
{
    let mut bv = BitVec::from_elem(33, false);
    bv.fill(false);
    bv.set(32, true);
    let m = bv.hash_feed_exec();
    proof {
        assert(1u32 << 0usize == 1u32) by (bit_vector);
        assert(0u32 | 1u32 == 1u32) by (bit_vector);
        assert(bv.storage@[0 as int] == 0u32);
        assert(bv.storage@[1 as int] == 1u32);
        // the Seq::new feed reads nbits at 0 and the blocks from 1 on
        assert(m@[2] == (bv.storage@[1 as int] as u64));
        assert(bv.storage@[1 as int] as u64 == 1u64);
    }
    assert(m@.len() == 3);
    assert(m@[0] == 33);
    assert(m@[1] == 0);
    assert(m@[2] == 1); // the tail bit at position 32
    // the spec feed agrees with the exec feed
    assert(m@ == hash_feed(&bv));
}

/// equal vectors feed equal streams (the Hash delegation rationale)
fn ut_hash_feed_eq_bridge()
{
    let mut a = BitVec::from_elem(33, false);
    a.fill(false);
    a.set(0, true);
    let mut b = BitVec::from_elem(33, false);
    b.fill(false);
    b.set(0, true);
    proof {
        assert(1u32 << 0usize == 1u32) by (bit_vector);
        assert(0u32 | 1u32 == 1u32) by (bit_vector);
        assert(a.storage@[0 as int] == 1u32);
        assert(b.storage@[0 as int] == 1u32);
    }
    let ra = a.eq_exec(&b);
    assert(ra);
    let fa = a.hash_feed_exec();
    let fb = b.hash_feed_exec();
    assert(fa@.len() == fb@.len());
    assert(fa@ == fb@);
}

// ---------------------------------------------------------------------------
// Extend / FromIterator
// ---------------------------------------------------------------------------

/// from_iter: the collect shape (test_from_bools content)
fn ut_from_iter_bools()
{
    let v = [true, false, true, true];
    let bv = BitVec::from_iter_bools(&v);
    assert(bv.nbits == 4);
    assert(bit_at(bv.storage@, bv.nbits, 0));
    assert(!bit_at(bv.storage@, bv.nbits, 1));
    assert(bit_at(bv.storage@, bv.nbits, 2));
    assert(bit_at(bv.storage@, bv.nbits, 3));
}

/// extend: prefix preservation and append order (test_bit_vec_extend tiers)
fn ut_extend_bools_prefix()
{
    let mut bv = BitVec::from_bytes(&[0b10110110]);
    let ghost before = bv.storage@;
    let n0 = bv.nbits;
    let ext = [false, true, false, false];
    bv.extend_bools(&ext);
    assert(bv.nbits == n0 + 4);
    assert forall|j: usize| j < n0 implies
        bit_at(bv.storage@, bv.nbits, j) == bit_at(before, n0, j) by { }
    assert(!bit_at(bv.storage@, bv.nbits, n0));
    assert(bit_at(bv.storage@, bv.nbits, (n0 + 1) as usize));
    assert(!bit_at(bv.storage@, bv.nbits, (n0 + 2) as usize));
    assert(!bit_at(bv.storage@, bv.nbits, (n0 + 3) as usize));
}

/// extend across a block boundary: the byte-load prefix plus a longer tail
fn ut_extend_bools_cross_block()
{
    let mut bv = BitVec::from_elem(32, true);
    let n0 = bv.nbits;
    let ext = [true, false];
    bv.extend_bools(&ext);
    assert(bv.nbits == 34);
    assert(bit_at(bv.storage@, bv.nbits, 31));
    assert(bit_at(bv.storage@, bv.nbits, 32));
    assert(!bit_at(bv.storage@, bv.nbits, 33));
}

} // verus!

fn main() {}
