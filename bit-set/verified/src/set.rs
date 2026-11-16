//! bit-set 0.11.1 core family (set/src/set.rs) -- Verus translation.
//!
//! Shares the crate-root BitVec mount (../lib.rs; single source of
//! verified BitVec facts, B = u32) and mirrors upstream `mod set` as a
//! sibling module: crate-root model/spec faces are reached via
//! `super::`, per the database/url multi-file precedent. The
//! other_op/difference family, subset/disjoint queries, ordering,
//! reserve_len and the iterator family live with their own batches (see
//! out/harness-inventory.md section 4).

use vstd::prelude::*;

verus! {

use super::bitvec_lib::{
    BitVec, bit_at, blocks_for_bits, count_bits, count_ones_spec, from_bytes_bit,
    int_div_bound_lemma, inv, lemma_and_bit, lemma_andnot_bit, lemma_count_range_const,
    lemma_count_split, lemma_or_bit, lemma_pow_lt_bit, lemma_xor_bit, spec_bit_capacity,
    trailing_zero,
};

// ===========================================================================
// Origin Rust: pub struct BitSet<B: BitBlock = u32> {
//     pub(crate) bit_vec: BitVec<B> } (set/src/set.rs:12-14)
// (field made pub: reference-style harnesses construct/inspect through it
//  -- minimal visibility relaxation, the bit-vec precedent.)
// ===========================================================================

pub struct BitSet {
    pub bit_vec: BitVec,
}

// ---------------------------------------------------------------------------
// spec model: membership over the underlying BitVec's bit-wise model
// ---------------------------------------------------------------------------

/// membership at index i: i is inside the universe and its bit is set.
pub open spec fn bs_at(bs: &BitSet, i: usize) -> bool {
    i < bs.bit_vec.nbits && bit_at(bs.bit_vec.storage@, bs.bit_vec.nbits, i)
}

/// structural invariant: the underlying BitVec invariant.
pub open spec fn bs_inv(bs: &BitSet) -> bool {
    inv(&bs.bit_vec)
}

/// number of members (the Hamming weight of the underlying bit-vector).
pub open spec fn bs_count(bs: &BitSet) -> int {
    count_ones_spec(&bs.bit_vec)
}

/// the iterator equality face: the maximum of the two universes (origin
/// fn eq is `self.iter().eq(other)`, set.rs:70; the two own-stream
/// element sequences are equal exactly when the padded bit faces agree
/// on the wider universe -- the tail padding is zero under inv, so the
/// element-sequence lengths ride along).
    /// the iterator equality face: the maximum of the two universes
    /// (origin fn eq is `self.iter().eq(other)`, set.rs:70; the two
    /// own-stream element sequences are equal exactly when the padded
    /// bit faces agree on the wider universe -- the tail padding is
    /// zero under inv, so the sequence lengths ride along).
pub open spec fn bs_max_nb(xs: &BitSet, ys: &BitSet) -> usize {
    if xs.bit_vec.nbits < ys.bit_vec.nbits {
        ys.bit_vec.nbits
    } else {
        xs.bit_vec.nbits
    }
}

impl BitSet {
    /// Origin Rust: pub fn new() -> Self { Self::default() }
    ///     (the impl BitSet<u32> specialization, set.rs:77-90)
    /// Upstream doc (set.rs:78-79):
    ///   Creates a new empty `BitSet`.
    pub exec fn new() -> (bs: BitSet)
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == 0,
            bs.bit_vec.storage@.len() == 0,
            forall|i: usize| !bs_at(&bs, i),
    {
        BitSet { bit_vec: super::bitvec_lib::new() }
    }

    /// Origin Rust: pub fn new_general() -> Self { Self::default() }
    ///     (set.rs:139-151)
    /// Upstream doc (set.rs:140-147):
    ///   Creates a new empty `BitSet`.
    pub exec fn new_general() -> (bs: BitSet)
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == 0,
            bs.bit_vec.storage@.len() == 0,
            forall|i: usize| !bs_at(&bs, i),
    {
        Self::default()
    }

    /// Origin Rust: impl Default for BitSet: BitSet { bit_vec: Default::default() }
    ///     (set.rs:28-35, via BitVec::default)
    pub exec fn default() -> (bs: BitSet)
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == 0,
            bs.bit_vec.storage@.len() == 0,
            forall|i: usize| !bs_at(&bs, i),
    {
        let bit_vec: BitVec = super::bitvec_lib::bv_default();
        BitSet { bit_vec }
    }

    /// Origin Rust: pub fn with_capacity(nbits: usize) -> Self {
    ///     let bit_vec = BitVec::from_elem(nbits, false);
    ///     Self::from_bit_vec(bit_vec) } (set.rs:92-107)
    /// Upstream doc (set.rs:92-98):
    ///   Creates a new `BitSet` with initially no contents, able to
    ///   hold `nbits` elements without resizing.
    pub exec fn with_capacity(nbits: usize) -> (bs: BitSet)
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == nbits,
            forall|i: usize| !bs_at(&bs, i),
    {
        let bit_vec = BitVec::from_elem(nbits, false);
        BitSet { bit_vec }
    }

    /// Origin Rust: pub fn with_capacity_general(nbits: usize) -> Self {
    ///     let bit_vec = BitVec::from_elem_general(nbits, false);
    ///     Self::from_bit_vec_general(bit_vec) } (set.rs:154-168)
    /// Upstream doc (set.rs:155-161):
    ///   Creates a new `BitSet` with initially no contents, able to
    ///   hold `nbits` elements without resizing.
    pub exec fn with_capacity_general(nbits: usize) -> (bs: BitSet)
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == nbits,
            forall|i: usize| !bs_at(&bs, i),
    {
        let bit_vec = BitVec::from_elem_general(nbits, false);
        BitSet { bit_vec }
    }

    /// Origin Rust: pub fn from_bit_vec(bit_vec: BitVec) -> Self {
    ///     BitSet { bit_vec } } (set.rs:109-128, BitSet<u32> specialization)
    /// Upstream doc (set.rs:110-116):
    ///   Creates a new `BitSet` from the given bit vector.
    pub exec fn from_bit_vec(bit_vec: BitVec) -> (bs: BitSet)
        requires
            inv(&bit_vec),
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == bit_vec.nbits,
            bs.bit_vec.storage@ == bit_vec.storage@,
            forall|i: usize| bs_at(&bs, i) == (i < bit_vec.nbits
                && bit_at(bit_vec.storage@, bit_vec.nbits, i)),
    {
        BitSet { bit_vec }
    }

    /// Origin Rust: pub fn from_bit_vec_general(bit_vec: BitVec<B>) -> Self {
    ///     BitSet { bit_vec } } (set.rs:180-189)
    /// Upstream doc (set.rs:170-179):
    ///   Creates a new `BitSet` from the given bit vector.
    pub exec fn from_bit_vec_general(bit_vec: BitVec) -> (bs: BitSet)
        requires
            inv(&bit_vec),
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == bit_vec.nbits,
            bs.bit_vec.storage@ == bit_vec.storage@,
            forall|i: usize| bs_at(&bs, i) == (i < bit_vec.nbits
                && bit_at(bit_vec.storage@, bit_vec.nbits, i)),
    {
        BitSet { bit_vec }
    }

    /// Origin Rust: pub fn from_bytes(bytes: &[u8]) -> Self {
    ///     BitSet { bit_vec: BitVec::from_bytes(bytes) } } (set.rs:130-134)
    pub exec fn from_bytes(bytes: &[u8]) -> (bs: BitSet)
        requires
            bytes.len() <= usize::MAX / 8,
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == 8 * bytes.len(),
            forall|i: usize| i < bs.bit_vec.nbits ==> bs_at(&bs, i)
                == from_bytes_bit(bytes@, i),
    {
        BitSet { bit_vec: BitVec::from_bytes(bytes) }
    }

    /// Origin Rust: pub fn from_bytes_general(bytes: &[u8]) -> Self {
    ///     BitSet { bit_vec: BitVec::from_bytes_general(bytes) } }
    ///     (set.rs:191-195; BitVec::from_bytes_general is the from_bytes
    ///     entry on the general block axis -- same entry translated here.)
    pub exec fn from_bytes_general(bytes: &[u8]) -> (bs: BitSet)
        requires
            bytes.len() <= usize::MAX / 8,
        ensures
            bs_inv(&bs),
            bs.bit_vec.nbits == 8 * bytes.len(),
            forall|i: usize| i < bs.bit_vec.nbits ==> bs_at(&bs, i)
                == from_bytes_bit(bytes@, i),
    {
        BitSet { bit_vec: BitVec::from_bytes(bytes) }
    }

    /// Origin Rust: pub fn capacity(&self) -> usize { self.bit_vec.capacity() }
    ///     (set.rs:197-211)
    /// Upstream doc (set.rs:197-199):
    ///   Returns the capacity in bits for this bit vector. Inserting any
    ///   element less than this amount will not trigger a resizing.
    pub exec fn capacity(&self) -> (r: usize)
        requires
            bs_inv(self),
        ensures
            r == spec_bit_capacity(&self.bit_vec),
    {
        self.bit_vec.capacity()
    }

    /// Origin Rust: pub fn into_bit_vec(self) -> BitVec<B> { self.bit_vec }
    ///     (set.rs:261-279)
    /// Upstream doc (set.rs:261-262):
    ///   Consumes this set to return the underlying bit vector.
    pub exec fn into_bit_vec(self) -> (bv: BitVec)
        requires
            bs_inv(&self),
        ensures
            bv.nbits == self.bit_vec.nbits,
            bv.storage@ == self.bit_vec.storage@,
    {
        self.bit_vec
    }

    /// Origin Rust: pub fn get_ref(&self) -> &BitVec<B> { &self.bit_vec }
    ///     (set.rs:281-297)
    /// Upstream doc (set.rs:281-283):
    ///   Returns a reference to the underlying bit vector.
    pub exec fn get_ref(&self) -> (r: &BitVec)
        requires
            bs_inv(self),
        ensures
            r.nbits == self.bit_vec.nbits,
            r.storage@ == self.bit_vec.storage@,
    {
        &self.bit_vec
    }

    /// Origin Rust: pub fn contains(&self, value: usize) -> bool {
    ///     let bit_vec = &self.bit_vec;
    ///     value < bit_vec.len() && bit_vec[value] }
    ///     (set.rs:651-656; the Index read expands through the verified
    ///     BitVec get -- Index-get bridge, the bit-vec precedent.)
    /// Upstream doc (set.rs:650-651):
    ///   Returns `true` if this set contains the specified integer.
    pub exec fn contains(&self, value: usize) -> (r: bool)
        requires
            bs_inv(self),
        ensures
            r == bs_at(self, value),
    {
        let bit_vec = &self.bit_vec;
        value < bit_vec.len() && match bit_vec.get(value) {
            Some(b) => b,
            None => false, // dead arm under value < bit_vec.len()
        }
    }

    /// Origin Rust: pub fn insert(&mut self, value: usize) -> bool {
    ///     if self.contains(value) { return false; }
    ///     let len = self.bit_vec.len();
    ///     if value >= len { self.bit_vec.grow(value - len + 1, false); }
    ///     self.bit_vec.set(value, true); true } (set.rs:684-699)
    /// Upstream doc (set.rs:684-685):
    ///   Adds a value to the set. Returns `true` if the value was not already
    ///   present in the set.
    pub exec fn insert(&mut self, value: usize) -> (r: bool)
        requires
            bs_inv(old(self)),
            value <= usize::MAX - 1,
        ensures
            bs_inv(final(self)),
            r == !bs_at(old(self), value),
            final(self).bit_vec.nbits
                == (if bs_at(old(self), value) {
                    old(self).bit_vec.nbits
                } else {
                    (if value >= old(self).bit_vec.nbits {
                        (value + 1) as usize
                    } else {
                        old(self).bit_vec.nbits
                    })
                }),
            forall|i: usize| #[trigger] bs_at(final(self), i)
                == (bs_at(old(self), i) || (r && i == value)),
    {
        if self.contains(value) {
            return false;
        }
        let len = self.bit_vec.len();
        if value >= len {
            proof {
                // grow's arity precondition: nbits + (value - len + 1) == value + 1 <= MAX
                assert((len as int) + ((value - len + 1) as int) == (value as int) + 1);
            }
            self.bit_vec.grow(value - len + 1, false);
        }
        proof {
            // grow (when fired) preserved old memberships below the old
            // universe and set the fresh range to false; set(value, true)
            // sets exactly the value bit.
            assert forall|i: usize| i < old(self).bit_vec.nbits ==>
                bit_at(self.bit_vec.storage@, self.bit_vec.nbits, i)
                    == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, i) by {
                if value >= len {
                    assert(self.bit_vec.nbits == old(self).bit_vec.nbits + (value - len + 1));
                    assert(old(self).bit_vec.nbits == len);
                } else {
                    assert(self.bit_vec.nbits == old(self).bit_vec.nbits);
                }
            }
        }
        self.bit_vec.set(value, true);
        proof {
            assert(value < self.bit_vec.nbits);
            assert forall|i: usize| bs_at(final(self), i)
                == (bs_at(old(self), i) || (i == value)) by {
                if value >= len {
                    // membership below the old universe is preserved or is i == value
                    if i < old(self).bit_vec.nbits {
                        if i == value {
                            assert(i < len); // i < old nbits <= len
                            assert(false); // value >= len contradicts i < len
                        } else {
                            // set preserved it
                            assert(bit_at(final(self).bit_vec.storage@,
                                final(self).bit_vec.nbits, i)
                                == bit_at(self.bit_vec.storage@, self.bit_vec.nbits, i));
                            assert(self.bit_vec.storage@ == final(self).bit_vec.storage@);
                        }
                    } else if i < value {
                        assert(final(self).bit_vec.nbits == value + 1);
                        // the grown range [old nbits, value) is false and set
                        // preserved it
                        assert(i < final(self).bit_vec.nbits);
                        assert(!bit_at(final(self).bit_vec.storage@,
                            final(self).bit_vec.nbits, i));
                    } else if i == value {
                        assert(bit_at(final(self).bit_vec.storage@,
                            final(self).bit_vec.nbits, value));
                    } else {
                        // i > value >= final universe unless old universe was larger
                        if value + 1 > old(self).bit_vec.nbits {
                            assert(i >= final(self).bit_vec.nbits);
                        } else {
                            assert(final(self).bit_vec.nbits == old(self).bit_vec.nbits);
                            assert(i > value && i < old(self).bit_vec.nbits
                                || i >= old(self).bit_vec.nbits);
                        }
                    }
                } else {
                    assert(final(self).bit_vec.nbits == old(self).bit_vec.nbits);
                    if i == value {
                        assert(bit_at(final(self).bit_vec.storage@,
                            final(self).bit_vec.nbits, value));
                    } else if i < old(self).bit_vec.nbits {
                        assert(bit_at(final(self).bit_vec.storage@,
                            final(self).bit_vec.nbits, i)
                            == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, i));
                    }
                }
            }
            assert(!bs_at(old(self), value)); // insert's early-return guard
        }
        true
    }

    /// Origin Rust: pub fn remove(&mut self, value: usize) -> bool {
    ///     if !self.contains(value) { return false; }
    ///     self.bit_vec.set(value, false); true } (set.rs:701-711)
    /// Upstream doc (set.rs:701-702):
    ///   Removes a value from the set. Returns `true` if the value was
    ///   present in the set.
    pub exec fn remove(&mut self, value: usize) -> (r: bool)
        requires
            bs_inv(old(self)),
        ensures
            bs_inv(final(self)),
            r == bs_at(old(self), value),
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            forall|i: usize| bs_at(final(self), i)
                == (bs_at(old(self), i) && i != value),
    {
        if !self.contains(value) {
            return false;
        }
        proof {
            assert(value < self.bit_vec.nbits);
        }
        self.bit_vec.set(value, false);
        proof {
            assert forall|i: usize| bs_at(final(self), i)
                == (bs_at(old(self), i) && i != value) by {
                if i == value {
                    assert(!bit_at(final(self).bit_vec.storage@,
                        final(self).bit_vec.nbits, value));
                } else if i < old(self).bit_vec.nbits {
                    assert(bit_at(final(self).bit_vec.storage@, final(self).bit_vec.nbits, i)
                        == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, i));
                }
            }
        }
        true
    }

    /// Origin Rust: pub fn count(&self) -> usize {
    ///     self.bit_vec.blocks().fold(0, |acc, n| acc + n.count_ones()) }
    ///     (set.rs:601-607; the fold computes the Hamming weight of the
    ///     blocks, the value the verified BitVec::count_ones carries -- the
    ///     blocks().fold materializes as that entry, the none()/all() fold
    ///     precedent.)
    /// Upstream doc (set.rs:601-603):
    ///   Counts the number of set bits in this set.
    ///   Note that this function scans the set to calculate the number.
    pub exec fn count(&self) -> (r: usize)
        requires
            bs_inv(self),
        ensures
            r as int == bs_count(self),
    {
        let total = self.bit_vec.count_ones();
        proof {
            // count_bits bounded by nbits (a value-store of u64 width)
            super::bitvec_lib::lemma_count_bits_bound(self.bit_vec.storage@, self.bit_vec.nbits, 0,
                self.bit_vec.nbits);
            assert(bs_count(self) <= self.bit_vec.nbits as int);
            assert(bs_count(self) <= usize::MAX as int);
            assert((total as usize) as int == bs_count(self));
        }
        (total as usize)
    }

    /// Origin Rust: pub fn len(&self) -> usize { self.count() }
    ///     (set.rs:609-616)
    /// Upstream doc (set.rs:609-611):
    ///   Counts the number of set bits in this set.
    ///   Note that this function scans the set to calculate the number.
    pub exec fn len(&self) -> (r: usize)
        requires
            bs_inv(self),
        ensures
            r as int == bs_count(self),
    {
        self.count()
    }

    /// Origin Rust: pub fn is_empty(&self) -> bool { self.bit_vec.none() }
    ///     (set.rs:618-622)
    /// Upstream doc (set.rs:618-619):
    ///   Returns whether there are no bits set in this set
    pub exec fn is_empty(&self) -> (r: bool)
        requires
            bs_inv(self),
        ensures
            r == (forall|i: usize| !bs_at(self, i)),
    {
        let none = self.bit_vec.none();
        proof {
            // direction "no member": none's own postcondition.
            // direction "nonempty": a nonzero block holds an in-universe
            // set bit (the pick lemma + the position case analysis).
            if !none {
                assert(!super::bitvec_lib::none_spec(&self.bit_vec));
                let w = choose|w: int|
                    0 <= w < self.bit_vec.storage@.len()
                        && self.bit_vec.storage@[w as int] != 0u32;
                let wu: usize = w as usize;
                let blk = self.bit_vec.storage@[w as int];
                assert(blk != 0u32);
                assert((blk >> 0) == blk) by (bit_vector);
                blk_set_bit_exists(blk, 0);
                let j = choose|j: usize| (blk & (1u32 << j)) != 0u32 && j < 32;
                let i = 32 * wu + j;
                let n = self.bit_vec.nbits;
                let nb = super::bitvec_lib::blocks_for_bits(n);
                assert(self.bit_vec.storage@.len() == nb) by {}
                if n % 32 == 0 {
                    // storage alignment: every block bit is in-universe
                    assert(n == 32 * nb);
                    assert(w <= (nb - 1) as int);
                    assert(i <= 32 * (nb - 1) + 31);
                    assert(i < 32 * nb);
                    assert(i < n);
                } else if w < (self.bit_vec.storage@.len() - 1) as int {
                    // an interior block: below the last full block tier
                    assert(nb >= 1);
                    assert(w <= (nb - 2) as int);
                    assert(i <= 32 * (nb - 2) + 31);
                    assert(32 * (nb - 1) < n);
                    assert(i < 32 * (nb - 1));
                    assert(i < n);
                } else {
                    // w is the last block, n % 32 > 0: the trailing-zero
                    // invariant caps its set bits below nbits % 32
                    assert(w == (self.bit_vec.storage@.len() - 1) as int);
                    assert(w == (nb - 1) as int);
                    assert(blk < (1u32 << (n % 32)) as u32);
                    assert(j < n % 32) by (bit_vector)
                        requires
                            j <= 31usize,
                            blk < (1u32 << (n % 32)) as u32,
                            (blk & (1u32 << j)) != 0u32,
                    ;
                    assert(32 * (nb - 1) == 32 * (n / 32));
                    assert(i == 32 * (n / 32) + j);
                    assert(32 * (n / 32) + j < 32 * (n / 32) + n % 32);
                    assert(32 * (n / 32) + n % 32 == n);
                    assert(i < n);
                }
                assert(bs_at(self, i as usize));
                assert(!(forall|t: usize| !bs_at(self, t)));
            }
        }
        none
    }

    /// Origin Rust: pub fn make_empty(&mut self) { self.bit_vec.fill(false) }
    ///     (set.rs:624-632)
    /// Upstream doc (set.rs:624-627):
    ///   Removes all elements of this set.
    ///   Different from [`reset`] only in that the capacity is preserved.
    pub exec fn make_empty(&mut self)
        requires
            bs_inv(old(self)),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            forall|i: usize| !bs_at(final(self), i),
    {
        self.bit_vec.fill(false);
        proof {
            assert forall|i: usize| !bs_at(final(self), i) by { }
        }
    }

    /// Origin Rust: pub fn clear(&mut self) { self.make_empty() }
    ///     (set.rs:644-649
    ///     #[deprecated(since = "0.9.0", note = "please use `fn make_empty` instead")])
    /// Upstream doc (set.rs:644):
    ///   Clears all bits in this set
    pub exec fn clear(&mut self)
        requires
            bs_inv(old(self)),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            forall|i: usize| !bs_at(final(self), i),
    {
        self.make_empty();
    }

    /// Origin Rust: pub fn reset(&mut self) { self.bit_vec.remove_all() }
    ///     (set.rs:634-642)
    /// Upstream doc (set.rs:634-637):
    ///   Resets this set to an empty state.
    ///   Different from [`make_empty`] only in that the capacity may NOT be preserved.
    pub exec fn reset(&mut self)
        requires
            bs_inv(old(self)),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == 0,
            forall|i: usize| !bs_at(final(self), i),
    {
        self.bit_vec.remove_all();
        proof {
            assert forall|i: usize| !bs_at(final(self), i) by { }
        }
    }

    /// Origin Rust: pub fn truncate(&mut self, element: usize) {
    ///     self.bit_vec.truncate(element) } (set.rs:713-716)
    /// Upstream doc (set.rs:713-714):
    ///   Excludes `element` and all greater elements from the `BitSet`.
    pub exec fn truncate(&mut self, element: usize)
        requires
            bs_inv(old(self)),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == (if element < old(self).bit_vec.nbits {
                element
            } else {
                old(self).bit_vec.nbits
            }),
            forall|i: usize| i < final(self).bit_vec.nbits ==> bs_at(final(self), i)
                == bs_at(old(self), i),
    {
        self.bit_vec.truncate(element);
        proof {
            assert forall|i: usize| i < final(self).bit_vec.nbits ==>
                bs_at(final(self), i) == bs_at(old(self), i) by {
                if i < final(self).bit_vec.nbits {
                    assert(bit_at(final(self).bit_vec.storage@, final(self).bit_vec.nbits, i)
                        == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, i));
                }
            }
        }
    }

    // =======================================================================
    // In-place bitwise combination family (the upstream `other_op` closure
    // F monomorphized into concrete word ops per entry).
    // =======================================================================

    /// Origin Rust: `fn other_op<F>` grow phase
    ///     `if self_len < other_len { self_bit_vec.grow(other_len - self_len, false) }`
    ///     (set/src/set.rs:335-349)
    /// shared preamble of union_with/intersect_with/difference_with/
    /// symmetric_difference_with: pad self out to the longer universe,
    /// the added region filled false.
    fn grow_to_cover(&mut self, other_not_used_callee: &Self)
        requires
            bs_inv(old(self)),
            bs_inv(other_not_used_callee),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == if old(self).bit_vec.nbits < other_not_used_callee.bit_vec.nbits {
                other_not_used_callee.bit_vec.nbits
            } else {
                old(self).bit_vec.nbits
            },
            forall|j: usize| j < final(self).bit_vec.nbits ==> bs_at(final(self), j)
                == if j < old(self).bit_vec.nbits { bs_at(old(self), j) } else { false },
            forall|j: usize| j < final(self).bit_vec.nbits ==>
                (#[trigger] bit_at(final(self).bit_vec.storage@, final(self).bit_vec.nbits, j)
                    == (j < old(self).bit_vec.nbits
                        && #[trigger] bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, j))),
    {
        let self_len = self.bit_vec.len();
        let other_len = other_not_used_callee.bit_vec.len();
        if self_len < other_len {
            let ghost old_nb = old(self).bit_vec.nbits;
            proof {
                assert(old_nb == self_len);
                assert(old_nb + (other_len - self_len) == other_len);
                assert(old_nb + (other_len - self_len) <= usize::MAX as int);
            }
            self.bit_vec.grow(other_len - self_len, false);
            proof {
                assert forall|j: usize| j < self.bit_vec.nbits ==> bs_at(final(self), j)
                    == if j < old_nb { bs_at(old(self), j) } else { false } by {
                    if j < old_nb {
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j)
                            == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, j));
                    }
                }
            }
        }
    }

    /// Origin Rust: pub fn union_with(&mut self, other: &Self)
    ///     { self.other_op(other, |w1, w2| w1 | w2) } (set/src/set.rs:438-440)
    /// Upstream doc (set.rs:419-424):
    ///   Unions in-place with the specified other bit vector.
    pub exec fn union_with(&mut self, other: &Self)
        requires
            bs_inv(old(self)),
            bs_inv(other),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == if old(self).bit_vec.nbits < other.bit_vec.nbits {
                other.bit_vec.nbits
            } else {
                old(self).bit_vec.nbits
            },
            forall|j: usize| j < final(self).bit_vec.nbits ==> bs_at(final(self), j)
                == (bs_at(old(self), j) || bs_at(other, j)),
    {
        let self_len = self.bit_vec.len();
        let other_len = other.bit_vec.len();
        if self_len < other_len {
            self.bit_vec.grow(other_len - self_len, false);
        }
        let ghost old_nb = old(self).bit_vec.nbits;
        let ghost olds = old(self).bit_vec.storage@;
        let ghost s1_nb = self.bit_vec.nbits;
        let ghost s1_e = s1_nb % 32;
        let ghost s1: Seq<u32> = self.bit_vec.storage@;
        let ghost s1_tail_ok: bool = (s1_e > 0 ==> s1[(s1.len() - 1) as int] < (1u32 << s1_e));
        let ghost grow_faces: bool = (forall|j2: usize| j2 < s1_nb ==>
            (#[trigger] bit_at(s1, s1_nb, j2)
                == (j2 < old_nb && bit_at(olds, old_nb, j2))));
        proof {
            // freeze the post-grow self faces the post proof consumes
            // (pure ghost terms: valid across the storage write loop)
            if s1_e > 0 {
                assert(trailing_zero(&self.bit_vec));
                assert(s1[(s1.len() - 1) as int] < (1u32 << s1_e));
                assert(s1_tail_ok);
            }
            assert forall|j2: usize| j2 < s1_nb ==>
                (#[trigger] bit_at(s1, s1_nb, j2)
                    == (j2 < old_nb && bit_at(olds, old_nb, j2))) by {
                if j2 < s1_nb {
                    if j2 < old_nb {
                        int_div_bound_lemma(j2, old_nb);
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2)
                            == bit_at(old(self).bit_vec.storage@,
                                old(self).bit_vec.nbits, j2));
                    } else {
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2) == false);
                    }
                }
            }
            assert(grow_faces);
        }
        let ghost old_stg: Seq<u32> = old(self).bit_vec.storage@;
        let ghost os: Seq<u32> = other.bit_vec.storage@;
        let ow = other.bit_vec.storage();
        let o_len = ow.len();
        let k = self.bit_vec.storage().len();
        proof {
            assert(ow@ == os);
            assert(k == s1.len());
            assert((o_len as int) == os.len());
        }
        let mut i: usize = 0;
        while i < k
            invariant
                i <= k,
                (k as int) == s1.len(),
                (o_len as int) == os.len(),
                ow@ == os,
                self.bit_vec.nbits == s1_nb,
                s1_tail_ok,
                forall|j2: usize| j2 < s1_nb ==>
                    (#[trigger] bit_at(s1, s1_nb, j2)
                        == (j2 < old_nb && bit_at(olds, old_nb, j2))),
                self.bit_vec.storage@.len() == s1.len(),
                forall|q: usize| (q as int) < (i as int) ==>
                    self.bit_vec.storage@[q as int]
                        == (s1[q as int] | (if (q as int) < os.len() { os[q as int] } else { 0u32 })),
                forall|q: usize| (q as int) >= (i as int) && (q as int) < s1.len() ==>
                    self.bit_vec.storage@[q as int] == s1[q as int],
            decreases (k - i),
        {
            let oldw = self.bit_vec.storage[i];
            let w = if i < o_len { ow[i] } else { 0u32 };
            let neww = oldw | w;
            self.bit_vec.storage.set(i, neww);
            proof {
                assert(self.bit_vec.storage@[i as int] == neww);
                assert(w == (if (i as int) < os.len() { os[i as int] } else { 0u32 }));
                assert(self.bit_vec.storage@[i as int]
                    == (s1[i as int] | (if (i as int) < os.len() { os[i as int] } else { 0u32 })));
            }
            i += 1;
        }
        proof {
            let s2 = self.bit_vec.storage@;
            assert(s2.len() == s1.len());
            assert forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
                == (s1[q as int] | (if (q as int) < os.len() { os[q as int] } else { 0u32 })) by { }
            // the trailing face of the last block survives the word-wise OPNAME
            let e = self.bit_vec.nbits % 32;
            if e > 0 {
                {
                    let k0 = (k as int) - 1;
                    let s1_last = s1[k0];
                    let wpadL: u32 = if k0 < os.len() { os[k0] } else { 0u32 };
                    let s2_last = s2[k0];
                    let e32 = e as u32;
                    assert((1u32 << e) == (1u32 << e32));
                    assert(s1_last < (1u32 << e32)); // the post-grow tail face captured above
                    if k0 < os.len() {
                        // wpadL is other's last own block, under the shared
                        // block index; its tail width does not exceed e
                        assert(k0 == os.len() - 1);
                        assert((other.bit_vec.nbits as int) > k0 * 32);
                        assert(other.bit_vec.nbits <= self.bit_vec.nbits);
                        assert((other.bit_vec.nbits as int) % 32 <= (e as int));
                        lemma_pow2_mono(other.bit_vec.nbits % 32, e);
                        assert(os[k0] == other.bit_vec.storage@[(os.len() - 1) as int]);
                        assert(other.bit_vec.storage@[(os.len() - 1) as int]
                            < (1u32 << (other.bit_vec.nbits % 32)));
                        assert(wpadL < (1u32 << (other.bit_vec.nbits % 32)));
                        assert(wpadL < (1u32 << e32));
                    } else {
                        assert(wpadL == 0u32);
                        assert(wpadL < (1u32 << e32));
                    }
                    assert(s2_last == s1_last | wpadL);
                    assert(s2_last < (1u32 << e32)) by (bit_vector)
                        requires
                            s1_last < (1u32 << e32),
                            wpadL < (1u32 << e32),
                            s2_last == s1_last | wpadL,
                    ;

                };
            }
            assert(trailing_zero(&self.bit_vec)) by {
                if e > 0 {
                    assert(self.bit_vec.storage@[(blocks_for_bits(self.bit_vec.nbits) - 1) as int]
                        == s2[(k as int) - 1]);
                }
            }
        lemma_word_face(&other.bit_vec, s1, s2, self.bit_vec.nbits, old_stg, old_nb, 0u8);
        }
    }
    /// Origin Rust: pub fn intersect_with(&mut self, other: &Self)
    ///     { self.other_op(other, |w1, w2| w1 & w2) } (set/src/set.rs:461-463)
    /// Upstream doc (set.rs:442-447):
    ///   Intersects in-place with the specified other bit vector.
    pub exec fn intersect_with(&mut self, other: &Self)
        requires
            bs_inv(old(self)),
            bs_inv(other),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == if old(self).bit_vec.nbits < other.bit_vec.nbits {
                other.bit_vec.nbits
            } else {
                old(self).bit_vec.nbits
            },
            forall|j: usize| j < final(self).bit_vec.nbits ==> bs_at(final(self), j)
                == (bs_at(old(self), j) && bs_at(other, j)),
            // batch-H4 append (twin row: the same conjunction face
            // restated with an explicit trigger on the final-side term).
            // The auto-trigger of the row above lands on the other side
            // only, which leaves the zero-self layouts of the UT
            // harness without an in-scope matching term (the batch-H3
            // frozen is_empty items); this twin E-matches the
            // post-call membership term directly.
            forall|j: usize| j < final(self).bit_vec.nbits ==>
                (#[trigger] bs_at(final(self), j)
                    == (bs_at(old(self), j) && bs_at(other, j))),
    {
        let self_len = self.bit_vec.len();
        let other_len = other.bit_vec.len();
        if self_len < other_len {
            self.bit_vec.grow(other_len - self_len, false);
        }
        let ghost old_nb = old(self).bit_vec.nbits;
        let ghost olds = old(self).bit_vec.storage@;
        let ghost s1_nb = self.bit_vec.nbits;
        let ghost s1_e = s1_nb % 32;
        let ghost s1: Seq<u32> = self.bit_vec.storage@;
        let ghost s1_tail_ok: bool = (s1_e > 0 ==> s1[(s1.len() - 1) as int] < (1u32 << s1_e));
        let ghost grow_faces: bool = (forall|j2: usize| j2 < s1_nb ==>
            (#[trigger] bit_at(s1, s1_nb, j2)
                == (j2 < old_nb && bit_at(olds, old_nb, j2))));
        proof {
            // freeze the post-grow self faces the post proof consumes
            // (pure ghost terms: valid across the storage write loop)
            if s1_e > 0 {
                assert(trailing_zero(&self.bit_vec));
                assert(s1[(s1.len() - 1) as int] < (1u32 << s1_e));
                assert(s1_tail_ok);
            }
            assert forall|j2: usize| j2 < s1_nb ==>
                (#[trigger] bit_at(s1, s1_nb, j2)
                    == (j2 < old_nb && bit_at(olds, old_nb, j2))) by {
                if j2 < s1_nb {
                    if j2 < old_nb {
                        int_div_bound_lemma(j2, old_nb);
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2)
                            == bit_at(old(self).bit_vec.storage@,
                                old(self).bit_vec.nbits, j2));
                    } else {
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2) == false);
                    }
                }
            }
            assert(grow_faces);
        }
        let ghost old_stg: Seq<u32> = old(self).bit_vec.storage@;
        let ghost os: Seq<u32> = other.bit_vec.storage@;
        let ow = other.bit_vec.storage();
        let o_len = ow.len();
        let k = self.bit_vec.storage().len();
        proof {
            assert(ow@ == os);
            assert(k == s1.len());
            assert((o_len as int) == os.len());
        }
        let mut i: usize = 0;
        while i < k
            invariant
                i <= k,
                (k as int) == s1.len(),
                (o_len as int) == os.len(),
                ow@ == os,
                self.bit_vec.nbits == s1_nb,
                s1_tail_ok,
                forall|j2: usize| j2 < s1_nb ==>
                    (#[trigger] bit_at(s1, s1_nb, j2)
                        == (j2 < old_nb && bit_at(olds, old_nb, j2))),
                self.bit_vec.storage@.len() == s1.len(),
                forall|q: usize| (q as int) < (i as int) ==>
                    self.bit_vec.storage@[q as int]
                        == (s1[q as int] & (if (q as int) < os.len() { os[q as int] } else { 0u32 })),
                forall|q: usize| (q as int) >= (i as int) && (q as int) < s1.len() ==>
                    self.bit_vec.storage@[q as int] == s1[q as int],
            decreases (k - i),
        {
            let oldw = self.bit_vec.storage[i];
            let w = if i < o_len { ow[i] } else { 0u32 };
            let neww = oldw & w;
            self.bit_vec.storage.set(i, neww);
            proof {
                assert(self.bit_vec.storage@[i as int] == neww);
                assert(w == (if (i as int) < os.len() { os[i as int] } else { 0u32 }));
                assert(self.bit_vec.storage@[i as int]
                    == (s1[i as int] & (if (i as int) < os.len() { os[i as int] } else { 0u32 })));
            }
            i += 1;
        }
        proof {
            let s2 = self.bit_vec.storage@;
            assert(s2.len() == s1.len());
            assert forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
                == (s1[q as int] & (if (q as int) < os.len() { os[q as int] } else { 0u32 })) by { }
            // the trailing face of the last block survives the word-wise OPNAME
            let e = self.bit_vec.nbits % 32;
            if e > 0 {
                {
                    let k0 = (k as int) - 1;
                    let s1_last = s1[k0];
                    let wpadL: u32 = if k0 < os.len() { os[k0] } else { 0u32 };
                    let s2_last = s2[k0];
                    let e32 = e as u32;
                    assert((1u32 << e) == (1u32 << e32));
                    assert(s1_last < (1u32 << e32)); // the post-grow tail face captured above
                    if k0 < os.len() {
                        // wpadL is other's last own block, under the shared
                        // block index; its tail width does not exceed e
                        assert(k0 == os.len() - 1);
                        assert((other.bit_vec.nbits as int) > k0 * 32);
                        assert(other.bit_vec.nbits <= self.bit_vec.nbits);
                        assert((other.bit_vec.nbits as int) % 32 <= (e as int));
                        lemma_pow2_mono(other.bit_vec.nbits % 32, e);
                        assert(os[k0] == other.bit_vec.storage@[(os.len() - 1) as int]);
                        assert(other.bit_vec.storage@[(os.len() - 1) as int]
                            < (1u32 << (other.bit_vec.nbits % 32)));
                        assert(wpadL < (1u32 << (other.bit_vec.nbits % 32)));
                        assert(wpadL < (1u32 << e32));
                    } else {
                        assert(wpadL == 0u32);
                        assert(wpadL < (1u32 << e32));
                    }
                    assert(s2_last == s1_last & wpadL);
                    assert(s2_last < (1u32 << e32)) by (bit_vector)
                        requires
                            s1_last < (1u32 << e32),
                            s2_last == s1_last & wpadL,
                    ;

                };
            }
            assert(trailing_zero(&self.bit_vec)) by {
                if e > 0 {
                    assert(self.bit_vec.storage@[(blocks_for_bits(self.bit_vec.nbits) - 1) as int]
                        == s2[(k as int) - 1]);
                }
            }
        lemma_word_face(&other.bit_vec, s1, s2, self.bit_vec.nbits, old_stg, old_nb, 1u8);
        }
    }
    /// Origin Rust: pub fn difference_with(&mut self, other: &Self)
    ///     { self.other_op(other, |w1, w2| w1 & !w2) } (set/src/set.rs:493-495)
    /// Upstream doc (set.rs:465-470):
    ///   Makes this bit vector the difference with the specified other bit
    ///   vector in-place.
    pub exec fn difference_with(&mut self, other: &Self)
        requires
            bs_inv(old(self)),
            bs_inv(other),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == if old(self).bit_vec.nbits < other.bit_vec.nbits {
                other.bit_vec.nbits
            } else {
                old(self).bit_vec.nbits
            },
            forall|j: usize| j < final(self).bit_vec.nbits ==> bs_at(final(self), j)
                == (bs_at(old(self), j) && !bs_at(other, j)),
            // batch-H4 append (twin row: the same difference face
            // restated with an explicit trigger on the final-side term;
            // same trigger-topology motive as the intersect_with twin).
            forall|j: usize| j < final(self).bit_vec.nbits ==>
                (#[trigger] bs_at(final(self), j)
                    == (bs_at(old(self), j) && !bs_at(other, j))),
    {
        let self_len = self.bit_vec.len();
        let other_len = other.bit_vec.len();
        if self_len < other_len {
            self.bit_vec.grow(other_len - self_len, false);
        }
        let ghost old_nb = old(self).bit_vec.nbits;
        let ghost olds = old(self).bit_vec.storage@;
        let ghost s1_nb = self.bit_vec.nbits;
        let ghost s1_e = s1_nb % 32;
        let ghost s1: Seq<u32> = self.bit_vec.storage@;
        let ghost s1_tail_ok: bool = (s1_e > 0 ==> s1[(s1.len() - 1) as int] < (1u32 << s1_e));
        let ghost grow_faces: bool = (forall|j2: usize| j2 < s1_nb ==>
            (#[trigger] bit_at(s1, s1_nb, j2)
                == (j2 < old_nb && bit_at(olds, old_nb, j2))));
        proof {
            // freeze the post-grow self faces the post proof consumes
            // (pure ghost terms: valid across the storage write loop)
            if s1_e > 0 {
                assert(trailing_zero(&self.bit_vec));
                assert(s1[(s1.len() - 1) as int] < (1u32 << s1_e));
                assert(s1_tail_ok);
            }
            assert forall|j2: usize| j2 < s1_nb ==>
                (#[trigger] bit_at(s1, s1_nb, j2)
                    == (j2 < old_nb && bit_at(olds, old_nb, j2))) by {
                if j2 < s1_nb {
                    if j2 < old_nb {
                        int_div_bound_lemma(j2, old_nb);
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2)
                            == bit_at(old(self).bit_vec.storage@,
                                old(self).bit_vec.nbits, j2));
                    } else {
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2) == false);
                    }
                }
            }
            assert(grow_faces);
        }
        let ghost old_stg: Seq<u32> = old(self).bit_vec.storage@;
        let ghost os: Seq<u32> = other.bit_vec.storage@;
        let ow = other.bit_vec.storage();
        let o_len = ow.len();
        let k = self.bit_vec.storage().len();
        proof {
            assert(ow@ == os);
            assert(k == s1.len());
            assert((o_len as int) == os.len());
        }
        let mut i: usize = 0;
        while i < k
            invariant
                i <= k,
                (k as int) == s1.len(),
                (o_len as int) == os.len(),
                ow@ == os,
                self.bit_vec.nbits == s1_nb,
                s1_tail_ok,
                forall|j2: usize| j2 < s1_nb ==>
                    (#[trigger] bit_at(s1, s1_nb, j2)
                        == (j2 < old_nb && bit_at(olds, old_nb, j2))),
                self.bit_vec.storage@.len() == s1.len(),
                forall|q: usize| (q as int) < (i as int) ==>
                    self.bit_vec.storage@[q as int]
                        == (s1[q as int]
                            & (4294967295u32
                                ^ (if (q as int) < os.len() { os[q as int] } else { 0u32 }))),
                forall|q: usize| (q as int) >= (i as int) && (q as int) < s1.len() ==>
                    self.bit_vec.storage@[q as int] == s1[q as int],
            decreases (k - i),
        {
            let oldw = self.bit_vec.storage[i];
            let w = if i < o_len { ow[i] } else { 0u32 };
            let neww = oldw & (4294967295u32 ^ w);
            self.bit_vec.storage.set(i, neww);
            proof {
                assert(self.bit_vec.storage@[i as int] == neww);
                assert(w == (if (i as int) < os.len() { os[i as int] } else { 0u32 }));
                assert(self.bit_vec.storage@[i as int]
                    == (s1[i as int]
                        & (4294967295u32
                            ^ (if (i as int) < os.len() { os[i as int] } else { 0u32 }))));
            }
            i += 1;
        }
        proof {
            let s2 = self.bit_vec.storage@;
            assert(s2.len() == s1.len());
            assert forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
                == (s1[q as int]
                    & (4294967295u32
                        ^ (if (q as int) < os.len() { os[q as int] } else { 0u32 }))) by { }
            // the trailing face of the last block survives the word-wise andnot
            let e = self.bit_vec.nbits % 32;
            if e > 0 {
                {
                    let k0 = (k as int) - 1;
                    let s1_last = s1[k0];
                    let wpadL: u32 = if k0 < os.len() { os[k0] } else { 0u32 };
                    let s2_last = s2[k0];
                    let e32 = e as u32;
                    assert((1u32 << e) == (1u32 << e32));
                    assert(s1_last < (1u32 << e32)); // the post-grow tail face captured above
                    assert(s2_last == s1_last & (4294967295u32 ^ wpadL));
                    assert(s2_last < (1u32 << e32)) by (bit_vector)
                        requires
                            s1_last < (1u32 << e32),
                            s2_last == s1_last & (4294967295u32 ^ wpadL),
                    ;
                };
            }
            assert(trailing_zero(&self.bit_vec)) by {
                if e > 0 {
                    assert(self.bit_vec.storage@[(blocks_for_bits(self.bit_vec.nbits) - 1) as int]
                        == s2[(k as int) - 1]);
                }
            }
            lemma_word_face(&other.bit_vec, s1, s2, self.bit_vec.nbits, old_stg, old_nb, 2u8);
        }
    }

    /// Origin Rust: pub fn symmetric_difference_with(&mut self, other: &Self)
    ///     { self.other_op(other, |w1, w2| w1 ^ w2) } (set/src/set.rs:517-519)
    /// Upstream doc (set.rs:497-502):
    ///   Makes this bit vector the symmetric difference with the specified
    ///   other bit vector in-place.
    pub exec fn symmetric_difference_with(&mut self, other: &Self)
        requires
            bs_inv(old(self)),
            bs_inv(other),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == if old(self).bit_vec.nbits < other.bit_vec.nbits {
                other.bit_vec.nbits
            } else {
                old(self).bit_vec.nbits
            },
            forall|j: usize| j < final(self).bit_vec.nbits ==> bs_at(final(self), j)
                == (bs_at(old(self), j) != bs_at(other, j)),
    {
        let self_len = self.bit_vec.len();
        let other_len = other.bit_vec.len();
        if self_len < other_len {
            self.bit_vec.grow(other_len - self_len, false);
        }
        let ghost old_nb = old(self).bit_vec.nbits;
        let ghost olds = old(self).bit_vec.storage@;
        let ghost s1_nb = self.bit_vec.nbits;
        let ghost s1_e = s1_nb % 32;
        let ghost s1: Seq<u32> = self.bit_vec.storage@;
        let ghost s1_tail_ok: bool = (s1_e > 0 ==> s1[(s1.len() - 1) as int] < (1u32 << s1_e));
        let ghost grow_faces: bool = (forall|j2: usize| j2 < s1_nb ==>
            (#[trigger] bit_at(s1, s1_nb, j2)
                == (j2 < old_nb && bit_at(olds, old_nb, j2))));
        proof {
            // freeze the post-grow self faces the post proof consumes
            // (pure ghost terms: valid across the storage write loop)
            if s1_e > 0 {
                assert(trailing_zero(&self.bit_vec));
                assert(s1[(s1.len() - 1) as int] < (1u32 << s1_e));
                assert(s1_tail_ok);
            }
            assert forall|j2: usize| j2 < s1_nb ==>
                (#[trigger] bit_at(s1, s1_nb, j2)
                    == (j2 < old_nb && bit_at(olds, old_nb, j2))) by {
                if j2 < s1_nb {
                    if j2 < old_nb {
                        int_div_bound_lemma(j2, old_nb);
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2)
                            == bit_at(old(self).bit_vec.storage@,
                                old(self).bit_vec.nbits, j2));
                    } else {
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j2) == false);
                    }
                }
            }
            assert(grow_faces);
        }
        let ghost old_stg: Seq<u32> = old(self).bit_vec.storage@;
        let ghost os: Seq<u32> = other.bit_vec.storage@;
        let ow = other.bit_vec.storage();
        let o_len = ow.len();
        let k = self.bit_vec.storage().len();
        proof {
            assert(ow@ == os);
            assert(k == s1.len());
            assert((o_len as int) == os.len());
        }
        let mut i: usize = 0;
        while i < k
            invariant
                i <= k,
                (k as int) == s1.len(),
                (o_len as int) == os.len(),
                ow@ == os,
                self.bit_vec.nbits == s1_nb,
                s1_tail_ok,
                forall|j2: usize| j2 < s1_nb ==>
                    (#[trigger] bit_at(s1, s1_nb, j2)
                        == (j2 < old_nb && bit_at(olds, old_nb, j2))),
                self.bit_vec.storage@.len() == s1.len(),
                forall|q: usize| (q as int) < (i as int) ==>
                    self.bit_vec.storage@[q as int]
                        == (s1[q as int] ^ (if (q as int) < os.len() { os[q as int] } else { 0u32 })),
                forall|q: usize| (q as int) >= (i as int) && (q as int) < s1.len() ==>
                    self.bit_vec.storage@[q as int] == s1[q as int],
            decreases (k - i),
        {
            let oldw = self.bit_vec.storage[i];
            let w = if i < o_len { ow[i] } else { 0u32 };
            let neww = oldw ^ w;
            self.bit_vec.storage.set(i, neww);
            proof {
                assert(self.bit_vec.storage@[i as int] == neww);
                assert(w == (if (i as int) < os.len() { os[i as int] } else { 0u32 }));
                assert(self.bit_vec.storage@[i as int]
                    == (s1[i as int] ^ (if (i as int) < os.len() { os[i as int] } else { 0u32 })));
            }
            i += 1;
        }
        proof {
            let s2 = self.bit_vec.storage@;
            assert(s2.len() == s1.len());
            assert forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
                == (s1[q as int] ^ (if (q as int) < os.len() { os[q as int] } else { 0u32 })) by { }
            // the trailing face of the last block survives the word-wise xor
            let e = self.bit_vec.nbits % 32;
            if e > 0 {
                {
                    let k0 = (k as int) - 1;
                    let s1_last = s1[k0];
                    let wpadL: u32 = if k0 < os.len() { os[k0] } else { 0u32 };
                    let s2_last = s2[k0];
                    let e32 = e as u32;
                    assert(k0 * 32 + (e as int) == self.bit_vec.nbits);
                    assert((1u32 << e) == (1u32 << e32));
                    assert(s1_last < (1u32 << e32)); // the post-grow tail face captured above
                    if k0 < os.len() {
                        // wpadL is other's last own block, under the shared
                        // block index; its tail width does not exceed e
                        assert(k0 == os.len() - 1);
                        assert((other.bit_vec.nbits as int) > k0 * 32);
                        assert(other.bit_vec.nbits <= self.bit_vec.nbits);
                        assert((other.bit_vec.nbits as int) % 32 <= (e as int));
                        lemma_pow2_mono(other.bit_vec.nbits % 32, e);
                        assert(os[k0] == other.bit_vec.storage@[(os.len() - 1) as int]);
                        assert(other.bit_vec.storage@[(os.len() - 1) as int]
                            < (1u32 << (other.bit_vec.nbits % 32)));
                        assert(wpadL < (1u32 << (other.bit_vec.nbits % 32)));
                        assert(wpadL < (1u32 << e32));
                    } else {
                        assert(wpadL == 0u32);
                        assert(wpadL < (1u32 << e32));
                    }
                    assert(s2_last == s1_last ^ wpadL);
                    assert(s2_last < (1u32 << e32)) by (bit_vector)
                        requires
                            s1_last < (1u32 << e32),
                            wpadL < (1u32 << e32),
                            s2_last == s1_last ^ wpadL,
                    ;
                };
            }
            assert(trailing_zero(&self.bit_vec)) by {
                if e > 0 {
                    assert(self.bit_vec.storage@[(blocks_for_bits(self.bit_vec.nbits) - 1) as int]
                        == s2[(k as int) - 1]);
                }
            }
            assert forall|j: usize| j < self.bit_vec.nbits ==> bs_at(final(self), j)
                == (bs_at(old(self), j) != bs_at(other, j)) by {
                if j < self.bit_vec.nbits {
                    int_div_bound_lemma(j, self.bit_vec.nbits);
                    let kbi: usize = (j / 32) as usize;
                    let wpad: u32 = if (kbi as int) < os.len() { os[kbi as int] } else { 0u32 };
                    assert(kbi < s1.len());
                    assert(s2[kbi as int] == s1[kbi as int] ^ wpad);
                    lemma_xor_bit(s1[kbi as int], wpad, (j % 32) as usize);
                    lemma_padded_other_bit(&other.bit_vec, j, wpad);
                    assert(((wpad & (1u32 << (j % 32))) != 0u32) == (j < other.bit_vec.nbits
                        && bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j)));
                    let s1f = (s1[kbi as int] & (1u32 << (j % 32))) != 0u32;
                    let w2f = (wpad & (1u32 << (j % 32))) != 0u32;
                    let r2f: bool = (s2[kbi as int] & (1u32 << (j % 32))) != 0u32;
                    assert(r2f == (s1f != w2f));
                    assert(bit_at(s1, self.bit_vec.nbits, j)
                        == (j < old(self).bit_vec.nbits
                            && bit_at(old(self).bit_vec.storage@,
                                old(self).bit_vec.nbits, j)));
                    if j < old(self).bit_vec.nbits {
                        assert(s1f
                            == ((old(self).bit_vec.storage@[(j as int) / 32]
                                & (1u32 << (j % 32))) != 0u32));
                    } else {
                        assert(s1f == false);
                    }
                    assert(s1f == bs_at(old(self), j));
                    assert(w2f == bs_at(other, j));
                    assert(bs_at(final(self), j) == r2f);
                } else {
                    assert(bs_at(final(self), j) == false);
                }
            }
        }
    }

    /// Origin Rust: pub fn reserve_len(&mut self, len: usize)
    ///     { let cur_len = self.bit_vec.len();
    ///       if len >= cur_len { self.bit_vec.reserve(len - cur_len); } }
    ///     (set/src/set.rs:229-234)
    /// Upstream doc (set.rs:221-228):
    ///   Reserves capacity for at least `len` more elements... (each doc
    ///   example: reserve_len(10); assert!(s.capacity() >= 10);)
    pub exec fn reserve_len(&mut self, len: usize)
        requires
            bs_inv(old(self)),
            (len as int) < usize::MAX as int / 32, // upstream capacity-overflow face excluded
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            final(self).bit_vec.storage@ == old(self).bit_vec.storage@,
    {
        let cur_len = self.bit_vec.len();
        proof {
            assert(cur_len == self.bit_vec.nbits);
        }
        if len >= cur_len {
            proof {
                // the reserve call premises at this branch
                assert(len - cur_len == len - cur_len);
                assert((self.bit_vec.nbits as int) + ((len - cur_len) as int) == (len as int));
                assert(32 * (self.bit_vec.storage@.len() as int) <= usize::MAX as int) by {
                    assert(self.bit_vec.storage@.len()
                        == blocks_for_bits(self.bit_vec.nbits));
                    assert((self.bit_vec.nbits as int) <= (len as int));
                    assert(32 * (blocks_for_bits(self.bit_vec.nbits) as int)
                        <= (self.bit_vec.nbits as int) + 31);
                }
            }
            self.bit_vec.reserve(len - cur_len);
        }
    }

    /// Origin Rust: pub fn reserve_len_exact(&mut self, len: usize)
    ///     { let cur_len = self.bit_vec.len();
    ///       if len >= cur_len { self.bit_vec.reserve_exact(len - cur_len); } }
    ///     (set/src/set.rs:254-259)
    /// Upstream doc (set.rs:246-253):
    ///   Reserves the minimum capacity for the given `BitSet` to contain
    ///   `len` distinct elements.
    pub exec fn reserve_len_exact(&mut self, len: usize)
        requires
            bs_inv(old(self)),
            (len as int) < usize::MAX as int / 32, // upstream capacity-overflow face excluded
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            final(self).bit_vec.storage@ == old(self).bit_vec.storage@,
    {
        let cur_len = self.bit_vec.len();
        proof {
            assert(cur_len == self.bit_vec.nbits);
        }
        if len >= cur_len {
            proof {
                // the reserve_exact call premises at this branch
                assert((self.bit_vec.nbits as int) + ((len - cur_len) as int) == (len as int));
                assert(32 * (self.bit_vec.storage@.len() as int) <= usize::MAX as int) by {
                    assert(self.bit_vec.storage@.len()
                        == blocks_for_bits(self.bit_vec.nbits));
                    assert((self.bit_vec.nbits as int) <= (len as int));
                    assert(32 * (blocks_for_bits(self.bit_vec.nbits) as int)
                        <= (self.bit_vec.nbits as int) + 31);
                }
            }
            self.bit_vec.reserve_exact(len - cur_len);
        }
    }

    /// Origin Rust: #[inline] pub fn get_mut(&mut self) -> &mut BitVec<B>
    ///     { &mut self.bit_vec } (set/src/set.rs:320-322)
    /// Upstream doc (set.rs:299-318): Returns a mutable reference to the
    /// underlying bit vector. (the downstream-obligation tier: mutations
    /// through the reference stay within the BitVec method contracts that
    /// keep inv; the reference's final state is the caller's to account for)
    pub exec fn get_mut(&mut self) -> (r: &mut BitVec)
    {
        &mut self.bit_vec
    }

    /// Origin Rust: #[inline] pub fn shrink_to_fit(&mut self)
    ///     (set/src/set.rs:394-417)
    /// Upstream doc (set.rs:374-392):
    ///   Truncates the underlying vector to the least length required.
    /// Semantics, unpacked: the index scan finds the nonzero trailing
    /// block count; dropping whole trailing zero blocks never removes a
    /// set bit, and the universe is set to exactly the kept block count's
    /// bit width -- the kept-prefix bit faces and the zero cut words make
    /// the membership frame an equivalence. The unsafe storage surgery
    /// (storage_mut().truncate + set_len) stands as the bit-level
    /// truncate call here: same kept prefix, same universe face, and the
    /// structural invariant restored by the callee's own postconditions.
    pub exec fn shrink_to_fit(&mut self)
        requires
            bs_inv(old(self)),
            (old(self).bit_vec.nbits as int) < usize::MAX as int / 32, // upstream overflow faces excluded
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == 32 * final(self).bit_vec.storage@.len(),
            forall|i: usize| i < old(self).bit_vec.nbits ==> bs_at(final(self), i)
                == bs_at(old(self), i),
            // batch-H3 append (contract strengthening; two rows, callers
            // only gain facts, none retracted -- the harness tier needs
            // them for the UT bookkeeping faces):
            //   (a) the surgery is a pure prefix truncation, so the kept
            //       block count never exceeds the old one;
            //   (b) the member predicate is preserved at EVERY position,
            //       not just below the old universe -- the region the
            //       final universe newly covers reads the old tail word
            //       at-or-above its in-use width, and the trailing-zero
            //       half of inv zeroes those bits.
            final(self).bit_vec.nbits as int
                <= 32 * (old(self).bit_vec.storage@.len() as int),
            forall|i: usize| #[trigger] bs_at(final(self), i) == bs_at(old(self), i),
    {
        let ghost s0: Seq<u32> = self.bit_vec.storage@;
        proof {
            assert(s0 == old(self).bit_vec.storage@);
        }
        let ghost old_nb = old(self).bit_vec.nbits;
        let sref = self.bit_vec.storage();
        let old_len = sref.len();
        let mut n: usize = 0;
        while n < old_len && sref[old_len - 1 - n] == 0u32
            invariant
                n <= old_len,
                (old_len as int) == s0.len(),
                sref@ == s0,
                forall|q: usize| q < n ==> #[trigger] s0[old_len - 1 - q] == 0u32,
            decreases (old_len - n),
        {
            n += 1;
        }
        let trunc_len = old_len - n;
        proof {
            // the cut-away region is all zero words
            assert forall|p2: usize| (trunc_len <= p2) && (p2 < old_len) ==>
                s0[p2 as int] == 0u32 by {
                if trunc_len <= p2 && p2 < old_len {
                    let q = old_len - 1 - p2;
                    assert(q < n);
                    assert(s0[old_len - 1 - q] == 0u32);
                }
            }
            assert(old_nb < usize::MAX as int / 32);
        }
        // the unsafe storage surgery (origin storage_mut().truncate +
        // set_len): whole trailing zero blocks dropped, the universe set
        // to exactly the kept block count's bit width
        self.bit_vec.storage.truncate(trunc_len);
        proof {
            // vstd truncate: the prefix face
            assert(self.bit_vec.storage@ == s0.subrange(0, (trunc_len as int)));
            assert(self.bit_vec.storage@.len() == trunc_len);
        }
        self.bit_vec.nbits = trunc_len * 32;
        proof {
            // the structural invariant is restored here
            assert(blocks_for_bits(self.bit_vec.nbits) == trunc_len);
            assert(trailing_zero(&self.bit_vec));
            assert(inv(&self.bit_vec));
            // membership frame: kept words carry, cut words vanish
            assert forall|i: usize| i < old_nb ==> bs_at(final(self), i)
                == bs_at(old(self), i) by {
                if i < old_nb {
                    lemma_shrink_frame_at(self.bit_vec.storage@, s0,
                        self.bit_vec.nbits, old_nb, trunc_len as int, i);
                    assert(self.bit_vec.nbits == (trunc_len as int) * 32);
                    assert(bs_at(final(self), i)
                        == (i < self.bit_vec.nbits
                            && bit_at(self.bit_vec.storage@, self.bit_vec.nbits, i)));
                    assert(bs_at(old(self), i)
                        == (i < old_nb
                            && bit_at(old(self).bit_vec.storage@, old_nb, i)));
                    assert(old(self).bit_vec.storage@ == s0);
                }
            }
            // batch-H3 append row (a): the kept length bound
            assert((trunc_len as int) <= (s0.len() as int));
            assert(old(self).bit_vec.storage@ == s0);
            assert(final(self).bit_vec.nbits as int
                <= 32 * (old(self).bit_vec.storage@.len() as int));
            // batch-H3 append row (b): the full-range member frame
            assert forall|t: usize| #[trigger] bs_at(final(self), t)
                == bs_at(old(self), t) by {
                assert(self.bit_vec.nbits == (trunc_len as int) * 32);
                assert(old(self).bit_vec.storage@ == s0);
                if (t as int) < old_nb {
                    lemma_shrink_frame_at(self.bit_vec.storage@, s0,
                        self.bit_vec.nbits, old_nb, trunc_len as int, t);
                    assert(bs_at(final(self), t)
                        == (t < self.bit_vec.nbits
                            && bit_at(self.bit_vec.storage@, self.bit_vec.nbits, t)));
                    assert(bs_at(old(self), t)
                        == (t < old_nb
                            && bit_at(s0, old_nb, t)));
                } else {
                    // above the old universe the old side is memberless
                    assert(bs_at(old(self), t) == false);
                    if (t as int) < (self.bit_vec.nbits as int) {
                        // the final universe extends past the old one:
                        // t reads the old tail word at-or-above its
                        // in-use width; an aligned old universe cannot
                        // get here (the kept width would not exceed it)
                        let e0 = old_nb % 32;
                        if e0 == 0 {
                            assert(old_len as int == (old_nb as int) / 32) by {
                                assert(blocks_for_bits(old_nb) as int
                                    == (old_nb as int) / 32);
                                assert(blocks_for_bits(old_nb) as int
                                    == (old_len as int));
                            }
                            assert((old_nb as int) / 32 * 32 == old_nb);
                            assert((t as int) / 32 >= (old_nb as int) / 32);
                            assert((t as int) / 32 < (trunc_len as int)) by (nonlinear_arith)
                                requires
                                    (t as int) < (trunc_len as int) * 32,
                            ;
                            assert((trunc_len as int) <= (old_len as int));
                            assert(false);
                        }
                        // the unaligned case: t sits in the old last word,
                        // at-or-above the in-use width e0 -- the
                        // trailing-zero half of the old inv masks it
                        assert(blocks_for_bits(old_nb) as int
                            == (old_nb as int) / 32 + 1);
                        assert(old_len as int == (old_nb as int) / 32 + 1);
                        assert((old_nb as int) == 32 * ((old_len as int) - 1) + (e0 as int));
                        assert((t as int) / 32 >= (old_nb as int) / 32);
                        assert((t as int) / 32 < (trunc_len as int)) by (nonlinear_arith)
                            requires
                                (t as int) < (trunc_len as int) * 32,
                        ;
                        assert((trunc_len as int) <= (old_len as int));
                        assert((t as int) / 32 == (old_len as int) - 1);
                        assert((t as int) % 32 >= (e0 as int)) by (nonlinear_arith)
                            requires
                                (t as int) >= old_nb,
                                (t as int) < 32 * ((old_len as int) as int),
                                (old_nb as int) == 32 * ((old_len as int) - 1) + (e0 as int),
                                e0 <= 31usize,
                        ;
                        assert(t % 32 < 32);
                        assert(s0[(old_len as int) - 1] < (1u32 << e0));
                        lemma_pow_lt_bit(s0[(old_len as int) - 1], e0, t % 32);
                        assert(bit_at(s0, old_nb, t) == false);
                        assert(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, t)
                            == bit_at(s0, old_nb, t));
                    }
                }
            }
        }
    }

    /// Origin Rust: #[inline] pub fn is_disjoint(&self, other: &Self) -> bool
    ///     { self.intersection(other).next().is_none() } (set/src/set.rs:661-664)
    /// Deferred to the iterator batch: the definitionface is the
    /// intersection iterator's first step; the block-local spec face
    /// (no common member) will be carried with src/iter.rs.
    /// Upstream doc (set.rs:658-660):
    ///   Returns `true` if the set has no elements in common with `other`.

    /// Origin Rust: #[inline] pub fn is_subset(&self, other: &Self)
    ///     (set/src/set.rs:666-679; util::blocks_for_bits faces)
    /// Upstream doc (set.rs:665):
    ///   Returns `true` if the set is a subset of another.
    /// The block scan materialized as the padded word form (the zip/skip
    /// pair of the stream form): each own block must be the intersection
    /// with the other's padded word; self blocks beyond the other's join
    /// the zero-padding face, i.e. must be zero.
    pub exec fn is_subset(&self, other: &Self) -> (r: bool)
        requires
            bs_inv(self),
            bs_inv(other),
        ensures
            r == (forall|j: usize| j < self.bit_vec.nbits ==>
                (bs_at(self, j) ==> bs_at(other, j))),
    {
        let ghost s: Seq<u32> = self.bit_vec.storage@;
        let ghost os: Seq<u32> = other.bit_vec.storage@;
        let sw = self.bit_vec.storage();
        let ow = other.bit_vec.storage();
        let o_len = ow.len();
        let k = sw.len();
        proof {
            assert(sw@ == s);
            assert(ow@ == os);
            assert((k as int) == s.len());
        }
        let ghost old_nb = self.bit_vec.nbits;
        let ghost e0 = old_nb % 32;
        proof {
            if e0 > 0 {
                assert(trailing_zero(&self.bit_vec));
                assert(s[(s.len() - 1) as int] < (1u32 << e0));
            }
        }
        let mut good = true;
        let mut fail_kb: usize = k;
        for kbi in 0..k
            invariant
                (k as int) == s.len(),
                sw@ == s,
                ow@ == os,
                (o_len as int) == os.len(),
                good ==> (fail_kb == k
                    && forall|q: usize| (q as int) < (kbi as int) ==>
                        (s[q as int]
                            & (if (q as int) < os.len() { os[q as int] } else { 0u32 }))
                            == s[q as int]),
                (!good) ==> (fail_kb < k
                    && (s[fail_kb as int]
                        & (if (fail_kb as int) < os.len() { os[fail_kb as int] } else { 0u32 }))
                        != s[fail_kb as int]),
        {
            let w1 = sw[kbi];
            let w2 = if kbi < o_len { ow[kbi] } else { 0u32 };
            proof {
                assert(s[kbi as int] == w1);
                assert(w2 == (if (kbi as int) < os.len() { os[kbi as int] } else { 0u32 }));
            }
            if (w1 & w2) != w1 {
                good = false;
                fail_kb = kbi;
            }
        }
        proof {
            if good {
                assert(fail_kb == k);
                assert(forall|q: usize| (q as int) < (k as int) ==>
                    ((s[q as int]
                        & (if (q as int) < os.len() { os[q as int] } else { 0u32 }))
                        == s[q as int]));
                assert forall|j: usize| j < self.bit_vec.nbits ==>
                    (bs_at(self, j) ==> bs_at(other, j)) by {
                    if j < self.bit_vec.nbits {
                    int_div_bound_lemma(j, self.bit_vec.nbits);
                    let kbi2: usize = (j / 32) as usize;
                    let wpad = if (kbi2 as int) < os.len() { os[kbi2 as int] } else { 0u32 };
                    assert((s[kbi2 as int] & wpad) == s[kbi2 as int]);
                    let ownface = (s[kbi2 as int] & (1u32 << (j % 32))) != 0u32;
                    let padface = (wpad & (1u32 << (j % 32))) != 0u32;
                    lemma_padded_other_bit(&other.bit_vec, j, wpad);
                assert(((wpad & (1u32 << (j % 32))) != 0u32) == (j < other.bit_vec.nbits
                    && bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j)));
                    assert(padface == bs_at(other, j));
                    if ownface {
                        lemma_and_subset_bit(s[kbi2 as int], wpad, (j % 32) as usize);
                        assert(padface);
                    }
                    assert(ownface ==> padface);
                    assert(bs_at(self, j) == ownface);
                }
            }
            } else {
                // the failing word: some bit of self is missing in other
                let fail = fail_kb;
                let wpadf = if (fail as int) < os.len() { os[fail as int] } else { 0u32 };
                let w1 = s[fail as int];
                assert((w1 & wpadf) != w1);
                let d = w1 & (4294967295u32 ^ wpadf);
                lemma_andnot_nonzero(w1, wpadf);
                assert((w1 & wpadf) != w1);
                assert(d != 0u32);
                assert((d >> 0) == d) by (bit_vector);
                blk_set_bit_exists(d, 0);
                let t = choose|tw: usize|
                    tw <= 31 && ((d & (1u32 << tw)) != 0u32);
                assert((d & (1u32 << t)) != 0u32);
                lemma_andnot_bit_face(w1, wpadf, t);
                assert((w1 & (1u32 << t)) != 0u32);
                assert((wpadf & (1u32 << t)) == 0u32);
                let j: usize = ((fail as int) * 32 + (t as int)) as usize;
                {
                    assert(j < old_nb) by {
                        if (fail as int) < (k as int) - 1 {
                            assert((fail as int) * 32 + 31 < (k as int) * 32);
                            assert(old_nb > ((k as int) - 1) * 32);
                        } else if e0 == 0 {
                            assert(old_nb == (k as int) * 32);
                            assert(t < 32);
                        } else {
                            // the last word: the set bit of a trailing-masked
                            // word is below the tail width
                            assert(w1 == s[(k as int) - 1]);
                            assert(w1 < (1u32 << e0));
                            if t >= e0 {
                                lemma_pow_lt_bit(w1, e0, t);
                                assert(!((w1 & (1u32 << t)) != 0u32));
                                assert(false);
                            }
                        }
                    }
                    lemma_padded_other_bit(&other.bit_vec, j, wpadf);
                    assert(((wpadf & (1u32 << (j % 32))) != 0u32)
                        == (j < other.bit_vec.nbits
                            && bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j)));
                    assert((j % 32) as usize == t);
                    assert((wpadf & (1u32 << (j % 32))) == 0u32);
                    assert((j as int) / 32 == (fail as int));
                }
                assert(bs_at(self, j));
                assert(!bs_at(other, j));
                assert(!(forall|j: usize| j < self.bit_vec.nbits ==>
                    (bs_at(self, j) ==> bs_at(other, j))));
            }
        }
        good
    }

    /// Origin Rust: #[inline] pub fn is_superset(&self, other: &Self) -> bool
    ///     { other.is_subset(self) } (set/src/set.rs:681-684)
    /// Upstream doc (set.rs:680):
    ///   Returns `true` if the set is a superset of another.
    pub exec fn is_superset(&self, other: &Self) -> (r: bool)
        requires
            bs_inv(self),
            bs_inv(other),
        ensures
            r == (forall|j: usize| j < other.bit_vec.nbits ==>
                (bs_at(other, j) ==> bs_at(self, j))),
    {
        other.is_subset(self)
    }
}

// ===========================================================================
// Independent proof lemmas (tail banner): the machine bit-level witness
// pick for the is_empty nonempty direction.
// ===========================================================================

/// a nonzero block shifted to `step` still set at or above `step` yields
/// a bit position j in [step, 32) with the j-th bit set. (Recursion:
/// ghost code cannot run while loops.)
pub(crate) proof fn blk_set_bit_exists(blk: u32, step: usize)
    requires
        step <= 32,
        blk >> step != 0u32,
    ensures
        exists|j: usize| step <= j && j < 32 && (blk & (1u32 << j)) != 0u32,
    decreases
        32 - step,
{
    if step == 32 {
        assert((blk >> step) == 0u32) by (bit_vector)
            requires
                step == 32usize,
        ;
        assert(false);
    }
    if (blk & (1u32 << step)) != 0u32 {
        assert(step < 32);
        assert(exists|j: usize| step <= j && j < 32 && (blk & (1u32 << j)) != 0u32);
    } else {
        assert(step <= 31);
        assert((blk & (1u32 << step)) == (((blk >> step) & 1u32) << step)) by (bit_vector)
            requires
                step <= 31usize,
        ;
        assert(((blk >> step) & 1u32) << step == 0u32);
        assert((blk >> step) & 1u32 == 0u32) by (bit_vector)
            requires
                step <= 31usize,
                (((blk >> step) & 1u32) << step) == 0u32,
        ;
        assert((blk >> step) >> 1 == blk >> (step + 1)) by (bit_vector)
            requires
                step <= 31usize,
        ;
        assert((blk >> step) >> 1 != 0u32) by (bit_vector)
            requires
                ((blk >> step) & 1u32) == 0u32,
                (blk >> step) != 0u32,
        ;
        assert((blk >> (step + 1)) != 0u32);
        blk_set_bit_exists(blk, (step + 1) as usize);
    }
}

/// the zero block's masked face: no bit of zero is set (kept away from
/// the symbolic shift in the consumers' contexts).
pub(crate) proof fn lemma_zero_word_face(flag: u32)
    ensures
        (0u32 & flag) == 0u32,
{
    assert((0u32 & flag) == 0u32) by (bit_vector);
}

/// an intersecting rewrite keeps set bits: a set bit of the first word
/// is a set bit of the second (the subset face at one position).
pub(crate) proof fn lemma_and_subset_bit(x: u32, y: u32, t: usize)
    requires
        t <= 31usize,
        (x & y) == x,
        (x & (1u32 << t)) != 0u32,
    ensures
        (y & (1u32 << t)) != 0u32,
{
    assert((y & (1u32 << t)) != 0u32) by (bit_vector)
        requires
            t <= 31usize,
            (x & y) == x,
            (x & (1u32 << t)) != 0u32,
        ;
}

/// and-with complement: equality with the word is exactly the zero
/// complement word (the failing-word witness of the block scan).
pub(crate) proof fn lemma_andnot_nonzero(w1: u32, w2: u32)
    ensures
        ((w1 & w2) == w1) == ((w1 & (4294967295u32 ^ w2)) == 0u32),
{
    assert(((w1 & w2) == w1) == ((w1 & (4294967295u32 ^ w2)) == 0u32)) by (bit_vector);
}

/// a set bit of the and-with-complement word witnesses the pair of faces:
/// the first word has the bit, the second does not.
pub(crate) proof fn lemma_andnot_bit_face(w1: u32, w2: u32, t: usize)
    requires
        t <= 31usize,
        ((w1 & (4294967295u32 ^ w2)) & (1u32 << t)) != 0u32,
    ensures
        (w1 & (1u32 << t)) != 0u32 && (w2 & (1u32 << t)) == 0u32,
{
    assert(((w1 & (1u32 << t)) != 0u32) && ((w2 & (1u32 << t)) == 0u32)) by (bit_vector)
        requires
            t <= 31usize,
            ((w1 & (4294967295u32 ^ w2)) & (1u32 << t)) != 0u32,
        ;
}

/// the stored face combination behind _with (word faces to bit faces):
/// from the frozen post-grow faces and the storage image of the in-place
/// combine, each element's face is the pointwise boolean combination of
/// the two sets' faces. The per-element core lives in lemma_*_face_at
/// (concrete-index instances), the quantified flight is the caller-side
/// assert below.
pub(crate) proof fn lemma_word_face(
    other: &BitVec,
    s1: Seq<u32>, s2: Seq<u32>,
    nb2: usize,
    old_stg: Seq<u32>, old_nb: usize,
    kind: u8,
)
    requires
        kind == 0u8 || kind == 1u8 || kind == 2u8,
        inv(other),
        s1.len() == blocks_for_bits(nb2),
        s2.len() == s1.len(),
        forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
            == (if kind == 0u8 {
                    s1[q as int] | (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                } else if kind == 2u8 {
                    s1[q as int]
                        & (4294967295u32
                            ^ (if (q as int) < other.storage@.len() {
                                    other.storage@[q as int]
                                } else { 0u32 }))
                } else {
                    s1[q as int] & (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                }),
        forall|j: usize| j < nb2 ==>
            (#[trigger] bit_at(s1, nb2, j)
                == (j < old_nb && bit_at(old_stg, old_nb, j))),
    ensures
        forall|j: usize| j < nb2 ==>
            (kind == 0u8 ==>
                (bit_at(s2, nb2, j)
                    == ((j < old_nb && bit_at(old_stg, old_nb, j))
                        || (j < other.nbits && bit_at(other.storage@, other.nbits, j)))))
            && forall|j: usize| j < nb2 ==>
                (kind == 2u8 ==>
                    (bit_at(s2, nb2, j)
                        == ((j < old_nb && bit_at(old_stg, old_nb, j))
                            && !(j < other.nbits && bit_at(other.storage@, other.nbits, j)))))
            && forall|j: usize| j < nb2 ==>
                (kind == 1u8 ==>
                    (bit_at(s2, nb2, j)
                        == ((j < old_nb && bit_at(old_stg, old_nb, j))
                            && (j < other.nbits && bit_at(other.storage@, other.nbits, j))))),
{
    assert forall|j: usize| j < nb2 ==>
        (kind == 0u8 ==>
            (bit_at(s2, nb2, j)
                == ((j < old_nb && bit_at(old_stg, old_nb, j))
                    || (j < other.nbits && bit_at(other.storage@, other.nbits, j))))) by {
        if j < nb2 && kind == 0u8 {
            lemma_or_face_at(other, s1, s2, nb2, old_stg, old_nb, j, kind);
        }
    }
    assert forall|j: usize| j < nb2 ==>
        (kind == 1u8 ==>
            (bit_at(s2, nb2, j)
                == ((j < old_nb && bit_at(old_stg, old_nb, j))
                    && (j < other.nbits && bit_at(other.storage@, other.nbits, j))))) by {
        if j < nb2 && kind == 1u8 {
            lemma_and_face_at(other, s1, s2, nb2, old_stg, old_nb, j, kind);
        }
    }
    assert forall|j: usize| j < nb2 ==>
        (kind == 2u8 ==>
            (bit_at(s2, nb2, j)
                == ((j < old_nb && bit_at(old_stg, old_nb, j))
                    && !(j < other.nbits && bit_at(other.storage@, other.nbits, j))))) by {
        if j < nb2 && kind == 2u8 {
            lemma_andnot_face_at(other, s1, s2, nb2, old_stg, old_nb, j, kind);
        }
    }
}

/// the concrete-index core of the or combination.
pub(crate) proof fn lemma_or_face_at(
    other: &BitVec,
    s1: Seq<u32>, s2: Seq<u32>,
    nb2: usize,
    old_stg: Seq<u32>, old_nb: usize,
    j: usize, kind: u8,
)
    requires
        kind == 0u8,
        j < nb2,
        inv(other),
        s1.len() == blocks_for_bits(nb2),
        s2.len() == s1.len(),
        forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
            == (if kind == 0u8 {
                    s1[q as int] | (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                } else if kind == 2u8 {
                    s1[q as int]
                        & (4294967295u32
                            ^ (if (q as int) < other.storage@.len() {
                                    other.storage@[q as int]
                                } else { 0u32 }))
                } else {
                    s1[q as int] & (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                }),
        forall|w: usize| w < nb2 ==>
            (#[trigger] bit_at(s1, nb2, w)
                == (w < old_nb && bit_at(old_stg, old_nb, w))),
    ensures
        bit_at(s2, nb2, j)
            == ((j < old_nb && bit_at(old_stg, old_nb, j))
                || (j < other.nbits && bit_at(other.storage@, other.nbits, j))),
{
    int_div_bound_lemma(j, nb2);
    let kbi: usize = (j / 32) as usize;
    lemma_block_below(j, nb2, kbi);
    assert(kbi < s1.len());
    let wpad: u32 = if (kbi as int) < other.storage@.len() {
        other.storage@[kbi as int]
    } else {
        0u32
    };
    assert(s2[kbi as int] == s1[kbi as int] | wpad);
    lemma_or_bit(s1[kbi as int], wpad, (j % 32) as usize);
    lemma_padded_other_bit(other, j, wpad);
    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
    assert(bit_at(s1, nb2, j) == (j < old_nb && bit_at(old_stg, old_nb, j))); // instance of the merged-face requirement
    let s2w: u32 = s2[kbi as int];
    assert(bit_at(s2, nb2, j) == ((s2w & (1u32 << ((j % 32) as u32))) != 0u32));
}

/// the concrete-index core of the and combination.
pub(crate) proof fn lemma_and_face_at(
    other: &BitVec,
    s1: Seq<u32>, s2: Seq<u32>,
    nb2: usize,
    old_stg: Seq<u32>, old_nb: usize,
    j: usize, kind: u8,
)
    requires
        kind == 1u8,
        j < nb2,
        inv(other),
        s1.len() == blocks_for_bits(nb2),
        s2.len() == s1.len(),
        forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
            == (if kind == 0u8 {
                    s1[q as int] | (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                } else if kind == 2u8 {
                    s1[q as int]
                        & (4294967295u32
                            ^ (if (q as int) < other.storage@.len() {
                                    other.storage@[q as int]
                                } else { 0u32 }))
                } else {
                    s1[q as int] & (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                }),
        forall|w: usize| w < nb2 ==>
            (#[trigger] bit_at(s1, nb2, w)
                == (w < old_nb && bit_at(old_stg, old_nb, w))),
    ensures
        bit_at(s2, nb2, j)
            == ((j < old_nb && bit_at(old_stg, old_nb, j))
                && (j < other.nbits && bit_at(other.storage@, other.nbits, j))),
{
    int_div_bound_lemma(j, nb2);
    let kbi: usize = (j / 32) as usize;
    lemma_block_below(j, nb2, kbi);
    assert(kbi < s1.len());
    let wpad: u32 = if (kbi as int) < other.storage@.len() {
        other.storage@[kbi as int]
    } else {
        0u32
    };
    assert(s2[kbi as int] == s1[kbi as int] & wpad);
    lemma_and_bit(s1[kbi as int], wpad, (j % 32) as usize);
    lemma_padded_other_bit(other, j, wpad);
    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
    assert(bit_at(s1, nb2, j) == (j < old_nb && bit_at(old_stg, old_nb, j))); // instance of the merged-face requirement
    let s2w: u32 = s2[kbi as int];
    assert(bit_at(s2, nb2, j) == ((s2w & (1u32 << ((j % 32) as u32))) != 0u32));
}

/// the concrete-index core of the andnot combination.
pub(crate) proof fn lemma_andnot_face_at(
    other: &BitVec,
    s1: Seq<u32>, s2: Seq<u32>,
    nb2: usize,
    old_stg: Seq<u32>, old_nb: usize,
    j: usize, kind: u8,
)
    requires
        kind == 2u8,
        j < nb2,
        inv(other),
        s1.len() == blocks_for_bits(nb2),
        s2.len() == s1.len(),
        forall|q: usize| (q as int) < s1.len() ==> s2[q as int]
            == (if kind == 0u8 {
                    s1[q as int] | (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                } else if kind == 2u8 {
                    s1[q as int]
                        & (4294967295u32
                            ^ (if (q as int) < other.storage@.len() {
                                    other.storage@[q as int]
                                } else { 0u32 }))
                } else {
                    s1[q as int] & (if (q as int) < other.storage@.len() {
                            other.storage@[q as int]
                        } else { 0u32 })
                }),
        forall|w: usize| w < nb2 ==>
            (#[trigger] bit_at(s1, nb2, w)
                == (w < old_nb && bit_at(old_stg, old_nb, w))),
    ensures
        bit_at(s2, nb2, j)
            == ((j < old_nb && bit_at(old_stg, old_nb, j))
                && !(j < other.nbits && bit_at(other.storage@, other.nbits, j))),
{
    int_div_bound_lemma(j, nb2);
    let kbi: usize = (j / 32) as usize;
    lemma_block_below(j, nb2, kbi);
    assert(kbi < s1.len());
    let wpad: u32 = if (kbi as int) < other.storage@.len() {
        other.storage@[kbi as int]
    } else {
        0u32
    };
    assert(s2[kbi as int] == s1[kbi as int] & (4294967295u32 ^ wpad));
    lemma_andnot_bit(s1[kbi as int], wpad, (j % 32) as usize);
    lemma_padded_other_bit(other, j, wpad);
    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
    assert(bit_at(s1, nb2, j) == (j < old_nb && bit_at(old_stg, old_nb, j))); // instance of the merged-face requirement
    let s2w: u32 = s2[kbi as int];
    assert(bit_at(s2, nb2, j) == ((s2w & (1u32 << ((j % 32) as u32))) != 0u32));
}

/// the shrink frame at one element: after the trailing-zero surgery the
/// kept bits are unchanged and the cut-away region was all zero.
pub(crate) proof fn lemma_shrink_frame_at(
    self_stg: Seq<u32>, old_stg: Seq<u32>,
    self_nb: usize, old_nb: usize,
    trunc_len: int, i: usize,
)
    requires
        i < old_nb,
        old_stg.len() == blocks_for_bits(old_nb),
        self_stg == old_stg.subrange(0, trunc_len),
        self_nb == trunc_len * 32,
        trunc_len <= old_stg.len(),
        forall|p: usize| trunc_len <= p && p < old_stg.len() ==>
            old_stg[p as int] == 0u32,
    ensures
        (i < self_nb && bit_at(self_stg, self_nb, i))
            == (i < old_nb && bit_at(old_stg, old_nb, i)),
{
    if i < trunc_len * 32 {
        assert((i as int) / 32 < trunc_len) by (nonlinear_arith)
            requires i < trunc_len * 32,;
        assert(self_stg == old_stg.subrange(0, trunc_len));
        assert(self_stg[(i as int) / 32] == old_stg[(i as int) / 32]);
        assert(i < self_nb) by (nonlinear_arith)
            requires
                i < trunc_len * 32,
                self_nb == trunc_len * 32,
            ;
    } else {
        // beyond the kept width the element sits in a cut word: zero
        assert(trunc_len * 32 <= i);
        int_div_bound_lemma(i, old_nb);
        assert((i as int) / 32 < old_stg.len());
        assert(old_stg[(i as int) / 32] == 0u32);
        lemma_zero_word_face(1u32 << (i % 32));
        assert(0u32 & (1u32 << (i % 32)) == 0u32);
        assert(bit_at(old_stg, old_nb, i)
            == ((old_stg[(i as int) / 32] & (1u32 << (i % 32))) != 0u32));
        assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
        assert(bit_at(old_stg, old_nb, i) == false);
    }
}

/// a set member index stays under the universe's block count (the block
/// scan face used by the word-level bridging lemmas).
pub(crate) proof fn lemma_block_below(j: usize, nb2: usize, kbi: usize)
    requires
        j < nb2,
        kbi == (j / 32) as usize,
    ensures
        (j as int) / 32 == (kbi as int),
{
    int_div_bound_lemma(j, nb2);
}

/// the two-power map is monotone within the u32 shift range.
pub(crate) proof fn lemma_pow2_mono(a: usize, b: usize)
    requires
        a <= b,
        b < 32,
    ensures
        (1u32 << a) <= (1u32 << b),
{
    assert((1u32 << (a as u32)) <= (1u32 << (b as u32))) by (bit_vector)
        requires
            (a as u32) <= (b as u32),
            (b as u32) <= 31u32,
    ;
    assert(1u32 << a == 1u32 << (a as u32));
    assert(1u32 << b == 1u32 << (b as u32));
}

/// one padded word of the other side has exactly the other set's bit
/// face at element j: own block inside the block count, zero padding
/// beyond, and the trailing zero tail of the last own block hiding all
/// bits at or above the universe end.
pub(crate) proof fn lemma_padded_other_bit(other: &BitVec, j: usize, word: u32)
    requires
        inv(other),
        word == if 0 <= (j as int) / 32 < other.storage@.len() {
            other.storage@[(j as int) / 32]
        } else {
            0u32
        },
    ensures
        ((word & (1u32 << (j % 32))) != 0u32)
            == (j < other.nbits && bit_at(other.storage@, other.nbits, j)),
{
    let kbi = (j as int) / 32;
    let t = (j % 32) as usize;
    if j < other.nbits {
        // inside the universe: the padded word is the own block
        int_div_bound_lemma(j, other.nbits);
        assert(kbi < other.storage@.len());
        assert(word == other.storage@[kbi]);
        assert(j < other.nbits && bit_at(other.storage@, other.nbits, j)
            == ((other.storage@[kbi] & (1u32 << t)) != 0u32)) by {
        }
    } else {
        if kbi >= other.storage@.len() {
            // beyond the other side's storage: the zero-padding face
            assert(word == 0u32);
            lemma_zero_word_face(1u32 << t);
            assert((word & (1u32 << t)) == 0u32);
        } else {
            // the last own block, at or above the universe end
            assert(other.nbits % 32 > 0) by {
                if other.nbits % 32 == 0 {
                    assert(kbi >= other.nbits / 32);
                    assert(other.storage@.len() == other.nbits / 32);
                    assert(kbi >= other.storage@.len());
                    assert(false);
                }
            }
            let e2 = other.nbits % 32;
            assert(kbi == other.storage@.len() - 1) by {
                assert(kbi >= other.nbits / 32);
                assert(other.storage@.len() == other.nbits / 32 + 1);
            }
            assert(t >= e2) by {
                assert((j as int) / 32 == kbi);
                assert(j >= other.nbits);
                assert(j < (kbi + 1) * 32);
                assert(other.nbits == kbi * 32 + e2);
            }
            lemma_pow_lt_bit(other.storage@[kbi], e2, t);
            assert(word == other.storage@[kbi]);
            assert(((word & (1u32 << (j % 32))) != 0u32) == false);
        }
    }
}

// ---------------------------------------------------------------------------
// Origin Rust: impl<B: BitBlock> Clone for BitSet<B> { fn clone(&self) ->
//     Self { BitSet { bit_vec: self.bit_vec.clone() } }
//     fn clone_from(&mut self, other) { self.bit_vec.clone_from(&other.bit_vec) } }
//     (set/src/set.rs:16-26; usize materialization -- the BitVec clone legs)
// ---------------------------------------------------------------------------

/// the padded bit walk decomposes into two constant member ranges
/// through the verified split lemmas (the bit-layer count face).
pub proof fn lemma_count_two_ranges(
    s: Seq<u32>,
    nb: usize,
    t0a: usize, t0b: usize,
    t1a: usize, t1b: usize,
)
    requires
        0 <= t0a as int,
        t0a <= t0b <= t1a <= t1b <= nb,
        forall|p: usize| p < t0a ==> !bit_at(s, nb, p),
        forall|p: usize| t0a <= p && p < t0b ==> bit_at(s, nb, p),
        forall|p: usize| t0b <= p && p < t1a ==> !bit_at(s, nb, p),
        forall|p: usize| t1a <= p && p < t1b ==> bit_at(s, nb, p),
        forall|p: usize| t1b <= p && p < nb ==> !bit_at(s, nb, p),
    ensures
        count_bits(s, nb, 0, nb)
            == ((t0b as int) - (t0a as int)) + ((t1b as int) - (t1a as int)),
{
    lemma_count_split(s, nb, 0, t0b, nb);
    assert(count_bits(s, nb, t0b, nb)
        == count_bits(s, nb, t0b, t1b) + count_bits(s, nb, t1b, nb)) by {
        lemma_count_split(s, nb, t0b, t1b, nb);
    }
    assert(count_bits(s, nb, t1b, nb) == 0int) by {
        lemma_count_range_const(s, nb, t1b, nb, false);
    }
    assert(count_bits(s, nb, t0b, t1b)
        == count_bits(s, nb, t0b, t1a) + count_bits(s, nb, t1a, t1b)) by {
        lemma_count_split(s, nb, t0b, t1a, t1b);
    }
    lemma_count_range_const(s, nb, t0b, t1a, false);
    assert(count_bits(s, nb, t0b, t1a) == 0int);
    lemma_count_range_const(s, nb, t1a, t1b, true);
    assert(count_bits(s, nb, 0, t0b)
        == count_bits(s, nb, 0, t0a) + count_bits(s, nb, t0a, t0b)) by {
        lemma_count_split(s, nb, 0, t0a, t0b);
    }
    lemma_count_range_const(s, nb, 0, t0a, false);
    assert(count_bits(s, nb, 0, t0a) == 0int);
    lemma_count_range_const(s, nb, t0a, t0b, true);
}
impl BitSet {

    /// Origin Rust: fn clone(&self) -> Self { BitSet { bit_vec:
    ///     self.bit_vec.clone() } } (set.rs:17-21)
    /// Upstream doc: (no doc comment on the trait impl; the semantic face
    /// is Copy-value equality: the clone has the same members.)
    pub exec fn clone(&self) -> (r: BitSet)
        requires
            bs_inv(self),
        ensures
            bs_inv(&r),
            r.bit_vec.nbits == self.bit_vec.nbits,
            forall|j: usize| #[trigger] bs_at(&r, j) == bs_at(self, j),
    {
        let bv = self.bit_vec.clone_exec();
        proof {
            assert(bv.storage@ == self.bit_vec.storage@);
            assert(bv.nbits == self.bit_vec.nbits);
        }
        let r = BitSet { bit_vec: bv };
        proof {
            assert(r.bit_vec.nbits == self.bit_vec.nbits);
            assert(r.bit_vec.storage@ == self.bit_vec.storage@);
        }
        r
    }

    /// Origin Rust: fn clone_from(&mut self, other) {
    ///     self.bit_vec.clone_from(&other.bit_vec) } (set.rs:23-25)
    /// Upstream doc: (no doc comment on the trait impl; the semantic
    /// face is the in-place copy: after clone_from, self has the same
    /// members as other.)
    pub exec fn clone_from(&mut self, other: &BitSet)
        requires
            bs_inv(old(self)),
            bs_inv(other),
        ensures
            bs_inv(final(self)),
            final(self).bit_vec.nbits == other.bit_vec.nbits,
            forall|j: usize| j < other.bit_vec.nbits
                ==> #[trigger] bs_at(final(self), j) == bs_at(other, j),
    {
        let other_bv = &other.bit_vec;
        self.bit_vec.clone_from_exec(other_bv);
        proof {
            assert(final(self).bit_vec.storage@ == other.bit_vec.storage@);
            assert(final(self).bit_vec.nbits == other.bit_vec.nbits);
        }
    }

    /// Origin Rust: impl<B: BitBlock> PartialEq for BitSet<B> { fn eq
    ///     (&self, other) -> bool { self.iter().eq(other) } } (set.rs:68-73)
    /// Upstream doc (set.rs:69):
    ///   impl PartialEq for BitSet: the trait equality over the element
    ///   iterators (no separate doc comment; the Rust API docs phrase it
    ///   as element-set equality over the iterator walk).
    pub exec fn eq(&self, other: &BitSet) -> (r: bool)
        requires
            bs_inv(self),
            bs_inv(other),
        ensures
            r == forall|j: usize| j < bs_max_nb(self, other)
                ==> (#[trigger] bs_at(self, j) == bs_at(other, j)),
    {
        let nb_s: usize = self.bit_vec.nbits;
        let nb_o: usize = other.bit_vec.nbits;
        let mnb: usize = if nb_s < nb_o { nb_o } else { nb_s };
        proof {
            assert(mnb == bs_max_nb(self, other));
        }
        let ghost s0: Seq<u32> = self.bit_vec.storage@;
        let ghost o0: Seq<u32> = other.bit_vec.storage@;
        let mut good = true;
        let mut failkb: usize = mnb;
        for j in 0..mnb
            invariant
                bs_inv(self),
                bs_inv(other),
                self.bit_vec.storage@ == s0,
                other.bit_vec.storage@ == o0,
                self.bit_vec.nbits == nb_s,
                other.bit_vec.nbits == nb_o,
                mnb == bs_max_nb(self, other),
                good ==> (failkb == mnb
                    && forall|q: usize| (q as int) < (j as int)
                        ==> (bs_at(self, q) == bs_at(other, q))),
                (!good) ==> (failkb < mnb
                    && (bs_at(self, failkb) != bs_at(other, failkb))),
        {
            let g1 = self.bit_vec.get(j);
            let g2 = other.bit_vec.get(j);
            let b1: bool = match g1 {
                Some(x) => x,
                None => false,
            };
            let b2: bool = match g2 {
                Some(x) => x,
                None => false,
            };
            proof {
                assert(bs_at(self, j) == b1) by {
                    if j < self.bit_vec.nbits {
                        assert(g1 == Some(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j)));
                        assert(b1 == bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j));
                    } else {
                        assert(g1 is None);
                        assert(b1 == false);
                        assert(bs_at(self, j) == false);
                    }
                }
                assert(bs_at(other, j) == b2) by {
                    if j < other.bit_vec.nbits {
                        assert(g2 == Some(bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j)));
                        assert(b2 == bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j));
                    } else {
                        assert(g2 is None);
                        assert(b2 == false);
                        assert(bs_at(other, j) == false);
                    }
                }
            }
            if b1 != b2 {
                good = false;
                failkb = j;
            }
        }
        proof {
            if good {
                assert(failkb == mnb);
                assert(forall|q: usize| (q as int) < (mnb as int)
                    ==> (bs_at(self, q) == bs_at(other, q)));
            } else {
                assert(failkb < mnb);
                assert(bs_at(self, failkb) != bs_at(other, failkb));
            }
        }
        good
    }

    /// Origin Rust: pub fn is_disjoint(&self, other: &Self) -> bool {
    ///     self.intersection(other).next().is_none() } (set.rs:661-663)
    /// Upstream doc (set.rs:658-659):
    ///   Returns `true` if the set has no elements in common with `other`.
    ///   This is equivalent to checking for an empty intersection.
    /// (Mirror mechanism note: the origin walks the intersection iterator;
    /// the mirror runs the padded word scan -- the None face of the
    /// iterator walk equals the no-common-word face of the padded scan,
    /// so the contract is stated on the padded-word level.)
    pub exec fn is_disjoint(&self, other: &Self) -> (r: bool)
        requires
            bs_inv(self),
            bs_inv(other),
        ensures
            r == forall|j: usize| !(bs_at(self, j) && bs_at(other, j)),
    {
        let ghost s: Seq<u32> = self.bit_vec.storage@;
        let ghost os: Seq<u32> = other.bit_vec.storage@;
        let sw = self.bit_vec.storage();
        let ow = other.bit_vec.storage();
        let k = sw.len();
        let ok = ow.len();
        proof {
            assert(sw@ == s);
            assert(ow@ == os);
            assert((k as int) == s.len());
            assert((ok as int) == os.len());
            assert(s == self.bit_vec.storage@);
            assert(os == other.bit_vec.storage@);
        }
        // the pairwise scan covers exactly the shared block range: a
        // common element must live in a block both storages carry
        let ub: usize = if k < ok { k } else { ok };
        let mut good = true;
        let mut failkb: usize = ub;
        for kbi in 0..ub
            invariant
                (k as int) == s.len(),
                (ok as int) == os.len(),
                ub <= k,
                ub <= ok,
                sw@ == s,
                ow@ == os,
                s == self.bit_vec.storage@,
                os == other.bit_vec.storage@,
                good ==> (failkb == ub
                    && forall|q: usize| (q as int) < (kbi as int)
                        ==> (s[q as int] & os[q as int]) == 0u32),
                (!good) ==> (failkb < ub
                    && (s[failkb as int] & os[failkb as int]) != 0u32),
        {
            let w1 = sw[kbi];
            let w2 = ow[kbi];
            proof {
                assert(s[kbi as int] == w1);
                assert(os[kbi as int] == w2);
            }
            if (w1 & w2) != 0u32 {
                good = false;
                failkb = kbi;
            }
        }
        proof {
            if good {
                assert(failkb == ub);
                assert(forall|q: usize| (q as int) < (ub as int)
                    ==> (s[q as int] & os[q as int]) == 0u32);
                assert forall|j: usize| !(bs_at(self, j) && bs_at(other, j)) by {
                    if bs_at(self, j) {
                        int_div_bound_lemma(j, self.bit_vec.nbits);
                        let k2: usize = (j / 32) as usize;
                        let m: u32 = 1u32 << (j % 32);
                        assert((s[k2 as int] & m) != 0u32);
                        if k2 < ok {
                            // the shared word is inside the scan: the other
                            // side's same bit is dead (the pairwise AND is 0)
                            assert(k2 < k) by (nonlinear_arith)
                                requires (k2 as int) * 32 <= (j as int)
                                    && (j as int) < (k2 as int) * 32 + 32
                                    && (j as int) < (k as int) * 32;
                            assert((s[k2 as int] & os[k2 as int]) == 0u32);
                            let w1h: u32 = s[k2 as int];
                            let w2h: u32 = os[k2 as int];
                            assert(os[k2 as int] == w2h);
                            assert(s[k2 as int] == w1h);
                            assert((w2h & m) == 0u32) by (bit_vector)
                                requires (w1h & w2h) == 0u32
                                    && (w1h & m) != 0u32
                                    && ((j % 32) as u32) < 32u32
                                    && m == (1u32 << ((j % 32) as u32));
                            assert((os[k2 as int] & m) == 0u32);
                            lemma_padded_other_bit(&other.bit_vec, j, w2h);
                            assert(bs_at(other, j) == false);
                        } else {
                            // the index is past the other storage: the
                            // padded word is the empty word
                            lemma_padded_other_bit(&other.bit_vec, j, 0u32);
                            assert(bs_at(other, j) == false);
                        }
                    }
                }
            } else {
                // the failing word: some bit has both faces set
                let fail = failkb;
                let w1 = s[fail as int];
                let w2 = os[fail as int];
                assert((w1 & w2) != 0u32);
                assert((w1 & w2) >> 0usize == w1 & w2) by (bit_vector);
                blk_set_bit_exists(w1 & w2, 0usize);
                assert(other.bit_vec.storage@ == os);
                assert(self.bit_vec.storage@ == s);
                let t = choose|tw: usize| tw <= 31
                    && (w1 & w2) & (1u32 << tw) != 0u32;
                assert((w1 & w2) & (1u32 << t) != 0u32);
                assert((w1 & (1u32 << t)) != 0u32) by (bit_vector)
                    requires (w1 & w2) & (1u32 << t) != 0u32;
                assert((w2 & (1u32 << t)) != 0u32) by (bit_vector)
                    requires (w1 & w2) & (1u32 << t) != 0u32;
                let j: usize = ((fail as int) * 32 + (t as int)) as usize;
                assert((j as int) / 32 == (fail as int)) by (nonlinear_arith)
                    requires (j as int) == (fail as int) * 32 + (t as int)
                        && 0 <= (t as int) && (t as int) < 32;
                assert((j as int) % 32 == (t as int)) by (nonlinear_arith)
                    requires (j as int) == (fail as int) * 32 + (t as int)
                        && 0 <= (t as int) && (t as int) < 32;
                lemma_padded_other_bit(&self.bit_vec, j, s[fail as int]);
                assert((s[fail as int] & (1u32 << (j % 32))) != 0u32);
                lemma_padded_other_bit(&other.bit_vec, j, os[fail as int]);
                assert((os[fail as int] & (1u32 << (j % 32))) != 0u32);
                assert(bs_at(self, j));
                assert(bs_at(other, j));
                assert(!forall|q: usize| !(bs_at(self, q) && bs_at(other, q)));
            }
        }
        good
    }
}

// ---------------------------------------------------------------------------
// batch D part 2: the element-collection ordering traits (set.rs:37-73
// faces) -- the lex ordering face and the Extend/FromIterator recursion
// ---------------------------------------------------------------------------

/// Origin Rust: impl<B: BitBlock> Ord for BitSet<B> { fn cmp(&self,
///     other) -> Ordering { self.iter().cmp(other) } } (set.rs:61-66)
/// u8 materialization of cmp::Ordering for the spec face (0 = Less, 1 =
/// Equal, 2 = Greater): the lex ordering of the two own-stream element
/// sequences is the position face of the padded bit walk -- the first
/// padded position where the two faces differ decides (self carrying
/// the bit is Less: its element sequence has that element and the other
/// sequence's next element is strictly larger). The Equal arm is the
/// padded equality of fn eq.
pub open spec fn bs_prefix_eq(xs: &BitSet, ys: &BitSet, w: usize) -> bool {
    forall|q: usize| q < w ==> (#[trigger] bs_at(xs, q) == bs_at(ys, q))
}

pub open spec fn bs_has_member_above(xs: &BitSet, from: usize) -> bool {
    exists|t: usize| from < t && t < xs.bit_vec.nbits && bs_at(xs, t)
}

/// SPEC-DOC MISMATCH note (none): the lex walk of the two element
/// sequences is surplus-aware -- the lex rule of the upstream
/// `Iterator::cmp` walk is: walk both sequences; at the earliest
/// differing position p, the side whose next element is strictly larger
/// loses, and a side with no next element (its walk ended) loses. The
/// mirror face decomposes into the padded bit positions for exactly
/// that rule (see the branch comments; the earlier 2-branch face missed
/// the surplus case -- a spec-transcription fix of the audit pass).
pub open spec fn bs_ordering_face(xs: &BitSet, ys: &BitSet) -> u8 {
    if (forall|j: usize| j < bs_max_nb(xs, ys)
        ==> (#[trigger] bs_at(xs, j) == bs_at(ys, j))) {
        1u8
    } else if (exists|w: usize| (bs_at(xs, w) && !bs_at(ys, w)
        && bs_prefix_eq(xs, ys, w) && bs_has_member_above(ys, w))) {
        // self holds the earliest diff and ys still has members after w:
        // self's next element is w, ys' is larger -- self is Less
        0u8
    } else if (exists|w: usize| (!bs_at(xs, w) && bs_at(ys, w)
        && bs_prefix_eq(xs, ys, w) && bs_has_member_above(xs, w))) {
        // ys holds the earliest diff and xs still has members after w:
        // xs' next element is larger -- self is Greater
        2u8
    } else if (exists|w: usize| (bs_at(xs, w) && !bs_at(ys, w)
        && bs_prefix_eq(xs, ys, w) && !bs_has_member_above(ys, w))) {
        // self holds the earliest diff and ys' walk ended: self survives
        2u8
    } else if (exists|w: usize| (!bs_at(xs, w) && bs_at(ys, w)
        && bs_prefix_eq(xs, ys, w) && !bs_has_member_above(xs, w))) {
        // ys holds the earliest diff and xs' walk ended: ys survives
        0u8
    } else {
        // the padded equality covers the wider universe (the tail
        // padding is zero under inv, so the walk lengths ride along)
        1u8
    }
}

impl BitSet {

    /// the surplus walk: whether the set still holds a member strictly
    /// above the position (the cmp walk ends at the earliest diff and
    /// compares the next elements of the two walks; the mirror scans
    /// the padded bits directly).
    /// Translation-only: no upstream fn counterpart (the pin's cmp is
    /// the one-line `self.iter().cmp(other)` delegation, set.rs:61-66;
    /// upstream context is the ordering-faces banner, set.rs:37-73).
    pub exec fn has_member_from(bs: &BitSet, from: usize) -> (r: bool)
        requires
            bs_inv(bs),
            from <= 4294967232usize,
        ensures
            r == bs_has_member_above(bs, from),
    {
        let nb = bs.bit_vec.nbits;
        let mut done = false;
        for q in (from + 1)..nb
            invariant
                bs_inv(bs),
                nb == bs.bit_vec.nbits,
                done ==> bs_has_member_above(bs, from),
                (!done) ==> (forall|t: usize| (from as int) < t
                    && t < (q as int) ==> !bs_at(bs, t)),
        {
            let g = bs.contains(q);
            if g {
                done = true;
                proof {
                    assert(bs_has_member_above(bs, from)) by {
                        // the witness: q is the first member above `from`
                        assert((q as int) < (nb as int));
                        assert((from as int) < (q as int));
                        assert(bs_at(bs, q));
                    }
                }
            }
        }
        done
    }
}

impl BitSet {

    /// Origin Rust: impl<B: BitBlock> PartialOrd for BitSet<B> { fn
    ///     partial_cmp(&self, other) -> Some(self.cmp(other)) }
    ///     (set.rs:54-59)
    /// (the Ord face is total under the padded walk, so the partial
    /// wrapper is Some of the u8 materialization.)
    pub exec fn partial_cmp(&self, other: &BitSet) -> (r: u8)
        requires
            bs_inv(self),
            bs_inv(other),
            self.bit_vec.nbits <= 4294967232usize,
            other.bit_vec.nbits <= 4294967232usize,
        ensures
            r == bs_ordering_face(self, other),
    {
        let c = self.cmp(other);
        c
    }

    /// Origin Rust: impl<B: BitBlock> Ord for BitSet<B> { fn cmp(&self,
    ///     other) -> Ordering { self.iter().cmp(other) } } (set.rs:61-66)
    /// (see bs_ordering_face for the u8 materialization note.)
    pub exec fn cmp(&self, other: &BitSet) -> (r: u8)
        requires
            bs_inv(self),
            bs_inv(other),
            self.bit_vec.nbits <= 4294967232usize,
            other.bit_vec.nbits <= 4294967232usize,
        ensures
            r == bs_ordering_face(self, other),
    {
        let nb_s: usize = self.bit_vec.nbits;
        let nb_o: usize = other.bit_vec.nbits;
        let mnb: usize = if nb_s < nb_o { nb_o } else { nb_s };
        proof {
            assert(mnb == bs_max_nb(self, other));
        }
        let ghost s0: Seq<u32> = self.bit_vec.storage@;
        let ghost o0: Seq<u32> = other.bit_vec.storage@;
        let mut good = true;
        let mut failkb: usize = mnb;
        let mut sflag = false;
        let ghost mut pwidth: int = 0int;
        for j in 0..mnb
            invariant
                bs_inv(self),
                bs_inv(other),
                self.bit_vec.storage@ == s0,
                other.bit_vec.storage@ == o0,
                self.bit_vec.nbits == nb_s,
                other.bit_vec.nbits == nb_o,
                mnb == bs_max_nb(self, other),
                good ==> (failkb == mnb && sflag == false),
                (!good) ==> (failkb < mnb
                    && (bs_at(self, failkb) != bs_at(other, failkb))
                    && sflag == bs_at(self, failkb)
                    && pwidth == failkb as int),
                (good && pwidth == j as int)
                    || (good && pwidth == j as int + 1)
                    || (!good && pwidth <= j as int),
                forall|q: usize| (q as int) < pwidth
                    ==> (#[trigger] bs_at(self, q) == bs_at(other, q)),
        {
            let g1 = self.bit_vec.get(j);
            let g2 = other.bit_vec.get(j);
            let b1: bool = match g1 {
                Some(x) => x,
                None => false,
            };
            let b2: bool = match g2 {
                Some(x) => x,
                None => false,
            };
            proof {
                assert(bs_at(self, j) == b1) by {
                    if j < self.bit_vec.nbits {
                        assert(g1 == Some(bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j)));
                        assert(b1 == bit_at(self.bit_vec.storage@, self.bit_vec.nbits, j));
                    } else {
                        assert(g1 is None);
                        assert(b1 == false);
                        assert(bs_at(self, j) == false);
                    }
                }
                assert(bs_at(other, j) == b2) by {
                    if j < other.bit_vec.nbits {
                        assert(g2 == Some(bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j)));
                        assert(b2 == bit_at(other.bit_vec.storage@, other.bit_vec.nbits, j));
                    } else {
                        assert(g2 is None);
                        assert(b2 == false);
                        assert(bs_at(other, j) == false);
                    }
                }
            }
            if good {
                if b1 != b2 {
                    good = false;
                    failkb = j;
                    sflag = b1;
                    proof {
                        // the prefix face of this round is handed over unchanged
                        assert(failkb == j);
                        assert(pwidth == failkb as int);
                    }
                } else {
                    proof {
                        assert(bs_at(self, j) == bs_at(other, j));
                        pwidth = j as int + 1;
                    }
                }
            }
        }
        proof {
            if good {
                assert(failkb == mnb);
                assert(sflag == false);
                // pwidth rides at mnb or mnb+1 after the last good round;
                // either scope covers the padded-equality face
                assert(forall|q: usize| (q as int) < (mnb as int)
                    ==> (#[trigger] bs_at(self, q) == bs_at(other, q)));
            } else {
                assert(failkb < mnb);
                let fw = failkb;
                assert(bs_at(self, fw) != bs_at(other, fw));
                assert(sflag == bs_at(self, fw));
                assert(pwidth == fw as int);
                assert(forall|q: usize| q < fw
                    ==> (#[trigger] bs_at(self, q) == bs_at(other, q)));
                if sflag {
                    assert(bs_at(self, fw) && !bs_at(other, fw));
                } else {
                    // the Greater face: the Less witness does not exist
                    assert(!exists|w: usize| (bs_at(self, w) && !bs_at(other, w)
                        && forall|q: usize| q < w ==> (#[trigger] bs_at(self, q) == bs_at(other, q)))) by {
                        if exists|w: usize| (bs_at(self, w) && !bs_at(other, w)
                            && forall|q: usize| q < w ==> (bs_at(self, q) == bs_at(other, q))) {
                            let w = choose|w2: usize| bs_at(self, w2) && !bs_at(other, w2)
                                && forall|q: usize| q < w2 ==> (bs_at(self, q) == bs_at(other, q));
                            if w < fw {
                                assert(bs_at(self, w) == bs_at(other, w));
                                assert(false);
                            } else if w == fw {
                                assert(bs_at(self, fw) == sflag);
                                assert(false);
                            } else {
                                assert(bs_at(self, fw) == bs_at(other, fw));
                                assert(false);
                            }
                        }
                    }
                }
            }
        }
        let surplus_o = Self::has_member_from(other, failkb);
        let surplus_s = Self::has_member_from(self, failkb);
        proof {
            if good {
                // Equal face: the padded walk covers the wider universe
                assert(forall|j: usize| j < mnb ==> (bs_at(self, j) == bs_at(other, j)));
                assert(bs_ordering_face(self, other) == 1u8);
            } else {
                let fw = failkb;
                assert((fw as int) < (mnb as int));
                assert(bs_at(self, fw) != bs_at(other, fw));
                assert(sflag == bs_at(self, fw));
                assert(bs_prefix_eq(self, other, fw));
                if sflag {
                    // self holds the earliest diff; the other walk's next
                    // element existence decides the two ordering faces
                    assert(bs_has_member_above(other, fw) == surplus_o);
                    if surplus_o {
                        assert(bs_ordering_face(self, other) == 0u8);
                    } else {
                        assert(bs_ordering_face(self, other) == 2u8);
                    }
                } else {
                    assert(bs_has_member_above(self, fw) == surplus_s);
                    if surplus_s {
                        assert(bs_ordering_face(self, other) == 2u8);
                    } else {
                        assert(bs_ordering_face(self, other) == 0u8);
                    }
                }
            }
        }
        if good {
            1u8
        } else if sflag {
            if surplus_o {
                0u8
            } else {
                2u8
            }
        } else {
            if surplus_s {
                2u8
            } else {
                0u8
            }
        }
    }

    /// Origin Rust: impl<B: BitBlock> Extend<usize> for BitSet<B> { fn
    ///     extend<I: IntoIterator<Item = usize>>(&mut self, iter) { for
    ///     i in iter { self.insert(i); } } } (set.rs:45-52)
    /// (the IntoIterator materialization: the harness drives a Vec; the
    /// elementwise face is the insert recursion, proven item by item.)
    pub exec fn extend_items(&mut self, items: &Vec<usize>)
        requires
            bs_inv(old(self)),
            forall|p: usize| p < items@.len()
                ==> items@[p as int] <= usize::MAX - 1,
        ensures
            bs_inv(final(self)),
            forall|j: usize| #[trigger] bs_at(final(self), j)
                == (bs_at(old(self), j)
                    || (exists|p: usize| p < items@.len()
                        && items@[p as int] == j)),
    {
        let ghost items_seq: Seq<usize> = items@;
        let ilen: usize = items.len();
        for q in 0..ilen
            invariant
                bs_inv(self),
                items@ == items_seq,
                (items@.len() as int) == ilen as int,
                q <= ilen,
                forall|p: usize| p < items@.len()
                    ==> items@[p as int] <= usize::MAX - 1,
                forall|j: usize| bs_at(self, j)
                    == (bs_at(old(self), j)
                        || (exists|p: usize| p < (q as int)
                            && items_seq[p as int] == j)),
        {
            let value = items[q];
            proof {
                assert(value == items_seq[q as int]);
            }
            self.insert(value);
            proof {
                let v = value;
                assert forall|j: usize|
                    bs_at(self, j) == (bs_at(old(self), j)
                        || (exists|p: usize| p < (q as int) + 1
                            && items_seq[p as int] == j)) by {
                    // split the insert face over the item list prefix
                    if bs_at(old(self), j) {
                        assert(bs_at(self, j) == true);
                        assert(bs_at(self, j) == (bs_at(old(self), j)
                            || (exists|p: usize| p < (q as int) + 1
                                && items_seq[p as int] == j)));
                    } else if j == v {
                        let p: usize = q;
                        assert(items_seq[p as int] == v);
                    } else {
                        assert(bs_at(self, j) == (bs_at(old(self), j)
                            || (exists|p: usize| p < (q as int) + 1
                                && items_seq[p as int] == j)));
                    }
                }
            }
        }
    }

    /// Origin Rust: impl<B: BitBlock> FromIterator<usize> for BitSet<B> {
    ///     fn from_iter<I: IntoIterator<Item = usize>>(iter) -> Self {
    ///     let mut ret = Self::default(); ret.extend(iter); ret } }
    ///     (set.rs:37-43)
    pub exec fn from_iter_items(items: &Vec<usize>) -> (r: BitSet)
        requires
            forall|p: usize| p < items@.len()
                ==> items@[p as int] <= usize::MAX - 1,
        ensures
            bs_inv(&r),
            forall|j: usize| #[trigger] bs_at(&r, j)
                == (exists|p: usize| p < items@.len()
                    && items@[p as int] == j),
    {
        let mut ret = Self::default();
        ret.extend_items(items);
        ret
    }
}

} // verus!
