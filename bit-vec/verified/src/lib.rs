
#![verifier::loop_isolation(false)]
#![feature(allocator_api)]
use vstd::prelude::*;
use vstd::seq::lemma_seq_ext_equal;
use std::alloc::Allocator; // needed by the assume_specification<Vec::capacity> signature

verus! {

// =====================================================================
// std external spec injection (the missing-standard-library-specifications
// fix branch, minimal sound spec): alloc::vec::Vec::capacity has no vstd
// spec while the capacity family (with_capacity/reserve/reserve_exact/
// capacity/push_within_capacity) needs its value. capacity is modeled as
// an uninterpreted function of the vec allocation state, tied down by the
// std Vec invariant (rustdoc: capacity "at least equal to length" when it
// holds elements):
//   ensures spec_vec_capacity(vec) == cap, cap@ >= vec@.len()
// reserve_exact is absent from vstd as well; injected with the same
// entries view as vstd's Vec::reserve (an allocator-layer operation).
// shrink_to_fit (the closing-batch addition) is absent too; injected
// with the entries view preserved plus the post-shrink std guarantee
// that the capacity still covers the length (rustdoc: down "as close
// as possible to the length", never below it).
// trusted-boundary disclosure in out/harness-inventory.md.
// =====================================================================

pub uninterp spec fn spec_vec_capacity<T, A: Allocator>(v: &Vec<T, A>) -> usize;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::capacity ](vec: &Vec<T, A>) -> (cap: usize)
    ensures
        spec_vec_capacity(vec) == cap,
        cap@ >= vec@.len(),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::reserve_exact ](
    vec: &mut Vec<T, A>,
    additional: usize,
)
    ensures
        final(vec)@ == old(vec)@,
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::shrink_to_fit ](
    vec: &mut Vec<T, A>,
)
    ensures
        final(vec)@ == old(vec)@,
        spec_vec_capacity(final(vec)) >= final(vec)@.len(),
;

/// saturating multiply-by-32 model (std usize::saturating_mul semantics).
pub open spec fn spec_sat_mul32(c: usize) -> usize {
    if (c as int) * 32 > usize::MAX as int {
        usize::MAX
    } else {
        ((c as int) * 32) as usize
    }
}

/// the BitVec capacity in bits: 32 per storage block, saturating
/// (the upstream capacity() materialization).
pub open spec fn spec_bit_capacity(bv: &BitVec) -> usize {
    spec_sat_mul32(spec_vec_capacity(&bv.storage))
}

// ===========================================================================
// 0. State model (Origin Rust: lib.rs:239-244)
//     pub struct BitVec<B = u32> { storage: Vec<B>, nbits: usize }
// u32 materialization; fields made pub (the reference-style harness
// builds them field by field -- minimal visibility relaxation).
// ===========================================================================

pub struct BitVec {
    pub storage: Vec<u32>,
    pub nbits: usize,
}

// ---------------------------------------------------------------------------
// spec model
// ---------------------------------------------------------------------------

/// Origin Rust: fn blocks_for_bits<B: BitBlock>(bits: usize) -> usize
///     { if bits % B::bits() == 0 { bits / B::bits() } else { bits / B::bits() + 1 } }
pub open spec fn blocks_for_bits(bits: usize) -> usize {
    ((bits as int) / 32 + if (bits as int) % 32 > 0 { 1int } else { 0int }) as usize
}

/// Origin Rust: fn mask_for_bits<B: BitBlock>(bits: usize) -> B
///     { (!B::zero()) >> ((B::bits() - bits % B::bits()) % B::bits()) }
/// u32 materialization (in spec mode `!`/shifts have mathematical
/// semantics, so it is written in 2^e form): with e = nbits%32 > 0 this
/// is 2^e-1 (low e bits set), with e % 32 == 0 it is all ones.
pub open spec fn trailing_mask(nbits: usize) -> u32 {
    if nbits % 32 == 0 {
        4294967295u32
    } else {
        ((1u32 << (nbits % 32)) - 1u32) as u32
    }
}

/// used-mask of the tail block (Origin Rust: the `mask = (B::one() <<
/// extra_bits) - B::one()` of last_block_with_mask, lib.rs:697, i.e. 2^e-1;
/// used only in the e>0 context).
pub open spec fn used_mask(nbits: usize) -> u32
    recommends
        nbits % 32 > 0,
{
    ((1u32 << (nbits % 32)) - 1u32) as u32
}

/// bit-wise model: the bool value at index i (read only under i < nbits).
pub open spec fn bit_at(storage: Seq<u32>, nbits: usize, i: usize) -> bool {
    (storage[(i / 32) as int] & (1u32 << (i % 32))) != 0u32
}

/// invariant half 1: storage has no excess length (lib.rs:745-747).
pub open spec fn len_inv(bv: &BitVec) -> bool {
    bv.storage@.len() == blocks_for_bits(bv.nbits)
}

/// invariant half 2: the last block's unused bits are all 0 (lib.rs:736-742
/// equivalent form, lemma_trailing_zero_alt).
pub open spec fn trailing_zero(bv: &BitVec) -> bool {
    let n = bv.nbits;
    n % 32 == 0 || bv.storage@[(blocks_for_bits(n) - 1) as int] < 1u32 << (n % 32)
}

/// Full structural invariant. For e>0, `last < 2^e` is equivalent to
/// `last & !used_mask(n) == 0`; the mask-form conversion goes through
/// lemma_trailing_zero_alt.
pub open spec fn inv(bv: &BitVec) -> bool {
    &&& len_inv(bv)
    &&& trailing_zero(bv)
}

/// Value-level all/none predicates (the upstream algorithm's direct
/// characterization on the block-value domain; one-way bridges to the
/// bit-wise model: all_spec => every used bit true, none_spec => every
/// used bit false, see lemma_all_spec_bits / lemma_none_spec_bits).
/// The fill(true) branch reads the old tail-block value as a placeholder
/// (fill semantics: the entry is an all-ones block value).
pub open spec fn all_spec(bv: &BitVec) -> bool {
    let w = bv.storage@.len();
    w == 0
    || (forall|k: usize| k < w - 1 ==> bv.storage@[k as int] == 4294967295u32)
        && bv.storage@[(w - 1) as int] == trailing_mask(bv.nbits)
}

pub open spec fn none_spec(bv: &BitVec) -> bool {
    forall|k: usize| k < bv.storage@.len() ==> bv.storage@[k as int] == 0u32
}


/// Selector for the tail ones-fill input (the tail-block op input for
///      the process family negated precondition).
pub open spec fn with_ones_input(pre: &BitVec, w2: usize) -> u32 {
    let n = pre.nbits;
    if n % 32 > 0 && w2 == (pre.storage@.len() - 1) as usize {
        pre.storage@[w2 as int] | (4294967295u32 ^ (((1u32 << (n % 32)) - 1u32) as u32))
    } else {
        pre.storage@[w2 as int]
    }
}


/// Sequence pointwise-equality predicate (carried bidirectionally between
///      if conditions and ensures).
pub open spec fn seq_ptwise<A>(s1: Seq<A>, s2: Seq<A>) -> bool {
    forall|w2: int| 0 <= w2 < s1.len() ==> s1[w2] == s2[w2]
}

/// exec bridge (spec fns cannot be called directly from the vstd exec
/// domain; per-value equal to blocks_for_bits).
/// Upstream doc (lib.rs:409-409):
///   Computes how many blocks are needed to store that many bits
pub exec fn blocks_for_bits_exec(bits: usize) -> (r: usize)
    ensures
        r == blocks_for_bits(bits),
{
    let q = bits / 32;
    if bits % 32 == 0 {
        q
    } else {
        q + 1
    }
}

/// Origin Rust: impl<B: BitBlock> Default for BitVec<B> { fn default() -> Self {
///     BitVec { storage: Vec::new(), nbits: 0 } } }
pub exec fn bv_default() -> (bv: BitVec)
    ensures
        inv(&bv),
        bv.nbits == 0,
        bv.storage@.len() == 0,
{
    BitVec { storage: Vec::new(), nbits: 0 }
}

/// Origin Rust: pub fn new_general() -> Self { Default::default() }
///             / pub fn new() -> Self (impl BitVec<u32> specialization, lib.rs:442-444)
/// Upstream doc (lib.rs:433-440):
///   Creates an empty `BitVec`.
pub exec fn new() -> (bv: BitVec)
    ensures
        inv(&bv),
        bv.nbits == 0,
{
    bv_default()
}

impl BitVec {
    /// Origin Rust: pub fn len(&self) -> usize { self.nbits }
    /// Upstream doc (lib.rs:1806-1806):
    ///   Returns the total number of bits in this vector
    pub exec fn len(&self) -> (r: usize)
        ensures
            r == self.nbits,
    {
        self.nbits
    }

    /// Origin Rust: pub fn is_empty(&self) -> bool { self.len() == 0 }
    /// Upstream doc (lib.rs:1822-1822):
    ///   Returns true if there are no bits in this vector
    pub exec fn is_empty(&self) -> (r: bool)
        ensures
            r == (self.nbits == 0),
    {
        self.nbits == 0
    }

    /// Origin Rust: pub fn from_elem_general(len: usize, bit: bool) -> Self
    ///     { let nblocks = blocks_for_bits::<B>(len);
    ///       let mut bit_vec = BitVec { storage: vec![if bit { !B::zero() } else { B::zero() }; nblocks], nbits: len };
    ///       bit_vec.fix_last_block(); bit_vec } (lib.rs:545-553)
///     The `vec![x; n]` literal construction (vstd has no equivalent exec
///     primitive) is rewritten as a while loop; semantics = single-value
///     fill (exec-code-preservation note).
    /// Upstream doc (lib.rs:530-543):
    ///   Creates a `BitVec` that holds `nbits` elements, setting each element
    ///   to `bit`.
    pub exec fn from_elem_general(len: usize, bit: bool) -> (bv: BitVec)
        ensures
            inv(&bv),
            bv.nbits == len,
            forall|i: usize| i < len ==> bit_at(bv.storage@, len, i) == bit,
    {
        /* exec bridge: the spec fn blocks_for_bits cannot be called directly
           in the exec domain. */
        let nblocks = blocks_for_bits_exec(len);
        /* Origin Rust: if bit { !B::zero() } else { B::zero() }; (in a spec
           context `!` cannot be asserted, materialized as a literal) */
        let fill: u32 = if bit { 4294967295u32 } else { 0u32 };
        let mut storage: Vec<u32> = Vec::new();
        let mut k: usize = 0;
        while k < nblocks
            invariant
                storage@.len() == k,
                k <= nblocks,
                forall|j: usize| j < k ==> storage@[j as int] == fill,
            decreases
                nblocks - k,
        {
            storage.push(fill);
            k += 1;
        }
        let mut bv = BitVec { storage, nbits: len };
        bv.fix_last_block();
        proof {
            assert(len_inv(&bv));
            assert(trailing_zero(&bv));
            assert forall|i: usize| i < len implies bit_at(bv.storage@, len, i) == bit by {
                int_div_bound_lemma(i, len);
                let w = i / 32;
                let b = i % 32;
                assert(w < nblocks);
                let e = len % 32;
                assert(e <= 31) by {
                    assert(e < 32);
                }
                let b_u = b as u32;
                let e_u = e as u32;
                assert(b_u <= 31u32) by {
                    assert(b < 32);
                }
                let mask: u32 = ((1u32 << e) - 1u32) as u32;
                let elem = bv.storage@[w as int];
                if e == 0 || w < nblocks - 1 {
                    if w < nblocks - 1 {
                        assert(elem == fill);
                        if bit {
                            assert((elem & (1u32 << b_u)) != 0u32) by (bit_vector)
                                requires
                                    elem == 4294967295u32,
                                    b_u <= 31u32,
                            ;
                        } else {
                            assert((elem & (1u32 << b_u)) == 0u32) by (bit_vector)
                                requires
                                    elem == 0u32,
                            ;
                        }
                    } else {
                        assert(w == nblocks - 1);
                        assert(nblocks >= 1);
                        assert(elem == fill);
                        if bit {
                            assert((elem & (1u32 << b_u)) != 0u32) by (bit_vector)
                                requires
                                    elem == 4294967295u32,
                                    b_u <= 31u32,
                            ;
                        } else {
                            assert((elem & (1u32 << b_u)) == 0u32) by (bit_vector)
                                requires
                                    elem == 0u32,
                            ;
                        }
                    }
                } else {
                    assert(nblocks >= 1);
                    assert(w == nblocks - 1);
                    assert(b_u < e_u) by {
                        int_div_bound_lemma(i, len);
                        assert(b <= (len - 1) % 32);
                        assert(e - 1 == (len - 1) % 32);
                    }
                    assert((mask & (1u32 << b_u)) == (1u32 << b_u)) by (bit_vector)
                        requires
                            mask == (1u32 << e_u) - 1u32,
                            b_u < e_u,
                            e_u <= 31u32,
                    ;
                    if bit {
                        assert(fill & mask == mask) by (bit_vector)
                            requires
                                fill == 4294967295u32,
                                mask == (1u32 << e_u) - 1u32,
                                e_u <= 31u32,
                        ;
                        assert(elem == fill & mask);
                        assert((fill & mask) & (1u32 << b) != 0u32) by (bit_vector)
                            requires
                                mask == ((1u32 << e) - 1u32) as u32,
                                fill == 4294967295u32,
                                e <= 31usize,
                                b <= 31usize,
                                b < e,
                        ;
                        assert((elem & (1u32 << b_u)) == ((fill & mask) & (1u32 << b_u)));
                        assert((elem & (1u32 << b_u)) != 0u32);
                    } else {
                        assert(fill & mask == 0u32) by (bit_vector)
                            requires
                                fill == 0u32,
                        ;
                        assert(elem == 0u32);
                        assert((elem & (1u32 << b_u)) == 0u32) by (bit_vector)
                            requires
                                elem == 0u32,
                        ;
                    }
                }
            }
        }
        bv
    }

    /// Origin Rust: pub fn from_elem(len: usize, bit: bool) -> Self
    ///     { BitVec::<u32>::from_elem_general(len, bit) } (lib.rs:461-463)
    /// Upstream doc (lib.rs:446-459):
    ///   Creates a `BitVec` that holds `nbits` elements, setting each element
    ///   to `bit`.
    pub exec fn from_elem(len: usize, bit: bool) -> (bv: BitVec)
        ensures
            inv(&bv),
            bv.nbits == len,
            forall|i: usize| i < len ==> bit_at(bv.storage@, len, i) == bit,
    {
        Self::from_elem_general(len, bit)
    }

    /// Origin Rust: pub fn get(&self, i: usize) -> Option<bool> {...} (lib.rs:780-790)
///     ensure_invariant() -> requires self.inv() (header convention).
///     std `Option::map` has no vstd contract; expanded with an explicit
///     match (equivalent semantics).
    /// Upstream doc (lib.rs:764-778):
    ///   Retrieves the value at index `i`, or `None` if the index is out of bounds.
    pub exec fn get(&self, i: usize) -> (r: Option<bool>)
        requires
            inv(self),
        ensures
            inv(self),
            i >= self.nbits ==> r is None,
            i < self.nbits ==> r == Some(bit_at(self.storage@, self.nbits, i)),
    {
        if i >= self.nbits {
            return None;
        }
        let w = i / 32;
        let b = i % 32;
        /* Origin Rust: let w = i / B::bits(); let b = i % B::bits(); (u32 materialized) */
        match self.storage.get(w) {
            Some(&block) => Some((block & (1u32 << b)) != 0u32),
            None => None,
        }
    }

    /// Origin Rust: pub fn get_unchecked(&self, i: usize) -> bool {...} (lib.rs:816-822)
///     # Safety contract: i < nbits (out of bounds = UB surface, the
///     caller's obligation).
    /// Upstream doc (lib.rs:792-814):
    ///   Retrieves the value at index `i`, without doing bounds checking.
    ///   For a safe alternative, see `get`.
    ///   # Safety
    ///   Calling this method with an out-of-bounds index is undefined behavior
    ///   even if the resulting reference is not used.
    pub exec fn get_unchecked(&self, i: usize) -> (r: bool)
        requires
            inv(self),
            i < self.nbits,
        ensures
            r == bit_at(self.storage@, self.nbits, i),
    {
        let w = i / 32;
        let b = i % 32;
        proof {
            int_div_bound_lemma(i, self.nbits);
        }
        let block = self.storage[w];
        (block & (1u32 << b)) != 0u32
    }

    /// Origin Rust: pub fn set(&mut self, i: usize, x: bool) {...} (lib.rs:895-912)
///     doc "# Panics: Panics if i is out of bounds" -> requires i < nbits.
    /// Upstream doc (lib.rs:879-893):
    ///   Sets the value of a bit at an index `i`.
    ///   # Panics
    ///   Panics if `i` is out of bounds.
    pub exec fn set(&mut self, i: usize, x: bool)
        requires
            len_inv(old(self)),
            trailing_zero(old(self)),
            i < old(self).nbits,
        ensures
            len_inv(final(self)),
            trailing_zero(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize|
                w2 < final(self).storage@.len() && w2 != i / 32 ==>
                final(self).storage@[w2 as int] == old(self).storage@[w2 as int],
            x ==> final(self).storage@[(i / 32) as int]
                == old(self).storage@[(i / 32) as int] | (1u32 << (i % 32)),
            !x ==> final(self).storage@[(i / 32) as int]
                == old(self).storage@[(i / 32) as int] & !(1u32 << (i % 32)),
            forall|j: usize|
                j < final(self).nbits && j != i ==> bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            bit_at(final(self).storage@, final(self).nbits, i) == x,
    {
        let w = i / 32;
        let b = i % 32;
        let flag = 1u32 << b;
        /* Origin Rust: let flag = B::one() << b; (u32 materialized) */
        let old_val = self.storage[w];
        let val = if x { old_val | flag } else { old_val & !flag };
        self.storage.set(w, val);
        proof {
            let b_u = b as u32;
            assert(b_u <= 31u32) by {
                assert(i % 32 < 32);
            }
            assert(flag == 1u32 << b_u);
            assert(flag == 1u32 << (i % 32));
            if self.nbits % 32 > 0 {
                let e = self.nbits % 32;
                let e_u = e as u32;
                let blocks = self.storage@.len();
                let last: usize = (blocks - 1) as usize;
                if w == last {
                    assert(old_val == old(self).storage@[(blocks - 1) as int]);
                    assert(old_val < (1u32 << e_u)) by {
                        assert(trailing_zero(old(self)));
                        assert(blocks_for_bits(final(self).nbits) == blocks);
                        assert(old_val < (1u32 << e));
                        assert(1u32 << e == 1u32 << (e as u32));
                    }
                    if x {
                        lemma_flag_below_mask(final(self).nbits, b);
                        assert((1u32 << b) < (1u32 << e));
                        assert((1u32 << b_u) < (1u32 << e_u)) by {
                            assert(1u32 << b_u == 1u32 << b);
                            assert(1u32 << e_u == 1u32 << e);
                            assert((1u32 << b) < (1u32 << e));
                        }
                        assert((old_val | flag) < (1u32 << e_u)) by (bit_vector)
                            requires
                                flag == 1u32 << b_u,
                                old_val < (1u32 << e_u),
                                (1u32 << b_u) < (1u32 << e_u),
                                e_u <= 31u32,
                        ;
                        assert(trailing_zero(final(self))) by {
                            assert(final(self).storage@[(blocks - 1) as int] < (1u32 << (final(self).nbits % 32)));
                        }
                    } else {
                        lemma_and_decreases(old_val, flag);
                        assert((old_val & !flag) <= old_val);
                        assert((old_val & !flag) < (1u32 << e_u)) by (bit_vector)
                            requires
                                (old_val & !flag) <= old_val,
                                old_val < (1u32 << e_u),
                                e_u <= 31u32,
                        ;
                        assert(trailing_zero(final(self))) by {
                            assert(final(self).storage@[(blocks - 1) as int] < (1u32 << (final(self).nbits % 32)));
                        }
                    }
                }
            }
            // bit semantics: j != i keeps its value, at j == i X is placed
            assert forall|j: usize|
                j < final(self).nbits && j != i implies bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j) by {
                let bj = j % 32;
                assert(bj < 32);
                if j / 32 == i / 32 {
                    lemma_other_bit_untouched(old_val, b, bj, x);
                    assert(final(self).storage@[(j / 32) as int] == val);
                    if x {
                        assert(val == old_val | (1u32 << b)) by {
                            assert(val == old_val | flag);
                            assert(flag == 1u32 << b);
                        }
                    } else {
                        assert(val == old_val & !(1u32 << b)) by {
                            assert(val == old_val & !flag);
                            assert(flag == 1u32 << b);
                        }
                    }
                } else {
                    assert(final(self).storage@[(j / 32) as int] == old(self).storage@[(j / 32) as int]);
                }
            }
            if x {
                assert((val & (1u32 << b)) != 0u32) by (bit_vector)
                    requires
                        val == old_val | (1u32 << b),
                        b <= 31usize,
                ;
            } else {
                assert((val & (1u32 << b)) == 0u32) by (bit_vector)
                    requires
                        val == old_val & !(1u32 << b),
                        b <= 31usize,
                ;
            }
            assert(bit_at(final(self).storage@, final(self).nbits, i) == x) by {
                assert(final(self).storage@[(i / 32) as int] == val);
                assert(bit_at(final(self).storage@, final(self).nbits, i)
                    == ((final(self).storage@[(i / 32) as int] & (1u32 << b)) != 0u32));
            }
        }
    }

    /// Origin Rust: pub fn push(&mut self, elem: bool) {...} (lib.rs:1797-1804)
///     checked_add(1).expect("Capacity overflow") (lib.rs:1802) -> requires
///     old(self).nbits < usize::MAX (# Panics: Capacity overflow = the
///     caller's obligation).
    /// Upstream doc (lib.rs:1784-1795):
    ///   Pushes a `bool` onto the end.
    pub exec fn push(&mut self, elem: bool)
        requires
            inv(old(self)),
            old(self).nbits < usize::MAX,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits + 1,
            forall|j: usize|
                j < old(self).nbits ==> bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            bit_at(final(self).storage@, final(self).nbits, (final(self).nbits - 1) as usize) == elem,
    {
        if self.nbits % 32 == 0 {
            self.storage.push(0u32);
        }
        let insert_pos = self.nbits;
        self.nbits = self.nbits + 1;
        proof {
            // establish set's call-site preconditions: len_inv + trailing_zero
            // (insert_pos is in the tail block)
            assert(self.nbits == old(self).nbits + 1);
            assert(insert_pos == old(self).nbits);
            if old(self).nbits % 32 == 0 {
                let e_new = self.nbits % 32;
                assert(e_new == 1);
                let last: usize = (self.storage@.len() - 1) as usize;
                assert(self.storage@.len() == old(self).storage@.len() + 1);
                assert(last == old(self).storage@.len() as usize);
                assert(insert_pos / 32 == last) by {
                    int_div_bound_lemma(insert_pos, self.nbits);
                    assert(blocks_for_bits(old(self).nbits) == old(self).storage@.len());
                    assert(old(self).nbits / 32 == last);
                    assert(blocks_for_bits(self.nbits) == self.storage@.len());
                    assert(old(self).nbits % 32 == 0);
                }
                let le = self.storage@[last as int];
                assert(le == 0u32) by {
                    assert(self.storage@ == old(self).storage@.push(0u32));
                }
                assert(le < (1u32 << e_new)) by (bit_vector)
                    requires
                        le == 0u32,
                        e_new == 1usize,
                ;
                assert(len_inv(self));
                assert(trailing_zero(self));
            } else {
                let e_old = old(self).nbits % 32;
                assert(0 < e_old < 32);
                assert(insert_pos % 32 == e_old);
                assert(self.storage@.len() == old(self).storage@.len());
                assert(insert_pos / 32 == (self.storage@.len() - 1) as usize) by {
                    int_div_bound_lemma(insert_pos, self.nbits);
                    assert(self.storage@.len() == blocks_for_bits(old(self).nbits));
                    assert(old(self).nbits == 32 * (old(self).nbits / 32) + e_old);
                    assert(blocks_for_bits(self.nbits) == blocks_for_bits(old(self).nbits)) by {
                        assert(self.nbits == 32 * (self.nbits / 32) + (self.nbits % 32));
                        assert(self.nbits % 32 == e_old + 1 || self.nbits % 32 == 0);
                    }
                }
                let le = self.storage@[(self.storage@.len() - 1) as int];
                assert(le == old(self).storage@[(old(self).storage@.len() - 1) as int]);
                if self.nbits % 32 > 0 {
                    let e_new = self.nbits % 32;
                    assert(e_new == e_old + 1);
                    assert(e_old <= 30) by {
                        assert(e_new <= 31) by {
                            assert(self.nbits % 32 < 32);
                        }
                    }
                    assert(le < (1u32 << e_old)) by {
                        assert(trailing_zero(old(self)));
                        assert(blocks_for_bits(old(self).nbits) == self.storage@.len());
                    }
                    lemma_pow_mono(e_old);
                    assert(le < (1u32 << e_new));
                    assert(trailing_zero(self)) by {
                        assert(self.storage@[(blocks_for_bits(self.nbits) - 1) as int]
                            == self.storage@[(self.storage@.len() - 1) as int]);
                        assert(self.storage@.len() == blocks_for_bits(self.nbits));
                    }
                } else {
                    assert(trailing_zero(self));
                }
                assert(len_inv(self));
            }
        }
        self.set(insert_pos, elem);
    }

    /// Origin Rust: pub fn pop(&mut self) -> Option<bool> {...} (lib.rs:1765-1782)
    /// Upstream doc (lib.rs:1752-1763):
    ///   Removes the last bit from the `BitVec`, and returns it. Returns `None` if the `BitVec` is empty.
    pub exec fn pop(&mut self) -> (r: Option<bool>)
        requires
            inv(old(self)),
        ensures
            inv(final(self)),
            old(self).nbits > 0 ==> final(self).nbits == old(self).nbits - 1
                && r == Some(bit_at(old(self).storage@, old(self).nbits, (old(self).nbits - 1) as usize)),
            old(self).nbits == 0 ==> final(self).nbits == 0 && r is None,
            forall|j: usize|
                j < final(self).nbits ==> bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
    {
        if self.is_empty() {
            return None;
        }
        let i = (self.nbits - 1) as usize;
        /* Origin Rust: let ret = self[i]; (Index<i> goes through get(i).expect, same-semantics expansion) */
        let ret = self.get(i).unwrap();
        self.set(i, false);
        self.nbits = i;
        if self.nbits % 32 == 0 {
            self.storage.pop();
        }
        proof {
            // tail-block value closure (set's element clause -> the new tail-block value)
            let e_old = old(self).nbits % 32;
            assert(0 <= e_old < 32);
            assert(i == old(self).nbits - 1);
            let old_last = old(self).storage@[(blocks_for_bits(old(self).nbits) - 1) as int];
            assert(len_inv(old(self)));
            if e_old == 1 {
            // i = 32k; here n%32==0, so a block pop happens; trailing is trivially true
                assert(self.nbits % 32 == 0) by {
                    assert(old(self).nbits == 32 * (old(self).nbits / 32) + 1);
                    assert(self.nbits == 32 * (self.nbits / 32)) by {
                        assert(self.nbits == old(self).nbits - 1);
                    }
                    assert(i == 32 * (i / 32));
                }
                assert(self.storage@.len() == blocks_for_bits(old(self).nbits) - 1);
                assert(blocks_for_bits(self.nbits) == self.storage@.len()) by {
                    assert(blocks_for_bits(self.nbits) == self.nbits / 32);
                }
                assert(trailing_zero(self));
                assert(len_inv(self));
            } else {
                // tail block not popped; storage length unchanged
                assert(self.storage@.len() == old(self).storage@.len());
                assert(blocks_for_bits(self.nbits) == blocks_for_bits(old(self).nbits)) by {
                    assert(self.nbits == 32 * (self.nbits / 32) + (self.nbits % 32));
                    assert(old(self).nbits == 32 * (old(self).nbits / 32) + e_old);
                    assert(self.nbits == old(self).nbits - 1);
                    assert(self.storage@.len() == blocks_for_bits(old(self).nbits));
                }
                assert(self.storage@.len() >= 1) by {
                    assert(old(self).nbits >= 1);
                    assert(blocks_for_bits(old(self).nbits) >= 1);
                }
                let last: usize = (self.storage@.len() - 1) as usize;
                assert(i / 32 == last) by {
                    if e_old == 0 {
                        assert(old(self).nbits == 32 * (old(self).nbits / 32));
                        assert(i == 32 * (old(self).nbits / 32) - 1);
                        assert(i % 32 == 31);
                        assert(i / 32 == old(self).nbits / 32 - 1) by {
                            assert(i == 32 * (i / 32) + i % 32);
                        }
                    } else {
                        assert(i % 32 == e_old - 1) by {
                            assert(old(self).nbits == 32 * (old(self).nbits / 32) + e_old);
                            assert(i == 32 * (i / 32) + i % 32);
                            assert(i / 32 == old(self).nbits / 32);
                        }
                    }
                    assert(self.storage@.len() == blocks_for_bits(old(self).nbits));
                    assert(last == (blocks_for_bits(old(self).nbits) - 1) as usize);
                }
                assert(self.storage@.len() == blocks_for_bits(self.nbits));
                if e_old == 0 {
                    assert(i % 32 == 31);
                    // for e_old==0 the old trailing constraint is trivially true;
                    // clearing bit 31 gives < 2^31
                    assert((old_last & !(1u32 << 31u32)) < (1u32 << 31u32)) by (bit_vector);
                    assert(final(self).storage@[(i / 32) as int] == old_last & !(1u32 << 31))
                        by {
                        assert(final(self).storage@[(i / 32) as int]
                            == old(self).storage@[(i / 32) as int] & !(1u32 << (i % 32)));
                        assert(old(self).storage@[(i / 32) as int] == old_last) by {
                            assert(i / 32 == (blocks_for_bits(old(self).nbits) - 1) as usize);
                        }
                    }
                    assert(trailing_zero(self)) by {
                        assert(self.nbits % 32 == 31);
                        assert(self.storage@[(blocks_for_bits(self.nbits) - 1) as int]
                            == final(self).storage@[(i / 32) as int]);
                    }
                } else {
                    let e_new = self.nbits % 32;
                    assert(e_new == e_old - 1) by {
                        assert(self.nbits % 32 == e_old - 1) by {
                            assert(old(self).nbits == 32 * (old(self).nbits / 32) + e_old);
                            assert(i == 32 * (i / 32) + i % 32);
                            assert(i / 32 == old(self).nbits / 32);
                            assert(i % 32 == e_old - 1);
                            assert(self.nbits == 32 * (self.nbits / 32) + (self.nbits % 32));
                        }
                    }
                    assert(old_last < (1u32 << e_old)) by {
                        assert(trailing_zero(old(self)));
                    }
                    assert((e_old - 1) as usize + 1 == e_old);
                    lemma_clear_top_below(old_last, (e_old - 1) as usize);
                    assert(final(self).storage@[(i / 32) as int] == old_last & !(1u32 << (e_old - 1)))
                        by {
                        assert(final(self).storage@[(i / 32) as int]
                            == old(self).storage@[(i / 32) as int] & !(1u32 << (i % 32)));
                        assert(i % 32 == e_old - 1);
                        assert(old(self).storage@[(i / 32) as int] == old_last) by {
                            assert(i / 32 == (blocks_for_bits(old(self).nbits) - 1) as usize);
                        }
                    }
                    assert(final(self).storage@[(i / 32) as int] < (1u32 << e_new)) by {
                        assert((1u32 << (e_old - 1)) == (1u32 << e_new)) by {
                            assert((e_old - 1) as usize == e_new) by {
                                assert(e_new == e_old - 1);
                            }
                        }
                        assert(1u32 << (e_old - 1) == 1u32 << ((e_old - 1) as usize));
                        assert(1u32 << e_new == 1u32 << (e_new as usize));
                    }
                    assert(trailing_zero(self)) by {
                        assert(self.nbits % 32 == e_new);
                        assert(self.storage@[(blocks_for_bits(self.nbits) - 1) as int]
                            == final(self).storage@[(i / 32) as int]);
                    }
                }
                assert(len_inv(self)) by {
                    assert(self.storage@.len() == blocks_for_bits(self.nbits));
                }
            }
        }
        Some(ret)
    }

    /// Origin Rust: fn fix_last_block(&mut self) {...} (lib.rs:721-725)
///     last_block_mut_with_mask inlined (private helper; with e = len%32 >
///     0, storage[len-1] &= (1<<e)-1).
    /// Upstream doc (lib.rs:719-720):
    ///   An operation might screw up the unused bits in the last block of the
    ///   `BitVec`. As per (3), it's assumed to be all 0s. This method fixes it up.
    pub exec fn fix_last_block(&mut self)
        requires
            len_inv(old(self)),
        ensures
            len_inv(final(self)),
            trailing_zero(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize|
                w2 < final(self).storage@.len() && (final(self).nbits % 32 == 0
                    || w2 != (final(self).storage@.len() - 1) as usize) ==>
                final(self).storage@[w2 as int] == old(self).storage@[w2 as int],
            final(self).nbits % 32 > 0 ==> final(self).storage@[(final(self).storage@.len() - 1) as int]
                == old(self).storage@[(old(self).storage@.len() - 1) as int]
                    & ((1u32 << (final(self).nbits % 32)) - 1u32) as u32,
            forall|j: usize|
                j < old(self).nbits ==> bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
    {
        let extra_bits = self.nbits % 32;
        if extra_bits > 0 {
            proof {
                assert(extra_bits <= 31) by {
                    assert(extra_bits < 32);
                }
                assert((1u32 << extra_bits) >= 2u32) by (bit_vector)
                    requires
                        extra_bits >= 1usize,
                        extra_bits <= 31usize,
                ;
            }
            let mask = ((1u32 << extra_bits) - 1u32) as u32;
            /* Origin Rust: let mask = (B::one() << extra_bits) - B::one();
               (u32 materialized) */
            let storage_len = self.storage.len();
            let cur = self.storage[(storage_len - 1) as usize];
            self.storage.set((storage_len - 1) as usize, cur & mask);
            proof {
                assert(self.storage@[(self.storage@.len() - 1) as int] == cur & mask);
                assert((cur & mask) < (1u32 << (extra_bits as u32))) by (bit_vector)
                    requires
                        (extra_bits as u32) <= 31u32,
                        mask == (1u32 << (extra_bits as u32)) - 1u32,
                ;
                assert(trailing_zero(final(self))) by {
                    assert(final(self).storage@[(blocks_for_bits(final(self).nbits) - 1) as int]
                        < (1u32 << (final(self).nbits % 32)));
                }
                assert forall|j: usize|
                    j < old(self).nbits implies bit_at(final(self).storage@, final(self).nbits, j)
                        == bit_at(old(self).storage@, old(self).nbits, j) by {
                    let bj = j % 32;
                    assert(bj < 32);
                    if j / 32 == (self.storage@.len() - 1) as usize {
                        assert(j < self.nbits);
                        assert(bj < extra_bits) by {
                            assert(j == 32 * (j / 32) + j % 32);
                            assert(j >= 32 * ((self.storage@.len() - 1) as int));
                            assert(old(self).nbits == 32 * ((self.storage@.len() - 1) as int)
                                + extra_bits);
                        }
                        assert(mask & (1u32 << bj) == (1u32 << bj)) by (bit_vector)
                            requires
                                mask == (1u32 << (extra_bits as u32)) - 1u32,
                                (bj as u32) < (extra_bits as u32),
                                (extra_bits as u32) <= 31u32,
                        ;
                        assert((cur & mask) & (1u32 << bj) == cur & (1u32 << bj)) by (bit_vector)
                            requires
                                mask & (1u32 << bj) == (1u32 << bj),
                        ;
                    }
                }
            }
        } else {
            proof {
                assert(trailing_zero(final(self))) by {
                    assert(final(self).nbits % 32 == 0);
                }
            }
        }
    }

    /// Origin Rust: fn fix_last_block_with_ones(&mut self) (lib.rs:727-733)
    ///     { if let Some((last_block, used_bits)) = self.last_block_mut_with_mask() {
    ///         *last_block |= !used_bits; } }
/// Upstream comment: change detection for nand/nor/xnor is easiest to
///     implement when the tail block's unused bits are all 1s.
///     last_block_mut_with_mask inlined (private helper; with e = len%32 >
///     0, storage[len-1] |= !mask); in a spec context `!` is materialized
///     as XOR all-ones (negate precedent).
    /// Upstream doc (lib.rs:727-728):
    ///   Operations such as change detection for xnor, nor and nand are easiest
    ///   to implement when unused bits are all set to 1s.
    pub exec fn fix_last_block_with_ones(&mut self)
        requires
            len_inv(old(self)),
        ensures
            len_inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize| w2 < final(self).storage@.len() ==>
                final(self).storage@[w2 as int] == with_ones_input(old(self), w2),
            forall|j: usize| j < old(self).nbits ==>
                bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
    {
        let extra_bits = self.nbits % 32;
        if extra_bits > 0 {
            proof {
                assert(extra_bits <= 31) by {
                    assert(extra_bits < 32);
                }
                assert((1u32 << extra_bits) >= 2u32) by (bit_vector)
                    requires
                        extra_bits >= 1usize,
                        extra_bits <= 31usize,
                ;
            }
            let mask = ((1u32 << extra_bits) - 1u32) as u32;
            /* Origin Rust: *last_block |= !used_bits; (`!` in a spec context
               is materialized as XOR all-ones) */
            let storage_len = self.storage.len();
            let cur = self.storage[(storage_len - 1) as usize];
            self.storage.set((storage_len - 1) as usize, cur | (4294967295u32 ^ mask));
            proof {
                assert(self.storage@ == old(self).storage@.update(
                    (storage_len - 1) as int,
                    cur | (4294967295u32 ^ mask),
                ));
                assert forall|w2: usize| w2 < self.storage@.len() ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2) by {
                    if w2 == (storage_len - 1) as usize {
                        assert(with_ones_input(old(self), w2)
                            == cur | (4294967295u32 ^ mask));
                    } else {
                        assert(with_ones_input(old(self), w2)
                            == old(self).storage@[w2 as int]);
                    }
                }
                assert forall|j: usize| j < self.nbits implies
                    bit_at(self.storage@, self.nbits, j)
                        == bit_at(old(self).storage@, self.nbits, j) by {
                    if j / 32 == (storage_len - 1) as usize {
                        lemma_with_ones_bit(old(self).storage@[(j / 32) as int],
                            self.nbits % 32, j % 32);
                    }
                }
            }
        } else {
            proof {
                assert(forall|w2: usize| w2 < self.storage@.len() ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2)) by {
                    assert forall|w2: usize| w2 < self.storage@.len() implies
                        self.storage@[w2 as int] == with_ones_input(old(self), w2) by { }
                }
            }
        }
    }
/// doc "# Invariants" (lib.rs:1840-1846): the all()/none() promises after
///     fill(bit).
    /// Upstream doc (lib.rs:1838-1846):
    ///   Assigns all bits in this vector to the given boolean value.
    ///   # Invariants
    ///   - After a call to `.fill(true)`, the result of [`all`] is `true`.
    ///   - After a call to `.fill(false)`, the result of [`none`] is `true`.
pub exec fn fill(&mut self, bit: bool)
    requires
        inv(old(self)),
    ensures
        inv(final(self)),
        final(self).nbits == old(self).nbits,
        final(self).storage@.len() == old(self).storage@.len(),
        bit ==> all_spec(final(self)),
        bit ==> (forall|j: usize|
            j < final(self).nbits ==> bit_at(final(self).storage@, final(self).nbits, j)),
        bit ==> (forall|j: usize| j < final(self).storage@.len() - 1 ==> final(self).storage@[j as int] == 4294967295u32),
        !bit ==> none_spec(final(self)),
        !bit ==> (forall|j: usize| j < final(self).nbits ==> !bit_at(final(self).storage@, final(self).nbits, j)),
{
    let fill_value: u32 = if bit { 4294967295u32 } else { 0u32 };
    /* Origin Rust: let block = if bit { !B::zero() } else { B::zero() };
       (`!` materialized in the spec context) */
    let len = self.storage.len();
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            self.storage@.len() == len,
            forall|j: usize| j < len && j < k ==> self.storage@[j as int] == fill_value,
            self.nbits == old(self).nbits,
            forall|j: usize| j >= k && j < len ==> self.storage@[j as int] == old(self).storage@[j as int],
        decreases
            len - k,
    {
        self.storage.set(k, fill_value);
        k += 1;
    }
    proof {
        if bit {
            assert(forall|j: usize| j < len ==> self.storage@[j as int] == 4294967295u32) by {
                assert forall|j: usize| j < len implies self.storage@[j as int] == fill_value by {
                    assert(len == old(self).storage@.len() == self.storage@.len());
                }
            }
        } else {
            assert(none_spec(self)) by {
                assert forall|j: usize| j < len implies self.storage@[j as int] == fill_value by {
                }
            }
        }
    }
    if bit {
        let before_fix_last: u32 = if len > 0 {
            proof { assert(len >= 1); }
            self.storage[(len - 1) as usize]
        } else {
            0u32
        };
        proof {
            let len2 = self.storage@.len();
            assert(len2 == len);
            if len2 > 0 {
                assert forall|j: usize| j < len2 implies self.storage@[j as int] == 4294967295u32 by {
                }
            }
        }
        self.fix_last_block();
        proof {
            let len2 = self.storage@.len();
            assert(len2 == len);
            if len2 > 0 {
                let e = self.nbits % 32;
                assert(forall|j: usize| j < len2 - 1 ==> self.storage@[j as int] == 4294967295u32) by {
                    assert(len2 >= 1);
                    assert forall|j: usize|
                        j < len2 - 1 implies self.storage@[j as int] == 4294967295u32 by {
                    }
                }
                if e == 0 {
                    assert(trailing_mask(self.nbits) == 4294967295u32);
                } else {
                    assert(e >= 1);
                    assert(self.storage@[(len2 - 1) as int] == ((1u32 << e) - 1u32) as u32) by {
                        assert((self.nbits % 32) == e);
                        assert(4294967295u32 & ((1u32 << e) - 1u32) as u32
                            == ((1u32 << e) - 1u32) as u32) by (bit_vector)
                            requires
                                e <= 31usize,
                        ;
                    }
                }
            }
        }
        proof {
            lemma_all_spec_bits(self);
        }
    } else {
        proof {
            assert(none_spec(self)) by {
                assert forall|j: usize| j < len implies self.storage@[j as int] == 0u32 by {
                }
            }
            assert(forall|j: usize| j < old(self).nbits ==> !bit_at(self.storage@, self.nbits, j)) by {
                lemma_none_spec_bits(self);
            }
        }
    }
}

/// Origin Rust: pub fn set_all(&mut self) {...} (lib.rs:930-936, deprecated <-> fill(true))
    /// Upstream doc (lib.rs:914-927):
    ///   Sets all bits to 1.
pub exec fn set_all(&mut self)
    requires
        inv(old(self)),
    ensures
        inv(final(self)),
        all_spec(final(self)),
        final(self).nbits == old(self).nbits,
        final(self).storage@.len() == old(self).storage@.len(),
        forall|j: usize|
            j < old(self).nbits ==> bit_at(final(self).storage@, final(self).nbits, j),
{
    self.fill(true);
}

/// Origin Rust: pub fn negate(&mut self) {...} (lib.rs:953-959)
    /// Upstream doc (lib.rs:938-951):
    ///   Flips all bits.
pub exec fn negate(&mut self)
    requires
        inv(old(self)),
    ensures
        inv(final(self)),
        final(self).nbits == old(self).nbits,
        final(self).storage@.len() == old(self).storage@.len(),
        forall|j: usize|
            j < old(self).nbits ==> bit_at(final(self).storage@, final(self).nbits, j)
                != bit_at(old(self).storage@, old(self).nbits, j),
{
    let len = self.storage.len();
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            self.storage@.len() == len,
            old(self).storage@.len() == len,
            self.nbits == old(self).nbits,
            forall|j: usize| j < k ==> self.storage@[j as int]
                == old(self).storage@[j as int] ^ 4294967295u32,
            forall|j: usize| j >= k && j < len ==> self.storage@[j as int] == old(self).storage@[j as int],
        decreases
            len - k,
    {
        let w = self.storage[k];
        /* Origin Rust: *w = !*w; (`!` is not expressible in a spec context,
           machine equivalent x ^ 0xFFFFFFFF) */
        self.storage.set(k, w ^ 4294967295u32);
        k += 1;
    }
    proof {
        assert(forall|j: usize| j < len ==> self.storage@[j as int]
            == old(self).storage@[j as int] ^ 4294967295u32) by {
            assert forall|j: usize| j < len implies self.storage@[j as int]
                == old(self).storage@[j as int] ^ 4294967295u32 by {
            }
        }
    }
    let pre_last: u32 = if len > 0 {
        proof { assert(len >= 1); }
        self.storage[(len - 1) as usize]
    } else {
        0u32
    };
    self.fix_last_block();
    proof {
        let len2 = self.storage@.len();
        let e = self.nbits % 32;
        assert(len2 == len);
        assert(len_inv(self));
        assert(self.nbits == 32 * ((self.nbits as int) / 32) + e);
        if len2 >= 1 {
            if e > 0 {
                assert(len2 == ((self.nbits as int) / 32 + 1) as usize);
                assert(self.nbits == 32 * ((len2 - 1) as int) + e);
                assert(pre_last == old(self).storage@[(len2 - 1) as int] ^ 4294967295u32);
                assert(self.storage@[(len2 - 1) as int]
                    == (old(self).storage@[(len2 - 1) as int] ^ 4294967295u32)
                        & ((1u32 << e) - 1u32) as u32);
            } else {
                assert(len2 == (((self.nbits as int) / 32) as usize));
                assert(pre_last == old(self).storage@[(len2 - 1) as int] ^ 4294967295u32);
                assert(self.storage@[(len2 - 1) as int]
                    == old(self).storage@[(len2 - 1) as int] ^ 4294967295u32);
            }
        }
        assert forall|j: usize|
            j < old(self).nbits implies bit_at(self.storage@, self.nbits, j)
                != bit_at(old(self).storage@, self.nbits, j) by {
            let k = j / 32;
            let old_block = old(self).storage@[k as int];
            if k < len2 - 1 {
                assert(self.storage@[k as int] == old_block ^ 4294967295u32);
                lemma_neg_bit(j % 32, old_block);
            } else {
                assert(k == len2 - 1);
                if e == 0 {
                    lemma_neg_bit(j % 32, old_block);
                } else {
                    assert(j % 32 < e) by {
                        assert(j == 32 * (j / 32) + j % 32);
                    }
                    let m: u32 = ((1u32 << e) - 1u32) as u32;
                    lemma_neg_bit_masked(j % 32, e, old_block, self.storage@[k as int], m);
                }
            }
        }
    }
}

/// Origin Rust: pub fn clear(&mut self) {...} (lib.rs:1831-1836, deprecated <-> fill(false))
    /// Upstream doc (lib.rs:1828-1828):
    ///   Clears all bits in this vector.
pub exec fn clear(&mut self)
    requires
        inv(old(self)),
    ensures
        inv(final(self)),
        none_spec(final(self)),
        final(self).nbits == old(self).nbits,
        final(self).storage@.len() == old(self).storage@.len(),
        forall|j: usize| j < old(self).nbits ==> !bit_at(final(self).storage@, final(self).nbits, j),
{
    self.fill(false);
}

/// Origin Rust: pub fn none(&self) -> bool {...} (lib.rs:1503-1505)
    /// Upstream doc (lib.rs:1489-1501):
    ///   Returns `true` if all bits are 0.
pub exec fn none(&self) -> (r: bool)
    requires
        len_inv(self),
    ensures
        r == none_spec(self),
        r ==> (forall|j: usize| j < self.nbits ==> !bit_at(self.storage@, self.nbits, j)),
{
    let len = self.storage.len();
    let mut k: usize = 0;
    let mut res = true;
    /* Nonzero-block witness: when res=false, nz records the index of the
       first `w != 0` (probeB). */
    let mut nz: usize = 0;
    while k < len
        invariant
            k <= len,
            self.storage@.len() == len,
            res == (forall|j: usize| j < k ==> self.storage@[j as int] == 0u32),
            !res ==> (nz < k && self.storage@[nz as int] != 0u32),
        decreases
            len - k,
    {
        /* Origin Rust: blocks().all(|w| w == B::zero()) (all expanded to a
         * full index loop, identical semantics -- the upstream short-circuit
         * only affects constant cost, not the result) */
        let w = self.storage[k];
        if w != 0u32 {
            res = false;
            nz = k;
        }
        k += 1;
    }
    proof {
        assert(k == len);
        if res {
            assert(forall|j: usize| j < len ==> self.storage@[j as int] == 0u32) by {
                assert forall|j: usize| j < len implies self.storage@[j as int] == 0u32 by {
                }
            }
            assert(none_spec(self)) by {
                assert(self.storage@.len() == len);
            }
            assert(forall|j: usize| j < self.nbits ==> !bit_at(self.storage@, self.nbits, j)) by {
                assert forall|j: usize| j < self.nbits implies !bit_at(self.storage@, self.nbits, j) by {
                    let k2 = j / 32;
                    assert(k2 < len) by {
                        int_div_bound_lemma(j, self.nbits);
                        assert(len_inv(self));
                    }
                    assert(self.storage@[k2 as int] == 0u32);
                    assert(0u32 & (1u32 << (j % 32)) == 0u32) by (bit_vector)
                        requires
                            j % 32 <= 31usize,
                    ;
                }
            }
        } else {
            assert(!none_spec(self)) by {
                assert(nz < self.storage@.len());
                assert(self.storage@[nz as int] != 0u32);
            }
        }
    }
    res
}

/// Origin Rust: pub fn any(&self) -> bool { !self.none() } (lib.rs:1521-1523)
    /// Upstream doc (lib.rs:1507-1519):
    ///   Returns `true` if any bit is 1.
pub exec fn any(&self) -> (r: bool)
    requires
        len_inv(self),
    ensures
        r == !none_spec(self),
{
    !self.none()
}

/// Origin Rust: pub fn all(&self) -> bool {...} (lib.rs:1271-1281)
///     blocks().all(...) folded into an index loop + bool ok; the
///     tmp/last_word semantics are preserved line by line.
    /// Upstream doc (lib.rs:1257-1269):
    ///   Returns `true` if all bits are 1.
pub exec fn all(&self) -> (r: bool)
    requires
        inv(self),
    ensures
        r == all_spec(self),
        r ==> (forall|j: usize| j < self.nbits ==> bit_at(self.storage@, self.nbits, j)),
{
    let len = self.storage.len();
    let n = self.nbits;
    let mut last_word: u32 = 4294967295u32;
    /* Origin Rust: let mut last_word = !B::zero(); (`!` materialized in the
       spec context) */
    let mut ok = true;
    /* Witness of a non-all-ones block: when ok=false, bad records the index
       of the first `tmp != !0` (probeB). */
    let mut bad: usize = 0;
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            self.storage@.len() == len,
            ok ==> (forall|j: usize| j + 1 < k ==> self.storage@[j as int] == 4294967295u32),
            !ok ==> (bad < k - 1 && self.storage@[bad as int] != 4294967295u32),
            (k == 0 ==> last_word == 4294967295u32)
                && (k >= 1 ==> last_word == self.storage@[(k - 1) as int]),
        decreases
            len - k,
    {
        let tmp = last_word;
        last_word = self.storage[k];
        /* Origin Rust: ok = ok && (tmp == !B::zero()); (spec-context
           materialization + witness index) */
        if tmp != 4294967295u32 {
            ok = false;
            bad = k - 1;
        }
        k += 1;
    }
    /* Origin Rust: self.blocks().all(|elem| { let tmp = last_word; last_word = elem;
        tmp == !B::zero() }) && (last_word == mask_for_bits(self.nbits)) */
    let mask = mask_for_bits_exec(n);
    proof { assert(mask == trailing_mask(n)); }
    let ok2 = ok && (last_word == mask);
    proof {
        assert(k == len);
        if len == 0 {
            assert(all_spec(self));
            assert(ok2);
        } else {
            if ok {
                assert(forall|j: usize| j < len - 1 ==> self.storage@[j as int] == 4294967295u32);
                assert(last_word == self.storage@[(len - 1) as int]);
                assert(all_spec(self) == (last_word == mask));
                if last_word == mask {
                    assert(all_spec(self));
                    assert(ok2 == all_spec(self));
                } else {
                    assert(!ok2);
                    assert(!all_spec(self));
                }
            } else {
                assert(!ok);
                assert(k >= 1);
                assert(bad + 1 < k);
                assert(bad < len);
                assert(self.storage@[bad as int] != 4294967295u32);
                assert(!all_spec(self));
                assert(ok2 == all_spec(self));
            }
        }
    }
    ok = ok2;
    proof {
        if ok {
            /* r == all_spec(self) and all_spec => bit-wise (probeA) */
            assert forall|j: usize| j < self.nbits implies bit_at(self.storage@, self.nbits, j) by {
                lemma_bit_of_all(self, j);
            }
        }
    }
    ok
}

    // -----------------------------------------------------------------------
//    process family (Origin Rust: lib.rs:643-656 fn process<F>, a closure
//    parameter and a zip inner loop). The closure F: FnMut(B,B)->B is
//    outside the vstd expressive domain (probeD/p_closure4: exec closure
//    requires can be written, but its postcondition cannot be quantified),
//    so each op materializes process as an index loop; the
//    assert_eq!(self.len(), other.len()) surface (# Panics) -> requires.
    // -----------------------------------------------------------------------

    /// Upstream doc of process (lib.rs:640-642): "Applies the given
    /// operation to the blocks of self and other, and sets self to be the
    /// result. This relies on the caller not to corrupt the last word."
    /// Origin Rust: pub fn or(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.process(other, |w1, w2| w1 | w2) } (lib.rs:1048-1052)
    /// Upstream doc (lib.rs:1023-1046):
    ///   Calculates the bitwise `or` of two bitvectors.
    ///   Sets `self` to the union of `self` and `other`. Both bitvectors must be
    ///   the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different lengths.
    pub exec fn or(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize| w2 < final(self).storage@.len() ==>
                final(self).storage@[w2 as int]
                    == old(self).storage@[w2 as int] | other.storage@[w2 as int],
            forall|j: usize| j < old(self).nbits ==> bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    || bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int]
                        == old(self).storage@[w2 as int] | other.storage@[w2 as int],
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int],
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int]),
                self.nbits % 32 > 0 ==>
                    self.storage@[(len - 1) as int] < 1u32 << (self.nbits % 32),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != old(self).storage@[widx as int]),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            let w = a | b;
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                /* postcondition frame made explicit: s_head is the
                   per-iteration sequence snapshot. */
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == old(self).storage@[w2 as int] by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == old(self).storage@[k as int]);
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == old(self).storage@[w3 as int] by { }
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: when changed'!=0, widx is either this
                 * step's k (w!=a => post[k]!=old[k]) or the old witness
                 * (widx < k; set(k,..) disturbs nothing). */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        assert(self.storage@[k as int] != old(self).storage@[k as int]);
                    }
                }
                if self.nbits % 32 > 0 && k == (len - 1) as usize {
                    let e = self.nbits % 32;
                    assert(1u32 << e == 1u32 << (e as u32));
                    assert(a < (1u32 << e)) by {
                        assert(len_inv(old(self)));
                        assert(trailing_zero(old(self)));
                        assert(old(self).storage@.len() == len);
                        assert(a == old(self).storage@[k as int]);
                        assert(k as int == (blocks_for_bits(old(self).nbits) - 1) as int);
                    }
                    assert(b < (1u32 << e)) by {
                        assert(self.nbits == other.nbits) by {
                            assert(old(self).nbits == other.nbits);
                            assert(self.nbits == old(self).nbits);
                        }
                        assert(e == other.nbits % 32);
                        assert(len_inv(other));
                        assert(trailing_zero(other));
                        assert(other.storage@.len() == len);
                        assert(b == other.storage@[k as int]);
                        assert(k as int == (blocks_for_bits(other.nbits) - 1) as int);
                    }
                    lemma_or_below(a, b, e);
                }
            }
            k += 1;
        }
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == (bit_at(so, self.nbits, j) || bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                lemma_or_bit(so[kb as int], other.storage@[kb as int], j % 32);
            }
            if r {
                assert(s != so) by {
                    assert(s[widx as int] != so[widx as int]);
                }
            } else {
                assert(seq_ptwise(s, so));
                lemma_seq_eq_iff(s, so);
                assert(s == so);
            }
        }
        r
    }

    /// Origin Rust: pub fn and(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.process(other, |w1, w2| w1 & w2) } (lib.rs:1079-1083)
    /// Upstream doc (lib.rs:1054-1077):
    ///   Calculates the bitwise `and` of two bitvectors.
    ///   Sets `self` to the intersection of `self` and `other`. Both bitvectors
    ///   must be the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different lengths.
    pub exec fn and(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize| w2 < final(self).storage@.len() ==>
                final(self).storage@[w2 as int]
                    == old(self).storage@[w2 as int] & other.storage@[w2 as int],
            forall|j: usize| j < old(self).nbits ==> bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    && bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==>
                    #[trigger] self.storage@[w2 as int]
                        == old(self).storage@[w2 as int] & other.storage@[w2 as int],
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int],
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int]),
                self.nbits % 32 > 0 ==>
                    self.storage@[(len - 1) as int] < 1u32 << (self.nbits % 32),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != old(self).storage@[widx as int]),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            let w = a & b;
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                /* postcondition frame made explicit: s_head is the
                   per-iteration sequence snapshot. */
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == old(self).storage@[w2 as int] by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == old(self).storage@[k as int]);
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == old(self).storage@[w3 as int] by { }
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: when changed'!=0, widx is either this
                 * step's k (w!=a => post[k]!=old[k]) or the old witness
                 * (widx < k; set(k,..) disturbs nothing). */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        assert(self.storage@[k as int] != old(self).storage@[k as int]);
                    }
                }
                if self.nbits % 32 > 0 && k == (len - 1) as usize {
                    let e = self.nbits % 32;
                    assert(1u32 << e == 1u32 << (e as u32));
                    assert(a < (1u32 << e)) by {
                        assert(len_inv(old(self)));
                        assert(trailing_zero(old(self)));
                        assert(old(self).storage@.len() == len);
                        assert(a == old(self).storage@[k as int]);
                        assert(k as int == (blocks_for_bits(old(self).nbits) - 1) as int);
                    }
                    assert(b < (1u32 << e)) by {
                        assert(self.nbits == other.nbits) by {
                            assert(old(self).nbits == other.nbits);
                            assert(self.nbits == old(self).nbits);
                        }
                        assert(e == other.nbits % 32);
                        assert(len_inv(other));
                        assert(trailing_zero(other));
                        assert(other.storage@.len() == len);
                        assert(b == other.storage@[k as int]);
                        assert(k as int == (blocks_for_bits(other.nbits) - 1) as int);
                    }
                    lemma_and_below(a, b, e);
                }
            }
            k += 1;
        }
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == (bit_at(so, self.nbits, j) && bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                lemma_and_bit(so[kb as int], other.storage@[kb as int], j % 32);
            }
            if r {
                assert(s != so) by {
                    assert(s[widx as int] != so[widx as int]);
                }
            } else {
                assert(seq_ptwise(s, so));
                lemma_seq_eq_iff(s, so);
                assert(s == so);
            }
        }
        r
    }

    /// Origin Rust: pub fn difference(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.process(other, |w1, w2| w1 & !w2) } (lib.rs:1118-1122)
///     The process closure `!w2`: `!` is not assertable in the spec context
///     (negate precedent), materialized with the machine equivalent
///     `4294967295u32 ^ w2`; identical exec body shape.
    /// Upstream doc (lib.rs:1085-1116):
    ///   Calculates the difference between two bitvectors.
    ///   Sets each element of `self` to the value of that element minus the
    ///   element of `other` at the same index. Both bitvectors must be the same
    ///   length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different length.
    pub exec fn difference(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize| w2 < final(self).storage@.len() ==>
                final(self).storage@[w2 as int]
                    == old(self).storage@[w2 as int] & (4294967295u32 ^ other.storage@[w2 as int]),
            forall|j: usize| j < old(self).nbits ==> bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    && !bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==> self.storage@[w2 as int]
                    == old(self).storage@[w2 as int] & (4294967295u32 ^ other.storage@[w2 as int]),
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int],
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int]),
                self.nbits % 32 > 0 ==>
                    self.storage@[(len - 1) as int] < 1u32 << (self.nbits % 32),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != old(self).storage@[widx as int]),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            /* Origin Rust: process op closure = w1 & !w2 (spec-context `!`
               materialized as XOR all-ones) */
            let w = a & (4294967295u32 ^ b);
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                /* postcondition frame made explicit: s_head is the
                   per-iteration sequence snapshot. */
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == old(self).storage@[w2 as int] by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == old(self).storage@[k as int]);
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == old(self).storage@[w3 as int] by { }
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: when changed'!=0, widx is either this
                 * step's k (w!=a => post[k]!=old[k]) or the old witness
                 * (widx < k; set(k,..) disturbs nothing). */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        assert(self.storage@[k as int] != old(self).storage@[k as int]);
                    }
                }
                if self.nbits % 32 > 0 && k == (len - 1) as usize {
                    let e = self.nbits % 32;
                    assert(1u32 << e == 1u32 << (e as u32));
                    assert(a < (1u32 << e)) by {
                        assert(len_inv(old(self)));
                        assert(trailing_zero(old(self)));
                        assert(old(self).storage@.len() == len);
                        assert(a == old(self).storage@[k as int]);
                        assert(k as int == (blocks_for_bits(old(self).nbits) - 1) as int);
                    }
                    assert((a & (4294967295u32 ^ b)) < (1u32 << (e as u32))) by (bit_vector)
                        requires
                            (e as u32) <= 31u32,
                            a < (1u32 << (e as u32)),
                    ;
                }
            }
            k += 1;
        }
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == (bit_at(so, self.nbits, j) && !bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                lemma_andnot_bit(so[kb as int], other.storage@[kb as int], j % 32);
            }
            if r {
                assert(s != so) by {
                    assert(s[widx as int] != so[widx as int]);
                }
            } else {
                assert(seq_ptwise(s, so));
                lemma_seq_eq_iff(s, so);
                assert(s == so);
            }
        }
        r
    }

    /// Origin Rust: pub fn xor(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.process(other, |w1, w2| w1 ^ w2) } (lib.rs:1149-1153)
    /// Upstream doc (lib.rs:1124-1147):
    ///   Calculates the xor of two bitvectors.
    ///   Sets `self` to the xor of `self` and `other`. Both bitvectors must be
    ///   the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different length.
    pub exec fn xor(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|w2: usize| w2 < final(self).storage@.len() ==>
                final(self).storage@[w2 as int]
                    == old(self).storage@[w2 as int] ^ other.storage@[w2 as int],
            forall|j: usize| j < old(self).nbits ==> bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    != bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==>
                    #[trigger] self.storage@[w2 as int]
                        == old(self).storage@[w2 as int] ^ other.storage@[w2 as int],
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int],
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == old(self).storage@[w2 as int]),
                self.nbits % 32 > 0 ==>
                    self.storage@[(len - 1) as int] < 1u32 << (self.nbits % 32),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != old(self).storage@[widx as int]),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            let w = a ^ b;
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                /* postcondition frame made explicit: s_head is the
                   per-iteration sequence snapshot. */
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == old(self).storage@[w2 as int] by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == old(self).storage@[k as int]);
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == old(self).storage@[w3 as int] by { }
                            assert(self.storage@[w2 as int] == old(self).storage@[w2 as int]);
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: when changed'!=0, widx is either this
                 * step's k (w!=a => post[k]!=old[k]) or the old witness
                 * (widx < k; set(k,..) disturbs nothing). */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        assert(self.storage@[k as int] != old(self).storage@[k as int]);
                    }
                }
                if self.nbits % 32 > 0 && k == (len - 1) as usize {
                    let e = self.nbits % 32;
                    assert(1u32 << e == 1u32 << (e as u32));
                    assert(a < (1u32 << e)) by {
                        assert(len_inv(old(self)));
                        assert(trailing_zero(old(self)));
                        assert(old(self).storage@.len() == len);
                        assert(a == old(self).storage@[k as int]);
                        assert(k as int == (blocks_for_bits(old(self).nbits) - 1) as int);
                    }
                    assert(b < (1u32 << e)) by {
                        assert(self.nbits == other.nbits) by {
                            assert(old(self).nbits == other.nbits);
                            assert(self.nbits == old(self).nbits);
                        }
                        assert(e == other.nbits % 32);
                        assert(len_inv(other));
                        assert(trailing_zero(other));
                        assert(other.storage@.len() == len);
                        assert(b == other.storage@[k as int]);
                        assert(k as int == (blocks_for_bits(other.nbits) - 1) as int);
                    }
                    lemma_xor_below(a, b, e);
                }
            }
            k += 1;
        }
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == (bit_at(so, self.nbits, j) != bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                lemma_xor_bit(so[kb as int], other.storage@[kb as int], j % 32);
            }
            if r {
                assert(s != so) by {
                    assert(s[widx as int] != so[widx as int]);
                }
            } else {
                assert(seq_ptwise(s, so));
                lemma_seq_eq_iff(s, so);
                assert(s == so);
            }
        }
        r
    }

    /// Origin Rust: #[deprecated(since = "0.7.0")] pub fn union(&mut self, other: &Self) -> bool
    ///     { self.or(other) } (lib.rs:986-990)
    /// Upstream doc (lib.rs:961-985):
    ///   Calculates the union of two bitvectors. This acts like the bitwise `or`
    ///   function.
    ///   Sets `self` to the union of `self` and `other`. Both bitvectors must be
    ///   the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different lengths.
    pub exec fn union(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            forall|j: usize| j < old(self).nbits ==> #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    || bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        let res = self.or(other);
        proof {
            assert forall|j: usize| j < old(self).nbits implies #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    || bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                lemma_or_bit(old(self).storage@[kb as int], other.storage@[kb as int], j % 32);
            }
        }
        res
    }

    /// Origin Rust: #[deprecated(since = "0.7.0")] pub fn intersect(&mut self, other: &Self) -> bool
    ///     { self.and(other) } (lib.rs:1017-1021)
    /// Upstream doc (lib.rs:992-1016):
    ///   Calculates the intersection of two bitvectors. This acts like the
    ///   bitwise `and` function.
    ///   Sets `self` to the intersection of `self` and `other`. Both bitvectors
    ///   must be the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different lengths.
    pub exec fn intersect(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            forall|j: usize| j < old(self).nbits ==> #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    && bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        let res = self.and(other);
        proof {
            assert forall|j: usize| j < old(self).nbits implies #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    && bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                lemma_and_bit(old(self).storage@[kb as int], other.storage@[kb as int], j % 32);
            }
        }
        res
    }

    /// Origin Rust: pub fn eq_vec(&self, v: &[bool]) -> bool (lib.rs:1584-1587)
    ///     { assert_eq!(self.nbits, v.len());
    ///       self.iter().zip(v.iter().cloned()).all(|(b1, b2)| b1 == b2) }
///     iter().zip(...) is folded into an index loop (precedent: none()/all());
///     the assert_eq! length check (doc # Panics) -> requires.
    /// Upstream doc (lib.rs:1566-1582):
    ///   Compares a `BitVec` to a slice of `bool`s.
    ///   Both the `BitVec` and slice must have the same length.
    ///   # Panics
    ///   Panics if the `BitVec` and slice are of different length.
    pub exec fn eq_vec(&self, v: &[bool]) -> (r: bool)
        requires
            inv(self),
            v.len() == self.nbits,
        ensures
            r == (forall|j: usize| j < self.nbits
                ==> #[trigger] bit_at(self.storage@, self.nbits, j) == v@[j as int]),
    {
        let mut j: usize = 0;
        let mut res = true;
        /* witness bit: the first mismatching index (probeB precedent) */
        let mut widx: usize = 0;
        while j < self.nbits
            invariant
                j <= self.nbits,
                res == (forall|w2: usize| w2 < j
                    ==> bit_at(self.storage@, self.nbits, w2) == v@[w2 as int]),
                !res ==> (widx < j
                    && bit_at(self.storage@, self.nbits, widx) != v@[widx as int]),
            decreases
                self.nbits - j,
        {
            /* Origin Rust: self.iter().zip(v.iter().cloned()) pairwise
               comparison (index-loop expansion) */
            let g = self.get(j);
            let gv = g.unwrap();
            let vb = v[j];
            if gv != vb {
                proof {
                    assert(bit_at(self.storage@, self.nbits, j) != v@[j as int]);
                }
                res = false;
                widx = j;
            } else {
                proof {
                    assert(bit_at(self.storage@, self.nbits, j) == v@[j as int]);
                }
            }
            j += 1;
        }
        res
    }

    /// Origin Rust: pub fn truncate(&mut self, len: usize) (lib.rs:1604-1612)
    ///     { self.ensure_invariant();
    ///       if len < self.len() { self.nbits = len;
    ///         self.storage.truncate(blocks_for_bits::<B>(len)); self.fix_last_block(); } }
    /// Upstream doc (lib.rs:1589-1602):
    ///   Shortens a `BitVec`, dropping excess elements.
    ///   If `len` is greater than the vector's current length, this has no
    ///   effect.
    pub exec fn truncate(&mut self, len: usize)
        requires
            inv(self),
        ensures
            inv(final(self)),
            final(self).nbits == (if len < old(self).nbits {
                len
            } else {
                old(self).nbits
            }),
            final(self).storage@.len() == blocks_for_bits(final(self).nbits),
            forall|j: usize| j < final(self).nbits ==>
                bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
    {
        if len < self.len() {
            self.nbits = len;
            /* Origin Rust: self.storage.truncate(blocks_for_bits::<B>(len)); */
            let nb = blocks_for_bits_exec(len);
            proof {
                /* blocks_for_bits is monotone (given len < old nbits) ->
                   nb <= old storage length */
                assert(blocks_for_bits(len) <= blocks_for_bits(old(self).nbits)) by {
                    if len % 32 > 0 {
                        assert(1 <= len % 32);
                        if old(self).nbits % 32 > 0 {
                            assert((len as int) / 32 <= (old(self).nbits as int) / 32);
                        } else {
                            assert((len as int) / 32 < (old(self).nbits as int) / 32) by {
                                assert(len <= old(self).nbits - 1);
                                assert((len as int) / 32 <= ((old(self).nbits - 1) as int) / 32);
                                assert(old(self).nbits
                                    == 32 * ((old(self).nbits as int) / 32));
                                assert(((old(self).nbits - 1) as int) / 32
                                    == (old(self).nbits as int) / 32 - 1);
                            }
                        }
                    } else {
                        assert((len as int) / 32 <= (old(self).nbits as int) / 32);
                    }
                }
                assert(blocks_for_bits(old(self).nbits) == old(self).storage@.len());
                assert(nb <= old(self).storage@.len());
            }
            self.storage.truncate(nb);
            proof {
                /* Prefix block-value preservation (instantiation of vstd
                   truncate's subrange semantics) */
                assert forall|w2: usize| w2 < nb ==> self.storage@[w2 as int]
                    == old(self).storage@[w2 as int] by {
                    assert(self.storage@ == old(self).storage@.subrange(0, nb as int));
                    assert forall|w3: usize| w3 < nb implies old(self).storage@.subrange(0, nb as int)[w3 as int]
                        == old(self).storage@[w3 as int] by {
                    }
                }
            }
            self.fix_last_block();
            proof {
                assert(len_inv(self));
                assert forall|j: usize|
                    j < self.nbits implies bit_at(self.storage@, self.nbits, j)
                        == bit_at(old(self).storage@, old(self).nbits, j) by {
                    int_div_bound_lemma(j, self.nbits);
                    assert(j / 32 < nb);
                }
            }
        }
    }

    /// Origin Rust: pub fn nand(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.fix_last_block_with_ones();
    ///     let result = self.process(other, |w1, w2| !(w1 & w2));
    ///     self.fix_last_block();
    ///     result } (lib.rs:1180-1187)
/// The process closure `!(w1 & w2)` is materialized as (w1 & w2) ^ 0xFFFFFFFF
/// (negate precedent); the input side goes through fix_last_block_with_ones
/// via with_ones_input.
/// nand's tail unused-bit op value agrees with the ones-filled input
/// (lemma_nand_last_iff), so the changed criterion is consistent with the
/// doc "Returns `true` if `self` changed" (nor/xnor differ -- see the issue
/// report).
    /// Upstream doc (lib.rs:1155-1178):
    ///   Calculates the nand of two bitvectors.
    ///   Sets `self` to the nand of `self` and `other`. Both bitvectors must be
    ///   the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different length.
    pub exec fn nand(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|j: usize| j < old(self).nbits ==> #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == !(bit_at(old(self).storage@, old(self).nbits, j)
                    && bit_at(other.storage@, other.nbits, j)),
            r == (final(self).storage@ != old(self).storage@),
    {
        self.fix_last_block_with_ones();
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int]
                        == ((with_ones_input(old(self), w2) & other.storage@[w2 as int]) ^ 4294967295u32),
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2),
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2)),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != with_ones_input(old(self), widx)),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            /* Origin Rust: process op closure = !(w1 & w2) (spec-context `!`
               materialized as XOR all-ones) */
            let w = (a & b) ^ 4294967295u32;
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == with_ones_input(old(self), w2) by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == with_ones_input(old(self), k));
                            assert(self.storage@[w2 as int] == with_ones_input(old(self), w2));
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == with_ones_input(old(self), w3) by { }
                            assert(self.storage@[w2 as int] == with_ones_input(old(self), w2));
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: this step changed a block (a!=w => the
                   difference persists) or an old witness (frame) */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        if k == (len - 1) as usize {
                            assert(self.storage@[k as int] != with_ones_input(old(self), k));
                        } else {
                            assert(self.storage@[k as int] != with_ones_input(old(self), k));
                        }
                    }
                }
            }
            k += 1;
        }
        self.fix_last_block();
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            let wlen = s.len();
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == !(bit_at(so, self.nbits, j) && bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                let bj = j % 32;
                if self.nbits % 32 == 0 || kb < (wlen - 1) as usize {
                    lemma_and_bit(so[kb as int], other.storage@[kb as int], bj);
                    lemma_neg_bit(bj, so[kb as int] & other.storage@[kb as int]);
                } else {
                    let e = self.nbits % 32;
                    lemma_nand_tail_bit(so[kb as int], other.storage@[kb as int], e, bj);
                }
            }
            if r {
                assert(s != so) by {
                    if widx == (wlen - 1) as usize && self.nbits % 32 > 0 {
                        let e = self.nbits % 32;
                        let l1 = with_ones_input(old(self), widx);
                        let opn = ((l1 & other.storage@[widx as int]) ^ 4294967295u32);
                        /* preprocessing-loop exit: prepared block value == opn
                           (processed-forall at widx) + opn != l1 */
                        assert(opn != l1);
                        assert(s[widx as int] == opn & (((1u32 << e) - 1u32) as u32)) by { }
                        lemma_nand_last_iff(so[widx as int], other.storage@[widx as int], e);
                        assert(s[widx as int] != so[widx as int]);
                    } else {
                        assert(s[widx as int] != so[widx as int]);
                    }
                }
            } else {
                assert forall|w2: usize| w2 < wlen implies
                    s[w2 as int] == so[w2 as int] by {
                    if w2 == (wlen - 1) as usize && self.nbits % 32 > 0 {
                        let e = self.nbits % 32;
                        let l1 = with_ones_input(old(self), w2);
                        let opn = ((l1 & other.storage@[w2 as int]) ^ 4294967295u32);
                        assert(opn == l1);
                        assert(s[w2 as int] == opn & (((1u32 << e) - 1u32) as u32)) by { }
                        lemma_nand_last_iff(so[w2 as int], other.storage@[w2 as int], e);
                        assert(s[w2 as int] == so[w2 as int]);
                    }
                }
                assert(seq_ptwise(s, so));
                lemma_seq_eq_iff(s, so);
                assert(s == so);
            }
        }
        r
    }

    /// Origin Rust: pub fn nor(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.fix_last_block_with_ones();
///     let result = self.process(other, |w1, w2| !(w1 | w2));
    ///     self.fix_last_block();
    ///     result } (lib.rs:1189-1221)
/// The process closure `!(w1 | w2)` is materialized as (w1 | w2) ^ 0xFFFFFFFF
/// (negate precedent); the input side goes through fix_last_block_with_ones
/// via with_ones_input. Unlike nand (lemma_nand_last_iff), for nor the
/// tail unused-bit op value differs from the ones-filled input, so the
/// changed criterion is NOT "used bits changed": the doc promise
/// "Returns `true` if `self` changed" is refuted (see the issue report).
    /// Upstream doc (lib.rs:1189-1212):
    ///   Calculates the nor of two bitvectors.
    ///   Sets `self` to the nor of `self` and `other`. Both bitvectors must be
    ///   the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different length.
    pub exec fn nor(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|j: usize| j < old(self).nbits ==> #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == (!bit_at(old(self).storage@, old(self).nbits, j)
                    && !bit_at(other.storage@, other.nbits, j)),
            // SPEC-DOC MISMATCH (bit-vec#165): the doc's "Returns `true` if
            // `self` changed" content-change clause is unprovable for nor;
            // the implementation-faithful form is carried instead.
            r == (!(forall|w2: usize| w2 < old(self).storage@.len() ==>
                (((with_ones_input(old(self), w2) | other.storage@[w2 as int]) ^ 4294967295u32)
                    == with_ones_input(old(self), w2)))),
    {
        self.fix_last_block_with_ones();
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int]
                        == ((with_ones_input(old(self), w2) | other.storage@[w2 as int]) ^ 4294967295u32),
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2),
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2)),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != with_ones_input(old(self), widx)),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            /* Origin Rust: process op closure = !(w1 | w2) (spec-context `!`
               materialized as XOR all-ones) */
            let w = (a | b) ^ 4294967295u32;
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == with_ones_input(old(self), w2) by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == with_ones_input(old(self), k));
                            assert(self.storage@[w2 as int] == with_ones_input(old(self), w2));
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == with_ones_input(old(self), w3) by { }
                            assert(self.storage@[w2 as int] == with_ones_input(old(self), w2));
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: this step changed a block (a!=w => the
                   difference persists) or an old witness (frame) */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        if k == (len - 1) as usize {
                            assert(self.storage@[k as int] != with_ones_input(old(self), k));
                        } else {
                            assert(self.storage@[k as int] != with_ones_input(old(self), k));
                        }
                    }
                }
            }
            k += 1;
        }
        self.fix_last_block();
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            let wlen = s.len();
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == (!bit_at(so, self.nbits, j) && !bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                let bj = j % 32;
                if self.nbits % 32 == 0 || kb < (wlen - 1) as usize {
                    lemma_or_bit(so[kb as int], other.storage@[kb as int], bj);
                    lemma_neg_bit(bj, so[kb as int] | other.storage@[kb as int]);
                } else {
                    let e = self.nbits % 32;
                    lemma_nor_tail_bit(so[kb as int], other.storage@[kb as int], e, bj);
                }
            }
            assert(r == (!(forall|w2: usize| w2 < old(self).storage@.len() ==>
                (((with_ones_input(old(self), w2) | other.storage@[w2 as int]) ^ 4294967295u32)
                    == with_ones_input(old(self), w2))))) by { }
        }
        r
    }    /// Origin Rust: pub fn xnor(&mut self, other: &Self) -> bool {
    ///     self.ensure_invariant(); debug_assert!(other.is_last_block_fixed());
    ///     self.fix_last_block_with_ones();
///     let result = self.process(other, |w1, w2| !(w1 ^ w2));
    ///     self.fix_last_block();
    ///     result } (lib.rs:1223-1255)
/// The process closure `!(w1 ^ w2)` is materialized as (w1 ^ w2) ^ 0xFFFFFFFF
/// (negate precedent); the input side goes through fix_last_block_with_ones
/// via with_ones_input. Like nor, xnor's tail unused-bit op value differs
/// from the ones-filled input, so the changed criterion is NOT "used bits
/// changed": the doc promise "Returns `true` if `self` changed" is refuted
/// (see the issue report).
    /// Upstream doc (lib.rs:1223-1246):
    ///   Calculates the xnor of two bitvectors.
    ///   Sets `self` to the xnor of `self` and `other`. Both bitvectors must be
    ///   the same length. Returns `true` if `self` changed.
    ///   # Panics
    ///   Panics if the bitvectors are of different length.
    pub exec fn xnor(&mut self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
            self.nbits == other.nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@.len() == old(self).storage@.len(),
            forall|j: usize| j < old(self).nbits ==> #[trigger] bit_at(final(self).storage@, old(self).nbits, j)
                == (bit_at(old(self).storage@, old(self).nbits, j)
                    == bit_at(other.storage@, other.nbits, j)),
            // SPEC-DOC MISMATCH (bit-vec#165): same as nor -- the doc's
            // content-change clause is unprovable for xnor; the
            // implementation-faithful form is carried instead.
            r == (!(forall|w2: usize| w2 < old(self).storage@.len() ==>
                (((with_ones_input(old(self), w2) ^ other.storage@[w2 as int]) ^ 4294967295u32)
                    == with_ones_input(old(self), w2)))),
    {
        self.fix_last_block_with_ones();
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut changed_bits: u32 = 0u32;
        let mut widx: usize = 0;
        let ghost mut s_head: Seq<u32> = Seq::empty();
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                old(self).storage@.len() == len,
                other.storage@.len() == len,
                self.nbits == old(self).nbits,
                old(self).nbits == other.nbits,
                inv(old(self)),
                inv(other),
                forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int]
                        == ((with_ones_input(old(self), w2) ^ other.storage@[w2 as int]) ^ 4294967295u32),
                forall|w2: usize| k <= w2 && w2 < len ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2),
                changed_bits == 0u32 <==> (forall|w2: usize| w2 < k ==>
                    self.storage@[w2 as int] == with_ones_input(old(self), w2)),
                changed_bits != 0u32 ==> (widx < k
                    && self.storage@[widx as int] != with_ones_input(old(self), widx)),
            decreases
                len - k,
        {
            proof { s_head = self.storage@; }
            let a = self.storage[k];
            let b = other.storage[k];
            /* Origin Rust: process op closure = !(w1 ^ w2) (spec-context `!`
               materialized as XOR all-ones) */
            let w = (a ^ b) ^ 4294967295u32;
            if (a ^ w) != 0u32 {
                widx = k;
            }
            self.storage.set(k, w);
            let cb0 = changed_bits;
            changed_bits = changed_bits | (a ^ w);
            proof {
                assert(self.storage@ == s_head.update(k as int, w));
                lemma_diff_nonzero(a, w);
                if (a ^ w) == 0u32 {
                    assert(a == w);
                } else {
                    assert(a != w);
                }
                if a == w {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            a == w,
                    ;
                }
                if (a ^ w) != 0u32 {
                    assert(changed_bits != 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            (a ^ w) != 0u32,
                    ;
                }
                if changed_bits == 0u32 {
                    assert((a ^ w) == 0u32) by (bit_vector)
                        requires
                            changed_bits == cb0 | (a ^ w),
                            changed_bits == 0u32,
                    ;
                    assert(cb0 == 0u32) by (bit_vector)
                        requires
                            changed_bits == 0u32,
                            changed_bits == cb0 | (a ^ w),
                    ;
                    assert(a == w);
                    assert forall|w2: usize| w2 < k + 1 implies
                        self.storage@[w2 as int] == with_ones_input(old(self), w2) by {
                        if w2 == k {
                            assert(a == w);
                            assert(self.storage@[k as int] == w);
                            assert(s_head[k as int] == a);
                            assert(a == with_ones_input(old(self), k));
                            assert(self.storage@[w2 as int] == with_ones_input(old(self), w2));
                        } else {
                            assert forall|w3: usize| w3 < k implies
                                self.storage@[w3 as int] == with_ones_input(old(self), w3) by { }
                            assert(self.storage@[w2 as int] == with_ones_input(old(self), w2));
                        }
                    }
                }
                /* reverse composition: cb0==0 && (a ^ w)==0 => changed'==0 */
                if cb0 == 0u32 && (a ^ w) == 0u32 {
                    assert((cb0 | (a ^ w)) == 0u32) by (bit_vector)
                        requires
                            cb0 == 0u32,
                            (a ^ w) == 0u32,
                    ;
                    assert(changed_bits == 0u32);
                }
                /* witness closure: this step changed a block (a!=w => the
                   difference persists) or an old witness (frame) */
                if changed_bits != 0u32 {
                    if (a ^ w) != 0u32 {
                        if k == (len - 1) as usize {
                            assert(self.storage@[k as int] != with_ones_input(old(self), k));
                        } else {
                            assert(self.storage@[k as int] != with_ones_input(old(self), k));
                        }
                    }
                }
            }
            k += 1;
        }
        self.fix_last_block();
        let r = changed_bits != 0u32;
        proof {
            let s = self.storage@;
            let so = old(self).storage@;
            let wlen = s.len();
            assert forall|j: usize| j < old(self).nbits implies bit_at(s, self.nbits, j)
                == (bit_at(so, self.nbits, j) == bit_at(other.storage@, other.nbits, j)) by {
                int_div_bound_lemma(j, self.nbits);
                let kb = j / 32;
                let bj = j % 32;
                if self.nbits % 32 == 0 || kb < (wlen - 1) as usize {
                    lemma_xor_bit(so[kb as int], other.storage@[kb as int], bj);
                    lemma_neg_bit(bj, so[kb as int] ^ other.storage@[kb as int]);
                } else {
                    let e = self.nbits % 32;
                    lemma_xnor_tail_bit(so[kb as int], other.storage@[kb as int], e, bj);
                }
            }
            assert(r == (!(forall|w2: usize| w2 < old(self).storage@.len() ==>
                (((with_ones_input(old(self), w2) ^ other.storage@[w2 as int]) ^ 4294967295u32)
                    == with_ones_input(old(self), w2))))) by { }
        }
        r
    }    /// Origin Rust: pub fn remove_all(&mut self) (lib.rs:1995-1998)
    ///     { self.storage.clear(); self.nbits = 0; }
    /// Upstream doc (lib.rs:1988-1994):
    ///   Removes all bits in this vector.
    ///   Note: this method is not named [`clear`] to avoid confusion whenever [`.fill(false)`]
    ///   is needed.
    pub exec fn remove_all(&mut self)
        requires
            inv(self),
        ensures
            inv(final(self)),
            final(self).nbits == 0,
            final(self).storage@ == Seq::empty(),
    {
        self.storage.clear();
        self.nbits = 0;
    }

    /// Origin Rust: pub fn count_ones(&self) -> u64 (lib.rs:1300-1304)
    ///     { self.ensure_invariant();
    ///       self.blocks().map(|elem| elem.count_ones() as u64).sum() }
    ///     u32::count_ones has no vstd spec (probeD/p_count); the intrinsic is
    ///     lowered to its own counting definition -- a 32-step bit loop per
    ///     block, identical value; blocks().map(..).sum() folds into the
    ///     block index loop (none()/all() precedent).
    /// Upstream doc (lib.rs:1283-1286):
    ///   Returns the number of ones in the binary representation.
    ///   Also known as the
    ///   [Hamming weight](https://en.wikipedia.org/wiki/Hamming_weight).
    pub exec fn count_ones(&self) -> (r: u64)
        requires
            inv(self),
        ensures
            r as int == count_ones_spec(self),
    {
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut total: u64 = 0;
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                total as int == popc_seq(self.storage@, k),
            decreases
                len - k,
        {
            let blk = self.storage[k];
            let mut j: usize = 0;
            let mut c: u64 = 0;
            while j < 32
                invariant
                    j <= 32,
                    c as int == popc(blk, j),
                decreases
                    32 - j,
            {
                /* Origin Rust: elem.count_ones() -- the intrinsic's
                   counting step: bit j contributes 1 when set. */
                if ((blk >> j) & 1u32) != 0u32 {
                    proof {
                        lemma_popc_bound(blk, j);
                        assert((c as int) < (u64::MAX as int));
                    }
                    c += 1;
                }
                proof {
                    lemma_bit_shift_test(blk, j);
                    assert(popc(blk, (j + 1) as usize) == popc(blk, j)
                        + (if (blk & (1u32 << j)) != 0u32 { 1int } else { 0int }));
                }
                j += 1;
            }
            proof {
                lemma_popc_bound(blk, 32);
                assert(popc_seq(self.storage@, (k + 1) as usize) == popc_seq(self.storage@, k)
                    + popc(self.storage@[k as int], 32));
                // overflow guard: popc_seq is monotone up to len and the
                // full bridge bounds it by nbits <= u64::MAX
                lemma_popc_seq_mono(self.storage@, (k + 1) as usize, len);
                lemma_popc_seq_is_count(self.storage@, self.nbits);
                lemma_count_bits_bound(self.storage@, self.nbits, 0, self.nbits);
                assert((total as int) + (c as int)
                    == popc_seq(self.storage@, (k + 1) as usize));
                assert((self.nbits as int) <= (u64::MAX as int));
            }
            total += c;
            k += 1;
        }
        proof {
            // block-level sums equal the bit-level count under inv (bridge)
            lemma_popc_seq_is_count(self.storage@, self.nbits);
        }
        total
    }

    /// Origin Rust: pub fn count_zeros(&self) -> u64 (lib.rs:1323-1331)
    ///     { self.ensure_invariant();
    ///       let extra_zeros = (B::bits() - (self.len() % B::bits())) % B::bits();
    ///       self.blocks().map(|elem| elem.count_zeros() as u64).sum::<u64>()
    ///           - extra_zeros as u64 }
    ///     count_zeros per block is the BitBlock default
    ///     bits() - count_ones() (lib.rs:173-175); same intrinsic lowering
    ///     as count_ones (32-step bit loop per block).
    /// Upstream doc (lib.rs:1306-1309):
    ///   Returns the number of zeros in the binary representation.
    ///   Also known as the opposite of
    ///   [Hamming weight](https://en.wikipedia.org/wiki/Hamming_weight).
    pub exec fn count_zeros(&self) -> (r: u64)
        requires
            inv(self),
            // u64 capacity: the whole-vector complement sum fits; upstream
            // would wrap/panic only past ~2^61 bytes of storage (practically
            // unallocatable; treated as a caller obligation here).
            32 * (blocks_for_bits(self.nbits) as int) <= (u64::MAX as int),
        ensures
            r as int + count_ones_spec(self) == (self.nbits as int),
    {
        let extra_zeros = (32 - (self.nbits % 32)) % 32;
        let len = self.storage.len();
        let mut k: usize = 0;
        let mut total: u64 = 0;
        while k < len
            invariant
                k <= len,
                self.storage@.len() == len,
                total as int == zeros_seq(self.storage@, k),
            decreases
                len - k,
        {
            let blk = self.storage[k];
            let mut j: usize = 0;
            let mut c: u64 = 0;
            while j < 32
                invariant
                    j <= 32,
                    c as int == popc(blk, j),
                decreases
                    32 - j,
            {
                if ((blk >> j) & 1u32) != 0u32 {
                    proof {
                        lemma_popc_bound(blk, j);
                        assert((c as int) < (u64::MAX as int));
                    }
                    c += 1;
                }
                proof {
                    lemma_bit_shift_test(blk, j);
                    assert(popc(blk, (j + 1) as usize) == popc(blk, j)
                        + (if (blk & (1u32 << j)) != 0u32 { 1int } else { 0int }));
                }
                j += 1;
            }
            proof {
                lemma_popc_bound(blk, 32);
                assert(popc_seq(self.storage@, (k + 1) as usize)
                    == popc_seq(self.storage@, k) + popc(self.storage@[k as int], 32));
                assert(zeros_seq(self.storage@, (k + 1) as usize) == zeros_seq(self.storage@, k)
                    + (32 - popc(self.storage@[k as int], 32)));
                // overflow guard: per-block complements sum to at most
                // 32 * len, which the caller's u64 capacity bound caps
                lemma_zeros_bound(self.storage@, (k + 1) as usize);
                assert((total as int) + (32 - (c as int))
                    == zeros_seq(self.storage@, (k + 1) as usize));
                assert(((k + 1) as int) <= (len as int));
                assert(32 * (len as int) <= (u64::MAX as int));
            }
            total += 32u64 - c;
            k += 1;
        }
        proof {
            // zeros_seq + popc_seq == 32 * len (per-block complement); the
            // invariant chain gives total == nbits + extra_zeros - ones,
            // so the final subtraction is defined.
            lemma_zeros_popc(self.storage@, len);
            lemma_popc_seq_is_count(self.storage@, self.nbits);
            lemma_count_bits_bound(self.storage@, self.nbits, 0, self.nbits);
            assert((total as int) + count_ones_spec(self) == 32 * (len as int));
            assert((32 * (len as int) - (extra_zeros as int)) == (self.nbits as int)) by {
                let e = self.nbits % 32;
                if e == 0 {
                    assert(extra_zeros == 0);
                    assert(len == blocks_for_bits(self.nbits));
                    assert((self.nbits as int) == 32 * ((self.nbits as int) / 32)) by {
                        assert((self.nbits as int) / 32 * 32
                            + (self.nbits as int) % 32 == (self.nbits as int));
                        assert((self.nbits as int) % 32 == 0);
                    }
                } else {
                    assert(extra_zeros == 32 - e);
                    assert(len == ((self.nbits as int) / 32 + 1) as usize) by {
                        assert(len == blocks_for_bits(self.nbits));
                    }
                    assert((self.nbits as int) == 32 * ((self.nbits as int) / 32) + e) by {
                        assert((self.nbits as int) / 32 * 32
                            + (self.nbits as int) % 32 == (self.nbits as int));
                    }
                }
            }
            assert((total as int) - (extra_zeros as int)
                == (self.nbits as int) - count_ones_spec(self));
            assert((total as int) >= (extra_zeros as int));
        }
        total - (extra_zeros as u64)
    }

    /// Origin Rust: pub fn to_bytes(&self) -> Vec<u8> (lib.rs:1546-1564)
    ///     { self.ensure_invariant();
    ///       let len = self.nbits / 8 + if self.nbits % 8 == 0 { 0 } else { 1 };
    ///       let mut result = Vec::with_capacity(len);
    ///       for byte_idx in 0..len { let mut byte = 0u8;
    ///         for bit_idx in 0..8 { let offset = byte_idx * 8 + bit_idx;
    ///           if offset < self.nbits && self[offset] { byte |= 1 << bit_idx; } }
    ///         result.push(util::reverse_bits(byte)); }
    ///       result }
    ///     Vec::with_capacity rewritten as Vec::new (no vstd with_capacity
    ///     spec; the capacity is a perf hint, not a semantic value);
    ///     self[offset] expands to get (Index-get precedent); util::
    ///     reverse_bits materializes via reverse_bits_exec.
    /// Upstream doc (lib.rs:1525-1528):
    ///   Organises the bits into bytes, such that the first bit in the
    ///   `BitVec` becomes the high-order bit of the first byte. If the
    ///   size of the `BitVec` is not a multiple of eight then trailing bits
    ///   will be filled-in with `false`.
    pub exec fn to_bytes(&self) -> (result: Vec<u8>)
        requires
            inv(self),
        ensures
            result@.len() == bytes_for_bits(self.nbits),
            forall|j: usize, q: usize|
                j < result@.len() && q < 8 ==>
                #[trigger] bit_u8(result@[j as int], (7 - (q as int)))
                    == (if (8 * j + q) < self.nbits {
                        bit_at(self.storage@, self.nbits, (8 * j + q) as usize)
                    } else {
                        false
                    }),
    {
        /* Origin Rust: let len = self.nbits / 8 + if ... (byte axis) */
        let nbytes = self.nbits / 8 + if self.nbits % 8 == 0 { 0 } else { 1 };
        proof {
            assert(nbytes == bytes_for_bits(self.nbits));
        }
        let mut result: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j < nbytes
            invariant
                j <= nbytes,
                result@.len() == j,
                nbytes == bytes_for_bits(self.nbits),
                forall|w2: usize, q: usize| w2 < j && q < 8 ==>
                    #[trigger] bit_u8(result@[w2 as int], (7 - (q as int)))
                        == (if (8 * w2 + q) < self.nbits {
                            bit_at(self.storage@, self.nbits, (8 * w2 + q) as usize)
                        } else {
                            false
                        }),
            decreases
                nbytes - j,
        {
            let mut byte: u8 = 0;
            let mut t: usize = 0;
            let ghost mut byte_head: u8 = 0u8;
            proof {
                assert(1u8 << 0 == 1u8) by (bit_vector);
            }
            while t < 8
                invariant
                    t <= 8,
                    forall|q: usize| q < t ==>
                        ((byte & (1u8 << q)) != 0u8)
                            == (if (8 * j + q) < self.nbits {
                                bit_at(self.storage@, self.nbits, (8 * j + q) as usize)
                            } else {
                                false
                            }),
                    t < 8 ==> byte < (1u8 << t),
                decreases
                    8 - t,
            {
                proof { byte_head = byte; }
                let offset = 8 * j + t;
                /* Origin Rust: if offset < self.nbits && self[offset]
                   (Index reads are get) */
                let placed: bool = if offset < self.nbits {
                    let g = self.get(offset);
                    if g == Some(true) {
                        byte = byte | (1u8 << t);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };
                proof {
                    assert(1u8 << t == 1u8 << (t as u8)) by {
                        assert(t < 8);
                    }
                    if placed {
                        assert(byte == byte_head | (1u8 << t));
                        assert(((byte & (1u8 << (t as u8))) != 0u8)) by (bit_vector)
                            requires
                                byte == byte_head | (1u8 << (t as u8)),
                                (t as u8) < 8u8,
                        ;
                        assert(1u8 << t == 1u8 << (t as u8));
                        assert forall|q: usize| q < t + 1 implies
                            ((byte & (1u8 << q)) != 0u8)
                                == (if (8 * j + q) < self.nbits {
                                    bit_at(self.storage@, self.nbits, (8 * j + q) as usize)
                                } else {
                                    false
                                }) by {
                            if q < t {
                                assert(((1u8 << t) & (1u8 << q)) == 0u8) by (bit_vector)
                                    requires
                                        (q as u8) < (t as u8),
                                ;
                                lemma_u8_or_keep(byte, byte_head, (1u8 << t), q);
                                // head's bit q: entry-invariant instance
                                assert(((byte_head & (1u8 << q)) != 0u8)
                                    == (if (8 * j + q) < self.nbits {
                                        bit_at(self.storage@, self.nbits, (8 * j + q) as usize)
                                    } else {
                                        false
                                    }));
                            } else {
                                // q == t: the read bit was true (guard by placed)
                                assert((8 * j + t) < self.nbits);
                                assert(offset == 8 * j + t);
                            }
                        }
                        // bound: byte < 2^(t+1)
                        if t + 1 < 8 {
                            lemma_u8_or_max(byte_head, t);
                        }
                    } else {
                        assert(byte == byte_head);
                        assert forall|q: usize| q < t implies
                            ((byte & (1u8 << q)) != 0u8)
                                == (if (8 * j + q) < self.nbits {
                                    bit_at(self.storage@, self.nbits, (8 * j + q) as usize)
                                } else {
                                    false
                                }) by { }
                        // q == t: bit t stays empty, and the guard read false
                        // (out of range or the bit itself was false)
                        lemma_u8_pow_lt_bit(byte_head, t, t);
                        // bound carries through: < 2^t => < 2^(t+1)
                        if t + 1 < 8 {
                            assert((byte < (1u8 << ((t + 1) as u8)))) by (bit_vector)
                                requires
                                    byte < (1u8 << (t as u8)),
                                    (t as u8) <= 6u8,
                            ;
                            assert(1u8 << (t + 1) == 1u8 << ((t + 1) as u8));
                        }
                    }
                }
                t += 1;
            }
            let rb = reverse_bits_exec(byte);
            let ghost mut s_pre_push: Seq<u8> = Seq::empty();
            proof { s_pre_push = result@; }
            result.push(rb);
            proof {
                assert(result@ == s_pre_push.push(rb));
                assert forall|w2: usize, q: usize| w2 < j + 1 && q < 8 implies
                    #[trigger] bit_u8(result@[w2 as int], (7 - (q as int)))
                        == (if (8 * w2 + q) < self.nbits {
                            bit_at(self.storage@, self.nbits, (8 * w2 + q) as usize)
                        } else {
                            false
                        }) by {
                    if w2 < j {
                        assert(result@[w2 as int] == s_pre_push[w2 as int]) by {
                            assert(result@ == s_pre_push.push(rb));
                        }
                    } else {
                        assert(w2 == j);
                        assert(result@[w2 as int] == rb) by {
                            assert(result@ == s_pre_push.push(rb));
                            assert(w2 as int == s_pre_push.len());
                        }
                        // rb bit (7-q) == byte bit q (reversal contract);
                        // byte bit q == self bit (8j+q) (inner-loop exit fact)
                        assert forall|q2: usize| q2 < 8 implies
                            #[trigger] bit_u8(rb, (7 - (q2 as int)))
                                == (if (8 * j + q2) < self.nbits {
                                    bit_at(self.storage@, self.nbits, (8 * j + q2) as usize)
                                } else {
                                    false
                                }) by {
                            let p7: int = 7 - (q2 as int);
                            assert(0 <= p7 < 8) by {
                                assert(q2 < 8);
                            }
                            // rev ensures instantiated at p == 7-q2
                            assert(bit_u8(rb, p7) == bit_u8(byte, (7 - p7))) by { }
                            assert((7 - p7) == (q2 as int)) by {
                                assert(q2 < 8);
                            }
                            assert(1u8 << q2 == 1u8 << (q2 as u8)) by {
                                assert(q2 < 8);
                            }
                        }
                    }
                }
            }
            j += 1;
        }
        result
    }

    /// Origin Rust: pub fn from_bytes(bytes: &[u8]) -> Self
    ///     { BitVec::<u32>::from_bytes_general(bytes) } (lib.rs:492-493)
    /// /  from_bytes_general (lib.rs:585-614):
    ///     { let len = bytes.len().checked_mul(u8::bits()).expect("capacity overflow");
    ///       let mut bit_vec = BitVec::with_capacity_general(len);
    ///       let complete_words = bytes.len() / B::bytes();
    ///       let extra_bytes = bytes.len() % B::bytes();
    ///       bit_vec.nbits = len;
    ///       for i in 0..complete_words { let mut accumulator = B::zero();
    ///         for idx in 0..B::bytes() {
    ///           accumulator |= B::from_byte(util::reverse_bits(bytes[i * B::bytes()
    ///               + idx])) << (idx * 8); }
    ///         bit_vec.storage.push(accumulator); }
    ///       if extra_bytes > 0 { let mut last_word = B::zero();
    ///         for (i, &byte) in bytes[complete_words * B::bytes()..].iter().enumerate() {
    ///           last_word |= B::from_byte(util::reverse_bits(byte)) << (i * 8); }
    ///         bit_vec.storage.push(last_word); }
    ///       bit_vec }
    ///     u32 axes: B::bytes() == 4, B::from_byte(b) == b as u32;
    ///     checked_mul -> requires (expect "capacity overflow");
    ///     with_capacity_general -> Vec::new (capacity is a perf hint);
    ///     Bytes::from_byte materializes as the u8-as-u32 cast.
    /// Upstream doc (lib.rs:477-479):
    ///   Transforms a byte-vector into a `BitVec`. Each byte becomes eight bits,
    ///   with the most significant bits of each byte coming first. Each
    ///   bit becomes `true` if equal to 1 or `false` if equal to 0.
    pub exec fn from_bytes(bytes: &[u8]) -> (bv: BitVec)
        requires
            bytes.len() <= usize::MAX / 8,
        ensures
            inv(&bv),
            bv.nbits == 8 * bytes.len(),
            forall|i: usize|
                i < bv.nbits ==> bit_at(bv.storage@, bv.nbits, i)
                    == from_bytes_bit(bytes@, i),
    {
        let len = bytes.len() * 8;
        let complete_words = bytes.len() / 4;
        let extra_bytes = bytes.len() % 4;
        let mut storage: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < complete_words
            invariant
                i <= complete_words,
                storage@.len() == i,
                forall|w2: usize, pos: usize|
                    w2 < i && pos < 32 ==>
                        ((storage@[w2 as int] & (1u32 << pos)) != 0u32)
                            == fb_byte(bytes@, (w2 as int), (pos as int)),
            decreases
                complete_words - i,
        {
            /* Origin Rust: let mut accumulator = B::zero(); */
            let mut accumulator: u32 = 0u32;
            let mut idx: usize = 0;
            proof {
                assert(1u32 << 0 == 1u32) by (bit_vector);
            }
            while idx < 4
                invariant
                    idx <= 4,
                    storage@.len() == i,
                    idx < 4 ==> accumulator < (1u32 << (8 * idx)),
                    forall|pos: usize|
                        pos < 8 * idx ==>
                            ((accumulator & (1u32 << pos)) != 0u32)
                                == fb_byte(bytes@, (i as int), (pos as int)),
                decreases
                    4 - idx,
            {
                /* Origin Rust: accumulator |= B::from_byte(
                   util::reverse_bits(bytes[i * B::bytes() + idx])) << (idx * 8); */
                let b = bytes[(4 * i + idx) as usize];
                let rb = reverse_bits_exec(b);
                proof {
                    assert(4 * i + idx < bytes.len()) by {
                        assert(idx < 4);
                        assert(i < complete_words);
                        assert(complete_words == bytes.len() / 4);
                    }
                }
                let shifted = ((rb as u32) << (8 * idx)) as u32;
                proof {
                    assert(8 * idx <= 24) by {
                        assert(idx <= 3);
                    }
                }
                let acc = accumulator | shifted;
                proof {
                    assert forall|pos: usize| pos < 8 * (idx + 1) implies
                        ((acc & (1u32 << pos)) != 0u32)
                            == fb_byte(bytes@, (i as int), (pos as int)) by {
                        if pos < 8 * idx {
                            lemma_shift_low_zero((rb as u32), idx, pos);
                            assert((shifted & (1u32 << pos)) == 0u32);
                            lemma_or_low_preserve(acc, accumulator, shifted, pos);
                        } else {
                            let t8: usize = ((8 * (idx as int)) as usize);
                            assert(t8 as int == 8 * (idx as int));
                            assert(pos >= t8);
                            let p: usize = ((pos - t8) as usize);
                            assert(p < 8) by {
                                assert(pos < 8 * (idx + 1));
                                assert(pos >= 8 * idx);
                            }
                            assert(pos == t8 + p);
                            assert((pos as int) / 8 == (idx as int)) by {
                                assert((pos as int) == 8 * (idx as int) + (p as int));
                                assert(p < 8);
                            }
                            assert((pos as int) % 8 == (p as int)) by {
                                assert((pos as int) == 8 * (idx as int) + (p as int));
                                assert(p < 8);
                            }
                            lemma_pow_lt_bit(accumulator, t8, pos);
                            lemma_or_compose_bit(acc, accumulator, shifted, pos);
                            assert(((shifted & (1u32 << pos)) != 0u32)
                                == (((rb & (1u8 << (p as u8))) != 0u8))) by {
                                assert(pos == t8 + p);
                                assert(t8 == 8 * idx);
                                lemma_pack_bit((rb as u32), idx, p);
                                lemma_u8_cast_bit(rb, p);
                            }
                            assert((((rb & (1u8 << (p as u8))) != 0u8)
                                == ((b & (1u8 << ((7 - (p as int)) as u8))) != 0u8))) by {
                                assert(bit_u8(rb, (p as int)) == bit_u8(b, (7 - (p as int))));
                            }
                            // fb_byte at (i, pos): byte index/pos arithmetic
                            assert(fb_byte(bytes@, (i as int), (pos as int))
                                == (((bytes@[(4 * (i as int) + (idx as int)) as int]
                                    & (1u8 << ((7 - (p as int)) as u8))) != 0u8))) by {
                                assert((pos as int) / 8 == (idx as int));
                                assert((pos as int) % 8 == (p as int));
                            }
                            assert((((bytes@[(4 * (i as int) + (idx as int)) as int]
                                & (1u8 << ((7 - (p as int)) as u8))) != 0u8)
                                == (((rb & (1u8 << (p as u8))) != 0u8)))) by {
                                assert(bit_u8(rb, (p as int)) == bit_u8(b, (7 - (p as int))));
                            }
                        }
                    }
                    if idx < 3 {
                        lemma_shift8_or_bound(accumulator, (rb as u32), ((8 * (idx as int)) as usize));
                        assert(acc == (accumulator | (((rb as u32) << (8 * idx)) as u32)));
                    }
                }
                accumulator = acc;
                idx += 1;
            }
            let ghost mut s_pre_push: Seq<u32> = Seq::empty();
            proof { s_pre_push = storage@; }
            storage.push(accumulator);
            proof {
                assert(storage@ == s_pre_push.push(accumulator));
                assert forall|w2: usize, pos: usize| w2 < i + 1 && pos < 32 implies
                    ((storage@[w2 as int] & (1u32 << pos)) != 0u32)
                        == fb_byte(bytes@, (w2 as int), (pos as int)) by {
                    if w2 < i {
                        assert(storage@[w2 as int] == s_pre_push[w2 as int]) by {
                            assert(storage@ == s_pre_push.push(accumulator));
                        }
                    } else {
                        assert(w2 == i);
                        assert(storage@[w2 as int] == accumulator) by {
                            assert(storage@ == s_pre_push.push(accumulator));
                            assert(w2 as int == s_pre_push.len());
                        }
                        assert forall|pos2: usize| pos2 < 32 implies
                            ((accumulator & (1u32 << pos2)) != 0u32)
                                == fb_byte(bytes@, (i as int), (pos2 as int)) by {
                            assert(idx == 4);
                        }
                    }
                }
            }
            i += 1;
        }
        // hoisted so the closing proofs can cite the tail-assembly state
        let mut last_word: u32 = 0u32;
        let mut a: usize = 0;
        let ghost mut s_pre_push2: Seq<u32> = Seq::empty();
        proof {
            assert(1u32 << 0 == 1u32) by (bit_vector);
        }
        if extra_bytes > 0 {
            /* Origin Rust: let mut last_word = B::zero(); */
            while a < extra_bytes
                invariant
                    a <= extra_bytes,
                    storage@.len() == complete_words,
                    last_word < (1u32 << (8 * a)),
                    forall|pos: usize|
                        pos < 8 * a ==>
                            ((last_word & (1u32 << pos)) != 0u32)
                                == fb_byte(bytes@, (complete_words as int), (pos as int)),
                decreases
                    extra_bytes - a,
            {
                /* Origin Rust: last_word |= B::from_byte(
                   util::reverse_bits(byte)) << (i * 8); */
                let b = bytes[(4 * complete_words + a) as usize];
                let rb = reverse_bits_exec(b);
                proof {
                    assert(4 * complete_words + a < bytes.len()) by {
                        assert(a < extra_bytes);
                        assert(extra_bytes == bytes.len() % 4);
                        assert(complete_words == bytes.len() / 4);
                    }
                }
                let shifted = ((rb as u32) << (8 * a)) as u32;
                proof {
                    assert(8 * a <= 24) by {
                        assert(a <= 3);
                    }
                }
                let lw = last_word | shifted;
                proof {
                    assert forall|pos: usize| pos < 8 * (a + 1) implies
                        ((lw & (1u32 << pos)) != 0u32)
                            == fb_byte(bytes@, (complete_words as int), (pos as int)) by {
                        if pos < 8 * a {
                            lemma_shift_low_zero((rb as u32), a, pos);
                            assert((shifted & (1u32 << pos)) == 0u32);
                            lemma_or_low_preserve(lw, last_word, shifted, pos);
                        } else {
                            let t8: usize = ((8 * (a as int)) as usize);
                            assert(t8 as int == 8 * (a as int));
                            assert(pos >= t8);
                            let p: usize = ((pos - t8) as usize);
                            assert(p < 8) by {
                                assert(pos < 8 * (a + 1));
                                assert(pos >= 8 * a);
                            }
                            assert(pos == t8 + p);
                            assert((pos as int) / 8 == (a as int)) by {
                                assert((pos as int) == 8 * (a as int) + (p as int));
                                assert(p < 8);
                            }
                            assert((pos as int) % 8 == (p as int)) by {
                                assert((pos as int) == 8 * (a as int) + (p as int));
                                assert(p < 8);
                            }
                            lemma_pow_lt_bit(last_word, t8, pos);
                            lemma_or_compose_bit(lw, last_word, shifted, pos);
                            assert(((shifted & (1u32 << pos)) != 0u32)
                                == (((rb & (1u8 << (p as u8))) != 0u8))) by {
                                assert(pos == t8 + p);
                                assert(t8 == 8 * a);
                                lemma_pack_bit((rb as u32), a, p);
                                lemma_u8_cast_bit(rb, p);
                            }
                            assert((((rb & (1u8 << (p as u8))) != 0u8)
                                == ((b & (1u8 << ((7 - (p as int)) as u8))) != 0u8))) by {
                                assert(bit_u8(rb, (p as int)) == bit_u8(b, (7 - (p as int))));
                            }
                            assert(fb_byte(bytes@, (complete_words as int), (pos as int))
                                == (((bytes@[(4 * (complete_words as int) + (a as int)) as int]
                                    & (1u8 << ((7 - (p as int)) as u8))) != 0u8))) by {
                                assert((pos as int) / 8 == (a as int));
                                assert((pos as int) % 8 == (p as int));
                            }
                            assert((((bytes@[(4 * (complete_words as int) + (a as int)) as int]
                                & (1u8 << ((7 - (p as int)) as u8))) != 0u8)
                                == (((rb & (1u8 << (p as u8))) != 0u8)))) by {
                                assert(bit_u8(rb, (p as int)) == bit_u8(b, (7 - (p as int))));
                            }
                        }
                    }
                    assert(lw == (last_word | (((rb as u32) << (8 * a)) as u32)));
                    lemma_shift8_or_bound(last_word, (rb as u32), ((8 * (a as int)) as usize));
                }
                last_word = lw;
                a += 1;
            }
            proof { s_pre_push2 = storage@; }
            storage.push(last_word);
            proof {
                assert(storage@ == s_pre_push2.push(last_word));
                assert(s_pre_push2.len() == complete_words as int) by {
                    assert(storage@ == s_pre_push2.push(last_word));
                }
                assert forall|w2: usize, pos: usize|
                    w2 < complete_words && pos < 32 implies
                        ((storage@[w2 as int] & (1u32 << pos)) != 0u32)
                            == fb_byte(bytes@, (w2 as int), (pos as int)) by {
                    assert((w2 as int) < s_pre_push2.len());
                    assert(storage@[w2 as int] == s_pre_push2[w2 as int]) by {
                        assert(storage@ == s_pre_push2.push(last_word));
                    }
                }
            }
        }
        let len2 = len;
        let bv = BitVec { storage, nbits: len2 };
        proof {
            let m = bytes.len();
            let nb: usize = if m % 4 == 0 {
                m / 4
            } else {
                ((m as int) / 4 + 1) as usize
            };
            assert(complete_words == m / 4) by {
                assert(complete_words == bytes.len() / 4);
            }
            assert(bv.storage@.len() == nb) by {
                if m % 4 == 0 {
                    assert(extra_bytes == 0);
                } else {
                    assert(extra_bytes > 0);
                    assert(bv.storage@.len() == complete_words + 1);
                }
            }
            // len_inv: nb == blocks_for_bits(8m)
            let w8: usize = ((8 * (m as int)) as usize);
            assert(blocks_for_bits(w8) == nb) by {
                assert(((8 * (m as int)) / 32) == ((m as int) / 4)) by {
                    assert(8 * (m as int) == 32 * ((m as int) / 4) + 8 * ((m as int) % 4));
                    assert((m as int) % 4 < 4);
                }
                if m % 4 == 0 {
                    assert((m as int) % 4 == 0);
                    assert(blocks_for_bits(w8) == ((8 * (m as int)) / 32));
                } else {
                    assert((m as int) % 4 > 0);
                    assert(blocks_for_bits(w8) == ((8 * (m as int)) / 32 + 1));
                }
            }
            assert(len_inv(&bv));
            // trailing_zero: the tail block's bits above 8*extra_bytes are 0
            assert(trailing_zero(&bv)) by {
                let e: usize = ((8 * (m as int)) as usize) % 32;
                if e > 0 {
                    let eb: usize = m % 4;
                    assert((e as int) == 8 * (eb as int)) by {
                        assert(8 * (m as int)
                            == 32 * ((m as int) / 4) + 8 * ((m as int) % 4));
                    }
                    assert(eb > 0);
                    assert(eb <= 3);
                    assert(bv.storage@.len() == ((m as int) / 4) + 1);
                    assert(((bv.storage@.len() - 1) as int) == ((m as int) / 4));
                    assert((bv.storage@.len() - 1) as int == s_pre_push2.len()) by {
                        assert(bv.storage@ == s_pre_push2.push(last_word));
                    }
                    let tail = bv.storage@[(bv.storage@.len() - 1) as int];
                    assert(tail == last_word) by {
                        assert(bv.storage@ == s_pre_push2.push(last_word));
                        assert(((bv.storage@.len() - 1) as int) == s_pre_push2.len());
                    }
                    // a == eb at the loop2 exit; the bound invariant closes
                    assert(last_word < (1u32 << (8 * eb)));
                }
            }
            assert(inv(&bv));
            // per-bit doc semantics: fb_byte at (w2, pos) == from_bytes_bit
            assert forall|i: usize| i < bv.nbits implies bit_at(bv.storage@, bv.nbits, i)
                == from_bytes_bit(bytes@, i) by {
                int_div_bound_lemma(i, bv.nbits);
                let w2 = i / 32;
                let pos = i % 32;
                assert((i as int) == 32 * (w2 as int) + (pos as int));
                assert(pos < 32);
                assert(((i / 8) as int) == 4 * (w2 as int) + ((pos as int) / 8)) by {
                    assert(((32 * (w2 as int)) + (pos as int))
                        == 8 * (4 * (w2 as int) + ((pos as int) / 8))
                            + ((pos as int) % 8));
                    assert(((pos as int) % 8) < 8);
                }
                assert(((i % 8) as int) == ((pos as int) % 8)) by {
                    assert((i as int) == 32 * (w2 as int) + (pos as int));
                    assert(((32 * (w2 as int)) % 8) == 0);
                }
                assert(bit_at(bv.storage@, bv.nbits, i)
                    == ((bv.storage@[w2 as int] & (1u32 << pos)) != 0u32)) by {
                    assert((i / 32) == w2);
                    assert((i % 32) == pos);
                }
                if w2 < ((m as int) / 4) as usize {
                    // full word: the assembly invariant covers the position
                    assert(((bv.storage@[w2 as int] & (1u32 << pos)) != 0u32)
                        == fb_byte(bytes@, (w2 as int), (pos as int))) by {
                    }
                } else {
                    assert((w2 as int) == (m as int) / 4) by {
                        assert(w2 < blocks_for_bits(((8 * (m as int)) as usize)));
                        assert((m as int) % 4 > 0);
                    }
                    let eb: usize = m % 4;
                    assert(complete_words == ((m as int) / 4) as usize) by {
                        assert(complete_words == m / 4);
                    }
                    assert((pos as int) < 8 * (eb as int)) by {
                        assert((i as int) < 8 * (m as int));
                        assert((i as int) == 32 * ((m as int) / 4) + (pos as int));
                        assert(8 * (m as int) == 32 * ((m as int) / 4) + 8 * (eb as int));
                    }
                    let tail = bv.storage@[w2 as int];
                    assert(tail == last_word) by {
                        assert(bv.storage@ == s_pre_push2.push(last_word));
                        assert((w2 as int) == s_pre_push2.len());
                    }
                    // tail word position fact (loop2-exit invariant at pos)
                    assert(((tail & (1u32 << pos)) != 0u32)
                        == fb_byte(bytes@, (complete_words as int), (pos as int))) by {
                        assert(a == eb);
                    }
                }
                // fb_byte == from_bytes_bit: byte index/bit-pos arithmetic
                assert(fb_byte(bytes@, (w2 as int), (pos as int))
                    == from_bytes_bit(bytes@, i)) by {
                    assert(((4 * (w2 as int)) + ((pos as int) / 8))
                        == ((i / 8) as int)) by {
                        assert(((i / 8) as int) == 4 * (w2 as int) + ((pos as int) / 8));
                    }
                    assert(((7 - (pos as int) % 8) as u8) == ((7 - (i % 8)) as u8)) by {
                        assert(((i % 8) as int) == ((pos as int) % 8));
                    }
                }
            }
        }
        bv
    }

    /// Origin Rust: pub fn insert(&mut self, at: usize, bit: bool) (lib.rs:1893-1923)
    ///     { assert!(at <= self.nbits, "insertion index ...");
    ///       self.ensure_invariant();
    ///       let last_block_bits = self.nbits % B::bits();
    ///       let block_at = at / B::bits();
    ///       let bit_at = at % B::bits();
    ///       if last_block_bits == 0 { self.storage.push(B::zero()); }
    ///       self.nbits += 1;
    ///       let mut carry = self.storage[block_at] >> (B::bits() - 1);
    ///       let lsbits_mask = (B::one() << bit_at) - B::one();
    ///       let set_bit = if bit { B::one() } else { B::zero() } << bit_at;
    ///       self.storage[block_at] = (self.storage[block_at] & lsbits_mask)
    ///           | ((self.storage[block_at] & !lsbits_mask) << 1) | set_bit;
    ///       for block_ref in &mut self.storage[block_at + 1..] {
    ///           let curr_carry = *block_ref >> (B::bits() - 1);
    ///           *block_ref = *block_ref << 1 | carry;
    ///           carry = curr_carry; } }
    ///     # Panics (assert) -> requires; the slice iterator is an
    ///     ascending block index loop (same order); the spec `!` is
    ///     materialized as XOR all-ones (negate precedent); upstream's
    ///     repeated self.storage[block_at] reads are one read (same value).
    /// Upstream doc (lib.rs:1869-1872, 1887-1890):
    ///   Inserts a given bit at index `at`, shifting all bits after by one.
    ///   # Panics
    ///   Panics if `at` is out of bounds for `BitVec`'s length (that is, if `at > BitVec::len()`)
    ///   # Time complexity
    ///   Takes O([`len`]) time. All items after the insertion index must be
    ///   shifted to the right. In the worst case, all elements are shifted when
    ///   the insertion index is 0.
    pub exec fn insert(&mut self, at: usize, bit: bool)
        requires
            inv(old(self)),
            at <= old(self).nbits,
            old(self).nbits < usize::MAX,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits + 1,
            final(self).storage@.len() == (if old(self).nbits % 32 == 0 {
                old(self).storage@.len() + 1
            } else {
                old(self).storage@.len()
            }),
            forall|j: usize|
                j < at ==> bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            bit_at(final(self).storage@, final(self).nbits, at) == bit,
            forall|j: usize|
                at <= j && j < old(self).nbits ==>
                #[trigger] bit_at(final(self).storage@, final(self).nbits, (j + 1) as usize)
                    == bit_at(old(self).storage@, old(self).nbits, j),
    {
        let last_block_bits = self.nbits % 32;
        let block_at = at / 32;
        let bit_at_w = at % 32;
        if last_block_bits == 0 {
            self.storage.push(0u32);
            proof {
                assert(self.storage@ == old(self).storage@.push(0u32));
            }
        }
        self.nbits = self.nbits + 1;
        proof {
            // block_at stays in range (the fresh tail covers the == case)
            assert(block_at < self.storage@.len()) by {
                assert(len_inv(old(self)));
                if old(self).nbits % 32 == 0 {
                    assert(self.storage@.len() == old(self).storage@.len() + 1);
                    assert(old(self).storage@.len()
                        == (old(self).nbits as int) / 32);
                    assert((at as int) / 32 <= (old(self).nbits as int) / 32);
                } else {
                    assert(self.storage@.len() == old(self).storage@.len());
                    assert(old(self).storage@.len()
                        == (old(self).nbits as int) / 32 + 1);
                    assert((at as int) <= (old(self).nbits as int));
                    assert((at as int) / 32 <= (old(self).nbits as int) / 32);
                }
            }
        }
        let base = self.storage[block_at];
        proof {
            // base is the pre-insert block value: the non-push case keeps the
            // sequence identical; the push case extends at the end, so
            // indices below the old length keep their old values
            if (block_at as int) < old(self).storage@.len() {
                if old(self).nbits % 32 == 0 {
                    assert(self.storage@ == old(self).storage@.push(0u32));
                } else {
                    assert(self.storage@ == old(self).storage@);
                }
                assert(base == old(self).storage@[block_at as int]);
            } else {
                assert((block_at as int) == old(self).storage@.len()) by {
                    assert(block_at < self.storage@.len());
                    assert(self.storage@.len() == old(self).storage@.len() + 1);
                }
                assert(self.storage@ == old(self).storage@.push(0u32));
                assert(base == self.storage@[block_at as int]);
                assert(self.storage@[block_at as int] == 0u32);
            }
        }
        let carry0 = base >> 31;
        proof {
            lemma_carry31(base);
            // carry0 in {0, 1}: the top bit moving to the next block
        }
        proof {
            assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32)) by { }
            assert((1u32 << (bit_at_w as u32)) != 0u32) by (bit_vector)
                requires
                    (bit_at_w as u32) < 32u32,
            ;
        }
        let lsbits_mask = ((1u32 << bit_at_w) - 1u32) as u32;
        let set_bit: u32 = (if bit { 1u32 } else { 0u32 }) << bit_at_w;
        proof {
            assert(set_bit == 0u32 || set_bit == (1u32 << bit_at_w)) by {
                if bit {
                    assert(set_bit == 1u32 << bit_at_w);
                } else {
                    assert((0u32 << bit_at_w) == 0u32) by (bit_vector)
                        requires
                            (bit_at_w as u32) < 32u32,
                    ;
                    assert(set_bit == 0u32);
                }
            }
            assert(lsbits_mask == ((1u32 << (bit_at_w as u32)) - 1u32));
        }
        let new_base = (base & lsbits_mask) | ((base & (4294967295u32 ^ lsbits_mask)) << 1) | set_bit;
        /* Origin Rust: self.storage[block_at] = ... */
        self.storage.set(block_at, new_base);
        let ghost mut s_pc: Seq<u32> = Seq::empty();
        proof {
            if old(self).nbits % 32 == 0 {
                assert(self.storage@
                    == (old(self).storage@.push(0u32)).update(block_at as int, new_base));
                s_pc = (old(self).storage@.push(0u32)).update(block_at as int, new_base);
            } else {
                assert(self.storage@ == old(self).storage@.update(block_at as int, new_base));
                s_pc = old(self).storage@.update(block_at as int, new_base);
            }
        }
        let len_total = self.storage.len();
        proof {
            assert(s_pc.len() == len_total as int);
        }
        let mut carry = carry0;
        let mut k: usize = block_at + 1;
        while k < len_total
            invariant
                k <= len_total,
                block_at + 1 <= k,
                self.storage@.len() == len_total,
                s_pc.len() == len_total as int,
                self.nbits == old(self).nbits + 1,
                forall|w2: usize| w2 <= block_at ==>
                    #[trigger] self.storage@[w2 as int] == s_pc[w2 as int],
                forall|w2: usize| block_at + 1 <= w2 && w2 < k ==>
                    #[trigger] self.storage@[w2 as int] ==
                        ((s_pc[w2 as int] << 1)
                            | (if w2 == block_at + 1 {
                                carry0
                            } else {
                                s_pc[(w2 - 1) as int] >> 31
                            })),
                forall|w2: usize| k <= w2 && w2 < len_total ==>
                    #[trigger] self.storage@[w2 as int] == s_pc[w2 as int],
                carry == if k == block_at + 1 {
                    carry0
                } else {
                    s_pc[(k - 1) as int] >> 31
                },
            decreases
                len_total - k,
        {
            let ghost mut s_head: Seq<u32> = Seq::empty();
            proof {
                s_head = self.storage@;
                // frame: position k is untouched so far
                assert(s_head[k as int] == s_pc[k as int]);
            }
            let curr = self.storage[k];
            let curr_carry = curr >> 31;
            proof {
                assert(curr == s_pc[k as int]);
                lemma_carry31(curr);
            }
            self.storage.set(k, (curr << 1) | carry);
            proof {
                assert(self.storage@ == s_head.update(k as int, (curr << 1) | carry));
                // position k takes the cascade form
                assert(((curr << 1) | carry) ==
                    ((s_pc[k as int] << 1)
                        | (if k == block_at + 1 {
                            carry0
                        } else {
                            s_pc[(k - 1) as int] >> 31
                        }))) by {
                    if k == block_at + 1 {
                        assert(carry == carry0);
                    } else {
                        assert(carry == s_pc[(k - 1) as int] >> 31);
                    }
                }
                assert forall|w2: usize| block_at + 1 <= w2 && w2 < k + 1 implies
                    self.storage@[w2 as int] ==
                        ((s_pc[w2 as int] << 1)
                            | (if w2 == block_at + 1 {
                                carry0
                            } else {
                                s_pc[(w2 - 1) as int] >> 31
                            })) by {
                    // positions < k carry over from the invariant (the
                    // update touches only k); position k is this step's set
                    if w2 < k {
                        assert(self.storage@[w2 as int] == s_head[w2 as int]);
                    } else {
                        assert(w2 == k);
                        assert(self.storage@[w2 as int] == ((curr << 1) | carry));
                    }
                }
                // untouched tail
                assert forall|w2: usize| k + 1 <= w2 && w2 < len_total implies
                    self.storage@[w2 as int] == s_pc[w2 as int] by {
                    assert(self.storage@ == s_head.update(k as int, (curr << 1) | carry));
                    assert(self.storage@[w2 as int] == s_head[w2 as int]);
                }
                // carry for the next iteration (k + 1 > block_at + 1)
                assert(curr_carry == s_pc[k as int] >> 31);
            }
            carry = curr_carry;
            k += 1;
        }
        proof {
            let sF = self.storage@;
            let sO = old(self).storage@;
            let nO = old(self).nbits;
            let nF = self.nbits;
            let ba = block_at;
            let b = bit_at_w;
            let eO = nO % 32;
            let pushed: bool = eO == 0;
            let L: usize = sO.len() as usize;
            let sb: u32 = set_bit;
            assert(sb == 0u32 || sb == (1u32 << b)) by {
                assert(sb == set_bit);
                if bit {
                    assert(sb == (1u32 << bit_at_w));
                    assert(bit_at_w == b);
                } else {
                    assert((0u32 << bit_at_w) == 0u32) by (bit_vector)
                        requires
                            (bit_at_w as u32) < 32u32,
                    ;
                    assert(set_bit == 0u32);
                    assert(sb == 0u32);
                }
            }
            assert(k == len_total);
            // s_pc: the old storage (plus the pushed zero tail) with the
            // block_at position rewritten by the base update
            assert(pushed ==> s_pc == sO.push(0u32).update(ba as int, new_base));
            assert(!pushed ==> s_pc == sO.update(ba as int, new_base));
            assert forall|w2: usize| (w2 as int) < sO.len() && w2 != ba implies
                #[trigger] s_pc[w2 as int] == sO[w2 as int] by {
                assert(s_pc.len() == sO.len() + (if pushed { 1int } else { 0int }));
            }
            assert(pushed ==> s_pc[L as int] == (if ba == L { new_base } else { 0u32 })) by {
                if pushed {
                    assert(s_pc == sO.push(0u32).update(ba as int, new_base));
                    assert((L as int) == sO.len());
                }
            }
            // full final map: below ba untouched, ba the rewritten base,
            // above ba the shift-cascade values
            assert forall|w2: usize| w2 < len_total implies
                #[trigger] sF[w2 as int] ==
                    (if w2 == ba {
                        new_base
                    } else if w2 > ba {
                        ((s_pc[w2 as int] << 1)
                            | (if w2 == ba + 1 {
                                carry0
                            } else {
                                s_pc[(w2 - 1) as int] >> 31
                            }))
                    } else {
                        s_pc[w2 as int]
                    }) by {
                assert(sF == self.storage@);
                if w2 == ba {
                    assert(self.storage@[w2 as int] == new_base) by {
                        assert(s_pc[w2 as int] == new_base) by {
                            if pushed {
                                assert(s_pc == sO.push(0u32).update(ba as int, new_base));
                            } else {
                                assert(s_pc == sO.update(ba as int, new_base));
                            }
                        }
                    }
                } else if w2 > ba {
                    assert(w2 >= ba + 1);
                    // instantiate the loop-exit cascade fact at its trigger form
                    assert(self.storage@[w2 as int] ==
                        ((s_pc[w2 as int] << 1)
                            | (if w2 == ba + 1 {
                                carry0
                            } else {
                                s_pc[(w2 - 1) as int] >> 31
                            }))) by { }
                } else {
                    // untouched by the base update and the cascade
                    assert(self.storage@[w2 as int] == s_pc[w2 as int]);
                    assert(sF[w2 as int] == s_pc[w2 as int]);
                }
            }
            // structural invariant closure
            assert(len_inv(self)) by {
                assert(sF.len() == len_total as int) by { }
                if pushed {
                    assert(eO == 0);
                    assert(len_total == L + 1);
                    assert(nF == nO + 1);
                    assert(nF % 32 == 1) by {
                        assert(nO == 32 * ((nO as int) / 32));
                    }
                    assert(blocks_for_bits(nF) == (((nF as int) / 32) + 1) as usize) by {
                        assert((nF as int) % 32 == 1);
                    }
                    assert(L == ((nO as int) / 32) as usize) by {
                        assert(blocks_for_bits(nO) == L);
                        assert(blocks_for_bits(nO) == ((nO as int) / 32) as usize) by {
                            assert((nO as int) % 32 == 0);
                        }
                    }
                } else {
                    assert(0 < eO < 32);
                    assert(len_total == L);
                    assert(nF == nO + 1);
                    assert(blocks_for_bits(nO) == L) by { }
                    if eO == 31 {
                        assert((nF as int) % 32 == 0) by {
                            assert(nO as int == 32 * ((nO as int) / 32) + 31);
                            assert((nF as int) == 32 * ((nO as int) / 32) + 32);
                            assert((nF as int) == 32 * (((nF as int) / 32)));
                        }
                        assert(blocks_for_bits(nF) == (((nF as int) / 32)) as usize) by {
                            assert((nF as int) == 32 * ((nF as int) / 32));
                        }
                        assert(((nF as int) / 32) == ((nO as int) / 32 + 1)) by {
                            assert(nO as int == 32 * ((nO as int) / 32) + 31);
                        }
                    } else {
                        assert(eO <= 30);
                        assert((nF as int) % 32 == (1 + (eO as int))) by {
                            assert(nO as int == 32 * ((nO as int) / 32) + eO);
                            assert(1 + (eO as int) < 32);
                        }
                        assert((nF as int) % 32 == (eO + 1) as int);
                        assert(blocks_for_bits(nF)
                            == ((((nF as int) / 32) + 1) as usize)) by {
                            assert((nF as int) % 32 > 0);
                        }
                        assert(((nF as int) / 32) == ((nO as int) / 32)) by {
                            assert(nO as int == 32 * ((nO as int) / 32) + eO);
                        }
                    }
                }
            }
            // trailing-zero closure for the fresh tail
            assert(trailing_zero(self)) by {
                let eF = nF % 32;
                if eF == 0 {
                } else if pushed {
                    assert(eF == 1);
                    let tail = sF[(len_total - 1) as int];
                    if ba == len_total - 1 {
                        assert(tail == new_base);
                        // at == nO: the only position inside the fresh block
                        assert(b == 0) by {
                            assert(ba == (at / 32));
                            assert(b == (at % 32));
                            assert(at <= nO);
                            assert(ba == len_total - 1);
                            assert(len_total == L + 1);
                            assert(L == ((nO as int) / 32) as usize);
                            assert((nO as int) % 32 == 0);
                            assert((nO as int) == 32 * ((nO as int) / 32));
                        }
                        assert(lsbits_mask == 0u32) by {
                            assert(lsbits_mask == ((1u32 << (b as u32)) - 1u32));
                            assert((1u32 << 0u32) - 1u32 == 0u32) by (bit_vector);
                            assert(b == 0);
                        }
                        // ba == L: base is the pushed zero block
                        assert(base == 0u32);
                        assert(new_base == ((base & lsbits_mask)
                            | (((base & (4294967295u32 ^ lsbits_mask)) << 1))
                            | set_bit)) by { }
                        assert(new_base == set_bit) by (bit_vector)
                            requires
                                new_base == ((base & lsbits_mask)
                                    | (((base & (4294967295u32 ^ lsbits_mask)) << 1))
                                    | set_bit),
                                base == 0u32,
                                lsbits_mask == 0u32,
                        ;
                        assert(set_bit <= 1u32) by {
                            if bit {
                                assert(set_bit == (1u32 << bit_at_w));
                                assert(bit_at_w == b);
                                assert((1u32 << bit_at_w) == 1u32) by (bit_vector)
                                    requires
                                        set_bit == (1u32 << bit_at_w),
                                        bit_at_w == 0usize,
                                ;
                            } else {
                                assert((0u32 << bit_at_w) == 0u32) by (bit_vector)
                                    requires
                                        (bit_at_w as u32) < 32u32,
                                ;
                                assert(set_bit == 0u32);
                            }
                        }
                        assert(tail <= 1u32);
                        assert(tail < 2u32);
                        assert(tail < (1u32 << (eF as u32))) by (bit_vector)
                            requires
                                (eF as u32) == 1u32,
                                tail <= 1u32,
                        ;
                    } else {
                        assert(tail ==
                            ((s_pc[(len_total - 1) as int] << 1)
                                | (if (len_total - 1) == ba + 1 {
                                    carry0
                                } else {
                                    s_pc[(len_total - 2) as int] >> 31
                                })));
                        assert(s_pc[(len_total - 1) as int] == 0u32) by {
                            assert(pushed);
                            assert(len_total == L + 1);
                            assert((len_total - 1) as int == sO.len());
                            assert(ba != len_total - 1);
                        }
                        assert((0u32 << 1) == 0u32) by (bit_vector);
                        // the incoming carry is a 0/1 value
                        if (len_total - 1) == ba + 1 {
                            lemma_carry31(base);
                            assert((carry0 & 1u32) == carry0) by (bit_vector)
                                requires
                                    carry0 == base >> 31,
                                    carry0 <= 1u32,
                            ;
                            assert(((0u32 << 1) | carry0) <= 1u32) by (bit_vector)
                                requires
                                    carry0 <= 1u32,
                            ;
                        } else {
                            lemma_carry31(s_pc[(len_total - 2) as int]);
                            let cval: u32 = s_pc[(len_total - 2) as int] >> 31;
                            assert((cval & 1u32) == cval) by (bit_vector)
                                requires
                                    cval <= 1u32,
                            ;
                            assert(((0u32 << 1) | cval) <= 1u32) by (bit_vector)
                                requires
                                    cval <= 1u32,
                            ;
                        }
                        assert(tail <= 1u32);
                        assert(tail < (1u32 << (eF as u32))) by (bit_vector)
                            requires
                                (eF as u32) == 1u32,
                                tail <= 1u32,
                        ;
                    }
                } else {
                    assert(1 <= eO <= 30);
                    assert(eF == eO + 1);
                    let tail = sF[(len_total - 1) as int];
                    assert((len_total - 1) as int == L - 1);
                    if ba == len_total - 1 {
                        assert(tail == new_base);
                        assert(base < (1u32 << eO)) by {
                            assert(trailing_zero(old(self)));
                            assert((L - 1) as int == blocks_for_bits(nO) - 1);
                        }
                        assert(b <= eO) by {
                            assert(at <= nO);
                            assert(ba == (at / 32));
                            assert(b == (at % 32));
                            if at < nO {
                                assert(at <= nO - 1);
                                assert((L - 1) as int == (nO as int) / 32);
                                assert(b < eO);
                            } else {
                                assert(b <= eO);
                            }
                        }
                        lemma_insert_block_below(base, b, eO, sb, lsbits_mask);
                        assert(lsbits_mask == ((1u32 << (b as u32)) - 1u32));
                        assert(tail < (1u32 << (eO + 1)));
                        assert(trailing_zero(self)) by {
                            assert(sF[(blocks_for_bits(nF) - 1) as int] < (1u32 << (nF % 32)));
                            assert((blocks_for_bits(nF) - 1) as int == (len_total - 1) as int);
                        }
                    } else {
                        assert(tail ==
                            ((s_pc[(len_total - 1) as int] << 1)
                                | (if (len_total - 1) == ba + 1 {
                                    carry0
                                } else {
                                    s_pc[(len_total - 2) as int] >> 31
                                })));
                        assert(s_pc[(len_total - 1) as int] == sO[(L - 1) as int]) by {
                            assert((len_total - 1) as int != ba) by {
                                assert(ba != len_total - 1);
                            }
                        }
                        assert(sO[(L - 1) as int] < (1u32 << eO)) by {
                            assert(trailing_zero(old(self)));
                            assert((L - 1) as int == blocks_for_bits(nO) - 1);
                        }
                        if (len_total - 1) == ba + 1 {
                            lemma_carry31(base);
                            lemma_shiftup_below(sO[(L - 1) as int], carry0, eO);
                        } else {
                            lemma_carry31(s_pc[(len_total - 2) as int]);
                            lemma_shiftup_below(sO[(L - 1) as int],
                                s_pc[(len_total - 2) as int] >> 31, eO);
                        }
                        assert(tail < (1u32 << (eO + 1)));
                        assert(trailing_zero(self)) by {
                            assert(sF[(blocks_for_bits(nF) - 1) as int] < (1u32 << (nF % 32)));
                            assert((blocks_for_bits(nF) - 1) as int == (len_total - 1) as int);
                        }
                    }
                }
            }
            assert(inv(final(self)));
            // extra frames for the per-bit semantics lemma
            assert(len_total as int == blocks_for_bits(nF) as int) by {
                assert(len_inv(self));
                assert(sF.len() == len_total as int);
                assert(self.nbits == nF);
            }
            assert(sO.len() == blocks_for_bits(nO) as int) by {
                assert(len_inv(old(self)));
                assert(sO.len() == (old(self).storage@).len());
            }
            assert(sO.len() <= len_total as int) by {
                if !pushed {
                    assert(len_total == L);
                } else {
                    assert(len_total == L + 1);
                }
            }
            // base vs the old sequence entry (frame for the semantics lemma)
            if (ba as int) < sO.len() {
                assert(base == sO[ba as int]);
            } else {
                // the fresh pushed zero block (pre-rewrite frame facts)
                assert(base == 0u32);
            }
            insert_bit_semantics(sF, s_pc, sO, nF, nO, ba, b, carry0, new_base,
                sb, lsbits_mask, base, at, len_total);
            // the set bit value carries the inserted boolean
            assert(bit_at(final(self).storage@, final(self).nbits, at) == bit) by {
                if bit {
                    assert(set_bit == (1u32 << bit_at_w));
                    assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32)) by { }
                    assert(set_bit != 0u32) by (bit_vector)
                        requires
                            set_bit == (1u32 << (bit_at_w as u32)),
                            (bit_at_w as u32) < 32u32,
                    ;
                } else {
                    assert((0u32 << bit_at_w) == 0u32) by (bit_vector)
                        requires
                            (bit_at_w as u32) < 32u32,
                    ;
                    assert(set_bit == 0u32);
                }
                assert(sb == set_bit);
                assert(set_bit != 0u32 == bit);
            }
        }
    }

    /// Origin Rust: pub fn remove(&mut self, at: usize) -> bool (lib.rs:1951-1986)
    ///     { assert!(at < self.nbits, "removal index ...");
    ///       self.ensure_invariant();
    ///       self.nbits -= 1;
    ///       let last_block_bits = self.nbits % B::bits();
    ///       let block_at = at / B::bits();
    ///       let bit_at = at % B::bits();
    ///       let lsbits_mask = (B::one() << bit_at) - B::one();
    ///       let mut carry = B::zero();
    ///       for block_ref in self.storage[block_at + 1..].iter_mut().rev() {
    ///           let curr_carry = *block_ref & B::one();
    ///           *block_ref = *block_ref >> 1 | (carry << (B::bits() - 1));
    ///           carry = curr_carry; }
    ///       let result = (self.storage[block_at] >> bit_at) & B::one() == B::one();
    ///       self.storage[block_at] = (self.storage[block_at] & lsbits_mask)
    ///           | ((self.storage[block_at] & (!lsbits_mask << 1)) >> 1)
    ///           | carry << (B::bits() - 1);
    ///       if last_block_bits == 0 { self.storage.pop(); }
    ///       result }
    ///     # Panics (assert) -> requires; the reversed slice iterator is a
    ///     descending block index loop (same order); the spec `!` is
    ///     materialized as XOR all-ones (negate precedent); upstream's
    ///     repeated self.storage[block_at] reads are one read (same value).
    /// Upstream doc (lib.rs:1930-1950):
    ///   Remove a bit at index `at`, shifting all bits after by one.
    ///   # Panics
    ///   Panics if `at` is out of bounds for `BitVec`'s length (that is, if `at >= BitVec::len()`)
    ///   # Time complexity
    ///   Takes O([`len`]) time. All items after the removal index must be
    ///   shifted to the left. In the worst case, all elements are shifted when
    ///   the removal index is 0.
    pub exec fn remove(&mut self, at: usize) -> (result: bool)
        requires
            inv(old(self)),
            at < old(self).nbits,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits - 1,
            final(self).storage@.len() == (if old(self).nbits % 32 == 1 {
                old(self).storage@.len() - 1
            } else {
                old(self).storage@.len() as int
            }),
            result == bit_at(old(self).storage@, old(self).nbits, at),
            forall|j: usize|
                j < at ==> bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            forall|j: usize|
                at <= j && j < final(self).nbits ==>
                #[trigger] bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, (j + 1) as usize),
    {
        let block_at = at / 32;
        let bit_at_w = at % 32;
        /* Origin Rust: self.nbits -= 1; (no underflow: at < old nbits) */
        self.nbits = self.nbits - 1;
        let last_block_bits = self.nbits % 32;
        proof {
            assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32)) by { }
            assert((1u32 << (bit_at_w as u32)) != 0u32) by (bit_vector)
                requires
                    (bit_at_w as u32) < 32u32,
            ;
        }
        let lsbits_mask = ((1u32 << bit_at_w) - 1u32) as u32;
        let len_total = self.storage.len();
        proof {
            assert(len_total >= 1) by {
                assert(len_inv(old(self)));
                assert(blocks_for_bits(old(self).nbits) >= 1);
            }
        }
        let mut carry: u32 = 0u32;
        /* Origin Rust: for block_ref in self.storage[block_at + 1..].iter_mut().rev()
           (descending block index loop, same order). */
        let ghost mut s_pre: Seq<u32> = Seq::empty();
        proof {
            s_pre = self.storage@;
            assert(s_pre == old(self).storage@);
        }
        let mut k: usize = (len_total - 1) as usize;
        while k > block_at
            invariant
                block_at <= k,
                k <= (len_total - 1) as usize,
                self.storage@.len() == len_total,
                s_pre.len() == len_total as int,
                self.nbits == old(self).nbits - 1,
                // blocks cascaded so far: those strictly above k
                forall|w2: usize| k < w2 && w2 < len_total ==>
                    #[trigger] self.storage@[w2 as int] == rem_cascade(s_pre, w2, len_total),
                // blocks not yet processed: block_at < w2 <= k
                forall|w2: usize| block_at < w2 && w2 <= k ==>
                    #[trigger] self.storage@[w2 as int] == s_pre[w2 as int],
                // blocks at and below block_at
                forall|w2: usize| w2 <= block_at ==>
                    #[trigger] self.storage@[w2 as int] == s_pre[w2 as int],
                carry == if k == (len_total - 1) as usize {
                    0u32
                } else {
                    s_pre[(k + 1) as int] & 1u32
                },
            decreases
                k,
        {
            let ghost mut s_head: Seq<u32> = Seq::empty();
            proof {
                s_head = self.storage@;
                assert(s_head[k as int] == s_pre[k as int]);
            }
            let curr = self.storage[k];
            let curr_carry = curr & 1u32;
            proof {
                assert(curr == s_pre[k as int]);
                if k == (len_total - 1) as usize {
                    assert(carry == 0u32);
                    assert((0u32 << 31) == 0u32) by (bit_vector);
                } else {
                    assert(carry == s_pre[(k + 1) as int] & 1u32);
                }
            }
            self.storage.set(k, (curr >> 1) | (carry << 31));
            proof {
                assert(self.storage@ == s_head.update(k as int, (curr >> 1) | (carry << 31)));
                // position k takes the cascade form
                assert(((curr >> 1) | (carry << 31))
                    == rem_cascade(s_pre, k, len_total)) by {
                    if k == (len_total - 1) as usize {
                        assert(carry == 0u32);
                        assert((0u32 << 31) == 0u32) by (bit_vector);
                    } else {
                        assert(carry == s_pre[(k + 1) as int] & 1u32);
                    }
                }
                // untouched positions keep the pre-cascade values
                assert forall|w2: usize| (k - 1) < w2 && w2 < len_total implies
                    #[trigger] self.storage@[w2 as int] == rem_cascade(s_pre, w2, len_total) by {
                    if w2 == k {
                        assert(self.storage@[w2 as int] == (curr >> 1) | (carry << 31));
                    } else {
                        assert(self.storage@[w2 as int] == s_head[w2 as int]);
                    }
                }
                assert forall|w2: usize| block_at < w2 && w2 <= (k - 1) implies
                    #[trigger] self.storage@[w2 as int] == s_pre[w2 as int] by {
                    assert(self.storage@[w2 as int] == s_head[w2 as int]);
                }
                assert forall|w2: usize| w2 <= block_at implies
                    #[trigger] self.storage@[w2 as int] == s_pre[w2 as int] by {
                    assert(self.storage@[w2 as int] == s_head[w2 as int]);
                }
            }
            carry = curr_carry;
            k = (k - 1) as usize;
        }
        let base = self.storage[block_at];
        proof {
            assert(k == block_at);
            // the base block is untouched by the cascade
            assert(base == s_pre[block_at as int]);
            assert(lsbits_mask == ((1u32 << (bit_at_w as u32)) - 1u32));
            assert(s_pre == old(self).storage@);
        }
        let result = (base >> bit_at_w) & 1u32 == 1u32;
        proof {
            lemma_remove_result_bit(base, bit_at_w);
            assert(bit_at(old(self).storage@, old(self).nbits, at)
                == ((old(self).storage@[(at / 32) as int] & (1u32 << (at % 32))) != 0u32)) by { }
            assert((at / 32) == block_at);
            assert((at % 32) == bit_at_w);
            assert(s_pre[(at / 32) as int] == old(self).storage@[(at / 32) as int]);
            assert(1u32 << (at % 32) == 1u32 << ((at % 32) as u32));
            assert(((base >> bit_at_w) & 1u32) == ((base >> (bit_at_w as u32)) & 1u32)) by { }
            assert((((base >> (bit_at_w as u32)) & 1u32) != 0u32)
                == (((base >> (bit_at_w as u32)) & 1u32) == 1u32)) by (bit_vector);
            assert((((base >> bit_at_w) & 1u32) != 0u32) == result) by { }
            assert(((base & (1u32 << bit_at_w)) != 0u32) == result) by {
                assert((((base >> bit_at_w) & 1u32) != 0u32)
                    == (((base & (1u32 << bit_at_w)) != 0u32)));
                assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32));
            }
        }
        let carry_in = carry;
        /* Origin Rust: self.storage[block_at] = (self.storage[block_at] & lsbits_mask)
           | ((self.storage[block_at] & (!lsbits_mask << 1)) >> 1)
           | carry << (B::bits() - 1);
           (`!` materialized as XOR all-ones; repeated reads are one read) */
        let new_base = (base & lsbits_mask)
            | ((base & ((4294967295u32 ^ lsbits_mask) << 1)) >> 1)
            | (carry_in << 31);
        let ghost mut pre_set: Seq<u32> = Seq::empty();
        proof {
            pre_set = self.storage@;
        }
        /* Origin Rust: self.storage.set(block_at, rewrite) */
        self.storage.set(block_at, new_base);
        proof {
            assert(self.storage@ == pre_set.update(block_at as int, new_base));
        }
        // the incoming carry is the neighbor block's old bit 0 (or zero)
        proof {
            assert(carry_in == rem_carry_in(s_pre, block_at, len_total)) by {
                if k == (len_total - 1) as usize {
                    assert(block_at == len_total - 1);
                    assert(carry_in == 0u32);
                    assert((block_at + 1) == len_total);
                } else {
                    assert(carry_in == s_pre[(k + 1) as int] & 1u32);
                    assert((k + 1) == block_at + 1);
                }
            }
        }
        let ghost mut pre_pop: Seq<u32> = Seq::empty();
        proof {
            pre_pop = self.storage@;
            // pre_pop is the post-set sequence: the cascade map with the
            // base position rewritten
            assert forall|w2: usize| (w2 as int) < len_total implies
                #[trigger] pre_pop[w2 as int] ==
                    (if (w2 as int) == (block_at as int) {
                        new_base
                    } else {
                        pre_set[w2 as int]
                    }) by {
                if (w2 as int) == (block_at as int) {
                    // the base update position
                } else {
                    // the cascade left positions below/at/above untouched
                    assert(pre_pop[w2 as int] == pre_set[w2 as int]);
                }
            }
            assert forall|w2: usize| (w2 as int) < len_total implies
                #[trigger] pre_set[w2 as int] ==
                    (if (w2 as int) < (block_at as int) {
                        s_pre[w2 as int]
                    } else if (w2 as int) == (block_at as int) {
                        s_pre[w2 as int]
                    } else {
                        rem_cascade(s_pre, w2, len_total)
                    }) by {
                if (w2 as int) <= (block_at as int) {
                } else {
                }
            }
        }
        /* Origin Rust: if last_block_bits == 0 { self.storage.pop(); } */
        if last_block_bits == 0 {
            self.storage.pop();
        }
        proof {
            let sF = self.storage@;
            let sO = old(self).storage@;
            let nO = old(self).nbits;
            let nF = self.nbits;
            let eO = nO % 32;
            let ba = block_at;
            let b = bit_at_w;
            let eF = nF % 32;
            assert(sO.len() == len_total as int) by { }
            assert(sF.len() <= len_total as int) by { }
            // the final sequence: pop keeps the surviving prefix
            if last_block_bits == 0 {
                assert(eO == 1);
                assert(sF.len() == len_total as int - 1) by {
                    assert(len_total >= 1);
                }
                assert(sF == pre_pop.subrange(0, (len_total - 1) as int)) by { }
                assert forall|w2: usize| (w2 as int) < len_total as int - 1 implies
                    #[trigger] sF[w2 as int] == pre_pop[w2 as int] by {
                    assert(pre_pop.subrange(0, (len_total - 1) as int)[w2 as int]
                        == pre_pop[w2 as int]);
                }
            } else {
                assert(eO != 1);
                assert(sF == pre_pop) by { }
                assert forall|w2: usize| (w2 as int) < len_total implies
                    #[trigger] sF[w2 as int] == pre_pop[w2 as int] by { }
            }
            // the final position map (valid surviving positions only)
            assert forall|w2: usize| (w2 as int) < sF.len() implies
                #[trigger] sF[w2 as int] ==
                    (if w2 == ba {
                        new_base
                    } else if (w2 as int) > (ba as int) {
                        rem_cascade(sO, w2, len_total)
                    } else {
                        sO[w2 as int]
                    }) by {
                assert(s_pre == sO);
                if (w2 as int) < (ba as int) {
                    assert(sF[w2 as int] == pre_pop[w2 as int]);
                    assert(pre_pop[w2 as int] == pre_set[w2 as int]);
                    assert(pre_set[w2 as int] == s_pre[w2 as int]);
                } else if (w2 as int) == (ba as int) {
                    assert(sF[w2 as int] == pre_pop[w2 as int]);
                    assert(pre_pop[w2 as int] == new_base);
                } else {
                    assert(sF[w2 as int] == pre_pop[w2 as int]);
                    assert(pre_pop[w2 as int] == pre_set[w2 as int]);
                    assert(pre_set[w2 as int] == rem_cascade(s_pre, w2, len_total));
                }
            }
            // structural invariant: storage length tracks blocks_for_bits
            assert(len_inv(self)) by {
                assert(blocks_for_bits(nO) == len_total) by {
                    assert(len_inv(old(self)));
                }
                if eO == 1 {
                    assert(eF == 0);
                    assert((nF as int) % 32 == 0);
                    assert(blocks_for_bits(nF) == ((nF as int) / 32) as usize) by {
                        assert((nF as int) % 32 == 0);
                    }
                    assert((nF as int) / 32 == len_total as int - 1) by {
                        assert(nO as int == 32 * ((len_total as int) - 1) + 1);
                        assert(nF as int == nO as int - 1);
                    }
                } else if eO == 0 {
                    assert(eF == 31);
                    assert((nF as int) % 32 == 31);
                    assert(blocks_for_bits(nF) == ((((nF as int) / 32) + 1) as usize)) by {
                        assert((nF as int) % 32 > 0);
                    }
                    assert((nF as int) / 32 == len_total as int - 1) by {
                        assert(nO as int == 32 * (len_total as int));
                        assert(nF as int == nO as int - 1);
                    }
                } else {
                    assert(2 <= eO <= 31);
                    assert(eF == eO - 1) by {
                        assert(nO as int == 32 * ((nO as int) / 32) + eO);
                        assert(nF as int == nO as int - 1);
                    }
                    assert((nF as int) % 32 > 0);
                    assert(blocks_for_bits(nF) == ((((nF as int) / 32) + 1) as usize)) by {
                        assert((nF as int) % 32 > 0);
                    }
                    assert((nF as int) / 32 == (nO as int) / 32) by {
                        assert(nO as int == 32 * ((nO as int) / 32) + eO);
                        assert(nF as int == nO as int - 1);
                    }
                    assert(((nO as int) / 32) + 1 == len_total as int) by {
                        assert(len_inv(old(self)));
                        assert(blocks_for_bits(nO) == (((nO as int) / 32) + 1) as usize) by {
                            assert((nO as int) % 32 > 0);
                        }
                    }
                }
            }
            // trailing-zero closure for the surviving tail
            assert(trailing_zero(self)) by {
                if eF == 0 {
                } else if eO == 0 {
                    assert(eF == 31);
                    let tail = sF[((len_total - 1) as int)];
                    assert((len_total - 1) as int == blocks_for_bits(nF) - 1) by { }
                    if ba == len_total - 1 {
                        assert(tail == new_base);
                        assert(carry_in == 0u32) by {
                            assert(carry_in == rem_carry_in(s_pre, ba, len_total));
                            assert((ba + 1) == len_total);
                        }
                        assert(lsbits_mask == ((1u32 << (b as u32)) - 1u32));
                        lemma_remove_block_top(base, b, carry_in, lsbits_mask);
                        assert(tail < (1u32 << 31u32));
                        assert(tail < (1u32 << (nF % 32)));
                        assert(trailing_zero(self)) by { }
                    } else {
                        assert(tail == rem_cascade(s_pre, (len_total - 1) as usize, len_total)) by { }
                        let ot0: u32 = s_pre[((len_total - 1) as int)];
                        let tt0: u32 = (ot0 >> 1) | (0u32 << 31);
                        assert(rem_cascade(s_pre, (len_total - 1) as usize, len_total) == tt0) by {
                            assert((((len_total - 1) as usize) + 1) == len_total);
                            assert((0u32 << 31) == 0u32) by (bit_vector);
                        }
                        assert(tail == tt0) by { }
                        assert(tt0 < (1u32 << 31u32)) by (bit_vector)
                            requires
                                tt0 == ((ot0 >> 1) | (0u32 << 31)),
                        ;
                        assert(tail < (1u32 << 31u32));
                        assert(tail < (1u32 << (nF % 32)));
                        assert(trailing_zero(self)) by { }
                    }
                } else {
                    // 2 <= eO <= 31, no pop: the tail shifts down one tier
                    assert(2 <= eO <= 31);
                    assert(eF == eO - 1);
                    let tail = sF[((len_total - 1) as int)];
                    assert((len_total - 1) as int == blocks_for_bits(nF) - 1) by { }
                    if ba == len_total - 1 {
                        assert(tail == new_base);
                        assert(base < (1u32 << eO)) by {
                            assert(trailing_zero(old(self)));
                            assert((len_total - 1) as int == blocks_for_bits(nO) - 1);
                        }
                        assert(b < eO) by {
                            assert(at <= nO - 1);
                            assert(ba == (at / 32));
                            assert(b == (at % 32));
                            assert(nO as int == 32 * ((len_total - 1) as int) + eO);
                        }
                        assert(carry_in == 0u32) by {
                            assert(carry_in == rem_carry_in(s_pre, ba, len_total));
                            assert((ba + 1) == len_total);
                        }
                        assert(lsbits_mask == ((1u32 << (b as u32)) - 1u32));
                        lemma_remove_block_below(base, b, eO, carry_in, lsbits_mask);
                        assert(tail < (1u32 << (eO - 1)));
                        assert(tail < (1u32 << (nF % 32)));
                        assert(trailing_zero(self)) by { }
                    } else {
                        let old_tail = s_pre[(len_total - 1) as int];
                        assert(old_tail < (1u32 << eO)) by {
                            assert(trailing_zero(old(self)));
                            assert((len_total - 1) as int == blocks_for_bits(nO) - 1);
                        }
                        assert(tail == rem_cascade(s_pre, (len_total - 1) as usize, len_total)) by { }
                        let tt1: u32 = (old_tail >> 1) | (0u32 << 31);
                        assert(rem_cascade(s_pre, (len_total - 1) as usize, len_total) == tt1) by {
                            assert((((len_total - 1) as usize) + 1) == len_total);
                            assert((0u32 << 31) == 0u32) by (bit_vector);
                        }
                        assert(tail == tt1) by { }
                        assert((0u32 << 31) == 0u32) by (bit_vector);
                        assert(tt1 == ((old_tail >> 1) | (0u32 << 31))) by { }
                        lemma_shiftdown_below(old_tail, 0u32, eO);
                        assert(tail < (1u32 << (eO - 1)));
                        assert(tail < (1u32 << (nF % 32)));
                        assert(trailing_zero(self)) by { }
                    }
                }
            }
            assert(inv(final(self)));
            // per-bit semantics closure
            assert(nF == nO - 1);
            assert(sO.len() == len_total as int);
            assert(len_total as int == blocks_for_bits(nO) as int);
            assert(sF.len() == blocks_for_bits(nF) as int);
            assert(len_inv(old(self)));
            assert(s_pre == sO);
            remove_bit_semantics(sF, s_pre, nF, nO, ba, b, base, new_base,
                carry_in, lsbits_mask, at, len_total);
            // the exec-level postconditions are in old-storage terms
            assert(s_pre == old(self).storage@);
        }
        result
    }

    /// Origin Rust: pub fn with_capacity(capacity: usize) -> Self
    ///     { BitVec::<u32>::with_capacity_general(capacity) } (lib.rs:472-475)
    ///     The "at least capacity bits" tier lives in the Vec allocation
    ///     layer, where vstd carries no capacity value (see the injected
    ///     assume_specification in this file; only the entries view is
    ///     asserted, the reallocation-free tier is not).
    /// Upstream doc (lib.rs:465-471):
    ///   Constructs a new, empty `BitVec` with the specified capacity.
    ///   The bitvector will be able to hold at least `capacity` bits without
    ///   reallocating. If `capacity` is 0, it will not allocate.
    ///   It is important to note that this function does not specify the
    ///   *length* of the returned bitvector, but only the *capacity*.
    pub exec fn with_capacity(capacity: usize) -> (bv: BitVec)
        ensures
            inv(&bv),
            bv.nbits == 0,
            bv.storage@ == Seq::<u32>::empty(),
    {
        Self::with_capacity_general(capacity)
    }

    /// Origin Rust: pub fn with_capacity_general(capacity: usize) -> Self
    ///     { BitVec { storage: Vec::with_capacity(blocks_for_bits::<B>(capacity)),
    ///       nbits: 0 } } (lib.rs:563-570; the capacity tier note as with_capacity;
    ///       blocks_for_bits called through the exec bridge)
    /// Upstream doc (lib.rs:555-561):
    ///   Constructs a new, empty `BitVec` with the specified capacity.
    ///   The bitvector will be able to hold at least `capacity` bits without
    ///   reallocating. If `capacity` is 0, it will not allocate.
    ///   It is important to note that this function does not specify the
    ///   *length* of the returned bitvector, but only the *capacity*.
    pub exec fn with_capacity_general(capacity: usize) -> (bv: BitVec)
        ensures
            inv(&bv),
            bv.nbits == 0,
            bv.storage@ == Seq::<u32>::empty(),
    {
        BitVec { storage: Vec::with_capacity(blocks_for_bits_exec(capacity)), nbits: 0 }
    }

    /// Origin Rust: pub fn reserve(&mut self, additional: usize) (lib.rs:1631-1644)
    ///     { let desired_cap = self.len().checked_add(additional)
    ///         .expect("capacity overflow");
    ///       let storage_len = self.storage.len();
    ///       if desired_cap > self.capacity() {
    ///           self.storage
    ///               .reserve(blocks_for_bits::<B>(desired_cap) - storage_len); } }
    ///     # Panics ("capacity overflow") -> requires (the checked_add tier,
    ///     documented); the reserve-argument subtraction cannot underflow:
    ///     taking the branch forces desired_cap > capacity == 32 * storage
    ///     blocks (the saturating tier yields capacity == usize::MAX, which
    ///     no desired_cap exceeds, so the branch is unreachable there), so
    ///     blocks_for_bits(desired_cap) > storage_len. The practical-domain
    ///     bound for that arithmetic is carried as requires (a store of
    ///     more than 2^59 blocks is not realizable memory).
    /// Upstream doc (lib.rs:1614-1630):
    ///   Reserves capacity for at least `additional` more bits to be inserted in the given
    ///   `BitVec`. The collection may reserve more space to avoid frequent reallocations.
    ///   # Panics
    ///   Panics if the new capacity overflows `usize`.
    pub exec fn reserve(&mut self, additional: usize)
        requires
            inv(old(self)),
            (old(self).nbits as int + additional as int) < usize::MAX as int,
            32 * (old(self).storage@.len()) <= usize::MAX as int,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@ == old(self).storage@,
            final(self).storage@.len() == old(self).storage@.len(),
    {
        /* Origin Rust: let desired_cap = self.len().checked_add(additional)
           .expect("capacity overflow"); */
        let desired_cap = self.nbits + additional;
        proof {
            assert((desired_cap as int) == (self.nbits as int) + (additional as int));
        }
        let storage_len = self.storage.len();
        if desired_cap > self.capacity() {
            proof {
                // the branch rules out the saturating capacity tier
                assert((desired_cap as int) > (spec_bit_capacity(self) as int));
                assert((spec_bit_capacity(self) as int) != (usize::MAX as int));
                assert((spec_vec_capacity(&self.storage) as int) * 32
                    <= usize::MAX as int);
                assert((spec_bit_capacity(self) as int)
                    == 32 * (spec_vec_capacity(&self.storage) as int));
                assert((spec_vec_capacity(&self.storage)) as int
                    >= (self.storage@.len() as int));
                assert((desired_cap as int) > 32 * (self.storage@.len() as int));
                assert((desired_cap as int) >= 32 * (self.storage@.len() as int) + 1);
            }
            /* Origin Rust: self.storage.reserve(blocks_for_bits::<B>(desired_cap)
               - storage_len); */
            let extra = blocks_for_bits_exec(desired_cap) - storage_len;
            proof {
                assert((blocks_for_bits(desired_cap) as int)
                    >= (storage_len as int) + 1) by {
                    assert((desired_cap as int) / 32 >= (storage_len as int));
                }
                assert((extra as int) >= 1);
            }
            self.storage.reserve(extra);
        }
    }

    /// The obligation surface equals reserve's (the same ropework subtrace
    /// under Vec::reserve_exact's injected entries-view spec).
    /// Origin Rust: pub fn reserve_exact(&mut self, additional: usize) (lib.rs:1666-1678)
    ///     { ... the identical shape with reserve_exact ... }
    /// Upstream doc (lib.rs:1633-1664):
    ///   Reserves the minimum capacity for exactly `additional` more bits to be inserted in the
    ///   given `BitVec`. Does nothing if the capacity is already sufficient.
    ///   Note that the allocator may give the collection more space than it requests. Therefore
    ///   capacity can not be relied upon to be precisely minimal. Prefer `reserve` if future
    ///   insertions are expected.
    ///   # Panics
    ///   Panics if the new capacity overflows `usize`.
    pub exec fn reserve_exact(&mut self, additional: usize)
        requires
            inv(old(self)),
            (old(self).nbits as int + additional as int) < usize::MAX as int,
            32 * (old(self).storage@.len()) <= usize::MAX as int,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@ == old(self).storage@,
            final(self).storage@.len() == old(self).storage@.len(),
    {
        /* Origin Rust: let desired_cap = self.len().checked_add(additional)
           .expect("capacity overflow"); */
        let desired_cap = self.nbits + additional;
        proof {
            assert((desired_cap as int) == (self.nbits as int) + (additional as int));
        }
        let storage_len = self.storage.len();
        if desired_cap > self.capacity() {
            proof {
                assert((desired_cap as int) > (spec_bit_capacity(self) as int));
                assert((spec_bit_capacity(self) as int) != (usize::MAX as int));
                assert((spec_vec_capacity(&self.storage) as int) * 32
                    <= usize::MAX as int);
                assert((spec_bit_capacity(self) as int)
                    == 32 * (spec_vec_capacity(&self.storage) as int));
                assert((spec_vec_capacity(&self.storage)) as int
                    >= (self.storage@.len() as int));
                assert((desired_cap as int) > 32 * (self.storage@.len() as int));
                assert((desired_cap as int) >= 32 * (self.storage@.len() as int) + 1);
            }
            /* Origin Rust: self.storage.reserve_exact(blocks_for_bits::<B>(desired_cap)
               - storage_len); */
            let extra = blocks_for_bits_exec(desired_cap) - storage_len;
            proof {
                assert((blocks_for_bits(desired_cap) as int)
                    >= (storage_len as int) + 1) by {
                    assert((desired_cap as int) / 32 >= (storage_len as int));
                }
                assert((extra as int) >= 1);
            }
            self.storage.reserve_exact(extra);
        }
    }

    /// Origin Rust: pub fn capacity(&self) -> usize
    ///     { self.storage.capacity().saturating_mul(B::bits()) } (lib.rs:1691-1698)
    ///     The value spec rides on the injected capacity model; under the
    ///     practical-domain bound (no 2^59-block store exists) the bit
    ///     capacity covers the storage length 32-fold.
    /// Upstream doc (lib.rs:1678-1689):
    ///   Returns the capacity in bits for this bit vector. Inserting any
    ///   element less than this amount will not trigger a resizing.
    pub exec fn capacity(&self) -> (r: usize)
        ensures
            r == spec_bit_capacity(self),
            32 * (self.storage@.len()) <= usize::MAX as int ==>
                (r as int) >= 32 * (self.storage@.len() as int),
    {
        /* Origin Rust: self.storage.capacity().saturating_mul(B::bits()) */
        let c = self.storage.capacity();
        proof {
            assert(spec_vec_capacity(&self.storage) == c);
        }
        let r2 = c.saturating_mul(32);
        proof {
            assert(r2 == spec_sat_mul32(c)) by { }
        }
        r2
    }

    /// The ok-branch reuses the push semantics (nbits + 1; old bits keep
    /// their values; the fresh tail carries the bit); the err-branch
    /// leaves the vector unchanged. The capacity read uses the pre-change
    /// value, which the injected model pins at spec_bit_capacity(old).
    /// Origin Rust: pub fn push_within_capacity(&mut self, bit: bool) -> Result<(), bool>
    ///     { let len = self.len();
    ///       if len == self.capacity() { return Err(bit); }
    ///       let bits = B::bits();
    ///       if len % bits == 0 { self.storage.push(B::zero()); }
    ///       let block_at = len / B::bits();
    ///       let bit_at = len % B::bits();
    ///       let flag = if bit { B::one() << bit_at } else { B::zero() };
    ///       self.nbits += 1;
    ///       self.storage[block_at] |= flag;
    ///       self.ensure_invariant();
    ///       Ok(()) } (lib.rs:2032-2059; `|= flag` is one read plus the set
    ///       rewrite; ensure_invariant() is a no-op here -- the invariant
    ///       is proven in place)
    /// Upstream doc (lib.rs:2000-2030):
    ///   Appends an element if there is sufficient spare capacity, otherwise an error is returned
    ///   with the element.
    ///   Unlike [`push`] this method will not reallocate when there's insufficient capacity.
    ///   The caller should use [`reserve`] to ensure that there is enough capacity.
    ///   # Time Complexity
    ///   Takes *O(1)* time.
    pub exec fn push_within_capacity(&mut self, bit: bool) -> (r: Result<(), bool>)
        requires
            old(self).nbits < usize::MAX,
            inv(old(self)),
            old(self).nbits < usize::MAX,
        ensures
            inv(final(self)),
            old(self).nbits == spec_bit_capacity(old(self)) ==>
                r is Err
                && r.get_Err_0() == bit
                && final(self).nbits == old(self).nbits
                && final(self).storage@ == old(self).storage@,
            old(self).nbits != spec_bit_capacity(old(self)) ==>
                (r is Ok
                    && final(self).nbits == old(self).nbits + 1
                    && final(self).storage@.len() == (if old(self).nbits % 32 == 0 {
                        old(self).storage@.len() + 1
                    } else {
                        old(self).storage@.len()
                    })),
            old(self).nbits != spec_bit_capacity(old(self)) ==>
                forall|j: usize|
                    j < old(self).nbits ==>
                    bit_at(final(self).storage@, final(self).nbits, j)
                        == bit_at(old(self).storage@, old(self).nbits, j),
            old(self).nbits != spec_bit_capacity(old(self)) ==>
                bit_at(final(self).storage@, final(self).nbits,
                    (final(self).nbits - 1) as usize) == bit,
    {
        /* Origin Rust: let len = self.len(); if len == self.capacity()
           { return Err(bit); } */
        let len = self.nbits;
        let cap = self.capacity();
        proof {
            assert(cap == spec_bit_capacity(old(self)));
        }
        if len == cap {
            return Err(bit);
        }
        /* Origin Rust: let bits = B::bits(); if len % bits == 0
           { self.storage.push(B::zero()); } */
        if len % 32 == 0 {
            self.storage.push(0u32);
            proof {
                assert(len_inv(old(self)));
                assert(self.storage@ == old(self).storage@.push(0u32));
            }
        }
        let block_at = len / 32;
        let bit_at_w = len % 32;
        /* Origin Rust: let flag = if bit { B::one() << bit_at } else { B::zero() }; */
        let flag: u32 = if bit { 1u32 << bit_at_w } else { 0u32 };
        /* Origin Rust: self.nbits += 1; */
        self.nbits = self.nbits + 1;
        /* Origin Rust: self.storage[block_at] |= flag; // set the bit */
        let oldv = self.storage[block_at];
        let ghost mut s_pre: Seq<u32> = Seq::empty();
        proof {
            s_pre = self.storage@;
            let nO = old(self).nbits;
            let eO = nO % 32;
            let L = old(self).storage@.len();
            assert(len == nO);
            // the target block is the old tail or the freshly pushed one
            if eO == 0 {
                assert((block_at as int) == L as int) by {
                    int_div_bound_lemma(len, (nO + 1) as usize);
                    assert(len_inv(old(self)));
                    assert((nO as int) == 32 * (L as int));
                }
                assert(s_pre == old(self).storage@.push(0u32));
                assert(s_pre[L as int] == 0u32);
                assert(oldv == 0u32);
            } else {
                assert((block_at as int) == (L - 1) as int) by {
                    int_div_bound_lemma(len, (nO + 1) as usize);
                    assert(len_inv(old(self)));
                    assert((nO as int) == 32 * ((L - 1) as int) + eO);
                }
                assert(s_pre == old(self).storage@);
                assert(s_pre[(L - 1) as int] == old(self).storage@[(L - 1) as int]);
                assert(oldv == old(self).storage@[(L - 1) as int]);
            }
        }
        self.storage.set(block_at, oldv | flag);
        /* Origin Rust: self.ensure_invariant(); */
        proof {
            let nO = old(self).nbits;
            let eO = nO % 32;
            let L = old(self).storage@.len();
            let sF = self.storage@;
            let sO = old(self).storage@;
            let nF = self.nbits;
            let eF = nF % 32;
            let nv = oldv | flag;
            assert(len == nO);
            assert(nF == nO + 1);
            assert(sF == s_pre.update(block_at as int, nv));
            assert(forall|w2: usize| (w2 as int) < sF.len() && (w2 as int) != (block_at as int)
                ==> sF[w2 as int] == s_pre[w2 as int]) by { }
            // old bits keep their values
            assert forall|j: usize| j < nO implies bit_at(sF, nF, j)
                == bit_at(sO, nO, j) by {
                int_div_bound_lemma(j, nO);
                let wj = j / 32;
                let tj = j % 32;
                assert(tj < 32);
                assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                if (wj as int) == (block_at as int) {
                    // the else-path: strictly below the appended position
                    assert(eO > 0);
                    assert(tj < bit_at_w) by {
                        assert((j as int) == 32 * (block_at as int) + (tj as int));
                        assert((nO as int) == 32 * (block_at as int) + (bit_at_w as int));
                        assert((j as int) < (nO as int));
                    }
                    let msk: u32 = 1u32 << (bit_at_w as u32);
                    assert((flag == msk) || (flag == 0u32)) by {
                        if bit {
                            assert(flag == 1u32 << bit_at_w);
                            assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32));
                        } else {
                            assert(flag == 0u32);
                        }
                    }
                    assert(((nv) & (1u32 << ((tj as u32)))) != 0u32
                        == ((oldv & (1u32 << ((tj as u32)))) != 0u32)) by (bit_vector)
                        requires
                            nv == (oldv | flag),
                            (tj as u32) < (bit_at_w as u32),
                            (flag == msk || flag == 0u32),
                            msk == (1u32 << (bit_at_w as u32)),
                    ;
                    assert(((sF[block_at as int]) & (1u32 << (j % 32))) != 0u32
                        == ((sO[(L - 1) as int] & (1u32 << (j % 32))) != 0u32)) by {
                        assert(sF[block_at as int] == nv);
                        assert(oldv == sO[(L - 1) as int]);
                        assert((wj as int) == ((L - 1) as int));
                    }
                } else {
                    // untouched block (or the pushed tail below block_at)
                    assert(sF[wj as int] == s_pre[wj as int]);
                    assert(s_pre[wj as int] == sO[wj as int]) by {
                        if eO == 0 {
                            assert((wj as int) < L as int);
                            assert(s_pre == sO.push(0u32));
                        } else {
                            assert(s_pre == sO);
                        }
                    }
                }
            }
            // the appended bit
            assert(bit_at(sF, nF, nO as usize) == bit) by {
                int_div_bound_lemma(nO, nF);
                assert((nO / 32) == block_at) by {
                    if eO == 0 {
                        assert((nO as int) == 32 * (L as int));
                    } else {
                        assert((nO as int) == 32 * (block_at as int) + (bit_at_w as int));
                    }
                }
                assert((nO % 32) == bit_at_w);
                let msk2: u32 = 1u32 << (bit_at_w as u32);
                if bit {
                    assert(flag == 1u32 << bit_at_w);
                    assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32));
                    assert(((nv) & msk2) != 0u32) by (bit_vector)
                        requires
                            nv == (oldv | flag),
                            flag == msk2,
                            msk2 == (1u32 << (bit_at_w as u32)),
                            (bit_at_w as u32) < 32u32,
                    ;
                } else {
                    assert(flag == 0u32);
                    assert((oldv & (1u32 << (bit_at_w as u32))) != 0u32
                        == ((nv & (1u32 << (bit_at_w as u32))) != 0u32)) by (bit_vector)
                        requires
                            nv == (oldv | flag),
                            flag == 0u32,
                            (bit_at_w as u32) < 32u32,
                    ;
                    assert(oldv < (1u32 << (bit_at_w as u32))) by {
                        if eO == 0 {
                            assert(oldv == 0u32);
                            assert((1u32 << bit_at_w) == 1u32) by (bit_vector)
                                requires
                                    bit_at_w == 0usize,
                            ;
                            assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32));
                        } else {
                            assert(trailing_zero(old(self)));
                            assert((L - 1) as int == blocks_for_bits(nO) - 1);
                            assert(old(self).storage@[(L - 1) as int]
                                < (1u32 << (nO % 32)));
                            assert(bit_at_w == eO) by {
                                assert((bit_at_w as int) == (nO as int) % 32);
                                assert(eO == nO % 32);
                            }
                            assert(1u32 << (nO % 32) == 1u32 << (eO as u32)) by {
                                assert(1u32 << eO == 1u32 << (eO as u32));
                            }
                            assert(1u32 << (eO as u32) == 1u32 << (bit_at_w as u32)) by { }
                        }
                    }
                    assert((nv & (1u32 << (bit_at_w as u32))) == 0u32) by (bit_vector)
                        requires
                            nv == (oldv | flag),
                            flag == 0u32,
                            oldv < (1u32 << (bit_at_w as u32)),
                    ;

                }
            }
            // structural invariants
            assert(len_inv(self)) by {
                if eO == 0 {
                    assert(eF == 1);
                    assert(sF.len() == L as int + 1) by { }
                    assert((nF as int) % 32 == 1) by {
                        assert((nO as int) == 32 * (L as int));
                    }
                } else if eO == 31 {
                    assert(eF == 0);
                    assert(sF.len() == L as int) by { }
                    assert((nF as int) % 32 == 0) by {
                        assert((nO as int) == 32 * ((L - 1) as int) + 31);
                        assert((nF as int) == (nO as int) + 1);
                    }
                    assert(blocks_for_bits(nF) == (((nF as int) / 32)) as usize) by {
                        assert((nF as int) == 32 * ((nF as int) / 32));
                    }
                    assert(((nF as int) / 32) == L as int) by {
                        assert((nF as int) == 32 * ((L - 1) as int) + 32);
                    }
                } else {
                    assert(2 <= eF <= 31);
                    assert(eF == eO + 1) by {
                        assert((nO as int) == 32 * ((nO as int) / 32) + eO);
                        assert((nF as int) == (nO as int) + 1);
                    }
                    assert(sF.len() == L as int) by { }
                    assert(blocks_for_bits(nF) == (((nF as int) / 32) + 1) as usize) by {
                        assert((nF as int) % 32 > 0);
                    }
                    assert(((nF as int) / 32) == (nO as int) / 32) by {
                        assert((nO as int) == 32 * ((nO as int) / 32) + eO);
                        assert((nF as int) == (nO as int) + 1);
                    }
                    assert(((nO as int) / 32) + 1 == L as int) by {
                        assert(len_inv(old(self)));
                        assert((nO as int) % 32 > 0);
                    }
                }
            }
            assert(trailing_zero(self)) by {
                if eF == 0 {
                } else if eO == 0 {
                    assert(eF == 1);
                    let tail = sF[(blocks_for_bits(nF) - 1) as int];
                    assert(tail == nv) by {
                        assert((blocks_for_bits(nF) - 1) as int == L as int);
                        assert(sF[L as int] == nv);
                    }
                    assert(nv < 2u32) by {
                        if bit {
                            assert(oldv == 0u32);
                            assert(flag == 1u32 << bit_at_w);
                            assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32));
                            assert((1u32 << (bit_at_w as u32)) == 1u32) by (bit_vector)
                                requires
                                    bit_at_w == 0usize,
                            ;
                            assert(flag == 1u32);
                            assert((0u32 | 1u32) < 2u32) by (bit_vector);
                        } else {
                            assert(oldv == 0u32);
                            assert(flag == 0u32);
                            assert((0u32 | 0u32) < 2u32) by (bit_vector);
                        }
                    }
                    assert(nv < (1u32 << 1u32)) by (bit_vector)
                        requires
                            nv < 2u32,
                    ;
                    assert(trailing_zero(self)) by { }
                } else {
                    // 1 <= eO <= 31: the old tail may gain one used bit
                    let tail = sF[(blocks_for_bits(nF) - 1) as int];
                    assert((blocks_for_bits(nF) - 1) as int == (L - 1) as int);
                    assert(tail == nv);
                    assert(oldv < (1u32 << eO)) by {
                        assert(trailing_zero(old(self)));
                        assert((L - 1) as int == blocks_for_bits(nO) - 1);
                    }
                    if eO == 31 {
                        assert(eF == 0);
                        assert(trailing_zero(self)) by { }
                    } else {
                        assert(eF == eO + 1);
                        assert(bit_at_w == eO) by {
                            assert((nO as int) == 32 * ((L - 1) as int) + eO);
                            assert((bit_at_w as int) == (nO as int) % 32);
                        }
                        if bit {
                            let msk: u32 = 1u32 << (eO as u32);
                            assert(flag == msk) by {
                                assert(flag == 1u32 << bit_at_w);
                                assert(1u32 << bit_at_w == 1u32 << (bit_at_w as u32));
                            }
                            assert(nv < (1u32 << ((eO + 1) as u32))) by (bit_vector)
                                requires
                                    nv == (oldv | flag),
                                    oldv < (1u32 << (eO as u32)),
                                    flag == (1u32 << (eO as u32)),
                                    (eO as u32) <= 30u32,
                            ;
                            assert(nv < (1u32 << (nF % 32))) by {
                                assert((nF % 32) == (eO + 1));
                                assert(1u32 << (eO + 1) == 1u32 << ((eO + 1) as u32));
                            }
                            assert(trailing_zero(self)) by { }
                        } else {
                            assert(flag == 0u32);
                            assert(nv == oldv) by (bit_vector)
                                requires
                                    nv == (oldv | flag),
                                    flag == 0u32,
                            ;
                            assert(nv < (1u32 << eO)) by { }
                            lemma_pow_mono(eO);
                            assert((1u32 << eO) < (1u32 << eF)) by {
                                assert(eF == eO + 1);
                                assert(1u32 << (eO + 1) == 1u32 << ((eO + 1) as u32));
                            }
                            assert(nv < (1u32 << eF));
                            assert(trailing_zero(self)) by { }
                        }
                    }
                }
            }
            assert(inv(final(self)));
        }
        Ok(())
    }
}

/// Origin Rust: fn mask_for_bits<B: BitBlock>(bits) -> B
///     { (!B::zero()) >> ((B::bits() - bits % B::bits()) % B::bits()) }
///     (exec bridge; the e>0 branch carries the machine form (1<<e)-1; the
///     bv reconciliation of !0>>(32-e) with 2^e-1 is in lemma_masks_agree).
/// Upstream doc (lib.rs:426-426):
///   Computes the bitmask for the final word of the vector
pub exec fn mask_for_bits_exec(nbits: usize) -> (r: u32)
    ensures
        r == trailing_mask(nbits),
{
    let e = nbits % 32;
    if e == 0 {
        proof {
            assert(trailing_mask(nbits) == 4294967295u32);
        }
        4294967295u32
    } else {
        proof {
            assert(e == nbits % 32);
            assert(e <= 31);
            assert((1u32 << e) >= 2u32) by (bit_vector)
                requires
                    e >= 1usize,
                    e <= 31usize,
            ;
        }
        let r: u32 = ((1u32 << e) - 1u32) as u32;
        proof {
            assert(trailing_mask(nbits) == ((1u32 << e) - 1u32) as u32) by {
            }
        }
        assert(r == trailing_mask(nbits));
        r
    }
}


// ---------------------------------------------------------------------------
// byte family (to_bytes/from_bytes).
//     util::reverse_bits is a REVERSE_TABLE lookup (util.rs:1-3) where the
//     table is a compile-time loop over the `reverse_bits` intrinsic
//     (util.rs:5-16); materialized here as the equivalent branch-free swap
//     network with the per-bit reversal contract ensured (std
//     u8::reverse_bits semantics: out bit p == in bit 7-p).
// ---------------------------------------------------------------------------

pub exec fn reverse_bits_exec(byte: u8) -> (r: u8)
    ensures
        forall|p: int| 0 <= p < 8 ==> bit_u8(r, p) == bit_u8(byte, (7 - p)),
{
    let x1 = ((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1);
    let x2 = ((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2);
    let x3 = ((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4);
    proof {
        assert(((x3 & (1u8 << 0)) != 0u8) == (((byte & (1u8 << 7)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 1)) != 0u8) == (((byte & (1u8 << 6)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 2)) != 0u8) == (((byte & (1u8 << 5)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 3)) != 0u8) == (((byte & (1u8 << 4)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 4)) != 0u8) == (((byte & (1u8 << 3)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 5)) != 0u8) == (((byte & (1u8 << 2)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 6)) != 0u8) == (((byte & (1u8 << 1)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
        assert(((x3 & (1u8 << 7)) != 0u8) == (((byte & (1u8 << 0)) != 0u8))) by (bit_vector)
            requires
                x1 == (((byte & 0xAAu8) >> 1) | ((byte & 0x55u8) << 1)),
                x2 == (((x1 & 0xCCu8) >> 2) | ((x1 & 0x33u8) << 2)),
                x3 == (((x2 & 0xF0u8) >> 4) | ((x2 & 0x0Fu8) << 4)),
        ;
    }
    x3
}

/// positions below 8*idx stay 0 after the pack shift.
pub proof fn lemma_shift_low_zero(v: u32, idx: usize, pos: usize)
    requires
        pos < 8 * idx,
        idx < 4,
        8 * idx < 32,
    ensures
        ((((v << (8 * idx)) as u32) & (1u32 << pos)) == 0u32),
{
    assert(((((v << (8 * idx)) as u32) & (1u32 << pos)) == 0u32)) by (bit_vector)
        requires
            (pos as u32) < (8 * (idx as u32)),
    ;
}

/// packing bound: x < 2^t and y < 2^8 => x | (y << t) < 2^(t+8) (t <= 24).
pub proof fn lemma_shift8_or_bound(x: u32, y: u32, t: usize)
    requires
        x < (1u32 << t),
        y < 256u32,
        t <= 16,
    ensures
        ((x | (y << t)) < (1u32 << (t + 8))),
{
    assert(1u32 << t == 1u32 << (t as u32));
    assert((y << t) == (y << (t as u32)));
    assert(((x | (y << (t as u32))) < (1u32 << ((t + 8) as u32)))) by (bit_vector)
        requires
            x < (1u32 << (t as u32)),
            y < 256u32,
            ((t + 8) as u32) <= 24u32,
    ;
    assert(1u32 << (t + 8) == 1u32 << ((t + 8) as u32));
}

/// bit above the bound is zero: x < 2^t and t <= p < 32 => bit p empty.
pub proof fn lemma_pow_lt_bit(x: u32, t: usize, p: usize)
    requires
        x < (1u32 << t),
        t <= p,
        p < 32,
        t < 32,
    ensures
        ((x & (1u32 << p)) == 0u32),
{
    assert((x & (1u32 << p)) == 0u32) by (bit_vector)
        requires
            x < (1u32 << (t as u32)),
            (t as u32) <= (p as u32),
            (p as u32) < 32u32,
    ;
}

/// the freshly packed bit: (v << 8idx) bit (8idx+p) == v bit p.
pub proof fn lemma_pack_bit(v: u32, idx: usize, p: usize)
    requires
        idx < 4,
        p < 8,
        8 * idx + p < 32,
    ensures
        (((((v << (8 * idx)) as u32) & (1u32 << ((8 * idx + p) as usize))) != 0u32)
            == ((v & (1u32 << p)) != 0u32)),
{
    let sh: u32 = ((8 * (idx as u32)) as u32);
    let pp: u32 = (p as u32);
    assert(((((v << sh) as u32) & (1u32 << (sh + pp))) != 0u32)
        == (((v & (1u32 << pp)) != 0u32))) by (bit_vector)
        requires
            (sh + pp) < 32u32,
            pp < 8u32,
    ;
    assert((v << (8 * idx)) == (v << sh));
    assert(1u32 << p == 1u32 << pp);
    assert(1u32 << ((8 * idx + p) as usize) == 1u32 << (sh + pp));
}

/// u8 as u32 preserves single bits: bit p of the cast == bit p of the byte.
pub proof fn lemma_u8_cast_bit(x: u8, p: usize)
    requires
        p < 8,
    ensures
        (((x as u32) & (1u32 << p)) != 0u32) == (((x & (1u8 << (p as u8))) != 0u8)),
{
    if p == 0 {
        assert((((x as u32) & (1u32 << 0)) != 0u32)
            == (((x & (1u8 << 0)) != 0u8))) by (bit_vector);
    } else if p == 1 {
        assert((((x as u32) & (1u32 << 1)) != 0u32)
            == (((x & (1u8 << 1)) != 0u8))) by (bit_vector);
    } else if p == 2 {
        assert((((x as u32) & (1u32 << 2)) != 0u32)
            == (((x & (1u8 << 2)) != 0u8))) by (bit_vector);
    } else if p == 3 {
        assert((((x as u32) & (1u32 << 3)) != 0u32)
            == (((x & (1u8 << 3)) != 0u8))) by (bit_vector);
    } else if p == 4 {
        assert((((x as u32) & (1u32 << 4)) != 0u32)
            == (((x & (1u8 << 4)) != 0u8))) by (bit_vector);
    } else if p == 5 {
        assert((((x as u32) & (1u32 << 5)) != 0u32)
            == (((x & (1u8 << 5)) != 0u8))) by (bit_vector);
    } else if p == 6 {
        assert((((x as u32) & (1u32 << 6)) != 0u32)
            == (((x & (1u8 << 6)) != 0u8))) by (bit_vector);
    } else {
        assert((((x as u32) & (1u32 << 7)) != 0u32)
            == (((x & (1u8 << 7)) != 0u8))) by (bit_vector);
    }
    assert(1u32 << p == 1u32 << ((p) as u32));
}

/// positions below the fresh byte keep their value across the packing OR.
pub proof fn lemma_or_low_preserve(new_acc: u32, acc: u32, shifted: u32, pos: usize)
    requires
        new_acc == acc | shifted,
        pos < 32,
        ((shifted & (1u32 << pos)) == 0u32),
    ensures
        ((new_acc & (1u32 << pos)) != 0u32) == ((acc & (1u32 << pos)) != 0u32),
{
    assert(((new_acc & (1u32 << pos)) != 0u32) == ((acc & (1u32 << pos)) != 0u32))
        by (bit_vector)
            requires
                new_acc == acc | shifted,
                ((shifted & (1u32 << pos)) == 0u32),
        ;
}

/// freshly OR-composed position: when acc's bit pos is 0, the OR's bit pos
///     is the shifted value's bit pos.
pub proof fn lemma_or_compose_bit(new_acc: u32, acc: u32, shifted: u32, pos: usize)
    requires
        new_acc == acc | shifted,
        pos < 32,
        ((acc & (1u32 << pos)) == 0u32),
    ensures
        ((new_acc & (1u32 << pos)) != 0u32) == ((shifted & (1u32 << pos)) != 0u32),
{
    assert(((new_acc & (1u32 << pos)) != 0u32) == ((shifted & (1u32 << pos)) != 0u32))
        by (bit_vector)
            requires
                new_acc == acc | shifted,
                ((acc & (1u32 << pos)) == 0u32),
        ;
}

/// u8 bound to bit p: x < 2^t and t <= p < 8 => bit p empty.
pub proof fn lemma_u8_pow_lt_bit(x: u8, t: usize, p: usize)
    requires
        x < (1u8 << t),
        t <= p,
        p < 8,
        t < 8,
    ensures
        ((x & (1u8 << p)) == 0u8),
{
    assert(((x & (1u8 << (p as u8))) == 0u8)) by (bit_vector)
        requires
            x < (1u8 << (t as u8)),
            (t as u8) <= (p as u8),
    ;
    assert(1u8 << p == 1u8 << (p as u8));
}

/// u8 flag fill-up bound: x < 2^t => x | 1<<t < 2^(t+1) (t+1 < 8).
pub proof fn lemma_u8_or_max(x: u8, t: usize)
    requires
        t < 8,
        t + 1 < 8,
        x < (1u8 << t),
    ensures
        ((x | (1u8 << t)) < (1u8 << (t + 1))),
{
    if t == 0 {
        assert(((x | (1u8 << 0)) < (1u8 << 1))) by (bit_vector)
            requires
                x < (1u8 << 0),
        ;
    } else if t == 1 {
        assert(((x | (1u8 << 1)) < (1u8 << 2))) by (bit_vector)
            requires
                x < (1u8 << 1),
        ;
    } else if t == 2 {
        assert(((x | (1u8 << 2)) < (1u8 << 3))) by (bit_vector)
            requires
                x < (1u8 << 2),
        ;
    } else if t == 3 {
        assert(((x | (1u8 << 3)) < (1u8 << 4))) by (bit_vector)
            requires
                x < (1u8 << 3),
        ;
    } else if t == 4 {
        assert(((x | (1u8 << 4)) < (1u8 << 5))) by (bit_vector)
            requires
                x < (1u8 << 4),
        ;
    } else if t == 5 {
        assert(((x | (1u8 << 5)) < (1u8 << 6))) by (bit_vector)
            requires
                x < (1u8 << 5),
        ;
    } else {
        assert(((x | (1u8 << 6)) < (1u8 << 7))) by (bit_vector)
            requires
                x < (1u8 << 6),
        ;
    }
    assert(1u8 << t == 1u8 << (((t) as u8)));
    assert(1u8 << (t + 1) == 1u8 << ((t + 1) as u8));
}

/// u8 OR flag placement keeps other flag positions.
pub proof fn lemma_u8_or_keep(new_byte: u8, byte: u8, flag: u8, q: usize)
    requires
        new_byte == byte | flag,
        q < 8,
        ((flag & (1u8 << q)) == 0u8),
    ensures
        ((new_byte & (1u8 << q)) != 0u8) == ((byte & (1u8 << q)) != 0u8),
{
    assert(((new_byte & (1u8 << (q as u8))) != 0u8) == (((byte & (1u8 << (q as u8))) != 0u8))) by (bit_vector)
        requires
            new_byte == byte | flag,
            ((flag & (1u8 << (q as u8))) == 0u8),
    ;
    assert(1u8 << q == 1u8 << (q as u8));
}


// ---------------------------------------------------------------------------
// insert introduction semantics (the per-bit ensures derivation): the
// left-side bits keep their values, the at-position takes the inserted
/// value, and the right-side bits move up by one position across the
/// within-block rewrite, the block-at carry, and the cascade.
// ---------------------------------------------------------------------------

/// the full per-bit postcondition of insert, derived from the frame facts.
pub proof fn insert_bit_semantics(
    sF: Seq<u32>, s_pc: Seq<u32>, sO: Seq<u32>, nF: usize, nO: usize,
    ba: usize, b: usize, carry0: u32, new_base: u32,
    sb: u32, m: u32, base: u32, at: usize, len_total: usize,
)
    requires
        nF == nO + 1,
        (ba as int) < (len_total as int),
        at == 32 * (ba as int) + b,
        at <= nO,
        b < 32,
        // frames
        sF.len() == len_total as int,
        s_pc.len() == len_total as int,
        (sO.len() + 1) >= (len_total as int),
        sO.len() == blocks_for_bits(nO) as int,
        len_total as int == blocks_for_bits(nF) as int,
        sO.len() <= len_total as int,
        sF[ba as int] == new_base,
        forall|w2: usize| w2 < len_total && w2 > ba ==>
            #[trigger] sF[w2 as int] ==
                (((s_pc[w2 as int] << 1)
                    | (if w2 == ba + 1 {
                        carry0
                    } else {
                        s_pc[(w2 - 1) as int] >> 31
                    }))),
        forall|w2: usize| w2 < len_total && w2 < ba ==>
            #[trigger] sF[w2 as int] == s_pc[w2 as int],
        forall|w2: usize| (w2 as int) < sO.len() && w2 != ba ==>
            #[trigger] s_pc[w2 as int] == sO[w2 as int],
        // base-block facts
        new_base == (((base & m) | (((base & (4294967295u32 ^ m)) << 1)))
            | sb),
        m == ((1u32 << (b as u32)) - 1u32),
        (sb == 0u32 || sb == (1u32 << (b as u32))),
        carry0 == base >> 31,
        // base is the pre-rewrite entry: the old block value, or the
        // freshly pushed zero block when ba is past the old sequence
        (ba as int) < sO.len() ==> base == sO[ba as int],
        sO.len() <= (ba as int) ==> base == 0u32,
    ensures
        forall|j: usize| j < at ==> bit_at(sF, nF, j) == bit_at(sO, nO, j),
        bit_at(sF, nF, at) == (sb != 0u32),
        forall|j: usize| at <= j && j < nO ==>
            bit_at(sF, nF, (j + 1) as usize) == bit_at(sO, nO, j),
{
    // bit_at frame: position i reads block i/32 at bit i%32 (spec forms
    // bridge to the (t as u32) cast used by the machine lemmas)
    // (a) j < at: the position keeps its value
    assert forall|j: usize| j < at implies bit_at(sF, nF, j) == bit_at(sO, nO, j) by {
        assert(j < nO) by {
            assert(j < at);
            assert(at <= nO);
        }
        int_div_bound_lemma(j, nO);
        assert(j < nO) by { assert(j < at); assert(at <= nO); }
        let wj = j / 32;
        let tj = j % 32;
        assert(tj < 32);
        if wj < ba {
            assert((wj as int) == (j as int) / 32);
            assert((wj as int) < sO.len()) by {
                assert((j as int) / 32 < blocks_for_bits(nO) as int);
                assert(sO.len() == blocks_for_bits(nO) as int);
            }
            assert((wj as int) < len_total as int) by {
                assert(sO.len() <= len_total as int);
            }
            assert(sF[wj as int] == s_pc[wj as int]);
            assert(s_pc[wj as int] == sO[wj as int]) by {
                assert(wj != ba);
                assert((wj as int) < sO.len());
            }
            assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        } else {
            assert(wj == ba) by {
                assert((j as int) < (at as int)) by { assert(j < at); }
                assert((at as int) == 32 * (ba as int) + (b as int));
                assert((j as int) / 32 < (ba as int) + 1) by {
                    assert((j as int) < 32 * ((ba as int) + 1));
                }
                assert((j as int) >= 32 * (ba as int)) by {
                    assert((wj as int) >= ba as int);
                }
            }
            let tj2 = j % 32;
            assert(tj2 < b) by {
                assert((j as int) < (at as int));
                assert((j as int) == 32 * (ba as int) + (tj2 as int));
                assert((at as int) == 32 * (ba as int) + (b as int));
            }
            lemma_insert_block_bit(base, b, tj2, sb, m);
            assert(sF[ba as int] == new_base);
            // the old block entry is the pre-rewrite base
            assert((ba as int) == (j as int) / 32);
            assert((ba as int) < sO.len()) by {
                assert((j as int) / 32 < blocks_for_bits(nO) as int);
                assert(sO.len() == blocks_for_bits(nO) as int);
            }
            assert(sO[ba as int] == base) by {
                assert((ba as int) < sO.len());
            }
            assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        }
    }
    // (b) the inserted position reads the set value
    assert(bit_at(sF, nF, at) == (sb != 0u32)) by {
        int_div_bound_lemma(at, nF);
        let wj = at / 32;
        let tj = at % 32;
        assert(wj == ba) by {
            assert((at as int) == 32 * (ba as int) + (b as int));
        }
        assert(tj == b) by {
            assert((at as int) == 32 * (ba as int) + (b as int));
        }
        lemma_insert_block_bit(base, b, tj, sb, m);
        assert(sF[ba as int] == new_base);
        assert(1u32 << (at % 32) == 1u32 << ((at % 32) as u32));
    }
    // (c) j in [at, nO): the value moves to position j+1
    assert forall|j: usize| at <= j && j < nO implies
        bit_at(sF, nF, (j + 1) as usize) == bit_at(sO, nO, j) by {
        int_div_bound_lemma(j, nO);
        let i1 = (j + 1) as usize;
        int_div_bound_lemma(i1, nF);
        let wj = j / 32;
        let tj = j % 32;
        let w1 = i1 / 32;
        let t1 = i1 % 32;
        assert((j as int) == 32 * (wj as int) + (tj as int));
        assert((i1 as int) == (j as int) + 1);
        assert((i1 as int) == 32 * (w1 as int) + (t1 as int));
        if w1 == ba {
            assert(b < t1) by {
                assert((j as int) >= (at as int));
                assert((j as int) == 32 * (ba as int) + (t1 as int) - 1) by {
                    assert((i1 as int) == 32 * (ba as int) + (t1 as int));
                    assert((i1 as int) == (j as int) + 1);
                }
                assert((at as int) == 32 * (ba as int) + (b as int));
            }
            lemma_insert_block_bit(base, b, t1, sb, m);
            assert(sF[ba as int] == new_base);
            // the old block entry is the pre-rewrite base
            assert((ba as int) == (j as int) / 32) by {
                assert((j as int) == 32 * (ba as int) + (tj as int));
                assert((tj as int) < 32);
            }
            assert((ba as int) < sO.len()) by {
                assert((j as int) / 32 < blocks_for_bits(nO) as int);
                assert(sO.len() == blocks_for_bits(nO) as int);
            }
            assert(sO[ba as int] == base) by {
                assert((ba as int) < sO.len());
            }
            assert(1u32 << (i1 % 32) == 1u32 << ((i1 % 32) as u32));
            assert((t1 as int) - 1 == (tj as int)) by {
                assert((i1 as int) == (j as int) + 1);
                assert((i1 as int) == 32 * (ba as int) + (t1 as int));
                assert((j as int) == 32 * (ba as int) + (tj as int));
                assert((tj as int) < 32);
            }
        } else {
            assert(w1 > ba) by {
                assert((i1 as int) >= (at as int) + 1);
                assert((at as int) == 32 * (ba as int) + (b as int));
                assert((i1 as int) >= 32 * (ba as int) + (b as int) + 1);
                assert((i1 as int) > 32 * (ba as int) + 31) by {
                    assert((b as int) <= 31);
                }
                assert((w1 as int) >= (ba as int) + 1);
            }
            // the moved-up position's block stays in range
            assert((w1 as int) == (i1 as int) / 32);
            int_div_bound_lemma(i1, nF);
            assert((w1 as int) < blocks_for_bits(nF) as int);
            assert((w1 as int) < len_total as int);
            // instantiate the cascade frame at its trigger form
            assert(sF[w1 as int] ==
                (((s_pc[w1 as int] << 1)
                    | (if w1 == ba + 1 {
                        carry0
                    } else {
                        s_pc[(w1 - 1) as int] >> 31
                    }))));
            assert(1u32 << (i1 % 32) == 1u32 << ((i1 % 32) as u32));
            if t1 == 0 {
                // the moved position reads bit 0, the old one the top bit:
                // both masks as constant flags
                assert((1u32 << ((i1 % 32) as u32)) == 1u32) by (bit_vector)
                    requires
                        ((i1 % 32) as u32) == 0u32,
                ;
                assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32)) by { }
                assert((1u32 << ((j % 32) as u32)) == (1u32 << 31u32)) by (bit_vector)
                    requires
                        ((j % 32) as u32) == 31u32,
                ;
                assert((w1 as int) >= 1) by {
                    assert((w1 as int) >= (ba as int) + 1);
                    assert((ba as int) + 1 >= 1);
                }
                assert((j as int) == 32 * ((w1 as int) - 1) + 31) by {
                    assert((i1 as int) == 32 * (w1 as int));
                    assert((i1 as int) == (j as int) + 1);
                }
                // the incoming carry is a 0/1 flag (before the shift lemma)
                if w1 == ba + 1 {
                    lemma_carry31(base);
                } else {
                    assert((w1 as int) >= (ba as int) + 2);
                    lemma_carry31(s_pc[(w1 - 1) as int]);
                }
                lemma_shiftup_bit(s_pc[w1 as int],
                    (if w1 == ba + 1 {
                        carry0
                    } else {
                        s_pc[(w1 - 1) as int] >> 31
                    }), 0);
                if w1 == ba + 1 {
                    // carry0 reads the base block's top bit
                    assert(bit_at(sO, nO, j) == ((sO[ba as int] & (1u32 << 31)) != 0u32)) by {
                        assert((j / 32) == ba) by {
                            assert((j as int) == 32 * (ba as int) + 31);
                        }
                        assert((j % 32) == 31);
                    }
                } else {
                    // the incoming carry is the left neighbor's top bit
                    assert((w1 - 1) != ba) by {
                        assert((w1 as int) >= (ba as int) + 2);
                    }
                    assert(((w1 - 1) as int) == (j as int) / 32);
                    assert(((w1 - 1) as int) < sO.len()) by {
                        assert((j as int) / 32 < blocks_for_bits(nO) as int);
                        assert(sO.len() == blocks_for_bits(nO) as int);
                    }
                    assert(s_pc[(w1 - 1) as int] == sO[(w1 - 1) as int]) by {
                        assert(((w1 - 1) as int) != (ba as int));
                        assert(((w1 - 1) as int) < sO.len());
                    }
                    assert(bit_at(sO, nO, j)
                        == ((sO[(w1 - 1) as int] & (1u32 << 31)) != 0u32)) by {
                        assert((j / 32) == (w1 - 1)) by {
                            assert((j as int) == 32 * ((w1 as int) - 1) + 31);
                        }
                        assert((j % 32) == 31);
                    }
                }
            } else {
                assert(1 <= t1 < 32);
                // the incoming carry is a 0/1 flag (before the shift lemma)
                if w1 == ba + 1 {
                    lemma_carry31(base);
                } else {
                    lemma_carry31(s_pc[(w1 - 1) as int]);
                }
                lemma_shiftup_bit(s_pc[w1 as int],
                    (if w1 == ba + 1 {
                        carry0
                    } else {
                        s_pc[(w1 - 1) as int] >> 31
                    }), t1);
                assert((w1 as int) != ba) by {
                    assert((w1 as int) >= (ba as int) + 1);
                }
                assert((w1 as int) == (j as int) / 32);
                assert((w1 as int) < sO.len()) by {
                    assert((j as int) / 32 < blocks_for_bits(nO) as int);
                    assert(sO.len() == blocks_for_bits(nO) as int);
                }
                assert(s_pc[w1 as int] == sO[w1 as int]) by {
                    assert((w1 as int) != (ba as int));
                    assert((w1 as int) < sO.len());
                }
                assert((t1 as int) - 1 == (tj as int)) by {
                    assert((i1 as int) == 32 * (w1 as int) + (t1 as int));
                    assert((j as int) == 32 * (w1 as int) + (tj as int));
                    assert((i1 as int) == (j as int) + 1);
                    assert((tj as int) < 32);
                    assert((t1 as int) < 32);
                }
                assert((j / 32) == w1) by {
                    assert((j as int) == 32 * (w1 as int) + (tj as int));
                }
                assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
            }
        }
    }
}


// ---------------------------------------------------------------------------
// remove introduction semantics (the per-bit ensures derivation): the
// left-side bits keep their values, and the right-side bits move down by
// one position across the within-block rewrite, the block-at carry, and
// the descending cascade.
// ---------------------------------------------------------------------------

/// the descending cascade value of block w2: shifted own bits with the next
/// block's old bit 0 carried into bit 31 (see rem_carry_in for the base).
pub open spec fn rem_cascade(s: Seq<u32>, w2: usize, len_total: usize) -> u32 {
    (s[w2 as int] >> 1)
        | (if w2 + 1 == len_total {
            0u32
        } else {
            ((s[(w2 + 1) as int] & 1u32) << 31)
        })
}

/// the carry arriving at block_at: the bit 0 of the block right above it
/// (zero when block_at is the top block and the cascade is empty).
pub open spec fn rem_carry_in(s: Seq<u32>, ba: usize, len_total: usize) -> u32 {
    if ba + 1 == len_total {
        0u32
    } else {
        s[(ba + 1) as int] & 1u32
    }
}

/// the full per-bit postcondition of remove, derived from the frame facts.
pub proof fn remove_bit_semantics(
    sF: Seq<u32>, sO: Seq<u32>, nF: usize, nO: usize,
    ba: usize, b: usize, base: u32, new_base: u32, carry_in: u32,
    m: u32, at: usize, len_total: usize,
)
    requires
        nF == nO - 1,
        sO.len() == len_total as int,
        len_total as int == blocks_for_bits(nO) as int,
        sF.len() == blocks_for_bits(nF) as int,
        at == 32 * (ba as int) + b,
        at < nO,
        b < 32,
        (ba as int) < len_total as int,
        carry_in == rem_carry_in(sO, ba, len_total),
        m == ((1u32 << (b as u32)) - 1u32),
        base == sO[ba as int],
        new_base == ((base & m) | ((base & ((4294967295u32 ^ m) << 1)) >> 1)
            | (carry_in << 31)),
        // frames: the surviving final position map
        forall|w2: usize| (w2 as int) < sF.len() ==>
            #[trigger] sF[w2 as int] ==
                (if w2 == ba {
                    new_base
                } else if (w2 as int) > (ba as int) {
                    rem_cascade(sO, w2, len_total)
                } else {
                    sO[w2 as int]
                }),
    ensures
        forall|j: usize| j < at ==> bit_at(sF, nF, j) == bit_at(sO, nO, j),
        forall|j: usize| at <= j && j < nF ==>
            bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize),
{
    // (a) j < at: the position keeps its value
    assert forall|j: usize| j < at implies bit_at(sF, nF, j) == bit_at(sO, nO, j) by {
        assert(j < nF) by {
            assert(j < at);
            assert(at < nO);
        }
        assert((j as int) / 32 < blocks_for_bits(nF) as int) by {
            int_div_bound_lemma(j, nF);
        }
        int_div_bound_lemma(j, nO);
        let wj = j / 32;
        let tj = j % 32;
        assert(tj < 32);
        assert((wj as int) == (j as int) / 32);
        if (wj as int) < (ba as int) {
            assert((wj as int) < sF.len());
            assert(sF[wj as int] == sO[wj as int]);
            assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        } else {
            assert((wj as int) == (ba as int)) by {
                assert((j as int) < (at as int));
                assert((at as int) == 32 * (ba as int) + (b as int));
                assert((j as int) < 32 * ((ba as int) + 1));
            }
            let tj2 = j % 32;
            assert(tj2 < b) by {
                assert((j as int) == 32 * (ba as int) + (tj2 as int));
                assert((at as int) == 32 * (ba as int) + (b as int));
                assert((j as int) < (at as int));
            }
            assert((wj as int) < sF.len());
            assert(sF[ba as int] == new_base);
            assert(sO[ba as int] == base);
            lemma_remove_block_bit(base, b, tj2, carry_in, m);
            assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        }
    }
    // (b) j in [at, nF): the old value at j+1 moves down to j
    // (b1) same block as the removed position
    assert forall|j: usize| at <= j && j < nF && (j / 32) == ba implies
        bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize) by {
        int_div_bound_lemma(j, nF);
        let wj = j / 32;
        let tj = j % 32;
        let i2 = (j + 1) as usize;
        int_div_bound_lemma(i2, nO);
        let w2 = i2 / 32;
        let t2 = i2 % 32;
        assert((j as int) == 32 * (wj as int) + (tj as int));
        assert((i2 as int) == 32 * (w2 as int) + (t2 as int));
        assert((i2 as int) == (j as int) + 1);
        assert((wj as int) == (ba as int));
        assert(tj >= b) by {
            assert((j as int) >= (at as int));
            assert((j as int) == 32 * (ba as int) + (tj as int));
            assert((at as int) == 32 * (ba as int) + (b as int));
        }
        assert(sF[ba as int] == new_base) by { }
        assert(sO[ba as int] == base) by { }
        // per-side definitional bridges
        assert(bit_at(sF, nF, j)
            == (((sF[ba as int]) & (1u32 << (j % 32))) != 0u32)) by { }
        assert(bit_at(sO, nO, i2)
            == (((sO[(i2 / 32) as int]) & (1u32 << (i2 % 32))) != 0u32)) by { }
        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        assert(1u32 << (i2 % 32) == 1u32 << ((i2 % 32) as u32));
        if tj <= 30 {
            lemma_remove_block_bit(base, b, tj, carry_in, m);
            assert((w2 as int) == (ba as int)) by {
                assert((i2 as int) == 32 * (ba as int) + (tj as int) + 1);
                assert((tj as int) <= 30);
            }
            assert((t2 as int) == 1 + (tj as int)) by {
                assert((i2 as int) == 32 * (ba as int) + (t2 as int));
                assert((j as int) == 32 * (ba as int) + (tj as int));
            }
        } else {
            assert(tj == 31);
            // new base bit 31 is the carried bit 0 of the next block
            assert((w2 as int) == (ba as int) + 1) by {
                assert((i2 as int) == 32 * (ba as int) + 32);
            }
            assert((w2 as int) < sO.len());
            assert((ba + 1) != len_total) by {
                assert((ba as int) + 1 < sO.len());
                assert(sO.len() == len_total as int);
            }
            assert(carry_in == sO[(ba + 1) as int] & 1u32) by {
                assert(carry_in == rem_carry_in(sO, ba, len_total));
                assert((ba + 1) != len_total);
            }
            let nb1: u32 = sO[(ba + 1) as int];
            assert(((carry_in & 1u32) != 0u32)
                == ((nb1 & 1u32) != 0u32)) by (bit_vector)
                requires
                    carry_in == (nb1 & 1u32),
            ;
            lemma_remove_block_bit(base, b, 31, carry_in, m);
            assert((1u32 << ((i2 % 32) as u32)) == 1u32) by (bit_vector)
                requires
                    ((i2 % 32) as u32) == 0u32,
            ;
            assert((1u32 << ((j % 32) as u32)) == (1u32 << 31u32)) by (bit_vector)
                requires
                    ((j % 32) as u32) == 31u32,
            ;
        }
    }
    // (b2) blocks above ba: the cascade moves every bit down one
    assert forall|j: usize|
        at <= j && j < nF && (j / 32) != ba && (j % 32) <= 30 implies
        bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize) by {
        int_div_bound_lemma(j, nF);
        let wj = j / 32;
        let tj = j % 32;
        let i2 = (j + 1) as usize;
        int_div_bound_lemma(i2, nO);
        let w2 = i2 / 32;
        let t2 = i2 % 32;
        assert((j as int) == 32 * (wj as int) + (tj as int));
        assert((i2 as int) == 32 * (w2 as int) + (t2 as int));
        assert((i2 as int) == (j as int) + 1);
        assert((wj as int) > (ba as int)) by {
            assert((j as int) >= (at as int));
            assert((at as int) == 32 * (ba as int) + (b as int));
            assert((b as int) <= 31);
            assert((wj as int) >= (ba as int));
        }
        assert((wj as int) < sF.len());
        assert(sF[wj as int] == rem_cascade(sO, wj, len_total)) by { }
        // the raw carry value arriving at block wj
        let cv: u32 = (if wj + 1 == len_total {
            0u32
        } else {
            sO[(wj + 1) as int] & 1u32
        });
        assert(rem_cascade(sO, wj, len_total)
            == ((sO[wj as int] >> 1) | (cv << 31))) by {
            if wj + 1 == len_total {
                assert((0u32 << 31) == 0u32) by (bit_vector);
            }
        }
        assert(sF[wj as int] == ((sO[wj as int] >> 1) | (cv << 31))) by { }
        // per-side definitional bridges
        assert(bit_at(sF, nF, j)
            == (((sF[wj as int]) & (1u32 << (j % 32))) != 0u32)) by { }
        assert(bit_at(sO, nO, i2)
            == (((sO[(i2 / 32) as int]) & (1u32 << (i2 % 32))) != 0u32)) by { }
        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        assert(1u32 << (i2 % 32) == 1u32 << ((i2 % 32) as u32));
        lemma_shiftdown_bit(sO[wj as int], cv, tj);
        assert((((sF[wj as int]) & (1u32 << ((tj as u32)))) != 0u32)
            == (((sO[wj as int]) & (1u32 << (((tj + 1) as u32)))) != 0u32)) by { }
        assert((w2 as int) == (wj as int)) by {
            assert((i2 as int) == 32 * (wj as int) + (tj as int) + 1);
            assert((tj as int) <= 30);
        }
        assert((t2 as int) == 1 + (tj as int)) by {
            assert((i2 as int) == 32 * (wj as int) + (t2 as int));
            assert((j as int) == 32 * (wj as int) + (tj as int));
        }
        assert((1u32 << ((i2 % 32) as u32)) == (1u32 << (((tj + 1) as u32)))) by {
            assert((t2 as int) == 1 + (tj as int));
        }
    }
    assert forall|j: usize|
        at <= j && j < nF && (j / 32) != ba && (j % 32) == 31 implies
        bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize) by {
        int_div_bound_lemma(j, nF);
        let wj = j / 32;
        let tj = j % 32;
        let i2 = (j + 1) as usize;
        int_div_bound_lemma(i2, nO);
        let w2 = i2 / 32;
        let t2 = i2 % 32;
        assert((j as int) == 32 * (wj as int) + (tj as int));
        assert((i2 as int) == 32 * (w2 as int) + (t2 as int));
        assert((i2 as int) == (j as int) + 1);
        assert((wj as int) > (ba as int)) by {
            assert((j as int) >= (at as int));
            assert((at as int) == 32 * (ba as int) + (b as int));
            assert((b as int) <= 31);
            assert((wj as int) >= (ba as int));
        }
        assert((wj as int) < sF.len());
        assert(sF[wj as int] == rem_cascade(sO, wj, len_total)) by { }
        // bit 31 is the carried bit 0 of the block above
        assert((w2 as int) == (wj as int) + 1) by {
            assert((i2 as int) == 32 * (wj as int) + 32);
        }
        assert((w2 as int) < sO.len());
        assert((wj + 1) != len_total) by {
            assert((wj as int) + 1 < sO.len());
            assert(sO.len() == len_total as int);
        }
        let cv: u32 = (sO[(wj + 1) as int] & 1u32);
        assert(rem_cascade(sO, wj, len_total)
            == ((sO[wj as int] >> 1) | (cv << 31))) by {
            assert((wj + 1) != len_total);
        }
        assert(sF[wj as int] == ((sO[wj as int] >> 1) | (cv << 31))) by { }
        assert((sO[(wj + 1) as int]) == sO[w2 as int]) by {
            assert(((wj + 1) as usize) == w2);
        }
        lemma_shiftdown_bit(sO[wj as int], cv, 31);
        // per-side definitional bridges
        assert(bit_at(sF, nF, j)
            == (((sF[wj as int]) & (1u32 << (j % 32))) != 0u32)) by { }
        assert(bit_at(sO, nO, i2)
            == (((sO[(i2 / 32) as int]) & (1u32 << (i2 % 32))) != 0u32)) by { }
        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        assert(1u32 << (i2 % 32) == 1u32 << ((i2 % 32) as u32));
        assert((1u32 << ((i2 % 32) as u32)) == 1u32) by (bit_vector)
            requires
                ((i2 % 32) as u32) == 0u32,
        ;
        assert((1u32 << ((j % 32) as u32)) == (1u32 << 31u32)) by (bit_vector)
            requires
                ((j % 32) as u32) == 31u32,
        ;
        // explicit value chain for the two sides
        assert(sF[wj as int] == ((sO[wj as int] >> 1) | (cv << 31))) by { }
        assert((((sF[wj as int]) & (1u32 << 31u32)) != 0u32)
            == ((((sO[wj as int] >> 1) | (cv << 31)) & (1u32 << 31u32)) != 0u32)) by {
            assert(sF[wj as int] == ((sO[wj as int] >> 1) | (cv << 31)));
        }
        assert((((cv << 31) & (1u32 << 31u32)) != 0u32)
            == (((cv & 1u32) != 0u32))) by (bit_vector);
        let nb2: u32 = sO[(wj + 1) as int];
        assert(((cv & 1u32) != 0u32)
            == (((nb2 & 1u32) != 0u32))) by (bit_vector)
            requires
                cv == (nb2 & 1u32),
        ;
        assert(sO[w2 as int] == sO[(wj + 1) as int]) by {
            assert(((wj + 1) as usize) == w2);
        }
        assert((((sO[w2 as int] & 1u32) != 0u32)
            == ((sO[(wj + 1) as int] & 1u32) != 0u32))) by {
            assert(sO[w2 as int] == sO[(wj + 1) as int]);
        }
        assert(bit_at(sO, nO, i2)
            == (((sO[w2 as int]) & 1u32) != 0u32)) by {
            assert((i2 / 32) == w2);
            assert((i2 % 32) == 0);
        }
    }
    // combined closure over both block relations
    assert forall|j: usize| at <= j && j < nF implies
        bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize) by {
        if (j / 32) == ba {
            assert(at <= j && j < nF && (j / 32) == ba) by { }
            assert(bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize)) by { }
        } else {
            assert(at <= j && j < nF && (j / 32) != ba) by { }
            assert(bit_at(sF, nF, j) == bit_at(sO, nO, (j + 1) as usize)) by { }
        }
    }
}


// ---------------------------------------------------------------------------
// insert/remove (Origin Rust: lib.rs:1893-1923 / 1951-1986): the within-
// block rewrite (w & lsbits_mask) | ((w & !lsbits_mask) << 1) | set_bit and
// the block-carry shifts (w << 1) | carry / (w >> 1) | (carry << 31),
// all in machine-equal forms (the spec `!` is XOR all-ones).
// ---------------------------------------------------------------------------

/// insert's base-block rewrite, bit t: below b unchanged; at b the set bit;
/// above b the old bits shifted from t-1.
pub proof fn lemma_insert_block_bit(w: u32, b: usize, t: usize, sb: u32, m: u32)
    requires
        b < 32,
        t < 32,
        (sb == 0u32 || sb == (1u32 << (b as u32))),
        m == ((1u32 << (b as u32)) - 1u32),
    ensures
        t < b ==> (((((w & m) | ((w & (4294967295u32 ^ m)) << 1) | sb) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << ((t as u32)))) != 0u32)),
        t == b ==> (((((w & m) | ((w & (4294967295u32 ^ m)) << 1) | sb) & (1u32 << (t as u32))) != 0u32) == (sb != 0u32)),
        b < t ==> (((((w & m) | ((w & (4294967295u32 ^ m)) << 1) | sb) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << (((t - 1) as u32)))) != 0u32)),
{
    if t < b {
        assert(((((w & m) | ((w & (4294967295u32 ^ m)) << 1) | sb) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << ((t as u32)))) != 0u32)) by (bit_vector)
            requires
                (b as u32) < 32u32,
                (t as u32) < (b as u32),
                m == ((1u32 << (b as u32)) - 1u32),
                (sb == 0u32 || sb == (1u32 << (b as u32))),
        ;
    } else if t == b {
        assert(((((w & m) | ((w & (4294967295u32 ^ m)) << 1) | sb) & (1u32 << (t as u32))) != 0u32) == (sb != 0u32)) by (bit_vector)
            requires
                (b as u32) < 32u32,
                (t as u32) == (b as u32),
                m == ((1u32 << (b as u32)) - 1u32),
                (sb == 0u32 || sb == (1u32 << (b as u32))),
        ;
    } else {
        assert(((((w & m) | ((w & (4294967295u32 ^ m)) << 1) | sb) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << (((t - 1) as u32)))) != 0u32)) by (bit_vector)
            requires
                (b as u32) < 32u32,
                (b as u32) < (t as u32),
                (t as u32) < 32u32,
                m == ((1u32 << (b as u32)) - 1u32),
                (sb == 0u32 || sb == (1u32 << (b as u32))),
        ;
    }
}

/// insert's base-block rewrite tail bound: w < 2^e, b <= e <= 30 => the
/// rewritten value stays below 2^(e+1).
pub proof fn lemma_insert_block_below(w: u32, b: usize, e: usize, sb: u32, m: u32)
    requires
        b <= e,
        e <= 30,
        w < (1u32 << e),
        (sb == 0u32 || sb == (1u32 << (b as u32))),
        m == ((1u32 << (b as u32)) - 1u32),
    ensures
        (((w & m) | (((w & (4294967295u32 ^ m)) << 1)) | sb) < (1u32 << (e + 1))),
{
    assert(((((w & m) | (((w & (4294967295u32 ^ m)) << 1)) | sb))
        < (1u32 << ((e + 1) as u32)))) by (bit_vector)
        requires
            (e as u32) <= 30u32,
            (b as u32) <= (e as u32),
            w < (1u32 << (e as u32)),
            m == ((1u32 << (b as u32)) - 1u32),
            (sb == 0u32 || sb == (1u32 << (b as u32))),
    ;
    assert(1u32 << (e + 1) == 1u32 << ((e + 1) as u32));
}

/// the cascaded shift-up (w << 1) | carry: bit 0 is the carry, bit t (t>=1)
/// is the old bit t-1; carry in {0, 1}.
pub proof fn lemma_shiftup_bit(w: u32, c: u32, t: usize)
    requires
        t < 32,
        c <= 1u32,
    ensures
        t == 0 ==> ((((w << 1) | c) & 1u32) == (c & 1u32)),
        t >= 1 ==> (((((w << 1) | c) & (1u32 << (t as u32))) != 0u32)
            == (((w & (1u32 << ((t - 1) as u32))) != 0u32))),
{
    if t == 0 {
        assert((((w << 1) | c) & 1u32) == (c & 1u32)) by (bit_vector)
            requires
                c <= 1u32,
            ;
    } else {
        assert(((((w << 1) | c) & (1u32 << (t as u32))) != 0u32)
            == (((w & (1u32 << ((t - 1) as u32))) != 0u32))) by (bit_vector)
            requires
                (t as u32) < 32u32,
                (t as u32) >= 1u32,
                c <= 1u32,
        ;
    }
}

/// the cascaded shift-up value bound: w < 2^e, carry <= 1, e <= 30.
pub proof fn lemma_shiftup_below(w: u32, c: u32, e: usize)
    requires
        w < (1u32 << e),
        c <= 1u32,
        e <= 30,
    ensures
        ((w << 1) | c) < (1u32 << (e + 1)),
{
    assert(((w << 1) | c) < (1u32 << ((e + 1) as u32))) by (bit_vector)
        requires
            w < (1u32 << (e as u32)),
            c <= 1u32,
            ((e + 1) as u32) <= 31u32,
    ;
    assert(1u32 << (e + 1) == 1u32 << ((e + 1) as u32));
}

/// top-bit extraction: (x >> 31) is 0/1 and equals x's bit 31 as a flag.
pub proof fn lemma_carry31(x: u32)
    ensures
        (x >> 31) <= 1u32,
        (((x >> 31) & 1u32) != 0u32) == (((x & (1u32 << 31u32)) != 0u32)),
{
    assert((x >> 31) <= 1u32) by (bit_vector);
    assert((((x >> 31) & 1u32) != 0u32)
        == (((x & (1u32 << 31u32)) != 0u32))) by (bit_vector);
}

/// remove's base-block rewrite, bit t: below b unchanged; b..=30 from the old
/// bit t+1; bit 31 from the carry.
pub proof fn lemma_remove_block_bit(w: u32, b: usize, t: usize, c: u32, m: u32)
    requires
        b < 32,
        t < 32,
        m == ((1u32 << (b as u32)) - 1u32),
    ensures
        t < b ==> (((((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << ((t as u32)))) != 0u32)),
        b <= t && t <= 30 ==> (((((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << (((t + 1) as u32)))) != 0u32)),
        t == 31 ==> (((((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) & (1u32 << (31))) != 0u32) == ((c & 1u32) != 0u32)),
{
    if t < b {
        assert(((((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << ((t as u32)))) != 0u32)) by (bit_vector)
            requires
                (b as u32) < 32u32,
                (t as u32) < (b as u32),
                m == ((1u32 << (b as u32)) - 1u32),
        ;
    } else if t <= 30 {
        assert(((((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) & (1u32 << (t as u32))) != 0u32) == ((w & (1u32 << (((t + 1) as u32)))) != 0u32)) by (bit_vector)
            requires
                (b as u32) < 32u32,
                (b as u32) <= (t as u32),
                (t as u32) <= 30u32,
                m == ((1u32 << (b as u32)) - 1u32),
        ;
    } else {
        assert(((((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) & (1u32 << (31))) != 0u32) == ((c & 1u32) != 0u32)) by (bit_vector)
            requires
                (b as u32) < 32u32,
                (t as u32) == 31u32,
                m == ((1u32 << (b as u32)) - 1u32),
        ;
    }
}

/// remove's result read: (w >> b) & 1 nonzero iff bit b is set.
pub proof fn lemma_remove_result_bit(w: u32, b: usize)
    requires
        b < 32,
    ensures
        (((w >> b) & 1u32) != 0u32) == (((w & (1u32 << b)) != 0u32)),
{
    assert((((w >> b) & 1u32) != 0u32) == (((w & (1u32 << b)) != 0u32))) by (bit_vector)
        requires
            (b as u32) < 32u32,
    ;
    assert(1u32 << b == 1u32 << (b as u32));
}

/// the cascaded shift-down: (w >> 1) | (c << 31), bit t (t <= 30) is the old
/// bit t+1, bit 31 is the carried bit from the neighbor block.
pub proof fn lemma_shiftdown_bit(w: u32, c: u32, t: usize)
    requires
        t < 32,
    ensures
        t <= 30 ==> (((((w >> 1) | (c << 31)) & (1u32 << (t as u32))) != 0u32)
            == (((w & (1u32 << ((t + 1) as u32))) != 0u32))),
        t == 31 ==> (((((w >> 1) | (c << 31)) & (1u32 << 31)) != 0u32)
            == (((c & 1u32) != 0u32))),
{
    if t <= 30 {
        assert(((((w >> 1) | (c << 31)) & (1u32 << (t as u32))) != 0u32)
            == (((w & (1u32 << ((t + 1) as u32))) != 0u32))) by (bit_vector)
            requires
                (t as u32) <= 30u32,
        ;
    } else {
        assert(((((w >> 1) | (c << 31)) & (1u32 << 31)) != 0u32)
            == (((c & 1u32) != 0u32))) by (bit_vector);
    }
}

/// the cascaded shift-down tail bound: with a zero carry-in, w < 2^e
/// gives (w >> 1) | (c << 31) < 2^(e-1) (1 <= e <= 31).
pub proof fn lemma_shiftdown_below(w: u32, c: u32, e: usize)
    requires
        1 <= e,
        e <= 31,
        w < (1u32 << e),
        c == 0u32,
    ensures
        ((w >> 1) | (c << 31)) < (1u32 << (e - 1)),
{
    assert((((w >> 1) | (c << 31)) < (1u32 << ((e - 1) as u32)))) by (bit_vector)
        requires
            w < (1u32 << (e as u32)),
            c == 0u32,
            (e as u32) >= 1u32,
            (e as u32) <= 31u32,
    ;
    assert(1u32 << (e - 1) == 1u32 << ((e - 1) as u32));
}

/// remove's base-block rewrite tail bound: with ba in the last block, the
/// rewritten value stays below 2^(e-1) (the carry is zero: no blocks above).
pub proof fn lemma_remove_block_below(w: u32, b: usize, e: usize, c: u32, m: u32)
    requires
        b < e,
        1 <= e,
        e <= 31,
        w < (1u32 << e),
        c == 0u32,
        m == ((1u32 << (b as u32)) - 1u32),
    ensures
        (((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31))
            < (1u32 << (e - 1))),
{
    assert(((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) < (1u32 << ((e - 1) as u32))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            (b as u32) < (e as u32),
            w < (1u32 << (e as u32)),
            m == ((1u32 << (b as u32)) - 1u32),
            c == 0u32,
    ;
    assert(1u32 << (e - 1) == 1u32 << ((e - 1) as u32));
}

/// remove's base-block rewrite top bound: any base value with a zero carry
/// keeps bit 31 clear (the nbits % 32 == 0 tail tier).
pub proof fn lemma_remove_block_top(w: u32, b: usize, c: u32, m: u32)
    requires
        b < 32,
        c == 0u32,
        m == ((1u32 << (b as u32)) - 1u32),
    ensures
        (((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31))
            < (1u32 << 31)),
{
    assert(((w & m) | ((w & ((4294967295u32 ^ m) << 1)) >> 1) | (c << 31)) < (1u32 << 31u32)) by (bit_vector)
        requires
            (b as u32) < 32u32,
            m == ((1u32 << (b as u32)) - 1u32),
            c == 0u32,
    ;
    assert((1u32 << 31) == (1u32 << 31u32));
}

// ---------------------------------------------------------------------------
// popcount / bit-count model (count_ones/count_zeros):
//     popc(x, k) counts the set bits at positions 0..k-1 of one block value,
//     popc_seq sums it over blocks, count_bits counts set bits at bit
//     positions i..j via the bit_at model, zeros_seq is popc_seq's
//     per-block complement; count_ones_spec is the bit-level semantic view.
//     All return int (unbounded): counts never wrap.
// ---------------------------------------------------------------------------

/// set-bit count of one block value at positions 0..k-1 (k <= 32).
pub open spec fn popc(x: u32, k: usize) -> int
    decreases
        k,
{
    if k == 0 {
        0int
    } else {
        popc(x, (k - 1) as usize)
            + (if (x & (1u32 << ((k - 1) as usize))) != 0u32 { 1int } else { 0int })
    }
}

/// sum of popc(block, 32) over the first k blocks.
pub open spec fn popc_seq(s: Seq<u32>, k: usize) -> int
    decreases
        k,
{
    if k == 0 {
        0int
    } else {
        popc_seq(s, (k - 1) as usize) + popc(s[(k - 1) as int], 32)
    }
}

/// per-block complement sum: (32 - popc(block, 32)) over the first k blocks.
pub open spec fn zeros_seq(s: Seq<u32>, k: usize) -> int
    decreases
        k,
{
    if k == 0 {
        0int
    } else {
        zeros_seq(s, (k - 1) as usize) + (32 - popc(s[(k - 1) as int], 32))
    }
}

/// set-bit count at bit positions i..j-1 (the bit_at model, i <= j <= n).
pub open spec fn count_bits(s: Seq<u32>, n: usize, i: usize, j: usize) -> int
    decreases
        j - i,
{
    if i >= j {
        0int
    } else {
        (if bit_at(s, n, i) { 1int } else { 0int }) + count_bits(s, n, (i + 1) as usize, j)
    }
}

/// semantic view: the number of set bits among the nbits bits.
pub open spec fn count_ones_spec(bv: &BitVec) -> int {
    count_bits(bv.storage@, bv.nbits, 0, bv.nbits)
}

// ---------------------------------------------------------------------------
// byte model (to_bytes/from_bytes):
//     bit_u8 tests one bit position of a byte value; bytes_for_bits is the
//     byte-count ceiling of to_bytes (blocks_for_bits on the byte axis).
// ---------------------------------------------------------------------------

/// bit test at position p (0 <= p < 8) of a byte value.
pub open spec fn bit_u8(x: u8, p: int) -> bool {
    (x & (1u8 << (p as u8))) != 0u8
}

/// number of bytes to hold nbits bits (to_bytes result length).
pub open spec fn bytes_for_bits(nbits: usize) -> usize {
    ((nbits as int) / 8 + if (nbits as int) % 8 > 0 { 1int } else { 0int }) as usize
}

/// from_bytes source model: the storage bit (word, pos) reads the input
///     byte (4*word + pos/8) at position (7 - pos%8) (each byte's most
///     significant bits come first).
pub open spec fn fb_byte(bs: Seq<u8>, word: int, pos: int) -> bool {
    ((bs[(4 * word + pos / 8) as int] & (1u8 << ((7 - pos % 8) as u8))) != 0u8)
}

/// the doc-visible bit view of from_bytes: bit i reads byte i/8 at pos 7-i%8.
pub open spec fn from_bytes_bit(bs: Seq<u8>, i: usize) -> bool {
    ((bs[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8)
}


// ===========================================================================
// Proof lemmas (machine bit-level obligations and model bridges, placed at
// the end of the file so the exec implementation reads directly)
// ===========================================================================
/// all_spec => every bit i < nbits is true (mask block entails bit-wise).
pub proof fn lemma_all_spec_bits(bv: &BitVec)
    requires
        inv(bv),
        all_spec(bv),
    ensures
        forall|j: usize| j < bv.nbits ==> bit_at(bv.storage@, bv.nbits, j),
{
    assert forall|j: usize| j < bv.nbits implies bit_at(bv.storage@, bv.nbits, j) by {
        lemma_bit_of_all(bv, j);
    }
}

/// single-point focus: all_spec => bit j set (mask block entails the bit;
/// probeA).
pub proof fn lemma_bit_of_all(bv: &BitVec, j: usize)
    requires
        inv(bv),
        all_spec(bv),
        j < bv.nbits,
    ensures
        bit_at(bv.storage@, bv.nbits, j),
{
    let w = bv.storage@.len();
    let e = bv.nbits % 32;
    assert(w == blocks_for_bits(bv.nbits));
    if e > 0 {
        assert((w as int) == (bv.nbits as int) / 32 + 1);
        assert(bv.nbits == 32 * ((w - 1) as int) + e);
    } else {
        assert(bv.nbits == 32 * (w as int));
    }
    let k = j / 32;
    assert(k < w) by {
        int_div_bound_lemma(j, bv.nbits);
    }
    if k == w - 1 {
        assert(bv.storage@[(j / 32) as int] == trailing_mask(bv.nbits));
        if e == 0 {
            assert(trailing_mask(bv.nbits) == 4294967295u32);
            lemma_flag_set_ones(bv.storage@[(j / 32) as int], j % 32);
        } else {
            assert(j % 32 < e) by {
                assert(j == 32 * (j / 32) + j % 32);
            }
            lemma_flag_set_mask(bv.storage@[(j / 32) as int], e, j % 32);
        }
    } else {
        assert(k < w - 1);
        assert(bv.storage@[(j / 32) as int] == 4294967295u32);
        lemma_flag_set_ones(bv.storage@[(j / 32) as int], j % 32);
    }
    lemma_flag_nonzero(j % 32);
}

/// shifted power is nonzero: 1 << b != 0 (b <= 31). In the spec domain
/// shifts are uninterpreted; bit-level validity goes through bv.
pub proof fn lemma_flag_nonzero(b: usize)
    requires
        b <= 31usize,
    ensures
        (1u32 << b) != 0u32,
{
    assert((1u32 << b) != 0u32) by (bit_vector)
        requires
            b <= 31usize,
    ;
}

/// bit of an all-ones word: x == 0xFFFFFFFF => bit b set (b <= 31).
pub proof fn lemma_flag_set_ones(x: u32, b: usize)
    requires
        b <= 31usize,
        x == 4294967295u32,
    ensures
        x & (1u32 << b) == (1u32 << b),
{
    assert((x & (1u32 << b)) == (1u32 << b)) by (bit_vector)
        requires
            x == 4294967295u32,
            b <= 31usize,
    ;
}

/// bit of a mask word: x == 2^e - 1 and b < e <= 31 => bit b set.
pub proof fn lemma_flag_set_mask(x: u32, e: usize, b: usize)
    requires
        e <= 31usize,
        b <= 31usize,
        b < e,
        x == ((1u32 << e) - 1u32) as u32,
    ensures
        x & (1u32 << b) == (1u32 << b),
{
    assert((x & (1u32 << b)) == (1u32 << b)) by (bit_vector)
        requires
            x == ((1u32 << e) - 1u32) as u32,
            e <= 31usize,
            b <= 31usize,
            b < e,
    ;
}

/// negation bit: bit b of x^all-ones is the negation of bit b of x.
pub proof fn lemma_neg_bit(b: usize, x: u32)
    requires
        b <= 31usize,
    ensures
        (x & (1u32 << b)) == 0u32 <==> ((x ^ 4294967295u32) & (1u32 << b)) != 0u32,
{
    assert(((x & (1u32 << b)) == 0u32) <==> (((x ^ 4294967295u32) & (1u32 << b)) != 0u32))
        by (bit_vector)
        requires
            b <= 31usize,
    ;
}

/// masked-negation tail block: for bit b < e, bit b of (x^all-ones)
///     & 2^e-1 is the negation of bit b of x.
pub proof fn lemma_neg_bit_masked(b: usize, e: usize, x: u32, y: u32, m: u32)
    requires
        e <= 31usize,
        b <= 31usize,
        b < e,
        m == ((1u32 << e) - 1u32) as u32,
        y == (x ^ 4294967295u32) & m,
    ensures
        (x & (1u32 << b)) == 0u32 <==> (y & (1u32 << b)) != 0u32,
{
    assert(((x & (1u32 << b)) == 0u32) <==> (((x ^ 4294967295u32) & m) & (1u32 << b)) != 0u32)
        by (bit_vector)
        requires
            e <= 31usize,
            b <= 31usize,
            b < e,
            m == ((1u32 << e) - 1u32) as u32,
    ;
}

/// none_spec => every bit i < nbits is false.
pub proof fn lemma_none_spec_bits(bv: &BitVec)
    requires
        inv(bv),
        none_spec(bv),
    ensures
        forall|j: usize| j < bv.nbits ==> !bit_at(bv.storage@, bv.nbits, j),
{
    assert forall|j: usize| j < bv.nbits implies !bit_at(bv.storage@, bv.nbits, j) by {
        let k = j / 32;
        assert(k < bv.storage@.len()) by {
            int_div_bound_lemma(j, bv.nbits);
            assert(len_inv(bv));
        }
        assert(bv.storage@[k as int] == 0u32);
        assert(0u32 & (1u32 << (j % 32)) == 0u32) by (bit_vector)
            requires
                j % 32 <= 31usize,
        ;
    }
}

// ---------------------------------------------------------------------------
// lemmas (machine bit-level obligations, single-level bv assertions)
// ---------------------------------------------------------------------------

/// int division bound: i < n => i/32 < blocks_for_bits(n) and i%32 < 32.
pub proof fn int_div_bound_lemma(i: usize, n: usize)
    requires
        i < n,
    ensures
        i / 32 < blocks_for_bits(n),
        i % 32 < 32,
{
    assert(i / 32 < blocks_for_bits(n)) by {
        assert(blocks_for_bits(n) == ((n as int) / 32 + if (n as int) % 32 > 0 { 1int } else {
            0int
        }) as usize);
        assert((i as int) / 32 <= (n as int) / 32);
    }
}

/// equivalence of the trailing-block zero-bit predicate: for e>0,
/// `last >> e == 0` is equivalent to `last < 2^e` (and to
/// `last & !mask_for_bits(n) == 0`).
pub proof fn lemma_trailing_zero_alt(nbits: usize, last: u32)
    requires
        nbits % 32 > 0,
    ensures
        (last >> (nbits % 32) == 0u32) <==> last < (1u32 << (nbits % 32)),
{
    let e = nbits % 32;
    assert((last >> (e as u32) == 0u32) <==> last < (1u32 << (e as u32))) by (bit_vector)
        requires
            0 < (e as u32) < 32u32,
    ;
    assert(last >> (nbits % 32) == last >> (e as u32));
    assert(1u32 << e == 1u32 << (e as u32));
}

/// for e>0, mask_for_bits(n) == (1<<e)-1 (mask conversion bridge).
pub proof fn lemma_masks_agree(nbits: usize)
    requires
        nbits % 32 > 0,
    ensures
        trailing_mask(nbits) == used_mask(nbits),
{
    assert(trailing_mask(nbits) == used_mask(nbits));
}

/// b < e = nbits%32 => 2^b < 2^e (set's flag stays below the tail mask).
pub proof fn lemma_flag_below_mask(nbits: usize, b: usize)
    requires
        nbits % 32 > 0,
        b < nbits % 32,
    ensures
        (1u32 << b) < (1u32 << (nbits % 32)),
{
    let e = nbits % 32;
    assert((1u32 << (b as u32)) < (1u32 << (e as u32))) by (bit_vector)
        requires
            (b as u32) < (e as u32),
            (e as u32) <= 31u32,
    ;
    assert(1u32 << b == 1u32 << (b as u32));
    assert(1u32 << e == 1u32 << (e as u32));
}

/// clearing a bit is monotone: a & !flag <= a (unsigned).
pub proof fn lemma_and_decreases(a: u32, flag: u32)
    ensures
        a & !flag <= a,
{
    assert(a & !flag <= a) by (bit_vector);
}

/// two bits in one block never interfere: setting/clearing bit b leaves
/// bit bj (b != bj) untouched.
pub proof fn lemma_other_bit_untouched(old_block: u32, b: usize, bj: usize, x: bool)
    requires
        b < 32,
        bj < 32,
        b != bj,
    ensures
        x ==> ((old_block | (1u32 << b)) & (1u32 << bj)) == (old_block & (1u32 << bj)),
        !x ==> ((old_block & !(1u32 << b)) & (1u32 << bj)) == (old_block & (1u32 << bj)),
{
    let p = 1u32 << b;
    let q = 1u32 << bj;
    assert(p == 1u32 << (b as u32)) by {
        assert(1u32 << b == 1u32 << (b as u32));
    }
    assert(q == 1u32 << (bj as u32)) by {
        assert(1u32 << bj == 1u32 << (bj as u32));
    }
    assert(p & q == 0u32) by (bit_vector)
        requires
            p == 1u32 << (b as u32),
            q == 1u32 << (bj as u32),
            (b as u32) != (bj as u32),
    ;
    if x {
        assert((old_block | p) & q == old_block & q) by (bit_vector)
            requires
                p & q == 0u32,
        ;
    } else {
        assert((old_block & !p) & q == old_block & q) by (bit_vector)
            requires
                p & q == 0u32,
        ;
    }
}

/// x < 2^(b+1) => after clearing bit b it is < 2^b (the value-level fact
///     sealing pop's tail argument).
pub proof fn lemma_clear_top_below(x: u32, b: usize)
    requires
        b <= 30,
        x < (1u32 << (b + 1)),
    ensures
        (x & !(1u32 << b)) < (1u32 << b),
{
    let bb: u32 = b as u32;
    assert(bb <= 30u32);
    assert(1u32 << (bb + 1u32) == 1u32 << (b + 1)) by {
        assert(bb + 1u32 == (b + 1) as u32);
        assert(1u32 << ((b + 1) as u32) == 1u32 << (b + 1));
    }
    assert((x & !(1u32 << bb)) < (1u32 << bb)) by (bit_vector)
        requires
            bb <= 30u32,
            x < (1u32 << (bb + 1u32)),
    ;
    assert(1u32 << bb == 1u32 << b) by {
        assert(1u32 << (b as u32) == 1u32 << b);
    }
    assert(x & !(1u32 << bb) == x & !(1u32 << b));
    assert((1u32 << bb) == (1u32 << b));
}

/// power-shift relation: 2^e < 2^(e+1) (e <= 30, within u32).
pub proof fn lemma_pow_mono(e: usize)
    requires
        e <= 30,
    ensures
        (1u32 << e) < (1u32 << (e + 1)),
{
    assert((1u32 << (e as u32)) < (1u32 << ((e + 1) as u32))) by (bit_vector)
        requires
            (e as u32) <= 30u32,
    ;
    assert(1u32 << e == 1u32 << (e as u32));
    assert(1u32 << (e + 1) == 1u32 << ((e + 1) as u32));
}

// ---------------------------------------------------------------------------
// process family (or/and/difference/xor/nand/nor/xnor, Origin Rust:
// lib.rs:643-656). Bit-level lemmas for word-wise ops: the block op's
// value at bit b is the boolean operation on the operands' bits at b.
// ---------------------------------------------------------------------------

/// or bit: ((x | y) & flag) != 0 is equivalent to
///     (x&flag)!=0 || (y&flag)!=0.
pub proof fn lemma_or_bit(x: u32, y: u32, b: usize)
    requires
        b <= 31usize,
    ensures
        ((x | y) & (1u32 << b)) != 0u32
            <==> ((x & (1u32 << b)) != 0u32 || (y & (1u32 << b)) != 0u32),
{
    assert((((x | y) & (1u32 << b)) != 0u32)
        == (((x & (1u32 << b)) != 0u32) || ((y & (1u32 << b)) != 0u32))) by (bit_vector)
        requires
            b <= 31usize,
    ;
}

/// and bit: ((x & y) & flag) != 0 is equivalent to
///     (x&flag)!=0 && (y&flag)!=0.
pub proof fn lemma_and_bit(x: u32, y: u32, b: usize)
    requires
        b <= 31usize,
    ensures
        ((x & y) & (1u32 << b)) != 0u32
            <==> ((x & (1u32 << b)) != 0u32 && (y & (1u32 << b)) != 0u32),
{
    assert((((x & y) & (1u32 << b)) != 0u32)
        == (((x & (1u32 << b)) != 0u32) && ((y & (1u32 << b)) != 0u32))) by (bit_vector)
        requires
            b <= 31usize,
    ;
}

/// difference bit (difference, word op = x & !y):
///     ((x & (all-ones ^ y)) & flag) != 0 is equivalent to
///     (x&flag)!=0 && (y&flag)==0.
pub proof fn lemma_andnot_bit(x: u32, y: u32, b: usize)
    requires
        b <= 31usize,
    ensures
        ((x & (4294967295u32 ^ y)) & (1u32 << b)) != 0u32
            <==> ((x & (1u32 << b)) != 0u32 && (y & (1u32 << b)) == 0u32),
{
    assert((((x & (4294967295u32 ^ y)) & (1u32 << b)) != 0u32)
        == (((x & (1u32 << b)) != 0u32) && ((y & (1u32 << b)) == 0u32))) by (bit_vector)
        requires
            b <= 31usize,
    ;
}

/// xor bit: ((x ^ y) & flag) != 0 is equivalent to
///     (x&flag)!=0 != (y&flag)!=0.
pub proof fn lemma_xor_bit(x: u32, y: u32, b: usize)
    requires
        b <= 31usize,
    ensures
        ((x ^ y) & (1u32 << b)) != 0u32
            <==> (((x & (1u32 << b)) != 0u32) != ((y & (1u32 << b)) != 0u32)),
{
    assert((((x ^ y) & (1u32 << b)) != 0u32)
        == (((x & (1u32 << b)) != 0u32) != ((y & (1u32 << b)) != 0u32))) by (bit_vector)
        requires
            b <= 31usize,
    ;
}

/// XOR difference is nonzero iff the two values differ (process's
/// changed_bits reading).
pub proof fn lemma_diff_nonzero(a: u32, b: u32)
    ensures
        (a ^ b) != 0u32 <==> a != b,
{
    assert(((a ^ b) != 0u32) == (a != b)) by (bit_vector);
}

/// or stays below: a, b < 2^e => (a|b) < 2^e (e <= 31).
pub proof fn lemma_or_below(a: u32, b: u32, e: usize)
    requires
        e <= 31usize,
        a < (1u32 << e),
        b < (1u32 << e),
    ensures
        (a | b) < (1u32 << e),
{
    /* spec-domain shift widening: bridge via the in-machine form first
       (1u32 << (e as u32)), then settle back after the bv close. */
    assert(1u32 << e == 1u32 << (e as u32));
    assert((a | b) < (1u32 << (e as u32))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            a < (1u32 << (e as u32)),
            b < (1u32 << (e as u32)),
    ;
}

/// and stays below: a, b < 2^e => (a&b) < 2^e.
pub proof fn lemma_and_below(a: u32, b: u32, e: usize)
    requires
        e <= 31usize,
        a < (1u32 << e),
        b < (1u32 << e),
    ensures
        (a & b) < (1u32 << e),
{
    /* spec-domain shift widening: bridge via the in-machine form first
       (1u32 << (e as u32)), then settle back after the bv close. */
    assert(1u32 << e == 1u32 << (e as u32));
    assert((a & b) < (1u32 << (e as u32))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            a < (1u32 << (e as u32)),
            b < (1u32 << (e as u32)),
    ;
}

/// xor stays below: a, b < 2^e => (a^b) < 2^e.
pub proof fn lemma_xor_below(a: u32, b: u32, e: usize)
    requires
        e <= 31usize,
        a < (1u32 << e),
        b < (1u32 << e),
    ensures
        (a ^ b) < (1u32 << e),
{
    /* spec-domain shift widening: bridge via the in-machine form first
       (1u32 << (e as u32)), then settle back after the bv close. */
    assert(1u32 << e == 1u32 << (e as u32));
    assert((a ^ b) < (1u32 << (e as u32))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            a < (1u32 << (e as u32)),
            b < (1u32 << (e as u32)),
    ;
}



/// nand tail-block bit: with the ones-complemented input L1 = old|compl
///     and the other tail o (< 2^e), bit b (< e) of the masked op value
///     (L1 & o)^all-ones & mask <=> !(bit b of old && bit b of o).
pub proof fn lemma_nand_tail_bit(old: u32, o: u32, e: usize, b: usize)
    requires
        e <= 31usize,
        b <= 31usize,
        b < e,
        old < (1u32 << e),
        o < (1u32 << e),
    ensures
        ((((((old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32))) & o) ^ 4294967295u32)
            & (((1u32 << e) - 1u32) as u32)) & (1u32 << b)) != 0u32)
            <==> (!((old & (1u32 << b)) != 0u32 && (o & (1u32 << b)) != 0u32)),
{
    assert(1u32 << e == 1u32 << (e as u32));
    let l1: u32 = old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32));
    let op: u32 = (l1 & o) ^ 4294967295u32;
    let mask: u32 = ((1u32 << e) - 1u32) as u32;
    let flag: u32 = 1u32 << b;
    assert((((((l1 & o) ^ 4294967295u32) & mask) & flag) != 0u32)
        == (!((old & flag) != 0u32 && (o & flag) != 0u32))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            (b as u32) < (e as u32),
            l1 == old | (4294967295u32
                ^ (((1u32 << (e as u32)) - 1u32) as u32)),
            mask == ((1u32 << (e as u32)) - 1u32) as u32,
            flag == 1u32 << (b as u32),
            old < (1u32 << (e as u32)),
            o < (1u32 << (e as u32)),
    ;
}

/// nor tail-block bit: bit b of the masked op <=> boolean nor (input via
/// the with-ones L1).
pub proof fn lemma_nor_tail_bit(old: u32, o: u32, e: usize, b: usize)
    requires
        e <= 31usize,
        b <= 31usize,
        b < e,
        old < (1u32 << e),
        o < (1u32 << e),
    ensures
        (((((((old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32)))) | o) ^ 4294967295u32)) & (((1u32 << e) - 1u32) as u32)) & (1u32 << b)) != 0u32
            <==> (!( (old & (1u32 << b)) != 0u32 || (o & (1u32 << b)) != 0u32)),
{
    assert(1u32 << e == 1u32 << (e as u32));
    let l1: u32 = old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32));
    let opn: u32 = (l1 | o) ^ 4294967295u32;
    let m: u32 = ((1u32 << (e as u32)) - 1u32) as u32;
    let flag: u32 = 1u32 << b;
    assert((((opn & m) & flag) != 0u32) == ((!( (old & flag) != 0u32 || (o & flag) != 0u32)))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            (b as u32) < (e as u32),
            m == ((1u32 << (e as u32)) - 1u32) as u32,
            l1 == old | (4294967295u32 ^ (((1u32 << (e as u32)) - 1u32) as u32)),
            opn == ((l1 | o) ^ 4294967295u32),
            flag == 1u32 << (b as u32),
            old < (1u32 << (e as u32)),
            o < (1u32 << (e as u32)),
    ;
}

/// xnor tail-block bit: bit b of the masked op <=> boolean xnor (input
/// via the with-ones L1).
pub proof fn lemma_xnor_tail_bit(old: u32, o: u32, e: usize, b: usize)
    requires
        e <= 31usize,
        b <= 31usize,
        b < e,
        old < (1u32 << e),
        o < (1u32 << e),
    ensures
        (((((((old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32)))) ^ o) ^ 4294967295u32)) & (((1u32 << e) - 1u32) as u32)) & (1u32 << b)) != 0u32
            <==> (((old & (1u32 << b)) != 0u32) == ((o & (1u32 << b)) != 0u32)),
{
    assert(1u32 << e == 1u32 << (e as u32));
    let l1: u32 = old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32));
    let opn: u32 = (l1 ^ o) ^ 4294967295u32;
    let m: u32 = ((1u32 << (e as u32)) - 1u32) as u32;
    let flag: u32 = 1u32 << b;
    assert((((opn & m) & flag) != 0u32) == ((((old & flag) != 0u32) == ((o & flag) != 0u32)))) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            (b as u32) < (e as u32),
            m == ((1u32 << (e as u32)) - 1u32) as u32,
            l1 == old | (4294967295u32 ^ (((1u32 << (e as u32)) - 1u32) as u32)),
            opn == ((l1 ^ o) ^ 4294967295u32),
            flag == 1u32 << (b as u32),
            old < (1u32 << (e as u32)),
            o < (1u32 << (e as u32)),
    ;
}

/// nand tail changed-equivalence: masked op == old is equivalent to
/// op == L1.
pub proof fn lemma_nand_last_iff(old: u32, o: u32, e: usize)
    requires
        e <= 31usize,
        old < (1u32 << e),
        o < (1u32 << e),
    ensures
        (((((old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32)))) & o) ^ 4294967295u32) & (((1u32 << e) - 1u32) as u32)) == old
            <==> (((((old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32)))) & o) ^ 4294967295u32)) == (old | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32))),
{
    assert(1u32 << e == 1u32 << (e as u32));
    let m: u32 = ((1u32 << (e as u32)) - 1u32) as u32;
    let l1: u32 = old | (4294967295u32 ^ (((1u32 << (e as u32)) - 1u32) as u32));
    let opn: u32 = (l1 & o) ^ 4294967295u32;
    assert(((opn & m) == old) == (opn == l1)) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            m == ((1u32 << (e as u32)) - 1u32) as u32,
            l1 == old | (4294967295u32 ^ (((1u32 << (e as u32)) - 1u32) as u32)),
            opn == ((l1 & o) ^ 4294967295u32),
            old < (1u32 << (e as u32)),
            o < (1u32 << (e as u32)),
    ;
}

/// bit semantics of the tail ones-fill input: for b < e,
/// ((last | compl) & flag) == (last & flag).
pub proof fn lemma_with_ones_bit(last: u32, e: usize, b: usize)
    requires
        e <= 31usize,
        b <= 31usize,
        b < e,
    ensures
        ((last | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32))) & (1u32 << b))
            == (last & (1u32 << b)),
{
    assert(1u32 << e == 1u32 << (e as u32));
    assert(1u32 << b == 1u32 << (b as u32));
    let complm: u32 = 4294967295u32 ^ (((1u32 << e) - 1u32) as u32);
    let flag: u32 = 1u32 << b;
    assert(((last | complm) & flag) == (last & flag)) by (bit_vector)
        requires
            (b as u32) < (e as u32),
            (e as u32) <= 31u32,
            complm == 4294967295u32 ^ (((1u32 << (e as u32)) - 1u32) as u32),
            flag == 1u32 << (b as u32),
    ;
}

/// mask recovery of the tail ones-fill: last & compl == 0 (the
/// trailing-zero form) => (last|compl)&mask == last.
pub proof fn lemma_with_ones_masked(last: u32, e: usize)
    requires
        e <= 31usize,
        last < (1u32 << e),
    ensures
        (last | (4294967295u32 ^ (((1u32 << e) - 1u32) as u32)))
            & (((1u32 << e) - 1u32) as u32) == last,
{
    let mask: u32 = ((1u32 << e) - 1u32) as u32;
    let complm: u32 = 4294967295u32 ^ mask;
    assert(1u32 << e == 1u32 << (e as u32));
    assert(((last | complm) & mask) == last) by (bit_vector)
        requires
            (e as u32) <= 31u32,
            mask == ((1u32 << (e as u32)) - 1u32) as u32,
            complm == 4294967295u32 ^ (((1u32 << (e as u32)) - 1u32) as u32),
            last < (1u32 << (e as u32)),
    ;
}

/// Sequence equality bridge (process's changed conclusion: blocks pairwise
///      equal <=> seq equal; two-way wrapper of vstd::seq::lemma_seq_ext_equal).
pub proof fn lemma_seq_eq_iff<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.len() == s2.len(),
    ensures
        (s1 == s2) <==> seq_ptwise(s1, s2),
{
    if s1 == s2 {
        assert(seq_ptwise(s1, s2)) by {
            assert forall|w2: int| 0 <= w2 < s1.len() implies s1[w2] == s2[w2] by {
                assert(s1[w2] == s2[w2]);
            }
        }
    } else {
        if seq_ptwise(s1, s2) {
            lemma_seq_ext_equal(s1, s2);
            assert(false);
        }
        assert(!seq_ptwise(s1, s2));
    }
}

// ---------------------------------------------------------------------------
// popcount family (count_ones/count_zeros): machine bit tests, the bound,
// the segment-split induction, the block<->bit correspondence, the
// tail-stability fact and the block<->bit-count bridges.
// ---------------------------------------------------------------------------

/// popc_seq is nonnegative and bounded per counted position.
pub proof fn lemma_popc_seq_bound(s: Seq<u32>, k: usize)
    ensures
        0 <= popc_seq(s, k) <= 32 * (k as int),
    decreases
        k,
{
    if k == 0 {
    } else {
        lemma_popc_seq_bound(s, (k - 1) as usize);
        lemma_popc_range(s[(k - 1) as int], 32);
    }
}

/// popc_seq is monotone in the block count.
pub proof fn lemma_popc_seq_mono(s: Seq<u32>, k: usize, m: usize)
    requires
        (k as int) <= s.len(),
        k <= m,
        (m as int) <= s.len(),
    ensures
        popc_seq(s, k) <= popc_seq(s, m),
    decreases
        m - k,
{
    if k == m {
    } else {
        lemma_popc_seq_mono(s, k, (m - 1) as usize);
        lemma_popc_range(s[(m - 1) as int], 32);
        assert(popc_seq(s, m) == popc_seq(s, (m - 1) as usize)
            + popc(s[(m - 1) as int], 32));
    }
}

/// zeros_seq is bounded by 32 per block.
pub proof fn lemma_zeros_bound(s: Seq<u32>, k: usize)
    requires
        (k as int) <= s.len(),
    ensures
        0 <= zeros_seq(s, k) <= 32 * (k as int),
    decreases
        k,
{
    if k == 0 {
    } else {
        lemma_zeros_bound(s, (k - 1) as usize);
        lemma_popc_range(s[(k - 1) as int], 32);
        assert(zeros_seq(s, k) == zeros_seq(s, (k - 1) as usize)
            + (32 - popc(s[(k - 1) as int], 32)));
    }
}

/// popc range: between 0 and the counted positions.
pub proof fn lemma_popc_range(x: u32, k: usize)
    ensures
        0 <= popc(x, k) <= (k as int),
    decreases
        k,
{
    if k == 0 {
    } else {
        lemma_popc_range(x, (k - 1) as usize);
        assert(popc(x, k) == popc(x, (k - 1) as usize)
            + (if (x & (1u32 << ((k - 1) as usize))) != 0u32 { 1int } else { 0int }));
    }
}

/// count_bits never exceeds the counted positions.
pub proof fn lemma_count_bits_bound(s: Seq<u32>, n: usize, i: usize, j: usize)
    requires
        i <= j,
        j <= n,
    ensures
        count_bits(s, n, i, j) <= ((j as int) - (i as int)),
    decreases
        j - i,
{
    if i >= j {
    } else {
        assert(count_bits(s, n, i, j) == (if bit_at(s, n, i) { 1int } else { 0int })
            + count_bits(s, n, (i + 1) as usize, j));
        lemma_count_bits_bound(s, n, (i + 1) as usize, j);
    }
}

/// the intrinsic's counting step agrees with the flag-based bit test:
///     (x >> j) & 1 is nonzero iff bit j of x is set.
pub proof fn lemma_bit_shift_test(x: u32, j: usize)
    requires
        j <= 31usize,
    ensures
        (((x >> j) & 1u32) != 0u32) <==> ((x & (1u32 << j)) != 0u32),
{
    assert((((x >> j) & 1u32) != 0u32) == (((x & (1u32 << j)) != 0u32))) by (bit_vector)
        requires
            j <= 31usize,
    ;
    assert(1u32 << j == 1u32 << (j as u32));
}

/// popc never exceeds the counted positions.
pub proof fn lemma_popc_bound(x: u32, k: usize)
    requires
        k <= 32,
    ensures
        popc(x, k) <= (k as int),
    decreases
        k,
{
    if k == 0 {
    } else {
        lemma_popc_bound(x, (k - 1) as usize);
        assert(popc(x, k) == popc(x, (k - 1) as usize)
            + (if (x & (1u32 << ((k - 1) as usize))) != 0u32 { 1int } else { 0int }));
    }
}

/// count over [i, m) splits at j: counts compose additively.
pub proof fn lemma_count_split(s: Seq<u32>, n: usize, i: usize, j: usize, m: usize)
    requires
        i <= j,
        j <= m,
        m <= n,
    ensures
        count_bits(s, n, i, j) + count_bits(s, n, j, m) == count_bits(s, n, i, m),
    decreases
        m - i,
{
    if i == j {
        assert(count_bits(s, n, j, m) == count_bits(s, n, i, m));
    } else {
        // peel from the low end (the definition peels bit i)
        assert(count_bits(s, n, i, m) == (if bit_at(s, n, i) { 1int } else { 0int })
            + count_bits(s, n, (i + 1) as usize, m));
        assert(count_bits(s, n, i, j) == (if bit_at(s, n, i) { 1int } else { 0int })
            + count_bits(s, n, (i + 1) as usize, j));
        lemma_count_split(s, n, (i + 1) as usize, j, m);
    }
}

/// block-local correspondence: counting set bits at positions [32w, 32w+k)
///     equals popc of block w over its low k bits.
pub proof fn lemma_block_count(s: Seq<u32>, n: usize, w: usize, k: usize)
    requires
        k <= 32,
        (w as int) < s.len(),
        32 * (w as int) + (k as int) <= (n as int),
    ensures
        count_bits(s, n, (32 * w) as usize, (32 * w + k) as usize) == popc(s[w as int], k),
    decreases
        k,
{
    if k == 0 {
    } else {
        lemma_block_count(s, n, w, (k - 1) as usize);
        let lo: usize = ((32 * (w as int)) as usize);
        let idx_int = (lo as int) + ((k - 1) as int);
        let idx = idx_int as usize;
        assert(idx_int < n as int);
        assert((idx_int / 32) == (w as int)) by {
            assert(idx_int == 32 * (w as int) + ((k - 1) as int));
            assert((k - 1) < 32);
        }
        assert((idx % 32) as int == ((k - 1) as int)) by {
            assert(idx_int == 32 * (w as int) + ((k - 1) as int));
            assert((k - 1) < 32);
        }
        assert(bit_at(s, n, idx) == ((s[w as int] & (1u32 << ((k - 1) as usize))) != 0u32));
        // peel the last position off the count via the split lemma; the
        // singleton count unfolds definitionally
        lemma_count_split(s, n, lo, idx, (idx + 1) as usize);
        assert(count_bits(s, n, idx, (idx + 1) as usize)
            == (if bit_at(s, n, idx) { 1int } else { 0int })
                + count_bits(s, n, (idx + 1) as usize, (idx + 1) as usize));
        assert(count_bits(s, n, (idx + 1) as usize, (idx + 1) as usize) == 0int);
        assert((idx + 1) as int == 32 * (w as int) + (k as int));
        assert(popc(s[w as int], k) == popc(s[w as int], (k - 1) as usize)
            + (if (s[w as int] & (1u32 << ((k - 1) as usize))) != 0u32 { 1int } else { 0int }));
    }
}

/// popc stability under a zero tail: x < 2^e => bits >= e do not count.
pub proof fn lemma_popc_stable(x: u32, e: usize, k: usize)
    requires
        e <= k,
        k <= 32,
        e <= 31usize,
        x < (1u32 << e),
    ensures
        popc(x, k) == popc(x, e),
    decreases
        k - e,
{
    if k == e {
    } else {
        lemma_popc_stable(x, e, (k - 1) as usize);
        assert((x & (1u32 << ((k - 1) as usize))) == 0u32) by (bit_vector)
            requires
                e <= 31usize,
                ((k - 1) as u32) >= (e as u32),
                x < (1u32 << (e as u32)),
        ;
        assert(popc(x, k) == popc(x, (k - 1) as usize)
            + (if (x & (1u32 << ((k - 1) as usize))) != 0u32 { 1int } else { 0int }));
    }
}

/// full-block prefix: popc_seq over w blocks equals the bit count of the
///     flat prefix [0, 32w).
pub proof fn lemma_popc_seq(s: Seq<u32>, n: usize, w: usize)
    requires
        (w as int) <= s.len(),
        32 * (w as int) <= (n as int),
    ensures
        popc_seq(s, w) == count_bits(s, n, 0, (32 * w) as usize),
    decreases
        w,
{
    if w == 0 {
    } else {
        lemma_popc_seq(s, n, (w - 1) as usize);
        lemma_block_count(s, n, (w - 1) as usize, 32);
        lemma_count_split(s, n, 0, (32 * (w - 1)) as usize, (32 * w) as usize);
        assert(popc_seq(s, w) == popc_seq(s, (w - 1) as usize)
            + popc(s[(w - 1) as int], 32));
    }
}

/// per-block complement: zeros + ones == 32 * blocks.
pub proof fn lemma_zeros_popc(s: Seq<u32>, k: usize)
    requires
        (k as int) <= s.len(),
    ensures
        zeros_seq(s, k) + popc_seq(s, k) == 32 * (k as int),
    decreases
        k,
{
    if k == 0 {
    } else {
        lemma_zeros_popc(s, (k - 1) as usize);
        lemma_popc_bound(s[(k - 1) as int], 32);
        assert(zeros_seq(s, k) == zeros_seq(s, (k - 1) as usize)
            + (32 - popc(s[(k - 1) as int], 32)));
        assert(popc_seq(s, k) == popc_seq(s, (k - 1) as usize)
            + popc(s[(k - 1) as int], 32));
    }
}

/// constant-bit range count: every bit in [lo, hi) equal to b.
pub proof fn lemma_count_range_const(s: Seq<u32>, n: usize, lo: usize, hi: usize, b: bool)
    requires
        lo <= hi,
        hi <= n,
        forall|h: usize| lo <= h && h < hi ==> bit_at(s, n, h) == b,
    ensures
        count_bits(s, n, lo, hi) == (if b { ((hi as int) - (lo as int)) } else { 0int }),
    decreases
        hi - lo,
{
    if lo >= hi {
        assert(lo == hi);
    } else {
        assert(lo + 1 <= hi);
        lemma_count_range_const(s, n, (lo + 1) as usize, hi, b);
        assert(count_bits(s, n, lo, hi) == (if bit_at(s, n, lo) { 1int } else { 0int })
            + count_bits(s, n, (lo + 1) as usize, hi));
        assert(bit_at(s, n, lo) == b);
        assert(count_bits(s, n, lo, hi) == (if b { 1int } else { 0int })
            + (if b { ((hi as int) - ((lo + 1) as int)) } else { 0int }));
    }
}

/// every bit constant: the count is all-or-nothing.
pub proof fn lemma_count_const(s: Seq<u32>, n: usize, b: bool)
    requires
        forall|h: usize| h < n ==> bit_at(s, n, h) == b,
    ensures
        count_bits(s, n, 0, n) == (if b { (n as int) } else { 0int }),
{
    lemma_count_range_const(s, n, 0, n, b);
}

/// all bits constant b except one position carrying !b.
pub proof fn lemma_count_const_except(s: Seq<u32>, n: usize, exc: usize, b: bool)
    requires
        1 <= n,
        exc < n,
        forall|h: usize| h < n && h != exc ==> bit_at(s, n, h) == b,
        bit_at(s, n, exc) == !b,
    ensures
        count_bits(s, n, 0, n) == (if b { (n - 1) as int } else { 1int }),
{
    // split around the exception position
    lemma_count_split(s, n, 0, exc, n);
    lemma_count_split(s, n, exc, (exc + 1) as usize, n);
    lemma_count_range_const(s, n, 0, exc, b);
    lemma_count_range_const(s, n, (exc + 1) as usize, n, b);
    assert(count_bits(s, n, exc, (exc + 1) as usize)
        == (if !b { 1int } else { 0int })) by {
        assert(count_bits(s, n, exc, (exc + 1) as usize)
            == (if bit_at(s, n, exc) { 1int } else { 0int })
                + count_bits(s, n, (exc + 1) as usize, (exc + 1) as usize));
        assert(count_bits(s, n, (exc + 1) as usize, (exc + 1) as usize) == 0int);
        assert(bit_at(s, n, exc) == !b);
    }
}

/// block<->bit bridge (the doc semantics of count_ones): with the length
///     and trailing-zero invariants, popc_seq over all blocks equals the
///     flat count of set bits among the nbits.
pub proof fn lemma_popc_seq_is_count(s: Seq<u32>, n: usize)
    requires
        s.len() == (blocks_for_bits(n) as int),
        n % 32 == 0 || s[(s.len() - 1) as int] < (1u32 << (n % 32)),
    ensures
        popc_seq(s, s.len() as usize) == count_bits(s, n, 0, n),
{
    let len = s.len() as usize;
    let e = n % 32;
    if e == 0 {
        assert(len == (n as int) / 32) by {
            assert(n as int == 32 * ((n as int) / 32));
        }
        lemma_popc_seq(s, n, len);
        assert((32 * len) as int == n as int);
    } else {
        assert(len == (n as int) / 32 + 1) by {
            assert(n as int == 32 * ((n as int) / 32) + e);
        }
        lemma_popc_seq(s, n, (len - 1) as usize);
        lemma_block_count(s, n, (len - 1) as usize, e);
        lemma_count_split(s, n, 0, (32 * (len - 1)) as usize, n);
        lemma_popc_stable(s[(len - 1) as int], e, 32);
        assert(popc_seq(s, len) == popc_seq(s, (len - 1) as usize)
            + popc(s[(len - 1) as int], 32));
        assert((32 * (len - 1)) as int == n as int - e);
    }
}

// ===========================================================================
// The closing coverage diff-set batch additions, appended at the file tail
// so the incremental SMT context of the preceding obligations is
// undisturbed:
//   * the borrow family: blocks/blocks(), iter/iter(), the Iter and
//     IntoIter cursor materializations, Index via the get bridge;
//   * grow, append, split_off (the variable-shift family);
//   * shrink_to_fit (on the header Vec injection).
// Lossy-abstraction disclosure (borrow family): the upstream
// Iter/IntoIter/Blocks ride on core::ops::Range / alloc::rc::Rc /
// slice::Iter compounds, none of which has a vstd spec, so they are
// carried by the equivalent "vector reference + pos cursor (+ end)"
// index model (the slab IterExec/IntoIterExec precedent):
//   - Iter: bit_vec reference + [pos, end) cursor; next() reads
//     bit_vec.get(pos) -- the upstream .unwrap() never fires because
//     pos < end == nbits, which is exactly the machine obligation;
//   - IntoIter: the owned BitVec + [pos, end) cursor (the BitVec
//     handover of into_iter materialized as a field);
//   - Blocks: the storage reference + [pos, len) cursor over whole
//     blocks (the slice::Iter clone-into-value tier).
// The Rc<RefCell> side-carriers (iter_mut/IterMut/MutBorrowedBit/
// get_mut/get_unchecked_mut) stay blocked: no vstd Rc/RefCell model
// (harness-inventory evidence).
// ===========================================================================

impl BitVec {

    /// Origin Rust: impl<B: BitBlock> Index<usize> for BitVec<B> {
    ///     type Output = bool;
    ///     fn index(&self, i: usize) -> &bool {
    ///         if self.get(i).expect("index out of bounds") { &true } else { &false } } }
    ///     (lib.rs:396-405; the &true/&false statics are an upstream
    ///     borrowing trick -- the value tier is carried here. The
    ///     "index out of bounds" panic of the expect is the caller's
    ///     contractualized obligation; the readable tier runs through
    ///     the verified get, so Index's semantics is the get bridge.)
    pub exec fn index_exec(&self, i: usize) -> (r: bool)
        requires
            inv(self),
            i < self.nbits,
        ensures
            r == bit_at(self.storage@, self.nbits, i),
    {
        match self.get(i) {
            Some(b) => b,
            None => panic!("index out of bounds"),
        }
    }

    /// Origin Rust: pub fn blocks(&self) -> Blocks<'_, B> {
    ///     Blocks { iter: self.storage.iter() } } (lib.rs:666-672; the
    ///     slice::Iter cursor materialized as the storage reference +
    ///     pos pair, see the BlocksExec disclosure above.)
    /// Upstream doc (lib.rs:665-665):
    ///   Iterator over the underlying blocks of data
    pub exec fn blocks(&self) -> (r: BlocksExec)
        requires
            inv(self),
        ensures
            blocks_inv(&r),
            r.pos == 0,
            r.end == self.storage@.len(),
            r.storage@ == self.storage@,
    {
        BlocksExec { storage: &self.storage, pos: 0, end: self.storage.len() }
    }

    /// Origin Rust: pub fn iter(&self) -> Iter<'_, B> {
    ///     self.ensure_invariant();
    ///     Iter { bit_vec: self, range: 0..self.nbits } } (lib.rs:1344-1350;
    ///     the Range cursor as the [pos, end) pair, see the IterExec
    ///     disclosure above.)
    /// Upstream doc (lib.rs:1333-1340):
    ///   Returns an iterator over the elements of the vector in order.
    pub exec fn iter(&self) -> (r: IterExec)
        requires
            inv(self),
        ensures
            iter_inv(&r),
            r.bit_vec == self,
            r.pos == 0,
            r.end == self.nbits,
    {
        IterExec { bit_vec: self, pos: 0, end: self.nbits }
    }

    /// Origin Rust: pub fn shrink_to_fit(&mut self) {
    ///     self.storage.shrink_to_fit(); } (lib.rs:1865-1867; rides on
    ///     the header Vec::shrink_to_fit injection: the entries view is
    ///     invariant, all used bits keep their values.)
    /// Upstream doc (lib.rs:1859-1864):
    ///   Shrinks the capacity of the underlying storage as much as
    ///   possible.
    ///   It will drop down as close as possible to the length but the
    ///   allocator may still inform the underlying storage that there
    ///   is space for a few more elements/bits.
    pub exec fn shrink_to_fit(&mut self)
        requires
            inv(old(self)),
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits,
            final(self).storage@ == old(self).storage@,
            forall|j: usize|
                j < old(self).nbits ==>
                bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
    {
        self.storage.shrink_to_fit();
        // the per-bit tier is the entries-view congruence (bit_at's
        // args are unchanged; nbits is a documentation parameter there)
    }

    /// Origin Rust: pub fn grow(&mut self, n: usize, value: bool) (lib.rs:1711-1750)
    ///     { self.ensure_invariant();
    ///       let new_nbits = self.nbits.checked_add(n).expect("capacity overflow");
    ///       let new_nblocks = blocks_for_bits::<B>(new_nbits);
    ///       let full_value = if value { !B::zero() } else { B::zero() };
    ///       let num_cur_blocks = blocks_for_bits::<B>(self.nbits);
    ///       if self.nbits % B::bits() > 0 {
    ///         let mask = mask_for_bits::<B>(self.nbits);
    ///         if value { self.storage[num_cur_blocks - 1] |= !mask; } }
    ///       let stop_idx = cmp::min(self.storage.len(), new_nblocks);
    ///       for idx in num_cur_blocks..stop_idx { self.storage[idx] = full_value; }
    ///       if new_nblocks > self.storage.len() {
    ///         let to_add = new_nblocks - self.storage.len();
    ///         self.storage.extend(iter::repeat_n(full_value, to_add)); }
    ///       self.nbits = new_nbits;
    ///       self.fix_last_block(); }
    ///     # Panics ("capacity overflow" of the checked_add) -> requires;
    ///     extend(repeat_n) transcribed as the equivalent push loop; the
    ///     mid-block writes of the compare-and-set loop are dead code
    ///     under len_inv (stop_idx == num_cur_blocks) -- transcribed
    ///     verbatim for fidelity; upstream's own comment admits the
    ///     bulk writes are "technically wrong" for the unused tail bits
    ///     and are masked back by the final fix_last_block, which is
    ///     exactly the obligation chain proven here.
    /// Upstream doc (lib.rs:1695-1700):
    ///   Grows the `BitVec` in-place, adding `n` copies of `value` to the `BitVec`.
    ///   # Panics
    ///   Panics if the new len overflows a `usize`.
    pub exec fn grow(&mut self, n: usize, value: bool)
        requires
            inv(old(self)),
            (old(self).nbits as int + n as int) <= usize::MAX as int,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits + n,
            forall|j: usize|
                j < old(self).nbits ==>
                bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            forall|j: usize|
                old(self).nbits <= j && j < final(self).nbits ==>
                bit_at(final(self).storage@, final(self).nbits, j) == value,
    {
        let new_nbits = self.nbits + n;
        let new_nblocks = blocks_for_bits_exec(new_nbits);
        let full_value: u32 = if value { 4294967295u32 } else { 0u32 };
        let num_cur_blocks = blocks_for_bits_exec(self.nbits);
        let ghost s0: Seq<u32> = self.storage@;
        proof {
            assert(s0 == old(self).storage@);
            assert(self.nbits == old(self).nbits);
            assert(num_cur_blocks == blocks_for_bits(self.nbits));
        }
        // the loop-entry frame (the tail OR, if any, has already fired)
        let ghost mut s1: Seq<u32> = Seq::empty();
        let ghost mut tail_mod: bool = false; // whether the tail OR fired
        let ghost mut tail_nv: u32 = 0u32; // the post-OR tail value
        let ghost mut tail_o: u32 = 0u32; // the pre-OR tail value
        let ghost mut msk: u32 = 0u32; // the tail mask, set when e > 0
        if self.nbits % 32 > 0 {
            let mask = mask_for_bits_exec(self.nbits);
            if value {
                let idx = (num_cur_blocks - 1) as usize;
                proof {
                    assert(len_inv(old(self)));
                    assert(blocks_for_bits(self.nbits) == num_cur_blocks);
                    assert(self.storage@.len() == num_cur_blocks as int);
                    assert(num_cur_blocks >= 1);
                    assert(idx < self.storage@.len());
                    assert(mask == trailing_mask(self.nbits));
                    assert(trailing_mask(self.nbits)
                        == ((1u32 << (self.nbits % 32)) - 1u32) as u32);
                    assert(1u32 << (self.nbits % 32)
                        == 1u32 << ((self.nbits % 32) as u32));
                    assert(mask == ((1u32 << ((self.nbits % 32) as u32)) - 1u32));
                    assert(idx as int == blocks_for_bits(self.nbits) as int - 1);
                }
                let blk = self.storage[idx];
                proof {
                    assert(blk == s0[idx as int]);
                }
                let nv = blk | (4294967295u32 ^ mask);
                self.storage.set(idx, nv);
                proof {
                    assert(self.storage@ == s0.update(idx as int, nv));
                    s1 = self.storage@;
                    tail_o = blk;
                    tail_nv = nv;
                    tail_mod = true;
                    msk = mask;
                    assert(s1.len() == s0.len());
                    assert forall|w2: usize| (w2 as int) < s1.len() && (w2 as int) != (idx as int)
                        implies s1[w2 as int] == s0[w2 as int] by { }
                    assert(s1[idx as int] == nv);
                }
            } else {
                // Origin Rust comment tier: "Extra bits are already zero by invariant."
                proof {
                    s1 = self.storage@;
                    assert(s1 == s0);
                }
            }
        } else {
            proof {
                s1 = self.storage@;
                assert(s1 == s0);
            }
        }
        /* Origin Rust: let stop_idx = cmp::min(self.storage.len(), new_nblocks);
           for idx in num_cur_blocks..stop_idx { self.storage[idx] = full_value; } */
        let stop_idx = if self.storage.len() < new_nblocks {
            self.storage.len()
        } else {
            new_nblocks
        };
        let mut idx: usize = num_cur_blocks;
        while idx < stop_idx
            invariant
                num_cur_blocks <= idx,
                idx <= stop_idx,
                stop_idx <= self.storage@.len(),
                self.storage@.len() == s1.len(),
                forall|w2: usize| (w2 as int) < s1.len()
                    && ((w2 as int) < num_cur_blocks || (w2 as int) >= (idx as int)) ==>
                    self.storage@[w2 as int] == s1[w2 as int],
                forall|w2: usize| (num_cur_blocks as int) <= (w2 as int)
                    && (w2 as int) < (idx as int) ==>
                    self.storage@[w2 as int] == full_value,
            decreases stop_idx - idx,
        {
            let ghost s_h = self.storage@;
            self.storage.set(idx, full_value);
            proof {
                assert(self.storage@ == s_h.update(idx as int, full_value));
            }
            idx = idx + 1;
        }
        proof {
            // the compare-and-set block writes are dead code under
            // len_inv: stop_idx == num_cur_blocks (storage.len() ==
            // blocks_for_bits(nbits) == num_cur_blocks, and
            // blocks_for_bits is monotone in the bit count)
            assert(s1.len() == blocks_for_bits(self.nbits) as int);
            assert((num_cur_blocks as int) <= (new_nblocks as int)) by {
                assert(blocks_for_bits(self.nbits) <= blocks_for_bits(new_nbits)) by {
                    assert(self.nbits <= new_nbits);
                }
            }
            assert(stop_idx == num_cur_blocks) by {
                assert(self.storage@.len() == num_cur_blocks as int);
            }
            assert forall|w2: usize| (w2 as int) < s1.len() implies
                self.storage@[w2 as int] == s1[w2 as int] by { }
        }
        /* Origin Rust: if new_nblocks > self.storage.len() {
           let to_add = new_nblocks - self.storage.len();
           self.storage.extend(iter::repeat_n(full_value, to_add)); } } */
        let ghost mut sE: Seq<u32> = Seq::empty();
        if new_nblocks > self.storage.len() {
            let to_add = new_nblocks - self.storage.len();
            proof {
                sE = self.storage@;
                assert(sE == s1);
                assert(self.storage@.len() == num_cur_blocks as int) by {
                    assert(len_inv(old(self)));
                    assert(old(self).storage@.len() == blocks_for_bits(old(self).nbits) as int);
                    assert(blocks_for_bits(old(self).nbits) == num_cur_blocks);
                    assert(old(self).nbits == self.nbits);
                    assert(s0 == old(self).storage@);
                    assert(s1.len() == s0.len());
                    assert(self.storage@.len() == s1.len());
                }
                // the fresh-block count: exactly the missing top blocks
                assert((to_add as int) == (new_nblocks as int) - (num_cur_blocks as int)) by { }
                assert((new_nblocks as int) == (num_cur_blocks as int) + (to_add as int)) by { }
            }
            let mut cnt: usize = 0;
            while cnt < to_add
                invariant
                    cnt <= to_add,
                    self.storage@.len() == num_cur_blocks as int + (cnt as int),
                    forall|w2: usize| (w2 as int) < num_cur_blocks ==>
                        self.storage@[w2 as int] == s1[w2 as int],
                    forall|m: usize| (num_cur_blocks as int) <= (m as int)
                        && (m as int) < self.storage@.len() ==>
                        self.storage@[m as int] == full_value,
                decreases to_add - cnt,
            {
                let ghost s_h = self.storage@;
                self.storage.push(full_value);
                proof {
                    assert(self.storage@ == s_h.push(full_value));
                }
                cnt = cnt + 1;
            }
        } else {
            proof {
                sE = self.storage@;
                assert(sE == s1);
                assert(self.storage@.len() == num_cur_blocks as int);
                // no fresh blocks: the new count is exactly the current one
                assert((new_nblocks as int) <= (num_cur_blocks as int)) by { }
                assert(new_nblocks == num_cur_blocks) by { }
                assert(self.storage@.len() == new_nblocks as int);
            }
        }
        // the extend tier finished at exactly blocks_for_bits(new_nbits)
        proof {
            assert(blocks_for_bits(new_nbits) == new_nblocks) by { }
            assert(self.storage@.len() == new_nblocks as int) by { }
        }
        self.nbits = new_nbits;
        proof {
            assert(blocks_for_bits(self.nbits) == new_nblocks) by { }
            assert(len_inv(self)) by { }
        }
        let ghost pre_fix = self.storage@;
        self.fix_last_block();
        proof {
            let nO = old(self).nbits;
            let nF = self.nbits;
            let e = nO % 32;
            let L = blocks_for_bits(nO);
            assert(s0 == old(self).storage@);
            assert(pre_fix.len() == new_nblocks as int);
            assert(nF == nO + n);
            // nO <= 32 * L (equality only when e == 0)
            assert((nO as int) <= 32 * (L as int)) by {
                assert((nO as int) == 32 * ((nO as int) / 32) + (e as int));
                assert(((nO as int) / 32) <= (L as int));
                assert((L as int) <= ((nO as int) / 32) + 1);
            }
            // (a) j < nO keeps its value
            assert forall|j: usize| j < nO implies
                bit_at(self.storage@, nF, j)
                    == bit_at(old(self).storage@, nO, j) by {
                assert(j < nF);
                int_div_bound_lemma(j, nO);
                let w = j / 32;
                let t = j % 32;
                assert(t < 32);
                assert((w as int) < (L as int)) by {
                    assert((j as int) / 32 < (L as int)) by {
                        assert((j as int) < (nO as int));
                        assert((j as int) <= 32 * (L as int) - 1);
                    }
                    assert((w as int) == (j as int) / 32);
                }
                if !tail_mod {
                    assert(pre_fix[w as int] == s1[w as int]);
                    assert(s1[w as int] == s0[w as int]);
                    assert(pre_fix[w as int] == s0[w as int]);
                } else {
                    // the tail OR fired: only position L-1 differs
                    if (w as int) == (L as int) - 1 {
                        assert((t as int) < (e as int)) by {
                            assert((nO as int) == 32 * ((L as int) - 1) + (e as int)) by {
                                assert((nO as int) == 32 * ((nO as int) / 32) + (e as int));
                                assert((e as int) > 0);
                                assert(((nO as int) / 32) == (L as int) - 1);
                            }
                            assert((j as int) == 32 * (w as int) + (t as int));
                            assert((j as int) < (nO as int));
                        }
                        // the OR fills only the unused tail bits: bits
                        // below e keep their values
                        assert((msk as u32) == ((1u32 << (e as u32)) - 1u32)) by {
                            assert(msk == trailing_mask(nO));
                            assert(trailing_mask(nO) == ((1u32 << (nO % 32)) - 1u32) as u32);
                            assert((nO % 32) == e);
                            assert(1u32 << (nO % 32) == 1u32 << ((nO % 32) as u32));
                            assert(1u32 << e == 1u32 << ((e) as u32));
                        }
                        assert(((4294967295u32 ^ msk) & (1u32 << ((t) as u32))) == 0u32) by (bit_vector)
                            requires
                                msk == ((1u32 << (e as u32)) - 1u32),
                                (t as u32) < (e as u32),
                                (e as u32) <= 31u32,
                        ;
                        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                        assert(((tail_nv & (1u32 << ((t) as u32))) != 0u32)
                            == ((tail_o & (1u32 << ((t) as u32))) != 0u32)) by (bit_vector)
                            requires
                                tail_nv == tail_o | (4294967295u32 ^ msk),
                                ((4294967295u32 ^ msk) & (1u32 << ((t) as u32))) == 0u32,
                        ;
                        assert(1u32 << (j % 32) == 1u32 << ((t) as u32));
                        assert(pre_fix[w as int] == s1[w as int]);
                        assert(s1[w as int] == tail_nv);
                        assert(s0[w as int] == tail_o);
                    } else {
                        assert(pre_fix[w as int] == s1[w as int]);
                        assert(s1[w as int] == s0[w as int]);
                        assert(pre_fix[w as int] == s0[w as int]);
                    }
                }
            }
            // (b) j in [nO, nF) reads the grown value
            assert forall|j: usize| nO <= j && j < nF implies
                bit_at(self.storage@, nF, j) == value by {
                assert(j < nF);
                int_div_bound_lemma(j, nF);
                let w = j / 32;
                let t = j % 32;
                assert(t < 32);
                assert((w as int) < (new_nblocks as int)) by {
                    assert((j as int) / 32 < (new_nblocks as int));
                    assert((w as int) == (j as int) / 32);
                }
                if (w as int) < (L as int) {
                    // the greedy tail of the old last block: e must be
                    // positive here (e == 0 would force w >= L)
                    assert((e as int) > 0) by {
                        if (e as int) == 0 {
                            assert((nO as int) == 32 * (L as int)) by {
                                assert((nO as int) == 32 * ((nO as int) / 32) + (e as int));
                                assert(((nO as int) / 32) == (L as int));
                            }
                            assert((j as int) >= (nO as int));
                            assert((w as int) == (j as int) / 32);
                            assert((w as int) >= (nO as int) / 32);
                            assert((w as int) >= (L as int));
                            assert((w as int) < (L as int));
                        }
                    }
                    assert((w as int) == (L as int) - 1) by {
                        assert((j as int) >= (nO as int));
                        assert((nO as int) > 32 * ((L as int) - 1));
                        assert((j as int) >= 32 * ((L as int) - 1));
                        assert((j as int) < 32 * (L as int));
                        assert((w as int) == (j as int) / 32);
                    }
                    assert((t as int) >= (e as int)) by {
                        assert((nO as int) == 32 * ((L as int) - 1) + (e as int));
                        assert((j as int) == 32 * (w as int) + (t as int));
                        assert((j as int) >= (nO as int));
                    }
                    if value {
                        // the OR sets every tail bit at t >= e
                        assert(tail_mod);
                        assert(pre_fix[w as int] == s1[w as int]);
                        assert(s1[w as int] == tail_nv);
                        assert((msk as u32) == ((1u32 << (e as u32)) - 1u32)) by {
                            assert(msk == trailing_mask(nO));
                            assert(trailing_mask(nO) == ((1u32 << (nO % 32)) - 1u32) as u32);
                            assert((nO % 32) == e);
                            assert(1u32 << (nO % 32) == 1u32 << ((nO % 32) as u32));
                            assert(1u32 << e == 1u32 << ((e) as u32));
                        }
                        assert(((4294967295u32 ^ msk) & (1u32 << ((t) as u32))) != 0u32) by (bit_vector)
                            requires
                                msk == ((1u32 << (e as u32)) - 1u32),
                                (e as u32) <= (t as u32),
                                (t as u32) <= 31u32,
                        ;
                        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                        assert((tail_nv & (1u32 << (t as u32))) != 0u32) by (bit_vector)
                            requires
                                tail_nv == tail_o | (4294967295u32 ^ msk),
                                ((4294967295u32 ^ msk) & (1u32 << (t as u32))) != 0u32,
                        ;
                        assert(1u32 << (j % 32) == 1u32 << ((t) as u32));
                    } else {
                        // the non-grown tail bits were zero by the old
                        // invariant, and the OR never fired for value false
                        assert(!tail_mod);
                        assert(pre_fix[w as int] == s1[w as int]);
                        assert(s1[w as int] == s0[w as int]);
                        assert(s0[w as int] < ((1u32 << (e as u32)) - 1u32 + 1u32)) by { }
                        assert(s0[w as int] < (1u32 << e)) by {
                            assert(trailing_zero(old(self)));
                            assert(blocks_for_bits(nO) == L);
                            assert(1u32 << (nO % 32) == 1u32 << ((nO % 32) as u32));
                            assert((nO % 32) == e);
                            assert(s0[w as int] == old(self).storage@[(L - 1) as int]);
                            assert(old(self).storage@[(L - 1) as int] < (1u32 << (nO as int % 32))) by { }
                            assert((1u32 << (nO as int % 32)) == (1u32 << ((nO % 32) as u32))) by { }
                            assert((1u32 << ((nO % 32) as u32)) == (1u32 << ((e) as u32))) by { }
                        }
                        assert(1u32 << e == 1u32 << ((e) as u32));
                        lemma_pow_lt_bit(s0[w as int], e, t);
                        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                        assert(1u32 << (j % 32) == 1u32 << ((t) as u32));
                    }
                } else {
                    // a full fresh block
                    assert(pre_fix[w as int] == full_value);
                    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                    if value {
                        assert((4294967295u32 & (1u32 << ((t) as u32))) != 0u32) by (bit_vector)
                            requires
                                (t as u32) <= 31u32,
                        ;
                        assert(full_value == 4294967295u32);
                        assert((pre_fix[w as int] & (1u32 << ((t) as u32))) != 0u32);
                    } else {
                        assert((0u32 & (1u32 << ((t) as u32))) == 0u32) by (bit_vector)
                            requires
                                (t as u32) <= 31u32,
                        ;
                        assert(full_value == 0u32);
                        assert((pre_fix[w as int] & (1u32 << ((t) as u32))) == 0u32);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// the borrow-family cursor models (see the disclosure banner above)
// ---------------------------------------------------------------------------

/// Origin Rust (lib.rs:666-672 fn blocks): the iterator well-formedness --
/// the cursor stays within the storage blocks.
/// Blocks well-formedness: the [pos, end) cursor stays within the
/// borrowed storage (end starts at the whole-block sequence length and
/// steps down from the back under next_back; the borrow never changes
/// under the iterator).
pub open spec fn blocks_inv(b: &BlocksExec) -> bool {
    b.pos <= b.end && (b.end as int) <= b.storage@.len()
}

/// Origin Rust (lib.rs:2353-2357):
///   pub struct Blocks<'a, B: 'a> { iter: slice::Iter<'a, B> }
/// transcribed as BlocksExec (the slice::Iter cursor as the [pos, end)
/// pair over the borrowed storage; slab IterExec precedent).
pub struct BlocksExec<'a> {
    pub storage: &'a Vec<u32>,
    pub pos: usize,
    pub end: usize,
}

/// Origin Rust (lib.rs:2191-2194):
///   pub struct Iter<'a, B: 'a = u32> { bit_vec: &'a BitVec<B>, range: Range<usize> }
/// transcribed as IterExec (the Range cursor as the [pos, end) pair; the
/// slab IterExec precedent -- no vstd spec for Range).
pub struct IterExec<'a> {
    pub bit_vec: &'a BitVec,
    pub pos: usize,
    pub end: usize,
}

/// Iter well-formedness: the borrowed vector stays invariant and the
/// cursor stays within [0, end == nbits].
pub open spec fn iter_inv<'a>(it: &IterExec<'a>) -> bool {
    inv(it.bit_vec)
        && it.pos <= it.end
        && (it.end as int) <= it.bit_vec.nbits as int
}

impl<'a> IterExec<'a> {

    /// Origin Rust (lib.rs:2254-2259):
    ///   fn next(&mut self) -> Option<bool> {
    ///       self.range.next().map(|i| self.bit_vec.get(i).unwrap()) }
    /// transcription: the Range::next advance as the pos step; the
    /// get().unwrap() panic tier never fires (pos < end == nbits is the
    /// invariant), which is the machine-checked obligation.
    pub exec fn next(&mut self) -> (r: Option<bool>)
        requires
            iter_inv(&*old(self)),
        ensures
            iter_inv(&*final(self)),
            final(self).end == old(self).end,
            final(self).bit_vec == old(self).bit_vec,
            r.is_Some() <==> (old(self).pos as int) < (old(self).end as int),
            r matches Some(b) ==> (
                old(self).pos < old(self).end
                && final(self).pos == old(self).pos + 1
                && b == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, old(self).pos)
            ),
            r matches None ==> (
                final(self).pos == old(self).end
                && old(self).pos == old(self).end
            ),
    {
        if self.pos < self.end {
            let g = self.bit_vec.get(self.pos);
            let b = match g {
                Some(b) => b,
                None => panic!("called `Option::unwrap()` on a `None` value"),
            };
            self.pos = self.pos + 1;
            Some(b)
        } else {
            None
        }
    }

    /// Origin Rust (lib.rs:2261-2266):
    ///   fn nth(&mut self, n: usize) -> Option<Self::Item> {
    ///       self.range.nth(n).and_then(|i| self.bit_vec.get(i)) }
    /// transcription: the Range::nth skip tier -- an exact advance by n
    /// positions when the remaining tail is longer than n, a full
    /// exhaustion otherwise (Range::nth consumes up to and including the
    /// upper bound). The and_then propagates the get Option directly
    /// (no panic tier here, unlike next).
    pub exec fn nth(&mut self, n: usize) -> (r: Option<bool>)
        requires
            iter_inv(&*old(self)),
        ensures
            iter_inv(&*final(self)),
            final(self).end == old(self).end,
            final(self).bit_vec == old(self).bit_vec,
            final(self).pos >= old(self).pos,
            final(self).pos <= old(self).end,
            r.is_Some() <==> ((old(self).pos as int) + (n as int)
                < (old(self).end as int)),
            r matches Some(b) ==> (
                old(self).pos + n < old(self).end
                && final(self).pos == old(self).pos + n + 1
                && b == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits,
                    (old(self).pos + n) as usize)
            ),
            r matches None ==> final(self).pos == old(self).end,
    {
        let rem = self.end - self.pos;
        if n < rem {
            self.pos = self.pos + n;
            let g = self.bit_vec.get(self.pos);
            self.pos = self.pos + 1;
            g
        } else {
            self.pos = self.end;
            None
        }
    }

    /// Origin Rust (lib.rs:2287-2292 DoubleEndedIterator for Iter):
    ///   fn next_back(&mut self) -> Option<bool> {
    ///       self.range.next_back().map(|i| self.bit_vec.get(i).unwrap()) }
    pub exec fn next_back(&mut self) -> (r: Option<bool>)
        requires
            iter_inv(&*old(self)),
        ensures
            iter_inv(&*final(self)),
            final(self).pos == old(self).pos,
            final(self).bit_vec == old(self).bit_vec,
            r.is_Some() <==> (old(self).pos as int) < (old(self).end as int),
            r matches Some(b) ==> (
                old(self).pos < old(self).end
                && final(self).end == old(self).end - 1
                && old(self).pos <= final(self).end
                && b == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits,
                    (old(self).end - 1) as usize)
            ),
            r matches None ==> (
                final(self).end == old(self).end
                && old(self).pos == old(self).end
            ),
    {
        if self.pos < self.end {
            self.end = self.end - 1;
            let g = self.bit_vec.get(self.end);
            match g {
                Some(b) => Some(b),
                None => panic!("called `Option::unwrap()` on a `None` value"),
            }
        } else {
            None
        }
    }

    /// Origin Rust (lib.rs:2268-2270):
    ///   fn size_hint(&self) -> (usize, Option<usize>) { self.range.size_hint() }
    /// (ExactSizeIterator tier: the remaining count on both ends.)
    pub exec fn size_hint(&self) -> (ret: (usize, Option<usize>))
        requires
            iter_inv(&*self),
        ensures
            ret.0 == self.end - self.pos,
            ret.1 matches Some(h) ==> h == self.end - self.pos,
    {
        (self.end - self.pos, Some(self.end - self.pos))
    }
}

/// Origin Rust (lib.rs:2306-2314 impl<'a, B: BitBlock> IntoIterator for &'a BitVec<B>):
///   fn into_iter(self) -> Iter<'a, B> { self.iter() }
/// transcription: the adapter call tier (the shared-borrow into_iter).
pub exec fn bitvec_ref_into_iter(bv: &BitVec) -> (r: IterExec)
    requires
        inv(bv),
    ensures
        iter_inv(&r),
        r.bit_vec == bv,
        r.pos == 0,
        r.end == bv.nbits,
{
    bv.iter()
}

/// Origin Rust (lib.rs:2316-2319):
///   pub struct IntoIter<B = u32> { bit_vec: BitVec<B>, range: Range<usize> }
/// transcribed as IntoIterExec (the owned BitVec handover + the [pos, end)
/// cursor; the slab IntoIterExec precedent).
pub struct IntoIterExec {
    pub bit_vec: BitVec,
    pub pos: usize,
    pub end: usize,
}

/// IntoIter well-formedness (the owned vector stays invariant; the cursor
/// stays within [0, end == nbits]).
pub open spec fn into_iter_inv(it: &IntoIterExec) -> bool {
    inv(&it.bit_vec)
        && it.pos <= it.end
        && (it.end as int) <= it.bit_vec.nbits as int
}

/// Origin Rust (lib.rs:2339-2351 impl<B: BitBlock> IntoIterator for BitVec<B>):
///   fn into_iter(self) -> IntoIter<B> {
///       let nbits = self.nbits;
///       IntoIter { bit_vec: self, range: 0..nbits } }
/// transcription: the owned handover (the BitVec value moves into the
/// cursor; the entries view and nbits are preserved).
pub exec fn bitvec_into_iter(bv: BitVec) -> (r: IntoIterExec)
    requires
        inv(&bv),
    ensures
        into_iter_inv(&r),
        r.pos == 0,
        r.end == bv.nbits,
        r.bit_vec.nbits == bv.nbits,
        r.bit_vec.storage@ == bv.storage@,
{
    let nbits = bv.nbits;
    IntoIterExec { bit_vec: bv, pos: 0, end: nbits }
}

impl IntoIterExec {

    /// Origin Rust (lib.rs:2321-2328):
    ///   fn next(&mut self) -> Option<bool> {
    ///       self.range.next().map(|i| self.bit_vec.get(i).unwrap()) }
    /// transcription: as Iter::next, over the owned vector (the value is
    /// only read, the cursor advances).
    pub exec fn next(&mut self) -> (r: Option<bool>)
        requires
            into_iter_inv(&*old(self)),
        ensures
            into_iter_inv(&*final(self)),
            final(self).end == old(self).end,
            final(self).pos == old(self).pos || final(self).pos == old(self).pos + 1,
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            final(self).bit_vec.storage@ == old(self).bit_vec.storage@,
            r.is_Some() <==> (old(self).pos as int) < (old(self).end as int),
            r matches Some(b) ==> (
                old(self).pos < old(self).end
                && final(self).pos == old(self).pos + 1
                && b == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits, old(self).pos)
            ),
            r matches None ==> (
                final(self).pos == old(self).end
                && old(self).pos == old(self).end
            ),
    {
        if self.pos < self.end {
            let g = self.bit_vec.get(self.pos);
            let b = match g {
                Some(b) => b,
                None => panic!("called `Option::unwrap()` on a `None` value"),
            };
            self.pos = self.pos + 1;
            Some(b)
        } else {
            None
        }
    }

    /// Origin Rust (lib.rs:2330-2335 DoubleEndedIterator for IntoIter):
    ///   fn next_back(&mut self) -> Option<bool> {
    ///       self.range.next_back().map(|i| self.bit_vec.get(i).unwrap()) }
    pub exec fn next_back(&mut self) -> (r: Option<bool>)
        requires
            into_iter_inv(&*old(self)),
        ensures
            into_iter_inv(&*final(self)),
            final(self).pos == old(self).pos,
            final(self).bit_vec.nbits == old(self).bit_vec.nbits,
            final(self).bit_vec.storage@ == old(self).bit_vec.storage@,
            r.is_Some() <==> (old(self).pos as int) < (old(self).end as int),
            r matches Some(b) ==> (
                old(self).pos < old(self).end
                && final(self).end == old(self).end - 1
                && old(self).pos <= final(self).end
                && b == bit_at(old(self).bit_vec.storage@, old(self).bit_vec.nbits,
                    (old(self).end - 1) as usize)
            ),
            r matches None ==> (
                final(self).end == old(self).end
                && old(self).pos == old(self).end
            ),
    {
        if self.pos < self.end {
            self.end = self.end - 1;
            let g = self.bit_vec.get(self.end);
            match g {
                Some(b) => Some(b),
                None => panic!("called `Option::unwrap()` on a `None` value"),
            }
        } else {
            None
        }
    }

    /// Origin Rust (lib.rs:2337-2337 ExactSizeIterator for IntoIter):
    /// (the trait-default size_hint = (len, Some(len)) tier)
    pub exec fn size_hint(&self) -> (ret: (usize, Option<usize>))
        requires
            into_iter_inv(&*self),
        ensures
            ret.0 == self.end - self.pos,
            ret.1 matches Some(h) ==> h == self.end - self.pos,
    {
        (self.end - self.pos, Some(self.end - self.pos))
    }
}

impl<'a> BlocksExec<'a> {

    /// Origin Rust (lib.rs:2362-2366):
    ///   fn next(&mut self) -> Option<B> { self.iter.next().cloned() }
    /// transcription: the forward slice cursor over the borrowed storage
    /// (u32 is a value copy; the clone tier is a move).
    pub exec fn next(&mut self) -> (r: Option<u32>)
        requires
            blocks_inv(&*old(self)),
        ensures
            blocks_inv(&*final(self)),
            final(self).end == old(self).end,
            final(self).storage == old(self).storage,
            r.is_Some() <==> (old(self).pos as int) < (old(self).end as int),
            r matches Some(w) ==> (
                old(self).pos < old(self).end
                && final(self).pos == old(self).pos + 1
                && w == old(self).storage@[old(self).pos as int]
            ),
            r matches None ==> (
                final(self).pos == old(self).end
                && old(self).pos == old(self).end
            ),
    {
        if self.pos < self.end {
            let w = self.storage[self.pos];
            self.pos = self.pos + 1;
            Some(w)
        } else {
            None
        }
    }

    /// Origin Rust (lib.rs:2367-2370):
    ///   fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
    /// (ExactSizeIterator tier: the remaining block count on both ends.)
    pub exec fn size_hint(&self) -> (ret: (usize, Option<usize>))
        requires
            blocks_inv(&*self),
        ensures
            ret.0 == self.end - self.pos,
            ret.1 matches Some(h) ==> h == self.end - self.pos,
    {
        (self.end - self.pos, Some(self.end - self.pos))
    }

    /// Origin Rust (lib.rs:2373-2378 DoubleEndedIterator for Blocks):
    ///   fn next_back(&mut self) -> Option<B> { self.iter.next_back().cloned() }
    /// transcription: the backward slice cursor: the end edge steps down
    /// and the item is the (new) last unreturned block.
    pub exec fn next_back(&mut self) -> (r: Option<u32>)
        requires
            blocks_inv(&*old(self)),
        ensures
            blocks_inv(&*final(self)),
            final(self).pos == old(self).pos,
            final(self).storage == old(self).storage,
            r.is_Some() <==> (old(self).pos as int) < (old(self).end as int),
            r matches Some(w) ==> (
                old(self).pos < old(self).end
                && final(self).end == old(self).end - 1
                && old(self).pos <= final(self).end
                && w == old(self).storage@[(old(self).end - 1) as int]
            ),
            r matches None ==> (
                final(self).end == old(self).end
                && old(self).pos == old(self).end
            ),
    {
        if self.pos < self.end {
            self.end = self.end - 1;
            let w = self.storage[self.end];
            Some(w)
        } else {
            None
        }
    }
}
// ===========================================================================
// Appended movers: append / split_off (the variable-shift family, reusing
// the batch-B frame discipline -- ghost snapshots, per-position Vec::set
// updates, and the subrange bridges).
// ===========================================================================

impl BitVec {

    /// Origin Rust: pub fn append(&mut self, other: &mut Self) (lib.rs:1394-1423)
    ///     { self.ensure_invariant();
    ///       debug_assert!(other.is_last_block_fixed());
    ///       let b = self.len() % B::bits();
    ///       let o = other.len() % B::bits();
    ///       let will_overflow = (b + o > B::bits()) || (o == 0 && b != 0);
    ///       self.nbits += other.len();
    ///       other.nbits = 0;
    ///       if b == 0 { self.storage.append(&mut other.storage); }
    ///       else {
    ///         self.storage.reserve(other.storage.len());
    ///         for block in other.storage.drain(..) {
    ///           { let last = self.storage.last_mut().unwrap();
    ///             *last |= block << b; }
    ///           self.storage.push(block >> (B::bits() - b)); }
    ///         if !will_overflow { self.storage.pop(); } } }
    ///     transcription: drain(..) as the by-index read loop plus the
    ///     final clear (drain(..) empties the source in order);
    ///     last_mut().unwrap() as the len-1 index/set pair (b != 0 means
    ///     nbits > 0, so the storage is nonempty and the unwrap never
    ///     fires -- the machine-checked obligation); the trailing pop
    ///     drops the last pushed block, which in the !will_overflow
    ///     world provably carries no payload bits. The mid-loop states
    ///     clobber the tail invariant (upstream never repairs it before
    ///     the end); the final state restores it by the block arithmetic.
    /// Upstream doc (lib.rs:1377-1392):
    ///   Moves all bits from `other` into `Self`, leaving `other` empty.
    pub exec fn append(&mut self, other: &mut Self)
        requires
            inv(old(self)),
            inv(old(other)),
            (old(self).nbits as int + old(other).nbits as int) <= usize::MAX as int,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits + old(other).nbits,
            inv(final(other)),
            final(other).nbits == 0,
            final(other).storage@ == Seq::<u32>::empty(),
            forall|j: usize|
                j < old(self).nbits ==>
                #[trigger] bit_at(final(self).storage@, final(self).nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            forall|j: usize|
                j < old(other).nbits ==>
                #[trigger] bit_at(final(self).storage@, final(self).nbits,
                    (old(self).nbits + j) as usize)
                    == bit_at(old(other).storage@, old(other).nbits, j),
    {
        let b = self.nbits % 32;
        let o = other.nbits % 32;
        let will_overflow = b + o > 32 || (o == 0 && b != 0);
        let nO = self.nbits;
        let nOt = other.nbits;
        let ghost sS: Seq<u32> = self.storage@;
        let ghost sOt: Seq<u32> = other.storage@;
        proof {
            assert(sS == old(self).storage@);
            assert(sOt == old(other).storage@);
            assert(blocks_for_bits(nO) == sS.len() as usize);
            assert(blocks_for_bits(nOt) == sOt.len() as usize);
        }
        self.nbits = self.nbits + other.nbits;
        other.nbits = 0;
        if b == 0 {
            self.storage.append(&mut other.storage);
            proof {
                let sF = self.storage@;
                let nF = self.nbits;
                assert(sF == sS + sOt); // the Vec::append entries tier
                assert(other.storage@ == Seq::<u32>::empty());
                assert(len_inv(final(other))) by {
                    assert(final(other).nbits == 0);
                    assert(blocks_for_bits(0) == 0);
                }
                assert(trailing_zero(final(other)));
                // storage length: concat == blocks_for_bits(nF)
                assert((sF.len() as int) == (sS.len() as int) + (sOt.len() as int));
                assert(len_inv(final(self))) by {
                    assert((nO as int) % 32 == 0) by { assert(b == 0); }
                    let qo = nO as int / 32;
                    assert((nO as int) == 32 * qo);
                    if (nOt as int) % 32 == 0 {
                        let q = (nOt as int) / 32;
                        assert((nOt as int) == 32 * q);
                        assert((nF as int) == 32 * (qo + q));
                        assert(blocks_for_bits(nF) as int == qo + q);
                        assert((sS.len() as int) == blocks_for_bits(nO) as int == qo);
                        assert((sOt.len() as int) == q);
                    } else {
                        let q = (nOt as int) / 32;
                        assert((nOt as int) == 32 * q + ((nOt as int) % 32));
                        assert((nF as int) == 32 * (qo + q) + ((nOt as int) % 32));
                        assert(blocks_for_bits(nF) as int == qo + q + 1);
                        assert((sS.len() as int) == blocks_for_bits(nO) as int) by {
                            assert((nO as int) % 32 == 0);
                        }
                        assert((sS.len() as int) == qo) by {
                            assert(blocks_for_bits(nO) as int == qo) by {
                                assert((nO as int) % 32 == 0);
                            }
                        }
                        assert((sOt.len() as int) == q + 1) by {
                            assert(blocks_for_bits(nOt) as int == q + 1) by {
                                assert((nOt as int) % 32 > 0);
                            }
                        }
                        assert((sS.len() as int) + (sOt.len() as int)
                            == qo + q + 1);
                    }
                    assert((sF.len() as int) == blocks_for_bits(nF) as int);
                }
                assert(trailing_zero(final(self))) by {
                    // the concat inherits the tail-block discipline of
                    // whichever side owns the final tail
                    if (sOt.len() as int) > 0 {
                        assert((nF as int) % 32 == (nOt as int) % 32);
                        if (nOt as int % 32 > 0) {
                            assert(sF[(sF.len() - 1) as int]
                                == sOt[(sOt.len() - 1) as int]);
                            assert(trailing_zero(old(other)));
                            assert(sOt[(sOt.len() - 1) as int]
                                < (1u32 << (nOt as int % 32)));
                            assert(1u32 << (nOt as int % 32)
                                == 1u32 << ((nOt as int % 32) as u32));
                            assert(1u32 << (nF as int % 32)
                                == 1u32 << ((nF as int % 32) as u32));
                            assert((nF as int % 32) == (nOt as int % 32));
                        } else {
                            assert((nF as int) % 32 == 0);
                        }
                    } else {
                        if (nO as int % 32 == 0) {
                            assert((nF as int) % 32 == 0);
                        } else {
                            assert(sF[(sF.len() - 1) as int]
                                == sS[(sS.len() - 1) as int]);
                            assert(trailing_zero(old(self)));
                            assert((nF as int) % 32 == (nO as int) % 32);
                        }
                    }
                }
                // kept tier: j < nO reads the concat's low half
                assert forall|j: usize| j < nO implies
                    bit_at(sF, nF, j) == bit_at(sS, nO, j) by {
                    int_div_bound_lemma(j, nO);
                    let w = j / 32;
                    let t = j % 32;
                    assert(t < 32);
                    assert((w as int) < sS.len()) by {
                        assert((j as int) / 32 < (sS.len() as int)) by {
                            assert((nO as int) <= 32 * (sS.len() as int));
                            assert((j as int) < (nO as int));
                        }
                        assert((w as int) == (j as int) / 32);
                    }
                    assert(sF[w as int] == sS[w as int]); // concat-low axiom tier
                    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                }
                // moved tier: j < nOt lands past the SELF tail
                assert forall|j: usize| j < nOt implies
                    bit_at(sF, nF, (nO + j) as usize) == bit_at(sOt, nOt, j) by {
                    int_div_bound_lemma(j, nOt);
                    let i = (nO + j) as usize;
                    let w = i / 32;
                    let t = i % 32;
                    // nO is a block multiple: the global block is the
                    // other's block offset by sS.len(), bit unchanged
                    assert((i as int) == (nO as int) + (j as int));
                    assert((nO as int) % 32 == 0) by { assert(b == 0); }
                    let wj = j / 32;
                    let tj = j % 32;
                    assert((w as int) == (sS.len() as int) + (wj as int)) by {
                        assert((i as int) == 32 * (sS.len() as int) + (j as int));
                        assert((j as int) == 32 * (wj as int) + (tj as int));
                        assert((i as int) == 32 * ((sS.len() as int) + (wj as int))
                            + (tj as int));
                        assert((tj as int) < 32);
                    }
                    assert((t as int) == (tj as int)) by {
                        assert((i as int) == 32 * ((w as int)) + (t as int));
                        assert((i as int) == 32 * ((w as int)) + (tj as int));
                    }
                    assert(sF[w as int] == sOt[wj as int]); // concat-high axiom tier
                    assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
                    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                }
            }
        } else {
            // the moving cascade (b in [1, 31])
            self.storage.reserve(other.storage.len());
            let L: usize = self.storage.len();
            let M: usize = other.storage.len();
            proof {
                assert(L == blocks_for_bits(nO) as usize);
                assert(M == blocks_for_bits(nOt) as usize);
                assert(L >= 1);
                assert(b >= 1);
            }
            let mut k: usize = 0;
            while k < M
                invariant
                    k <= M,
                    self.nbits == nO + nOt,
                    other.nbits == 0,
                    other.storage@ == sOt,
                    other.storage@.len() == M as int,
                    self.storage@.len() == L + k,
                    b >= 1,
                    b <= 31,
                    (L as int) == blocks_for_bits(nO) as int,
                    (M as int) == blocks_for_bits(nOt) as int,
                    (nO as int) == 32 * ((L as int) - 1) + (b as int),
                    forall|w2: int| 0 <= w2 < (L as int) - 1 ==>
                        #[trigger] self.storage@[w2] == sS[w2],
                    self.storage@[(L as int) - 1] == (if k == 0 {
                        sS[(L as int) - 1]
                    } else {
                        sS[(L as int) - 1] | (sOt[0] << (b as u32))
                    }),
                    forall|w2: int| (L as int) <= w2 < (L as int + k) - 1 ==>
                        #[trigger] self.storage@[w2] == ((sOt[w2 - (L as int)]
                            >> ((32 - b) as u32))
                            | (sOt[w2 - (L as int) + 1] << (b as u32))),
                    k >= 1 ==> self.storage@[(L as int + k) - 1]
                        == (sOt[(k as int) - 1] >> ((32 - b) as u32)),
                decreases M - k,
            {
                let blk = other.storage[k];
                proof {
                    assert(blk == sOt[k as int]);
                }
                let last_i: usize = self.storage.len() - 1;
                proof {
                    assert((last_i as int) == (L as int + k) - 1);
                }
                let lv = self.storage[last_i];
                let nv = lv | (blk << b);
                proof {
                    // the new value joins the cascade frame
                    assert((nv as u32) == lv | (blk << (b as u32))) by { }
                    assert(lv == self.storage@[last_i as int]);
                }
                let ghost s_h = self.storage@;
                self.storage.set(last_i, nv);
                proof {
                    assert(self.storage@ == s_h.update(last_i as int, nv));
                    // position-value bookkeeping of this step
                    if k == 0 {
                        assert(last_i as int == (L as int) - 1);
                        assert(lv == sS[(L as int) - 1]);
                        assert(s_h[last_i as int] == sS[(L as int) - 1]);
                        assert(nv == sS[(L as int) - 1] | (sOt[0] << (b as u32)));
                    } else {
                        assert(last_i as int == (L as int + k) - 1);
                        assert(lv == sOt[(k as int) - 1] >> ((32 - b) as u32));
                        assert(nv == (sOt[(k as int) - 1] >> ((32 - b) as u32))
                            | (sOt[k as int] << (b as u32)));
                    }
                    // the untouched positions keep their step values
                    assert forall|w2: int| 0 <= w2 < L - 1 implies
                        self.storage@[w2] == s_h[w2] by { }
                    if k >= 1 {
                        assert forall|w2: int| (L as int) <= w2 < (L as int + k) - 1 implies
                            self.storage@[w2] == s_h[w2] by { }
                        assert(self.storage@[(L as int) - 1]
                            == sS[(L as int) - 1] | (sOt[0] << (b as u32))) by { }
                    }
                }
                let hi = blk >> (32 - b);
                let ghost s_t = self.storage@;
                self.storage.push(hi);
                proof {
                    assert(self.storage@ == s_t.push(hi));
                    assert(hi == sOt[k as int] >> ((32 - b) as u32));
                    // the new top block is the pushed remainder
                    assert(self.storage@.len() == L as int + k + 1);
                    assert(self.storage@[(L as int + k + 1) - 1]
                        == sOt[k as int] >> ((32 - b) as u32));
                    // lower positions survive the push
                    assert forall|w2: int| 0 <= w2 < L - 1 implies
                        self.storage@[w2] == s_h[w2] by { }
                    if k >= 1 {
                        assert(self.storage@[(L as int) - 1]
                            == sS[(L as int) - 1] | (sOt[0] << (b as u32)));
                    } else {
                        assert(self.storage@[(L as int) - 1]
                            == sS[(L as int) - 1] | (sOt[0] << (b as u32))) by { }
                    }
                }
                k = k + 1;
            }
            // drain(..) ends with the source emptied
            other.storage.clear();
            proof {
                assert(other.storage@ == Seq::<u32>::empty());
                assert(len_inv(final(other))) by {
                    assert(final(other).nbits == 0);
                    assert(blocks_for_bits(0) == 0);
                }
                assert(trailing_zero(final(other)));
            }
            let ghost s_cascade = self.storage@;
            if !will_overflow {
                let p = self.storage.pop();
                proof {
                    // the subrange bridge (the batch-B pop idiom)
                    assert(self.storage@.len() == (L + M - 1) as int) by { }
                    assert(self.storage@
                        == s_cascade.subrange(0, ((L + M - 1) as int))) by { }
                    assert forall|w2: int| 0 <= w2 < (L as int + M as int) - 1 implies
                        #[trigger] self.storage@[w2] == s_cascade[w2] by {
                        assert(s_cascade.subrange(0, ((L + M - 1) as int))[w2]
                            == s_cascade[w2]);
                    }
                }
            }
            // assemble the exact final frame for the kit
            proof {
                let sF = self.storage@;
                assert(if !will_overflow {
                    (sF.len() as int) == (L as int + M as int) - 1
                } else {
                    (sF.len() as int) == (L as int + M as int)
                });
                assert(sS.len() == L as int);
                assert(sOt.len() == M as int);
                assert forall|w2: int| 0 <= w2 < (L as int) - 1 implies
                    #[trigger] sF[w2] == sS[w2] by { }
                if M >= 1 {
                    assert(sF[(L as int) - 1]
                        == (sS[(L as int) - 1] | (sOt[0] << (b as u32))));
                    assert forall|w2: int| (L as int) <= w2
                        && w2 <= (L as int + M as int) - 2 implies
                        #[trigger] sF[w2] == ((sOt[w2 - (L as int)] >> ((32 - b) as u32))
                            | (sOt[w2 - (L as int) + 1] << (b as u32))) by { }
                    if will_overflow {
                        assert(sF.len() == (L + M) as int) by { }
                        assert(sF[(L + M - 1) as int]
                            == (sOt[(M as int) - 1] >> ((32 - b) as u32))) by { }
                        assert(sF[(sF.len() - 1) as int]
                            == (sOt[(M as int) - 1] >> ((32 - b) as u32))) by { }
                    }
                } else {
                    assert(sF[(L as int) - 1] == sS[(L as int) - 1]);
                }
                // the sources' tail disciplines feed the kit
                assert(trailing_zero(old(self)));
                assert(trailing_zero(old(other)));
                assert(sS[(L as int) - 1] < (1u32 << (b as u32))) by {
                    assert(nO as int % 32 == b as int);
                    assert(blocks_for_bits(nO) == L);
                    assert(1u32 << (nO as int % 32) == 1u32 << ((nO as int % 32) as u32));
                }
                if o > 0 {
                    assert(sOt[(M as int) - 1] < (1u32 << (o as u32))) by {
                        assert(blocks_for_bits(nOt) == M);
                        assert(1u32 << (nOt as int % 32)
                            == 1u32 << ((nOt as int % 32) as u32));
                        assert((nOt as int % 32) == (o as int));
                    }
                }
                append_shift_semantics(sF, sS, sOt, nO, nOt, b, o, !will_overflow);
                // the kit's tiers land on the exec ensures
                assert(len_inv(final(self))) by {
                    assert(self.storage@.len() == blocks_for_bits(final(self).nbits) as int);
                }
                assert(trailing_zero(final(self))) by {
                    if (nO + nOt) % 32 == 0 {
                    } else {
                        let eF = (nO + nOt) % 32;
                        assert(1u32 << (eF) == 1u32 << ((eF) as u32));
                    }
                }
            }
        }
    }

    /// Origin Rust: pub fn split_off(&mut self, at: usize) -> Self (lib.rs:1449-1487)
    ///     { self.ensure_invariant();
    ///       assert!(at <= self.len(), "`at` out of bounds");
    ///       let mut other = BitVec::<B>::default();
    ///       if at == 0 { mem::swap(self, &mut other); return other; }
    ///       else if at == self.len() { return other; }
    ///       let w = at / B::bits(); let b = at % B::bits();
    ///       other.nbits = self.nbits - at;
    ///       self.nbits = at;
    ///       if b == 0 { other.storage = self.storage.split_off(w); }
    ///       else {
    ///         other.storage.reserve(self.storage.len() - w);
    ///         { let mut iter = self.storage[w..].iter();
    ///           let mut last = *iter.next().unwrap();
    ///           for &cur in iter {
    ///             other.storage.push((last >> b) | (cur << (B::bits() - b)));
    ///             last = cur; }
    ///           other.storage.push(last >> b); }
    ///         self.storage.truncate(w + 1);
    ///         self.fix_last_block(); }
    ///       other }
    ///     # Panics ("`at` out of bounds") -> requires; mem::swap
    ///     transcribed as the two-field swap pair (the struct is exactly
    ///     the storage + nbits pair). Faithful downstream shape note:
    ///     the b != 0 branch always pushes L - w blocks, but
    ///     blocks_for_bits(nbits) == L - w only for o == b's outside; when
    ///     the split-point tail coincides with or passes beyond the old
    ///     tail count (0 < e <= b, in old-tail terms) the returned vector
    ///     carries one surplus trailing zero block (the upstream
    ///     len-invariant is NOT restored; runtime-confirmed against the
    ///     pinned tree, out/poc/splitoff-slack-block) -- the faithful
    ///     ensures carry the slack explicitly instead of asserting the
    ///     violated invariant.
    /// Upstream doc (lib.rs:1425-1430):
    ///   Splits the `BitVec` into two at the given bit,
    ///   retaining the first half in-place and returning the second one.
    ///   # Panics
    ///   Panics if `at` out of bounds.
    pub exec fn split_off(&mut self, at: usize) -> (other: BitVec)
        requires
            inv(old(self)),
            at <= old(self).nbits,
        ensures
            inv(final(self)),
            trailing_zero(&other),
            final(self).nbits == at,
            other.nbits == old(self).nbits - at,
            (blocks_for_bits(other.nbits) as int) <= other.storage@.len(),
            other.storage@.len() <= (blocks_for_bits(other.nbits) as int) + 1,
            other.storage@.len() == (blocks_for_bits(other.nbits) as int) + 1 ==>
                other.storage@[(other.storage@.len() - 1) as int] == 0u32,
            forall|j: usize|
                j < at ==>
                #[trigger] bit_at(final(self).storage@, at, j)
                    == bit_at(old(self).storage@, old(self).nbits, j),
            forall|j: usize|
                j < old(self).nbits - at ==>
                #[trigger] bit_at(other.storage@, other.nbits, j)
                    == bit_at(old(self).storage@, old(self).nbits, (at + j) as usize),
    {
        let nO = self.nbits;
        let ghost sO: Seq<u32> = self.storage@;
        proof {
            assert(sO == old(self).storage@);
            assert(blocks_for_bits(nO) == sO.len() as usize);
        }
        /* Origin Rust: let mut other = BitVec::<B>::default(); */
        let mut other = BitVec { storage: Vec::new(), nbits: 0 };
        if at == 0 {
            /* Origin Rust: mem::swap(self, &mut other); return other; */
            core::mem::swap(&mut self.storage, &mut other.storage);
            core::mem::swap(&mut self.nbits, &mut other.nbits);
            proof {
                // other receives the whole old vector; self is the empty one
                assert(other.storage@ == sO);
                assert(other.nbits == nO);
                assert(self.storage@ == Seq::<u32>::empty());
                assert(self.nbits == 0);
                assert(inv(self)) by {
                    assert(blocks_for_bits(0) == 0);
                }
                assert(trailing_zero(&other)) by {
                    if nO as int % 32 == 0 {
                    } else {
                        assert(trailing_zero(old(self)));
                        assert(other.storage@[(blocks_for_bits(nO) - 1) as int]
                            < (1u32 << (nO as int % 32)));
                        assert(1u32 << (nO as int % 32)
                            == 1u32 << ((nO as int % 32) as u32));
                    }
                }
                assert((blocks_for_bits(other.nbits) as int)
                    == other.storage@.len());
            }
            return other;
        }
        if at == self.nbits {
            // the tail is empty: other stays the default
            proof {
                assert(other.storage@ == Seq::<u32>::empty());
                assert(other.nbits == 0);
                assert((blocks_for_bits(other.nbits) as int)
                    <= other.storage@.len());
                assert(self.storage@.len() == blocks_for_bits(nO) as int);
            }
            return other;
        }
        let w = at / 32;
        let b = at % 32;
        let L: usize = self.storage.len();
        proof {
            assert(L == blocks_for_bits(nO) as usize);
            assert(w + 1 <= L);
        }
        other.nbits = self.nbits - at;
        self.nbits = at;
        if b == 0 {
            let t = self.storage.split_off(w);
            proof {
                // Vec::split_off: the prefix stays, the suffix moves
                assert(t@ == sO.subrange(w as int, sO.len() as int));
                assert(self.storage@ == sO.subrange(0, w as int));
            }
            other.storage = t;
            proof {
                let sF = self.storage@;
                let sT = other.storage@;
                let nOt = other.nbits;
                // structural tiers
                assert((sF.len() as int) == w as int);
                assert((sT.len() as int) == (L as int) - (w as int));
                assert(len_inv(final(self))) by {
                    assert(blocks_for_bits(at) as int == w as int) by {
                        assert((at as int) % 32 == 0) by { assert(b == 0); }
                        assert((at as int) == 32 * (w as int));
                    }
                }
                assert(trailing_zero(final(self))) by {
                    assert((final(self).nbits as int) % 32 == 0);
                }
                assert(sT.len() as int == blocks_for_bits(nOt) as int) by {
                    let q = (nO as int) / 32;
                    if (nO as int) % 32 == 0 {
                        assert((nO as int) == 32 * q);
                        assert((nOt as int) == 32 * (q - w as int));
                        assert(blocks_for_bits(nOt) as int == q - w as int);
                        assert((L as int) == q);
                    } else {
                        let e = (nO as int) % 32;
                        assert((nO as int) == 32 * q + e);
                        assert((L as int) == q + 1);
                        assert((nOt as int) == 32 * (q - w as int) + e);
                        assert(blocks_for_bits(nOt) as int == q + 1 - w as int);
                    }
                    assert((sT.len() as int) == (L as int) - (w as int));
                }
                assert(trailing_zero(&other)) by {
                    if nOt as int % 32 == 0 {
                    } else {
                        assert(sT[(sT.len() - 1) as int]
                            == sO[(L as int) - 1]);
                        assert(trailing_zero(old(self)));
                        assert(sO[(L as int) - 1] < (1u32 << (nO as int % 32)));
                        assert((nOt as int % 32) == (nO as int % 32));
                        assert(1u32 << (nO as int % 32)
                            == 1u32 << ((nO as int % 32) as u32));
                        assert(1u32 << (nOt as int % 32)
                            == 1u32 << ((nOt as int % 32) as u32));
                    }
                }
                // kept tier: the prefix survives verbatim
                assert forall|j: usize| j < at implies
                    bit_at(self.storage@, at, j) == bit_at(sO, nO, j) by {
                    int_div_bound_lemma(j, at);
                    let wj = j / 32;
                    assert((wj as int) < w as int) by {
                        assert((j as int) < (at as int));
                        assert(at as int == 32 * (w as int));
                    }
                    assert(sF[wj as int] == sO[wj as int]); // subrange-low axiom tier
                    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                }
                // moved tier: the suffix at its shifted readout
                assert forall|j: usize| j < nOt implies
                    bit_at(sT, nOt, j) == bit_at(sO, nO, (at + j) as usize) by {
                    int_div_bound_lemma(j, nOt);
                    let i = (at + j) as usize;
                    let wj = j / 32;
                    let tj = j % 32;
                    assert((at as int) % 32 == 0) by { assert(b == 0); }
                    assert((i as int) == 32 * (w as int + wj as int) + (tj as int));
                    assert(sT[wj as int] == sO[w as int + wj as int]); // subrange-high tier
                    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                    assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
                    assert((i as int % 32) == (tj as int));
                }
            }
        } else {
            /* Origin Rust: other.storage.reserve(self.storage.len() - w); */
            other.storage.reserve(L - w);
            /* Origin Rust: { let mut iter = self.storage[w..].iter();
               let mut last = *iter.next().unwrap();
               for &cur in iter {
                 other.storage.push((last >> b) | (cur << (B::bits() - b)));
                 last = cur; }
               other.storage.push(last >> b); } */
            let mut last = self.storage[w];
            proof {
                assert(last == sO[w as int]);
            }
            let mut p: usize = 0;
            while w + 1 + p < L
                invariant
                    p <= (L - 1) - (w + 1) + 1,
                    w + 1 + p <= L,
                    self.storage@ == sO,
                    other.nbits == nO - at,
                    self.nbits == at,
                    other.storage@.len() == p as int,
                    1 <= b <= 31,
                    forall|r: int| 0 <= r < p as int ==>
                        #[trigger] other.storage@[r] == ((sO[w as int + r]
                            >> (b as u32))
                            | (sO[w as int + r + 1] << ((32 - b) as u32))),
                    last == sO[w as int + p as int],
                decreases L - (w + 1 + p),
            {
                let cur = self.storage[w + 1 + p];
                proof {
                    assert(cur == sO[(w + 1 + p) as int]);
                }
                let pv = (last >> b) | (cur << (32 - b));
                let ghost s_b = other.storage@;
                other.storage.push(pv);
                proof {
                    assert(other.storage@ == s_b.push(pv));
                    assert(pv == ((sO[w as int + p as int] >> (b as u32))
                        | (sO[(w + 1 + p) as int] << ((32 - b) as u32))));
                    assert(other.storage@[p as int] == pv);
                    assert forall|r: int| 0 <= r < p as int implies
                        other.storage@[r] == s_b[r] by { }
                }
                last = cur;
                p = p + 1;
            }
            // the tail push (last >> b)
            let tail_v = last >> b;
            proof {
                assert(last == sO[(w + p) as int]) by { }
                assert((w + p) as int == (L - 1) as int) by {
                    assert(w + 1 + p <= L);
                    assert(w + 1 + p + 1 > L);
                }
            }
            let ghost s_ot_pre = other.storage@;
            other.storage.push(tail_v);
            proof {
                assert(other.storage@ == s_ot_pre.push(tail_v));
                assert(tail_v == sO[(L - 1) as int] >> (b as u32));
                assert(other.storage@.len() as int == (L - w) as int);
                assert(other.storage@[(L - w - 1) as int] == tail_v);
            }
            /* Origin Rust: self.storage.truncate(w + 1); self.fix_last_block(); */
            self.storage.truncate(w + 1);
            proof {
                assert(self.storage@ == sO.subrange(0, (w + 1) as int)) by { }
                assert(self.storage@.len() == (w + 1) as int);
                assert(blocks_for_bits(at) as int == (w + 1) as int) by {
                    assert((at as int) == 32 * (w as int) + (b as int));
                    assert((b as int) > 0);
                }
                assert(len_inv(self));
            }
            let ghost pre_fix = self.storage@;
            self.fix_last_block();
            proof {
                let sT = other.storage@;
                let nOt = other.nbits;
                // kit frames: the cascade map of the moved half
                assert(sT.len() == (L - w) as int);
                assert(sT.len() as usize == L - w);
                assert(sT[(L - w - 1) as int] == (sO[(L - 1) as int] >> (b as u32)));
                assert forall|r: int| 0 <= r < (L as int) - (w as int) - 1 implies
                    sT[r] == ((sO[w + r] >> (b as u32))
                        | (sO[w + r + 1] << ((32 - b) as u32))) by { }
                // the kept tier (inline): the fix's per-bit frame over the sO prefix
                assert forall|j: usize| j < at implies
                    bit_at(self.storage@, at, j) == bit_at(sO, nO, j) by {
                    int_div_bound_lemma(j, at);
                    let wj = j / 32;
                    assert((wj as int) <= w as int) by {
                        assert((j as int) < (at as int));
                        assert((at as int) == 32 * (w as int) + (b as int));
                        assert((j as int) < 32 * (w as int + 1));
                    }
                    // pre-fix prefix equals sO on [0, w]
                    assert(pre_fix[wj as int] == sO[wj as int]) by {
                        assert(pre_fix == sO.subrange(0, (w + 1) as int));
                        assert(pre_fix[wj as int] == sO.subrange(0, (w + 1) as int)[wj as int]);
                        assert(sO.subrange(0, (w + 1) as int)[wj as int] == sO[wj as int]);
                    }
                    assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
                }
                // the kit: slack accounting, trailing, and the moved tier
                split_off_shift_semantics(sO, sT, at, nO, nOt, b, w, L);

// ---------------------------------------------------------------------------
// split kit (the shifted half): the moving branch of split_off pushes
// L - w blocks -- the pairs (last >> b) | (cur << (32 - b)) plus the
// tail push (last >> b); when the split tail position reaches or
// passes the old tail count (0 < e <= b in the caller's terms) one
// surplus trailing zero block remains (the upstream length invariant is
// NOT restored -- runtime-confirmed, out/poc/splitoff-slack-block; the
// faithful slack clauses are carried explicitly below).
// ---------------------------------------------------------------------------

/// the per-bit postcondition, the slack accounting, and the trailing
/// discipline of split_off's moving branch (b > 0), derived from the
/// cascade block frames.
pub proof fn split_off_shift_semantics(
    sO: Seq<u32>, sT: Seq<u32>,
    at: usize, nO: usize, nOt: usize, b: usize, w: usize, L: usize,
)
    requires
        (b as int) >= 1,
        (b as int) <= 31,
        (at as int) < (nO as int),
        (at as int) == 32 * (w as int) + (b as int),
        (nOt as int) == ((nO as int) - (at as int)),
        (sO.len() as int) == (L as int),
        (blocks_for_bits(nO) as int) == (L as int),
        (sT.len() as int) == ((L as int) - (w as int)),
        // the source tail discipline (the caller's invariant)
        ((nO as int) % 32 == 0)
            || (sO[(sO.len() - 1) as int] < (1u32 << (((nO as int) % 32) as u32))),
        // the moved-half block frames
        forall|r: int| 0 <= r < (L as int) - (w as int) - 1 ==>
            (sT[r] == ((sO[w + r] >> (b as u32))
                | (sO[w + r + 1] << ((32 - b) as u32)))),
        sT[((L as int) - (w as int)) - 1]
            == (sO[(L as int - 1)] >> (b as u32)),
    ensures
        (blocks_for_bits(nOt) as int) <= (sT.len() as int),
        (sT.len() as int) <= (blocks_for_bits(nOt) as int) + 1,
        (sT.len() as int) == (blocks_for_bits(nOt) as int) + 1 ==>
            sT[(sT.len() - 1) as int] == 0u32,
        ((nOt as int) % 32 == 0)
            || (sT[(blocks_for_bits(nOt) - 1) as int]
                < (1u32 << (((nOt as int) % 32) as u32))),
        forall|j: usize| j < nOt ==>
            #[trigger] bit_at(sT, nOt, j) == bit_at(sO, nO, (at + j) as usize),
{
    let e = nO % 32;
    let e = nO % 32;
    // (structure) the tail push leaves exactly L - w blocks; the
    // blocks_for_bits match turns on the old-tail/split-tail
    // comparison (the slack accounting, runtime-confirmed)
    assert(sT.len() == (L - w) as int);
    assert((nOt as int) == ((nO as int) - (at as int)));
    if (e as int) > 0 && (e as int) <= (b as int) {
        // 0 < e <= b: the pushed tail carries no payload bits
        assert(blocks_for_bits(nOt) as int == (L as int - w as int) - 1) by {
            assert((nO as int) == 32 * ((L as int) - 1) + (e as int)) by {
                assert(blocks_for_bits(nO) == L);
                assert((e as int) > 0);
            }
            if (e as int) == (b as int) {
                assert((nOt as int) == 32 * ((L as int) - 1 - w as int)) by {
                    assert((at as int) == 32 * (w as int) + (b as int));
                }
                assert((nOt as int) % 32 == 0);
                assert(blocks_for_bits(nOt) as int == (L as int) - 1 - w as int);
            } else {
                assert((nOt as int) == 32 * ((L as int) - 2 - w as int)
                    + (32 + (e as int) - (b as int))) by {
                    assert((at as int) == 32 * (w as int) + (b as int));
                    assert((e as int) < (b as int));
                }
                assert((nOt as int) % 32 == 32 - ((b as int) - (e as int)));
                assert(((b as int) - (e as int)) > 0);
                assert(((b as int) - (e as int)) < 32);
                assert(blocks_for_bits(nOt) as int
                    == (L as int) - 2 - w as int + 1);
            }
        }
        assert(sT.len() as int == blocks_for_bits(nOt) as int + 1);
        // the surplus block is the pushed last >> b, always zero
        // (the old tail is bounded by 2^e <= 2^b)
        assert(sT[(sT.len() - 1) as int] == sO[(L as int - 1)] >> (b as u32));
        assert(sO[(L as int - 1)] < (1u32 << (e as u32))) by {
            assert(e == 0 || sO[(L - 1) as int] < (1u32 << ((nO as int % 32) as u32)));
            assert(blocks_for_bits(nO) == L);
            assert(1u32 << (nO as int % 32) == 1u32 << ((nO as int % 32) as u32));
            assert((nO as int % 32) == (e as int));
        }
        let v_t: u32 = sO[(L as int - 1)];
        assert((v_t >> (b as u32)) == 0u32) by (bit_vector)
            requires
                v_t < (1u32 << (e as u32)),
                (e as u32) <= (b as u32),
                (b as u32) <= 31u32,
        ;
        assert(sT[(sT.len() - 1) as int] == 0u32);
        // trailing: nOt % 32 == e - b == 0 exactly here
        if (e as int) < (b as int) {
            // nOt % 32 = 32 - (b - e): the top valid block is
            // the mid container (low: old block L-2, high: L-1)
            let band = 32 - (b as int - e as int);
            assert((nOt as int) % 32 == band);
            let top_i = (blocks_for_bits(nOt) - 1) as int;
            assert(top_i == (L as int) - w as int - 2);
            let lo_v: u32 = sO[(L as int - 2)];
            let hi_v: u32 = sO[(L as int - 1)];
            let bU: u32 = b as u32;
            let eU: u32 = e as u32;
            let shU: u32 = ((32 - b) as u32);
            let bandU: u32 = (32u32 - (bU - eU)) as u32;
            assert(shU == (32u32 - bU)) by { }
            assert((bandU as int) == band) by { }
            assert(sT[top_i]
                == ((lo_v >> bU) | (hi_v << shU))) by { }
            assert((hi_v << shU) < (1u32 << bandU)) by (bit_vector)
                requires
                    hi_v < (1u32 << eU),
                    bandU == (eU + shU),
                    bandU <= 31u32,
                    shU <= 31u32,
            ;
            assert((lo_v >> bU) < (1u32 << bandU)) by (bit_vector)
                requires
                    (32u32 - bU) <= bandU,
                    bU >= 1u32,
                    bandU <= 31u32,
            ;
            assert((((lo_v >> bU) | (hi_v << shU)) < (1u32 << bandU))) by (bit_vector)
                requires
                    (lo_v >> bU) < (1u32 << bandU),
                    (hi_v << shU) < (1u32 << bandU),
            ;
            assert(sT[top_i] < (1u32 << bandU)) by { }
            assert((nOt as int) % 32 == 0
                || (sT[(blocks_for_bits(nOt) - 1) as int]
                    < (1u32 << ((nOt as int % 32) as u32)))) by {
                assert(1u32 << (nOt as int % 32) == 1u32 << ((nOt as int % 32) as u32));
                assert((nOt as int % 32) == band);
            }
        } else {
            // e == b: nOt is a whole-block multiple; no tail bound
            assert((nOt as int) % 32 == 0);
            assert((nOt as int) % 32 == 0 || (sT[(blocks_for_bits(nOt) - 1) as int] < (1u32 << ((nOt as int % 32) as u32))));
        }
    } else {
        // the tight world: exactly blocks_for_bits blocks
        assert(blocks_for_bits(nOt) as int == (L as int - w as int)) by {
            if (e as int) == 0 {
                assert((nO as int) == 32 * (L as int)) by {
                    assert(blocks_for_bits(nO) == L);
                    assert((e as int) == 0);
                }
                assert((nOt as int) == 32 * ((L as int) - w as int) - (b as int)) by {
                    assert((at as int) == 32 * (w as int) + (b as int));
                }
                assert((b as int) > 0);
                assert((nOt as int) == 32 * ((L as int) - w as int - 1)
                    + (32 - (b as int)));
                assert((nOt as int) % 32 == 32 - (b as int));
                assert(blocks_for_bits(nOt) as int == (L as int) - w as int);
            } else {
                // e > b
                assert((e as int) > (b as int));
                assert((nO as int) == 32 * ((L as int) - 1) + (e as int)) by {
                    assert(blocks_for_bits(nO) == L);
                }
                assert((nOt as int) == 32 * ((L as int) - 1 - w as int)
                    + ((e as int) - (b as int))) by {
                    assert((at as int) == 32 * (w as int) + (b as int));
                }
                assert((nOt as int) % 32 == (e as int) - (b as int));
                assert(((e as int) - (b as int)) > 0);
                assert(((e as int) - (b as int)) < 32);
                assert(blocks_for_bits(nOt) as int
                    == (L as int) - 1 - w as int + 1);
            }
        }
        assert(sT.len() as int == blocks_for_bits(nOt) as int);
        // trailing: the top valid block is the pure-shifted tail
        if (nOt as int) % 32 > 0 {
            let band = nOt as int % 32;
            let top_i = (blocks_for_bits(nOt) - 1) as int;
            assert(top_i == (L as int) - w as int - 1);
            assert(sT[top_i] == (sO[(L as int - 1)] >> (b as u32)));
            if (e as int) > 0 {
                assert(sO[(L as int - 1)] < (1u32 << (e as u32))) by {
                    assert(e == 0 || sO[(L - 1) as int] < (1u32 << ((nO as int % 32) as u32)));
                    assert(blocks_for_bits(nO) == L);
                    assert(1u32 << (nO as int % 32)
                        == 1u32 << ((nO as int % 32) as u32));
                    assert((nO as int % 32) == (e as int));
                }
                let tv: u32 = sO[(L as int - 1)];
                let bU: u32 = b as u32;
                let eU: u32 = e as u32;
                let bandU: u32 = (band) as u32;
                assert((tv >> bU) < (1u32 << bandU)) by (bit_vector)
                    requires
                        tv < (1u32 << eU),
                        bandU == (eU - bU),
                        bU <= 31u32,
                        eU <= 31u32,
                ;
            } else {
                // e == 0: any tail word, still bounded by the shift
                let tv: u32 = sO[(L as int - 1)];
                let bU: u32 = b as u32;
                let bndU: u32 = (32u32 - bU) as u32;
                assert((tv >> bU) < (1u32 << bndU)) by (bit_vector)
                    requires
                        bndU == (32u32 - bU),
                        bndU <= 31u32,
                ;
                assert((1u32 << (32u32 - bU))
                    == (1u32 << ((band) as u32))) by { }
            }
            assert(1u32 << (band) == 1u32 << ((band) as u32)) by { }
            assert((nOt as int) % 32 == 0
                || (sT[(blocks_for_bits(nOt) - 1) as int]
                    < (1u32 << ((nOt as int % 32) as u32)))) by {
                assert(1u32 << (nOt as int % 32)
                    == 1u32 << ((nOt as int % 32) as u32));
            }
        } else {
            assert((nOt as int) % 32 == 0 || (sT[(blocks_for_bits(nOt) - 1) as int] < (1u32 << ((nOt as int % 32) as u32))));
        }
    }
    // (b) moved tier: bit j of the result reads old bit at + j
    assert forall|j: usize| j < nOt implies
        bit_at(sT, nOt, j)
            == bit_at(sO, nO, (at + j) as usize) by {
        assert(((at as int) + (j as int)) < (nO as int)) by {
            assert(j < nOt);
            assert((nOt as int) == ((nO as int) - (at as int)));
        }
        let i = (at + j) as usize;
        int_div_bound_lemma(j, nOt);
        let wj = j / 32;
        let tj = j % 32;
        let wi = i / 32;
        let ti = i % 32;
        assert((i as int) == 32 * (w as int) + (b as int) + (j as int));
        assert((j as int) == 32 * (wj as int) + (tj as int));
        assert(tj < 32);
        assert((wi as int) < (L as int)) by {
            assert((i as int) < (nO as int)) by {
                assert(j < nOt);
                assert((nOt as int) == ((nO as int) - (at as int)));
            }
            assert((nO as int) <= 32 * (L as int)) by {
                assert(blocks_for_bits(nO) == L);
            }
            assert((i as int) / 32 < (L as int));
        }
        if (b as int) + (tj as int) < 32 {
            // the source bit stays in block (w + wj); delivered by
            // the low shift (sO[w + wj] >> b)
            assert((wi as int) == (w as int) + (wj as int)) by {
                assert((i as int)
                    == 32 * ((w as int) + (wj as int))
                        + ((b as int) + (tj as int)));
                assert((b as int) + (tj as int) < 32);
            }
            assert((ti as int) == (b as int) + (tj as int));
            assert((wj as int) <= (L as int) - (w as int) - 1) by {
                assert((i as int) < (nO as int));
                assert((nO as int) <= 32 * (L as int)) by { }
                assert((i as int) == 32 * (w as int + wj as int)
                    + (b as int + tj as int));
                assert((i as int) < 32 * ((w as int + wj as int) + 1));
                assert(32 * (w as int + wj as int) < (nO as int));
            }
            if (wj as int) < (L as int) - (w as int) - 1 {
                // mid container of the result
                assert(sT[wj as int]
                    == ((sO[(w as int + wj as int)] >> (b as u32))
                        | (sO[(w as int + wj as int) + 1]
                            << ((32 - b) as u32))));
                lemma_shl_low_zero(
                    sO[(w as int + wj as int) + 1], (32 - b) as usize, tj);
                assert((sO[(w as int + wj as int) + 1]
                    << ((32 - b) as u32)) & (1u32 << (tj as u32)) == 0u32);
                lemma_or_low_preserve(sT[wj as int],
                    (sO[(w as int + wj as int)] >> (b as u32)),
                    (sO[(w as int + wj as int) + 1]
                        << ((32 - b) as u32)), tj);
                lemma_shr_bit(sO[(w as int + wj as int)], b, tj);
            } else {
                // the tail slot: a pure shift of the last block
                assert((wj as int) == (L as int) - (w as int) - 1);
                assert(sT[wj as int]
                    == (sO[(L as int - 1)] >> (b as u32)));
                assert((w as int) + (wj as int) == (L as int) - 1);
                lemma_shr_bit(sO[(L as int - 1)], b, tj);
            }
            assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
            assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
        } else {
            // the source bit crosses into block (w + wj + 1);
            // delivered by the high shift (sO[w + wj + 1] << (32 - b)).
            // The tail slot never hosts a crossing bit: it would
            // place i at or past 32 * L, beyond nO.
            assert((b as int) + (tj as int) >= 32);
            assert((wj as int) < (L as int) - (w as int) - 1) by {
                if (wj as int) >= (L as int) - (w as int) - 1 {
                    assert((wj as int) == (L as int) - (w as int) - 1);
                    assert((w as int) + (wj as int) == (L as int) - 1);
                    assert((i as int)
                        == 32 * ((L as int) - 1) + (b as int) + (tj as int));
                    assert((i as int) >= 32 * (L as int)) by { }
                    assert((nO as int) <= 32 * (L as int)) by {
                        assert(blocks_for_bits(nO) == L);
                    }
                    assert((i as int) < (nO as int)) by { }
                    assert(false);
                }
            }
            assert((wi as int) == (w as int) + (wj as int) + 1) by {
                assert((i as int)
                    == 32 * ((w as int) + (wj as int))
                        + ((b as int) + (tj as int)));
                assert((b as int) + (tj as int) >= 32);
                assert((b as int) + (tj as int) < 64) by {
                    assert((b as int) <= 31);
                    assert((tj as int) <= 31);
                }
            }
            assert((ti as int) == (b as int) + (tj as int) - 32);
            assert(sT[wj as int]
                == ((sO[(w as int + wj as int)] >> (b as u32))
                    | (sO[(wi as int)] << ((32 - b) as u32)))) by {
                assert((w as int + wj as int) + 1 == (wi as int));
            }
            lemma_shr_hi_zero(sO[(w as int + wj as int)], b, tj);
            assert((sO[(w as int + wj as int)] >> (b as u32))
                & (1u32 << (tj as u32)) == 0u32);
            lemma_or_compose_bit(sT[wj as int],
                (sO[(w as int + wj as int)] >> (b as u32)),
                (sO[(wi as int)] << ((32 - b) as u32)), tj);
            // the high part's bit tj is the source's bit ti
            lemma_shl_bit(sO[(wi as int)], (32 - b) as usize, ti);
            assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
            assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
        }
    }
}
            }
        }
        other
    }
}


// ---------------------------------------------------------------------------
// append kit (the variable-shift block cascade): the moving branch of
// append pushes each source block in two halves -- its low b bits are
// OR-ed into the current tail block, and the remaining 32-b bits are
// shifted down into a fresh block -- so each destination bit crosses at
// most one block boundary. The four half-shift machines below carry the
// bit exchange and the region-disjointness facts; the two preexisting
// OR lemmas (lemma_or_low_preserve / lemma_or_compose_bit) transfer the
// bit between the OR partners.
// ---------------------------------------------------------------------------

/// (x << b) bit (t + b) == x bit t (t + b < 32): the shift-up half.
pub proof fn lemma_shl_bit(x: u32, b: usize, t: usize)
    requires
        (t as int) + (b as int) < 32,
    ensures
        (((x << (b as u32)) & (1u32 << ((t + b) as u32))) != 0u32)
            == ((x & (1u32 << (t as u32))) != 0u32),
{
    let b32: u32 = b as u32;
    let t32: u32 = t as u32;
    assert((((x << b32) & (1u32 << (t32 + b32))) != 0u32)
        == ((x & (1u32 << t32)) != 0u32)) by (bit_vector)
        requires
            (t32 + b32) < 32u32,
    ;
    assert((1u32 << (t32 + b32)) == (1u32 << ((t + b) as u32))) by {
        assert(((t32 as int) + (b32 as int)) == ((t as int) + (b as int)));
    }
}

/// (x << b) bit q == 0 for q < b: the shift-up clears the low region.
pub proof fn lemma_shl_low_zero(x: u32, b: usize, q: usize)
    requires
        (q as int) < (b as int),
        (b as int) <= 31,
    ensures
        ((x << (b as u32)) & (1u32 << (q as u32))) == 0u32,
{
    let b32: u32 = b as u32;
    let q32: u32 = q as u32;
    assert(((x << b32) & (1u32 << q32)) == 0u32) by (bit_vector)
        requires
            q32 < b32,
    ;
}

/// (x >> c) bit t == x bit (t + c) (t + c < 32): the shift-down half.
pub proof fn lemma_shr_bit(x: u32, c: usize, t: usize)
    requires
        (t as int) + (c as int) < 32,
    ensures
        (((x >> (c as u32)) & (1u32 << (t as u32))) != 0u32)
            == ((x & (1u32 << ((t + c) as u32))) != 0u32),
{
    let c32: u32 = c as u32;
    let t32: u32 = t as u32;
    assert((((x >> c32) & (1u32 << t32)) != 0u32)
        == ((x & (1u32 << (t32 + c32))) != 0u32)) by (bit_vector)
        requires
            (t32 + c32) < 32u32,
    ;
    assert((1u32 << (t32 + c32)) == (1u32 << ((t + c) as u32))) by {
        assert(((t32 as int) + (c32 as int)) == ((t as int) + (c as int)));
    }
}

/// (x >> c) bit q == 0 for q + c >= 32: the shift-down clears the top.
pub proof fn lemma_shr_hi_zero(x: u32, c: usize, q: usize)
    requires
        (q as int) + (c as int) >= 32,
        (q as int) < 32,
        (c as int) <= 31,
    ensures
        ((x >> (c as u32)) & (1u32 << (q as u32))) == 0u32,
{
    let c32: u32 = c as u32;
    let q32: u32 = q as u32;
    assert(((x >> c32) & (1u32 << q32)) == 0u32) by (bit_vector)
        requires
            (q32 + c32) >= 32u32,
    ;
}

/// the full per-bit postcondition of append's moving branch (b > 0):
/// from the final block map (the self-tail OR, the mid containers, the
/// special final push, and the popped tier) to the kept and appended
/// bit tiers, the structural length tier, and the restored tail
/// discipline.
pub proof fn append_shift_semantics(
    sF: Seq<u32>, sS: Seq<u32>, sOt: Seq<u32>,
    nO: usize, nOt: usize, b: usize, o: usize, popped: bool,
)
    requires
        (b as int) >= 1,
        (b as int) <= 31,
        (sS.len() as int) == (blocks_for_bits(nO) as int),
        (sOt.len() as int) == (blocks_for_bits(nOt) as int),
        (nO as int) == 32 * ((sS.len() as int) - 1) + (b as int),
        (nO as int + nOt as int) <= usize::MAX as int,
        (o as int) == (nOt as int) % 32,
        (sS.len() as int) >= 1,
        sS[(sS.len() - 1) as int] < (1u32 << (b as u32)),
        (o as int) > 0 ==> sOt[(sOt.len() - 1) as int] < (1u32 << (o as u32)),
        popped == !((b as int + o as int > 32) || (o as int == 0)),
        (sF.len() as int) == (sS.len() as int) + (sOt.len() as int)
            - (if popped { 1int } else { 0int }),
        forall|w2: int| 0 <= w2 < (sS.len() as int) - 1 ==> sF[w2] == sS[w2],
        (sOt.len() as int) >= 1 ==> sF[(sS.len() - 1) as int]
            == (sS[(sS.len() - 1) as int] | (sOt[0] << (b as u32))),
        (sOt.len() as int) == 0 ==> sF[(sS.len() - 1) as int]
            == sS[(sS.len() - 1) as int],
        forall|w2: int| (sS.len() as int) <= w2
            && w2 <= (sS.len() as int + sOt.len() as int) - 2
            && w2 < (sF.len() as int) ==>
            #[trigger] sF[w2] == ((sOt[w2 - (sS.len() as int)] >> ((32 - b) as u32))
                | (sOt[w2 - (sS.len() as int) + 1] << (b as u32))),
        ((sOt.len() as int) >= 1 && !popped) ==> (sF[(sF.len() - 1) as int]
            == (sOt[(sOt.len() - 1) as int] >> ((32 - b) as u32))),
    ensures
        (sF.len() as int) == (blocks_for_bits((nO + nOt) as usize) as int),
        ((nO + nOt) % 32 == 0)
            || (sF[(blocks_for_bits((nO + nOt) as usize) - 1) as int]
                < (1u32 << (((nO + nOt) % 32) as u32))),
        forall|j: usize| j < nO ==> bit_at(sF, (nO + nOt) as usize, j) == bit_at(sS, nO, j),
        forall|j: usize| j < nOt ==>
            bit_at(sF, (nO + nOt) as usize, (nO + j) as usize) == bit_at(sOt, nOt, j),
{
    let L = sS.len() as int;
    let M = sOt.len() as int;
    let nF = (nO as int) + (nOt as int);
    // (structure) the length tier: blocks_for_bits(nF)
    //     == L + M - (popped ? 1 : 0)
    // (o == 0 keeps whole blocks; o > 0 keeps the shifted remainder
    // unless the b+o window fits within one block, in which case the
    // last pushed block is dropped)
    assert(blocks_for_bits((nO + nOt) as usize) as int
        == L + M - (if popped { 1int } else { 0int })) by {
        let full = (nOt as int) / 32;
        if (o as int) == 0 {
            assert((nOt as int) == 32 * full);
            assert(M == full) by {
                assert(blocks_for_bits(nOt) == (sOt.len() as usize));
                assert((nOt as int) % 32 == 0);
            }
            // o == 0 && b != 0 forces the will_overflow world
            assert(!popped) by { }
            assert((nF as int) == 32 * (L - 1 + full) + (b as int)) by {
                assert((nO as int) == 32 * (L - 1) + (b as int));
                assert((nOt as int) == 32 * full);
            }
            assert((nF as int) % 32 == (b as int)) by {
                assert((b as int) < 32);
            }
            assert((nF as int) / 32 == L - 1 + full);
            assert(blocks_for_bits((nO + nOt) as usize) as int == L + full) by { }
            assert(L + M - (if popped { 1int } else { 0int }) == L + full) by { }
        } else {
            assert((nOt as int) == 32 * full + (o as int));
            assert(M == full + 1) by {
                assert((nOt as int) % 32 > 0);
                assert(blocks_for_bits(nOt) == (sOt.len() as usize));
            }
            if (b as int + o as int) <= 32 {
                assert(popped) by { }
                if (b as int + o as int) == 32 {
                    assert((nF as int)
                        == 32 * (L - 1 + full) + 32) by {
                        assert((nO as int) == 32 * (L - 1) + (b as int));
                        assert((nOt as int) == 32 * full + (o as int));
                    }
                    assert((nF as int) % 32 == 0);
                    assert((nF as int) / 32 == L + full);
                    assert(blocks_for_bits((nO + nOt) as usize) as int == L + full) by { }
                    assert(L + M - 1 == L + full) by { }
                } else {
                    assert((nF as int)
                        == 32 * (L - 1 + full) + (b as int + o as int)) by {
                        assert((nO as int) == 32 * (L - 1) + (b as int));
                        assert((nOt as int) == 32 * full + (o as int));
                    }
                    assert((b as int + o as int) < 32);
                    assert((nF as int) % 32 == (b as int + o as int));
                    assert((nF as int) / 32 == L - 1 + full);
                    assert(blocks_for_bits((nO + nOt) as usize) as int
                        == L - 1 + full + 1) by { }
                    assert(L + M - 1 == L + full) by { }
                }
            } else {
                assert(!popped) by { }
                if (o as int) == 0 {
                    // whole-block other: M == full, the tail is b itself
                    assert(M == full) by { }
                    assert((nF as int)
                        == 32 * (L - 1 + full) + (b as int)) by {
                        assert((nO as int) == 32 * (L - 1) + (b as int));
                        assert((nOt as int) == 32 * full);
                    }
                    assert((b as int) >= 1);
                    assert((b as int) < 32);
                    assert((nF as int) % 32 == (b as int));
                    assert((nF as int) / 32 == L - 1 + full);
                    assert(blocks_for_bits((nO + nOt) as usize) as int
                        == L + full) by { }
                    assert(L + M == 32 * 0 + L + full) by { }
                } else {
                    // b + o > 32: the surplus spills into a fresh block
                    assert((b as int + o as int) >= 33) by {
                        if (b as int + o as int) <= 32 {
                            assert(popped);
                        }
                    }
                    assert(M == full + 1) by { }
                    assert((nF as int)
                        == 32 * (L + full) + (b as int + o as int - 32)) by {
                        assert((nO as int) == 32 * (L - 1) + (b as int));
                        assert((nOt as int) == 32 * full + (o as int));
                        assert((nF as int)
                            == 32 * (L - 1 + full) + (b as int + o as int)) by { }
                        assert((b as int + o as int)
                            == 32 + (b as int + o as int - 32)) by { }
                    }
                    assert((b as int + o as int - 32) >= 1) by { }
                    assert((b as int + o as int - 32) < 32) by {
                        assert((b as int) <= 31);
                        assert((o as int) <= 31);
                    }
                    assert((nF as int) % 32 == (b as int + o as int - 32));
                    assert((nF as int) / 32 == L + full);
                    assert(blocks_for_bits((nO + nOt) as usize) as int
                        == L + full + 1) by { }
                    assert(L + M == L + full + 1) by { }
                }
            }
        }
    }
    // (trailing) the restored tail discipline
    if (nF as int) % 32 != 0 {
        let eF = (nF as int) % 32;
        assert(0 < eF);
        assert(eF < 32);
        assert(sF.len() == blocks_for_bits((nO + nOt) as usize) as int);
        assert((blocks_for_bits((nO + nOt) as usize) - 1) == (sF.len() - 1));
        if M == 0 {
            // nothing appended: the tail is the self tail
            assert(sF[(L - 1) as int] == sS[(L - 1) as int]);
            assert(sS[(L - 1) as int] < (1u32 << (b as u32))) by { }
            assert((nF as int) == (nO as int)) by {
                assert((nOt as int) == 0) by { assert(M == 0); }
            }
            assert(eF == (b as int)) by { }
            assert(sF[(sF.len() - 1) as int] < (1u32 << (eF as u32)));
        } else if popped {
            // the slack block was dropped: the new tail is the last
            // surviving container (or the self tail when M == 1)
            assert((nF as int) % 32 == (b as int + o as int)) by {
                assert((nF as int) == 32 * (L - 1 + M - 1) + (b as int + o as int)) by {
                    let full = (nOt as int) / 32;
                    assert(M == full + 1) by { }
                    assert((nO as int) == 32 * (L - 1) + (b as int));
                    assert((nOt as int) == 32 * full + (o as int));
                }
                assert((b as int + o as int) < 32) by {
                    if (b as int + o as int) == 32 {
                        assert((nF as int) % 32 == 0);
                    }
                }
            }
            if M == 1 {
                // the tail is the self tail OR block
                assert((sF.len() - 1) == (L - 1)) by { }
                let b32: u32 = b as u32;
                let o32: u32 = o as u32;
                let v1: u32 = sOt[0];
                let v2: u32 = sS[(L - 1) as int];
                assert(sF[(L - 1) as int] == (v2 | (v1 << b32))) by { }
                assert(sOt[0] == sOt[(M - 1) as int]);
                assert(sOt[(M - 1) as int] < (1u32 << (o as u32))) by { }
                assert(v1 < (1u32 << o32)) by {
                    assert((1u32 << o32) == (1u32 << (o as u32))) by { }
                }
                assert((v1 << b32) < (1u32 << (b32 + o32))) by (bit_vector)
                    requires
                        v1 < (1u32 << o32),
                        (b32 + o32) <= 31u32,
                ;
                assert(v2 < (1u32 << (b32 + o32))) by (bit_vector)
                    requires
                        v2 < (1u32 << b32),
                        (b32 + o32) <= 31u32,
                ;
                assert((v2 | (v1 << b32)) < (1u32 << (b32 + o32))) by (bit_vector)
                    requires
                        v2 < (1u32 << (b32 + o32)),
                        (v1 << b32) < (1u32 << (b32 + o32)),
                ;
                assert(((b32 as int) + (o32 as int)) == ((nF as int) % 32)) by { }
                assert((1u32 << (b32 + o32))
                    == (1u32 << (((nF as int) % 32) as u32))) by { }
                assert(sF[(sF.len() - 1) as int] < (1u32 << ((nF as int % 32) as u32)));
            } else {
                // the tail is the container of sOt[M-2] and sOt[M-1]
                assert((sF.len() - 1) == L + M - 2) by { }
                let b32: u32 = b as u32;
                let o32: u32 = o as u32;
                let lo: u32 = sOt[(M - 2) as int];
                let hi: u32 = sOt[(M - 1) as int];
                let tail_word: u32 = sF[(L + M - 2) as int];
                let sh_dn: u32 = (32u32 - b32) as u32;
                assert(tail_word == ((lo >> sh_dn) | (hi << b32))) by { }
                assert(hi < (1u32 << o32)) by {
                    assert(sOt[(M - 1) as int] < (1u32 << (o as u32))) by {
                        assert((o as int) > 0);
                    }
                    assert((1u32 << (o as u32)) == (1u32 << o32)) by { }
                }
                assert((lo >> sh_dn) < (1u32 << (b32 + o32))) by (bit_vector)
                    requires
                        (sh_dn + b32) == 32u32,
                        b32 >= 1u32,
                        (b32 + o32) <= 31u32,
                ;
                assert((hi << b32) < (1u32 << (b32 + o32))) by (bit_vector)
                    requires
                        hi < (1u32 << o32),
                        (b32 + o32) <= 31u32,
                ;
                assert(tail_word < (1u32 << (b32 + o32))) by (bit_vector)
                    requires
                        tail_word == ((lo >> sh_dn) | (hi << b32)),
                        (lo >> sh_dn) < (1u32 << (b32 + o32)),
                        (hi << b32) < (1u32 << (b32 + o32)),
                ;
                assert(((b32 as int) + (o32 as int)) == ((nF as int) % 32)) by { }
                assert((1u32 << (b32 + o32))
                    == (1u32 << (((nF as int) % 32) as u32))) by { }
                assert(sF[(sF.len() - 1) as int] < (1u32 << ((nF as int % 32) as u32)));
            }
        } else {
            // the special final push is the tail
            assert((nF as int) % 32
                == (if (o as int) == 0 { b as int } else { b as int + o as int - 32 })) by {
                let full = (nOt as int) / 32;
                if (o as int) == 0 {
                    assert(M == full) by { }
                    assert((nF as int) == 32 * (L - 1 + full) + (b as int)) by {
                        assert((nO as int) == 32 * (L - 1) + (b as int));
                        assert((nOt as int) == 32 * full);
                    }
                    assert((b as int) >= 1);
                    assert((b as int) < 32);
                } else {
                    assert(M == full + 1) by { }
                    assert((b as int + o as int) >= 33) by {
                        if (b as int + o as int) <= 32 {
                            assert(popped);
                        }
                    }
                    assert((nF as int)
                        == 32 * (L + full) + (b as int + o as int - 32)) by {
                        assert((nO as int) == 32 * (L - 1) + (b as int));
                        assert((nOt as int) == 32 * full + (o as int));
                        assert((nF as int)
                            == 32 * (L - 1 + full) + (b as int + o as int)) by { }
                        assert((b as int + o as int)
                            == 32 + (b as int + o as int - 32)) by { }
                    }
                    assert((b as int + o as int - 32) >= 1);
                    assert((b as int + o as int - 32) < 32) by {
                        assert((b as int) <= 31);
                        assert((o as int) <= 31);
                    }
                }
            }
            assert((sF.len() - 1) == L + M - 1) by { }
            let b32: u32 = b as u32;
            let o32: u32 = o as u32;
            let hi: u32 = sOt[(M - 1) as int];
            let tail_word: u32 = sF[(L + M - 1) as int];
            let sh_dn: u32 = (32u32 - b32) as u32;
            assert(tail_word == (hi >> sh_dn)) by { }
            if (o as int) > 0 {
                assert(hi < (1u32 << o32)) by {
                    assert(sOt[(M - 1) as int] < (1u32 << (o as u32))) by { }
                    assert((1u32 << (o as u32)) == (1u32 << o32)) by { }
                }
                let tokU: u32 = ((b32 + o32 - 32u32) as u32);
                assert((hi >> sh_dn) < (1u32 << tokU)) by (bit_vector)
                    requires
                        hi < (1u32 << o32),
                        (sh_dn + b32) == 32u32,
                        (o32 + b32) >= 32u32,
                        tokU == (b32 + o32 - 32u32),
                ;
            } else {
                // o == 0: any tail word still bounded under the shift
                assert((hi >> sh_dn) < (1u32 << b32)) by (bit_vector)
                    requires
                        (sh_dn + b32) == 32u32,
                        b32 <= 31u32,
                ;
            }
            assert(sF[(sF.len() - 1) as int] == tail_word) by { }
            if (o as int) > 0 {
                assert(((nF as int % 32)) == ((b32 as int) + (o32 as int) - 32)) by { }
                assert(sF[(sF.len() - 1) as int] < (1u32 << (b32 + o32 - 32u32))) by { }
                assert((1u32 << (b32 + o32 - 32u32))
                    == (1u32 << (((nF as int) % 32) as u32))) by {
                    assert((nF as int % 32) == ((b32 as int) + (o32 as int) - 32));
                }
                assert(sF[(sF.len() - 1) as int] < (1u32 << ((nF as int % 32) as u32)));
            } else {
                assert((nF as int % 32) == (b as int)) by { }
                assert((1u32 << b32) == (1u32 << (((nF as int) % 32) as u32))) by {
                    assert((nF as int % 32) == (b32 as int));
                }
                assert(sF[(sF.len() - 1) as int] < (1u32 << ((nF as int % 32) as u32)));
            }
        }
    }
    // (a) kept tier: j < nO reads its own block unchanged (below the
    // b-boundary of the tail OR)
    assert forall|j: usize| j < nO implies
        bit_at(sF, (nO + nOt) as usize, j) == bit_at(sS, nO, j) by {
        int_div_bound_lemma(j, nO);
        let wj = j / 32;
        let tj = j % 32;
        assert(tj < 32);
        assert((wj as int) < L) by {
            assert((j as int) < (nO as int));
            assert((nO as int) <= 32 * L) by {
                assert((nO as int) == 32 * (L - 1) + (b as int));
                assert((b as int) < 32);
            }
            assert((wj as int) == (j as int) / 32);
        }
        if (wj as int) < L - 1 {
            assert(sF[wj as int] == sS[wj as int]);
        } else {
            assert((wj as int) == L - 1);
            assert((tj as int) < (b as int)) by {
                assert((j as int) < (nO as int));
                assert((nO as int) == 32 * (L - 1) + (b as int));
                assert((j as int) == 32 * (wj as int) + (tj as int));
            }
            if M >= 1 {
                // the tail OR fills only positions at or past b
                lemma_shl_low_zero(sOt[0], b, tj);
                assert((sOt[0] << (b as u32)) & (1u32 << (tj as u32)) == 0u32);
                lemma_or_low_preserve(sF[(L - 1) as int],
                    sS[(L - 1) as int], (sOt[0] << (b as u32)), tj);
            } else {
                assert(sF[(L - 1) as int] == sS[(L - 1) as int]);
            }
        }
        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
    }
    // (b) moved tier: bit j of the old other lands at nO + j
    assert forall|j: usize| j < nOt implies
        bit_at(sF, (nO + nOt) as usize, (nO + j) as usize) == bit_at(sOt, nOt, j) by {
        assert((nOt as int) >= 1) by {
            if (nOt as int) == 0 {
                assert(j < 0) by { assert(j < nOt); }
            }
        }
        assert((nOt as int) > 0);
        let i = (nO + j) as usize;
        assert((i as int) == (nO as int) + (j as int));
        int_div_bound_lemma(j, nOt);
        let wj = j / 32;
        let tj = j % 32;
        let wi = i / 32;
        let ti = i % 32;
        assert((j as int) == 32 * (wj as int) + (tj as int));
        assert(tj < 32);
        assert((wj as int) < M) by {
            if (o as int) == 0 {
                assert((nOt as int) == 32 * M) by {
                    assert((nOt as int) % 32 == 0);
                    assert((sOt.len() as usize) == blocks_for_bits(nOt));
                    assert(M == (nOt as int) / 32);
                }
            } else {
                assert((nOt as int) == 32 * (M - 1) + (o as int)) by {
                    assert((sOt.len() as usize) == blocks_for_bits(nOt));
                    assert(M == ((nOt as int) / 32) + 1) by {
                        assert((sOt.len() as usize) == blocks_for_bits(nOt));
                        assert((sOt.len() as int) == ((nOt as int) / 32) + 1) by {
                            assert(blocks_for_bits(nOt) as int
                                == ((nOt as int) / 32) + 1) by {
                                assert((nOt as int) % 32 == (o as int)) by { }
                                assert((o as int) > 0) by { }
                            }
                            assert(M == (sOt.len() as int)) by { }
                        }
                    }
                    assert((nOt as int) == 32 * ((nOt as int) / 32) + (o as int));
                }
                assert((nOt as int) < 32 * M) by { }
            }
            assert((nOt as int) <= 32 * M);
            assert((j as int) < (nOt as int)) by { }
            assert((j as int) < 32 * M) by { }
            assert((wj as int) == (j as int) / 32);
            assert((j as int) / 32 < M);
        }
        // i decomposes as 32*(L - 1 + wj) + (b + tj)
        assert((i as int) == 32 * (L - 1 + (wj as int)) + ((b as int) + (tj as int))) by {
            assert((nO as int) == 32 * (L - 1) + (b as int));
            assert((j as int) == 32 * (wj as int) + (tj as int));
        }
        assert(1u32 << (j % 32) == 1u32 << ((j % 32) as u32));
        assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
        if (b as int) + (tj as int) < 32 {
            // stays within the container started at the old tail
            assert((wi as int) == L - 1 + (wj as int)) by { }
            assert((ti as int) == (b as int) + (tj as int));
            if (wj as int) == 0 {
                // the self tail block: sS[L-1] | (sOt[0] << b)
                assert(sF[(L - 1) as int]
                    == (sS[(L - 1) as int] | (sOt[0] << (b as u32))));
                assert((sS[(L - 1) as int] & (1u32 << (ti as u32))) == 0u32) by {
                    assert((ti as int) >= (b as int)) by { }
                    assert((ti as int) < 32);
                    assert((b as int) <= (ti as int)) by {
                        assert((ti as int) >= (b as int));
                    }
                    assert((b as usize) <= (ti as usize)) by { }
                    assert((ti as usize) < 32);
                    lemma_pow_lt_bit(sS[(L - 1) as int], b, ti);
                }
                lemma_or_compose_bit(sF[(L - 1) as int],
                    sS[(L - 1) as int], (sOt[0] << (b as u32)), ti);
                lemma_shl_bit(sOt[0], b, tj);
                assert(1u32 << (ti as int) == 1u32 << ((ti) as u32)) by {
                    assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
                    assert((ti as usize) == (i % 32));
                }
            } else {
                // a mid container: the low part covers [0, 32-b), the
                // (sOt[wj] << b) part carries the bit
                assert((L <= L - 1 + (wj as int) <= L + M - 2)) by {
                    assert((wj as int) >= 1);
                    assert((wj as int) <= M - 1);
                }
                let w2 = L - 1 + (wj as int);
                assert(sF[w2 as int]
                    == ((sOt[(w2 - L) as int] >> ((32 - b) as u32))
                        | (sOt[(w2 - L) as int + 1] << (b as u32))));
                assert((w2 - L) as int == (wj as int) - 1);
                lemma_shr_hi_zero(sOt[(wj as int) - 1], (32 - b) as usize, ti);
                assert((sOt[(wj as int) - 1] >> ((32 - b) as u32))
                    & (1u32 << (ti as u32)) == 0u32);
                lemma_or_compose_bit(sF[w2 as int],
                    (sOt[(wj as int) - 1] >> ((32 - b) as u32)),
                    (sOt[(wj as int)] << (b as u32)), ti);
                lemma_shl_bit(sOt[(wj as int)], b, tj);
                assert(1u32 << (ti as int) == 1u32 << ((ti) as u32)) by {
                    assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
                    assert((ti as usize) == (i % 32));
                }
            }
        } else {
            // crosses into the block after the old tail: delivered by
            // (sOt[wj] >> (32 - b)); the crossing wj == M-1 case lands
            // in the special block (unpopped only, since popped bounds
            // every payload bit below 32 - b)
            assert((wi as int) == L + (wj as int)) by {
                assert((b as int) + (tj as int) >= 32);
                assert((b as int) + (tj as int) < 64) by { }
            }
            assert((ti as int) == (b as int) + (tj as int) - 32);
            if (wj as int) <= M - 2 {
                let w2 = L + (wj as int);
                assert(sF[w2 as int]
                    == ((sOt[(w2 - L) as int] >> ((32 - b) as u32))
                        | (sOt[(w2 - L) as int + 1] << (b as u32))));
                assert((w2 - L) as int == (wj as int));
                lemma_shl_low_zero(sOt[(wj as int) + 1], b, ti);
                assert((sOt[(wj as int) + 1] << (b as u32))
                    & (1u32 << (ti as u32)) == 0u32);
                lemma_or_low_preserve(sF[w2 as int],
                    (sOt[(wj as int)] >> ((32 - b) as u32)),
                    (sOt[(wj as int) + 1] << (b as u32)), ti);
                lemma_shr_bit(sOt[(wj as int)], (32 - b) as usize, ti);
                assert(1u32 << (ti as int) == 1u32 << ((ti) as u32)) by {
                    assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
                    assert((ti as usize) == (i % 32));
                }
            } else {
                // wj == M-1: the crossing bit needs the special block
                assert(!popped) by {
                    if popped {
                        assert((b as int + o as int) <= 32) by { }
                        assert((o as int) > 0) by {
                            if (o as int) == 0 {
                                assert(popped == false) by { }
                            }
                        }
                        // the last payload bit sits below 32 - b
                        assert((tj as int) < (o as int)) by {
                            assert((j as int) < (nOt as int));
                            assert((nOt as int) == 32 * (M - 1) + (o as int)) by { }
                            assert((j as int) == 32 * (M - 1) + (tj as int));
                        }
                        assert((b as int + tj as int) < 32) by {
                            assert((tj as int) < (o as int) <= (32 - b as int)) by { }
                        }
                        assert(false);
                    }
                }
                assert((wj as int) == M - 1);
                assert((wi as int) == L + M - 1);
                assert(sF[(L + M - 1) as int]
                    == (sOt[(M - 1) as int] >> ((32 - b) as u32)));
                lemma_shr_bit(sOt[(M - 1) as int], (32 - b) as usize, ti);
                assert(1u32 << (ti as int) == 1u32 << ((ti) as u32)) by {
                    assert(1u32 << (i % 32) == 1u32 << ((i % 32) as u32));
                    assert((ti as usize) == (i % 32));
                }
            }
        }
    }
    // the bit_at congruence fittings
    assert forall|j: usize| j < nO implies
        bit_at(sF, (nO + nOt) as usize, j) == bit_at(sS, nO, j) by { }
    assert forall|j: usize| j < nOt implies
        bit_at(sF, (nO + nOt) as usize, (nO + j) as usize) == bit_at(sOt, nOt, j) by { }
}

// ===========================================================================
// Coverage diff-set batch D: the verifiable tail of the public surface --
// the cold-borrow face (storage), the unsafe contract domain
// (storage_mut / set_len; the caller-side cfg(test) faces are not taken),
// and the std trait periphery (Clone / PartialEq / PartialOrd / Ord /
// Hash / Display / Extend / FromIterator; Default is the bv_default of
// the state-model section above). The std unsafe keyword itself is
// transcribed away as in get_unchecked above: the Safety contract rides
// requires, the rest of the body is the plain effect.
// Surface evidence: out/batchD-probe/p1.rs (slice return, &mut Vec
// return, char stream, Vec::clone spec availability, lex recursion).
// ===========================================================================

/// Origin Rust (lib.rs:2109-2135 family): the Ordering carrier of
/// std::cmp::Ordering -- materialized as the crate-local three-variant
/// enum (int is spec-only, so the values travel through ord_code).
pub enum BvOrd {
    Less,
    Equal,
    Greater,
}

pub open spec fn ord_code(o: BvOrd) -> int {
    match o {
        BvOrd::Less => -1int,
        BvOrd::Equal => 0int,
        BvOrd::Greater => 1int,
    }
}

/// bit-at-int: the int-indexed reading of a block sequence (the lex
/// family walks int positions; congruent with bit_at on usize).
pub open spec fn lex_bit(s: Seq<u32>, i: int) -> bool {
    (s[i / 32] & (1u32 << (i % 32))) != 0u32
}

/// The lexicographic order walk: the first min-length position where the
/// bits differ decides, else the length decides. Positions outside
/// [0, min(la, lb)] fall back to 0 (the spec fn cannot carry requires;
/// the call family always enters at 0 with la, lb >= 0).
pub open spec fn spec_cmp_from(a: Seq<u32>, b: Seq<u32>, i: int, la: int, lb: int) -> int
    decreases if la < lb { la - i } else { lb - i },
{
    if i < 0 || i > la || i > lb {
        0int
    } else if i == la || i == lb {
        if la < lb { -1int } else if la > lb { 1int } else { 0int }
    } else {
        let x = lex_bit(a, i);
        let y = lex_bit(b, i);
        if x == y {
            spec_cmp_from(a, b, i + 1, la, lb)
        } else if y { -1int } else { 1int }
    }
}

/// the whole-vector compare against spec_cmp_from at the origin.
pub open spec fn spec_bv_cmp(x: &BitVec, y: &BitVec) -> int {
    spec_cmp_from(x.storage@, y.storage@, 0int, x.nbits as int, y.nbits as int)
}

/// prefix-equality frame: equal bits on [i, j) leave the walk unchanged.
pub proof fn lemma_cmp_frame(a: Seq<u32>, b: Seq<u32>, la: int, lb: int, i: int, j: int)
    requires
        0 <= i,
        i <= j,
        j <= la,
        j <= lb,
        forall|k: int| i <= k < j ==> lex_bit(a, k) == lex_bit(b, k),
    ensures
        spec_cmp_from(a, b, i, la, lb) == spec_cmp_from(a, b, j, la, lb),
    decreases j - i,
{
    if i == j {
    } else {
        assert(i < la && i < lb);
        assert(lex_bit(a, i) == lex_bit(b, i));
        assert(spec_cmp_from(a, b, i, la, lb) == spec_cmp_from(a, b, i + 1, la, lb));
        lemma_cmp_frame(a, b, la, lb, i + 1, j);
    }
}

/// first-difference decide: with the [0, widx) prefix equal and the
/// widx bits differing, the origin walk answers by the widx bit pair.
pub proof fn lemma_cmp_first_diff(a: Seq<u32>, b: Seq<u32>, la: int, lb: int, widx: int)
    requires
        0 <= widx,
        widx < la,
        widx < lb,
        forall|k: int| 0 <= k < widx ==> lex_bit(a, k) == lex_bit(b, k),
        lex_bit(a, widx) != lex_bit(b, widx),
    ensures
        spec_cmp_from(a, b, 0int, la, lb)
            == (if lex_bit(b, widx) { -1int } else { 1int }),
{
    lemma_cmp_frame(a, b, la, lb, 0int, widx);
    assert(spec_cmp_from(a, b, widx, la, lb)
        == (if lex_bit(b, widx) { -1int } else { 1int }));
}

/// equal-tail decide: equal bits from i to the shorter end make the
/// walk from i answer by the lengths.
pub proof fn lemma_cmp_equal_tail(a: Seq<u32>, b: Seq<u32>, la: int, lb: int, i: int)
    requires
        0 <= i,
        i <= la,
        i <= lb,
        forall|k: int| i <= k < la && i <= k < lb ==> lex_bit(a, k) == lex_bit(b, k),
    ensures
        spec_cmp_from(a, b, i, la, lb)
            == (if la < lb { -1int } else if la > lb { 1int } else { 0int }),
    decreases if la < lb { la - i } else { lb - i },
{
    if i == la || i == lb {
        assert(spec_cmp_from(a, b, i, la, lb)
            == (if la < lb { -1int } else if la > lb { 1int } else { 0int }));
    } else {
        assert(lex_bit(a, i) == lex_bit(b, i));
        assert(spec_cmp_from(a, b, i, la, lb) == spec_cmp_from(a, b, i + 1, la, lb));
        lemma_cmp_equal_tail(a, b, la, lb, i + 1);
    }
}

impl BitVec {

    /// Origin Rust: pub fn storage(&self) -> &[B] { &self.storage }
    ///     (lib.rs:678-680)
    /// Upstream doc (lib.rs:674-676):
    ///   Exposes the raw block storage of this `BitVec`.
    ///   Only really intended for `BitSet`.
    pub exec fn storage(&self) -> (r: &[u32])
        ensures
            r@ == self.storage@,
            r.len() == self.storage@.len(),
    {
        &self.storage
    }

    /// Origin Rust: pub unsafe fn storage_mut(&mut self) -> &mut Vec<B>
    ///     { &mut self.storage } (lib.rs:689-691)
    /// Upstream doc (lib.rs:681-687):
    ///   Exposes the raw block storage of this `BitVec`.
    ///   # Safety
    ///   Can break the structure's invariants despite not
    ///   giving real memory unsafety. Only really intended for `BitSet`.
    /// The unsafe tier is the caller's: after the borrow the caller may
    /// have broken inv. The callee contract is the value identity at
    /// return (the borrowed storage still holds the pre-call entry
    /// sequence); the post-borrow state is not the callee's to state --
    /// this is the probe B finding (the final-state form is unprovable).
    pub exec fn storage_mut(&mut self) -> (r: &mut Vec<u32>)
        ensures
            old(self).storage@ == r@,
    {
        &mut self.storage
    }

    /// Origin Rust: pub unsafe fn set_len(&mut self, len: usize)
    ///     { self.nbits = len; } (lib.rs:1818-1820)
    /// Upstream doc (lib.rs:1812-1816):
    ///   Sets the number of bits that this `BitVec` considers initialized.
    ///   # Safety
    ///   Almost certainly can cause bad stuff. Only really intended for `BitSet`.
    /// The Safety contract is designed as requires: the new length stays
    /// within the bit capacity (the std Vec::set_len rationale carried
    /// over to the bit domain). inv is deliberately NOT ensured -- the
    /// unsafe caller may legitimately break the structural invariant
    /// here; later in-contract reads stay within the storage because
    /// of the capacity bound.
    pub exec fn set_len(&mut self, len: usize)
        requires
            len <= spec_bit_capacity(self),
        ensures
            final(self).storage@ == old(self).storage@,
            final(self).nbits == len,
    {
        self.nbits = len;
    }

    /// Origin Rust: impl<B: BitBlock> Clone for BitVec<B> fn clone(&self)
    ///     (lib.rs:2093-2099) { self.ensure_invariant();
    ///       BitVec { storage: self.storage.clone(), nbits: self.nbits } }
    /// (ensure_invariant is the cfg(test) no-op tier; Vec::clone
    /// carries its vstd spec -- the probe D reading -- so the entries
    /// view transfers and the bit-at tier is pointwise identical.)
    pub exec fn clone_exec(&self) -> (r: BitVec)
        requires
            inv(self),
        ensures
            inv(&r),
            r.storage@ == self.storage@,
            r.nbits == self.nbits,
    {
        BitVec { storage: self.storage.clone(), nbits: self.nbits }
    }

    /// Origin Rust: fn clone_from(&mut self, source: &Self)
    ///     (lib.rs:2101-2106) { debug_assert!(source.is_last_block_fixed());
    ///       self.nbits = source.nbits;
    ///       self.storage.clone_from(&source.storage); }
    /// (the debug_assert tier is inv(source); Vec::clone_from has no
    /// vstd spec -- transcribed as the overwrite with the clone, which
    /// is the documented semantics of clone_from.)
    pub exec fn clone_from_exec(&mut self, source: &BitVec)
        requires
            inv(self),
            inv(source),
        ensures
            inv(final(self)),
            final(self).storage@ == source.storage@,
            final(self).nbits == source.nbits,
        {
            self.nbits = source.nbits;
            self.storage = source.storage.clone();
        }

    /// Origin Rust: impl<B: BitBlock> cmp::PartialEq fn eq(&self, other)
    ///     (lib.rs:2177-2184) { if self.nbits != other.nbits {
    ///       self.ensure_invariant(); other.ensure_invariant();
    ///       return false; }
    ///       self.blocks().zip(other.blocks()).all(|(w1, w2)| w1 == w2) }
    /// (the blocks zip-all is the storage pairwise walk; under inv and
    /// equal nbits both storage lengths coincide, so the zip never
    /// truncates. The value tier carries the full iff; the bit tier is
    /// stated in the direction the contract gives for free -- value
    /// equality implies per-bit equality.)
    pub exec fn eq_exec(&self, other: &BitVec) -> (r: bool)
        requires
            inv(self),
            inv(other),
        ensures
            r == (self.nbits == other.nbits
                && (forall|w2: usize| w2 < self.storage@.len()
                    ==> #[trigger] self.storage@[w2 as int]
                        == other.storage@[w2 as int])),
            r ==> (self.nbits == other.nbits
                && (forall|j: usize| j < self.nbits
                    ==> bit_at(self.storage@, self.nbits, j)
                        == bit_at(other.storage@, other.nbits, j))),
        {
        if self.nbits != other.nbits {
            false
        } else {
            proof {
                assert(blocks_for_bits(self.nbits) == blocks_for_bits(other.nbits));
                assert(self.storage@.len() == other.storage@.len());
            }
            let len = self.storage.len();
            let mut w2: usize = 0;
            let mut res = true;
            while w2 < len
                invariant
                    w2 <= len,
                    len == self.storage@.len(),
                    len == other.storage@.len(),
                    res == (forall|k: usize| k < w2
                        ==> self.storage@[k as int] == other.storage@[k as int]),
                decreases len - w2,
            {
                let a = self.storage[w2];
                let b = other.storage[w2];
                if a != b {
                    assert(self.storage@[w2 as int] != other.storage@[w2 as int]);
                    res = false;
                } else {
                    assert(self.storage@[w2 as int] == other.storage@[w2 as int]);
                }
                w2 = w2 + 1;
            }
            res
        }
    }

    /// Origin Rust: impl<B: BitBlock> Ord fn cmp(&self, other: &Self)
    ///     (lib.rs:2118-2134) { self.ensure_invariant();
    ///       debug_assert!(other.is_last_block_fixed());
    ///       let mut a = self.iter(); let mut b = other.iter();
    ///       loop { match (a.next(), b.next()) { ... } } }
    /// (the double-iterator match pairs are the position walk over both
    /// bit vectors -- the first differing position decides, else the
    /// lengths decide; the exec tier is the decided-flag/witness scan,
    /// eq_vec's widx precedent. the debug_assert tier is inv(other).)
    pub exec fn cmp_exec(&self, other: &BitVec) -> (r: BvOrd)
        requires
            inv(self),
            inv(other),
        ensures
            ord_code(r) == spec_bv_cmp(self, other),
        {
            let mut i: usize = 0;
            let mut decided: bool = false;
            let mut dx: bool = false;
            let mut dy: bool = false;
            let ghost mut widx: int = -1int;
            while i < self.nbits && i < other.nbits
                invariant
                    i <= self.nbits,
                    i <= other.nbits,
                    decided == (widx >= 0),
                    widx >= 0 ==> widx < i as int,
                    decided ==> (dx != dy
                        && lex_bit(self.storage@, widx) == dx
                        && lex_bit(other.storage@, widx) == dy
                        && forall|k: int| 0 <= k < widx
                            ==> lex_bit(self.storage@, k) == lex_bit(other.storage@, k)),
                    !decided ==> forall|k: int| 0 <= k < i as int
                        ==> lex_bit(self.storage@, k) == lex_bit(other.storage@, k),
                decreases if self.nbits < other.nbits {
                    self.nbits - i
                } else {
                    other.nbits - i
                },
            {
                let g = self.get(i);
                let h = other.get(i);
                let gv = g.unwrap();
                let hv = h.unwrap();
                proof {
                    assert(bit_at(self.storage@, self.nbits, i) == gv);
                    assert(bit_at(other.storage@, other.nbits, i) == hv);
                    assert(gv == lex_bit(self.storage@, i as int));
                    assert(hv == lex_bit(other.storage@, i as int));
                }
                if gv != hv && !decided {
                    decided = true;
                    dx = gv;
                    dy = hv;
                    proof {
                        widx = i as int;
                        assert forall|k: int| 0 <= k < widx implies
                            lex_bit(self.storage@, k) == lex_bit(other.storage@, k) by { }
                    }
                }
                i = i + 1;
            }
            let mut r: BvOrd = BvOrd::Equal;
            proof {
                let la = self.nbits as int;
                let lb = other.nbits as int;
                if widx >= 0int {
                    assert(lex_bit(self.storage@, widx) == dx);
                    assert(lex_bit(other.storage@, widx) == dy);
                    lemma_cmp_first_diff(self.storage@, other.storage@, la, lb, widx);
                } else {
                    lemma_cmp_equal_tail(self.storage@, other.storage@, la, lb, i as int);
                    lemma_cmp_frame(self.storage@, other.storage@, la, lb, 0int, i as int);
                }
            }
            if decided {
                if dy {
                    r = BvOrd::Less;
                } else {
                    r = BvOrd::Greater;
                }
            } else {
                if self.nbits < other.nbits {
                    r = BvOrd::Less;
                } else if self.nbits > other.nbits {
                    r = BvOrd::Greater;
                }
            }
            r
        }

    /// Origin Rust: impl<B: BitBlock> PartialOrd fn partial_cmp(&self, other)
    ///     (lib.rs:2111-2113) { Some(self.cmp(other)) }
    /// (BitVecs are always comparable -- the Option is never None.)
    pub exec fn partial_cmp_exec(&self, other: &BitVec) -> (r: Option<BvOrd>)
        requires
            inv(self),
            inv(other),
        ensures
            r.is_Some(),
            r matches Some(o) ==> ord_code(o) == spec_bv_cmp(self, other),
        {
            Some(self.cmp_exec(other))
        }

    /// Origin Rust: impl<B: BitBlock> fmt::Display fn fmt(&self, fmt)
    ///     (lib.rs:2138-2144) { self.ensure_invariant();
    ///       for bit in self { fmt.write_char(if bit { '1' } else { '0' })?; }
    ///       Ok(()) }
    /// (the Formatter face is materialized as the emitted char stream --
    /// the observable write_char call sequence, in iteration order.)
    pub exec fn display_chars(&self) -> (r: Vec<char>)
        requires
            inv(self),
        ensures
            r@.len() == self.nbits,
            forall|j: usize|
                j < self.nbits
                    ==> r@[j as int] == bit_char(bit_at(self.storage@, self.nbits, j)),
        {
            let mut out: Vec<char> = Vec::new();
            let mut i: usize = 0;
            while i < self.nbits
                invariant
                    out@.len() == i,
                    i <= self.nbits,
                    forall|k: usize| k < i
                        ==> out@[k as int]
                            == bit_char(bit_at(self.storage@, self.nbits, k)),
                decreases self.nbits - i,
            {
                let w = i / 32;
                let b = i % 32;
                proof {
                    int_div_bound_lemma(i, self.nbits);
                }
                let block = self.storage[w];
                let bit = (block & (1u32 << b)) != 0u32;
                let ch = if bit { '1' } else { '0' };
                proof {
                    assert(ch == bit_char(bit));
                    assert(bit == bit_at(self.storage@, self.nbits, i));
                }
                out.push(ch);
                i = i + 1;
            }
            out
        }

    /// Origin Rust: impl<B: BitBlock> hash::Hash fn hash(&self, state)
    ///     (lib.rs:2166-2172) { self.ensure_invariant();
    ///       self.nbits.hash(state);
    ///       for elem in self.blocks() { elem.hash(state); } }
    /// (the Hasher trait face is materialized as the Hash::hash input
    /// feed: nbits first, then every storage block in order -- the
    /// delegation that makes equal vectors hash to equal states.)
    pub exec fn hash_feed_exec(&self) -> (r: Vec<u64>)
        requires
            inv(self),
        ensures
            r@ == hash_feed(self),
            r@.len() == 1 + self.storage@.len(),
        {
            let mut out: Vec<u64> = Vec::new();
            out.push(self.nbits as u64);
            let len = self.storage.len();
            let mut w: usize = 0;
            while w < len
                invariant
                    w <= len,
                    len == self.storage@.len(),
                    out@ == hash_feed_upto(self, w),
                    out@.len() == 1 + w,
                decreases len - w,
            {
                let blk = self.storage[w];
                proof {
                    let w1: usize = (w + 1) as usize;
                    lemma_hash_feed_upto_step(self, w, w1);
                }
                out.push(blk as u64);
                w = w + 1;
            }
            proof {
                assert(out@ == hash_feed_upto(self, len));
                assert(hash_feed_upto(self, len) == hash_feed(self)) by {
                    assert forall|k: int| 0 <= k < (1 + self.storage@.len()) implies
                        hash_feed_upto(self, len)[k] == hash_feed(self)[k] by { }
                }
                assert(out@ == hash_feed(self));
            }
            out
        }

    /// Origin Rust: impl<B: BitBlock> Extend<bool> fn extend(&mut self, iterable)
    ///     (lib.rs:2080-2088) { self.ensure_invariant();
    ///       let iterator = iterable.into_iter();
    ///       let (min, _) = iterator.size_hint();
    ///       self.reserve(min);
    ///       for element in iterator { self.push(element) } }
    /// (IntoIterator materialized as the &[bool] iterator form, the
    /// eq_vec precedent: the size_hint lower bound is exactly the item
    /// count, and every item is one bit, so reserve(min) is reserve of
    /// the bit count. The push loop is the index walk.)
    pub exec fn extend_bools(&mut self, v: &[bool])
        requires
            inv(old(self)),
            (old(self).nbits as int + v.len() as int) < usize::MAX as int,
            32 * (old(self).storage@.len()) <= usize::MAX as int,
        ensures
            inv(final(self)),
            final(self).nbits == old(self).nbits + v.len(),
            forall|j: usize|
                j < old(self).nbits ==>
                    bit_at(final(self).storage@, final(self).nbits, j)
                        == bit_at(old(self).storage@, old(self).nbits, j),
            forall|k: usize|
                k < v.len() ==>
                    bit_at(final(self).storage@, final(self).nbits,
                        (old(self).nbits + k) as usize) == v@[k as int],
    {
        self.reserve(v.len());
        let mut k: usize = 0;
        while k < v.len()
            invariant
                inv(self),
                self.nbits == old(self).nbits + k,
                k <= v.len(),
                (self.nbits as int) < usize::MAX as int,
                forall|j: usize|
                    j < old(self).nbits ==>
                        bit_at(self.storage@, self.nbits, j)
                            == bit_at(old(self).storage@, old(self).nbits, j),
                forall|t: usize|
                    t < k ==>
                        bit_at(self.storage@, self.nbits, (old(self).nbits + t) as usize)
                            == v@[t as int],
            decreases v.len() - k,
        {
            self.push(v[k]);
            k = k + 1;
        }
    }

    /// Origin Rust: impl<B: BitBlock> FromIterator<bool> fn from_iter
    ///     (lib.rs:2071-2075) { let mut ret = Default::default();
    ///       ret.extend(iter); ret }
    /// (the Default seed is the verified bv_default; the pass-through
    /// extend carries its precondition family.)
    pub exec fn from_iter_bools(v: &[bool]) -> (bv: BitVec)
        requires
            (v.len() as int) < (usize::MAX as int),
        ensures
            inv(&bv),
            bv.nbits == v.len(),
            forall|k: usize|
                k < v.len() ==> bit_at(bv.storage@, bv.nbits, k) == v@[k as int],
    {
        let mut ret = bv_default();
        proof {
            assert((0usize as int) + (v.len() as int) < (usize::MAX as int));
            assert(32 * (0usize as int) <= (usize::MAX as int));
        }
        ret.extend_bools(v);
        ret
    }
}

/// the Display char family: '1' for a set bit, '0' otherwise.
pub open spec fn bit_char(b: bool) -> char {
    if b { '1' } else { '0' }
}

/// the Hash feed: nbits first, then every storage block, one u64 slot
/// per Hash::hash input value.
pub open spec fn hash_feed(bv: &BitVec) -> Seq<u64> {
    Seq::new((1 + bv.storage@.len()) as nat, |i: int|
        if i == 0 {
            bv.nbits as u64
        } else {
            bv.storage@[i - 1] as u64
        })
}

/// the partial feed up to storage block w (the out loop's frame).
pub open spec fn hash_feed_upto(bv: &BitVec, w: usize) -> Seq<u64> {
    Seq::new((1 + w) as nat, |i: int|
        if i == 0 {
            bv.nbits as u64
        } else {
            bv.storage@[i - 1] as u64
        })
}

pub proof fn lemma_hash_feed_upto_step(bv: &BitVec, w: usize, w1: usize)
    requires
        w < bv.storage@.len(),
        w1 == w + 1,
    ensures
        hash_feed_upto(bv, w1) == hash_feed_upto(bv, w).push(bv.storage@[w as int] as u64),
{
    let s = hash_feed_upto(bv, w);
    let t = s.push(bv.storage@[w as int] as u64);
    assert(hash_feed_upto(bv, w1).len() == 1 + (w as int) + 1);
    assert(t.len() == 1 + (w as int) + 1);
    assert forall|i: int| 0 <= i < (1 + (w as int) + 1) implies
        t[i] == hash_feed_upto(bv, w1)[i] by { }
    lemma_seq_ext_equal(t, hash_feed_upto(bv, w1));
}

} // verus!


// Verification driver (single-file driver form; the harness zone never
// duplicates this file's content).
fn main() {}
