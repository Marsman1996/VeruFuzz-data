
#![verifier::loop_isolation(false)]
use vstd::prelude::*;
use vstd::seq::lemma_seq_ext_equal;

verus! {

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
} // verus!


// Verification driver (single-file driver form; the harness zone never
// duplicates this file's content).
fn main() {}
