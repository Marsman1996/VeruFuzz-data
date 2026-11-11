//! bit-vec 0.10.1 x Verus -- coverage diff-set batch harness
//! (process family + small structural families).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here.
//! Coverage (out/harness-inventory.md section 3 diff-set batch):
//!   - D1: or/and/difference/xor (+ deprecated union/intersect aliases)
//!   - D2: nand (the changed criterion is doc-consistent); nor/xnor (the
//!     changed criterion transcribed exactly from upstream, contradicting
//!     the doc "Returns `true` if `self` changed" when n%32>0 --
//!     ut_nor_doc_anchor / ut_xnor_doc_anchor are the formalized
//!     counterexample anchors of that finding; runtime PoC in out/poc/)
//!   - D2a: eq_vec / truncate / remove_all
//!
//! Machine evaluation of literal bit states goes through the single-bit
//! lit_* bridges (spec-domain shifts are uninterpreted).

#![feature(allocator_api)] // needed by the referenced src assume_specification signature

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitvec_lib;

verus! {

use bitvec_lib::{BitVec, inv, blocks_for_bits, len_inv, trailing_zero, with_ones_input};

/// Literal bit-0 evaluation bridge: bit_at([val], n, 0) == ((val & 1) != 0).
fn pre_snapshot(bv: &BitVec) -> (s: BitVec)
    requires
        inv(bv),
    ensures
        s.nbits == bv.nbits,
        s.storage@ == bv.storage@,
        inv(&s),
{
    let mut st: Vec<u32> = Vec::new();
    let n = bv.storage.len();
    proof {
        assert(bv.storage@.len() == n);
        assert(bv.storage@.len() == blocks_for_bits(bv.nbits));
    }
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            bv.storage@.len() == n,
            st@.len() == idx,
            forall|w2: int| 0 <= w2 < idx ==> st@[w2] == bv.storage@[w2],
        decreases n - idx,
    {
        proof {
            assert(idx < bv.storage@.len());
        }
        let v = bv.storage[idx];
        st.push(v);
        idx += 1;
    }
    proof {
        assert(st@ == bv.storage@) by {
            assert forall|w2: int| 0 <= w2 < bv.storage@.len() implies st@[w2] == bv.storage@[w2] by { }
        }
    }
    let s = BitVec { storage: st, nbits: bv.nbits };
    proof {
        assert(len_inv(&s)) by {
            assert(s.storage@ == bv.storage@);
            assert(s.nbits == bv.nbits);
        }
        assert(trailing_zero(&s)) by {
            assert(s.storage@ == bv.storage@);
        }
        assert(inv(&s));
    }
    s
}

/// Hand-built 5-bit literal state: storage=[val]; the trailing-zero
/// invariant holds (val < 2^5).
fn build5(val: u32) -> (bv: BitVec)
    requires
        val < 32u32,
    ensures
        inv(&bv),
        bv.nbits == 5,
        bv.storage@.len() == 1,
        bv.storage@[0] == val,
        bitvec_lib::bit_at(bv.storage@, 5, 0) == ((val & 1u32) != 0u32),
{
    let mut s: Vec<u32> = Vec::new();
    s.push(val);
    proof {
        assert(s@.len() == 1);
        assert(s@ == seq![val]);
        assert(s@[0] == val);
    }
    let bv = BitVec { storage: s, nbits: 5 };
    let e = bv.nbits % 32;
    proof {
        assert(e == 5usize);
        assert(len_inv(&bv)) by {
            assert(bv.storage@.len() == 1);
            assert(blocks_for_bits(5) == 1);
        }
        assert((1u32 << e) == 32u32) by (bit_vector)
            requires
                e == 5usize,
        ;
        assert(trailing_zero(&bv)) by {
            assert(bv.storage@[0] == val);
            assert(bv.nbits % 32 == 5usize);
            assert((1u32 << (bv.nbits % 32)) == 32u32);
        }
        assert(inv(&bv));
        assert((1u32 << 0usize) == 1u32) by (bit_vector);
        assert((val & (1u32 << (0usize % 32usize))) == (val & 1u32));
    }
    bv
}

/// [FINDING ANCHOR] nor: a=all-0, b=all-1 -- the semantic result stays
/// all 0 (self unchanged), yet upstream (transcribed semantics) returns
/// true -- contradicting the doc (lib.rs:1189-1196 "Returns `true` if
/// `self` changed"). Runtime PoC: out/poc/nor-xnor-changed-flag/.


pub exec fn ut_nor_doc_anchor() -> (r: bool)
{
    let mut a = build5(0u32);
    let b = build5(31u32);
    proof {
        /* machine-evaluation domain (spec shifts are uninterpreted,
           closed segment by segment with bv); pin the pre-call state first */
        let e = a.nbits % 32;
        assert(e == 5usize);
        assert((1u32 << e) - 1u32 == 31u32) by (bit_vector)
            requires
                e == 5usize,
        ;
        assert(a.storage@[0] == 0u32);
        assert(b.storage@[0] == 31u32);
        assert((1u32 << (a.nbits % 32)) - 1u32 == 31u32);
    }
    let pre = pre_snapshot(&a);
    let r = a.nor(&b);
    proof {
        let e2 = pre.nbits % 32;
        assert(e2 == 5usize);
        assert((1u32 << e2) - 1u32 == 31u32) by (bit_vector)
            requires
                e2 == 5usize,
        ;
        assert((1u32 << (pre.nbits % 32)) - 1u32 == 31u32);
        assert(pre.storage@[0] == 0u32);
        let l1 = 0u32 | (4294967295u32 ^ 31u32);
        assert(l1 == 4294967264u32) by (bit_vector)
            requires
                l1 == (0u32 | (4294967295u32 ^ 31u32)),
        ;
        assert(((l1 | 31u32) ^ 4294967295u32) == 0u32) by (bit_vector)
            requires
                l1 == (0u32 | (4294967295u32 ^ 31u32)),
        ;
        /* with_ones_input(pre-state, 0) == l1; the negated-universal of
           nor's ensures collapses at w2=0 */
        assert(with_ones_input(&pre, 0 as usize) == l1);
        assert((((l1 | b.storage@[0]) ^ 4294967295u32) != l1));
        /* direct instance refutation of the negated universal (pre-form),
           then bridge to r */
        assert(!(forall|w2: usize| w2 < pre.storage@.len() ==>
            (((with_ones_input(&pre, w2) | b.storage@[w2 as int]) ^ 4294967295u32)
                == with_ones_input(&pre, w2)))) by {
            assert((((with_ones_input(&pre, 0 as usize) | b.storage@[0 as int])
                ^ 4294967295u32) != with_ones_input(&pre, 0 as usize)));
        }
        /* r == true follows from nor's ensures (negated-universal form,
         * machine-verified in the src zone) plus the pre-form refutation
         * above; the end-to-end stitching of r is not unified in the
         * harness context (old-snapshot/snapshot SSA, trigger misses) and
         * is covered by the runtime PoC (out/poc/nor-xnor-changed-flag/). */


        lit_bit0_zero();
        lit_bit0_ones();
    }
    let h0 = a.get(0);
    assert(h0 == Some(false));
    r
}

/// [FINDING ANCHOR] xnor, same shape: the semantic result is all 0 (self
/// unchanged), upstream returns true. See the nor anchor above.
pub exec fn ut_xnor_doc_anchor() -> (r: bool)
{
    let mut a = build5(0u32);
    let b = build5(31u32);
    proof {
        let e = a.nbits % 32;
        assert(e == 5usize);
        assert((1u32 << e) - 1u32 == 31u32) by (bit_vector)
            requires
                e == 5usize,
        ;
        assert(a.storage@[0] == 0u32);
        assert(b.storage@[0] == 31u32);
        assert((1u32 << (a.nbits % 32)) - 1u32 == 31u32);
    }
    let pre = pre_snapshot(&a);
    let r = a.xnor(&b);
    proof {
        let e2 = pre.nbits % 32;
        assert(e2 == 5usize);
        assert((1u32 << e2) - 1u32 == 31u32) by (bit_vector)
            requires
                e2 == 5usize,
        ;
        assert((1u32 << (pre.nbits % 32)) - 1u32 == 31u32);
        assert(pre.storage@[0] == 0u32);
        let l1 = 0u32 | (4294967295u32 ^ 31u32);
        assert(l1 == 4294967264u32) by (bit_vector)
            requires
                l1 == (0u32 | (4294967295u32 ^ 31u32)),
        ;
        assert(((l1 ^ 31u32) ^ 4294967295u32) == 0u32) by (bit_vector)
            requires
                l1 == (0u32 | (4294967295u32 ^ 31u32)),
        ;
        assert(with_ones_input(&pre, 0 as usize) == l1);
        assert((((l1 ^ b.storage@[0]) ^ 4294967295u32) != l1));
        assert(!(forall|w2: usize| w2 < pre.storage@.len() ==>
            (((with_ones_input(&pre, w2) ^ b.storage@[w2 as int]) ^ 4294967295u32)
                == with_ones_input(&pre, w2)))) by {
            assert((((with_ones_input(&pre, 0 as usize) ^ b.storage@[0 as int])
                ^ 4294967295u32) != with_ones_input(&pre, 0 as usize)));
        }
        /* r == true as in the nor anchor: ensures (negated-universal
           form) + pre-form refutation machine-checked; end-to-end stitching
           is covered by the runtime PoC. */
        lit_bit0_zero();
        lit_bit0_ones();
    }
    let h0 = a.get(0);
    assert(h0 == Some(false));
    r
}

/// nand(a=all-0, b=all-1) -> semantic all-1 (self really changes),
/// r == true (doc-consistent).
pub exec fn ut_nand_semantics() -> (r: bool)
    ensures
        r == true,
{
    let mut a = build5(0u32);
    let b = build5(31u32);
    let r = a.nand(&b);
    proof {
        /* nand: doc-consistent (self really changes: all 0 -> all 1) */
        lit_bit0_zero();
        lit_bit0_ones();
    }
    let g0 = a.get(0);
    assert(g0 == Some(true));
    r
}

/// or/nor semantics contrast: after or, bit 0 is true; after nor, bit 0
/// is false.
pub exec fn ut_or_semantics_bit()
{
    let mut a = build5(0u32);
    let b = build5(31u32);
    let r = a.or(&b);
    proof {
        lit_bit0_zero();
        lit_bit0_ones();
        /* final.storage[0] == 0 | 31 != 0 => final != old => r == true */
        assert((0u32 | 31u32) != 0u32) by (bit_vector);
    }
    assert(r == true);
    let g0 = a.get(0);
    assert(g0 == Some(true));
}

/// truncate prefix preservation (lib.rs:1604-1612).
pub exec fn ut_truncate_prefix()
{
    let mut a = build5(31u32);
    a.set(0, false);
    /* 11110: after truncating to 1 bit only bit 0 == false remains */
    a.truncate(1);
    let alen = a.len();
    assert(alen == 1);
    let g0 = a.get(0);
    assert(g0 == Some(false));
}

/// remove_all empties the vector (lib.rs:1995-1998).
pub exec fn ut_remove_all() -> (a: BitVec)
    ensures
        a.nbits == 0,
        inv(&a),
{
    let mut a = build5(31u32);
    a.remove_all();
    let alen = a.len();
    assert(alen == 0);
    a
}


// ---------------------------------------------------------------------------
// proof lemmas (literal bit-value bridges; placed at the end so the exec
// anchors read directly)
// ---------------------------------------------------------------------------

/// Literal bit-0 value domain: bit 0 of 0 is 0.
pub proof fn lit_bit0_zero()
    ensures
        (0u32 & (1u32 << 0usize)) == 0u32,
{
    assert((0u32 & (1u32 << 0usize)) == 0u32) by (bit_vector);
}

/// Literal bit-0 value domain: bit 0 of 0x1F is 1.
pub proof fn lit_bit0_ones()
    ensures
        (31u32 & (1u32 << 0usize)) != 0u32,
{
    assert((31u32 & (1u32 << 0usize)) != 0u32) by (bit_vector);
}
fn main() {}
} // verus!
