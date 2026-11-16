//! bit-set 0.11.1 x Verus -- UT harness, batch H2 (set_iter).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here, except small harness-local
//! bit-level bridge lemmas (the fixed-position pattern of batch H1).
//!
//! Coverage (upstream set/tests/set.rs, batch H2 -- the collect-family
//! UTs ride the batch-H2 exhaustion/yield contract of src/iter.rs:
//! each UT drives the cursor step by step, pins every yielded element
//! to the upstream expected list position by position, and closes on
//! the exhaustion step):
//!   test_bit_set_intersection / test_bit_set_difference /
//!   test_bit_set_symmetric_difference / test_bit_set_union /
//!   test_bit_set_iterator (the small-set half; the 10000-element half
//!   is a scale face, recorded as a batch note, not re-proven here)

#![feature(allocator_api)] // needed by the referenced src assume_specification signature
#![verifier::timeout(240)] // the crate-root timeout face (moved from src/lib.rs)

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitset_lib;

verus! {

use bitset_lib::set::{BitSet, bs_at, bs_inv};
use bitset_lib::bitvec_lib::{BitVec, bit_at, blocks_for_bits, int_div_bound_lemma, inv,
    lemma_pow_lt_bit};
use bitset_lib::iter::{BiExec, bi_at, bi_inv, bi_nb, bi_word, kind_merged, side_word_seq};

// ---------------------------------------------------------------------------
// harness-local bit bridges (the H1 fixed-position kit, extended to the
// padded side words of the iterator streams)
// ---------------------------------------------------------------------------

/// the trailing-clip face of a padded stream: the side word's bit at p
/// reads exactly the set's membership bit, with the tail block's unused
/// positions clipped to zero and past-storage indices padded to zero.
pub proof fn lemma_side_word_bit(st: Seq<u32>, nb: usize, p: usize)
    requires
        st.len() == blocks_for_bits(nb),
        nb % 32 == 0
            || st[(blocks_for_bits(nb) - 1) as int] < (1u32 << (nb % 32)),
        nb <= 4294967232usize,
    ensures
        ((side_word_seq(st, (p / 32) as usize) & (1u32 << (p % 32))) != 0u32)
            == (p < nb && bit_at(st, nb, p)),
{
    let i2: usize = (p / 32) as usize;
    let m2: u32 = 1u32 << (p % 32);
    if p < nb {
        // inside the universe: the padded word is the own block
        int_div_bound_lemma(p, nb);
        assert((i2 as int) < st.len());
        assert(((st.len() as int) - 1int) * 32 < (nb as int));
        assert((i2 as int) < (blocks_for_bits(nb) as int));
        assert((i2 as int) < (st.len() as int));
        assert(st.len() == blocks_for_bits(nb));
        assert(side_word_seq(st, i2) == st[i2 as int]);
        assert((st[i2 as int] & m2) != 0u32 == bit_at(st, nb, p));
    } else {
        if (i2 as int) >= st.len() {
            // past the storage: zero padding
            assert(side_word_seq(st, i2) == 0u32);
            assert((0u32 & m2) == 0u32) by (bit_vector);
        } else {
            // inside the tail block: the trailing clip clears the bit
            assert(nb % 32 > 0) by {
                if nb % 32 == 0 {
                    assert(st.len() == ((nb as int) / 32) as usize);
                    assert((i2 as int) < (nb as int) / 32);
                    assert((p as int) < nb as int);
                    assert(false);
                }
            }
            let e2 = nb % 32;
            assert((i2 as int) == (st.len() as int) - 1int) by {
                assert((p as int) >= (nb as int));
                assert((i2 as int) < (st.len() as int));
                assert((st.len() as int) == ((nb as int) / 32) + 1int);
                assert(((nb as int) / 32) * 32 <= (nb as int));
                assert((p as int) / 32 >= (nb as int) / 32);
                assert((i2 as int) >= (nb as int) / 32);
                assert((i2 as int) >= (st.len() as int) - 1int);
            }
            let wl: u32 = st[i2 as int];
            assert(wl < (1u32 << (e2 as u32)));
            // the position sits at-or-above the tail width in this block
            assert((e2 as int) <= (p % 32) as int) by {
                assert((p as int) < ((i2 as int) + 1int) * 32);
                assert((p as int) >= (nb as int));
                assert((nb as int) == 32 * (i2 as int) + (e2 as int));
            }
            assert((p % 32) < 32);
            assert((e2 as int) < 32int);
            lemma_pow_lt_bit(wl, e2 % 32, (p % 32) as usize);
            assert((wl & m2) == 0u32);
            assert(side_word_seq(st, i2) == wl);
        }
    }
}

/// the merged stream bit at one position: the monomorphized word op
/// reads the same bit on both side words (the per-kind fixed-position
/// face; parameters are values so callers instantiate it directly).
pub proof fn lemma_kind_merged_bit(kind: u8, wa: u32, wb: u32, tt: usize)
    requires
        kind <= 4u8,
        tt < 32usize,
    ensures
        ((kind_merged(kind, wa, wb) & (1u32 << tt)) != 0u32)
            == (if kind == 0u8 {
                ((wa & (1u32 << tt)) != 0u32) || ((wb & (1u32 << tt)) != 0u32)
            } else if kind == 1u8 {
                ((wa & (1u32 << tt)) != 0u32) && ((wb & (1u32 << tt)) != 0u32)
            } else if kind == 2u8 {
                ((wa & (1u32 << tt)) != 0u32) && ((wb & (1u32 << tt)) == 0u32)
            } else if kind == 3u8 {
                (((wa & (1u32 << tt)) != 0u32) != ((wb & (1u32 << tt)) != 0u32))
            } else {
                ((wa & (1u32 << tt)) != 0u32)
            }),
{
    if kind == 0u8 {
        let mg: u32 = wa | wb;
        assert(kind_merged(kind, wa, wb) == mg);
        assert((mg & (1u32 << tt)) != 0u32
            == (((wa & (1u32 << tt)) != 0u32) || ((wb & (1u32 << tt)) != 0u32))) by (bit_vector)
            requires tt < 32usize && mg == wa | wb;
    } else if kind == 1u8 {
        let mg: u32 = wa & wb;
        assert(kind_merged(kind, wa, wb) == mg);
        assert((mg & (1u32 << tt)) != 0u32
            == (((wa & (1u32 << tt)) != 0u32) && ((wb & (1u32 << tt)) != 0u32))) by (bit_vector)
            requires tt < 32usize && mg == wa & wb;
    } else if kind == 2u8 {
        let mg: u32 = wa & (4294967295u32 ^ wb);
        assert(kind_merged(kind, wa, wb) == mg);
        assert((mg & (1u32 << tt)) != 0u32
            == (((wa & (1u32 << tt)) != 0u32) && ((wb & (1u32 << tt)) == 0u32))) by (bit_vector)
            requires tt < 32usize && mg == wa & (4294967295u32 ^ wb);
    } else if kind == 3u8 {
        let mg: u32 = wa ^ wb;
        assert(kind_merged(kind, wa, wb) == mg);
        assert((mg & (1u32 << tt)) != 0u32
            == (((wa & (1u32 << tt)) != 0u32) != ((wb & (1u32 << tt)) != 0u32))) by (bit_vector)
            requires tt < 32usize && mg == wa ^ wb;
    } else {
        assert(kind_merged(kind, wa, wb) == wa);
        assert((wa & (1u32 << tt)) != 0u32 == ((wa & (1u32 << tt)) != 0u32));
    }
}

/// the cursor element face as a membership statement over the two
/// underlying sets: rounds the side-word bridge and the merged-bit
/// bridge into one membership formula (the driver-facing pin).
pub proof fn lemma_bi_at_membership(
    kind: u8, sa_seq: Seq<u32>, sb_seq: Seq<u32>, na: usize, nb2: usize, p: usize,
)
    requires
        kind <= 4u8,
        kind == 4u8 ==> sb_seq == sa_seq,
        kind == 4u8 ==> nb2 == na,
        sa_seq.len() == blocks_for_bits(na),
        na % 32 == 0
            || sa_seq[(blocks_for_bits(na) - 1) as int] < (1u32 << (na % 32)),
        kind == 4u8
            || (sb_seq.len() == blocks_for_bits(nb2)
                && (nb2 % 32 == 0
                    || sb_seq[(blocks_for_bits(nb2) - 1) as int]
                        < (1u32 << (nb2 % 32)))),
        na <= 4294967232usize,
        nb2 <= 4294967232usize,
    ensures
        ((kind_merged(kind, side_word_seq(sa_seq, (p / 32) as usize),
            side_word_seq(sb_seq, (p / 32) as usize)) & (1u32 << (p % 32))) != 0u32)
            == (if kind == 0u8 {
                (p < na && bit_at(sa_seq, na, p))
                    || (p < nb2 && bit_at(sb_seq, nb2, p))
            } else if kind == 1u8 {
                (p < na && bit_at(sa_seq, na, p))
                    && (p < nb2 && bit_at(sb_seq, nb2, p))
            } else if kind == 2u8 {
                (p < na && bit_at(sa_seq, na, p))
                    && !(p < nb2 && bit_at(sb_seq, nb2, p))
            } else if kind == 3u8 {
                ((p < na && bit_at(sa_seq, na, p))
                    != (p < nb2 && bit_at(sb_seq, nb2, p)))
            } else {
                (p < na && bit_at(sa_seq, na, p))
            }),
{
    let i2: usize = (p / 32) as usize;
    lemma_side_word_bit(sa_seq, na, p);
    if kind != 4u8 {
        lemma_side_word_bit(sb_seq, nb2, p);
    } else {
        lemma_side_word_bit(sb_seq, na, p);
    }
    lemma_kind_merged_bit(kind, side_word_seq(sa_seq, i2), side_word_seq(sb_seq, i2),
        (p % 32) as usize);
}

// ---------------------------------------------------------------------------
// the per-position pin kit (the driver-facing specializations of the
// membership bridge; value parameters so every call instantiates at
// exactly one grounded position)
// ---------------------------------------------------------------------------

/// the intersection stream's element face at ee: the merged bit is the
/// pair of the two sides' bits.
pub proof fn lemma_pin_and(
    it: &BiExec, av: &BitVec, bv: &BitVec, ee: usize,
)
    requires
        bi_inv(it),
        it.kind == 1u8,
        it.nb_self == av.nbits,
        it.nb_other == bv.nbits,
        it.a.storage@ == av.storage@,
        it.b.storage@ == bv.storage@,
        inv(av),
        inv(bv),
        av.nbits <= 4294967232usize,
        bv.nbits <= 4294967232usize,
    ensures
        bi_at(it, ee)
            == (((ee < bi_nb(it))
                && bit_at(av.storage@, av.nbits, ee))
                && (ee < bv.nbits && bit_at(bv.storage@, bv.nbits, ee))),
{
    let sa: Seq<u32> = av.storage@;
    let sb: Seq<u32> = bv.storage@;
    let i2: usize = (ee / 32) as usize;
    assert(bi_word(&it, i2) == kind_merged(1u8, side_word_seq(sa, i2), side_word_seq(sb, i2)));
    lemma_bi_at_membership(1u8, sa, sb, av.nbits, bv.nbits, ee);
    assert(((bi_nb(&it) as int) == if av.nbits < bv.nbits {
        av.nbits as int
    } else {
        bv.nbits as int
    }));
}

/// the union stream's element face at ee: the merged bit is the
/// disjunction of the two sides' bits.
pub proof fn lemma_pin_or(
    it: &BiExec, av: &BitVec, bv: &BitVec, ee: usize,
)
    requires
        bi_inv(it),
        it.kind == 0u8,
        it.nb_self == av.nbits,
        it.nb_other == bv.nbits,
        it.a.storage@ == av.storage@,
        it.b.storage@ == bv.storage@,
        inv(av),
        inv(bv),
        av.nbits <= 4294967232usize,
        bv.nbits <= 4294967232usize,
    ensures
        bi_at(it, ee)
            == ((ee < bi_nb(it))
                && ((ee < av.nbits && bit_at(av.storage@, av.nbits, ee))
                    || (ee < bv.nbits && bit_at(bv.storage@, bv.nbits, ee)))),
{
    let sa: Seq<u32> = av.storage@;
    let sb: Seq<u32> = bv.storage@;
    let i2: usize = (ee / 32) as usize;
    assert(bi_word(&it, i2) == kind_merged(0u8, side_word_seq(sa, i2), side_word_seq(sb, i2)));
    lemma_bi_at_membership(0u8, sa, sb, av.nbits, bv.nbits, ee);
}

/// the difference stream's element face at ee: the merged bit is the
/// first side's bit with the second side's bit subtracted.
pub proof fn lemma_pin_andnot(
    it: &BiExec, av: &BitVec, bv: &BitVec, ee: usize,
)
    requires
        bi_inv(it),
        it.kind == 2u8,
        it.nb_self == av.nbits,
        it.nb_other == bv.nbits,
        it.a.storage@ == av.storage@,
        it.b.storage@ == bv.storage@,
        inv(av),
        inv(bv),
        av.nbits <= 4294967232usize,
        bv.nbits <= 4294967232usize,
    ensures
        bi_at(it, ee)
            == ((ee < bi_nb(it)
                && (ee < av.nbits && bit_at(av.storage@, av.nbits, ee)))
                && !(ee < bv.nbits && bit_at(bv.storage@, bv.nbits, ee))),
{
    let sa: Seq<u32> = av.storage@;
    let sb: Seq<u32> = bv.storage@;
    let i2: usize = (ee / 32) as usize;
    assert(bi_word(&it, i2) == kind_merged(2u8, side_word_seq(sa, i2), side_word_seq(sb, i2)));
    lemma_bi_at_membership(2u8, sa, sb, av.nbits, bv.nbits, ee);
}

/// the symmetric difference stream's element face at ee: the merged bit
/// is the exclusive disjunction of the two sides' bits.
pub proof fn lemma_pin_xor(
    it: &BiExec, av: &BitVec, bv: &BitVec, ee: usize,
)
    requires
        bi_inv(it),
        it.kind == 3u8,
        it.nb_self == av.nbits,
        it.nb_other == bv.nbits,
        it.a.storage@ == av.storage@,
        it.b.storage@ == bv.storage@,
        inv(av),
        inv(bv),
        av.nbits <= 4294967232usize,
        bv.nbits <= 4294967232usize,
    ensures
        bi_at(it, ee)
            == ((ee < bi_nb(it))
                && ((ee < av.nbits && bit_at(av.storage@, av.nbits, ee))
                    != (ee < bv.nbits
                        && bit_at(bv.storage@, bv.nbits, ee)))),
{
    let sa: Seq<u32> = av.storage@;
    let sb: Seq<u32> = bv.storage@;
    let i2: usize = (ee / 32) as usize;
    assert(bi_word(&it, i2) == kind_merged(3u8, side_word_seq(sa, i2), side_word_seq(sb, i2)));
    lemma_bi_at_membership(3u8, sa, sb, av.nbits, bv.nbits, ee);
}

/// the own stream's element face at ee: the merged bit is the single
/// side's bit.
pub proof fn lemma_pin_own(
    it: &BiExec, av: &BitVec, ee: usize,
)
    requires
        bi_inv(it),
        it.kind == 4u8,
        it.nb_self == av.nbits,
        it.a.storage@ == av.storage@,
        it.b.storage@ == av.storage@,
        inv(av),
        av.nbits <= 4294967232usize,
    ensures
        bi_at(it, ee)
            == ((ee < bi_nb(it)) && (ee < av.nbits
                && bit_at(av.storage@, av.nbits, ee))),
{
    let sa: Seq<u32> = av.storage@;
    let i2: usize = (ee / 32) as usize;
    assert(it.b.storage@ == av.storage@);
    assert(bi_word(&it, i2) == kind_merged(4u8, side_word_seq(sa, i2), side_word_seq(sa, i2)));
    lemma_bi_at_membership(4u8, sa, sa, av.nbits, av.nbits, ee);
}

// ---------------------------------------------------------------------------
// UT bodies (one exec fn per upstream #[test]; each step drive pins the
// yielded element to the upstream expected list, the exhaustion step
// returns None)
// ---------------------------------------------------------------------------

/// upstream test_bit_set_intersection (tests/set.rs:106-127):
/// the intersection of {1,3,5,11,77,103} with {2,3,5,11,77} collects
/// [3, 5, 11, 77].
pub exec fn ut_intersection() -> (r: u64)
    ensures
        r == 4u64,
{
    let mut a = BitSet::new();
    let r1 = a.insert(1);
    assert(r1 == true);
    let r2 = a.insert(3);
    assert(r2 == true);
    let r3 = a.insert(5);
    assert(r3 == true);
    let r4 = a.insert(11);
    assert(r4 == true);
    let r5 = a.insert(77);
    assert(r5 == true);
    let r6 = a.insert(103);
    assert(r6 == true);
    let mut b = BitSet::new();
    let s1 = b.insert(2);
    assert(s1 == true);
    let s2 = b.insert(3);
    assert(s2 == true);
    let s3 = b.insert(5);
    assert(s3 == true);
    let s4 = b.insert(11);
    assert(s4 == true);
    let s5 = b.insert(77);
    assert(s5 == true);
    proof {
        assert forall|i: usize| bs_at(&a, i)
            == (i == 1 || i == 3 || i == 5 || i == 11 || i == 77 || i == 103) by { }
        assert forall|i: usize| bs_at(&b, i)
            == (i == 2 || i == 3 || i == 5 || i == 11 || i == 77) by { }
    }
    let mut it = BiExec::bi_intersection(&a.bit_vec, &b.bit_vec);
    // step 1 yields 3: the pair member at 3 with no member below it
    proof {
        let sa_seq: Seq<u32> = a.bit_vec.storage@;
        let sb_seq: Seq<u32> = b.bit_vec.storage@;
        assert(it.kind == 1u8);
        assert(bi_nb(&it) == 78usize);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 3usize);
        assert(bs_at(&a, 3));
        assert(bs_at(&b, 3));
        assert(bi_at(&it, 3));
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 0usize);
        assert(!bs_at(&a, 0));
        assert(!bs_at(&b, 0));
        assert(bi_at(&it, 0) == false);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 1usize);
        assert(!bs_at(&b, 1));
        assert(bi_at(&it, 1) == false);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 2usize);
        assert(!bs_at(&a, 2));
        assert(bi_at(&it, 2) == false);
    }
    let y1 = it.bi_next();
    assert(y1 == Some(3));
    // step 2 yields 5: the pair member, with 4 clear between
    proof {
        let sa_seq: Seq<u32> = a.bit_vec.storage@;
        let sb_seq: Seq<u32> = b.bit_vec.storage@;
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 5usize);
        assert(bs_at(&a, 5));
        assert(bs_at(&b, 5));
        assert(bi_at(&it, 5));
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 4usize);
        assert(!bs_at(&a, 4));
        assert(!bs_at(&b, 4));
        assert(bi_at(&it, 4) == false);
    }
    let y2 = it.bi_next();
    assert(y2 == Some(5));
    // step 3 yields 11: the pair member, with 6..10 clear between
    proof {
        let sa_seq: Seq<u32> = a.bit_vec.storage@;
        let sb_seq: Seq<u32> = b.bit_vec.storage@;
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 11usize);
        assert(bs_at(&a, 11));
        assert(bs_at(&b, 11));
        assert(bi_at(&it, 11));
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 6usize);
        assert(!bs_at(&a, 6));
        assert(!bs_at(&b, 6));
        assert(bi_at(&it, 6) == false);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 7usize);
        assert(!bs_at(&a, 7));
        assert(!bs_at(&b, 7));
        assert(bi_at(&it, 7) == false);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 8usize);
        assert(!bs_at(&a, 8));
        assert(!bs_at(&b, 8));
        assert(bi_at(&it, 8) == false);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 9usize);
        assert(!bs_at(&a, 9));
        assert(!bs_at(&b, 9));
        assert(bi_at(&it, 9) == false);
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 10usize);
        assert(!bs_at(&a, 10));
        assert(!bs_at(&b, 10));
        assert(bi_at(&it, 10) == false);
    }
    let y3 = it.bi_next();
    assert(y3 == Some(11));
    // step 4 yields 77: the long middle gap 12..76 holds no pair member
    proof {
        let sa_seq: Seq<u32> = a.bit_vec.storage@;
        let sb_seq: Seq<u32> = b.bit_vec.storage@;
        lemma_pin_and(&it, &a.bit_vec, &b.bit_vec, 77usize);
        assert(bs_at(&a, 77));
        assert(bs_at(&b, 77));
        assert(bi_at(&it, 77));
        assert forall|p: usize| 12int <= (p as int) && (p as int) < 77int
            ==> bi_at(&it, p) == false by {
            let i2: usize = (p / 32) as usize;
            assert(bi_word(&it, i2)
                == kind_merged(1u8, side_word_seq(sa_seq, i2), side_word_seq(sb_seq, i2)));
            lemma_bi_at_membership(1u8, sa_seq, sb_seq, 104usize, 78usize, p);
            assert(bs_at(&a, p) == (p < 104usize
                && bit_at(sa_seq, 104usize, p)));
            assert(bs_at(&b, p) == (p < 78usize
                && bit_at(sb_seq, 78usize, p)));
        }
    }
    let y4 = it.bi_next();
    assert(y4 == Some(77));
    // step 5 is the exhaustion step: the universe edge at 78 caps the
    // stream, so nothing further can be a member
    let y5 = it.bi_next();
    assert(y5 == None);
    4u64
}

/// upstream test_bit_set_difference (tests/set.rs:130-147):
/// the difference of {1,3,5,200,500} minus {3,200} collects [1, 5, 500].
pub exec fn ut_difference() -> (r: u64)
    ensures
        r == 3u64,
{
    let mut a = BitSet::new();
    let p1 = a.insert(1);
    assert(p1 == true);
    let p2 = a.insert(3);
    assert(p2 == true);
    let p3 = a.insert(5);
    assert(p3 == true);
    let p4 = a.insert(200);
    assert(p4 == true);
    let p5 = a.insert(500);
    assert(p5 == true);
    let mut b = BitSet::new();
    let q1 = b.insert(3);
    assert(q1 == true);
    let q2 = b.insert(200);
    assert(q2 == true);
    proof {
        assert forall|i: usize| bs_at(&a, i)
            == (i == 1 || i == 3 || i == 5 || i == 200 || i == 500) by { }
        assert forall|i: usize| bs_at(&b, i)
            == (i == 3 || i == 200) by { }
    }
    let mut it = BiExec::bi_difference(&a.bit_vec, &b.bit_vec);
    // step 1 yields 1: the a-member with the b stream clear below it
    proof {
        assert(bi_nb(&it) == 501usize);
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 0usize);
        assert(!bs_at(&a, 0));
        assert(bi_at(&it, 0) == false);
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 1usize);
        assert(bs_at(&a, 1));
        assert(!bs_at(&b, 1));
        assert(bi_at(&it, 1));
    }
    let y1 = it.bi_next();
    assert(y1 == Some(1));
    // step 2 yields 5: the a-member, with 2 and 4 clear and 3
    // subtracted away (the gap starts at the post-yield log 2)
    proof {
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 2usize);
        assert(!bs_at(&a, 2));
        assert(bi_at(&it, 2) == false);
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 3usize);
        assert(bs_at(&a, 3));
        assert(bs_at(&b, 3));
        assert(bi_at(&it, 3) == false);
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 4usize);
        assert(!bs_at(&a, 4));
        assert(bi_at(&it, 4) == false);
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 5usize);
        assert(bs_at(&a, 5));
        assert(!bs_at(&b, 5));
        assert(bi_at(&it, 5));
    }
    let y2 = it.bi_next();
    assert(y2 == Some(5));
    // step 3 yields 500: the long middle gap 6..499 is subtracted away
    // (the a-side carries only 200 there, and the b-side subtracts it)
    proof {
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 200usize);
        assert(bs_at(&a, 200));
        assert(bs_at(&b, 200));
        assert(bi_at(&it, 200) == false);
        lemma_pin_andnot(&it, &a.bit_vec, &b.bit_vec, 500usize);
        assert(bs_at(&a, 500));
        assert(!bs_at(&b, 500));
        assert(bi_at(&it, 500));
        assert forall|p: usize| 6int <= (p as int) && (p as int) < 500int
            ==> bi_at(&it, p) == false by {
            let sa_seq: Seq<u32> = a.bit_vec.storage@;
            let sb_seq: Seq<u32> = b.bit_vec.storage@;
            let i2: usize = (p / 32) as usize;
            assert(bi_word(&it, i2)
                == kind_merged(2u8, side_word_seq(sa_seq, i2), side_word_seq(sb_seq, i2)));
            lemma_bi_at_membership(2u8, sa_seq, sb_seq, 501usize, 201usize, p);
            assert(bs_at(&a, p) == (p < 501usize
                && bit_at(sa_seq, 501usize, p)));
            assert(bs_at(&b, p) == (p < 201usize
                && bit_at(sb_seq, 201usize, p)));
        }
    }
    let y3 = it.bi_next();
    assert(y3 == Some(500));
    // step 4 is the exhaustion step: the universe edge at 501
    let y4 = it.bi_next();
    assert(y4 == None);
    3u64
}

/// upstream test_bit_set_symmetric_difference (tests/set.rs:150-169):
/// the symmetric difference of {1,3,5,9,11} and {3,9,14,220} collects
/// [1, 5, 11, 14, 220].
pub exec fn ut_symmetric_difference() -> (r: u64)
    ensures
        r == 5u64,
{
    let mut a = BitSet::new();
    let f1 = a.insert(1);
    assert(f1 == true);
    let f2 = a.insert(3);
    assert(f2 == true);
    let f3 = a.insert(5);
    assert(f3 == true);
    let f4 = a.insert(9);
    assert(f4 == true);
    let f5 = a.insert(11);
    assert(f5 == true);
    let mut b = BitSet::new();
    let g1 = b.insert(3);
    assert(g1 == true);
    let g2 = b.insert(9);
    assert(g2 == true);
    let g3 = b.insert(14);
    assert(g3 == true);
    let g4 = b.insert(220);
    assert(g4 == true);
    proof {
        assert forall|i: usize| bs_at(&a, i)
            == (i == 1 || i == 3 || i == 5 || i == 9 || i == 11) by { }
        assert forall|i: usize| bs_at(&b, i)
            == (i == 3 || i == 9 || i == 14 || i == 220) by { }
    }
    let mut it = BiExec::bi_symmetric_difference(&a.bit_vec, &b.bit_vec);
    // step 1 yields 1: the pair disagrees only at 1 below it
    proof {
        assert(bi_nb(&it) == 221usize);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 0usize);
        assert(!bs_at(&a, 0));
        assert(!bs_at(&b, 0));
        assert(bi_at(&it, 0) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 1usize);
        assert(bs_at(&a, 1));
        assert(!bs_at(&b, 1));
        assert(bi_at(&it, 1));
    }
    let y1 = it.bi_next();
    assert(y1 == Some(1));
    // step 2 yields 5: positions 2, 3, 4 all agree between the sides
    proof {
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 2usize);
        assert(!bs_at(&a, 2));
        assert(!bs_at(&b, 2));
        assert(bi_at(&it, 2) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 3usize);
        assert(bs_at(&a, 3));
        assert(bs_at(&b, 3));
        assert(bi_at(&it, 3) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 4usize);
        assert(!bs_at(&a, 4));
        assert(!bs_at(&b, 4));
        assert(bi_at(&it, 4) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 5usize);
        assert(bs_at(&a, 5));
        assert(!bs_at(&b, 5));
        assert(bi_at(&it, 5));
    }
    let y2 = it.bi_next();
    assert(y2 == Some(5));
    // step 3 yields 11: 6..10 agree between the sides
    proof {
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 6usize);
        assert(!bs_at(&a, 6));
        assert(!bs_at(&b, 6));
        assert(bi_at(&it, 6) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 7usize);
        assert(!bs_at(&a, 7));
        assert(!bs_at(&b, 7));
        assert(bi_at(&it, 7) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 8usize);
        assert(!bs_at(&a, 8));
        assert(!bs_at(&b, 8));
        assert(bi_at(&it, 8) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 9usize);
        assert(bs_at(&a, 9));
        assert(bs_at(&b, 9));
        assert(bi_at(&it, 9) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 10usize);
        assert(!bs_at(&a, 10));
        assert(!bs_at(&b, 10));
        assert(bi_at(&it, 10) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 11usize);
        assert(bs_at(&a, 11));
        assert(!bs_at(&b, 11));
        assert(bi_at(&it, 11));
    }
    let y3 = it.bi_next();
    assert(y3 == Some(11));
    // step 4 yields 14: 12 and 13 agree (both clear)
    proof {
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 12usize);
        assert(!bs_at(&a, 12));
        assert(!bs_at(&b, 12));
        assert(bi_at(&it, 12) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 13usize);
        assert(!bs_at(&a, 13));
        assert(!bs_at(&b, 13));
        assert(bi_at(&it, 13) == false);
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 14usize);
        assert(!bs_at(&a, 14));
        assert(bs_at(&b, 14));
        assert(bi_at(&it, 14));
    }
    let y4 = it.bi_next();
    assert(y4 == Some(14));
    // step 5 yields 220: the long tail 15..219 is all-agreement
    proof {
        lemma_pin_xor(&it, &a.bit_vec, &b.bit_vec, 220usize);
        assert(!bs_at(&a, 220));
        assert(bs_at(&b, 220));
        assert(bi_at(&it, 220));
        assert forall|p: usize| 15int <= (p as int) && (p as int) < 220int
            ==> bi_at(&it, p) == false by {
            let sa_seq: Seq<u32> = a.bit_vec.storage@;
            let sb_seq: Seq<u32> = b.bit_vec.storage@;
            let i2: usize = (p / 32) as usize;
            assert(bi_word(&it, i2)
                == kind_merged(3u8, side_word_seq(sa_seq, i2), side_word_seq(sb_seq, i2)));
            lemma_bi_at_membership(3u8, sa_seq, sb_seq, 12usize, 221usize, p);
            assert(bs_at(&a, p) == (p < 12usize
                && bit_at(sa_seq, 12usize, p)));
            assert(bs_at(&b, p) == (p < 221usize
                && bit_at(sb_seq, 221usize, p)));
        }
    }
    let y5 = it.bi_next();
    assert(y5 == Some(220));
    // step 6 is the exhaustion step: the universe edge at 221
    let y6 = it.bi_next();
    assert(y6 == None);
    5u64
}

/// upstream test_bit_set_union (tests/set.rs:172-195):
/// the union of {1,3,5,9,11,19,24,160,200} with {1,5,9,13,19} collects
/// [1, 3, 5, 9, 11, 13, 19, 24, 160, 200].
pub exec fn ut_union() -> (r: u64)
    ensures
        r == 10u64,
{
    let mut a = BitSet::new();
    let v1 = a.insert(1);
    assert(v1 == true);
    let v2 = a.insert(3);
    assert(v2 == true);
    let v3 = a.insert(5);
    assert(v3 == true);
    let v4 = a.insert(9);
    assert(v4 == true);
    let v5 = a.insert(11);
    assert(v5 == true);
    let v6 = a.insert(160);
    assert(v6 == true);
    let v7 = a.insert(19);
    assert(v7 == true);
    let v8 = a.insert(24);
    assert(v8 == true);
    let v9 = a.insert(200);
    assert(v9 == true);
    let mut b = BitSet::new();
    let w1 = b.insert(1);
    assert(w1 == true);
    let w2 = b.insert(5);
    assert(w2 == true);
    let w3 = b.insert(9);
    assert(w3 == true);
    let w4 = b.insert(13);
    assert(w4 == true);
    let w5 = b.insert(19);
    assert(w5 == true);
    proof {
        assert forall|i: usize| bs_at(&a, i)
            == (i == 1 || i == 3 || i == 5 || i == 9 || i == 11
                || i == 19 || i == 24 || i == 160 || i == 200) by { }
        assert forall|i: usize| bs_at(&b, i)
            == (i == 1 || i == 5 || i == 9 || i == 13 || i == 19) by { }
    }
    let mut it = BiExec::bi_union(&a.bit_vec, &b.bit_vec);
    // step 1 yields 1 (a shared member; 0 on neither side)
    proof {
        assert(bi_nb(&it) == 201usize);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 0usize);
        assert(!bs_at(&a, 0));
        assert(!bs_at(&b, 0));
        assert(bi_at(&it, 0) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 1usize);
        assert(bs_at(&a, 1));
        assert(bi_at(&it, 1));
    }
    let y1 = it.bi_next();
    assert(y1 == Some(1));
    // step 2 yields 3: 2 is no member on either side
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 2usize);
        assert(!bs_at(&a, 2));
        assert(!bs_at(&b, 2));
        assert(bi_at(&it, 2) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 3usize);
        assert(bs_at(&a, 3));
        assert(bi_at(&it, 3));
    }
    let y2 = it.bi_next();
    assert(y2 == Some(3));
    // step 3 yields 5
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 4usize);
        assert(!bs_at(&a, 4));
        assert(!bs_at(&b, 4));
        assert(bi_at(&it, 4) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 5usize);
        assert(bs_at(&a, 5));
        assert(bi_at(&it, 5));
    }
    let y3 = it.bi_next();
    assert(y3 == Some(5));
    // step 4 yields 9: 6, 7, 8 on neither side
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 6usize);
        assert(!bs_at(&a, 6));
        assert(!bs_at(&b, 6));
        assert(bi_at(&it, 6) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 7usize);
        assert(!bs_at(&a, 7));
        assert(!bs_at(&b, 7));
        assert(bi_at(&it, 7) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 8usize);
        assert(!bs_at(&a, 8));
        assert(!bs_at(&b, 8));
        assert(bi_at(&it, 8) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 9usize);
        assert(bs_at(&a, 9));
        assert(bi_at(&it, 9));
    }
    let y4 = it.bi_next();
    assert(y4 == Some(9));
    // step 5 yields 11: 10 on neither side
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 10usize);
        assert(!bs_at(&a, 10));
        assert(!bs_at(&b, 10));
        assert(bi_at(&it, 10) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 11usize);
        assert(bs_at(&a, 11));
        assert(bi_at(&it, 11));
    }
    let y5 = it.bi_next();
    assert(y5 == Some(11));
    // step 6 yields 13 (the b-side member; 12 on neither side)
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 12usize);
        assert(!bs_at(&a, 12));
        assert(!bs_at(&b, 12));
        assert(bi_at(&it, 12) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 13usize);
        assert(bs_at(&b, 13));
        assert(bi_at(&it, 13));
    }
    let y6 = it.bi_next();
    assert(y6 == Some(13));
    // step 7 yields 19: 14..18 on neither side
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 14usize);
        assert(!bs_at(&a, 14));
        assert(!bs_at(&b, 14));
        assert(bi_at(&it, 14) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 15usize);
        assert(!bs_at(&a, 15));
        assert(!bs_at(&b, 15));
        assert(bi_at(&it, 15) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 16usize);
        assert(!bs_at(&a, 16));
        assert(!bs_at(&b, 16));
        assert(bi_at(&it, 16) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 17usize);
        assert(!bs_at(&a, 17));
        assert(!bs_at(&b, 17));
        assert(bi_at(&it, 17) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 18usize);
        assert(!bs_at(&a, 18));
        assert(!bs_at(&b, 18));
        assert(bi_at(&it, 18) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 19usize);
        assert(bs_at(&a, 19));
        assert(bi_at(&it, 19));
    }
    let y7 = it.bi_next();
    assert(y7 == Some(19));
    // step 8 yields 24: 20..23 on neither side
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 20usize);
        assert(!bs_at(&a, 20));
        assert(!bs_at(&b, 20));
        assert(bi_at(&it, 20) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 21usize);
        assert(!bs_at(&a, 21));
        assert(!bs_at(&b, 21));
        assert(bi_at(&it, 21) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 22usize);
        assert(!bs_at(&a, 22));
        assert(!bs_at(&b, 22));
        assert(bi_at(&it, 22) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 23usize);
        assert(!bs_at(&a, 23));
        assert(!bs_at(&b, 23));
        assert(bi_at(&it, 23) == false);
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 24usize);
        assert(bs_at(&a, 24));
        assert(bi_at(&it, 24));
    }
    let y8 = it.bi_next();
    assert(y8 == Some(24));
    // step 9 yields 160: the long gap 25..159 is memberless on both
    // sides (b's universe ends at 20, a's next member is 160)
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 160usize);
        assert(bs_at(&a, 160));
        assert(bi_at(&it, 160));
        assert forall|p: usize| 25int <= (p as int) && (p as int) < 160int
            ==> bi_at(&it, p) == false by {
            let sa_seq: Seq<u32> = a.bit_vec.storage@;
            let sb_seq: Seq<u32> = b.bit_vec.storage@;
            let i2: usize = (p / 32) as usize;
            assert(bi_word(&it, i2)
                == kind_merged(0u8, side_word_seq(sa_seq, i2), side_word_seq(sb_seq, i2)));
            lemma_bi_at_membership(0u8, sa_seq, sb_seq, 201usize, 20usize, p);
            assert(bs_at(&a, p) == (p < 201usize
                && bit_at(sa_seq, 201usize, p)));
            assert(bs_at(&b, p) == (p < 20usize
                && bit_at(sb_seq, 20usize, p)));
        }
    }
    let y9 = it.bi_next();
    assert(y9 == Some(160));
    // step 10 yields 200: 161..199 likewise memberless on both sides
    proof {
        lemma_pin_or(&it, &a.bit_vec, &b.bit_vec, 200usize);
        assert(bs_at(&a, 200));
        assert(bi_at(&it, 200));
        assert forall|p: usize| 161int <= (p as int) && (p as int) < 200int
            ==> bi_at(&it, p) == false by {
            let sa_seq: Seq<u32> = a.bit_vec.storage@;
            let sb_seq: Seq<u32> = b.bit_vec.storage@;
            let i2: usize = (p / 32) as usize;
            assert(bi_word(&it, i2)
                == kind_merged(0u8, side_word_seq(sa_seq, i2), side_word_seq(sb_seq, i2)));
            lemma_bi_at_membership(0u8, sa_seq, sb_seq, 201usize, 20usize, p);
            assert(bs_at(&a, p) == (p < 201usize
                && bit_at(sa_seq, 201usize, p)));
            assert(bs_at(&b, p) == (p < 20usize
                && bit_at(sb_seq, 20usize, p)));
        }
    }
    let y10 = it.bi_next();
    assert(y10 == Some(200));
    // step 11 is the exhaustion step: the universe edge at 201
    let y11 = it.bi_next();
    assert(y11 == None);
    10u64
}

/// upstream test_bit_set_iterator (tests/set.rs:47-61), small-set half:
/// drawing from [0, 2, 2, 3], the own-stream walk collects [0, 2, 3]
/// (the 10000-element half is a scale face and stays with the Rust-Cargo
/// test layer).
pub exec fn ut_iterator() -> (r: u64)
    ensures
        r == 3u64,
{
    let mut s = BitSet::new();
    let c1 = s.insert(0);
    assert(c1 == true);
    let c2 = s.insert(2);
    assert(c2 == true);
    let c3 = s.insert(3);
    assert(c3 == true);
    proof {
        assert forall|i: usize| bs_at(&s, i) == (i == 0 || i == 2 || i == 3) by { }
    }
    let mut it = BiExec::bi_iter(&s.bit_vec);
    // step 1 yields 0: nothing below it
    proof {
        assert(bi_nb(&it) == 4usize);
        lemma_pin_own(&it, &s.bit_vec, 0usize);
        assert(bs_at(&s, 0));
        assert(bi_at(&it, 0));
    }
    let y1 = it.bi_next();
    assert(y1 == Some(0));
    // step 2 yields 2: 1 clear between
    proof {
        lemma_pin_own(&it, &s.bit_vec, 1usize);
        assert(!bs_at(&s, 1));
        assert(bi_at(&it, 1) == false);
        lemma_pin_own(&it, &s.bit_vec, 2usize);
        assert(bs_at(&s, 2));
        assert(bi_at(&it, 2));
    }
    let y2 = it.bi_next();
    assert(y2 == Some(2));
    // step 3 yields 3
    proof {
        lemma_pin_own(&it, &s.bit_vec, 3usize);
        assert(bs_at(&s, 3));
        assert(bi_at(&it, 3));
    }
    let y3 = it.bi_next();
    assert(y3 == Some(3));
    // step 4 is the exhaustion step: the universe edge at 4
    let y4 = it.bi_next();
    assert(y4 == None);
    3u64
}

} // verus!

fn main() {}
