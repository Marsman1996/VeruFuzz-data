//! bit-set 0.11.1 x Verus -- UT harness, batch H1 (set_core).
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas/
//! transcriptions are never duplicated here.
//!
//! Coverage (upstream set/tests/set.rs, batch H1 -- the UTs whose
//! obligations close without the iterator-exhaustiveness tier):
//!   test_bit_set_basic / test_bit_set_from_usizes / test_bit_vec_remove /
//!   test_bit_vec_clone / test_bit_set_eq / test_bit_set_cmp
//! The iterator-collect UTs (intersection / difference / symmetric
//! difference / union / iterator) land in batch H2 -- their
//! expected-list faces need the exhaustiveness face of the walk
//! (recorded as a NoFace item in out/harness-inventory.md). The
//! display/debug UTs are string-format faces (Rust-Cargo layer runs
//! them verbatim); the capacity-value asserts of the shrink UTs are
//! allocator-runtime faces (those UTs land in batch H3 with the
//! membership/bookkeeping obligations).

#![feature(allocator_api)] // needed by the referenced src assume_specification signature
#![verifier::timeout(240)] // the crate-root timeout face (moved from src/lib.rs)

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitset_lib;

verus! {

use bitset_lib::set::{BitSet, bs_at, bs_inv, bs_count, bs_max_nb, bs_ordering_face};
use bitset_lib::bitvec_lib::{bit_at, count_bits, from_bytes_bit,
    lemma_count_range_const, lemma_count_split, lemma_popc_seq_is_count, popc, popc_seq};

// ---------------------------------------------------------------------------
// helpers: the count face over a small concrete member set (the
// count_ones face equals the count_bits recursion; the concrete member
// positions decompose into constant ranges through the verified split
// lemmas, so the popcount value closes as a sum of range counts)
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// member bridges over the concrete byte-built faces (the from_bytes
// face instance at i plus the bit-mask definition, hoisted into one
// lemma the harness bodies instantiate per concrete position)
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
        == (((bytes@[(i / 8) as int] & (1u8 << (7 - (i % 8)))) != 0u8)));
}

/// the zero-byte face: a set built from a single zero byte carries no
/// member at any position (every in-universe bit reads a clear byte bit;
/// every position above the universe is clipped by the universe bound).
/// Harness-local helper (no src-side duplication: the face rides the
/// from_bytes postcondition, instantiated here position-by-position).
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
// UT bodies (one exec fn per upstream #[test]; the assertions are the
// upstream assert_eq/assert! faces translated into verus asserts and
// ensures)
// ---------------------------------------------------------------------------

/// upstream test_bit_set_basic (tests/set.rs:90-103):
/// insert returns !present; contains tracks; count == 3 for {3,4,400}.
pub exec fn ut_basic() -> (r: u64)
    ensures
        r == 3u64,
{
    let mut b = BitSet::new();
    let r1 = b.insert(3);
    assert(r1 == true);
    assert(bs_at(&b, 3));
    let r2 = b.insert(3);
    assert(r2 == false);
    assert(bs_at(&b, 3));
    let r3 = b.insert(4);
    assert(r3 == true);
    let r4 = b.insert(4);
    assert(r4 == false);
    assert(bs_at(&b, 3) && bs_at(&b, 4));
    let r5 = b.insert(400);
    assert(r5 == true);
    let r6 = b.insert(400);
    assert(r6 == false);
    assert(bs_at(&b, 400));
    assert(!bs_at(&b, 2));
    let cnt = b.count();
    proof {
        let s = b.bit_vec.storage@;
        let n = b.bit_vec.nbits;
        assert((n as int) == 401int);
        // the count face via the member faces (the insert chain adds exactly
        // the elements 3, 4 and 400; each insert's postcondition preserves
        // every older element, so the accumulated member face closes
        // pointwise -- no concrete storage word values needed)
        assert forall|i: usize| #[trigger] bs_at(&b, i)
            == (i == 3 || i == 4 || i == 400) by { }
        // rectified to the bit model below the universe
        assert forall|p: usize| (p as int) < 401int
            ==> bit_at(s, n, p) == (p == 3 || p == 4 || p == 400) by {
            if (p as int) < 401int {
                assert(bs_at(&b, p) == bit_at(s, n, p));
            }
        }
        // the range premises of the two-range count decomposition, spelled
        // for the prover so it can instantiate them at the lemma's skolem
        // positions
        assert forall|p: usize| (p as int) < 3int ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 3int <= (p as int) && (p as int) < 5int
            ==> bit_at(s, n, p) by { }
        assert forall|p: usize| 5int <= (p as int) && (p as int) < 400int
            ==> !bit_at(s, n, p) by { }
        assert forall|p: usize| 400int <= (p as int) && (p as int) < 401int
            ==> bit_at(s, n, p) by { }
        // the two uniform member ranges [3,5) and [400,401): the counted
        // face decomposes through the verified range lemmas
        bitset_lib::set::lemma_count_two_ranges(s, n, 3usize, 5usize, 400usize, 401usize);
        assert(count_bits(s, n, 0usize, n) == 3int);
        assert(bs_count(&b) == 3int);
        assert(cnt as int == 3);
    }
    (cnt as u64)
}

/// upstream test_bit_set_from_usizes (tests/set.rs:35-44):
/// collect of [0, 2, 2, 3] equals the insert-built {0, 2, 3}.
pub exec fn ut_from_usizes() -> (r: u64)
    ensures
        r == 1u64,
{
    let mut items: Vec<usize> = Vec::new();
    items.push(0);
    items.push(2);
    items.push(2);
    items.push(3);
    proof {
        assert(items@.len() == 4int);
        assert(items@[0] == 0);
        assert(items@[1] == 2);
        assert(items@[2] == 2);
        assert(items@[3] == 3);
    }
    let a = BitSet::from_iter_items(&items);
    let mut b = BitSet::new();
    b.insert(0);
    b.insert(2);
    b.insert(3);
    let e = b.eq(&a);
    assert(e == true);
    1u64
}

/// upstream test_bit_vec_remove (tests/set.rs:458-471):
/// insert then remove returns true both times; empty again after.
pub exec fn ut_remove() -> (r: u64)
    ensures
        r == 1u64,
{
    let mut a = BitSet::new();
    let r1 = a.insert(1);
    assert(r1 == true);
    let d1 = a.remove(1);
    assert(d1 == true);
    assert(!bs_at(&a, 1));
    let r2 = a.insert(100);
    assert(r2 == true);
    let d2 = a.remove(100);
    assert(d2 == true);
    let r3 = a.insert(1000);
    assert(r3 == true);
    let d3 = a.remove(1000);
    assert(d3 == true);
    a.shrink_to_fit();
    1u64
}

/// upstream test_bit_vec_clone (tests/set.rs:473-490):
/// the clone is member-equal; removals do not cross the copies.
pub exec fn ut_clone() -> (r: u64)
    ensures
        r == 1u64,
{
    let mut a = BitSet::new();
    a.insert(1);
    a.insert(100);
    a.insert(1000);
    let b = a.clone();
    let e1 = a.eq(&b);
    assert(e1 == true);
    let mut b2 = b;
    let d = b2.remove(1);
    assert(d == true);
    assert(bs_at(&a, 1));
    let d2 = a.remove(1000);
    assert(d2 == true);
    assert(bs_at(&b2, 1000));
    1u64
}

/// upstream test_bit_set_eq (tests/set.rs:345-357):
/// eq over the from_bytes faces vs the empty set.
pub exec fn ut_eq() -> (r: u64)
    ensures
        r == 1u64,
{
    let bytes_a: &[u8] = &[0b10100010];
    let bytes_b: &[u8] = &[0b00000000];
    let a = BitSet::from_bytes(bytes_a);
    let b = BitSet::from_bytes(bytes_b);
    let c = BitSet::new();
    let e1 = a.eq(&a);
    assert(e1 == true);
    proof {
        // the divergence witnesses: byte 0 of 0b10100010 carries the
        // high bit, the comparison sets carry nothing there
        assert(bs_at(&a, 0) == from_bytes_bit(bytes_a@, 0));
        assert(bs_at(&b, 0) == from_bytes_bit(bytes_b@, 0));
        lemma_byte_member(&a, bytes_a, 0);
        lemma_byte_member(&b, bytes_b, 0);
        let w0: u8 = bytes_a@[0];
        let w1: u8 = bytes_b@[0];
        assert(w0 == 0b10100010u8);
        assert(w1 == 0b00000000u8);
        assert((w0 & (1u8 << 7)) != 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w1 & (1u8 << 7)) == 0u8) by (bit_vector)
            requires (w1 as u32) == 0u32;
        assert(bs_at(&a, 0));
        assert(!bs_at(&b, 0));
        assert(!bs_at(&c, 0));
    }
    let e2 = a.eq(&b);
    assert(e2 == false);
    let e3 = a.eq(&c);
    assert(e3 == false);
    let e4 = b.eq(&b);
    assert(e4 == true);
    let e5 = b.eq(&c);
    proof {
        // the zero byte carries no member anywhere; the empty set neither,
        // so the padded equality over the shared universe holds everywhere
        lemma_zero_byte_memberless(&b, bytes_b);
        assert(bs_max_nb(&b, &c) == 8usize);
    }
    assert(e5 == true);
    let e6 = c.eq(&c);
    assert(e6 == true);
    1u64
}

/// upstream test_bit_set_cmp (tests/set.rs:359-371):
/// the u8-materialized Ordering face (2 = Greater, 0 = Less, 1 = Equal).
pub exec fn ut_cmp() -> (r: u64)
    ensures
        r == 1u64,
{
    let bytes_a: &[u8] = &[0b10100010];
    let bytes_b: &[u8] = &[0b00000000];
    let a = BitSet::from_bytes(bytes_a);
    let b = BitSet::from_bytes(bytes_b);
    let c = BitSet::new();
    let c1 = a.cmp(&b);
    proof {
        // the ground members of the 0b10100010 byte: positions 0, 2 and 6
        // (byte bit 7-i), with the low-side non-members spelled out so the
        // cmp branch refutations can fire at fixed positions
        let w0: u8 = bytes_a@[0];
        assert(w0 == 0b10100010u8);
        assert(bs_at(&a, 0) == from_bytes_bit(bytes_a@, 0));
        assert(bs_at(&a, 2) == from_bytes_bit(bytes_a@, 2));
        assert(bs_at(&a, 6) == from_bytes_bit(bytes_a@, 6));
        lemma_byte_member(&a, bytes_a, 0);
        lemma_byte_member(&a, bytes_a, 2);
        lemma_byte_member(&a, bytes_a, 6);
        assert((w0 & (1u8 << 7)) != 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 5)) != 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 1)) != 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 6)) == 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 4)) == 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 3)) == 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 2)) == 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert((w0 & (1u8 << 0)) == 0u8) by (bit_vector)
            requires (w0 as u32) == 0b10100010u32;
        assert(bs_at(&a, 0));
        assert(bs_at(&a, 2));
        assert(bs_at(&a, 6));
        assert(!bs_at(&a, 1));
        assert(!bs_at(&a, 3));
        assert(!bs_at(&a, 4));
        assert(!bs_at(&a, 5));
        assert(!bs_at(&a, 7));
        // the zero byte side stays memberless everywhere
        lemma_zero_byte_memberless(&b, bytes_b);
        assert(!bs_at(&b, 0));
    }
    assert(c1 == 2u8);
    let c2 = a.cmp(&c);
    assert(c2 == 2u8);
    let c3 = b.cmp(&a);
    assert(c3 == 0u8);
    let c4 = b.cmp(&c);
    proof {
        // both sides are memberless, so the padded walks agree everywhere
        lemma_zero_byte_memberless(&b, bytes_b);
        assert(bs_max_nb(&b, &c) == 8usize);
    }
    assert(c4 == 1u8);
    let c5 = c.cmp(&a);
    assert(c5 == 0u8);
    let c6 = c.cmp(&b);
    assert(c6 == 1u8);
    1u64
}

} // verus!

fn main() {}
