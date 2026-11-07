//! harness: auto-generated coverage-diff set
//!
//! Coverage diff set = the members of the code/src public API (the src/lib.rs:277-297
//! export surface) not independently covered by the
//! UT face:
//!   * the ** universal equivalence group ** of "macro-expanded body == Flags trait
//!     default body" (the upstream UT double-checks Each case, example by
//!     example; here it is lifted to functional equivalence theorems) -- upstream
//!     sites: public.rs:32-285 (expansion) vs
//!     traits.rs:132-371 (default bodies).
//!   * the fold-union semantics of `Extend::extend` / `FromIterator`
//!     (public.rs:490-514)
//!     (a 4-element unrolled array loop; the equivalent spec is the union
//!     associativity chain).
//!   * the FLAGS/constant consistency of `__impl_public_bitflags_consts!`
//!     (traits.rs:134,
//!     public.rs:550-586) and `all_named` (traits.rs:158-165).
//!   * the ports of the traits.rs unknown/known family under the ** TestExternal
//!     instance shape ** (the internal unnamed flag `const _ = !0`, the
//!     code/src/tests.rs:122-143 fixture; mask == 0xffffffff), i.e.
//!     the full-mask ports of that family.
//!
//! Notation as in ut_ops: exec calls are let-bound first; a constant expectation =
//! the ensures chain (x == sem(...)) + a self-contained by (bit_vector) fold.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bfsrc;

use bfsrc::example_generated::TestFlags;
use bfsrc::traits::{
    complement_sem_of, contains_sem, difference_sem, flags_all, flags_all_named, flags_clear, flags_complement,
    flags_contains, flags_contains_unknown_bits, flags_difference, flags_empty, flags_from_bits,
    flags_from_bits_retain, flags_from_bits_truncate, flags_insert, flags_intersection,
    flags_intersects, flags_is_all, flags_is_empty, flags_known_bits, flags_remove,
    flags_symmetric_difference, flags_toggle, flags_truncate, flags_union, flags_unknown_bits,
    flag_bits_spec, flag_name_id_spec, from_name_lookup, intersection_sem, intersects_sem,
    is_all_sem_of, symmetric_difference_sem, tflags_all_bits, truncate_sem_of, union_sem,
};

verus! {

/* ============================================================
 * A. macro-expanded body == Flags trait default body (a functional equivalence
 *    group; universal over any bits inputs)
 *    (the universalization of the upstream UT per-case double-check "T::x(..) ==
 *    Flags::x(..)")
 * ============================================================ */

exec fn eq_union(a: u32, b: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let mb = TestFlags::from_bits_retain(b);
    let macro_side = ma.union(mb).bits;
    let trait_side = flags_union(a, b);
    assert(macro_side == trait_side);
    assert(ma.bits == a);
    assert(mb.bits == b);
}

exec fn eq_intersection(a: u32, b: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let mb = TestFlags::from_bits_retain(b);
    let macro_side = ma.intersection(mb).bits;
    let trait_side = flags_intersection(a, b);
    assert(macro_side == trait_side);
}

exec fn eq_difference(a: u32, b: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let mb = TestFlags::from_bits_retain(b);
    let macro_side = ma.difference(mb).bits;
    let trait_side = flags_difference(a, b);
    assert(macro_side == trait_side);
}

exec fn eq_symmetric_difference(a: u32, b: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let mb = TestFlags::from_bits_retain(b);
    let macro_side = ma.symmetric_difference(mb).bits;
    let trait_side = flags_symmetric_difference(a, b);
    assert(macro_side == trait_side);
}

exec fn eq_complement(a: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let macro_side = ma.complement().bits;
    let trait_side = flags_complement(0b0000_0111u32, a);
    assert(macro_side == trait_side);
}

exec fn eq_contains(a: u32, b: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let mb = TestFlags::from_bits_retain(b);
    let macro_side = ma.contains(&mb);
    let trait_side = flags_contains(a, b);
    assert(macro_side == trait_side);
}

exec fn eq_intersects(a: u32, b: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let mb = TestFlags::from_bits_retain(b);
    let macro_side = ma.intersects(&mb);
    let trait_side = flags_intersects(a, b);
    assert(macro_side == trait_side);
}

exec fn eq_is_empty(a: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let macro_side = ma.is_empty();
    let trait_side = flags_is_empty(a);
    assert(macro_side == trait_side);
}

exec fn eq_is_all(a: u32)
{
    let ma = TestFlags::from_bits_retain(a);
    let macro_side = ma.is_all();
    let trait_side = flags_is_all(0b0000_0111u32, a);
    assert(macro_side == trait_side);
}

exec fn eq_from_bits(a: u32)
{
    let macro_side = TestFlags::from_bits(a);
    let trait_side = flags_from_bits(0b0000_0111u32, a);
    assert(macro_side.is_some() == trait_side.is_some());
}

exec fn eq_from_bits_truncate(a: u32)
{
    let macro_side = TestFlags::from_bits_truncate(a).bits;
    let trait_side = flags_from_bits_truncate(0b0000_0111u32, a);
    assert(macro_side == trait_side);
}

exec fn eq_from_bits_retain(a: u32)
{
    let macro_side = TestFlags::from_bits_retain(a).bits;
    let trait_side = flags_from_bits_retain(a);
    assert(macro_side == trait_side);
}

exec fn eq_empty_all()
{
    let me = TestFlags::empty().bits;
    let te = flags_empty();
    assert(me == te);
    let ma = TestFlags::all().bits;
    let ta = flags_all();
    assert(ma == ta);
}

/// trait-side mask family: the consistency of known/unknown/contains_unknown (any v)
exec fn eq_known_unknown_bits(a: u32)
{
    let k = flags_known_bits(0b0000_0111u32, a);
    assert(k == a & 0b0000_0111u32);
    assert((a & 0b0000_0111u32) == truncate_sem_of(0b0000_0111u32, a));
    let u = flags_unknown_bits(0b0000_0111u32, a);
    assert(u == a & !0b0000_0111u32);
    let c = flags_contains_unknown_bits(0b0000_0111u32, a);
    assert(c == (a & !0b0000_0111u32 != 0u32));
    // the identity known + unknown == v (for any v)
    assert((a & 0b0000_0111u32) | (a & !0b0000_0111u32) == a) by (bit_vector);
}

/// the trait-side mut family (insert/remove/toggle/truncate/clear/set) agrees with the spec layer
exec fn eq_insert_remove_toggle_truncate(a: u32, b: u32)
{
    let mut v: u32 = a;
    flags_insert(&mut v, b);
    assert(v == union_sem(a, b));
    let mut w: u32 = a;
    flags_remove(&mut w, b);
    assert(w == difference_sem(a, b));
    let mut x: u32 = a;
    flags_toggle(&mut x, b);
    assert(x == symmetric_difference_sem(a, b));
    let mut y: u32 = a;
    flags_truncate(0b0000_0111u32, &mut y);
    assert(y == truncate_sem_of(0b0000_0111u32, a));
    let mut c: u32 = a;
    flags_clear(&mut c);
    assert(c == 0u32);
}

/* ============================================================
 * B. The fold-union semantics of Extend::extend / FromIterator
 *     (public.rs:490-514: `for item in iterator { self.insert(item) }`)
 * ============================================================ */

/// extend over a 4-element array: the iterative insert == the union chain (universal over any 5 bits)
exec fn prop_extend_fold_union(a0: u32, xs: [u32; 4])
{
    // Origin corresponds to the upstream loop `for item in iterator { self.insert(item) }`
    let mut acc: u32 = a0;
    acc = acc | xs[0];
    acc = acc | xs[1];
    acc = acc | xs[2];
    acc = acc | xs[3];
    assert(acc == union_sem(union_sem(union_sem(union_sem(a0, xs[0]), xs[1]), xs[2]), xs[3]));
    // the macro-side comparison (the generated Extend for TestFlags)
    let mut g = TestFlags::from_bits_retain(a0);
    g.insert(TestFlags::from_bits_retain(xs[0]));
    g.insert(TestFlags::from_bits_retain(xs[1]));
    g.insert(TestFlags::from_bits_retain(xs[2]));
    g.insert(TestFlags::from_bits_retain(xs[3]));
    assert(g.bits == acc);
}

/// FromIterator: an extend starting from empty == the union chain
exec fn prop_from_iter_fold_union(xs: [u32; 4])
{
    let mut acc: u32 = 0u32;
    acc = acc | xs[0];
    acc = acc | xs[1];
    acc = acc | xs[2];
    acc = acc | xs[3];
    assert(acc
        == union_sem(union_sem(union_sem(union_sem(0u32, xs[0]), xs[1]), xs[2]), xs[3]));
}

/* ============================================================
 * C. FLAGS/constant consistency + all_named (the universalization of the fixture flags.rs::cases)
 * ============================================================ */

exec fn prop_all_named_equals_all_when_all_named()
{
    // all 4 TestFlags entries are named => Flags::all_named == Flags::all (traits.rs:157)
    let an = flags_all_named();
    let al = flags_all();
    assert(an == al);
}

exec fn prop_flag_consts_match_table()
{
    proof {
        bfsrc::example_generated::lemma_consts_match_flags();
    }
    // the public constants agree with the FLAGS table entry by entry (the upstream flags.rs UT equalities)
    assert(TestFlags::A.bits == flag_bits_spec(0));
    assert(TestFlags::B.bits == flag_bits_spec(1));
    assert(TestFlags::C.bits == flag_bits_spec(2));
    assert(TestFlags::ABC.bits == flag_bits_spec(3));
    // the from_name lookup table hits all 4 ids (the name/id model: traits.rs relaxation 1)
    // from_name_lookup is a spec fn -- it appears as an assertion (exec context cannot let-bind it)
    assert(from_name_lookup(1u64) == Option::Some(TestFlags::A.bits));
    assert(from_name_lookup(2u64) == Option::Some(TestFlags::B.bits));
    assert(from_name_lookup(3u64) == Option::Some(TestFlags::C.bits));
    assert(from_name_lookup(4u64) == Option::Some(TestFlags::ABC.bits));

}

/* ============================================================
 * D. The TestExternal instance shape (internal unnamed flag `const _ = !0`; mask == 0xffffffff)
 *    -- the ports of the traits.rs unknown/known semantics under the full mask
 *    (the TestExternal fixture shape of code/src/tests.rs:122-143)
 * ============================================================ */

/// `Flags::all().bits()` of TestExternal: A|B|C|ABC|!(0) == !0
pub open spec fn test_external_all() -> u32 {
    0xffff_ffffu32
}

/// under the full mask known bits == v (unknown_bits is always 0)
exec fn prop_external_known_unknown_bits(v: u32)
{
    assert(v & 0xffff_ffffu32 == v) by (bit_vector);
    assert(v & !0xffff_ffffu32 == 0u32) by (bit_vector);
    let k = flags_known_bits(0xffff_ffffu32, v);
    assert(k == v & 0xffff_ffffu32);
    assert(k == v);
    let u = flags_unknown_bits(0xffff_ffffu32, v);
    assert(u == v & !0xffff_ffffu32);
    assert(u == 0u32);
    let c = flags_contains_unknown_bits(0xffff_ffffu32, v);
    assert(c == (v & !0xffff_ffffu32 != 0u32));
    assert(c == false);
}

/// full mask: the from_bits/from_bits_truncate semantics is the identity
exec fn prop_external_converters(v: u32)
{
    assert(truncate_sem_of(0xffff_ffffu32, v) == v) by (bit_vector);
    assert(v == truncate_sem_of(0xffff_ffffu32, v));
    let fbt = flags_from_bits_truncate(0xffff_ffffu32, v);
    assert(fbt == truncate_sem_of(0xffff_ffffu32, v));
    assert(fbt == v);
    let fb = flags_from_bits(0xffff_ffffu32, v);
    assert(fb.is_some());
    let fr = flags_from_bits_retain(v);
    assert(fr == v);
}

/// full mask: is_all <=> v == !0, plus the complement characterization
exec fn prop_external_all_complement(v: u32)
{
    assert((v & 0xffff_ffffu32 == 0xffff_ffffu32) == (v == 0xffff_ffffu32)) by (bit_vector);
    let s = flags_is_all(0xffff_ffffu32, v);
    assert(s == is_all_sem_of(0xffff_ffffu32, v));
    assert(is_all_sem_of(0xffff_ffffu32, v) == contains_sem(v, 0xffff_ffffu32));
    assert(is_all_sem_of(0xffff_ffffu32, v) == (v == 0xffff_ffffu32));
    // the complement characterization under the full mask (the TestExternal shape):
    // !v & all == !v
    // (the only truncating op degenerates to the plain complement over the
    // all-known bit domain) -- the upstream complement.rs:47
    // `case(!0, TestExternal::empty(), TestExternal::complement)` is exactly this instance
    assert(!v & 0xffff_ffffu32 == !v) by (bit_vector);
    let c = flags_complement(0xffff_ffffu32, v);
    assert(c == complement_sem_of(0xffff_ffffu32, v));
    assert(complement_sem_of(0xffff_ffffu32, v) == !v & 0xffff_ffffu32);
    assert(complement_sem_of(0xffff_ffffu32, v) == !v);
    // TestExternal::empty().complement().bits() == !0 (the upstream complement.rs:47 case)
    assert(!0u32 == 0xffff_ffffu32) by (bit_vector);
    assert(0xffff_ffffu32 & 0xffff_ffffu32 == 0xffff_ffffu32) by (bit_vector);
    let ec0 = flags_complement(0xffff_ffffu32, 0u32);
    assert(ec0 == complement_sem_of(0xffff_ffffu32, 0u32));
    assert(ec0 == !0u32 & 0xffff_ffffu32);
    assert(ec0 == 0xffff_ffffu32 & 0xffff_ffffu32);
    let ec = ec0;
    assert(ec == 0xffff_ffffu32);
}

fn main() {}
}
