//! harness: UT witnesses of `code/src/tests/`
//!
//! Reference-style organization: `#[path]` mounts verified/src/lib.rs
//! (specs/lemmas exist only once, in src).
//! Coverage (upstream file -> this file's fns):
//!   empty.rs -> ut_empty; all.rs -> ut_all; bits.rs -> ut_bits; clear.rs -> ut_clear;
//!   complement.rs -> ut_complement; contains.rs -> ut_contains;
//!   difference.rs -> ut_difference; intersection.rs -> ut_intersection;
//!   intersects.rs -> ut_intersects; is_all.rs -> ut_is_all; is_empty.rs -> ut_is_empty;
//!   known_bits.rs -> ut_known_bits; unknown_bits.rs/unknown.rs -> ut_unknown_bits;
//!   union.rs -> ut_union; insert.rs -> ut_insert_set; remove.rs -> ut_remove_set;
//!   symmetric_difference.rs -> ut_symmetric_difference_toggle;
//!   truncate.rs -> ut_truncate_mut; from_bits.rs -> ut_from_bits;
//!   from_bits_truncate.rs -> ut_from_bits_truncate;
//!   from_bits_retain.rs -> ut_from_bits_retain; from_name.rs -> ut_from_name;
//!   flags.rs/flag_name.rs -> ut_flags_table.
//!
//! Notation notes (SMT adaptation):
//! 1. verus `assert` lives in spec mode; exec calls are always let-bound first;
//! 2. each constant expectation takes two steps -- `x == sem(const)` (chained
//!    from the callee ensures)
//!    + `sem(const) == <upstream expectation>` (a self-contained `by (bit_vector)`
//!    fold) -- no unverified assumptions are introduced;
//! 3. the carrying instance is TestFlags:u32 (the same flag set as the TestFlags:u8
//!    of code/src/tests.rs:
//!    A=1 B=2 C=4 ABC=7); the u8 `1<<3` unknown-bit and `!0` upper-bound examples
//!    are adapted to u32.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bfsrc;

use bfsrc::example_generated::TestFlags;
use bfsrc::iter::IterNames;
use bfsrc::traits::{
    complement_sem_of, contains_sem, difference_sem, flags_all, flags_clear, flags_complement,
    flags_contains, flags_contains_unknown_bits, flags_difference, flags_empty, flags_from_bits,
    flags_from_bits_truncate, flags_insert, flags_intersection, flags_intersects, flags_is_all,
    flags_is_empty, flags_known_bits, flags_remove, flags_set, flags_symmetric_difference,
    flags_toggle, flags_truncate, flags_union, flags_unknown_bits, intersection_sem,
    intersects_sem, is_all_sem_of, is_empty_sem, symmetric_difference_sem, truncate_sem_of,
    union_sem, NUM_FLAGS,
};

verus! {

// ---------- empty.rs ----------
exec fn ut_empty()
{
    let f = TestFlags::empty();
    assert(f.bits == 0u32);
    let t = flags_empty();
    assert(t == 0u32);
}

// ---------- all.rs ----------
exec fn ut_all()
{
    let f = TestFlags::all();
    assert(f.bits == 0b0000_0111u32);
    let t = flags_all();
    assert(t == f.bits);
}

// ---------- bits.rs ----------
exec fn ut_bits()
{
    let f = TestFlags::from_bits_retain(0x1234_5678u32);
    assert(f.bits == 0x1234_5678u32);
    let g = TestFlags::from_bits_retain(0b1000u32);
    assert(g.bits == 0b1000u32);
}

// ---------- clear.rs ----------
exec fn ut_clear()
{
    let mut f = TestFlags::from_bits_retain(0b1111u32);
    f = TestFlags { bits: 0u32 };
    let e = TestFlags::empty();
    assert(f.bits == e.bits);
    let mut v: u32 = 0b1111u32;
    flags_clear(&mut v);
    assert(v == 0u32);
}

// ---------- complement.rs ----------
exec fn ut_complement()
{
    // expectation chain: r.bits == complement_sem(mask, v) (ensures) -> the sem fold == the upstream expectation
    let all_c = TestFlags::all().complement();
    assert(all_c.bits == complement_sem_of(0b0000_0111u32, 0b0000_0111u32));
    assert(complement_sem_of(0b0000_0111u32, 0b0000_0111u32) == 0u32) by (bit_vector);

    let full_c = TestFlags::from_bits_retain(0xffff_ffffu32).complement();
    assert(full_c.bits == complement_sem_of(0b0000_0111u32, 0xffff_ffffu32));
    assert(complement_sem_of(0b0000_0111u32, 0xffff_ffffu32) == 0u32) by (bit_vector);

    let c_c = TestFlags::C.complement();
    assert(c_c.bits == complement_sem_of(0b0000_0111u32, 0b0000_0100u32));
    assert(complement_sem_of(0b0000_0111u32, 0b0000_0100u32) == 0b0000_0011u32) by (bit_vector);

    // the complement of (C | 0x8): the unknown bit gets truncated (complement.rs:14-17)
    let cf0 = TestFlags::C.union(TestFlags::from_bits_retain(0b1000u32));
    assert(cf0.bits == union_sem(0b0000_0100u32, 0b0000_1000u32));
    assert(union_sem(0b0000_0100u32, 0b0000_1000u32) == 0b0000_1100u32) by (bit_vector);
    let cf1 = cf0.complement();
    assert(cf1.bits == complement_sem_of(0b0000_0111u32, 0b0000_1100u32));
    assert(complement_sem_of(0b0000_0111u32, 0b0000_1100u32) == 0b0000_0011u32) by (bit_vector);

    let e_c = TestFlags::empty().complement();
    assert(e_c.bits == complement_sem_of(0b0000_0111u32, 0u32));
    assert(complement_sem_of(0b0000_0111u32, 0u32) == 0b0000_0111u32) by (bit_vector);

    let u_c = TestFlags::from_bits_retain(0b1000u32).complement();
    assert(u_c.bits == complement_sem_of(0b0000_0111u32, 0b0000_1000u32));
    assert(complement_sem_of(0b0000_0111u32, 0b0000_1000u32) == 0b0000_0111u32) by (bit_vector);

    // the monomorphized trait-default-body side (mask = 0b111)
    let t1 = flags_complement(0b0000_0111u32, 0b0000_0111u32);
    assert(t1 == complement_sem_of(0b0000_0111u32, 0b0000_0111u32));
    let t2 = flags_complement(0b0000_0111u32, 0b0000_0100u32);
    assert(t2 == complement_sem_of(0b0000_0111u32, 0b0000_0100u32));
    let t3 = flags_complement(0b0000_0111u32, 0u32);
    assert(t3 == complement_sem_of(0b0000_0111u32, 0u32));
}

// ---------- contains.rs ----------
exec fn ut_contains()
{
    let e = TestFlags::empty();
    let a = TestFlags::A;
    let abc = TestFlags::ABC;
    let u8v = TestFlags::from_bits_retain(0b1000u32);
    // the upstream table (contains.rs), line by line:
    let c0 = e.contains(&a);
    assert(c0 == contains_sem(0u32, 0b0000_0001u32));
    assert(contains_sem(0u32, 0b0000_0001u32) == false) by (bit_vector);

    let a0 = a.contains(&e);
    assert(a0 == contains_sem(0b0000_0001u32, 0u32));
    assert(contains_sem(0b0000_0001u32, 0u32) == true) by (bit_vector);

    let a1 = a.contains(&TestFlags::A);
    assert(a1 == contains_sem(0b0000_0001u32, 0b0000_0001u32));
    assert(contains_sem(0b0000_0001u32, 0b0000_0001u32) == true) by (bit_vector);

    let a2 = a.contains(&TestFlags::B);
    assert(a2 == contains_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(contains_sem(0b0000_0001u32, 0b0000_0010u32) == false) by (bit_vector);

    let a3 = a.contains(&TestFlags::ABC);
    assert(a3 == contains_sem(0b0000_0001u32, 0b0000_0111u32));
    assert(contains_sem(0b0000_0001u32, 0b0000_0111u32) == false) by (bit_vector);

    let a4 = a.contains(&u8v);
    assert(a4 == contains_sem(0b0000_0001u32, 0b0000_1000u32));
    assert(contains_sem(0b0000_0001u32, 0b0000_1000u32) == false) by (bit_vector);

    let a5 = a.contains(&TestFlags::from_bits_retain(0b1001u32));
    assert(a5 == contains_sem(0b0000_0001u32, 0b0000_1001u32));
    assert(contains_sem(0b0000_0001u32, 0b0000_1001u32) == false) by (bit_vector);

    let k1 = abc.contains(&TestFlags::A);
    assert(k1 == contains_sem(0b0000_0111u32, 0b0000_0001u32));
    assert(contains_sem(0b0000_0111u32, 0b0000_0001u32) == true) by (bit_vector);

    let k4 = abc.contains(&TestFlags::ABC);
    assert(k4 == contains_sem(0b0000_0111u32, 0b0000_0111u32));
    assert(contains_sem(0b0000_0111u32, 0b0000_0111u32) == true) by (bit_vector);

    let k5 = abc.contains(&u8v);
    assert(k5 == contains_sem(0b0000_0111u32, 0b0000_1000u32));
    assert(contains_sem(0b0000_0111u32, 0b0000_1000u32) == false) by (bit_vector);

    let u2 = u8v.contains(&u8v);
    assert(u2 == contains_sem(0b0000_1000u32, 0b0000_1000u32));
    assert(contains_sem(0b0000_1000u32, 0b0000_1000u32) == true) by (bit_vector);

    let tc1 = flags_contains(0b0000_0111u32, 0b0000_0101u32);
    assert(tc1 == contains_sem(0b0000_0111u32, 0b0000_0101u32));
    assert(contains_sem(0b0000_0111u32, 0b0000_0101u32) == true) by (bit_vector);
    let tc2 = flags_contains(0b0000_0110u32, 0b0000_0101u32);
    assert(tc2 == contains_sem(0b0000_0110u32, 0b0000_0101u32));
    assert(contains_sem(0b0000_0110u32, 0b0000_0101u32) == false) by (bit_vector);
}

// ---------- difference.rs ----------
exec fn ut_difference()
{
    let ab = TestFlags::A.union(TestFlags::B);
    assert(ab.bits == union_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(union_sem(0b0000_0001u32, 0b0000_0010u32) == 0b0000_0011u32) by (bit_vector);
    let d1 = ab.difference(TestFlags::A);
    assert(d1.bits == difference_sem(0b0000_0011u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_0011u32, 0b0000_0001u32) == 0b0000_0010u32) by (bit_vector);

    let d2 = TestFlags::B.difference(TestFlags::A);
    assert(d2.bits == difference_sem(0b0000_0010u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_0010u32, 0b0000_0001u32) == 0b0000_0010u32) by (bit_vector);

    let d3 = TestFlags::from_bits_retain(0b1001u32).difference(TestFlags::A);
    assert(d3.bits == difference_sem(0b0000_1001u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_1001u32, 0b0000_0001u32) == 0b0000_1000u32) by (bit_vector);

    // difference vs `self & !other` (the Not path truncates) (difference.rs:30-38)
    let full = TestFlags::from_bits_retain(0xffff_ffffu32);
    let df = full.difference(TestFlags::A);
    assert(df.bits == difference_sem(0xffff_ffffu32, 0b0000_0001u32));
    assert(difference_sem(0xffff_ffffu32, 0b0000_0001u32) == 0xffff_fffeu32) by (bit_vector);

    let knownside = TestFlags::from_bits_truncate(0xffff_ffffu32);
    assert(knownside.bits == truncate_sem_of(0b0000_0111u32, 0xffff_ffffu32));
    assert(truncate_sem_of(0b0000_0111u32, 0xffff_ffffu32) == 0b0000_0111u32) by (bit_vector);
    let dk = knownside.difference(TestFlags::A);
    assert(dk.bits == difference_sem(0b0000_0111u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_0111u32, 0b0000_0001u32) == 0b0000_0110u32) by (bit_vector);

    let t = flags_difference(0b0000_1001u32, 0b0000_0001u32);
    assert(t == difference_sem(0b0000_1001u32, 0b0000_0001u32));
}

// ---------- intersection.rs ----------
exec fn ut_intersection()
{
    let e = TestFlags::empty();
    let all = TestFlags::all();
    let i0 = e.intersection(all);
    assert(i0.bits == intersection_sem(0u32, 0b0000_0111u32));
    assert(intersection_sem(0u32, 0b0000_0111u32) == 0u32) by (bit_vector);

    let i2 = all.intersection(all);
    assert(i2.bits == intersection_sem(0b0000_0111u32, 0b0000_0111u32));
    assert(intersection_sem(0b0000_0111u32, 0b0000_0111u32) == 0b0000_0111u32) by (bit_vector);

    let i3 = all.intersection(TestFlags::A);
    assert(i3.bits == intersection_sem(0b0000_0111u32, 0b0000_0001u32));
    assert(intersection_sem(0b0000_0111u32, 0b0000_0001u32) == 0b0000_0001u32) by (bit_vector);

    let i4 = all.intersection(TestFlags::from_bits_retain(0b1000u32));
    assert(i4.bits == intersection_sem(0b0000_0111u32, 0b0000_1000u32));
    assert(intersection_sem(0b0000_0111u32, 0b0000_1000u32) == 0u32) by (bit_vector);
}

// ---------- intersects.rs ----------
exec fn ut_intersects()
{
    let a = TestFlags::A;
    let x0 = a.intersects(&TestFlags::empty());
    assert(x0 == intersects_sem(0b0000_0001u32, 0u32));
    assert(intersects_sem(0b0000_0001u32, 0u32) == false) by (bit_vector);

    let x1 = a.intersects(&TestFlags::ABC);
    assert(x1 == intersects_sem(0b0000_0001u32, 0b0000_0111u32));
    assert(intersects_sem(0b0000_0001u32, 0b0000_0111u32) == true) by (bit_vector);

    let x2 = a.intersects(&TestFlags::B);
    assert(x2 == intersects_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(intersects_sem(0b0000_0001u32, 0b0000_0010u32) == false) by (bit_vector);

    let x5 = a.intersects(&TestFlags::from_bits_retain(0b1001u32));
    assert(x5 == intersects_sem(0b0000_0001u32, 0b0000_1001u32));
    assert(intersects_sem(0b0000_0001u32, 0b0000_1001u32) == true) by (bit_vector);

    let t1 = flags_intersects(0b0000_0111u32, 0b1000_0000u32);
    assert(t1 == intersects_sem(0b0000_0111u32, 0b1000_0000u32));
    assert(intersects_sem(0b0000_0111u32, 0b1000_0000u32) == false) by (bit_vector);
    let t2 = flags_intersects(0b0000_0111u32, 0b0000_0010u32);
    assert(t2 == intersects_sem(0b0000_0111u32, 0b0000_0010u32));
    assert(intersects_sem(0b0000_0111u32, 0b0000_0010u32) == true) by (bit_vector);
}

// ---------- is_all.rs ----------
exec fn ut_is_all()
{
    let s0 = TestFlags::empty().is_all();
    assert(s0 == is_all_sem_of(0b0000_0111u32, 0u32));
    assert(is_all_sem_of(0b0000_0111u32, 0u32) == false) by (bit_vector);

    let s1 = TestFlags::A.is_all();
    assert(s1 == is_all_sem_of(0b0000_0111u32, 0b0000_0001u32));
    assert(is_all_sem_of(0b0000_0111u32, 0b0000_0001u32) == false) by (bit_vector);

    let s2 = TestFlags::ABC.is_all();
    assert(s2 == is_all_sem_of(0b0000_0111u32, 0b0000_0111u32));
    assert(is_all_sem_of(0b0000_0111u32, 0b0000_0111u32) == true) by (bit_vector);

    // ABC | 0x8 is still is_all (unknown bits do not interfere) (is_all.rs:16-20)
    let x = TestFlags::ABC.union(TestFlags::from_bits_retain(0b1000u32));
    assert(x.bits == union_sem(0b0000_0111u32, 0b0000_1000u32));
    assert(union_sem(0b0000_0111u32, 0b0000_1000u32) == 0b0000_1111u32) by (bit_vector);
    let s3 = x.is_all();
    assert(s3 == is_all_sem_of(0b0000_0111u32, 0b0000_1111u32));
    assert(is_all_sem_of(0b0000_0111u32, 0b0000_1111u32) == true) by (bit_vector);

    let t3 = flags_is_all(0b0000_0111u32, 0xffff_ffffu32);
    assert(t3 == is_all_sem_of(0b0000_0111u32, 0xffff_ffffu32));
    assert(is_all_sem_of(0b0000_0111u32, 0xffff_ffffu32) == true) by (bit_vector);
}

// ---------- is_empty.rs ----------
exec fn ut_is_empty()
{
    let s0 = TestFlags::empty().is_empty();
    assert(s0 == is_empty_sem(0u32));
    assert(is_empty_sem(0u32) == true) by (bit_vector);

    let s1 = TestFlags::A.is_empty();
    assert(s1 == is_empty_sem(0b0000_0001u32));
    assert(is_empty_sem(0b0000_0001u32) == false) by (bit_vector);

    let s3 = TestFlags::from_bits_retain(0b1000u32).is_empty();
    assert(s3 == is_empty_sem(0b0000_1000u32));
    assert(is_empty_sem(0b0000_1000u32) == false) by (bit_vector);
}

// ---------- known_bits.rs ----------
exec fn ut_known_bits()
{
    let t0 = flags_known_bits(0b0000_0111u32, 0u32);
    assert(t0 == truncate_sem_of(0b0000_0111u32, 0u32));
    assert(truncate_sem_of(0b0000_0111u32, 0u32) == 0u32) by (bit_vector);

    let t2 = flags_known_bits(0b0000_0111u32, 0b0000_0111u32);
    assert(t2 == truncate_sem_of(0b0000_0111u32, 0b0000_0111u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_0111u32) == 0b0000_0111u32) by (bit_vector);

    // known_bits of ABC | 0x8 == A|B|C (known_bits.rs:15-19)
    let k = flags_known_bits(0b0000_0111u32, 0b0000_1111u32);
    assert(k == truncate_sem_of(0b0000_0111u32, 0b0000_1111u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1111u32) == 0b0000_0111u32) by (bit_vector);

    let t3 = flags_known_bits(0b0000_0111u32, 0b0000_1000u32);
    assert(t3 == truncate_sem_of(0b0000_0111u32, 0b0000_1000u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1000u32) == 0u32) by (bit_vector);
}

// ---------- unknown_bits.rs / unknown.rs ----------
exec fn ut_unknown_bits()
{
    let u1 = flags_unknown_bits(0b0000_0111u32, 0b0000_1000u32);
    assert(u1 == 0b0000_1000u32 & !0b0000_0111u32);
    assert(0b0000_1000u32 & !0b0000_0111u32 == 0b0000_1000u32) by (bit_vector);

    let u2 = flags_unknown_bits(0b0000_0111u32, 0b1111_1111u32);
    assert(u2 == 0b1111_1111u32 & !0b0000_0111u32);
    assert(0b1111_1111u32 & !0b0000_0111u32 == 0b1111_1000u32) by (bit_vector);

    // the positive/negative cases of contains_unknown_bits (unknown.rs)
    assert(0b0000_1000u32 & !0b0000_0111u32 != 0u32) by (bit_vector);
    let c1 = flags_contains_unknown_bits(0b0000_0111u32, 0b0000_1000u32);
    assert(c1 == true);
    assert(0b0000_0111u32 & !0b0000_0111u32 == 0u32) by (bit_vector);
    let c0 = flags_contains_unknown_bits(0b0000_0111u32, 0b0000_0111u32);
    assert(c0 == false);
    assert(0u32 & !0b0000_0111u32 == 0u32) by (bit_vector);
    let c2 = flags_contains_unknown_bits(0b0000_0111u32, 0u32);
    assert(c2 == false);
}

// ---------- union.rs ----------
exec fn ut_union()
{
    let e = TestFlags::empty();
    let u0 = e.union(TestFlags::A);
    assert(u0.bits == union_sem(0u32, 0b0000_0001u32));
    assert(union_sem(0u32, 0b0000_0001u32) == 0b0000_0001u32) by (bit_vector);

    let u1 = e.union(TestFlags::all());
    assert(u1.bits == union_sem(0u32, 0b0000_0111u32));
    assert(union_sem(0u32, 0b0000_0111u32) == 0b0000_0111u32) by (bit_vector);

    let u2 = e.union(TestFlags::from_bits_retain(0b1000u32));
    assert(u2.bits == union_sem(0u32, 0b0000_1000u32));
    assert(union_sem(0u32, 0b0000_1000u32) == 0b0000_1000u32) by (bit_vector);

    let uab = TestFlags::A.union(TestFlags::B);
    assert(uab.bits == union_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(union_sem(0b0000_0001u32, 0b0000_0010u32) == 0b0000_0011u32) by (bit_vector);
    let u3 = uab.union(TestFlags::C);
    assert(u3.bits == union_sem(0b0000_0011u32, 0b0000_0100u32));
    assert(union_sem(0b0000_0011u32, 0b0000_0100u32) == 0b0000_0111u32) by (bit_vector);
}

// ---------- insert.rs / set(_, true) ----------
exec fn ut_insert_set()
{
    let mut f = TestFlags::empty();
    f.insert(TestFlags::A);
    assert(f.bits == union_sem(0u32, 0b0000_0001u32));
    assert(union_sem(0u32, 0b0000_0001u32) == 0b0000_0001u32) by (bit_vector);
    f.insert(TestFlags::B);
    assert(f.bits == union_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(union_sem(0b0000_0001u32, 0b0000_0010u32) == 0b0000_0011u32) by (bit_vector);
    f.insert(TestFlags::C);
    assert(f.bits == union_sem(0b0000_0011u32, 0b0000_0100u32));
    assert(union_sem(0b0000_0011u32, 0b0000_0100u32) == 0b0000_0111u32) by (bit_vector);
    f.insert(TestFlags::from_bits_retain(0b1000u32));
    assert(f.bits == union_sem(0b0000_0111u32, 0b0000_1000u32));
    assert(union_sem(0b0000_0111u32, 0b0000_1000u32) == 0b0000_1111u32) by (bit_vector);
    let mut g = TestFlags::A;
    g.set(TestFlags::B, true);
    assert(g.bits == union_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(union_sem(0b0000_0001u32, 0b0000_0010u32) == 0b0000_0011u32) by (bit_vector);
    // the trait-default-body mut form
    let mut v: u32 = 0b0000_0001u32;
    flags_insert(&mut v, 0b0000_0010u32);
    assert(v == union_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(union_sem(0b0000_0001u32, 0b0000_0010u32) == 0b0000_0011u32) by (bit_vector);
}

// ---------- remove.rs / set(_, false) ----------
exec fn ut_remove_set()
{
    let mut f = TestFlags::ABC;
    f.remove(TestFlags::A);
    assert(f.bits == difference_sem(0b0000_0111u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_0111u32, 0b0000_0001u32) == 0b0000_0110u32) by (bit_vector);
    let ac = TestFlags::A.union(TestFlags::C);
    assert(ac.bits == union_sem(0b0000_0001u32, 0b0000_0100u32));
    assert(union_sem(0b0000_0001u32, 0b0000_0100u32) == 0b0000_0101u32) by (bit_vector);
    f.remove(ac);
    assert(f.bits == difference_sem(0b0000_0110u32, 0b0000_0101u32));
    assert(difference_sem(0b0000_0110u32, 0b0000_0101u32) == 0b0000_0010u32) by (bit_vector);
    let mut g = TestFlags::A;
    g.set(TestFlags::A, false);
    assert(g.bits == difference_sem(0b0000_0001u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_0001u32, 0b0000_0001u32) == 0u32) by (bit_vector);
    let mut v: u32 = 0b0000_0011u32;
    flags_remove(&mut v, 0b0000_0001u32);
    assert(v == difference_sem(0b0000_0011u32, 0b0000_0001u32));
    assert(difference_sem(0b0000_0011u32, 0b0000_0001u32) == 0b0000_0010u32) by (bit_vector);
    flags_set(&mut v, 0b0000_1000u32, true);
    assert(v == union_sem(0b0000_0010u32, 0b0000_1000u32));
    assert(union_sem(0b0000_0010u32, 0b0000_1000u32) == 0b0000_1010u32) by (bit_vector);
    assert(union_sem(0b0000_0010u32, 0b0000_1000u32) == 0b0000_1010u32) by (bit_vector);
    flags_set(&mut v, 0b0000_1010u32, false);
    assert(v == difference_sem(0b0000_1010u32, 0b0000_1010u32));
    assert(difference_sem(0b0000_1010u32, 0b0000_1010u32) == 0u32) by (bit_vector);
}

// ---------- symmetric_difference.rs / toggle ----------
exec fn ut_symmetric_difference_toggle()
{
    let mut f = TestFlags::A;
    f.toggle(TestFlags::all());
    assert(f.bits == symmetric_difference_sem(0b0000_0001u32, 0b0000_0111u32));
    assert(symmetric_difference_sem(0b0000_0001u32, 0b0000_0111u32) == 0b0000_0110u32) by (bit_vector);
    let d0 = TestFlags::A.symmetric_difference(TestFlags::empty());
    assert(d0.bits == symmetric_difference_sem(0b0000_0001u32, 0u32));
    assert(symmetric_difference_sem(0b0000_0001u32, 0u32) == 0b0000_0001u32) by (bit_vector);
    let d1 = TestFlags::A.symmetric_difference(TestFlags::A);
    assert(d1.bits == symmetric_difference_sem(0b0000_0001u32, 0b0000_0001u32));
    assert(symmetric_difference_sem(0b0000_0001u32, 0b0000_0001u32) == 0u32) by (bit_vector);
    // A ^ B ^ B == A (the toggling algebra of the upstream symmetric_difference.rs)
    let x = TestFlags::A;
    let y = TestFlags::B;
    let t = x.symmetric_difference(y).symmetric_difference(y);
    assert(t.bits == symmetric_difference_sem(symmetric_difference_sem(0b0000_0001u32, 0b0000_0010u32), 0b0000_0010u32));
    assert(symmetric_difference_sem(symmetric_difference_sem(0b0000_0001u32, 0b0000_0010u32), 0b0000_0010u32)
        == 0b0000_0001u32) by (bit_vector);
    let mut w: u32 = 0b0000_0001u32;
    flags_toggle(&mut w, 0b0000_0010u32);
    assert(w == symmetric_difference_sem(0b0000_0001u32, 0b0000_0010u32));
    assert(symmetric_difference_sem(0b0000_0001u32, 0b0000_0010u32) == 0b0000_0011u32) by (bit_vector);
}

// ---------- truncate.rs (mut form) ----------
exec fn ut_truncate_mut()
{
    let f0 = TestFlags::ABC.union(TestFlags::from_bits_retain(0b1000u32));
    assert(f0.bits == union_sem(0b0000_0111u32, 0b0000_1000u32));
    assert(union_sem(0b0000_0111u32, 0b0000_1000u32) == 0b0000_1111u32) by (bit_vector);
    let f = TestFlags::from_bits_truncate(f0.bits);
    assert(f.bits == truncate_sem_of(0b0000_0111u32, 0b0000_1111u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1111u32) == 0b0000_0111u32) by (bit_vector);
    let mut v: u32 = 0b0000_1000u32;
    flags_truncate(0b0000_0111u32, &mut v);
    assert(v == truncate_sem_of(0b0000_0111u32, 0b0000_1000u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1000u32) == 0u32) by (bit_vector);
    let mut w: u32 = 0b1000_0110u32;
    flags_truncate(0b0000_0111u32, &mut w);
    assert(w == truncate_sem_of(0b0000_0111u32, 0b1000_0110u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b1000_0110u32) == 0b0000_0110u32) by (bit_vector);
}

// ---------- from_bits.rs ----------
exec fn ut_from_bits()
{
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_0111u32) == 0b0000_0111u32) by (bit_vector);
    let r2 = TestFlags::from_bits(0b0000_0111u32);
    assert(r2.is_some());
    // unknown bits => None (from_bits.rs:22-23)
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1000u32) == 0u32) by (bit_vector);
    let r3 = TestFlags::from_bits(0b0000_1000u32);
    assert(r3.is_none());
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1001u32) == 0b0000_0001u32) by (bit_vector);
    let r4 = TestFlags::from_bits(0b0000_1001u32);
    assert(r4.is_none());
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1000u32) == 0u32) by (bit_vector);
    let t0 = flags_from_bits(0b0000_0111u32, 0b0000_1000u32);
    assert(t0.is_none());
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_0101u32) == 0b0000_0101u32) by (bit_vector);
    let t1 = flags_from_bits(0b0000_0111u32, 0b0000_0101u32);
    assert(t1.is_some());
}

// ---------- from_bits_truncate.rs ----------
exec fn ut_from_bits_truncate()
{
    let r1 = TestFlags::from_bits_truncate(0b0000_1000u32);
    assert(r1.bits == truncate_sem_of(0b0000_0111u32, 0b0000_1000u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1000u32) == 0u32) by (bit_vector);
    let r2 = TestFlags::from_bits_truncate(0b0000_1001u32);
    assert(r2.bits == truncate_sem_of(0b0000_0111u32, 0b0000_1001u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b0000_1001u32) == 0b0000_0001u32) by (bit_vector);
    let t0 = flags_from_bits_truncate(0b0000_0111u32, 0b1111_0000u32);
    assert(t0 == truncate_sem_of(0b0000_0111u32, 0b1111_0000u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b1111_0000u32) == 0u32) by (bit_vector);
    let t1 = flags_from_bits_truncate(0b0000_0111u32, 0b1000_0101u32);
    assert(t1 == truncate_sem_of(0b0000_0111u32, 0b1000_0101u32));
    assert(truncate_sem_of(0b0000_0111u32, 0b1000_0101u32) == 0b0000_0101u32) by (bit_vector);
}

// ---------- from_bits_retain.rs ----------
exec fn ut_from_bits_retain()
{
    let r1 = TestFlags::from_bits_retain(0b0000_1000u32);
    assert(r1.bits == 0b0000_1000u32);
    let r2 = TestFlags::from_bits_retain(0b1000_1001u32);
    assert(r2.bits == 0b1000_1001u32);
}

// ---------- from_name.rs (name-modeling id-check note) ----------
exec fn ut_from_name()
{
    let r0 = TestFlags::from_name(1u64);
    assert(r0.unwrap().bits == 0b0000_0001u32);
    let r1 = TestFlags::from_name(2u64);
    assert(r1.unwrap().bits == 0b0000_0010u32);
    let r2 = TestFlags::from_name(4u64);
    assert(r2.unwrap().bits == 0b0000_0111u32);
    let r3 = TestFlags::from_name(0u64); // "" (empty name, from_name.rs:10)
    assert(r3.is_none());
    let r4 = TestFlags::from_name(999u64); // an id outside the table (in the "a"/"0x1"/"A | B" class)
    assert(r4.is_none());
}

// ---------- flags.rs / flag_name.rs: the FLAGS table and the Flag accessors ----------
exec fn ut_flags_table()
{
    use bfsrc::traits::Flag;
    let f = Flag::new(1u64, 0b0000_0001u32);
    let nm = f.is_named();
    assert(nm);
    let unn = f.is_unnamed();
    assert(!unn);
    let n = f.name();
    assert(n == 1u64);
    let vb = f.value_bits_fn();
    assert(vb == 0b0000_0001u32);
    let flag_unnamed = Flag::new(0u64, 0xffff_ffffu32);
    let n2 = flag_unnamed.is_named();
    assert(!n2);
    let u2 = flag_unnamed.is_unnamed();
    assert(u2);
    let b0 = bfsrc::traits::flag_bits_at(0);
    let b1 = bfsrc::traits::flag_bits_at(1);
    let b2 = bfsrc::traits::flag_bits_at(2);
    let b3 = bfsrc::traits::flag_bits_at(3);
    assert(b0 == 0b0000_0001u32);
    assert(b1 == 0b0000_0010u32);
    assert(b2 == 0b0000_0100u32);
    assert(b3 == 0b0000_0111u32);
    assert(NUM_FLAGS == 4usize);
}

// ---------- a qualitative next on a fresh IterNames state (model witness) ----------
exec fn ut_drain_smoke()
{
    let it = IterNames::new(0u32);
    let (o1, s1) = it.next();
    assert(o1.is_none());
    let _ = s1;
}

fn main() {}
}
