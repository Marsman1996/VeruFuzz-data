//! harness: the spec.md theorem list (bitflags's officially maintained semantic doc,
//! code/spec.md)
//! -- migrated and extended from the legacy PoC verified/bitflags_u32.rs
//! (reference-style organization: specs live only in the src copy).
//!
//! spec.md section -> this file's fns:
//!   sec. Union -> t_union_neutral_zero / t_union_assoc
//!   sec. Intersection -> t_intersection_idempotent / t_intersection_absorbs_known
//!   sec. Contains -> t_contains_reflexive / t_contains_transitive
//!   sec. Intersects -> t_intersects_examples
//!   sec. Empty/sec. All -> t_all_contains_every_defined_flag /
//!                        t_empty_all_examples /
//!                 t_all_iff_mask_subset
//!   sec. Truncate -> t_truncate_idempotent /
//!                      t_truncated_nonempty_contains_defined_flag /
//!               t_truncate_union_closed
//!   sec. Complement -> t_double_complement_is_truncate / t_complement_has_no_unknown
//!   sec. Difference -> t_difference_is_not_complemented_intersection (the
//!                      spec.md text warning)
//!   the Operations algebra -> t_remove_cancels_insert / t_toggle_twice_identity

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bfsrc;

use bfsrc::traits::{
    complement_sem_of, contains_sem, difference_sem, from_name_lookup, intersection_sem,
    intersects_sem, is_all_sem_of, is_empty_sem, symmetric_difference_sem, truncate_sem_of,
    union_sem, tflags_all_bits,
};

verus! {

// ---------------------------------------------------------------------------
// Proof lemmas (the t_* theorem list: the entire verus! body of this file is
// standalone proof fns)
// ---------------------------------------------------------------------------
// ------------------- sec. Union -------------------

proof fn t_union_neutral_zero(a: u32)
    ensures union_sem(a, 0u32) == a
{
    assert(a | 0u32 == a) by (bit_vector);
}

proof fn t_union_assoc(a: u32, b: u32, c: u32)
    ensures union_sem(union_sem(a, b), c) == union_sem(a, union_sem(b, c))
{
    assert(((a | b) | c) == (a | (b | c))) by (bit_vector);
}

// ------------------- sec. Intersection -------------------

proof fn t_intersection_idempotent(a: u32)
    ensures intersection_sem(a, a) == a
{
    assert(a & a == a) by (bit_vector);
}

/// for this instance: the intersection with all() is exactly the known bits
proof fn t_intersection_absorbs_known(a: u32)
    ensures intersection_sem(a, tflags_all_bits()) == truncate_sem_of(tflags_all_bits(), a)
{
    assert(a & 0b0000_0111u32 == a & 0b0000_0111u32) by (bit_vector);
}

// ------------------- sec. Contains / sec. Intersects -------------------

proof fn t_contains_reflexive(a: u32)
    ensures contains_sem(a, a) == true
{
    assert(a & a == a) by (bit_vector);
}

proof fn t_contains_transitive(a: u32, b: u32, c: u32)
    requires contains_sem(a, b), contains_sem(b, c)
    ensures contains_sem(a, c)
{
    assert(a & b == b && b & c == c ==> a & c == c) by (bit_vector);
}

/// the two verbatim cases of spec.md sec. Intersects are machine-checked
proof fn t_intersects_examples()
    ensures
        intersects_sem(0b0000_0011u32, 0b0000_0010u32),
        !intersects_sem(0b0000_0011u32, 0b1111_0000u32),
        intersects_sem(0b0000_0011u32, 0b1111_1111u32),
        !intersects_sem(0b0000_0011u32, 0u32),
{
    assert(0b0000_0011u32 & 0b0000_0010u32 == 0b0000_0010u32) by (bit_vector);
    assert(0b0000_0011u32 & 0b1111_0000u32 == 0u32) by (bit_vector);
    assert(0b0000_0011u32 & 0b1111_1111u32 == 0b0000_0011u32) by (bit_vector);
    assert(0b0000_0011u32 & 0u32 == 0u32) by (bit_vector);
}

// ------------------- sec. All / sec. Empty -------------------

/// all() contains every defined flag (each of A/B/C is contained in all)
proof fn t_all_contains_every_defined_flag()
    ensures
        contains_sem(tflags_all_bits(), 0b0000_0001u32),
        contains_sem(tflags_all_bits(), 0b0000_0010u32),
        contains_sem(tflags_all_bits(), 0b0000_0100u32),
{
    assert(0b0000_0111u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
    assert(0b0000_0111u32 & 0b0000_0010u32 == 0b0000_0010u32) by (bit_vector);
    assert(0b0000_0111u32 & 0b0000_0100u32 == 0b0000_0100u32) by (bit_vector);
}

/// the two cases of spec.md sec. All/sec. Empty: 0b011 is contained in
/// full; 0b001 is not; 0 is fully empty; 001 is non-empty
proof fn t_empty_all_examples()
    ensures
        is_all_sem_of(tflags_all_bits(), 0b0000_0111u32) == true,
        is_all_sem_of(tflags_all_bits(), 0b0000_0001u32) == false,
        is_empty_sem(0u32) == true,
        is_empty_sem(0b0000_0001u32) == false,
        is_all_sem_of(tflags_all_bits(), 0xffff_ffffu32) == true,
        is_all_sem_of(tflags_all_bits(), 0b1000_0111u32) == true,
{
    assert(0b0000_0111u32 & 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
    assert(!(0b0000_0001u32 & 0b0000_0111u32 == 0b0000_0111u32)) by (bit_vector);
    assert(0xffff_ffffu32 & 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
    assert(0b1000_0111u32 & 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
}

/// the equivalent form of is_all (the traits.rs `is_all` body vs the contains view)
proof fn t_all_iff_mask_subset(v: u32)
    ensures is_all_sem_of(tflags_all_bits(), v)
        == (0b0000_0111u32 | v == v)
{
    assert((v & 0b0000_0111u32 == 0b0000_0111u32) == (0b0000_0111u32 | v == v))
        by (bit_vector);
}

// ------------------- sec. Truncate -------------------

/// truncate is idempotent: after truncation no unknown bits remain, and a
/// second truncation changes nothing
proof fn t_truncate_idempotent(b: u32)
    ensures
        truncate_sem_of(tflags_all_bits(), truncate_sem_of(tflags_all_bits(), b))
            == truncate_sem_of(tflags_all_bits(), b),
{
    assert((b & 0b0000_0111u32) & 0b0000_0111u32 == b & 0b0000_0111u32) by (bit_vector);
}

/// the instance conclusion of spec.md sec. Truncate: the single-bit A/B/C flags
/// imply that a non-empty known result must contain some defined flag
proof fn t_truncated_nonempty_contains_defined_flag(b: u32)
    ensures (b & 0b0000_0111u32) != 0u32
        ==> (
            (b & 0b0000_0111u32 & 0b0000_0001u32) == 0b0000_0001u32
            || (b & 0b0000_0111u32 & 0b0000_0010u32) == 0b0000_0010u32
            || (b & 0b0000_0111u32 & 0b0000_0100u32) == 0b0000_0100u32
        )
{
    assert(b & 0b0000_0111u32 != 0u32 ==>
           (b & 0b0000_0111u32 & 0b0000_0001u32 == 0b0000_0001u32 ||
            b & 0b0000_0111u32 & 0b0000_0010u32 == 0b0000_0010u32 ||
            b & 0b0000_0111u32 & 0b0000_0100u32 == 0b0000_0100u32)) by (bit_vector);
}

/// the union of two truncated values stays inside the truncated domain (the
/// safety precondition after composed operations)
proof fn t_truncate_union_closed(b1: u32, b2: u32)
    ensures truncate_sem_of(tflags_all_bits(),
        union_sem(truncate_sem_of(tflags_all_bits(), b1),
            truncate_sem_of(tflags_all_bits(), b2)))
        == union_sem(truncate_sem_of(tflags_all_bits(), b1),
            truncate_sem_of(tflags_all_bits(), b2))
{
    assert(((b1 & 0b0000_0111u32) | (b2 & 0b0000_0111u32)) & 0b0000_0111u32
        == ((b1 & 0b0000_0111u32) | (b2 & 0b0000_0111u32))) by (bit_vector);
}

// ------------------- sec. Complement -------------------

/// spec.md: "complement is the only operation that explicitly truncates its
/// result"; the double complement lands back on truncate
proof fn t_double_complement_is_truncate(b: u32)
    ensures complement_sem_of(tflags_all_bits(),
        complement_sem_of(tflags_all_bits(), b))
        == truncate_sem_of(tflags_all_bits(), b)
{
    assert(!(!b & 0b0000_0111u32) & 0b0000_0111u32 == b & 0b0000_0111u32) by (bit_vector);
}

/// the result of complement contains no unknown bits
proof fn t_complement_has_no_unknown(b: u32)
    ensures truncate_sem_of(tflags_all_bits(),
        complement_sem_of(tflags_all_bits(), b))
        == complement_sem_of(tflags_all_bits(), b)
{
    assert((!b & 0b0000_0111u32) & 0b0000_0111u32 == !b & 0b0000_0111u32) by (bit_vector);
}

// ------------------- sec. Difference (the semantic point spec.md explicitly warns about) ----------
// verbatim text: "This operation is not equivalent to the intersection of one flags
// value with the complement of another (`&!`). The former will truncate the
// result in the complement, where difference will not."

proof fn t_difference_is_not_complemented_intersection()
    ensures
        // complement(EMPTY) == all (the full known set)
        complement_sem_of(tflags_all_bits(), 0u32) == 0b0000_0111u32,
        // difference(unknown-only, EMPTY) == the original value (no truncation)
        difference_sem(0b1111_0000u32, 0u32) == 0b1111_0000u32,
        // intersection(unknown-only, complement(EMPTY)) == 0 (the truncation happens)
        intersection_sem(0b1111_0000u32, complement_sem_of(tflags_all_bits(), 0u32))
            == 0u32,
        // the two differ: difference != "intersection with complement"
        difference_sem(0b1111_0000u32, 0u32)
            != intersection_sem(0b1111_0000u32, complement_sem_of(tflags_all_bits(), 0u32)),
{
    assert(!0u32 & 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
    assert(0b1111_0000u32 & !0u32 == 0b1111_0000u32) by (bit_vector);
    assert(0b1111_0000u32 & 0b0000_0111u32 == 0u32) by (bit_vector);
}

// ------------------- the algebra of insert/remove/toggle -------------------

/// remove cancels insert (the tests.rs toggle/insert/remove-type checks)
proof fn t_remove_cancels_insert(a: u32, b: u32)
    ensures difference_sem(union_sem(a, b), b) == difference_sem(a, b)
{
    assert((a | b) & !(b) == a & !(b)) by (bit_vector);
}

/// a double toggle of the symmetric difference restores the original value
proof fn t_toggle_twice_identity(a: u32, b: u32)
    ensures symmetric_difference_sem(symmetric_difference_sem(a, b), b) == a
{
    assert((a ^ b) ^ b == a) by (bit_vector);
}

// ------------------- the machine-check of the "Zero-bit flags" claims of the lib.rs docs -------------------
// Original text (code/src/lib.rs, "Zero-bit flags"): "A zero-bit flag is always contained,
// but is never intersected. The names of zero-bit flags can be parsed, but are
// never formatted." -- claims (1)/(2) admit universal bit-level proofs; (3) at the
// parsing layer it is a name-table lookup
// (the value plays no part in the lookup condition); (4) "not formatted" means
// never-yielded: the upstream yield condition
// `remaining.intersects(bits)` (iter.rs:135) is always false when bits == 0.

proof fn t_zero_flag_always_contained(s: u32)
    ensures contains_sem(s, 0u32) == true
{
    assert(s & 0u32 == 0u32) by (bit_vector);
}

proof fn t_zero_flag_never_intersects(any: u32)
    ensures intersects_sem(any, 0u32) == false
{
    assert(any & 0u32 != 0u32 == false) by (bit_vector);
}

// ------------------- the named-flag lookup model -------------------

/// from_name modeled over the full table: all 4 names hit, all other ids give
/// None
proof fn t_from_name_table_total()
    ensures
        from_name_lookup(1u64) == Option::Some(0b0000_0001u32),
        from_name_lookup(2u64) == Option::Some(0b0000_0010u32),
        from_name_lookup(3u64) == Option::Some(0b0000_0100u32),
        from_name_lookup(4u64) == Option::Some(0b0000_0111u32),
        from_name_lookup(0u64) == Option::None,
        from_name_lookup(999u64) == Option::None,
{
    assert(true);
}

fn main() {}
}
