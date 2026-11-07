//! bitflags 2.13.2 x Verus -- the S2/S3/S4 PoC (per
//! doc/verus-cratesio-verification-design.md)
//!
//! Verification subject: the crates-io crate `bitflags 2.13.2`
//! (source: the `../code/` directory of this crate, downloaded and hash-pinned by `../fetch.sh`)
//! The semantic layer after macro expansion, i.e. the
//!     bitflags! { Flags: u32 { const A = 1; const B = 2; const C = 4; const ABC = A|B|C } }
//! instance of the crate documentation. The semantic bodies come from the `Flags`
//! trait default implementations of `src/traits.rs` (macro-expansion sample per
//! `src/example_generated.rs`).
//!
//! Upstream sources unmodified; .crate SHA-256 =
//!     3ded4057c258ba199e2d26386d3af3780957ecaee6c4ef4041c6b4b8b97c0b06
//!
//! Spec source (S1/L2 mining result): the crate's own `spec.md` -- bitflags's
//! officially maintained "quasi-formal" semantic document. The machine-checkable
//! parts are landed here one by one as Verus theorems; each theorem's comment
//! tags the corresponding spec.md section.
//!
//! Run (M0 PoC, verus-driven single file): `verus bitflags_u32.rs`

use vstd::prelude::*;

verus! {

/* ============================================================
 * L2 spec model -- bitflags `spec.md`, "Definitions" chapter
 * ============================================================ */

/// spec.md sec. Flag: the defined flags of the doc example (u32 instance).
/// The names mirror the flag names of the bitflags ecosystem (A/B/C); the uniform
/// allow suppresses rustc snake_case warnings.
#[allow(nonstandard_style)]
pub open spec fn defined_A() -> u32 { 0b0000_0001u32 }
#[allow(nonstandard_style)]
pub open spec fn defined_B() -> u32 { 0b0000_0010u32 }
#[allow(nonstandard_style)]
pub open spec fn defined_C() -> u32 { 0b0000_0100u32 }

/// The composed flag produced by the macro expansion (ABC = A|B|C): it is redundant
/// over the known bits (spec.md explicitly discusses this "composed flag" shape)
#[allow(nonstandard_style)]
pub open spec fn defined_ABC() -> u32 { defined_A() | defined_B() | defined_C() }

/// spec.md sec. Known bit / sec. Unknown bit -- mirrors `Flags::known_bits`:
/// `self.bits() & Self::all().bits()`; all() of the u32 instance = fold(FLAGS).
#[allow(nonstandard_style)]
pub open spec fn known_bits(v: u32) -> u32 { v & defined_ABC() }

/// spec.md sec. Empty
pub open spec fn is_empty_spec(v: u32) -> bool { v == 0u32 }

/// spec.md sec. All -- "Whether all defined flags are contained in a flags value":
/// a KNOWN subset of v (mirrors `Flags::is_all`: all().bits() | self.bits()
/// == self.bits()). Watch the direction: it is contains(self, KNOWN), not
/// contains(KNOWN, self) (the latter is "all bits of v are known" --
/// a different concept)
pub open spec fn is_all_spec(v: u32) -> bool { contains_flag(v, defined_ABC()) }

/// spec.md sec. Contains -- mirrors `Flags::contains`:
/// `self.bits() & other.bits() == other.bits()`
pub open spec fn contains_flag(a: u32, b: u32) -> bool { a & b == b }

/// spec.md sec. Intersects -- mirrors `Flags::intersects`:
/// `self.bits() & other.bits() != EMPTY`
pub open spec fn intersects_flag(a: u32, b: u32) -> bool { a & b != 0u32 }

/* --- the per-section semantics of spec.md sec. Operations (mirroring the
     traits.rs default implementation bodies) --- */

/// Union -- traits.rs: `Self::from_bits_retain(self.bits() | other.bits())`
pub open spec fn union_sem(a: u32, b: u32) -> u32 { a | b }

/// Intersection -- `self.bits() & other.bits()`
pub open spec fn intersection_sem(a: u32, b: u32) -> u32 { a & b }

/// Symmetric difference -- `^`
pub open spec fn symmetric_difference_sem(a: u32, b: u32) -> u32 { a ^ b }

/// Difference -- traits.rs: `self.bits() & !(other.bits())`.
/// The spec.md text emphasizes: difference does ** not ** truncate;
/// it is not equivalent to "intersection with the complement of another" (see the
/// witness theorem below)
pub open spec fn difference_sem(a: u32, b: u32) -> u32 { a & !b }

/// Complement -- traits.rs: `Self::from_bits_truncate(!self.bits())`
/// -- this is the only operation that explicitly truncates its result (as the
/// spec.md text says)
pub open spec fn complement_sem(a: u32) -> u32 { !a & defined_ABC() }

/// Truncate -- "Unset all unknown bits"
/// (traits.rs: `from_bits_retain(bits & all().bits())`)
pub open spec fn truncate_sem(a: u32) -> u32 { known_bits(a) }

/* ============================================================
 * Execution-layer mirror (S3) -- the semantic bodies line up with traits.rs;
 * each ensures is linked to a spec-layer definition (exec <-> spec);
 * the in-body exec bridge pattern: constant mask lemma + flat congruence.
 * ============================================================ */

#[inline]
/// Upstream doc (traits.rs:345-345):
///   The bitwise or (`|`) of the bits in `self` and `other`.
pub exec fn union(a: u32, b: u32) -> (r: u32)
    ensures r == union_sem(a, b)
{ a | b }

#[inline]
/// Upstream doc (traits.rs:339-339):
///   The bitwise and (`&`) of the bits in `self` and `other`.
pub exec fn intersection(a: u32, b: u32) -> (r: u32)
    ensures r == intersection_sem(a, b)
{ a & b }

#[inline]
/// Upstream doc (traits.rs:360-360):
///   The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
pub exec fn symmetric_difference(a: u32, b: u32) -> (r: u32)
    ensures r == symmetric_difference_sem(a, b)
{ a ^ b }

#[inline]
/// Upstream doc (traits.rs:351-354):
///   The intersection of `self` with the complement of `other` (`&!`).
///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
///   `difference` won't truncate `other`, but the `!` operator will.
pub exec fn difference(a: u32, b: u32) -> (r: u32)
    ensures r == difference_sem(a, b)
{ a & !(b) }

#[inline]
/// Upstream doc (traits.rs:366-366):
///   The bitwise negation (`!`) of the bits in `self`, truncating the result.
pub exec fn complement(a: u32) -> (r: u32)
    ensures r == complement_sem(a)
{
    let r0 = !(a) & 0b0000_0111u32;
    proof {
        lemma_known_mask_value();
        assert(r0 == complement_sem(a));
    }
    r0
}

#[inline]
/// Upstream doc (traits.rs:200-200):
///   Convert from a bits value, unsetting any unknown bits.
pub exec fn from_bits_truncate(b: u32) -> (r: u32)
    ensures r == truncate_sem(b)
{
    let r0 = b & 0b0000_0111u32;
    proof {
        lemma_known_mask_value();
        assert(r0 == truncate_sem(b));
    }
    r0
}

/// traits.rs `from_bits`: truncate first, then check for losslessness
#[inline]
/// Upstream doc (traits.rs:187-189):
///   Convert from a bits value.
///   This method will return `None` if any unknown bits are set.
pub exec fn from_bits(b: u32) -> (r: Option<u32>)
    ensures
        r.is_some() == (b == known_bits(b)),
        if r.is_some() { r.unwrap() == truncate_sem(b) } else { true }
{
    let t = from_bits_truncate(b);
    if t == b { Option::Some(t) } else { Option::None }
}

#[inline]
/// Upstream doc (traits.rs:276-276):
///   Whether all set bits in `other` are also set in `self`.
pub exec fn contains(a: u32, b: u32) -> (r: bool)
    ensures r == contains_flag(a, b)
{ a & b == b }

#[inline]
/// Upstream doc (traits.rs:268-268):
///   Whether any set bits in `other` are also set in `self`.
pub exec fn intersects(a: u32, b: u32) -> (r: bool)
    ensures r == intersects_flag(a, b)
{ a & b != 0u32 }

#[inline]
/// Upstream doc (traits.rs:256-256):
///   Whether all bits in this flags value are unset.
pub exec fn is_empty(a: u32) -> (r: bool)
    ensures r == is_empty_spec(a)
{ a == 0u32 }

/// traits.rs: `Self::all().bits() | self.bits() == self.bits()`
#[inline]
/// Upstream doc (traits.rs:261-261):
///   Whether all known bits in this flags value are set.
pub exec fn is_all(a: u32) -> (r: bool)
    ensures r == is_all_spec(a)
{
    let r0 = 0b0000_0111u32 | a == a;
    proof {
        lemma_known_mask_value();
        assert((0b0000_0111u32 | a == a) == (a & 0b0000_0111u32 == 0b0000_0111u32))
            by (bit_vector);
        assert(r0 == is_all_spec(a));
    }
    r0
}

#[inline]
/// Upstream doc (traits.rs:300-303):
///   The intersection of `self` with the complement of `other` (`&!`).
///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
///   `remove` won't truncate `other`, but the `!` operator will.
pub exec fn remove(a: u32, b: u32) -> (r: u32)
    ensures r == difference_sem(a, b)
{ difference(a, b) }

#[inline]
/// Upstream doc (traits.rs:292-292):
///   The bitwise or (`|`) of the bits in `self` and `other`.
pub exec fn insert(a: u32, b: u32) -> (r: u32)
    ensures r == union_sem(a, b)
{ union(a, b) }

#[inline]
/// Upstream doc (traits.rs:319-319):
///   Call [`Flags::insert`] when `value` is `true` or [`Flags::remove`] when `value` is `false`.
pub exec fn set(a: u32, b: u32, value: bool) -> (r: u32)
    ensures if value { r == union_sem(a, b) } else { r == difference_sem(a, b) }
{ if value { insert(a, b) } else { difference(a, b) } }

/* ============================================================
 * L0 -- an "entry theorem" (the design-doc sec. 5.2 shape): any input, any branch;
 * the entry's post-state is fully characterized by the spec layer; panic-freedom
 * is discharged automatically by the Verus machine semantics (bit ops never panic).
 * ============================================================ */

pub exec fn entry_union_or_remove(bits1: u32, bits2: u32, keep_other: bool) -> (r: u32)
    ensures if keep_other { r == union_sem(bits1, bits2) }
            else { r == difference_sem(bits1, bits2) }
{ if keep_other { union(bits1, bits2) } else { difference(bits1, bits2) } }

/* ============================================================
 * S4 -- the spec.md theorem list
 * ============================================================ */

// ---------------- sec. Definitions: the ABC redundant flag / known bits ----------------

#[allow(nonstandard_style)]
proof fn known_mask_instance()
    ensures defined_ABC() == 0b0000_0111u32, known_bits(0b1111_1111u32) == 0b0000_0111u32
{
    lemma_known_mask_value();
    assert(0b1111_1111u32 & defined_ABC() == 0b0000_0111u32) by (bit_vector);
}

// ---------------- sec. Union / sec. Intersection ----------------

proof fn union_neutral_zero(a: u32)
    ensures union_sem(a, 0u32) == a
{
    assert(a | 0u32 == a) by (bit_vector);
}

proof fn union_assoc(a: u32, b: u32, c: u32)
    ensures union_sem(union_sem(a, b), c) == union_sem(a, union_sem(b, c))
{
    assert(((a | b) | c) == (a | (b | c))) by (bit_vector);
}

proof fn intersection_idempotent(a: u32)
    ensures intersection_sem(a, a) == a
{
    assert(a & a == a) by (bit_vector);
}

proof fn intersection_absorbs_known(a: u32)
    ensures intersection_sem(a, defined_ABC()) == known_bits(a)
{
    lemma_known_mask_value();
    assert(a & 0b0000_0111u32 == a & 0b0000_0111u32) by (bit_vector);
}

// ---------------- sec. Contains / sec. Intersects ----------------

proof fn contains_reflexive(a: u32)
    ensures contains_flag(a, a) == true
{
    assert(a & a == a) by (bit_vector);
}

proof fn contains_transitive(a: u32, b: u32, c: u32)
    requires contains_flag(a, b), contains_flag(b, c)
    ensures contains_flag(a, c)
{
    assert(a & b == b && b & c == c ==> a & c == c) by (bit_vector);
}

/// The verbatim examples of spec.md sec. Intersects are machine-checked
proof fn spec_md_intersects_examples()
    ensures
        intersects_flag(0b0000_0011u32, 0b0000_0010u32) == true,
        !(intersects_flag(0b0000_0011u32, 0b1111_0000u32))
{
    assert(0b0000_0011u32 & 0b0000_0010u32 == 0b0000_0010u32) by (bit_vector);
    assert(0b0000_0011u32 & 0b1111_0000u32 == 0u32) by (bit_vector);
}

// ---------------- sec. Empty / sec. All ----------------

proof fn all_contains_every_defined_flag()
    ensures
        contains_flag(defined_ABC(), defined_A()),
        contains_flag(defined_ABC(), defined_B()),
        contains_flag(defined_ABC(), defined_C())
{
    lemma_known_mask_value();
    assert(0b0000_0111u32 & 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
    assert(0b0000_0111u32 & 0b0000_0010u32 == 0b0000_0010u32) by (bit_vector);
    assert(0b0000_0111u32 & 0b0000_0100u32 == 0b0000_0100u32) by (bit_vector);
}

/// The instance values of the spec.md sec. Empty/sec. All examples are machine-checked
proof fn spec_md_empty_and_all_examples()
    ensures
        is_all_spec(0b0000_0111u32) == true,
        is_all_spec(0b0000_0001u32) == false,
        is_empty_spec(0b0000_0000u32) == true,
        is_empty_spec(0b0000_0001u32) == false
{
    // is_all(0b0111)==true: the mask is a subset of itself
    assert(0b0000_0111u32 & 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
    // is_all(0b0001)==false: the mask is not a subset of 0b0001 (0b111 & 0b1 == 0b0001 != 0b0111)
    assert(!(0b0000_0001u32 & 0b0000_0111u32 == 0b0000_0111u32)) by (bit_vector);
    lemma_known_mask_value();
    assert(!(0b0000_0001u32 & defined_ABC() == defined_ABC()));
    // is_empty
    assert(0b0000_0000u32 == 0u32 && 0b0000_0001u32 != 0u32);
}

/// The equivalent form of is_all_spec: mask is a subset of v <=> (mask | v) == v
/// (the former is the spec.md contains posture, the latter the traits.rs `is_all` posture)
proof fn is_all_iff_mask_subset(v: u32)
    ensures is_all_spec(v) == (defined_ABC() | v == v)
{
    lemma_known_mask_value();
    assert((v & 0b0000_0111u32 == 0b0000_0111u32) == (0b0000_0111u32 | v == v))
        by (bit_vector);
}

// ---------------- sec. Truncate ----------------

/// the truncate semantics: drop unknown bits, keep known bits, idempotent
proof fn truncate_removes_unknown_and_is_idempotent(b: u32)
    ensures
        known_bits(truncate_sem(b)) == truncate_sem(b),
        truncate_sem(truncate_sem(b)) == truncate_sem(b)
{
    lemma_known_mask_value();
    assert((b & 0b0000_0111u32) & 0b0000_0111u32 == b & 0b0000_0111u32) by (bit_vector);
}

/// The instance conclusion of spec.md sec. Truncate: the A/B/C of this example are
/// all single-bit flags, so "a non-empty known result must contain some defined
/// flag" (the spec.md text's condition holds in this instance)
proof fn truncated_nonempty_contains_defined_flag(b: u32)
    ensures (b & 0b0000_0111u32) != 0u32 ==>
            ((b & 0b0000_0111u32 & 0b0000_0001u32) == 0b0000_0001u32 ||
             (b & 0b0000_0111u32 & 0b0000_0010u32) == 0b0000_0010u32 ||
             (b & 0b0000_0111u32 & 0b0000_0100u32) == 0b0000_0100u32)
{
    assert(b & 0b0000_0111u32 != 0u32 ==>
           (b & 0b0000_0111u32 & 0b0000_0001u32 == 0b0000_0001u32 ||
            b & 0b0000_0111u32 & 0b0000_0010u32 == 0b0000_0010u32 ||
            b & 0b0000_0111u32 & 0b0000_0100u32 == 0b0000_0100u32)) by (bit_vector);
}

/// the union of two known values is still known (the safety precondition of composed operations)
proof fn truncates_union_is_truncated(b1: u32, b2: u32)
    ensures truncate_sem(union_sem(truncate_sem(b1), truncate_sem(b2)))
            == union_sem(truncate_sem(b1), truncate_sem(b2))
{
    lemma_known_mask_value();
    assert(((b1 & 0b0000_0111u32) | (b2 & 0b0000_0111u32)) & 0b0000_0111u32 ==
           ((b1 & 0b0000_0111u32) | (b2 & 0b0000_0111u32))) by (bit_vector);
}

// ---------------- sec. Complement ----------------

/// spec.md: "The complement is the only operation that explicitly
/// truncates the result"; the double complement lands back on the truncate layer
proof fn double_complement_is_truncate(b: u32)
    ensures complement_sem(complement_sem(b)) == truncate_sem(b)
{
    lemma_known_mask_value();
    assert(!(!b & 0b0000_0111u32) & 0b0000_0111u32 == b & 0b0000_0111u32)
        by (bit_vector);
}

proof fn complement_has_no_unknown_bits(b: u32)
    ensures known_bits(complement_sem(b)) == complement_sem(b)
{
    lemma_known_mask_value();
    assert((!b & 0b0000_0111u32) & 0b0000_0111u32 == !b & 0b0000_0111u32)
        by (bit_vector);
}

// ---------------- sec. Difference (the semantic point spec.md explicitly warns about) ----------------

/// The spec.md text:
///   "This operation is not equivalent to the intersection of one flags value
///    with the complement of another (`&!`). The former will truncate the result
///    in the complement, where difference will not."
/// Witness: with a = 0b1111_0000 (unknown bits set) and b = 0 the two differ.
/// -- this span of spec.md text is machine-checked as a concrete numeric theorem
proof fn difference_is_not_complemented_intersection()
    ensures
        complement_sem(0u32) == 0b0000_0111u32,
        difference_sem(0b1111_0000u32, 0u32) == 0b1111_0000u32,
        intersection_sem(0b1111_0000u32, complement_sem(0u32)) == 0u32,
        difference_sem(0b1111_0000u32, 0u32)
            != intersection_sem(0b1111_0000u32, complement_sem(0u32))
{
    lemma_known_mask_value();
    assert(!0u32 & 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
    assert(0b1111_0000u32 & !0u32 == 0b1111_0000u32) by (bit_vector);
    assert(0b1111_0000u32 & 0b0000_0111u32 == 0u32) by (bit_vector);
}

// ---------------- the algebra of insert / remove / toggle ----------------

/// remove cancels insert (cf. the tests.rs toggle/insert/remove checks)
proof fn remove_cancels_insert_sem(a: u32, b: u32)
    ensures difference_sem(union_sem(a, b), b) == difference_sem(a, b)
{
    assert((a | b) & !(b) == a & !(b)) by (bit_vector);
}

/// a double toggle of the symmetric difference restores the original value
proof fn toggle_twice_is_identity(a: u32, b: u32)
    ensures symmetric_difference_sem(symmetric_difference_sem(a, b), b) == a
{
    assert((a ^ b) ^ b == a) by (bit_vector);
}


// ---------------------------------------------------------------------------
// Proof lemmas (the shared mask fact and the spec.md theorem list, placed at
// the end before the close of verus! so the exec implementations read directly)
// ---------------------------------------------------------------------------
/// A constant-level mask fact shared by all the theorems.
/// (trust-boundary note: 0b111 is the mirrored value of the "macro expansion"
///  step; in a real pipeline this step is auto-generated and checked by the S1
///  mining tool.)
pub proof fn lemma_known_mask_value()
    ensures defined_ABC() == 0b0000_0111u32
{
    assert(defined_ABC() == 0b0000_0111u32) by (bit_vector);
}
}

fn main() {}
