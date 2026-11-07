//! bitflags 2.13.2 x Verus -- instance mirror of the macro-expanded
//! inherent API face (the upstream code/
//! tree is untouched)
//!
//!
//! Upstream site: the expansion body of the `bitflags!` macro for
//! `pub struct TestFlags: u32 { const A = 0b1; const B = 0b10; const C = 0b100; const ABC = A|B|C }`
//!   * inherent method bodies: `public.rs:132-288 __impl_public_bitflags!` (the
//!     $BitFlags
//!     empty/all/bits/from_bits/from_bits_truncate/from_bits_retain/from_name/
//!     is_empty/is_all/intersects/contains/insert/remove/toggle/set/
//!     intersection/union/difference/symmetric_difference/complement)
//!   * operator trait forwarding: `public.rs:342-487 __impl_public_bitflags_ops!`
//!     (this file takes
//!     Not/Sub/BitOr/BitAnd as representative samples; the remaining ops
//!     are isomorphic forwardings)
//!   * constants and FLAGS: `public.rs:521-626 __impl_public_bitflags_consts!`
//!
//! Carried-verification note: macro definition bodies (the macro_rules
//! rules) are outside the transcription face, so per skill ruling
//! verification is carried by monomorphized instances:
//! this instance = `TestFlags:u32` (exactly the same parameterization as
//! the upstream `example_generated.rs`); every method of its expansion body
//! is transcribed here one by one; the method-body expressions are
//! ** literally isomorphic ** with the macro expansion results (`self.0` maps
//! directly onto the bits field); the equivalence "macro-expanded body ==
//! Flags trait default body" is closed by the theorem group of
//! verified/harness/coverage_props.rs.
//!
//! Relaxation ledger:
//! 1. The `from_name` expansion body (public.rs:194-226) is an unrolled chain
//!    of `if name == "<const name>" { return .. }`
//!    -- string literals are modeled per traits.rs relaxation 1 as `name_id: u64` (matching
//!    semantics unchanged: probe each constant, return on first match; the
//!    name content itself is std string equality, a trust boundary).
//! 2. The `all()` expansion body is const folding (public.rs:150-170 `const ALL`),
//!    transcribed as a constant literal + fold lemma (the `lemma` pulls the
//!    closed form of traits.rs::all_fold_spec).
//! 3. The struct is `pub struct TestFlags { bits: u32 }` (the 1-layer merge of
//!    the macro newtype declarations
//!    `$vis struct $BitFlags(<$PublicBitFlags as PublicFlags>::Internal) +
//! #[repr(transparent)] $vis struct $InternalBitFlags($T)`; the public type
//!    only newtype-forwards to the internal type, no operations).
//! 4. The state machines of the iterators (`__impl_public_bitflags_iter!`)
//!    are in verified/src/iter.rs.

use vstd::prelude::*;

use super::traits::{
    complement_sem_of, contains_sem, difference_sem, flag_name_id_spec, from_name_lookup,
    intersection_sem, intersects_sem, is_all_sem_of, is_empty_sem, symmetric_difference_sem,
    truncate_sem_of, union_sem, NUM_FLAGS, all_fold_spec, tflags_all_bits,
    lemma_tflags_all_bits,
};

verus! {

/// spec view: the bits of a flags value (mirrors the upstream `bits(&self) -> Self::Bits`)
pub open spec fn tf_bits(f: TestFlags) -> u32 {
    f.bits
}

/// monomorphized instance newtype (merge of `__declare_public_bitflags!` + the internal type; relaxation 3)
#[derive(Clone, Copy)]
pub struct TestFlags {
    pub bits: u32,
}

impl TestFlags {
    /// the sample A/B/C/ABC constants (`__impl_public_bitflags_consts!`: `pub const $Flag: Self = Self::from_bits_retain($value);`)
    #[allow(nonstandard_style)]
    pub const A: TestFlags = TestFlags { bits: 0b0000_0001u32 };
    #[allow(nonstandard_style)]
    pub const B: TestFlags = TestFlags { bits: 0b0000_0010u32 };
    #[allow(nonstandard_style)]
    pub const C: TestFlags = TestFlags { bits: 0b0000_0100u32 };
    #[allow(nonstandard_style)]
    pub const ABC: TestFlags = TestFlags { bits: 0b0000_0111u32 };




    /// public.rs:146-148 `fn empty() { Self(<$T as Bits>::EMPTY) }`
    /// Upstream doc (lib.rs:689-689):
    ///   Get a flags value with all bits unset.
    pub exec fn empty() -> (r: TestFlags)
        ensures tf_bits(r) == 0u32
    {
        TestFlags { bits: 0u32 }
    }

    /// public.rs:150-170 `fn all() { const ALL: $BitFlags = { .. folded .. }; ALL }`
    /// macro const folding => constant literal; the fold is in traits.rs::all_fold_spec
    /// Upstream doc (lib.rs:694-694):
    ///   Get a flags value with all known bits set.
    pub exec fn all() -> (r: TestFlags)
        ensures
            tf_bits(r) == tflags_all_bits(),
            tf_bits(r) == all_fold_spec(NUM_FLAGS as int),
    {
        proof {
            lemma_tflags_all_bits();
        }
        TestFlags { bits: 0b0000_0111u32 }
    }

    /// public.rs:172-174 `fn bits(&self) { self.0 }`
    /// Upstream doc (lib.rs:699-701):
    ///   Get the underlying bits value.
    ///   The returned value is exactly the bits set in this flags value.
    pub exec fn bits(&self) -> (r: u32)
        ensures
            r == self.bits,
            r == tf_bits(*self),
    {
        self.bits
    }

    /// public.rs:176-184 `fn from_bits(bits)`
    /// Upstream doc (lib.rs:706-708):
    ///   Convert from a bits value.
    ///   This method will return `None` if any unknown bits are set.
    pub exec fn from_bits(bits: u32) -> (r: Option<TestFlags>)
        ensures
            r.is_some() == (bits == truncate_sem_of(tflags_all_bits(), bits)),
            r.is_some() ==> tf_bits(r.unwrap()) == bits,
    {
        let truncated = Self::from_bits_truncate(bits);
        if truncated.bits == bits {
            Option::Some(TestFlags { bits })
        } else {
            Option::None
        }
    }

    /// public.rs:186-188 `fn from_bits_truncate(bits) { Self(bits & Self::all().0) }`
    /// Upstream doc (lib.rs:713-713):
    ///   Convert from a bits value, unsetting any unknown bits.
    pub exec fn from_bits_truncate(bits: u32) -> (r: TestFlags)
        ensures tf_bits(r) == truncate_sem_of(tflags_all_bits(), bits)
    {
        let all = Self::all();
        TestFlags { bits: bits & all.bits }
    }

    /// public.rs:190-192 `fn from_bits_retain(bits) { Self(bits) }`
    /// Upstream doc (lib.rs:718-718):
    ///   Convert from a bits value exactly.
    pub exec fn from_bits_retain(bits: u32) -> (r: TestFlags)
        ensures tf_bits(r) == bits
    {
        TestFlags { bits }
    }

    /// public.rs:194-226 `fn from_name(name)`: the macro generates
    /// `if name == "<name>" { return Some(Self(..)) }` for each constant; the name is modeled as a u64 id (relaxation 1)
    /// Upstream doc (lib.rs:723-726):
    ///   Get a flags value with the bits of a flag with the given name set.
    ///   This method will return `None` if `name` is empty or doesn't
    ///   correspond to any named flag.
    pub exec fn from_name(name: u64) -> (r: Option<TestFlags>)
        ensures
            r.is_some() == from_name_lookup(name).is_some(),
            r.is_some() ==> tf_bits(r.unwrap()) == from_name_lookup(name).unwrap(),
    {
        if super::traits::flag_name_id_at(0) == name {
            return Option::Some(TestFlags { bits: 0b0000_0001u32 });
        }
        if super::traits::flag_name_id_at(1) == name {
            return Option::Some(TestFlags { bits: 0b0000_0010u32 });
        }
        if super::traits::flag_name_id_at(2) == name {
            return Option::Some(TestFlags { bits: 0b0000_0100u32 });
        }
        if super::traits::flag_name_id_at(3) == name {
            return Option::Some(TestFlags { bits: 0b0000_0111u32 });
        }
        Option::None
    }

    /// public.rs:228-230 `fn is_empty(&self) { self.0 == EMPTY }`
    /// Upstream doc (lib.rs:731-731):
    ///   Whether all bits in `self` are unset.
    pub exec fn is_empty(&self) -> (r: bool)
        ensures r == is_empty_sem(self.bits)
    {
        self.bits == 0u32
    }

    /// public.rs:232-236 `fn is_all(&self){ Self::all().0 | self.0 == self.0 }`
    /// (NOTE verbatim: check against `Self::all`, not `Bits::ALL`)
    /// Upstream doc (lib.rs:736-736):
    ///   Whether all known bits in this flags value are set.
    pub exec fn is_all(&self) -> (r: bool)
        ensures r == is_all_sem_of(tflags_all_bits(), self.bits)
    {
        let all = Self::all();
        proof {
            // (all | v == v) == (v & all == all): the contains view vs the is_all body
            let amask: u32 = all.bits;
            let sbits: u32 = self.bits;
            assert(amask == tflags_all_bits());
            assert((amask | sbits == sbits) == (sbits & amask == amask)) by (bit_vector);
        }
        all.bits | self.bits == self.bits
    }

    /// public.rs:238-240 `fn intersects(&self, other)`
    /// Upstream doc (lib.rs:741-741):
    ///   Whether any set bits in `other` are also set in `self`.
    pub exec fn intersects(&self, other: &TestFlags) -> (r: bool)
        ensures r == intersects_sem(self.bits, other.bits)
    {
        self.bits & other.bits != 0u32
    }

    /// public.rs:242-244 `fn contains(&self, other)`
    /// Upstream doc (lib.rs:746-746):
    ///   Whether all set bits in `other` are also set in `self`.
    pub exec fn contains(&self, other: &TestFlags) -> (r: bool)
        ensures r == contains_sem(self.bits, other.bits)
    {
        self.bits & other.bits == other.bits
    }

    /// public.rs:246-248 `fn insert(&mut self, other) { *self = Self(self.0).union(other) }`
    /// Upstream doc (lib.rs:751-751):
    ///   The bitwise or (`|`) of the bits in `self` and `other`.
    pub exec fn insert(&mut self, other: TestFlags)
        ensures (*final(self)).bits == union_sem(old(self).bits, other.bits)
    {
        *self = TestFlags { bits: self.bits }.union(other);
    }

    /// public.rs:250-252 `fn remove(&mut self, other)`
    /// Upstream doc (lib.rs:756-759):
    ///   The intersection of `self` with the complement of `other` (`&!`).
    ///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
    ///   `remove` won't truncate `other`, but the `!` operator will.
    pub exec fn remove(&mut self, other: TestFlags)
        ensures (*final(self)).bits == difference_sem(old(self).bits, other.bits)
    {
        *self = TestFlags { bits: self.bits }.difference(other);
    }

    /// public.rs:254-256 `fn toggle(&mut self, other)`
    /// Upstream doc (lib.rs:764-764):
    ///   The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
    pub exec fn toggle(&mut self, other: TestFlags)
        ensures (*final(self)).bits == symmetric_difference_sem(old(self).bits, other.bits)
    {
        *self = TestFlags { bits: self.bits }.symmetric_difference(other);
    }

    /// public.rs:258-264 `fn set(&mut self, other, value)`
    /// Upstream doc (lib.rs:769-769):
    ///   Call `insert` when `value` is `true` or `remove` when `value` is `false`.
    pub exec fn set(&mut self, other: TestFlags, value: bool)
        ensures
            if value {
                (*final(self)).bits == union_sem(old(self).bits, other.bits)
            } else {
                (*final(self)).bits == difference_sem(old(self).bits, other.bits)
            },
    {
        if value {
            self.insert(other);
        } else {
            self.remove(other);
        }
    }

    /// public.rs:266-268 `fn intersection(self, other) { Self(self.0 & other.0) }`
    /// Upstream doc (lib.rs:774-774):
    ///   The bitwise and (`&`) of the bits in `self` and `other`.
    pub exec fn intersection(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == intersection_sem(self.bits, other.bits)
    {
        TestFlags { bits: self.bits & other.bits }
    }

    /// public.rs:270-272 `fn union(self, other) { Self(self.0 | other.0) }`
    /// Upstream doc (lib.rs:780-780):
    ///   The bitwise or (`|`) of the bits in `self` and `other`.
    pub exec fn union(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == union_sem(self.bits, other.bits)
    {
        TestFlags { bits: self.bits | other.bits }
    }

    /// public.rs:274-276 `fn difference(self, other) { Self(self.0 & !other.0) }`
    /// Upstream doc (lib.rs:786-789):
    ///   The intersection of `self` with the complement of `other` (`&!`).
    ///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
    ///   `difference` won't truncate `other`, but the `!` operator will.
    pub exec fn difference(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == difference_sem(self.bits, other.bits)
    {
        TestFlags { bits: self.bits & !other.bits }
    }

    /// public.rs:278-280 `fn symmetric_difference(self, other)`
    /// Upstream doc (lib.rs:795-795):
    ///   The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
    pub exec fn symmetric_difference(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == symmetric_difference_sem(self.bits, other.bits)
    {
        TestFlags { bits: self.bits ^ other.bits }
    }

    /// public.rs:282-284 `fn complement(self) { Self::from_bits_truncate(!self.0) }`
    /// Upstream doc (lib.rs:801-801):
    ///   The bitwise negation (`!`) of the bits in `self`, truncating the result.
    pub exec fn complement(self) -> (r: TestFlags)
        ensures tf_bits(r) == complement_sem_of(tflags_all_bits(), self.bits)
    {
        Self::from_bits_truncate(!self.bits)
    }

    /* ---- ops trait forwarding samples (public.rs:342-487 `__impl_public_bitflags_ops!`) ---- */

    /// public.rs:399 `fn bitor(self, other) { self.union(other) }`
    /// Upstream doc (public.rs:396-396):
    ///   The bitwise or (`|`) of the bits in `self` and `other`.
    pub exec fn op_bitor(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == union_sem(self.bits, other.bits)
    {
        self.union(other)
    }

    /// public.rs:450 `fn bitand(self, other) { self.intersection(other) }`
    /// Upstream doc (public.rs:436-436):
    ///   The bitwise and (`&`) of the bits in `self` and `other`.
    pub exec fn op_bitand(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == intersection_sem(self.bits, other.bits)
    {
        self.intersection(other)
    }

    /// public.rs:461 `fn sub(self, other) { self.difference(other) }`
    /// Upstream doc (public.rs:456-459):
    ///   The intersection of `self` with the complement of `other` (`&!`).
    ///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
    ///   `difference` won't truncate `other`, but the `!` operator will.
    pub exec fn op_sub(self, other: TestFlags) -> (r: TestFlags)
        ensures tf_bits(r) == difference_sem(self.bits, other.bits)
    {
        self.difference(other)
    }

    /// public.rs:484 `fn not(self) { self.complement() }`
    /// Upstream doc (public.rs:482-482):
    ///   The bitwise negation (`!`) of the bits in `self`, truncating the result.
    pub exec fn op_not(self) -> (r: TestFlags)
        ensures tf_bits(r) == complement_sem_of(tflags_all_bits(), self.bits)
    {
        self.complement()
    }
}

/* ============================================================
 * shared proof: consistency of the instance constants <-> the table specs
 * (the machine check of `__impl_public_bitflags_consts!` FLAGS being
 *  co-sourced with the constants)
 * ============================================================ */

// ---------------------------------------------------------------------------
// Proof lemmas (the two shared proof fns of this file, placed at the end
// before the close of verus! so the exec implementation reads directly)
// ---------------------------------------------------------------------------
/// A/B/C/ABC constants and the FLAGS table spec agree in both directions
/// (the machine-checked counterpart of the upstream flags.rs UT equalities)
pub proof fn lemma_consts_match_flags()
    ensures
        TestFlags::A.bits == super::traits::flag_bits_spec(0),
        TestFlags::B.bits == super::traits::flag_bits_spec(1),
        TestFlags::C.bits == super::traits::flag_bits_spec(2),
        TestFlags::ABC.bits == super::traits::flag_bits_spec(3),
{
    assert(TestFlags::A.bits == 0b0000_0001u32);
    assert(TestFlags::B.bits == 0b0000_0010u32);
    assert(TestFlags::C.bits == 0b0000_0100u32);
    assert(TestFlags::ABC.bits == 0b0000_0111u32);
}

/// the instance-side all() constant == the trait-side fold (macro-expansion
/// const folding == the trait default-body loop)
pub proof fn lemma_macro_all_equals_fold()
    ensures tflags_all_bits() == super::traits::all_fold_spec(NUM_FLAGS as int)
{
    lemma_tflags_all_bits();
}

}
