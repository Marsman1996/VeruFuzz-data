//! faest 0.3.0 -- Verus transcription of src/prover/field_commitment.rs,
//! batch FA6-pre (the FA6/FA11 material batch; GF(2^128) axis).
//!
//! Upstream: prover/field_commitment.rs (526 lines, pin 9ccc68c0):
//! FieldCommitment{key, tag} (:8-16), Default (:18-28), the
//! AddAssign/Add families (:30-109), the three degree-type aliases
//! FieldCommitDegOne/Two/Three (:111-112, :277-278, :397-398), and the
//! degree-raising Mul/Square faces (:123-261, :280-432) consumed by
//! universal_hashing.rs (the FA6 import face) and prover/aes.rs /
//! encryption.rs (the FA11 faces). The in-file test rows (:434-526)
//! ride the FA6-pre harness (verified/harness/ut_fa6p.rs), not this
//! twin.
//!
//! Representation lowering (trust boundary, FA3/FA1 conventions):
//!   - F: BigGaloisField is instantiated at the closed GF128 axis of
//!     fields/large_fields.rs (BigGF<u128, 1, 128> -> u128; the
//!     crate::fields::{BigGaloisField, Square} import pair of upstream
//!     :1-6 re-spells to crate::large_fields, the fa10w direct-mount
//!     naming). The GF192/GF256 instantiations of FA11 are a
//!     mechanical re-spelling gated on the FA3 wave lands (record-only
//!     here).
//!   - TAG_SIZE stays a const generic (the upstream usize array
//!     length); the field ops inside the bodies lower to the FA3
//!     exec/spec pairs: Add -> plain `^` (characteristic 2, the
//!     u128-limb xor), Mul -> gf128_mul (verifies gf128_mul_spec),
//!     Square -> gf128_square (verifies gf128_hmul; the mul_spec ==
//!     hmul bridge stays the FA3 deferral).
//!   - The std ops impl-operator dispatch (by-value/by-ref cross
//!     impls whose upstream bodies are the same expression up to
//!     moves) drops at the ops trait boundary; every impl block below
//!     carries its upstream line anchor, and impls that upstream
//!     writes out inline with identical bodies share one twin face
//!     with the anchor list (the FA10 convention: one face, both
//!     anchors -- no value content is lost, the ref/value splitter
//!     is Rust ownership bookkeeping).
//!
//! Upstream doc lines re-erected as obligations:
//!   - "Represents a polynomial commitment in GF of degree one"
//!     :111-112 resp. degree 2 (:277) / degree 3 (:397): the tag-slot
//!     algebra below is the degree face -- the Mul chain raises
//!     degree 1*1 -> 2 and 1*2 / 2*1 -> 3, square of degree 1 -> 2
//!     with the characteristic-2 zero middle coefficient (:249-275,
//!     the `F::ZERO` literal preserved at the Square faces).

use vstd::prelude::*;

use crate::large_fields::{
    gf128_hmul, gf128_mul, gf128_mul_spec, gf128_square, GF128_ZERO,
};

verus! {

// ===========================================================================
// The carrier (upstream :8-16):
//     #[derive(Debug, Clone)]
//     #[cfg_attr(test, derive(PartialEq))]
//     pub(crate) struct FieldCommitment<F, const TAG_SIZE: usize>
//     where F: BigGaloisField {
//         pub key: F,
//         pub tag: [F; TAG_SIZE] }
// Debug/Clone are record-only (no contract content); the test-only
// PartialEq derive rides the harness's concrete assert rows.
// ===========================================================================

pub struct FieldCommitment<const TAG_SIZE: usize> {
    /// The commitment key (the hidden VOLE key batch element); GF128
    /// axis: one u128 limb.
    pub key: u128,
    /// The commitment tag slots; slot i carries the degree-(i+1)
    /// coefficient face of the polynomial commitment.
    pub tag: [u128; TAG_SIZE],
}

// ===========================================================================
// Default (upstream :18-28): `Self { key: F::ZERO, tag: [F::ZERO;
// TAG_SIZE] }` over the field trait constants; GF128 lowers F::ZERO
// to the FA3 const GF128_ZERO (upstream large_fields.rs :919).
// ===========================================================================

impl<const TAG_SIZE: usize> FieldCommitment<TAG_SIZE> {
    pub fn default() -> (o: Self)
        ensures
            o.key == GF128_ZERO,
            forall |i: int|
                0 <= i < TAG_SIZE ==> o.tag[i] == GF128_ZERO,
    {
        FieldCommitment {
            key: GF128_ZERO,
            tag: [GF128_ZERO; TAG_SIZE],
        }
    }
}

// ===========================================================================
// AddAssign / Add family (upstream :30-109).
// Origin Rust (AddAssign<&Self>, :42-52; AddAssign<Self> :30-40 has
// the by-identical body at a moved rhs):
//     fn add_assign(&mut self, rhs: &Self) {
//         self.key += rhs.key;
//         for (l, r) in zip(self.tag.iter_mut(), rhs.tag) { *l += r; } }
// The field `+=` lowers to `^` (GF128 Add is the limb xor, FA3
// record); the zip iterator lowers to the index loop (same order,
// same element pairing, the FA1 xor_arrays loop-form precedent).
// ===========================================================================

impl<const TAG_SIZE: usize> FieldCommitment<TAG_SIZE> {
    pub fn add_assign(self: &mut Self, rhs: &Self)
        ensures
            final(self).key == old(self).key ^ rhs.key,
            forall |i: int|
                0 <= i < TAG_SIZE ==>
                    final(self).tag[i] == old(self).tag[i] ^ rhs.tag[i],
    {
        // the field-element zip of upstream lowers to the index loop
        // over a local working copy (the loop tracks the pointwise
        // xor against pin copies of both pre-state tag planes)
        let pre_self = self.tag;
        let pre_rhs = rhs.tag;
        proof {
            assert(pre_self == old(self).tag);
        }
        self.key = self.key ^ rhs.key;
        let mut work = self.tag;
        let mut i: usize = 0;
        while i < TAG_SIZE
            invariant
                0 <= i <= TAG_SIZE,
                self.key == old(self).key ^ rhs.key,
                work.len() == TAG_SIZE,
                forall |j: int|
                    0 <= j < i ==> work[j] == pre_self[j] ^ pre_rhs[j],
                forall |j: int|
                    i <= j < TAG_SIZE ==> work[j] == pre_self[j],
            decreases
                (TAG_SIZE - i) as int,
        {
            work[i] = work[i] ^ pre_rhs[i];
            i += 1;
        }
        self.tag = work;
    }

    /// AddAssign<F> / AddAssign<&F> (upstream :54-70, by-identical
    /// key-plane-only bodies; the two anchor impls share this face).
    /// The tag plane is untouched upstream (no tag statement in the
    /// impl body) -- the twin carries the preservation row.
    pub fn add_assign_field(self: &mut Self, rhs: u128)
        ensures
            final(self).key == old(self).key ^ rhs,
            forall |i: int|
                0 <= i < TAG_SIZE ==>
                    final(self).tag[i] == old(self).tag[i],
    {
        self.key = self.key ^ rhs;
    }

    /// Add<Self> (upstream :72-83): the upstream body `self += rhs;
    /// self` over the moved receiver.
    pub fn add(mut self, rhs: Self) -> (o: Self)
        ensures
            o.key == self.key ^ rhs.key,
            forall |i: int|
                0 <= i < TAG_SIZE ==> o.tag[i] == self.tag[i] ^ rhs.tag[i],
    {
        self.add_assign(&rhs);
        self
    }

    /// Add<&Self> (upstream :85-96): `self += *rhs`.
    pub fn add_ref(mut self, rhs: &Self) -> (o: Self)
        ensures
            o.key == self.key ^ rhs.key,
            forall |i: int|
                0 <= i < TAG_SIZE ==> o.tag[i] == self.tag[i] ^ rhs.tag[i],
    {
        self.add_assign(rhs);
        self
    }

    /// Add for &Self (upstream :98-109) -- body `self.clone() + rhs`,
    /// the upstream `TODO: implement without clone` note carried; the
    /// clone lowers to the field-copied moved self (no contract
    /// content in the clone itself).
    pub fn add_ref_ref(self: &Self, rhs: &Self) -> (o: Self)
        ensures
            o.key == self.key ^ rhs.key,
            forall |i: int|
                0 <= i < TAG_SIZE ==> o.tag[i] == self.tag[i] ^ rhs.tag[i],
    {
        let mut moved = FieldCommitment {
            key: self.key,
            tag: self.tag,
        };
        moved.add_assign(rhs);
        moved
    }
}

// ===========================================================================
// The degree aliases (upstream :111-112, :277-278, :397-398):
//     /// Represents a polynomial commitment in GF of degree one
//     pub type FieldCommitDegOne<F> = FieldCommitment<F, 1>;
//     /// Represents a polynomial commitment in GF of degree 2
//     pub type FieldCommitDegTwo<F> = FieldCommitment<F, 2>;
//     /// Represents a polynomial commitment in GF of degree 3
//     pub type FieldCommitDegThree<F> = FieldCommitment<F, 3>;
// ===========================================================================

pub type FieldCommitDegOne = FieldCommitment<1>;
pub type FieldCommitDegTwo = FieldCommitment<2>;
pub type FieldCommitDegThree = FieldCommitment<3>;

// ===========================================================================
// FieldCommitDegOne::new (upstream :114-121):
//     pub fn new(key: F, tag: F) -> Self { Self { key, tag: [tag] } }
// ===========================================================================

impl FieldCommitDegOne {
    pub fn new(key: u128, tag: u128) -> (o: Self)
        ensures
            o.key == key,
            o.tag[0] == tag,
    {
        FieldCommitment { key, tag: [tag] }
    }
}

// ===========================================================================
// Degree raising 1 % 1 -> 2 (upstream :123-175: Mul<&Self> for D1,
// Mul<Self> for &D1, Mul for D1 -- three impls with the same value
// body):
//     fn mul(self, rhs: &Self) -> FieldCommitDegTwo {
//         FieldCommitDegTwo {
//             key: self.key * rhs.key,
//             tag: [ self.tag[0] * rhs.tag[0],
//                    self.key * rhs.tag[0] + self.tag[0] * rhs.key ] } }
// by-value and by-ref re-typings of the same expression route through
// the reference face (anchors kept, the moved/self split is ownership
// bookkeeping).
// ===========================================================================

impl FieldCommitDegOne {
    /// Mul<&Self> for FieldCommitDegOne (:123-139); `Mul for D1`
    /// (:159-175) routes through this face.
    pub fn mul(mut self, rhs: &Self) -> (o: FieldCommitDegTwo)
        ensures
            o.key == gf128_mul_spec(self.key, rhs.key),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs.tag[0]),
            o.tag[1] == gf128_mul_spec(self.key, rhs.tag[0])
                ^ gf128_mul_spec(self.tag[0], rhs.key),
    {
        FieldCommitDegTwo {
            key: gf128_mul(self.key, rhs.key),
            tag: [
                gf128_mul(self.tag[0], rhs.tag[0]),
                gf128_mul(self.key, rhs.tag[0]) ^ gf128_mul(self.tag[0], rhs.key),
            ],
        }
    }

    /// Mul<Self> for &FieldCommitDegOne (upstream :141-157) -- the
    /// ref-receiver swap with the same body.
    pub fn mul_swap(self: &Self, mut rhs: Self) -> (o: FieldCommitDegTwo)
        ensures
            o.key == gf128_mul_spec(self.key, rhs.key),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs.tag[0]),
            o.tag[1] == gf128_mul_spec(self.key, rhs.tag[0])
                ^ gf128_mul_spec(self.tag[0], rhs.key),
    {
        FieldCommitDegOne {
            key: self.key,
            tag: [self.tag[0]],
        }.mul(&rhs)
    }

    /// Mul<&FieldCommitDegTwo> for FieldCommitDegOne and for
    /// &FieldCommitDegOne (upstream :196-232, same value body, two
    /// ownership spellings): degree 1*2 -> 3.
    pub fn mul_two_ref(self: &Self, rhs: &FieldCommitDegTwo) -> (o: FieldCommitDegThree)
        ensures
            o.key == gf128_mul_spec(self.key, rhs.key),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs.tag[0]),
            o.tag[1] == gf128_mul_spec(self.key, rhs.tag[0])
                ^ gf128_mul_spec(self.tag[0], rhs.tag[1]),
            o.tag[2] == gf128_mul_spec(self.key, rhs.tag[1])
                ^ gf128_mul_spec(self.tag[0], rhs.key),
    {
        FieldCommitDegThree {
            key: gf128_mul(self.key, rhs.key),
            tag: [
                gf128_mul(self.tag[0], rhs.tag[0]),
                gf128_mul(self.key, rhs.tag[0]) ^ gf128_mul(self.tag[0], rhs.tag[1]),
                gf128_mul(self.key, rhs.tag[1]) ^ gf128_mul(self.tag[0], rhs.key),
            ],
        }
    }

    /// Mul<FieldCommitDegTwo> for FieldCommitDegOne (upstream
    /// :177-194, by-value rhs): the same body at a moved rhs.
    pub fn mul_two(mut self, rhs: FieldCommitDegTwo) -> (o: FieldCommitDegThree)
        ensures
            o.key == gf128_mul_spec(self.key, rhs.key),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs.tag[0]),
            o.tag[1] == gf128_mul_spec(self.key, rhs.tag[0])
                ^ gf128_mul_spec(self.tag[0], rhs.tag[1]),
            o.tag[2] == gf128_mul_spec(self.key, rhs.tag[1])
                ^ gf128_mul_spec(self.tag[0], rhs.key),
    {
        self.mul_two_ref(&rhs)
    }

    /// Mul<&F> for FieldCommitDegOne (upstream :234-247):
    ///     fn mul(self, rhs: &F) -> Self {
    ///         Self { key: self.key * rhs, tag: self.tag } }
    /// The TAG IS KEPT (upstream body copies `self.tag` unchanged);
    /// only the key plane scales -- the known-value(scalar) multiply
    /// face consumed by FA11's MixColumns rows.
    pub fn mul_field_ref(mut self, rhs: &u128) -> (o: Self)
        ensures
            o.key == gf128_mul_spec(self.key, *rhs),
            o.tag[0] == self.tag[0],
    {
        FieldCommitDegOne {
            key: gf128_mul(self.key, *rhs),
            tag: self.tag,
        }
    }
}

// ===========================================================================
// Square on degree one (upstream :249-275: Square for &D1 and for D1,
// by-identical bodies):
//     fn square(self) -> FieldCommitDegTwo {
//         FieldCommitDegTwo { key: self.key.square(),
//             tag: [self.tag[0].square(), F::ZERO] } }
// The characteristic-2 zero middle coefficient is the F::ZERO literal
// (preserved as GF128_ZERO); F::square is FA3's gf128_square face
// (verifies gf128_hmul(v, v)).
// ===========================================================================

impl FieldCommitDegOne {
    /// Square for FieldCommitDegOne (:263-275); `Square for &D1`
    /// (:249-261) is the same body -- both anchors share this face.
    pub fn square(mut self) -> (o: FieldCommitDegTwo)
        ensures
            o.key == gf128_hmul(self.key, self.key),
            o.tag[0] == gf128_hmul(self.tag[0], self.tag[0]),
            o.tag[1] == GF128_ZERO,
    {
        FieldCommitDegTwo {
            key: gf128_square(self.key),
            tag: [gf128_square(self.tag[0]), GF128_ZERO],
        }
    }
}

// ===========================================================================
// FieldCommitDegTwo faces (upstream :280-396).
// ===========================================================================

impl FieldCommitDegTwo {
    /// AddAssign<&FieldCommitDegOne> for FieldCommitDegTwo (upstream
    /// :280-289): key plane add; only tag slot 1 absorbs the degree-1
    /// tag (upstream `self.tag[1] += rhs.tag[0]`).
    pub fn add_assign_one(self: &mut Self, rhs: &FieldCommitDegOne)
        ensures
            final(self).key == old(self).key ^ rhs.key,
            final(self).tag[0] == old(self).tag[0],
            final(self).tag[1] == old(self).tag[1] ^ rhs.tag[0],
    {
        self.key = self.key ^ rhs.key;
        self.tag[1] = self.tag[1] ^ rhs.tag[0];
    }

    /// Mul<F> / Mul<&F> for FieldCommitDegTwo and the two &-receiver
    /// spellings (upstream :291-345: four impls, one value body):
    ///     fn mul(mut self, rhs: F) -> Self {
    ///         Self { key: self.key * rhs,
    ///             tag: [self.tag[0] * rhs, self.tag[1] * rhs] } }
    /// Both tag slots scale (contrast the D1 Mul<&F> face above).
    pub fn mul_field(mut self, rhs: u128) -> (o: Self)
        ensures
            o.key == gf128_mul_spec(self.key, rhs),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs),
            o.tag[1] == gf128_mul_spec(self.tag[1], rhs),
    {
        FieldCommitDegTwo {
            key: gf128_mul(self.key, rhs),
            tag: [
                gf128_mul(self.tag[0], rhs),
                gf128_mul(self.tag[1], rhs),
            ],
        }
    }

    /// Mul<&FieldCommitDegOne> for FieldCommitDegTwo (:359-376) and
    /// the &-receiver (:378-395) plus the by-value Mul<D1> (:347-357)
    /// that upstream writes as the delegation `self * &rhs`; degree
    /// 2*1 -> 3:
    ///     tag: [t0*rt0, t0*rk + t1*rt0, t1*rk + k*rt0]
    pub fn mul_one_ref(self: &Self, rhs: &FieldCommitDegOne) -> (o: FieldCommitDegThree)
        ensures
            o.key == gf128_mul_spec(self.key, rhs.key),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs.tag[0]),
            o.tag[1] == gf128_mul_spec(self.tag[0], rhs.key)
                ^ gf128_mul_spec(self.tag[1], rhs.tag[0]),
            o.tag[2] == gf128_mul_spec(self.tag[1], rhs.key)
                ^ gf128_mul_spec(self.key, rhs.tag[0]),
    {
        FieldCommitDegThree {
            key: gf128_mul(self.key, rhs.key),
            tag: [
                gf128_mul(self.tag[0], rhs.tag[0]),
                gf128_mul(self.tag[0], rhs.key) ^ gf128_mul(self.tag[1], rhs.tag[0]),
                gf128_mul(self.tag[1], rhs.key) ^ gf128_mul(self.key, rhs.tag[0]),
            ],
        }
    }

    /// Mul<FieldCommitDegOne> for FieldCommitDegTwo (:347-357): the
    /// upstream delegation `self * &rhs` preserved at the twin.
    pub fn mul_one(mut self, rhs: FieldCommitDegOne) -> (o: FieldCommitDegThree)
        ensures
            o.key == gf128_mul_spec(self.key, rhs.key),
            o.tag[0] == gf128_mul_spec(self.tag[0], rhs.tag[0]),
            o.tag[1] == gf128_mul_spec(self.tag[0], rhs.key)
                ^ gf128_mul_spec(self.tag[1], rhs.tag[0]),
            o.tag[2] == gf128_mul_spec(self.tag[1], rhs.key)
                ^ gf128_mul_spec(self.key, rhs.tag[0]),
    {
        self.mul_one_ref(&rhs)
    }
}

// ===========================================================================
// FieldCommitDegThree faces (upstream :400-432): the tail-pointing Add
// impls that absorb a lower-degree commitment into the bottom slots.
// ===========================================================================

impl FieldCommitDegThree {
    /// Add<&FieldCommitDegOne> (upstream :400-413): key add; the
    /// degree-1 tag lands in slot 2 (upstream: slots 0/1 stored
    /// unchanged, `self.tag[2] + rhs.tag[0]`).
    pub fn add_one(self, rhs: &FieldCommitDegOne) -> (o: Self)
        ensures
            o.key == self.key ^ rhs.key,
            o.tag[0] == self.tag[0],
            o.tag[1] == self.tag[1],
            o.tag[2] == self.tag[2] ^ rhs.tag[0],
    {
        FieldCommitDegThree {
            key: self.key ^ rhs.key,
            tag: [
                self.tag[0],
                self.tag[1],
                self.tag[2] ^ rhs.tag[0],
            ],
        }
    }

    /// Add<&FieldCommitDegTwo> (upstream :415-432): key add; the
    /// degree-2 tag lands in slots 1/2, slot 0 unchanged.
    pub fn add_two(self, rhs: &FieldCommitDegTwo) -> (o: Self)
        ensures
            o.key == self.key ^ rhs.key,
            o.tag[0] == self.tag[0],
            o.tag[1] == self.tag[1] ^ rhs.tag[0],
            o.tag[2] == self.tag[2] ^ rhs.tag[1],
    {
        FieldCommitDegThree {
            key: self.key ^ rhs.key,
            tag: [
                self.tag[0],
                self.tag[1] ^ rhs.tag[0],
                self.tag[2] ^ rhs.tag[1],
            ],
        }
    }
}

} // verus!

// Records (upstream surfaces outside this twin's lowered scope):
//   - The in-file test rows (:434-526) -- including the `GF128::ONE *
//     2` Mul<u8> select semantics (upstream large_fields.rs :668-678:
//     ONE * 2u8 == ZERO, ONE * 3u8 == ONE) -- ride the FA6-pre harness
//     (verified/harness/ut_fa6p.rs), where the concrete rows pin the
//     spec faces over the oracle cross-checked constants.
//   - No `PartialEq` derive rides the twin (test-only upstream); the
//     harness asserts per-field program equalities instead.
