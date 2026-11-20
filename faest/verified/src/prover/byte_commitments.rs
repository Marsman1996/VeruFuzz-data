//! faest 0.3.0 -- Verus transcription of src/prover/byte_commitments.rs,
//! batch FA6-pre (the FA6/FA11 material batch; GF(2^128) axis).
//!
//! Upstream: prover/byte_commitments.rs (150 lines, pin 9ccc68c0):
//! ByteCommitment{key, tags} (:17-41, the per-byte VOLE commitment
//! carrier with square_inplace / combine), ByteCommits (:43-105, the
//! owned byte-plane container) and ByteCommitsRef (:107-150, the
//! slice view with from_slices + the same get faces). The upstream
//! file carries no in-file test rows; the FA6-pre harness
//! (verified/harness/ut_fa6p.rs) pins the value chains over the
//! ORACLE constants.
//!
//! Representation lowering (trust boundary, FA3/FA1 conventions):
//!   - F: BigGaloisField instantiates at the closed GF128 axis
//!     (u128); the crate::fields::{BigGaloisField, GF8} +
//!     crate::utils::array_ref import set of upstream :1-15 re-spells
//!     to crate::large_fields / crate::small_fields (the direct
//!     mount naming; the super:: import of FieldCommitDegOne keeps
//!     its upstream-relative shape).
//!   - `Array<F, U8>` (tags) lowers to the fixed array [u128; 8];
//!     `Box<Array<u8, L>>` / `Box<Array<F, Prod<L, U8>>>` lower to
//!     the Vec pair (keys: Vec<u8>, tags: Vec<u128>) with the 8:1
//!     length relation as the callsite requires (the FA1 hybrid-array
//!     trust convention: sizes ride as plain lengths; the Box carrier
//!     lowers to the owned Vec, the storage repr the FA11 faces
//!     allocate against).
//!   - `array_ref` (utils.rs:124-137): under the reference-rep
//!     lowering for `&Array<u8, L>` the call is an identity re-borrow
//!     of the backing slice -- no by-value copy happens upstream
//!     here, so the twin re-borrows directly (deviation-recording
//!     note, not a semantic fig; the by-value FA1 twin stays owned by
//!     the copy-consumer scenes).
//!   - The typenum L / Prod<L, U8> / L2 size algebra drops at the
//!     trust boundary (FA10-pre rijndael_shift_rows_1 precedent);
//!     lengths are run-time requires parameters.
//!
//! Re-homing record (batch FA11-beta, 2026-11): the derived GF128
//! faces this twin had re-erected locally (SquareBytes /
//! ByteCombineSquared at fields/large_fields.rs :215-276 resp.
//! :283-313 + the GF8-orbit lemma bank) have MOVED to the fields
//! seat -- src/fields/large_fields.rs, the FA11-beta section -- and
//! this twin re-exports them below via `pub use crate::
//! large_fields::{...}` (same names, same slot contracts; the
//! mounts that reach them as crate::prover::byte_commitments::{
//! sqb_slot8, SQ_COLS, ...} keep working through the re-export).
//! The FA6-pre re-homing note this header carried (the "^
//! re-homing pointer for FA3-wave3") is hereby discharged: single
//! source of truth in the fields tree.
//!
//! Bit-plane obligations (this batch's proof core, the GF8 small
//! orbit):
//!   1. The SquareBytes matrix columns ARE the GF8-square bytes of
//!      the eight basis bytes (upstream :240-251 formulas against the
//!      FA2 GF8::square_bits spread model) -- proven per-column, all
//!      eight, by bv (lemma_sq_cols_basis).
//!   2. The column picture closes the byte plane: the GF8::square_
//!      bits spread model is the XOR-linear map whose basis images
//!      are those columns (lemma_spread_xor_hom /
//!      lemma_gf8_sq_linear: spread GF2-linearity by bv, the
//!      low/high nibble voice images by bv, and the byte-range
//!      lemma).
//!   3. The combined-key duality rows (combined key after
//!      square_inplace == the GF128 square of the combined key) ride
//!      the harness at the sample level over the ORACLE constants
//!      (python-sim == oracle cross-checked full-256, zero
//!      mismatches); the full-256 quantified form needs the FA3 ring
//!      lemmas (mul_spec == hmul and the xor-bilinearity, both
//!      deferrals) and is recorded as D-FA6p-1 in the notes (the
//!      deep handover item to FA6).

use vstd::prelude::*;

use crate::large_fields::{
    gf128_byte_combine, gf128_byte_combine_bits, gf128_byte_combine_bits_spec,
    gf128_byte_combine_slice, gf128_byte_combine_spec,
};
use crate::small_fields::{gf8_ref_square_spread, gf8_square_bits};

use super::field_commitment::FieldCommitDegOne;

verus! {

// ===========================================================================
// Re-homing (FA11-beta): the SquareBytes / ByteCombineSquared GF128
// faces + the GF8-orbit lemma bank now live in the fields seat
// (src/fields/large_fields.rs, FA11-beta section); re-export keeps
// this module's sibling API surface stable (the harness mounts and
// the ByteCommitment faces below name them locally).
// ===========================================================================
pub use crate::large_fields::{
    SQ_COLS, gf128_byte_combine_bits_sq, gf128_byte_combine_sq_slice,
    gf128_square_byte8, gf128_square_byte_inplace, gf8_sq_bits_u8,
    gf8_sq_linear_spec, lemma_gf8_sq_linear, lemma_spread_byte_range,
    lemma_spread_xor_hom, lemma_sq_cols_basis, lemma_sq_linear_xor_hom,
    sqb_slot8,
};
// ===========================================================================
// ByteCommitment (upstream :17-41):
//     #[derive(Clone, Debug, Default)]
//     pub(crate) struct ByteCommitment<F> where F: BigGaloisField {
//         pub(crate) key: u8,
//         pub(crate) tags: Array<F, U8> }
//     impl {
//         pub fn square_inplace(&mut self) {
//             F::square_byte_inplace(self.tags.as_mut_slice());
//             self.key = GF8::square_bits(self.key); }
//         pub fn combine(&self) -> FieldCommitDegOne<F> {
//             FieldCommitDegOne::new(
//                 F::byte_combine_bits(self.key),
//                 F::byte_combine_slice(self.tags.as_slice())) } }
// ===========================================================================

pub struct ByteCommitment {
    /// The committed GF(2^8) byte (the hidden VOLE key byte).
    pub key: u8,
    /// The eight big-field tag slots, one per basis bit of key.
    pub tags: [u128; 8],
}

impl ByteCommitment {
    /// Derived Default (upstream derive: key 0, tags of field zeros).
    pub fn default() -> (o: Self)
        ensures
            o.key == 0u8,
            forall |j: int| 0 <= j < 8 ==> o.tags[j] == 0u128,
    {
        ByteCommitment { key: 0u8, tags: [0u128; 8] }
    }

    /// square_inplace (upstream :30-33): the tag plane squares
    /// through F::square_byte_inplace (the derived in-place twin
    /// above), the key plane through GF8::square_bits (FA2).
    pub fn square_inplace(self: &mut Self)
        ensures
            (final(self).key as u16) == gf8_ref_square_spread(old(self).key as u16),
            final(self).tags[0] == sqb_slot8(0, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[1] == sqb_slot8(1, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[2] == sqb_slot8(2, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[3] == sqb_slot8(3, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[4] == sqb_slot8(4, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[5] == sqb_slot8(5, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[6] == sqb_slot8(6, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
            final(self).tags[7] == sqb_slot8(7, old(self).tags[0], old(self).tags[1], old(self).tags[2], old(self).tags[3], old(self).tags[4], old(self).tags[5], old(self).tags[6], old(self).tags[7]),
    {
        let tag_slice: &mut [u128] = &mut self.tags;
        gf128_square_byte_inplace(tag_slice);
        self.key = gf8_square_bits(self.key);
    }

    /// combine (upstream :35-40): the degree-1 fold back to the big
    /// field -- key plane through byte_combine_bits, tag plane
    /// through byte_combine_slice over the 8 slots.
    pub fn combine(self: &Self) -> (o: FieldCommitDegOne)
        ensures
            o.key == gf128_byte_combine_bits_spec(self.key),
            o.tag[0] == gf128_byte_combine_spec(
                self.tags[0], self.tags[1], self.tags[2], self.tags[3],
                self.tags[4], self.tags[5], self.tags[6], self.tags[7],
            ),
    {
        FieldCommitDegOne::new(
            gf128_byte_combine_bits(self.key),
            gf128_byte_combine_slice(&self.tags),
        )
    }
}

// ===========================================================================
// ByteCommitsRef (upstream :107-150): the slice view.
//     #[derive(Debug, Clone, Copy)]
//     pub(crate) struct ByteCommitsRef<'a, F, L> {
//         pub(crate) keys: &'a Array<u8, L>,
//         pub(crate) tags: &'a Array<F, Prod<L, U8>> }
// The structural 8:1 length relation rides as requires on every
// face; the upstream doc line on from_slices (:122-124 "Panics if
// the lengths of the keys is not equal to the length of the tags
// divided by 8.") re-erects as the from_slices requires (the
// `# Panics` -> requires convention).
// ===========================================================================

pub struct ByteCommitsRef<'a> {
    pub keys: &'a [u8],
    pub tags: &'a [u128],
}

impl<'a> ByteCommitsRef<'a> {
    /// from_slices (upstream :125-130).
    pub fn from_slices(keys: &'a [u8], tags: &'a [u128]) -> (o: Self)
        requires
            keys.len() * 8 == tags.len(),
        ensures
            o.keys@ == keys@,
            o.tags@ == tags@,
    {
        ByteCommitsRef { keys, tags }
    }

    /// get_field_commit (upstream :132-137): identical fold to
    /// ByteCommitment::combine at the indexed byte.
    pub fn get_field_commit(self: &Self, index: usize) -> (o: FieldCommitDegOne)
        requires
            index < self.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.key == gf128_byte_combine_bits_spec(self.keys[index as int]),
            o.tag[0] == gf128_byte_combine_spec(
                self.tags[index * 8],
                self.tags[index * 8 + 1],
                self.tags[index * 8 + 2],
                self.tags[index * 8 + 3],
                self.tags[index * 8 + 4],
                self.tags[index * 8 + 5],
                self.tags[index * 8 + 6],
                self.tags[index * 8 + 7],
            ),
    {
        FieldCommitDegOne::new(
            gf128_byte_combine_bits(self.keys[index]),
            gf128_byte_combine_slice(&self.tags[index * 8..index * 8 + 8]),
        )
    }

    /// get_commits_ref (upstream :139-149, the Ref view; the ByteCommits
    /// view is :76-86): the sub-window view. The typenum L2 size
    /// lowers to the run-time window length l2 (the FA10-pre typenum
    /// precedent); the upstream debug_assert
    /// (start_byte + L2::USIZE <= L::USIZE) re-erects as requires.
    pub fn get_commits_ref(self: &Self, start_byte: usize, l2: usize) -> (o: ByteCommitsRef<'a>)
        requires
            start_byte + l2 <= self.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.keys.len() == l2,
            forall |j: int|
                0 <= j < l2 ==> o.keys[j] == self.keys[start_byte + j],
            o.tags.len() == l2 * 8,
            forall |j: int|
                0 <= j < l2 * 8 ==> o.tags[j] == self.tags[start_byte * 8 + j],
    {
        ByteCommitsRef {
            keys: &self.keys[start_byte..start_byte + l2],
            tags: &self.tags[start_byte * 8..(start_byte + l2) * 8],
        }
    }
}

// ===========================================================================
// ByteCommits (upstream :43-105): the owned container.
//     #[derive(Clone, Debug, Default)]
//     pub(crate) struct ByteCommits<F, L> {
//         pub(crate) keys: Box<Array<u8, L>>,
//         pub(crate) tags: Box<Array<F, Prod<L, U8>>> }
// The Box<Array> pair lowers to the Vec pair with the 8:1 length
// relation as the callsite requires (the FA1 hybrid-array trust
// convention; the structural typenum relation is this twin's
// requirements entry).
// ===========================================================================

pub struct ByteCommits {
    pub keys: Vec<u8>,
    pub tags: Vec<u128>,
}

impl ByteCommits {
    /// new (upstream :58-60); the structural 8:1 length relation
    /// re-erects as requires.
    pub fn new(keys: Vec<u8>, tags: Vec<u128>) -> (o: Self)
        requires
            keys.len() * 8 == tags.len(),
        ensures
            o.keys@ == keys@,
            o.tags@ == tags@,
    {
        ByteCommits { keys, tags }
    }

    /// Derived Default (upstream derive, zero-length-safe with the
    /// 8:1 relation preserved).
    pub fn default() -> (o: Self)
        ensures
            o.keys.len() == 0,
            o.tags.len() == 0,
    {
        ByteCommits {
            keys: Vec::new(),
            tags: Vec::new(),
        }
    }

    /// get_field_commit (upstream :62-67).
    pub fn get_field_commit(self: &Self, index: usize) -> (o: FieldCommitDegOne)
        requires
            index < self.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.key == gf128_byte_combine_bits_spec(self.keys[index as int]),
            o.tag[0] == gf128_byte_combine_spec(
                self.tags[index * 8],
                self.tags[index * 8 + 1],
                self.tags[index * 8 + 2],
                self.tags[index * 8 + 3],
                self.tags[index * 8 + 4],
                self.tags[index * 8 + 5],
                self.tags[index * 8 + 6],
                self.tags[index * 8 + 7],
            ),
    {
        FieldCommitDegOne::new(
            gf128_byte_combine_bits(self.keys[index]),
            gf128_byte_combine_slice(&self.tags[index * 8..index * 8 + 8]),
        )
    }

    /// get_field_commit_sq (upstream :69-74): the squared fold -- key
    /// plane through byte_combine_bits_sq (the GF8::square_bits
    /// composition), tag plane through byte_combine_sq_slice
    /// (square_byte then byte_combine).
    pub fn get_field_commit_sq(self: &Self, index: usize) -> (o: FieldCommitDegOne)
        requires
            index < self.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.key == gf128_byte_combine_bits_spec(gf8_sq_bits_u8(self.keys[index as int])),
            o.tag[0] == gf128_byte_combine_spec(
                sqb_slot8(0, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(1, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(2, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(3, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(4, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(5, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(6, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
                sqb_slot8(7, self.tags[index * 8], self.tags[index * 8 + 1], self.tags[index * 8 + 2], self.tags[index * 8 + 3], self.tags[index * 8 + 4], self.tags[index * 8 + 5], self.tags[index * 8 + 6], self.tags[index * 8 + 7]),
            ),
    {
        FieldCommitDegOne::new(
            gf128_byte_combine_bits_sq(self.keys[index]),
            gf128_byte_combine_sq_slice(&self.tags[index * 8..index * 8 + 8]),
        )
    }

    /// get_commits_ref (upstream :76-86): the sub-window borrow view;
    /// same typenum-L2 lowering as the Ref face above.
    pub fn get_commits_ref(self: &Self, start_byte: usize, l2: usize) -> (o: ByteCommitsRef)
        requires
            start_byte + l2 <= self.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.keys.len() == l2,
            forall |j: int|
                0 <= j < l2 ==> o.keys[j] == self.keys[(start_byte + j) as int],
            o.tags.len() == l2 * 8,
            forall |j: int|
                0 <= j < l2 * 8 ==> o.tags[j] == self.tags[(start_byte * 8 + j) as int],
    {
        ByteCommitsRef {
            keys: &self.keys[start_byte..start_byte + l2],
            tags: &self.tags[start_byte * 8..(start_byte + l2) * 8],
        }
    }

    /// to_ref (upstream :88-93): the full-window borrow view.
    pub fn to_ref(self: &Self) -> (o: ByteCommitsRef)
        requires
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.keys.len() == self.keys.len(),
            forall |j: int|
                0 <= j < self.keys.len() ==> o.keys[j] == self.keys[j as int],
            o.tags.len() == self.tags.len(),
            forall |j: int|
                0 <= j < self.tags.len() ==> o.tags[j] == self.tags[j as int],
    {
        ByteCommitsRef {
            keys: &self.keys,
            tags: &self.tags,
        }
    }

    /// get (upstream :95-100): the per-byte commitment carrier clone.
    pub fn get(self: &Self, idx: usize) -> (o: ByteCommitment)
        requires
            idx < self.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.key == self.keys[idx as int],
            o.tags == [
                self.tags[idx * 8],
                self.tags[idx * 8 + 1],
                self.tags[idx * 8 + 2],
                self.tags[idx * 8 + 3],
                self.tags[idx * 8 + 4],
                self.tags[idx * 8 + 5],
                self.tags[idx * 8 + 6],
                self.tags[idx * 8 + 7],
            ],
    {
        let mut t: [u128; 8] = [0u128; 8];
        let mut j: usize = 0;
        while j < 8
            invariant
                j <= 8,
                idx < self.keys.len(),
                self.keys.len() * 8 == self.tags.len(),
                forall |q: int|
                    0 <= q < j ==> t[q] == self.tags[idx * 8 + q],
            decreases
                8 - j,
        {
            t[j] = self.tags[idx * 8 + j];
            j += 1;
        }
        ByteCommitment { key: self.keys[idx], tags: t }
    }
}

// Records (upstream surfaces outside this twin's lowered scope):
//   - ByteCommits::iter (upstream :102-104, the map(|idx| self.get(idx))
//     iterator): the closure/iterator carrier drops at the iterator
//     boundary; the per-item face IS get above (the FA11 consumers
//     re-spell their loops, the same lattice decision as the FA10
//     byte-mover faces).
//   - The combined-key duality (combined key after square_inplace ==
//     the field square of the combined key) is D-FA6p-1:
//     harness-sample-pinned over the ORACLE constants (python-sim
//     cross-check zero mismatches over the full byte domain), the
//     full-256 quantified form deferred to FA6 (needs the FA3 ring
//     lemmas: mul_spec == hmul and the dword xor-bilinearity).

} // verus!
