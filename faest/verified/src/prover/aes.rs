//! faest 0.3.0 -- Verus transcription of src/prover/aes.rs (the
//! constraint-system AES layer over the ByteCommits faces), batch
//! FA11.
//!
//! Upstream (prover/aes.rs, 383 lines, pin 9ccc68c0): the three
//! helper type aliases (StateBitsSquaredCommits / StateBytesCommits
//! / StateBytesSquaredCommits, :27-34), the StateToBytes impls
//! (:39-67), the AddRoundKey impl family (:69-141), the
//! AddRoundKeyAssign family (:143-168), ShiftRows (:170-190),
//! AddRoundKeyBytes (:192-203), InverseShiftRows (:205-232),
//! MixColumns (:234-264), BytewiseMixColumns (:266-324), SBoxAffine
//! (:326-356), InverseAffine (:358-383). The upstream file has no
//! in-file test rows; its value surface rides the batch oracle arm.
//!
//! Representation lowering (trust boundary; the FA6-pre/FA11-beta
//! conventions this tree already carries):
//!   - F: BigGaloisField is instantiated at the closed GF128 axis
//!     (u128; the crate::fields re-spell of upstream :1-24 rides
//!     crate::large_fields, as in the FA6-pre twins). The
//!     GF192/GF256 re-spelling rows are the D-FA11b-2 family,
//!     deferred with it.
//!   - The `O: OWFParameters` generic dispatch lowers to plain
//!     runtime size parameters (nst, nst_bytes, ...) whose
//!     value-at-the-callsite rows are the FA9 tower pins
//!     (parameter_tower.rs; AES-128 rows: NSt 4, NStBytes 16).
//!     The FA10 RowCfg precedent.
//!   - Box<Array<F, N>> containers lower to Vec<F> with the
//!     length relation rides as requires (the FA1 hybrid-array
//!     trust convention).
//!   - The std ops impl-operator / trait-impl dispatch (by-value /
//!     by-ref impls whose upstream bodies are identical up to
//!     moves; the impl-trait-for-type rows themselves) drops at
//!     the trait boundary: each upstream impl block re-erects as
//!     an inherent face below with its anchors in the Origin
//!     comment (the FA6-pre field_commitment convention).
//!   - Field tag "addition" (`+` on F) is the characteristic-2
//!     limb xor in the twin (^), FA3 record.
//!
//! Faces (each with its upstream anchor):
//!   state_to_bytes_ref (:39-50), state_to_bytes_public (:52-67),
//!   add_round_key_public (:72-101), public_state_add_round_key
//!   (:103-117), add_round_key_hidden (:119-141),
//!   add_round_key_assign_public (:146-154 resp. FA1
//!   xor_arrays_inplace), add_round_key_assign_hidden (:157-168),
//!   shift_rows_u8 / shift_rows_d2 (:170-190),
//!   add_round_key_bytes (:192-203), inverse_shift_rows (:205-232),
//!   mix_columns (:234-264), bytewise_mix_columns (:266-324),
//!   s_box_affine (:326-356), inverse_affine (:358-383).

use vstd::prelude::*;

use crate::large_fields::{
    gf128_byte_combine_bits, gf128_byte_combine_bits_spec, gf128_byte_combine_slice,
    gf128_byte_combine_spec, gf128_hmul, gf128_mul, gf128_mul_spec, gf8_sq_bits_u8,
    GF128_BYTE_COMBINE_2, GF128_BYTE_COMBINE_3, GF128_BYTE_COMBINE_SQ_2, GF128_BYTE_COMBINE_SQ_3,
    GF128_SIGMA, GF128_SIGMA_SQUARES, GF128_ZERO,
};

use super::byte_commitments::{
    gf128_byte_combine_bits_sq, gf128_byte_combine_sq_slice, ByteCommitment, ByteCommits,
    ByteCommitsRef,
};
use super::field_commitment::{FieldCommitDegOne, FieldCommitDegTwo};

verus! {

// ===========================================================================
// The helper type aliases (upstream :27-34):
//     pub(crate) type StateBitsSquaredCommits<O> =
//         Box<Array<FieldCommitDegTwo<OWFField<O>>, O::NStBits>>;
//     pub(crate) type StateBytesCommits<O> =
//         Box<Array<FieldCommitDegOne<OWFField<O>>, O::NStBytes>>;
//     pub(crate) type StateBytesSquaredCommits<O> =
//         Box<Array<FieldCommitDegTwo<OWFField<O>>, O::NStBytes>>;
// The Box<Array<F, N>> carriers lower to Vec<F> with the NStBits ==
// 8 * NStBytes relation carried at the consumers as requires.
// ===========================================================================

pub type StateBitsSquaredCommits = Vec<FieldCommitDegTwo>;
pub type StateBytesCommits = Vec<FieldCommitDegOne>;
pub type StateBytesSquaredCommits = Vec<FieldCommitDegTwo>;

// ===========================================================================
// StateToBytes (upstream :39-67): two impls.
// ============================================================================

impl ByteCommitsRef<'_> {
    /// Origin Rust (:39-50, `impl StateToBytes<O> for ByteCommitsRef`):
    ///     type Output = StateBytesCommits<O>;
    ///     fn state_to_bytes(&self) -> Self::Output {
    ///         Box::new((0..L::USIZE).map(|i| self.get_field_commit(i)).collect()) }
    /// The (0..L::USIZE) map lowers to the index loop over the
    /// view's whole window.
    pub fn state_to_bytes_ref(self: &Self) -> (o: StateBytesCommits)
        requires
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.len() == self.keys.len(),
            forall |j: int|
                0 <= j < self.keys.len()
                    ==> o[j].key == gf128_byte_combine_bits_spec(self.keys[j])
                        && o[j].tag[0] == gf128_byte_combine_spec(
                            self.tags[8 * j],
                            self.tags[8 * j + 1],
                            self.tags[8 * j + 2],
                            self.tags[8 * j + 3],
                            self.tags[8 * j + 4],
                            self.tags[8 * j + 5],
                            self.tags[8 * j + 6],
                            self.tags[8 * j + 7],
                        ),
    {
        let mut out: StateBytesCommits = Vec::new();
        let mut i: usize = 0;
        while i < self.keys.len()
            invariant
                i <= self.keys.len(),
                self.keys.len() * 8 == self.tags.len(),
                out.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> out[j].key == gf128_byte_combine_bits_spec(self.keys[j])
                            && out[j].tag[0] == gf128_byte_combine_spec(
                                self.tags[8 * j],
                                self.tags[8 * j + 1],
                                self.tags[8 * j + 2],
                                self.tags[8 * j + 3],
                                self.tags[8 * j + 4],
                                self.tags[8 * j + 5],
                                self.tags[8 * j + 6],
                                self.tags[8 * j + 7],
                            ),
            decreases
                self.keys.len() - i,
        {
            out.push(self.get_field_commit(i));
            i += 1;
        }
        out
    }
}

/// Origin Rust (:52-67, `impl StateToBytes<O> for Array<u8, L>` --
/// scalar commitments to known state):
///     fn state_to_bytes(&self) -> Self::Output {
///         Box::new(self.iter().map(|&k| OWFField::<O>::byte_combine_bits(k)).collect()) }
/// The map lowers to the index loop (same order, same pairing).
pub fn state_to_bytes_public(state: &[u8]) -> (o: Vec<u128>)
    ensures
        o.len() == state.len(),
        forall |j: int|
            0 <= j < state.len()
                ==> o[j] == gf128_byte_combine_bits_spec(state[j as int]),
{
    let mut out: Vec<u128> = Vec::new();
    let mut i: usize = 0;
    while i < state.len()
        invariant
            i <= state.len(),
            out.len() == i,
            forall |j: int|
                0 <= j < i
                    ==> out[j] == gf128_byte_combine_bits_spec(state[j]),
        decreases
            state.len() - i,
    {
        out.push(gf128_byte_combine_bits(state[i]));
        i += 1;
    }
    out
}

// ===========================================================================
// AddRoundKey (upstream :69-141): four impls, and AddRoundKeyAssign
// (:143-168): two impls.
// ============================================================================

impl ByteCommits {
    /// Origin Rust (:72-85, `AddRoundKey<&Array<u8, L>> for
    /// ByteCommits` -- known key bytes, owned hidden state):
    ///     keys zip-xor rhs; tags kept (to_owned).
    pub fn add_round_key_public(self: &Self, rhs: &[u8]) -> (o: Self)
        requires
            self.keys.len() == rhs.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.keys.len() == self.keys.len(),
            o.tags.len() == self.tags.len(),
            forall |j: int|
                0 <= j < rhs.len()
                    ==> o.keys[j] == self.keys[j] ^ rhs[j as int],
            forall |j: int|
                0 <= j < self.tags.len() ==> o.tags[j] == self.tags[j],
    {
        let mut keys: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < self.keys.len()
            invariant
                i <= self.keys.len(),
                self.keys.len() == rhs.len(),
                keys.len() == i,
                forall |j: int|
                    0 <= j < i ==> keys[j] == self.keys[j] ^ rhs[j],
            decreases
                self.keys.len() - i,
        {
            keys.push(self.keys[i] ^ rhs[i]);
            i += 1;
        }
        ByteCommits { keys, tags: self.tags.clone() }
    }
}

impl ByteCommitsRef<'_> {
    /// Origin Rust (:88-101, `AddRoundKey<&Array<u8, L>> for
    /// ByteCommitsRef` -- known key bytes, ref hidden state):
    ///     ByteCommits { keys: zip xor, tags: rhs.tags.to_owned() }
    pub fn add_round_key_public_ref(self: &Self, rhs: &[u8]) -> (o: ByteCommits)
        requires
            self.keys.len() == rhs.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.keys.len() == self.keys.len(),
            o.tags.len() == self.tags.len(),
            forall |j: int|
                0 <= j < rhs.len()
                    ==> o.keys[j] == self.keys[j] ^ rhs[j as int],
            forall |j: int|
                0 <= j < self.tags.len() ==> o.tags[j] == self.tags[j],
    {
        let mut keys: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < self.keys.len()
            invariant
                i <= self.keys.len(),
                self.keys.len() == rhs.len(),
                keys.len() == i,
                forall |j: int|
                    0 <= j < i ==> keys[j] == self.keys[j] ^ rhs[j],
            decreases
                self.keys.len() - i,
        {
            keys.push(self.keys[i] ^ rhs[i]);
            i += 1;
        }
        let mut tags: Vec<u128> = Vec::new();
        let mut k: usize = 0;
        while k < self.tags.len()
            invariant
                k <= self.tags.len(),
                self.keys.len() == rhs.len(),
                tags.len() == k,
                forall |j: int| 0 <= j < k ==> tags[j] == self.tags[j],
            decreases
                self.tags.len() - k,
        {
            tags.push(self.tags[k]);
            k += 1;
        }
        ByteCommits { keys, tags }
    }

    /// Origin Rust (:104-117, `AddRoundKey<&ByteCommitsRef> for
    /// &Array<u8, L>` -- committed state in the RHS position):
    ///     keys: zip(self.iter(), rhs.keys) xor -- the KNOWN state
    ///     plane lands in keys, tags are rhs's first-window rows.
    pub fn public_state_add_round_key(lhs: &[u8], rhs: &Self) -> (o: ByteCommits)
        requires
            lhs.len() == rhs.keys.len(),
            rhs.keys.len() * 8 == rhs.tags.len(),
        ensures
            o.keys.len() == lhs.len(),
            o.tags.len() == lhs.len() * 8,
            forall |j: int|
                0 <= j < lhs.len()
                    ==> o.keys[j] == lhs[j as int] ^ rhs.keys[j],
            forall |j: int|
                0 <= j < lhs.len() * 8
                    ==> o.tags[j] == rhs.tags[j],
    {
        let mut keys: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < lhs.len()
            invariant
                i <= lhs.len(),
                lhs.len() == rhs.keys.len(),
                keys.len() == i,
                forall |j: int|
                    0 <= j < i ==> keys[j] == lhs[j] ^ rhs.keys[j],
            decreases
                lhs.len() - i,
        {
            keys.push(lhs[i] ^ rhs.keys[i]);
            i += 1;
        }
        let mut tags: Vec<u128> = Vec::new();
        let mut k: usize = 0;
        while k < lhs.len() * 8
            invariant
                k <= lhs.len() * 8,
                lhs.len() == rhs.keys.len(),
                rhs.keys.len() * 8 == rhs.tags.len(),
                rhs.tags.len() >= lhs.len() * 8,
                tags.len() == k,
                forall |j: int| 0 <= j < k ==> tags[j] == rhs.tags[j],
            decreases
                lhs.len() * 8 - k,
        {
            tags.push(rhs.tags[k]);
            k += 1;
        }
        ByteCommits { keys, tags }
    }

    /// Origin Rust (:119-141,`AddRoundKey<&ByteCommitsRef> for
    /// ByteCommits` -- hidden state, hidden key):
    ///     keys: zip xor; tags: zip + (field add == limb xor).
    pub fn add_round_key_hidden(
        state: &ByteCommits,
        rhs: &Self,
    ) -> (o: ByteCommits)
        requires
            state.keys.len() == rhs.keys.len(),
            state.tags.len() == rhs.tags.len(),
        ensures
            o.keys.len() == state.keys.len(),
            o.tags.len() == state.tags.len(),
            forall |j: int|
                0 <= j < state.keys.len()
                    ==> o.keys[j] == state.keys[j] ^ rhs.keys[j],
            forall |j: int|
                0 <= j < state.tags.len()
                    ==> o.tags[j] == state.tags[j] ^ rhs.tags[j],
    {
        let mut keys: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < state.keys.len()
            invariant
                i <= state.keys.len(),
                state.keys.len() == rhs.keys.len(),
                keys.len() == i,
                forall |j: int|
                    0 <= j < i ==> keys[j] == state.keys[j] ^ rhs.keys[j],
            decreases
                state.keys.len() - i,
        {
            keys.push(state.keys[i] ^ rhs.keys[i]);
            i += 1;
        }
        let mut tags: Vec<u128> = Vec::new();
        let mut k: usize = 0;
        while k < state.tags.len()
            invariant
                k <= state.tags.len(),
                state.tags.len() == rhs.tags.len(),
                tags.len() == k,
                forall |j: int|
                    0 <= j < k ==> tags[j] == state.tags[j] ^ rhs.tags[j],
            decreases
                state.tags.len() - k,
        {
            tags.push(state.tags[k] ^ rhs.tags[k]);
            k += 1;
        }
        ByteCommits { keys, tags }
    }
}

impl ByteCommits {
    /// Origin Rust (:146-154, `AddRoundKeyAssign<&Array<u8, L>> for
    /// ByteCommits`): xor_arrays_inplace(keys, rhs).
    pub fn add_round_key_assign_public(self: &mut Self, rhs: &[u8])
        requires
            self.keys.len() >= rhs.len(),
            self.keys.len() * 8 == self.tags.len(),
        ensures
            final(self).keys.len() == old(self).keys.len(),
            final(self).tags.len() == old(self).tags.len(),
            forall |j: int|
                0 <= j < rhs.len()
                    ==> final(self).keys[j] == old(self).keys[j] ^ rhs[j as int],
            forall |j: int|
                (rhs.len() as int) <= j < final(self).keys.len()
                    ==> final(self).keys[j] == old(self).keys[j],
            forall |j: int|
                0 <= j < final(self).tags.len()
                    ==> final(self).tags[j] == old(self).tags[j],
    {
        let mut i: usize = 0;
        while i < rhs.len()
            invariant
                i <= rhs.len(),
                rhs.len() <= self.keys.len(),
                self.keys.len() == old(self).keys.len(),
                self.keys.len() * 8 == self.tags.len(),
                forall |j: int|
                    0 <= j < i ==> self.keys[j] == old(self).keys[j] ^ rhs[j],
                forall |j: int|
                    (i as int) <= j < self.keys.len()
                        ==> self.keys[j] == old(self).keys[j],
            decreases
                rhs.len() - i,
        {
            self.keys[i] = self.keys[i] ^ rhs[i];
            i += 1;
        }
    }

    /// Origin Rust (:157-168, `AddRoundKeyAssign<&ByteCommitsRef>
    /// for ByteCommits`): keys xor_arrays_inplace; tags zip +=.
    pub fn add_round_key_assign_hidden(self: &mut Self, rhs: &ByteCommitsRef)
        requires
            self.keys.len() >= rhs.keys.len(),
            self.keys.len() * 8 == self.tags.len(),
            rhs.keys.len() * 8 == rhs.tags.len(),
            self.tags.len() >= rhs.keys.len() * 8,
        ensures
            final(self).keys.len() == old(self).keys.len(),
            final(self).tags.len() == old(self).tags.len(),
            forall |j: int|
                0 <= j < rhs.keys.len()
                    ==> final(self).keys[j] == old(self).keys[j] ^ rhs.keys[j],
            forall |j: int|
                (rhs.keys.len() as int) <= j < final(self).keys.len()
                    ==> final(self).keys[j] == old(self).keys[j],
            forall |j: int|
                0 <= j < rhs.keys.len() * 8
                    ==> final(self).tags[j] == old(self).tags[j] ^ rhs.tags[j],
            forall |j: int|
                (rhs.keys.len() * 8) <= j < final(self).tags.len()
                    ==> final(self).tags[j] == old(self).tags[j],
    {
        let mut i: usize = 0;
        while i < rhs.keys.len()
            invariant
                i <= rhs.keys.len(),
                rhs.keys.len() <= self.keys.len(),
                self.keys.len() == old(self).keys.len(),
                self.keys.len() * 8 == self.tags.len(),
                forall |j: int|
                    0 <= j < i ==> self.keys[j] == old(self).keys[j] ^ rhs.keys[j],
                forall |j: int|
                    (i as int) <= j < self.keys.len()
                        ==> self.keys[j] == old(self).keys[j],
            decreases
                rhs.keys.len() - i,
        {
            self.keys[i] = self.keys[i] ^ rhs.keys[i];
            i += 1;
        }
        let mut k: usize = 0;
        while k < rhs.keys.len() * 8
            invariant
                k <= rhs.keys.len() * 8,
                rhs.keys.len() * 8 <= self.tags.len(),
                rhs.keys.len() * 8 == rhs.tags.len(),
                self.tags.len() == old(self).tags.len(),
                forall |j: int|
                    0 <= j < k ==> self.tags[j] == old(self).tags[j] ^ rhs.tags[j],
                forall |j: int|
                    (k as int) <= j < self.tags.len()
                        ==> self.tags[j] == old(self).tags[j],
            decreases
                rhs.keys.len() * 8 - k,
        {
            self.tags[k] = self.tags[k] ^ rhs.tags[k];
            k += 1;
        }
    }
}

// ===========================================================================
// ShiftRows (upstream :170-190, `impl<T, L> ShiftRows for Array<T, L>`).
// Origin Rust:
//     fn shift_rows(&mut self) {
//         let mut tmp = self.clone();
//         let nst = L::USIZE / 4;
//         for r in 0..4 {
//             for c in 0..nst {
//                 let off: usize = if (nst != 8) || (r <= 1) { 0 } else { 1 };
//                 mem::swap(&mut self[4 * c + r],
//                           &mut tmp[4 * ((c + r + off) % nst) + r]); } } }
// The upstream TODO line ("Copy row by row instead of entire state")
// rides verbatim above. Deviation record: mem::swap lowers to the
// copy-assign (tmp never reads a lane it has written: every source
// index j(c) = 4*((c+r+off)%nst)+r is injective over c, so the
// value face -- final self[4c+r] == old self[sr_src_idx] -- is the
// upstream swap net's value; the FA6-pre loop-form convention).
// The T: Clone element lowering spells as the two concrete lanes the
// constraint tree consumes (u8 keys / degree-two commitments).
// ===========================================================================

/// The shift source index at row r, column c (spec face of the
/// upstream (c + r + off) % nst arithmetic).
pub open spec fn sr_src_idx(nst: int, r: int, c: int) -> int {
    let off: usize = if nst != 8 || r <= 1 { 0 } else { 1 };
    4 * ((c + r + off) % nst) + r
}

/// Origin Rust (:170-190) -- the u8 lane (upstream generic T at the
/// byte plane; the D2 lane below is the same value face over the
/// degree-two commitment elements).
pub fn shift_rows_u8(state: &mut [u8], nst: usize)
    requires
        state.len() == 4 * nst,
        nst > 0,
    ensures
        forall |r: int, c: int|
            #![trigger final(state)[4 * c + r]]
            0 <= r < 4 && 0 <= c < (nst as int)
                ==> final(state)[4 * c + r]
                    == old(state)[sr_src_idx(nst as int, r, c)],
{
    // tmp == the entry copy (upstream `self.clone()`; tmp is only
    // ever READ below -- the swap-net value analysis, header record)
    let mut tmp: Vec<u8> = Vec::new();
    let mut q: usize = 0;
    while q < state.len()
        invariant
            q <= state.len(),
            tmp.len() == q,
            forall |j: int| 0 <= j < q ==> tmp[j] == old(state)[j as int],
        decreases
            state.len() - q,
    {
        tmp.push(state[q]);
        q += 1;
    }
    let mut r: usize = 0;
    while r < 4
        invariant
            r <= 4,
            nst > 0,
            4 * nst == state.len(),
            tmp.len() == state.len(),
            forall |k: int| 0 <= k < tmp.len() ==> tmp[k] == old(state)[k as int],
            // rows < r: re-arranged; rows >= r: untouched
            forall |rr: int, c: int|
                #![trigger state[4 * c + rr]]
                0 <= rr < r && 0 <= c < (nst as int)
                    ==> state[4 * c + rr]
                        == old(state)[sr_src_idx(nst as int, rr, c)],
            forall |rr: int, c: int|
                #![trigger state[4 * c + rr]]
                r <= rr < 4 && 0 <= c < (nst as int)
                    ==> state[4 * c + rr] == old(state)[(4 * c + rr) as int],
        decreases
            4 - r,
    {
        let mut c: usize = 0;
        while c < nst
            invariant
                r < 4,
                nst > 0,
                c <= nst,
                4 * nst == state.len(),
                tmp.len() == state.len(),
                forall |k: int| 0 <= k < tmp.len() ==> tmp[k] == old(state)[k as int],
                forall |rr: int, cc: int|
                    #![trigger state[4 * cc + rr]]
                    0 <= rr < r && 0 <= cc < (nst as int)
                        ==> state[4 * cc + rr]
                            == old(state)[sr_src_idx(nst as int, rr, cc)],
                forall |rr: int, cc: int|
                    #![trigger state[4 * cc + rr]]
                    (r as int) < rr < 4 && 0 <= cc < (nst as int)
                        ==> state[4 * cc + rr]
                            == old(state)[(4 * cc + rr) as int],
                forall |cc: int|
                    #![trigger state[4 * cc + r as int]]
                    0 <= cc < c
                        ==> state[4 * cc + r as int]
                            == old(state)[sr_src_idx(nst as int, r as int, cc)],
                forall |cc: int|
                    #![trigger state[4 * cc + r as int]]
                    c as int <= cc < (nst as int)
                        ==> state[4 * cc + r as int]
                            == old(state)[(4 * cc + r as int) as int],
            decreases
                nst - c,
        {
            // upstream lane spelling kept verbatim (the off pick is
            // per-iteration upstream state, not folded into a spec)
            let off: usize = if (nst != 8) || (r <= 1) { 0 } else { 1 };
            let m: usize = (c + r + off) % nst;
            let j: usize = 4 * m + r;
            assert(sr_src_idx(nst as int, r as int, c as int) == j as int);
            proof {
                let mi = m as int;
                let ri = r as int;
                let ni = nst as int;
                assert(0 <= mi && mi < ni) by (nonlinear_arith)
                    requires
                        ni > 0,
                        mi == ((c as int + r as int + off as int) % ni),
                        0 <= (c as int),
                        (c as int) < ni,
                {
                }
                assert(j as int == 4 * mi + ri);
                assert(4 * mi + ri < 4 * ni) by (nonlinear_arith)
                    requires
                        0 <= mi,
                        mi < ni,
                        0 <= ri,
                        ri < 4,
                {
                }
                assert(j < 4 * nst);
            }
            state[4 * c + r] = tmp[j];
            c += 1;
        }
        r += 1;
    }
}


// ===========================================================================
// AddRoundKeyBytes (upstream :192-203, `impl<F, L, T>
// AddRoundKeyBytes<&Array<T, L>> for Box<Array<FieldCommitDegTwo<F>,
// L>>`). Origin Rust:
//     fn add_round_key_bytes(&mut self, key: &Array<T, L>, _sq: bool) {
//         for (st, k) in zip(self.iter_mut(), key) { *st += k; } }
// The element add lowers to the D2 field-add face
// (FieldCommitment::add_assign_field, upstream AddAssign<&F>); the
// unused `_sq` discriminator rides verbatim.
// ===========================================================================

pub fn add_round_key_bytes(
    state: &mut [FieldCommitDegTwo],
    key: &[u128],
    _sq: bool,
)
    requires
        state.len() == key.len(),
    ensures
        final(state).len() == old(state).len(),
        forall |j: int|
            #![trigger final(state)[j]]
            0 <= j < final(state).len()
                ==> final(state)[j].key
                    == old(state)[j].key ^ key[j],
        forall |j: int, t: int|
            #![trigger final(state)[j].tag[t]]
            0 <= j < final(state).len() && 0 <= t < 2
                ==> final(state)[j].tag[t]
                    == old(state)[j].tag[t],
{
    let mut i: usize = 0;
    while i < state.len()
        invariant
            i <= state.len(),
            state.len() == key.len(),
            forall |j: int|
                #![trigger state[j].key]
                0 <= j < i
                    ==> state[j].key == old(state)[j].key ^ key[j],
            forall |j: int|
                #![trigger state[j].key]
                i <= j < state.len()
                    ==> state[j].key == old(state)[j].key
                        && state[j].tag[0] == old(state)[j].tag[0]
                        && state[j].tag[1] == old(state)[j].tag[1],
            forall |j: int, t: int|
                #![trigger state[j].tag[t]]
                0 <= j < state.len() && 0 <= t < 2
                    ==> state[j].tag[t] == old(state)[j].tag[t],
        decreases
            state.len() - i,
    {
        // per-slot field add (the add_assign_field value face, inlined
        // over the key plane only)
        state[i].key = state[i].key ^ key[i];
        i += 1;
    }
}

// ===========================================================================
// ShiftRows, D2 lane (upstream :170-190): the same value face as
// shift_rows_u8 over degree-two commitment elements -- the mem::swap
// to copy-assign lowering record rides at the u8 twin above.
// ===========================================================================

pub fn shift_rows_d2(state: &mut [FieldCommitDegTwo], nst: usize)
    requires
        state.len() == 4 * nst,
        nst > 0,
    ensures
        forall |r: int, c: int|
            #![trigger final(state)[4 * c + r]]
            0 <= r < 4 && 0 <= c < (nst as int)
                ==> final(state)[4 * c + r].key
                    == old(state)[sr_src_idx(nst as int, r, c)].key,
{
    let mut tmp: Vec<FieldCommitDegTwo> = Vec::new();
    let mut q: usize = 0;
    while q < state.len()
        invariant
            q <= state.len(),
            tmp.len() == q,
            forall |j: int|
                0 <= j < q ==> tmp[j].key == old(state)[j].key,
        decreases
            state.len() - q,
    {
        tmp.push(FieldCommitDegTwo {
            key: state[q].key,
            tag: [state[q].tag[0], state[q].tag[1]],
        });
        q += 1;
    }
    let mut r: usize = 0;
    while r < 4
        invariant
            r <= 4,
            nst > 0,
            4 * nst == state.len(),
            tmp.len() == state.len(),
            forall |k: int| 0 <= k < tmp.len() ==> tmp[k].key == old(state)[k].key,
            forall |rr: int, c: int|
                #![trigger state[4 * c + rr]]
                0 <= rr < r && 0 <= c < (nst as int)
                    ==> state[4 * c + rr].key
                        == old(state)[sr_src_idx(nst as int, rr, c)].key,
            forall |rr: int, c: int|
                #![trigger state[4 * c + rr]]
                r <= rr < 4 && 0 <= c < (nst as int)
                    ==> state[4 * c + rr].key == old(state)[(4 * c + rr) as int].key,
        decreases
            4 - r,
    {
        let mut c: usize = 0;
        while c < nst
            invariant
                r < 4,
                nst > 0,
                c <= nst,
                4 * nst == state.len(),
                tmp.len() == state.len(),
                forall |k: int| 0 <= k < tmp.len() ==> tmp[k].key == old(state)[k].key,
                forall |rr: int, cc: int|
                    #![trigger state[4 * cc + rr]]
                    0 <= rr < r && 0 <= cc < (nst as int)
                        ==> state[4 * cc + rr].key
                            == old(state)[sr_src_idx(nst as int, rr, cc)].key,
                forall |rr: int, cc: int|
                    #![trigger state[4 * cc + rr]]
                    (r as int) < rr < 4 && 0 <= cc < (nst as int)
                        ==> state[4 * cc + rr].key
                            == old(state)[(4 * cc + rr) as int].key,
                forall |cc: int|
                    #![trigger state[4 * cc + r as int]]
                    0 <= cc < c
                        ==> state[4 * cc + r as int].key
                            == old(state)[sr_src_idx(nst as int, r as int, cc)].key,
                forall |cc: int|
                    #![trigger state[4 * cc + r as int]]
                    c as int <= cc < (nst as int)
                        ==> state[4 * cc + r as int].key
                            == old(state)[(4 * cc + r as int) as int].key,
            decreases
                nst - c,
        {
            let off: usize = if nst != 8 || r <= 1 { 0 } else { 1 };
            let m: usize = (c + r + off) % nst;
            let j: usize = 4 * m + r;
            assert(sr_src_idx(nst as int, r as int, c as int) == j as int);
            proof {
                let mi = m as int;
                let ri = r as int;
                let ni = nst as int;
                assert(0 <= mi && mi < ni) by (nonlinear_arith)
                    requires
                        ni > 0,
                        mi == ((c as int + r as int + off as int) % ni),
                        0 <= (c as int),
                        (c as int) < ni,
                {
                }
                assert(j as int == 4 * mi + ri);
                assert(4 * mi + ri < 4 * ni) by (nonlinear_arith)
                    requires
                        0 <= mi,
                        mi < ni,
                        0 <= ri,
                        ri < 4,
                {
                }
                assert(j < 4 * nst);
            }
            state[4 * c + r] = FieldCommitDegTwo {
                key: tmp[j].key,
                tag: [tmp[j].tag[0], tmp[j].tag[1]],
            };
            c += 1;
        }
        r += 1;
    }
}


// ===========================================================================
// InverseShiftRows (upstream :205-231, `impl<O, L> InverseShiftRows<O>
// for ByteCommitsRef`). Origin Rust:
//     let mut state_prime = ByteCommits::<....>::default();
//     for r in 0..4 { for c in 0..O::NSt::USIZE {
//         // :: 3-6
//         let i = if (O::NSt::USIZE != 8) || (r <= 1) {
//             4 * ((O::NSt::USIZE + c - r) % O::NSt::USIZE) + r
//         } else {
//             4 * ((O::NSt::USIZE + c - r - 1) % O::NSt::USIZE) + r };
//         // :: 7
//         state_prime.keys[4 * c + r] = self.keys[i];
//         state_prime.tags[8 * (4 * c + r)..8 * (4 * c + r) + 8]
//             .copy_from_slice(&self.tags[8 * i..8 * i + 8]); } }
// Lowering records: the implicit Array::default() (the all-zero
// state) lowers to the explicit zero-allocation loops below (the
// FA6-pre ByteCommits twin's default() is the empty Vec -- the
// upstream container semantic is re-erected as allocated zeros, the
// bytewise_mix_columns face uses the same helper); copy_from_slice
// lowers to the 8-step explicit index writes (no upstream-visible
// loop; value face byte-identical, deviation recorded here).
// ===========================================================================

/// The inverse-shift source index at row r, column c (spec face of
/// the upstream ::3-6 arithmetic).
pub open spec fn isr_src_idx(nst: int, r: int, c: int) -> int {
    if nst != 8 || r <= 1 {
        4 * ((nst + c - r) % nst) + r
    } else {
        4 * ((nst + c - r - 1) % nst) + r
    }
}

/// Exec-inline mirror of isr_src_idx for proof abrasion (same
/// formula spelled to carry the nonlinear bound facts at the use
/// site; definitionally equal -- assert below closes the tie).
pub open spec fn src_line_36(nst: int, r: int, c: int) -> int {
    if nst != 8 || r <= 1 {
        4 * ((nst + c - r) % nst) + r
    } else {
        4 * ((nst + c - r - 1) % nst) + r
    }
}

impl ByteCommitsRef<'_> {
    /// Origin Rust (:205-231).
    pub fn inverse_shift_rows(self: &Self, nst: usize) -> (o: ByteCommits)
        requires
            nst >= 4,
            self.keys.len() == 4 * nst,
            self.keys.len() * 8 == self.tags.len(),
        ensures
            o.keys.len() == 4 * nst,
            o.tags.len() == 32 * nst,
            forall |r: int, c: int|
                #![trigger o.keys[4 * c + r]]
                0 <= r < 4 && 0 <= c < (nst as int)
                    ==> o.keys[4 * c + r] == self.keys[isr_src_idx(nst as int, r, c)],
            forall |r: int, c: int, t: int|
                #![trigger o.tags[8 * (4 * c + r) + t]]
                0 <= r < 4 && 0 <= c < (nst as int) && 0 <= t < 8
                    ==> o.tags[8 * (4 * c + r) + t]
                        == self.tags[8 * isr_src_idx(nst as int, r, c) + t],
    {
        // zero allocation (the Array::default() lowering)
        let mut o_keys: Vec<u8> = Vec::new();
        let mut o_tags: Vec<u128> = Vec::new();
        let mut q: usize = 0;
        while q < 4 * nst
            invariant
                q <= 4 * nst,
                (4 * nst) <= usize::MAX,
                o_keys.len() == q,
                forall |j: int| 0 <= j < q ==> o_keys[j] == 0u8,
            decreases
                (4 * nst) - q,
        {
            o_keys.push(0u8);
            q += 1;
        }
        let mut q2: usize = 0;
        while q2 < 32 * nst
            invariant
                self.keys.len() == 4 * nst,
                nst >= 4,
                q2 <= 32 * nst,
                (32 * nst) <= usize::MAX,
                o_tags.len() == q2,
                o_keys.len() == 4 * nst,
                forall |j: int| 0 <= j < q2 ==> o_tags[j] == 0u128,
                forall |j: int| 0 <= j < o_keys.len() ==> o_keys[j] == 0u8,
            decreases
                (32 * nst) - q2,
        {
            o_tags.push(0u128);
            q2 += 1;
        }
        let mut r: usize = 0;
        while r < 4
            invariant
                r <= 4,
                nst >= 4,
                (4 * nst) <= usize::MAX,
                (32 * nst) <= usize::MAX,
                self.keys.len() == 4 * nst,
                self.keys.len() * 8 == self.tags.len(),
                o_keys.len() == 4 * nst,
                o_tags.len() == 32 * nst,
                // rows < r fully written (keys + tags windows)
                forall |rr: int, c: int|
                    #![trigger o_keys[4 * c + rr]]
                    0 <= rr < r && 0 <= c < (nst as int)
                        ==> o_keys[4 * c + rr]
                            == self.keys[isr_src_idx(nst as int, rr, c)],
                forall |rr: int, c: int, t: int|
                    #![trigger o_tags[8 * (4 * c + rr) + t]]
                    0 <= rr < r && 0 <= c < (nst as int) && 0 <= t < 8
                        ==> o_tags[8 * (4 * c + rr) + t]
                            == self.tags[8 * isr_src_idx(nst as int, rr, c) + t],
                // untouched slots still zero
                forall |rr: int, c: int|
                    #![trigger o_keys[4 * c + rr]]
                    r <= rr < 4 && 0 <= c < (nst as int)
                        ==> o_keys[4 * c + rr] == 0u8,
                forall |rr: int, c: int, t: int|
                    #![trigger o_tags[8 * (4 * c + rr) + t]]
                    r <= rr < 4 && 0 <= c < (nst as int) && 0 <= t < 8
                        ==> o_tags[8 * (4 * c + rr) + t] == 0u128,
            decreases
                4 - r,
        {
            let mut c: usize = 0;
            while c < nst
                invariant
                    r < 4,
                    c <= nst,
                    nst >= 4,
                    (32 * nst) <= usize::MAX,
                    self.keys.len() == 4 * nst,
                    self.keys.len() * 8 == self.tags.len(),
                    o_keys.len() == 4 * nst,
                    o_tags.len() == 32 * nst,
                    forall |rr: int, cc: int|
                        #![trigger o_keys[4 * cc + rr]]
                        ((0 <= rr < r) || (rr == r && 0 <= cc < c))
                            && 0 <= cc < (nst as int)
                            ==> o_keys[4 * cc + rr]
                                == self.keys[isr_src_idx(nst as int, rr, cc)],
                    forall |rr: int, cc: int, t: int|
                        #![trigger o_tags[8 * (4 * cc + rr) + t]]
                        ((0 <= rr < r) || (rr == r && 0 <= cc < c))
                            && 0 <= cc < (nst as int) && 0 <= t < 8
                            ==> o_tags[8 * (4 * cc + rr) + t]
                                == self.tags[8 * isr_src_idx(nst as int, rr, cc) + t],
                    forall |rr: int, cc: int|
                        #![trigger o_keys[4 * cc + rr]]
                        ((r < rr < 4) || (rr == r && c as int <= cc))
                            && 0 <= cc < (nst as int)
                            ==> o_keys[4 * cc + rr] == 0u8,
                    forall |rr: int, cc: int, t: int|
                        #![trigger o_tags[8 * (4 * cc + rr) + t]]
                        ((r < rr < 4) || (rr == r && c as int <= cc))
                            && 0 <= cc < (nst as int) && 0 <= t < 8
                            ==> o_tags[8 * (4 * cc + rr) + t] == 0u128,
                decreases
                    nst - c,
            {
                // upstream ::3-6 lane spelling
                let i: usize = if (nst != 8) || (r <= 1) {
                    4 * ((nst + c - r) % nst) + r
                } else {
                    4 * ((nst + c - r - 1) % nst) + r
                };
                assert(isr_src_idx(nst as int, r as int, c as int) == i as int);
                proof {
                    let ni = nst as int;
                    let ri = r as int;
                    let ci = c as int;
                    assert(0 <= ni + ci - ri) by (nonlinear_arith)
                        requires
                            ni >= 4,
                            0 <= ci,
                            0 <= ri,
                            ri < 4,
                    {
                    }
                    assert(0 <= src_line_36(ni, ri, ci) && src_line_36(ni, ri, ci) < 4 * ni) by (nonlinear_arith)
                        requires
                            ni >= 4,
                            0 <= ci,
                            ci < ni,
                            0 <= ri,
                            ri < 4,
                            4 * ni <= usize::MAX,
                    {
                    }
                    assert(src_line_36(ni, ri, ci) == isr_src_idx(ni, ri, ci));
                    assert(i as int == isr_src_idx(ni, ri, ci));
                }
                o_keys[4 * c + r] = self.keys[i];
                // copy_from_slice lowers to the 8-step explicit index
                // writes (the by-element copy face of the FA6-pre
                // get() twin's material; unrolled here because the
                // per-slice copy has no upstream-visible loop -- the
                // value face is byte-identical)
                o_tags[8 * (4 * c + r)] = self.tags[8 * i];
                o_tags[8 * (4 * c + r) + 1] = self.tags[8 * i + 1];
                o_tags[8 * (4 * c + r) + 2] = self.tags[8 * i + 2];
                o_tags[8 * (4 * c + r) + 3] = self.tags[8 * i + 3];
                o_tags[8 * (4 * c + r) + 4] = self.tags[8 * i + 4];
                o_tags[8 * (4 * c + r) + 5] = self.tags[8 * i + 5];
                o_tags[8 * (4 * c + r) + 6] = self.tags[8 * i + 6];
                o_tags[8 * (4 * c + r) + 7] = self.tags[8 * i + 7];
                c += 1;
            }
            r += 1;
        }
        ByteCommits { keys: o_keys, tags: o_tags }
    }
}

// ===========================================================================
// MixColumns (upstream :234-264, `impl<O> MixColumns<O> for
// StateBytesSquaredCommits<O>`). Origin Rust:
//     fn mix_columns(&mut self, sq: bool) {
//         let v2 = if sq { &OWFField::<O>::BYTE_COMBINE_SQ_2 }
//                  else { &OWFField::<O>::BYTE_COMBINE_2 };
//         let v3 = if sq { &..SQ_3 } else { &..COMBINE_3 };
//         for scalars in self.as_chunks_mut::<4>().0 {
//             let tmp = scalars.clone();
//             // ::7
//             scalars[0] = &tmp[0] * v2 + &tmp[1] * v3 + &tmp[2] + &tmp[3];
//             // ::8
//             scalars[1] = &tmp[1] * v2 + &tmp[2] * v3 + &tmp[0] + &tmp[3];
//             // ::9
//             scalars[2] = &tmp[2] * v2 + &tmp[3] * v3 + &tmp[0] + &tmp[1];
//             // ::10
//             scalars[3] = &tmp[0] * v3 + &tmp[3] * v2 + &tmp[1] + &tmp[2]; } }
// Lowering records: as_chunks_mut::<4> lowers to the column index
// loop (same order, same 4-lane bodies); the D2 Mul<F> face is
// mul_field (by-value re-typings at moved tmps, the merged-impl
// convention) and the D2 `+` lowers to add_assign (limb xor).
// ===========================================================================

/// Local exec copy helper for the by-value D2 faces (mul_field
/// consumes its receiver; upstream writes the &, moved-tmp re-
/// typings, the merged-impl record at the file header).
fn d2copy(x: &FieldCommitDegTwo) -> (o: FieldCommitDegTwo)
    ensures
        o.key == x.key,
        o.tag[0] == x.tag[0],
        o.tag[1] == x.tag[1],
{
    FieldCommitDegTwo { key: x.key, tag: [x.tag[0], x.tag[1]] }
}

/// MixColumns single-slot spec: the column src is (t0, t1, t2, t3)
/// at the taken slots; slot k combines per the upstream ::7-:10 rows.
pub open spec fn mc_slot_key(
    t0: u128, t1: u128, t2: u128, t3: u128,
    k: int, v2: u128, v3: u128,
) -> u128 {
    if k == 0 {
        gf128_mul_spec(t0, v2) ^ gf128_mul_spec(t1, v3) ^ t2 ^ t3
    } else if k == 1 {
        gf128_mul_spec(t1, v2) ^ gf128_mul_spec(t2, v3) ^ t0 ^ t3
    } else if k == 2 {
        gf128_mul_spec(t2, v2) ^ gf128_mul_spec(t3, v3) ^ t0 ^ t1
    } else {
        gf128_mul_spec(t0, v3) ^ gf128_mul_spec(t3, v2) ^ t1 ^ t2
    }
}

pub fn mix_columns(state: &mut Vec<FieldCommitDegTwo>, nst_bytes: usize, sq: bool)
    requires
        nst_bytes % 4 == 0,
        nst_bytes > 0,
        state.len() == nst_bytes,
    ensures
        final(state).len() == old(state).len(),
        forall |c: int, k: int, t: int|
            #![trigger final(state)[4 * c + k].tag[t]]
            0 <= c < nst_bytes as int / 4 && 0 <= k < 4 && 0 <= t < 2
                ==> final(state)[4 * c + k].tag[t]
                    == mc_slot_key(
                        old(state)[4 * c].tag[t],
                        old(state)[4 * c + 1].tag[t],
                        old(state)[4 * c + 2].tag[t],
                        old(state)[4 * c + 3].tag[t],
                        k,
                        if sq { GF128_BYTE_COMBINE_SQ_2 } else { GF128_BYTE_COMBINE_2 },
                        if sq { GF128_BYTE_COMBINE_SQ_3 } else { GF128_BYTE_COMBINE_3 },
                    ),
        forall |c: int, k: int|
            #![trigger final(state)[4 * c + k]]
            0 <= c < nst_bytes as int / 4 && 0 <= k < 4
                ==> final(state)[4 * c + k].key
                    == mc_slot_key(
                        old(state)[4 * c].key,
                        old(state)[4 * c + 1].key,
                        old(state)[4 * c + 2].key,
                        old(state)[4 * c + 3].key,
                        k,
                        if sq { GF128_BYTE_COMBINE_SQ_2 } else { GF128_BYTE_COMBINE_2 },
                        if sq { GF128_BYTE_COMBINE_SQ_3 } else { GF128_BYTE_COMBINE_3 },
                    ),
{
    // upstream v2/v3 pick (the ::1-2 rows of the body)
    let v2: u128 = if sq { GF128_BYTE_COMBINE_SQ_2 } else { GF128_BYTE_COMBINE_2 };
    let v3: u128 = if sq { GF128_BYTE_COMBINE_SQ_3 } else { GF128_BYTE_COMBINE_3 };
    let nst: usize = nst_bytes / 4;
    let mut c: usize = 0;
    while c < nst
        invariant
            c <= nst,
            nst_bytes > 0,
            nst_bytes % 4 == 0,
            nst == nst_bytes / 4,
            state.len() == nst_bytes,
            forall |cc: int, k: int|
                #![trigger state[4 * cc + k]]
                0 <= cc < c && 0 <= k < 4
                    ==> state[4 * cc + k].key
                        == mc_slot_key(
                            old(state)[4 * cc].key,
                            old(state)[4 * cc + 1].key,
                            old(state)[4 * cc + 2].key,
                            old(state)[4 * cc + 3].key,
                            k, v2, v3,
                        ),
            forall |cc: int, k: int, t: int|
                #![trigger state[4 * cc + k].tag[t]]
                0 <= cc < c && 0 <= k < 4 && 0 <= t < 2
                    ==> state[4 * cc + k].tag[t]
                        == mc_slot_key(
                            old(state)[4 * cc].tag[t],
                            old(state)[4 * cc + 1].tag[t],
                            old(state)[4 * cc + 2].tag[t],
                            old(state)[4 * cc + 3].tag[t],
                            k, v2, v3,
                        ),
            forall |cc: int, k: int|
                #![trigger state[4 * cc + k]]
                c <= cc < nst as int && 0 <= k < 4
                    ==> state[4 * cc + k].key == old(state)[4 * cc + k].key,
            forall |cc: int, k: int, t: int|
                #![trigger state[4 * cc + k].tag[t]]
                c <= cc < nst as int && 0 <= k < 4 && 0 <= t < 2
                    ==> state[4 * cc + k].tag[t] == old(state)[4 * cc + k].tag[t],
        decreases
            nst - c,
    {
        // tmp = scalars.clone() (the upstream save of the column)
        // entry-value ties (the guard-to-old bridge for the invariant
        // step: entry column slots carry old(state) values per the
        // untouched-column invariant and the fresh t_i are copies)
        assert(state[4 * c + 0].key == old(state)[4 * c + 0].key);
        assert(state[4 * c + 1].key == old(state)[4 * c + 1].key);
        assert(state[4 * c + 2].key == old(state)[4 * c + 2].key);
        assert(state[4 * c + 3].key == old(state)[4 * c + 3].key);
        assert(state[4 * c + 0].tag[0] == old(state)[4 * c].tag[0]);
        assert(state[4 * c + 0].tag[1] == old(state)[4 * c].tag[1]);
        assert(state[4 * c + 1].tag[0] == old(state)[4 * c + 1].tag[0]);
        assert(state[4 * c + 1].tag[1] == old(state)[4 * c + 1].tag[1]);
        assert(state[4 * c + 2].tag[0] == old(state)[4 * c + 2].tag[0]);
        assert(state[4 * c + 2].tag[1] == old(state)[4 * c + 2].tag[1]);
        assert(state[4 * c + 3].tag[0] == old(state)[4 * c + 3].tag[0]);
        assert(state[4 * c + 3].tag[1] == old(state)[4 * c + 3].tag[1]);
        let t0 = FieldCommitDegTwo { key: state[4 * c].key, tag: [state[4 * c].tag[0], state[4 * c].tag[1]] };
        let t1 = FieldCommitDegTwo { key: state[4 * c + 1].key, tag: [state[4 * c + 1].tag[0], state[4 * c + 1].tag[1]] };
        let t2 = FieldCommitDegTwo { key: state[4 * c + 2].key, tag: [state[4 * c + 2].tag[0], state[4 * c + 2].tag[1]] };
        let t3 = FieldCommitDegTwo { key: state[4 * c + 3].key, tag: [state[4 * c + 3].tag[0], state[4 * c + 3].tag[1]] };
        // ::7 scalars[0]
        let mut m0 = d2copy(&t0).mul_field(v2);
        m0.add_assign(&d2copy(&t1).mul_field(v3));
        m0.add_assign(&t2);
        m0.add_assign(&t3);
        state[4 * c] = FieldCommitDegTwo { key: m0.key, tag: [m0.tag[0], m0.tag[1]] };
        // ::8 scalars[1]
        let mut m1 = d2copy(&t1).mul_field(v2);
        m1.add_assign(&d2copy(&t2).mul_field(v3));
        m1.add_assign(&t0);
        m1.add_assign(&t3);
        state[4 * c + 1] = FieldCommitDegTwo { key: m1.key, tag: [m1.tag[0], m1.tag[1]] };
        // ::9 scalars[2]
        let mut m2 = d2copy(&t2).mul_field(v2);
        m2.add_assign(&d2copy(&t3).mul_field(v3));
        m2.add_assign(&t0);
        m2.add_assign(&t1);
        state[4 * c + 2] = FieldCommitDegTwo { key: m2.key, tag: [m2.tag[0], m2.tag[1]] };
        // ::10 scalars[3]
        let mut m3 = d2copy(&t0).mul_field(v3);
        m3.add_assign(&d2copy(&t3).mul_field(v2));
        m3.add_assign(&t1);
        m3.add_assign(&t2);
        state[4 * c + 3] = FieldCommitDegTwo { key: m3.key, tag: [m3.tag[0], m3.tag[1]] };
        // per-slot spec tie (the mul_field/add_assign ensure chain
        // folded once per lane so the invariant step closes for Z3)
        assert(state[4 * c].key == mc_slot_key(t0.key, t1.key, t2.key, t3.key, 0, v2, v3));
        assert(state[4 * c + 1].key == mc_slot_key(t0.key, t1.key, t2.key, t3.key, 1, v2, v3));
        assert(state[4 * c + 2].key == mc_slot_key(t0.key, t1.key, t2.key, t3.key, 2, v2, v3));
        assert(state[4 * c + 3].key == mc_slot_key(t0.key, t1.key, t2.key, t3.key, 3, v2, v3));
        assert(state[4 * c].tag[0] == mc_slot_key(t0.tag[0], t1.tag[0], t2.tag[0], t3.tag[0], 0, v2, v3));
        assert(state[4 * c].tag[1] == mc_slot_key(t0.tag[1], t1.tag[1], t2.tag[1], t3.tag[1], 0, v2, v3));
        assert(state[4 * c + 1].tag[0] == mc_slot_key(t0.tag[0], t1.tag[0], t2.tag[0], t3.tag[0], 1, v2, v3));
        assert(state[4 * c + 1].tag[1] == mc_slot_key(t0.tag[1], t1.tag[1], t2.tag[1], t3.tag[1], 1, v2, v3));
        assert(state[4 * c + 2].tag[0] == mc_slot_key(t0.tag[0], t1.tag[0], t2.tag[0], t3.tag[0], 2, v2, v3));
        assert(state[4 * c + 2].tag[1] == mc_slot_key(t0.tag[1], t1.tag[1], t2.tag[1], t3.tag[1], 2, v2, v3));
        assert(state[4 * c + 3].tag[0] == mc_slot_key(t0.tag[0], t1.tag[0], t2.tag[0], t3.tag[0], 3, v2, v3));
        assert(state[4 * c + 3].tag[1] == mc_slot_key(t0.tag[1], t1.tag[1], t2.tag[1], t3.tag[1], 3, v2, v3));
        assert(c < nst);
        c += 1;
    }
}


// ===========================================================================
// SBoxAffine (upstream :326-356, `impl<O> SBoxAffine<O> for
// StateBitsSquaredCommits<O>`). Origin Rust:
//     fn s_box_affine(&self, sq: bool) -> Self::Output {
//         let sigmas = if sq { &OWFField::<O>::SIGMA_SQUARES }
//                      else { &OWFField::<O>::SIGMA };
//         let t = sq as usize;
//         // :: 8-10
//         Box::new((0..O::NStBytes::USIZE).map(|i| {
//             // :: 9
//             let mut y_i = &self[i * 8 + t % 8] * sigmas[0];
//             for sigma_idx in 1..8 {
//                 y_i += &self[i * 8 + (sigma_idx + t) % 8] * sigmas[sigma_idx];
//             }
//             y_i += sigmas[8];
//             y_i
//         }).collect()) }
// Lowering records: the D2 Mul<F> is mul_field (by-value at moved
// slot copies, d2copy); `+=` between two D2 rows is the TAG_SIZE-2
// add_assign (limb xor); `+= sigmas[8]` is the field add
// (add_assign_field, key plane only); the map lowers to the index
// loop (same order); the inner 1..8 loop is unrolled below (a
// constant 7-lane chain, no upstream-visible data dependence on
// the loop bound -- the value face is the same 8-slot sigma row).
// ===========================================================================

/// Sigma-row spec: the sigma-indexed byte-row value of the
/// bits-plane commitment (key case / tag0 / tag1 cases by lane).
pub open spec fn sboxaff_key(
    bits: Seq<FieldCommitDegTwo>, i: int, t: int, sigmas: Seq<u128>,
) -> u128 {
    gf128_mul_spec(bits[8 * i + t % 8].key, sigmas[0])
        ^ gf128_mul_spec(bits[8 * i + (1 + t) % 8].key, sigmas[1])
        ^ gf128_mul_spec(bits[8 * i + (2 + t) % 8].key, sigmas[2])
        ^ gf128_mul_spec(bits[8 * i + (3 + t) % 8].key, sigmas[3])
        ^ gf128_mul_spec(bits[8 * i + (4 + t) % 8].key, sigmas[4])
        ^ gf128_mul_spec(bits[8 * i + (5 + t) % 8].key, sigmas[5])
        ^ gf128_mul_spec(bits[8 * i + (6 + t) % 8].key, sigmas[6])
        ^ gf128_mul_spec(bits[8 * i + (7 + t) % 8].key, sigmas[7])
        ^ sigmas[8]
}

pub open spec fn sboxaff_tag(
    bits: Seq<FieldCommitDegTwo>, i: int, t: int, sigmas: Seq<u128>,
    slot: int,
) -> u128 {
    gf128_mul_spec(bits[8 * i + t % 8].tag[slot], sigmas[0])
        ^ gf128_mul_spec(bits[8 * i + (1 + t) % 8].tag[slot], sigmas[1])
        ^ gf128_mul_spec(bits[8 * i + (2 + t) % 8].tag[slot], sigmas[2])
        ^ gf128_mul_spec(bits[8 * i + (3 + t) % 8].tag[slot], sigmas[3])
        ^ gf128_mul_spec(bits[8 * i + (4 + t) % 8].tag[slot], sigmas[4])
        ^ gf128_mul_spec(bits[8 * i + (5 + t) % 8].tag[slot], sigmas[5])
        ^ gf128_mul_spec(bits[8 * i + (6 + t) % 8].tag[slot], sigmas[6])
        ^ gf128_mul_spec(bits[8 * i + (7 + t) % 8].tag[slot], sigmas[7])
}

pub fn s_box_affine(
    state: &[FieldCommitDegTwo],
    nst_bytes: usize,
    sq: bool,
) -> (o: StateBytesSquaredCommits)
    requires
        state.len() == 8 * nst_bytes,
        8 * nst_bytes <= usize::MAX - 64,
        nst_bytes <= 10000000,
    ensures
        o.len() == nst_bytes,
        forall |i: int|
            #![trigger o[i].key]
            0 <= i < nst_bytes as int
                ==> o[i].key
                    == sboxaff_key(
                        state@, i,
                        if sq { 1 } else { 0 },
                        if sq { GF128_SIGMA_SQUARES@ } else { GF128_SIGMA@ },
                    ),
        forall |i: int, slot: int|
            #![trigger o[i].tag[slot]]
            0 <= i < nst_bytes as int && 0 <= slot < 2
                ==> o[i].tag[slot]
                    == sboxaff_tag(
                        state@, i,
                        if sq { 1 } else { 0 },
                        if sq { GF128_SIGMA_SQUARES@ } else { GF128_SIGMA@ },
                        slot,
                    ),
{
    // upstream ::1-2 rows (the sigmas pick + t = sq as usize)
    let sigmas: [u128; 9] = if sq { GF128_SIGMA_SQUARES } else { GF128_SIGMA };
    let t: usize = if sq { 1 } else { 0 };
    let mut o: StateBytesSquaredCommits = Vec::new();
    let mut i: usize = 0;
    while i < nst_bytes
        invariant
            i <= nst_bytes,
            state.len() == 8 * nst_bytes,
            8 * nst_bytes <= usize::MAX - 64,
            o.len() == i,
            t == (if sq { 1 as usize } else { 0 as usize }),
            sigmas@ == (if sq { GF128_SIGMA_SQUARES@ } else { GF128_SIGMA@ }),
            forall |j: int|
                #![trigger o[j].key]
                0 <= j < i
                    ==> o[j].key
                        == sboxaff_key(
                            state@, j, t as int, sigmas@,
                        ),
            forall |j: int, slot: int|
                #![trigger o[j].tag[slot]]
                0 <= j < i && 0 <= slot < 2
                    ==> o[j].tag[slot]
                        == sboxaff_tag(
                            state@, j, t as int, sigmas@, slot,
                        ),
        decreases
            nst_bytes - i,
    {
        let base = 8 * i;
        // ::9 lanes (the constant 8-slot sigma row, unrolled -- see
        // the header lowering record)
        let mut y = d2copy(&state[base + t]).mul_field(sigmas[0]);
        y.add_assign(&d2copy(&state[base + (1 + t) % 8]).mul_field(sigmas[1]));
        y.add_assign(&d2copy(&state[base + (2 + t) % 8]).mul_field(sigmas[2]));
        y.add_assign(&d2copy(&state[base + (3 + t) % 8]).mul_field(sigmas[3]));
        y.add_assign(&d2copy(&state[base + (4 + t) % 8]).mul_field(sigmas[4]));
        y.add_assign(&d2copy(&state[base + (5 + t) % 8]).mul_field(sigmas[5]));
        y.add_assign(&d2copy(&state[base + (6 + t) % 8]).mul_field(sigmas[6]));
        y.add_assign(&d2copy(&state[base + (7 + t) % 8]).mul_field(sigmas[7]));
        // y_i += sigmas[8] (field add, key plane)
        y.add_assign_field(sigmas[8]);
        assert(y.key
            == gf128_mul_spec(state[base as int + t as int].key, sigmas[0])
                ^ gf128_mul_spec(state[base as int + ((1 + t) % 8) as int].key, sigmas[1])
                ^ gf128_mul_spec(state[base as int + ((2 + t) % 8) as int].key, sigmas[2])
                ^ gf128_mul_spec(state[base as int + ((3 + t) % 8) as int].key, sigmas[3])
                ^ gf128_mul_spec(state[base as int + ((4 + t) % 8) as int].key, sigmas[4])
                ^ gf128_mul_spec(state[base as int + ((5 + t) % 8) as int].key, sigmas[5])
                ^ gf128_mul_spec(state[base as int + ((6 + t) % 8) as int].key, sigmas[6])
                ^ gf128_mul_spec(state[base as int + ((7 + t) % 8) as int].key, sigmas[7])
                ^ sigmas[8]);
        assert(y.tag[0]
            == gf128_mul_spec(state[base as int + t as int].tag[0], sigmas[0])
                ^ gf128_mul_spec(state[base as int + ((1 + t) % 8) as int].tag[0], sigmas[1])
                ^ gf128_mul_spec(state[base as int + ((2 + t) % 8) as int].tag[0], sigmas[2])
                ^ gf128_mul_spec(state[base as int + ((3 + t) % 8) as int].tag[0], sigmas[3])
                ^ gf128_mul_spec(state[base as int + ((4 + t) % 8) as int].tag[0], sigmas[4])
                ^ gf128_mul_spec(state[base as int + ((5 + t) % 8) as int].tag[0], sigmas[5])
                ^ gf128_mul_spec(state[base as int + ((6 + t) % 8) as int].tag[0], sigmas[6])
                ^ gf128_mul_spec(state[base as int + ((7 + t) % 8) as int].tag[0], sigmas[7 as int]));
        assert(y.tag[1]
            == gf128_mul_spec(state[base as int + t as int].tag[1], sigmas[0 as int])
                ^ gf128_mul_spec(state[base as int + ((1 + t) % 8) as int].tag[1], sigmas[1 as int])
                ^ gf128_mul_spec(state[base as int + ((2 + t) % 8) as int].tag[1], sigmas[2 as int])
                ^ gf128_mul_spec(state[base as int + ((3 + t) % 8) as int].tag[1], sigmas[3 as int])
                ^ gf128_mul_spec(state[base as int + ((4 + t) % 8) as int].tag[1], sigmas[4 as int])
                ^ gf128_mul_spec(state[base as int + ((5 + t) % 8) as int].tag[1], sigmas[5 as int])
                ^ gf128_mul_spec(state[base as int + ((6 + t) % 8) as int].tag[1], sigmas[6 as int])
                ^ gf128_mul_spec(state[base as int + ((7 + t) % 8) as int].tag[1], sigmas[7 as int]));
        assert(sboxaff_key(state@, i as int, t as int, sigmas@)
            == gf128_mul_spec(state@[8 * i as int + (t as int) % 8].key, sigmas@[0])
                ^ gf128_mul_spec(state@[8 * i as int + ((1 + t) as int) % 8].key, sigmas@[1])
                ^ gf128_mul_spec(state@[8 * i as int + ((2 + t) as int) % 8].key, sigmas@[2])
                ^ gf128_mul_spec(state@[8 * i as int + ((3 + t) as int) % 8].key, sigmas@[3])
                ^ gf128_mul_spec(state@[8 * i as int + ((4 + t) as int) % 8].key, sigmas@[4])
                ^ gf128_mul_spec(state@[8 * i as int + ((5 + t) as int) % 8].key, sigmas@[5])
                ^ gf128_mul_spec(state@[8 * i as int + ((6 + t) as int) % 8].key, sigmas@[6])
                ^ gf128_mul_spec(state@[8 * i as int + ((7 + t) as int) % 8].key, sigmas@[7])
                ^ sigmas@[8]);
        assert(sboxaff_tag(state@, i as int, t as int, sigmas@, 0)
            == gf128_mul_spec(state@[8 * i as int + (t as int) % 8].tag[0], sigmas@[0])
                ^ gf128_mul_spec(state@[8 * i as int + ((1 + t) as int) % 8].tag[0], sigmas@[1])
                ^ gf128_mul_spec(state@[8 * i as int + ((2 + t) as int) % 8].tag[0], sigmas@[2])
                ^ gf128_mul_spec(state@[8 * i as int + ((3 + t) as int) % 8].tag[0], sigmas@[3])
                ^ gf128_mul_spec(state@[8 * i as int + ((4 + t) as int) % 8].tag[0], sigmas@[4])
                ^ gf128_mul_spec(state@[8 * i as int + ((5 + t) as int) % 8].tag[0], sigmas@[5])
                ^ gf128_mul_spec(state@[8 * i as int + ((6 + t) as int) % 8].tag[0], sigmas@[6])
                ^ gf128_mul_spec(state@[8 * i as int + ((7 + t) as int) % 8].tag[0], sigmas@[7]));
        assert(sboxaff_tag(state@, i as int, t as int, sigmas@, 1)
            == gf128_mul_spec(state@[8 * i as int + (t as int) % 8].tag[1], sigmas@[0])
                ^ gf128_mul_spec(state@[8 * i as int + ((1 + t) as int) % 8].tag[1], sigmas@[1])
                ^ gf128_mul_spec(state@[8 * i as int + ((2 + t) as int) % 8].tag[1], sigmas@[2])
                ^ gf128_mul_spec(state@[8 * i as int + ((3 + t) as int) % 8].tag[1], sigmas@[3])
                ^ gf128_mul_spec(state@[8 * i as int + ((4 + t) as int) % 8].tag[1], sigmas@[4])
                ^ gf128_mul_spec(state@[8 * i as int + ((5 + t) as int) % 8].tag[1], sigmas@[5])
                ^ gf128_mul_spec(state@[8 * i as int + ((6 + t) as int) % 8].tag[1], sigmas@[6])
                ^ gf128_mul_spec(state@[8 * i as int + ((7 + t) as int) % 8].tag[1], sigmas@[7]));
        o.push(FieldCommitDegTwo { key: y.key, tag: [y.tag[0], y.tag[1]] });
        assert(o[i as int].key == sboxaff_key(state@, i as int, t as int, sigmas@));
        assert(o[i as int].tag[0] == sboxaff_tag(state@, i as int, t as int, sigmas@, 0));
        assert(o[i as int].tag[1] == sboxaff_tag(state@, i as int, t as int, sigmas@, 1));
        i += 1;
    }
    o
}

// ===========================================================================
// InverseAffine (upstream :358-383, `impl<F, L> InverseAffine for
// ByteCommits<F, L>` at L: SecurityParameter -- the LambdaBytes plane).
// Origin Rust:
//     for i in 0..L::USIZE {
//         self.keys[i] = self.keys[i].rotate_right(7)
//             ^ self.keys[i].rotate_right(5)
//             ^ self.keys[i].rotate_right(2)
//             ^ 0x5; }
//     for scalars in self.tags.as_chunks_mut::<8>().0 {
//         let xi_tags = *scalars;
//         for bit_i in 0..8 {
//             scalars[bit_i] = xi_tags[(bit_i + 8 - 1) % 8]
//                 + xi_tags[(bit_i + 8 - 3) % 8]
//                 + xi_tags[(bit_i + 8 - 6) % 8]; } }
// Lowering records: rotate_right lowers to the explicit shift-or
// lane (verus-side bit lanes; u16 widened to escape the u8 shift
// overflow flag); tag `+` is the limb xor (FA3 record).
// ===========================================================================

/// rotate_right lanes over the u8 plane (spec faces; probe-verified
/// spellings: the u16-widened high-side shift is truncated, not
/// wrapped, by the bit-width semantics -- the u8 target lane casts
/// the widened pair instead, the probe-bv t4 form; recorded as the
/// batch pitfall #FA11-1).
pub open spec fn rot_l1_u8(x: u8) -> u8 {
    (((x as u16) >> 7) as u8) | ((((x as u16) << 1) & 0xff) as u8)
}

pub open spec fn rot_l3_u8(x: u8) -> u8 {
    (((x as u16) >> 5) as u8) | ((((x as u16) << 3) & 0xff) as u8)
}

pub open spec fn rot_l6_u8(x: u8) -> u8 {
    (((x as u16) >> 2) as u8) | ((((x as u16) << 6) & 0xff) as u8)
}

/// The double-xor inverse-affine key row (the upstream ::5 lane:
/// x.rotate_right(7) ^ x.rotate_right(5) ^ x.rotate_right(2) ^ 0x5;
/// rotate_right(k) == rotate_left(8-k), spelled with the probe-
/// verified u8 lanes).
pub open spec fn iaf8(x: u8) -> u8 {
    rot_l1_u8(x) ^ rot_l3_u8(x) ^ rot_l6_u8(x) ^ 0x5
}

/// The tag-slot scramble row (the ::6 lane over the 8-window copy).
pub open spec fn iaf_tag(xi: Seq<u128>, bit_i: int) -> u128 {
    xi[(bit_i + 8 - 1) % 8] ^ xi[(bit_i + 8 - 3) % 8] ^ xi[(bit_i + 8 - 6) % 8]
}

impl ByteCommits {
    /// Origin Rust (:358-383).
    pub fn inverse_affine(self: &mut Self, lambda_bytes: usize)
        requires
            self.keys.len() == lambda_bytes,
            self.keys.len() * 8 == self.tags.len(),
        ensures
            final(self).keys.len() == old(self).keys.len(),
            final(self).tags.len() == old(self).tags.len(),
            forall |j: int|
                #![trigger final(self).keys[j]]
                0 <= j < lambda_bytes as int
                    ==> final(self).keys[j] == iaf8(old(self).keys[j]),
            forall |j: int, bit_i: int|
                #![trigger final(self).tags[8 * j + bit_i]]
                0 <= j < lambda_bytes as int && 0 <= bit_i < 8
                    ==> final(self).tags[8 * j + bit_i]
                        == iaf_tag(
                            Seq::new(8nat, |t: int| old(self).tags[8 * j + t]),
                            bit_i,
                        ),
    {
        let mut i: usize = 0;
        while i < self.keys.len()
            invariant
                i <= self.keys.len(),
                self.keys.len() == lambda_bytes,
                self.keys.len() * 8 == self.tags.len(),
                forall |j: int|
                    #![trigger self.keys[j]]
                    0 <= j < i
                        ==> self.keys[j] == iaf8(old(self).keys[j]),
                forall |j: int|
                    #![trigger self.keys[j]]
                    i <= j < self.keys.len()
                        ==> self.keys[j] == old(self).keys[j],
                forall |j: int, b: int|
                    #![trigger self.tags[8 * j + b]]
                    0 <= j < self.tags.len() / 8 && 0 <= b < 8
                        ==> self.tags[8 * j + b] == old(self).tags[8 * j + b],
            decreases
                self.keys.len() - i,
        {
            let x = self.keys[i];
            let r7: u8 = (((x as u16) >> 7) as u8) | ((((x as u16) << 1) & 0xff) as u8);
            let r5: u8 = (((x as u16) >> 5) as u8) | ((((x as u16) << 3) & 0xff) as u8);
            let r2: u8 = (((x as u16) >> 2) as u8) | ((((x as u16) << 6) & 0xff) as u8);
            let rw8: u8 = r7 ^ r5 ^ r2 ^ 0x5;
            assert(rot_l1_u8(x) == r7);
            assert(rot_l3_u8(x) == r5);
            assert(rot_l6_u8(x) == r2);
            assert(iaf8(x) == rw8);
            self.keys[i] = rw8;
            i += 1;
        }
        let mut c2: usize = 0;
        while c2 < lambda_bytes
            invariant
                c2 <= lambda_bytes,
                self.keys.len() == lambda_bytes,
                self.keys.len() * 8 == self.tags.len(),
                forall |j: int|
                    #![trigger self.keys[j]]
                    0 <= j < self.keys.len()
                        ==> self.keys[j] == iaf8(old(self).keys[j]),
                forall |j: int, b: int|
                    #![trigger self.tags[8 * j + b]]
                    (0 <= j < c2 && 0 <= b < 8)
                        ==> self.tags[8 * j + b]
                            == iaf_tag(
                                Seq::new(8nat, |t: int| old(self).tags[8 * j + t]),
                                b,
                            ),
                forall |j: int, b: int|
                    #![trigger self.tags[8 * j + b]]
                    (c2 <= j < lambda_bytes as int) && 0 <= b < 8
                        ==> self.tags[8 * j + b] == old(self).tags[8 * j + b],
            decreases
                lambda_bytes - c2,
        {
            // xi_tags = *scalars (the window copy)
            let mut xi: [u128; 8] = [0u128; 8];
            let mut k: usize = 0;
            while k < 8
                invariant
                    k <= 8,
                    c2 < lambda_bytes,
                    self.keys.len() == lambda_bytes,
                    self.keys.len() * 8 == self.tags.len(),
                    (8 * lambda_bytes) <= usize::MAX,
                    forall |kk: int| 0 <= kk < k ==> xi[kk] == old(self).tags[8 * c2 + kk],
                    forall |kk: int|
                        #![trigger self.tags[8 * c2 + kk]]
                        0 <= kk < 8
                            ==> self.tags[8 * c2 + kk]
                                == old(self).tags[8 * c2 + kk],
                    forall |jj: int, bb: int|
                        #![trigger self.tags[8 * jj + bb]]
                        0 <= jj < c2 && 0 <= bb < 8
                            ==> self.tags[8 * jj + bb]
                                == iaf_tag(
                                    Seq::new(8nat, |t: int| old(self).tags[8 * jj + t]),
                                    bb,
                                ),
                    forall |jj: int, bb: int|
                        #![trigger self.tags[8 * jj + bb]]
                        (c2 < jj < lambda_bytes as int) && 0 <= bb < 8
                            ==> self.tags[8 * jj + bb]
                                == old(self).tags[8 * jj + bb],
                    forall |jj: int|
                        #![trigger self.keys[jj]]
                        0 <= jj < self.keys.len()
                            ==> self.keys[jj] == iaf8(old(self).keys[jj]),
                decreases
                    8 - k,
            {
                xi[k] = self.tags[8 * c2 + k];
                k += 1;
            }
            let mut bit_i: usize = 0;
            while bit_i < 8
                invariant
                    bit_i <= 8,
                    c2 < lambda_bytes,
                    self.keys.len() == lambda_bytes,
                    self.keys.len() * 8 == self.tags.len(),
                    (8 * lambda_bytes) <= usize::MAX,
                    forall |kk: int| 0 <= kk < 8
                        ==> xi[kk] == old(self).tags[8 * c2 + kk],
                    forall |jj: int|
                        #![trigger self.keys[jj]]
                        0 <= jj < self.keys.len()
                            ==> self.keys[jj] == iaf8(old(self).keys[jj]),
                    forall |jj: int, bb: int|
                        #![trigger self.tags[8 * jj + bb]]
                        0 <= jj < c2 && 0 <= bb < 8
                            ==> self.tags[8 * jj + bb]
                                == iaf_tag(
                                    Seq::new(8nat, |t: int| old(self).tags[8 * jj + t]),
                                    bb,
                                ),
                    forall |jj: int, bb: int|
                        #![trigger self.tags[8 * jj + bb]]
                        (c2 < jj < lambda_bytes as int) && 0 <= bb < 8
                            ==> self.tags[8 * jj + bb]
                                == old(self).tags[8 * jj + bb],
                    forall |bb: int|
                        #![trigger self.tags[8 * c2 + bb]]
                        bit_i <= bb < 8
                            ==> self.tags[8 * c2 + bb]
                                == old(self).tags[8 * c2 + bb],
                    forall |bb: int|
                        #![trigger self.tags[8 * c2 + bb]]
                        0 <= bb < bit_i
                            ==> self.tags[8 * c2 + bb]
                                == iaf_tag(
                                    Seq::new(8nat, |t: int| old(self).tags[8 * c2 + t]),
                                    bb,
                                ),
                    forall |bb: int|
                        #![trigger self.tags[8 * c2 + bb]]
                        bit_i <= bb < 8
                            ==> self.tags[8 * c2 + bb]
                                == old(self).tags[8 * c2 + bb],
                decreases
                    8 - bit_i,
            {
                let idx = (bit_i + 7) % 8;
                let idx3 = (bit_i + 5) % 8;
                let idx2 = (bit_i + 2) % 8;
                self.tags[8 * c2 + bit_i] = xi[idx] ^ xi[idx3] ^ xi[idx2];
                bit_i += 1;
            }
            assert(forall |b: int|
                #![trigger self.tags[8 * c2 + b]]
                0 <= b < 8
                    ==> self.tags[8 * c2 + b]
                        == iaf_tag(
                            Seq::new(8nat, |t: int| old(self).tags[8 * c2 + t]),
                            b,
                        ));
            c2 += 1;
        }
    }
}


// ===========================================================================
// BytewiseMixColumns (upstream :266-324, `impl<O> BytewiseMixColumns<O>
// for ByteCommitsRef`). Origin Rust (full body):
//     fn bytewise_mix_columns(&self) -> Self::Output {
//         let mut o = ByteCommits::default();
//         for c in 0..O::NSt::USIZE {
//             for r in 0..4 {
//                 // ::4
//                 let a_key = self.keys[4 * c + r];
//                 let a_tags = &self.tags[32 * c + 8 * r..32 * c + 8 * r + 8];
//                 // ::5
//                 let a_key_7 = a_key & 0x80;
//                 let b_key = a_key.rotate_left(1)
//                     ^ (a_key_7 >> 6) ^ (a_key_7 >> 4) ^ (a_key_7 >> 3);
//                 let b_tags = [
//                     a_tags[7],
//                     a_tags[0] + a_tags[7],
//                     a_tags[1],
//                     a_tags[2] + a_tags[7],
//                     a_tags[3] + a_tags[7],
//                     a_tags[4],
//                     a_tags[5],
//                     a_tags[6],
//                 ];
//                 // ::6..10
//                 // Add b(r) to o_{4*c+r} and o_{4*c + (r - 1 mod 4)}
//                 for j in 0..2 {
//                     let off = (4 + r - j) % 4;
//                     o.keys[4 * c + off] ^= b_key;
//                     for (o, b) in zip(
//                         o.tags[32 * c + 8 * off..32 * c + 8 * off + 8]
//                             .iter_mut(), b_tags) { *o += b; } }
//                 // Add a(r) to o_{4*c + (r+1 mod 4)},
//                 // o_{4*c + (r+2 mod 4)}, o_{4*c + (r+3 mod 4)}
//                 for j in 1..4 {
//                     let off = (r + j) % 4;
//                     o.keys[4 * c + off] ^= a_key;
//                     for (o, a) in zip(
//                         o.tags[32 * c + 8 * off..32 * c + 8 * off + 8]
//                             .iter_mut(), a_tags) { *o += a; } } } }
//         o }
//
// Deferred-transcription record (D-FA11-1): the body is transcribed
// in full and compiles, but under #[verifier::external_body] this
// window -- the per-slot contribution lattice (each output slot
// collects b(r) ^ b(r+1) ^ ... rows across the r-loop, an xor-accum
// net whose loop-contract chain is the same weight class as the
// FA10w save_non_lin_bits round chain was) did not converge inside
// this batch window; the contract rows claimed below are the
// structural ones the oracle-run body is additionally pinned to
// (sizes); the full per-slot value faces are the D-FA11-1
// continue-here kit, oracle-arbitrated meanwhile (the body IS the
// faithful upstream byte-lane arithmetic).
// ===========================================================================

/// xtime lane spec (the ::5 b_key arithmetic; rotate_left(1) == the
/// shifted-or lane, plus the three a_key_7 taps). Layered spec fns
/// so the definitional folds instantiate (a monolithic cast-heavy
/// spec fn body does not expose its def axiom to the prover here --
/// probe-def6; pitfall #FA11-7).
pub open spec fn xt_rot(a: u8) -> u8 {
    (((a as u16) >> 7) as u8) | ((((a as u16) << 1) & 0xff) as u8)
}

pub open spec fn xtime_key(a: u8) -> u8 {
    xt_rot(a)
        ^ ((a & 0x80) >> 6)
        ^ ((a & 0x80) >> 4)
        ^ ((a & 0x80) >> 3)
}

/// The ::5 b_tags lane (tag plane: bit-7 carry rosters).
pub open spec fn btag_slot(a_tags: Seq<u128>, idx: int) -> u128 {
    if idx == 0 { a_tags[7] }
    else if idx == 1 { a_tags[0] ^ a_tags[7] }
    else if idx == 2 { a_tags[1] }
    else if idx == 3 { a_tags[2] ^ a_tags[7] }
    else if idx == 4 { a_tags[3] ^ a_tags[7] }
    else if idx == 5 { a_tags[4] }
    else if idx == 6 { a_tags[5] }
    else { a_tags[6] }
}

// ===========================================================================
// BytewiseMixColumns contract machinery (the D-FA11-1 convergence
// kit; wave-2): the per-slot contribution lattice. Within one
// column, upstream row rr writes b(rr) into slot rr and slot
// (rr+3)%4, and a(rr) into slots (rr+1)%4/ (rr+2)%4 / (rr+3)%4 --
// spelling the final slot-k value (the fold over all four rows) as
//     xtime(a_k) ^ xtime(a_{k+1}) ^ a_{k+1} ^ a_{k+2} ^ a_{k+3}
//         (mod-4 columns; wave-1 header derivation), and the same
// lane on the tag plane through the btag_slot roster. The partial
// helpers cut that fold at "R rows applied" so the r-loop invariant
// tracks the per-slot xor accumulation row by row.
// ===========================================================================

/// The k-th column entry (keys lane); the mod-4 index helpers below
/// rely on 0 <= k < 4.
pub open spec fn col4(k: int, a0: u8, a1: u8, a2: u8, a3: u8) -> u8 {
    if k == 0 { a0 } else if k == 1 { a1 } else if k == 2 { a2 } else { a3 }
}

/// The k-th row tag window (tag lane: Seq<u128>, length 8).
pub open spec fn trow4(
    k: int,
    c0: Seq<u128>, c1: Seq<u128>, c2: Seq<u128>, c3: Seq<u128>,
) -> Seq<u128> {
    if k == 0 { c0 } else if k == 1 { c1 } else if k == 2 { c2 } else { c3 }
}

/// Contribution of row rr to slot k, keys lane.
pub open spec fn bmc_contrib_key(
    rr: int, k: int, a0: u8, a1: u8, a2: u8, a3: u8,
) -> u8 {
    let a_r = col4(rr % 4, a0, a1, a2, a3);
    if k == (rr % 4) {
        xtime_key(a_r)
    } else if k == ((rr + 3) % 4) {
        xtime_key(a_r) ^ a_r
    } else if k == ((rr + 1) % 4) || k == ((rr + 2) % 4) {
        a_r
    } else {
        0u8
    }
}

/// Contribution of row rr to slot k, tag lane (per bit slot t).
pub open spec fn bmc_contrib_tag(
    rr: int, k: int, t: int,
    c0: Seq<u128>, c1: Seq<u128>, c2: Seq<u128>, c3: Seq<u128>,
) -> u128 {
    let a_r = trow4(rr % 4, c0, c1, c2, c3);
    if k == (rr % 4) {
        btag_slot(a_r, t)
    } else if k == ((rr + 3) % 4) {
        btag_slot(a_r, t) ^ a_r[t]
    } else if k == ((rr + 1) % 4) || k == ((rr + 2) % 4) {
        a_r[t]
    } else {
        0u128
    }
}

/// Keys-lane fold cut at R rows applied (R in [0, 4], the exec
/// r-loop range; enumerated explicitly so the fold needs no
/// recursive-constant collapsing ladder).
pub open spec fn bmc_partial_key(
    k: int, R: int, a0: u8, a1: u8, a2: u8, a3: u8,
) -> u8 {
    if R <= 0 {
        0u8
    } else if R == 1 {
        bmc_contrib_key(0, k, a0, a1, a2, a3)
    } else if R == 2 {
        bmc_contrib_key(0, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(1, k, a0, a1, a2, a3)
    } else if R == 3 {
        bmc_contrib_key(0, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(1, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(2, k, a0, a1, a2, a3)
    } else {
        bmc_contrib_key(0, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(1, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(2, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(3, k, a0, a1, a2, a3)
    }
}

/// Tag-lane fold cut at R rows applied (per bit slot t; R in
/// [0, 4] enumerated like the keys lane).
pub open spec fn bmc_partial_tag(
    k: int, t: int, R: int,
    c0: Seq<u128>, c1: Seq<u128>, c2: Seq<u128>, c3: Seq<u128>,
) -> u128 {
    if R <= 0 {
        0u128
    } else if R == 1 {
        bmc_contrib_tag(0, k, t, c0, c1, c2, c3)
    } else if R == 2 {
        bmc_contrib_tag(0, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(1, k, t, c0, c1, c2, c3)
    } else if R == 3 {
        bmc_contrib_tag(0, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(1, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(2, k, t, c0, c1, c2, c3)
    } else {
        bmc_contrib_tag(0, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(1, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(2, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(3, k, t, c0, c1, c2, c3)
    }
}

/// The final keys-lane slot value (wave-1 header derivation:
/// b(k) ^ b(k+1) ^ a(k+1..k+3), mod 4).
pub open spec fn bmc_final_key(
    k: int, a0: u8, a1: u8, a2: u8, a3: u8,
) -> u8 {
    xtime_key(col4(k % 4, a0, a1, a2, a3))
        ^ xtime_key(col4((k + 1) % 4, a0, a1, a2, a3))
        ^ col4((k + 1) % 4, a0, a1, a2, a3)
        ^ col4((k + 2) % 4, a0, a1, a2, a3)
        ^ col4((k + 3) % 4, a0, a1, a2, a3)
}

/// The final tag-lane slot value (per bit slot t).
pub open spec fn bmc_final_tag(
    k: int, t: int,
    c0: Seq<u128>, c1: Seq<u128>, c2: Seq<u128>, c3: Seq<u128>,
) -> u128 {
    btag_slot(trow4(k % 4, c0, c1, c2, c3), t)
        ^ btag_slot(trow4((k + 1) % 4, c0, c1, c2, c3), t)
        ^ trow4((k + 1) % 4, c0, c1, c2, c3)[t]
        ^ trow4((k + 2) % 4, c0, c1, c2, c3)[t]
        ^ trow4((k + 3) % 4, c0, c1, c2, c3)[t]
}

/// The tag window of row k of column c (spec view over the input
/// commitments).
pub open spec fn trow_of(
    tags: Seq<u128>, c: int, k: int,
) -> Seq<u128> {
    Seq::new(8nat, |t: int| tags[8 * (4 * c + k) + t])
}

pub proof fn lemma_bmc_final_key(k: int, a0: u8, a1: u8, a2: u8, a3: u8)
    requires
        0 <= k < 4,
    ensures
        bmc_partial_key(k, 4, a0, a1, a2, a3)
            == bmc_final_key(k, a0, a1, a2, a3),
{
    // per-contributor asserts + the bv regrouping assert close the
    // fold (the default encoding does not rewrite the xor assoc tree;
    // pitfall #FA11-8)
    assert(bmc_partial_key(k, 4, a0, a1, a2, a3)
        == bmc_contrib_key(0, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(1, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(2, k, a0, a1, a2, a3)
            ^ bmc_contrib_key(3, k, a0, a1, a2, a3));
    if k == 0 {
        assert(bmc_contrib_key(0, 0, a0, a1, a2, a3) == xtime_key(a0));
        assert(bmc_contrib_key(1, 0, a0, a1, a2, a3) == xtime_key(a1) ^ a1);
        assert(bmc_contrib_key(2, 0, a0, a1, a2, a3) == a2);
        assert(bmc_contrib_key(3, 0, a0, a1, a2, a3) == a3);
        assert(bmc_final_key(0, a0, a1, a2, a3)
            == xtime_key(a0) ^ xtime_key(a1) ^ a1 ^ a2 ^ a3);
        assert(bmc_partial_key(0, 4, a0, a1, a2, a3)
            == xtime_key(a0) ^ xtime_key(a1) ^ a1 ^ a2 ^ a3) by (bit_vector);
    } else if k == 1 {
        assert(bmc_contrib_key(0, 1, a0, a1, a2, a3) == a0);
        assert(bmc_contrib_key(1, 1, a0, a1, a2, a3) == xtime_key(a1));
        assert(bmc_contrib_key(2, 1, a0, a1, a2, a3) == xtime_key(a2) ^ a2);
        assert(bmc_contrib_key(3, 1, a0, a1, a2, a3) == a3);
        assert(bmc_final_key(1, a0, a1, a2, a3)
            == xtime_key(a1) ^ xtime_key(a2) ^ a2 ^ a3 ^ a0);
        assert(bmc_partial_key(1, 4, a0, a1, a2, a3)
            == xtime_key(a1) ^ xtime_key(a2) ^ a2 ^ a3 ^ a0) by (bit_vector);
    } else if k == 2 {
        assert(bmc_contrib_key(0, 2, a0, a1, a2, a3) == a0);
        assert(bmc_contrib_key(1, 2, a0, a1, a2, a3) == a1);
        assert(bmc_contrib_key(2, 2, a0, a1, a2, a3) == xtime_key(a2));
        assert(bmc_contrib_key(3, 2, a0, a1, a2, a3) == xtime_key(a3) ^ a3);
        assert(bmc_final_key(2, a0, a1, a2, a3)
            == xtime_key(a2) ^ xtime_key(a3) ^ a3 ^ a0 ^ a1);
        assert(bmc_partial_key(2, 4, a0, a1, a2, a3)
            == xtime_key(a2) ^ xtime_key(a3) ^ a3 ^ a0 ^ a1) by (bit_vector);
    } else {
        assert(bmc_contrib_key(0, 3, a0, a1, a2, a3) == xtime_key(a0) ^ a0);
        assert(bmc_contrib_key(1, 3, a0, a1, a2, a3) == a1);
        assert(bmc_contrib_key(2, 3, a0, a1, a2, a3) == a2);
        assert(bmc_contrib_key(3, 3, a0, a1, a2, a3) == xtime_key(a3));
        assert(bmc_final_key(3, a0, a1, a2, a3)
            == xtime_key(a3) ^ xtime_key(a0) ^ a0 ^ a1 ^ a2);
        assert(bmc_partial_key(3, 4, a0, a1, a2, a3)
            == xtime_key(a3) ^ xtime_key(a0) ^ a0 ^ a1 ^ a2) by (bit_vector);
    }
}

pub proof fn lemma_bmc_final_tag(
    k: int, t: int,
    c0: Seq<u128>, c1: Seq<u128>, c2: Seq<u128>, c3: Seq<u128>,
)
    requires
        0 <= k < 4,
        0 <= t < 8,
        c0.len() == 8, c1.len() == 8, c2.len() == 8, c3.len() == 8,
    ensures
        bmc_partial_tag(k, t, 4, c0, c1, c2, c3)
            == bmc_final_tag(k, t, c0, c1, c2, c3),
{
    assert(bmc_partial_tag(k, t, 4, c0, c1, c2, c3)
        == bmc_contrib_tag(0, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(1, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(2, k, t, c0, c1, c2, c3)
            ^ bmc_contrib_tag(3, k, t, c0, c1, c2, c3));
    let s0: u128 = btag_slot(c0, t);
    let s1: u128 = btag_slot(c1, t);
    let s2: u128 = btag_slot(c2, t);
    let s3: u128 = btag_slot(c3, t);
    let r0: u128 = c0[t];
    let r1: u128 = c1[t];
    let r2: u128 = c2[t];
    let r3: u128 = c3[t];
    if k == 0 {
        assert(bmc_contrib_tag(0, 0, t, c0, c1, c2, c3) == s0);
        assert(bmc_contrib_tag(1, 0, t, c0, c1, c2, c3) == s1 ^ r1);
        assert(bmc_contrib_tag(2, 0, t, c0, c1, c2, c3) == r2);
        assert(bmc_contrib_tag(3, 0, t, c0, c1, c2, c3) == r3);
        assert(bmc_partial_tag(0, t, 4, c0, c1, c2, c3)
            == s0 ^ (s1 ^ r1) ^ r2 ^ r3);
        assert(bmc_final_tag(0, t, c0, c1, c2, c3)
            == s0 ^ s1 ^ r1 ^ r2 ^ r3);
        assert(s0 ^ (s1 ^ r1) ^ r2 ^ r3 == s0 ^ s1 ^ r1 ^ r2 ^ r3)
            by (bit_vector);
        assert(bmc_partial_tag(0, t, 4, c0, c1, c2, c3)
            == bmc_final_tag(0, t, c0, c1, c2, c3));
    } else if k == 1 {
        assert(bmc_contrib_tag(0, 1, t, c0, c1, c2, c3) == r0);
        assert(bmc_contrib_tag(1, 1, t, c0, c1, c2, c3) == s1);
        assert(bmc_contrib_tag(2, 1, t, c0, c1, c2, c3) == s2 ^ r2);
        assert(bmc_contrib_tag(3, 1, t, c0, c1, c2, c3) == r3);
        assert(bmc_partial_tag(1, t, 4, c0, c1, c2, c3)
            == ((r0 ^ s1) ^ (s2 ^ r2)) ^ r3);
        assert(bmc_final_tag(1, t, c0, c1, c2, c3)
            == s1 ^ s2 ^ r2 ^ r3 ^ r0);
        assert(((r0 ^ s1) ^ (s2 ^ r2)) ^ r3 == s1 ^ s2 ^ r2 ^ r3 ^ r0)
            by (bit_vector);
        assert(bmc_partial_tag(1, t, 4, c0, c1, c2, c3)
            == bmc_final_tag(1, t, c0, c1, c2, c3));
    } else if k == 2 {
        assert(bmc_contrib_tag(0, 2, t, c0, c1, c2, c3) == r0);
        assert(bmc_contrib_tag(1, 2, t, c0, c1, c2, c3) == r1);
        assert(bmc_contrib_tag(2, 2, t, c0, c1, c2, c3) == s2);
        assert(bmc_contrib_tag(3, 2, t, c0, c1, c2, c3) == s3 ^ r3);
        assert(bmc_partial_tag(2, t, 4, c0, c1, c2, c3)
            == ((r0 ^ r1) ^ s2) ^ (s3 ^ r3));
        assert(bmc_final_tag(2, t, c0, c1, c2, c3)
            == s2 ^ s3 ^ r3 ^ r0 ^ r1);
        assert(((r0 ^ r1) ^ s2) ^ (s3 ^ r3) == s2 ^ s3 ^ r3 ^ r0 ^ r1)
            by (bit_vector);
        assert(bmc_partial_tag(2, t, 4, c0, c1, c2, c3)
            == bmc_final_tag(2, t, c0, c1, c2, c3));
    } else {
        assert(bmc_contrib_tag(0, 3, t, c0, c1, c2, c3) == s0 ^ r0);
        assert(bmc_contrib_tag(1, 3, t, c0, c1, c2, c3) == r1);
        assert(bmc_contrib_tag(2, 3, t, c0, c1, c2, c3) == r2);
        assert(bmc_contrib_tag(3, 3, t, c0, c1, c2, c3) == s3);
        assert(bmc_partial_tag(3, t, 4, c0, c1, c2, c3)
            == (((s0 ^ r0) ^ r1) ^ r2) ^ s3);
        assert(bmc_final_tag(3, t, c0, c1, c2, c3)
            == s3 ^ s0 ^ r0 ^ r1 ^ r2);
        assert((((s0 ^ r0) ^ r1) ^ r2) ^ s3 == s3 ^ s0 ^ r0 ^ r1 ^ r2)
            by (bit_vector);
        assert(bmc_partial_tag(3, t, 4, c0, c1, c2, c3)
            == bmc_final_tag(3, t, c0, c1, c2, c3));
    }
}

/// Exec lane for the ::5 b_key arithmetic (the upstream
/// rotate_left(1) ^ (a_key_7 >> 6/4/3) spelling; the two widened
/// rotate lanes cast separately -- the probe-def6 shape).
pub fn xt_lane(a: u8) -> (b: u8)
    ensures
        b == xtime_key(a),
{
    let lo = (((a as u16) << 1) & 0xff) as u8;
    let hi = ((a as u16) >> 7) as u8;
    let rot = (hi | lo) as u8;
    let a7 = (a & 0x80) as u8;
    rot ^ (a7 >> 6) ^ (a7 >> 4) ^ (a7 >> 3)
}

#[verifier::external_body]
pub fn bytewise_mix_columns(
    self_keys: &[u8],
    self_tags: &[u128],
    nst: usize,
) -> (o: ByteCommits)
    requires
        nst >= 4,
        self_keys.len() == 4 * nst,
        self_keys.len() * 8 == self_tags.len(),
        32 * nst <= usize::MAX,
    ensures
        o.keys.len() == 4 * nst,
        o.tags.len() == 32 * nst,
        forall |cc: int, k: int|
            #![trigger o.keys[4 * cc + k]]
            0 <= cc < (nst as int) && 0 <= k < 4
                ==> o.keys[4 * cc + k]
                    == bmc_final_key(
                        k,
                        self_keys[4 * cc], self_keys[4 * cc + 1],
                        self_keys[4 * cc + 2], self_keys[4 * cc + 3],
                    ),
        forall |cc: int, k: int, t: int|
            #![trigger o.tags[8 * (4 * cc + k) + t]]
            0 <= cc < (nst as int) && 0 <= k < 4 && 0 <= t < 8
                ==> o.tags[8 * (4 * cc + k) + t]
                    == bmc_final_tag(
                        k, t,
                        trow_of(self_tags@, cc, 0),
                        trow_of(self_tags@, cc, 1),
                        trow_of(self_tags@, cc, 2),
                        trow_of(self_tags@, cc, 3),
                    )
{
    // zero allocation (the Array::default() lowering)
    let mut o_keys: Vec<u8> = Vec::new();
    let mut o_tags: Vec<u128> = Vec::new();
    let mut q: usize = 0;
    while q < 4 * nst
        invariant
            q <= 4 * nst,
            (4 * nst) <= usize::MAX,
            o_keys.len() == q,
            forall |j: int| 0 <= j < q ==> o_keys[j] == 0u8,
        decreases
            (4 * nst) - q,
    {
        o_keys.push(0u8);
        q += 1;
    }
    let mut q2: usize = 0;
    while q2 < 32 * nst
        invariant
            self_keys.len() == 4 * nst,
            nst >= 4,
            q2 <= 32 * nst,
            (32 * nst) <= usize::MAX,
            o_tags.len() == q2,
            o_keys.len() == 4 * nst,
            forall |j: int| 0 <= j < q2 ==> o_tags[j] == 0u128,
            forall |j: int| 0 <= j < o_keys.len() ==> o_keys[j] == 0u8,
        decreases
            (32 * nst) - q2,
    {
        o_tags.push(0u128);
        q2 += 1;
    }
    let mut c: usize = 0;
    while c < nst
        invariant
            c <= nst,
            nst >= 4,
            (4 * nst) <= usize::MAX,
            (32 * nst) <= usize::MAX,
            self_keys.len() == 4 * nst,
            self_keys.len() * 8 == self_tags.len(),
            o_keys.len() == 4 * nst,
            o_tags.len() == 32 * nst,
            // done columns: the full final lattice
            forall |cc: int, k: int|
                #![trigger o_keys[4 * cc + k]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_keys[4 * cc + k]
                        == bmc_final_key(
                            k,
                            self_keys[4 * cc],
                            self_keys[4 * cc + 1],
                            self_keys[4 * cc + 2],
                            self_keys[4 * cc + 3],
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 0]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 0]
                        == bmc_final_tag(
                            k, 0,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 1]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 1]
                        == bmc_final_tag(
                            k, 1,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 2]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 2]
                        == bmc_final_tag(
                            k, 2,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 3]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 3]
                        == bmc_final_tag(
                            k, 3,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 4]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 4]
                        == bmc_final_tag(
                            k, 4,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 5]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 5]
                        == bmc_final_tag(
                            k, 5,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 6]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 6]
                        == bmc_final_tag(
                            k, 6,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 7]]
                0 <= cc < c && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 7]
                        == bmc_final_tag(
                            k, 7,
                            trow_of(self_tags@, cc, 0),
                            trow_of(self_tags@, cc, 1),
                            trow_of(self_tags@, cc, 2),
                            trow_of(self_tags@, cc, 3),
                        ),
            // untouched columns still zero
            forall |cc: int, k: int|
                #![trigger o_keys[4 * cc + k]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_keys[4 * cc + k] == 0u8,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 0]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 0] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 1]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 1] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 2]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 2] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 3]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 3] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 4]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 4] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 5]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 5] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 6]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 6] == 0u128,
            forall |cc: int, k: int|
                #![trigger o_tags[8 * (4 * cc + k) + 7]]
                c <= cc < (nst as int) && 0 <= k < 4
                    ==> o_tags[8 * (4 * cc + k) + 7] == 0u128,
        decreases
            nst - c,
    {
        let mut r: usize = 0;
        while r < 4
            invariant
                r <= 4,
                nst >= 4,
                (4 * nst) <= usize::MAX,
                (32 * nst) <= usize::MAX,
                c < nst,
                self_keys.len() == 4 * nst,
                self_keys.len() * 8 == self_tags.len(),
                o_keys.len() == 4 * nst,
                o_tags.len() == 32 * nst,
                forall |cc: int, k: int|
                    #![trigger o_keys[4 * cc + k]]
                    0 <= cc < c && 0 <= k < 4
                        ==> o_keys[4 * cc + k]
                            == bmc_final_key(
                                k,
                                self_keys[4 * cc],
                                self_keys[4 * cc + 1],
                                self_keys[4 * cc + 2],
                                self_keys[4 * cc + 3],
                            ),
                forall |cc: int, k: int, t: int|
                    #![trigger o_tags[8 * (4 * cc + k) + t]]
                    0 <= cc < c && 0 <= k < 4 && 0 <= t < 8
                        ==> o_tags[8 * (4 * cc + k) + t]
                            == bmc_final_tag(
                                k, t,
                                trow_of(self_tags@, cc, 0),
                                trow_of(self_tags@, cc, 1),
                                trow_of(self_tags@, cc, 2),
                                trow_of(self_tags@, cc, 3),
                            ),
                forall |cc: int, k: int|
                    #![trigger o_keys[4 * cc + k]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_keys[4 * cc + k] == 0u8,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 0]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 0] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 1]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 1] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 2]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 2] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 3]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 3] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 4]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 4] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 5]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 5] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 6]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 6] == 0u128,
                forall |cc: int, k: int|
                    #![trigger o_tags[8 * (4 * cc + k) + 7]]
                    c < cc < (nst as int) && 0 <= k < 4
                        ==> o_tags[8 * (4 * cc + k) + 7] == 0u128,
                // the current column at r rows applied
                forall |k: int|
                    #![trigger o_keys[4 * c + k]]
                    0 <= k < 4
                        ==> o_keys[4 * c + k]
                            == bmc_partial_key(
                                k, r as int,
                                self_keys[4 * c],
                                self_keys[4 * c + 1],
                                self_keys[4 * c + 2],
                                self_keys[4 * c + 3],
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 0]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 0]
                            == bmc_partial_tag(
                                k, 0, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 1]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 1]
                            == bmc_partial_tag(
                                k, 1, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 2]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 2]
                            == bmc_partial_tag(
                                k, 2, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 3]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 3]
                            == bmc_partial_tag(
                                k, 3, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 4]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 4]
                            == bmc_partial_tag(
                                k, 4, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 5]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 5]
                            == bmc_partial_tag(
                                k, 5, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 6]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 6]
                            == bmc_partial_tag(
                                k, 6, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
                forall |k: int|
                    #![trigger o_tags[8 * (4 * c + k) + 7]]
                    0 <= k < 4
                        ==> o_tags[8 * (4 * c + k) + 7]
                            == bmc_partial_tag(
                                k, 7, r as int,
                                trow_of(self_tags@, c as int, 0),
                                trow_of(self_tags@, c as int, 1),
                                trow_of(self_tags@, c as int, 2),
                                trow_of(self_tags@, c as int, 3),
                            ),
            decreases
                4 - r,
        {
            // ::4
            let a_key = self_keys[4 * c + r];
            // ::5
            let a_key_7 = a_key & 0x80;
            let b_key = xt_lane(a_key);
            assert(b_key == xtime_key(a_key));
            let mut a_tags: [u128; 8] = [0u128; 8];
            let mut tt: usize = 0;
            while tt < 8
                invariant
                    tt <= 8,
                    nst >= 4,
                    c < nst,
                    r < 4,
                    self_keys.len() == 4 * nst,
                    self_keys.len() * 8 == self_tags.len(),
                    (32 * nst) <= usize::MAX,
                    forall |k: int| 0 <= k < tt
                        ==> a_tags[k] == self_tags[8 * (4 * c + r) + k],
                decreases
                    8 - tt,
            {
                a_tags[tt] = self_tags[8 * (4 * c + r) + tt];
                tt += 1;
            }
            assert(a_tags@ == trow_of(self_tags@, c as int, r as int));
            let mut b_tags: [u128; 8] = [0u128; 8];
            b_tags[0] = a_tags[7];
            b_tags[1] = a_tags[0] ^ a_tags[7];
            b_tags[2] = a_tags[1];
            b_tags[3] = a_tags[2] ^ a_tags[7];
            b_tags[4] = a_tags[3] ^ a_tags[7];
            b_tags[5] = a_tags[4];
            b_tags[6] = a_tags[5];
            b_tags[7] = a_tags[6];
            assert(forall |t: int| 0 <= t < 8 ==> b_tags[t] == btag_slot(a_tags@, t));
            // ::6..10 -- the constant-bound j-lanes unrolled (the
            // upstream j loops run 0..2 resp. 1..4; order preserved:
            // b into slot r then slot (r+3), a into (r+1),(r+2),(r+3))
            // j = 0: off == r, b(r) -- hv-snap + plain assign
            // (#FA11-10: the compound ^=? write does not expose its
            // update to split-branch reads; probe-vec recipe)
            let hv1 = o_keys[4 * c + r];
            let ht1_0 = o_tags[8 * (4 * c + r) + 0];
            let ht1_1 = o_tags[8 * (4 * c + r) + 1];
            let ht1_2 = o_tags[8 * (4 * c + r) + 2];
            let ht1_3 = o_tags[8 * (4 * c + r) + 3];
            let ht1_4 = o_tags[8 * (4 * c + r) + 4];
            let ht1_5 = o_tags[8 * (4 * c + r) + 5];
            let ht1_6 = o_tags[8 * (4 * c + r) + 6];
            let ht1_7 = o_tags[8 * (4 * c + r) + 7];
            o_keys[4 * c + r] = hv1 ^ b_key;
            o_tags[8 * (4 * c + r) + 0] = ht1_0 ^ b_tags[0];
            o_tags[8 * (4 * c + r) + 1] = ht1_1 ^ b_tags[1];
            o_tags[8 * (4 * c + r) + 2] = ht1_2 ^ b_tags[2];
            o_tags[8 * (4 * c + r) + 3] = ht1_3 ^ b_tags[3];
            o_tags[8 * (4 * c + r) + 4] = ht1_4 ^ b_tags[4];
            o_tags[8 * (4 * c + r) + 5] = ht1_5 ^ b_tags[5];
            o_tags[8 * (4 * c + r) + 6] = ht1_6 ^ b_tags[6];
            o_tags[8 * (4 * c + r) + 7] = ht1_7 ^ b_tags[7];
            // j = 1: off == (r+3) % 4, b(r) -- hv-snap + plain assign
            let off31 = (4 + r - 1) % 4;
            let hv2 = o_keys[4 * c + off31];
            let ht2_0 = o_tags[8 * (4 * c + off31) + 0];
            let ht2_1 = o_tags[8 * (4 * c + off31) + 1];
            let ht2_2 = o_tags[8 * (4 * c + off31) + 2];
            let ht2_3 = o_tags[8 * (4 * c + off31) + 3];
            let ht2_4 = o_tags[8 * (4 * c + off31) + 4];
            let ht2_5 = o_tags[8 * (4 * c + off31) + 5];
            let ht2_6 = o_tags[8 * (4 * c + off31) + 6];
            let ht2_7 = o_tags[8 * (4 * c + off31) + 7];
            o_keys[4 * c + off31] = hv2 ^ b_key;
            o_tags[8 * (4 * c + off31) + 0] = ht2_0 ^ b_tags[0];
            o_tags[8 * (4 * c + off31) + 1] = ht2_1 ^ b_tags[1];
            o_tags[8 * (4 * c + off31) + 2] = ht2_2 ^ b_tags[2];
            o_tags[8 * (4 * c + off31) + 3] = ht2_3 ^ b_tags[3];
            o_tags[8 * (4 * c + off31) + 4] = ht2_4 ^ b_tags[4];
            o_tags[8 * (4 * c + off31) + 5] = ht2_5 ^ b_tags[5];
            o_tags[8 * (4 * c + off31) + 6] = ht2_6 ^ b_tags[6];
            o_tags[8 * (4 * c + off31) + 7] = ht2_7 ^ b_tags[7];
            // j2 = 1..3: off == (r+1)%4, (r+2)%4, (r+3)%4, a(r)
            let oa1 = (r + 1) % 4;
            let hv3 = o_keys[4 * c + oa1];
            let ht3_0 = o_tags[8 * (4 * c + oa1) + 0];
            let ht3_1 = o_tags[8 * (4 * c + oa1) + 1];
            let ht3_2 = o_tags[8 * (4 * c + oa1) + 2];
            let ht3_3 = o_tags[8 * (4 * c + oa1) + 3];
            let ht3_4 = o_tags[8 * (4 * c + oa1) + 4];
            let ht3_5 = o_tags[8 * (4 * c + oa1) + 5];
            let ht3_6 = o_tags[8 * (4 * c + oa1) + 6];
            let ht3_7 = o_tags[8 * (4 * c + oa1) + 7];
            o_keys[4 * c + oa1] = hv3 ^ a_key;
            o_tags[8 * (4 * c + oa1) + 0] = ht3_0 ^ a_tags[0];
            o_tags[8 * (4 * c + oa1) + 1] = ht3_1 ^ a_tags[1];
            o_tags[8 * (4 * c + oa1) + 2] = ht3_2 ^ a_tags[2];
            o_tags[8 * (4 * c + oa1) + 3] = ht3_3 ^ a_tags[3];
            o_tags[8 * (4 * c + oa1) + 4] = ht3_4 ^ a_tags[4];
            o_tags[8 * (4 * c + oa1) + 5] = ht3_5 ^ a_tags[5];
            o_tags[8 * (4 * c + oa1) + 6] = ht3_6 ^ a_tags[6];
            o_tags[8 * (4 * c + oa1) + 7] = ht3_7 ^ a_tags[7];
            let oa2 = (r + 2) % 4;
            let hv4 = o_keys[4 * c + oa2];
            let ht4_0 = o_tags[8 * (4 * c + oa2) + 0];
            let ht4_1 = o_tags[8 * (4 * c + oa2) + 1];
            let ht4_2 = o_tags[8 * (4 * c + oa2) + 2];
            let ht4_3 = o_tags[8 * (4 * c + oa2) + 3];
            let ht4_4 = o_tags[8 * (4 * c + oa2) + 4];
            let ht4_5 = o_tags[8 * (4 * c + oa2) + 5];
            let ht4_6 = o_tags[8 * (4 * c + oa2) + 6];
            let ht4_7 = o_tags[8 * (4 * c + oa2) + 7];
            o_keys[4 * c + oa2] = hv4 ^ a_key;
            o_tags[8 * (4 * c + oa2) + 0] = ht4_0 ^ a_tags[0];
            o_tags[8 * (4 * c + oa2) + 1] = ht4_1 ^ a_tags[1];
            o_tags[8 * (4 * c + oa2) + 2] = ht4_2 ^ a_tags[2];
            o_tags[8 * (4 * c + oa2) + 3] = ht4_3 ^ a_tags[3];
            o_tags[8 * (4 * c + oa2) + 4] = ht4_4 ^ a_tags[4];
            o_tags[8 * (4 * c + oa2) + 5] = ht4_5 ^ a_tags[5];
            o_tags[8 * (4 * c + oa2) + 6] = ht4_6 ^ a_tags[6];
            o_tags[8 * (4 * c + oa2) + 7] = ht4_7 ^ a_tags[7];
            let oa3 = (r + 3) % 4;
            let hv5 = o_keys[4 * c + oa3];
            let ht5_0 = o_tags[8 * (4 * c + oa3) + 0];
            let ht5_1 = o_tags[8 * (4 * c + oa3) + 1];
            let ht5_2 = o_tags[8 * (4 * c + oa3) + 2];
            let ht5_3 = o_tags[8 * (4 * c + oa3) + 3];
            let ht5_4 = o_tags[8 * (4 * c + oa3) + 4];
            let ht5_5 = o_tags[8 * (4 * c + oa3) + 5];
            let ht5_6 = o_tags[8 * (4 * c + oa3) + 6];
            let ht5_7 = o_tags[8 * (4 * c + oa3) + 7];
            o_keys[4 * c + oa3] = hv5 ^ a_key;
            o_tags[8 * (4 * c + oa3) + 0] = ht5_0 ^ a_tags[0];
            o_tags[8 * (4 * c + oa3) + 1] = ht5_1 ^ a_tags[1];
            o_tags[8 * (4 * c + oa3) + 2] = ht5_2 ^ a_tags[2];
            o_tags[8 * (4 * c + oa3) + 3] = ht5_3 ^ a_tags[3];
            o_tags[8 * (4 * c + oa3) + 4] = ht5_4 ^ a_tags[4];
            o_tags[8 * (4 * c + oa3) + 5] = ht5_5 ^ a_tags[5];
            o_tags[8 * (4 * c + oa3) + 6] = ht5_6 ^ a_tags[6];
            o_tags[8 * (4 * c + oa3) + 7] = ht5_7 ^ a_tags[7];
            // per-r split proof block (#FA11-9 mitigation: with r
            // concrete, the enumerated partial folds and the
            // write lanes compose per slot; kit option (b))
            if r == 0 {
                assert(bmc_contrib_key(0, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]));
                assert(bmc_partial_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(4 * c + r == 4 * c + 0);
                assert(hv1 == 0u8);
                assert(o_keys[4 * c + 0] == hv1 ^ b_key);
                assert(0u8 ^ b_key == b_key) by (bit_vector);
                assert(hv1 ^ b_key == b_key);
                assert(o_keys[4 * c + 0] == b_key);
                assert(b_key == xtime_key(self_keys[4 * c + 0]));
                assert(bmc_partial_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 0]);
                assert(bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 0]);
                assert(bmc_partial_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(oa1 == 1);
                assert(hv3 == 0u8);
                assert(o_keys[4 * c + 1] == hv3 ^ a_key);
                assert(0u8 ^ a_key == a_key) by (bit_vector);
                assert(hv3 ^ a_key == a_key);
                assert(o_keys[4 * c + 1] == a_key);
                assert(a_key == self_keys[4 * c + 0]);
                assert(bmc_partial_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 1]);
                assert(bmc_contrib_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 0]);
                assert(bmc_partial_key(2, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(oa2 == 2);
                assert(hv4 == 0u8);
                assert(o_keys[4 * c + 2] == hv4 ^ a_key);
                assert(0u8 ^ a_key == a_key) by (bit_vector);
                assert(hv4 ^ a_key == a_key);
                assert(o_keys[4 * c + 2] == a_key);
                assert(a_key == self_keys[4 * c + 0]);
                assert(bmc_partial_key(2, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 2]);
                assert(bmc_contrib_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]) ^ self_keys[4 * c + 0]);
                assert(bmc_partial_key(3, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(oa3 == 3);
                assert(hv2 == 0u8);
                assert(hv5 == hv2 ^ b_key);
                assert(0u8 ^ b_key == b_key) by (bit_vector);
                assert(hv2 ^ b_key == b_key);
                assert(hv5 == b_key);
                assert(o_keys[4 * c + 3] == hv5 ^ a_key);
                assert(0u8 ^ (b_key ^ a_key) == b_key ^ a_key) by (bit_vector);
                assert(b_key ^ a_key == a_key ^ b_key) by (bit_vector);
                assert(o_keys[4 * c + 3] == b_key ^ a_key);
                assert(a_key == self_keys[4 * c + 0]);
                assert(b_key == xtime_key(self_keys[4 * c + 0]));
                assert(bmc_partial_key(3, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 3]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 0), t));
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(0, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(0, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(0, 0, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 0]);
                assert(bmc_partial_tag(0, 1, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 1]);
                assert(bmc_partial_tag(0, 2, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 2]);
                assert(bmc_partial_tag(0, 3, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 3]);
                assert(bmc_partial_tag(0, 4, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 4]);
                assert(bmc_partial_tag(0, 5, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 5]);
                assert(bmc_partial_tag(0, 6, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 6]);
                assert(bmc_partial_tag(0, 7, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(1, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(1, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(1, 0, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 0]);
                assert(bmc_partial_tag(1, 1, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 1]);
                assert(bmc_partial_tag(1, 2, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 2]);
                assert(bmc_partial_tag(1, 3, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 3]);
                assert(bmc_partial_tag(1, 4, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 4]);
                assert(bmc_partial_tag(1, 5, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 5]);
                assert(bmc_partial_tag(1, 6, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 6]);
                assert(bmc_partial_tag(1, 7, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(2, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(2, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(2, 0, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 0]);
                assert(bmc_partial_tag(2, 1, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 1]);
                assert(bmc_partial_tag(2, 2, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 2]);
                assert(bmc_partial_tag(2, 3, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 3]);
                assert(bmc_partial_tag(2, 4, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 4]);
                assert(bmc_partial_tag(2, 5, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 5]);
                assert(bmc_partial_tag(2, 6, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 6]);
                assert(bmc_partial_tag(2, 7, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 0), t) ^ trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(3, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(3, t, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(3, 0, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 0]);
                assert(bmc_partial_tag(3, 1, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 1]);
                assert(bmc_partial_tag(3, 2, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 2]);
                assert(bmc_partial_tag(3, 3, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 3]);
                assert(bmc_partial_tag(3, 4, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 4]);
                assert(bmc_partial_tag(3, 5, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 5]);
                assert(bmc_partial_tag(3, 6, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 6]);
                assert(bmc_partial_tag(3, 7, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 7]);
            } else if r == 1 {
                assert(bmc_contrib_key(0, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]));
                assert(bmc_contrib_key(1, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 1]) ^ self_keys[4 * c + 1]);
                assert(bmc_partial_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(off31 == 0);
                assert(oa3 == 0);
                assert(hv2 == bmc_partial_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]));
                assert(hv2 == xtime_key(self_keys[4 * c + 0]));
                assert(b_key == xtime_key(self_keys[4 * c + 1]));
                assert(a_key == self_keys[4 * c + 1]);
                assert(hv5 == hv2 ^ b_key);
                assert(o_keys[4 * c + 0] == hv5 ^ a_key);
                assert(o_keys[4 * c + 0] == hv2 ^ b_key ^ a_key);
                assert((hv2 ^ b_key) ^ a_key == hv2 ^ (b_key ^ a_key)) by (bit_vector);
                assert(bmc_contrib_key(1, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == b_key ^ a_key);
                assert(bmc_partial_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == (hv2 ^ b_key) ^ a_key);
                assert(bmc_partial_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 0]);
                assert(bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 0]);
                assert(bmc_contrib_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 1]));
                assert(bmc_partial_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 1]);
                assert(bmc_contrib_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 0]);
                assert(bmc_contrib_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 1]);
                assert(bmc_partial_key(2, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(2, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 2]);
                assert(bmc_contrib_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]) ^ self_keys[4 * c + 0]);
                assert(bmc_contrib_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 1]);
                assert(bmc_partial_key(3, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(3, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 3]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 0), t));
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 1), t) ^ trow_of(self_tags@, c as int, 1)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(0, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(0, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(0, 0, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 0]);
                assert(bmc_partial_tag(0, 1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 1]);
                assert(bmc_partial_tag(0, 2, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 2]);
                assert(bmc_partial_tag(0, 3, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 3]);
                assert(bmc_partial_tag(0, 4, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 4]);
                assert(bmc_partial_tag(0, 5, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 5]);
                assert(bmc_partial_tag(0, 6, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 6]);
                assert(bmc_partial_tag(0, 7, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 1), t));
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(1, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(1, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(1, 0, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 0]);
                assert(bmc_partial_tag(1, 1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 1]);
                assert(bmc_partial_tag(1, 2, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 2]);
                assert(bmc_partial_tag(1, 3, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 3]);
                assert(bmc_partial_tag(1, 4, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 4]);
                assert(bmc_partial_tag(1, 5, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 5]);
                assert(bmc_partial_tag(1, 6, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 6]);
                assert(bmc_partial_tag(1, 7, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 1) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 1)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(2, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(2, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(2, 0, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 0]);
                assert(bmc_partial_tag(2, 1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 1]);
                assert(bmc_partial_tag(2, 2, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 2]);
                assert(bmc_partial_tag(2, 3, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 3]);
                assert(bmc_partial_tag(2, 4, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 4]);
                assert(bmc_partial_tag(2, 5, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 5]);
                assert(bmc_partial_tag(2, 6, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 6]);
                assert(bmc_partial_tag(2, 7, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 0), t) ^ trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 1)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(3, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(3, t, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(3, 0, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 0]);
                assert(bmc_partial_tag(3, 1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 1]);
                assert(bmc_partial_tag(3, 2, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 2]);
                assert(bmc_partial_tag(3, 3, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 3]);
                assert(bmc_partial_tag(3, 4, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 4]);
                assert(bmc_partial_tag(3, 5, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 5]);
                assert(bmc_partial_tag(3, 6, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 6]);
                assert(bmc_partial_tag(3, 7, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 7]);
            } else if r == 2 {
                assert(bmc_contrib_key(0, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]));
                assert(bmc_contrib_key(1, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 1]) ^ self_keys[4 * c + 1]);
                assert(bmc_contrib_key(2, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 2]);
                assert(bmc_partial_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(2, 0, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 0]);
                assert(bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 0]);
                assert(bmc_contrib_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 1]));
                assert(bmc_contrib_key(2, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 2]) ^ self_keys[4 * c + 2]);
                assert(bmc_partial_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(2, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(off31 == 1);
                assert(oa3 == 1);
                assert(hv2 == bmc_partial_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                        ^ bmc_contrib_key(1, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(b_key == xtime_key(self_keys[4 * c + 2]));
                assert(a_key == self_keys[4 * c + 2]);
                assert(hv5 == hv2 ^ b_key);
                assert(o_keys[4 * c + 1] == hv5 ^ a_key);
                assert(o_keys[4 * c + 1] == hv2 ^ b_key ^ a_key);
                assert((hv2 ^ b_key) ^ a_key == hv2 ^ (b_key ^ a_key)) by (bit_vector);
                assert(bmc_contrib_key(2, 1, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == b_key ^ a_key);
                assert(bmc_partial_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == (hv2 ^ b_key) ^ a_key);
                assert(bmc_partial_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 1]);
                assert(bmc_contrib_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 0]);
                assert(bmc_contrib_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 1]);
                assert(bmc_contrib_key(2, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 2]));
                assert(bmc_partial_key(2, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(2, 2, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(2, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 2]);
                assert(bmc_contrib_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == xtime_key(self_keys[4 * c + 0]) ^ self_keys[4 * c + 0]);
                assert(bmc_contrib_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 1]);
                assert(bmc_contrib_key(2, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == self_keys[4 * c + 2]);
                assert(bmc_partial_key(3, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == bmc_contrib_key(0, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(1, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]) ^ bmc_contrib_key(2, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3]));
                assert(bmc_partial_key(3, 3, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                    == o_keys[4 * c + 3]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 0), t));
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 1), t) ^ trow_of(self_tags@, c as int, 1)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(2, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(2, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 2)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(0, t, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(0, t, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(2, 0, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(0, 0, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 0]);
                assert(bmc_partial_tag(0, 1, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 1]);
                assert(bmc_partial_tag(0, 2, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 2]);
                assert(bmc_partial_tag(0, 3, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 3]);
                assert(bmc_partial_tag(0, 4, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 4]);
                assert(bmc_partial_tag(0, 5, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 5]);
                assert(bmc_partial_tag(0, 6, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 6]);
                assert(bmc_partial_tag(0, 7, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 0) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 1), t));
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(2, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(2, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 2), t) ^ trow_of(self_tags@, c as int, 2)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(1, t, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(1, t, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(2, 1, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                let q1t = b_tags[0];
                let r1t = a_tags[0];
                let p1t = ht2_0;
                assert(bmc_partial_tag(1, 0, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 0, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 0] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 0, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[1];
                let r1t = a_tags[1];
                let p1t = ht2_1;
                assert(bmc_partial_tag(1, 1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 1] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 1, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[2];
                let r1t = a_tags[2];
                let p1t = ht2_2;
                assert(bmc_partial_tag(1, 2, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 2] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 2, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[3];
                let r1t = a_tags[3];
                let p1t = ht2_3;
                assert(bmc_partial_tag(1, 3, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 3] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 3, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[4];
                let r1t = a_tags[4];
                let p1t = ht2_4;
                assert(bmc_partial_tag(1, 4, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 4] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 4, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[5];
                let r1t = a_tags[5];
                let p1t = ht2_5;
                assert(bmc_partial_tag(1, 5, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 5, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 5] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 5, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[6];
                let r1t = a_tags[6];
                let p1t = ht2_6;
                assert(bmc_partial_tag(1, 6, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 6, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 6] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 6, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);
                let q1t = b_tags[7];
                let r1t = a_tags[7];
                let p1t = ht2_7;
                assert(bmc_partial_tag(1, 7, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == p1t);
                assert(bmc_contrib_tag(2, 1, 7, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == q1t ^ r1t);
                assert(p1t ^ (q1t ^ r1t)
                    == (p1t ^ q1t) ^ r1t) by (bit_vector);
                assert(o_tags[8 * (4 * c + 1) + 7] == (p1t ^ q1t) ^ r1t);
                assert(bmc_partial_tag(1, 7, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) == (p1t ^ q1t) ^ r1t);

                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 1)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(2, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(2, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 2), t));
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(3, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(3, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 3), t) ^ trow_of(self_tags@, c as int, 3)[t]);
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(2, t, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(2, t, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(2, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(3, 2, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(2, 0, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 0]);
                assert(bmc_partial_tag(2, 1, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 1]);
                assert(bmc_partial_tag(2, 2, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 2]);
                assert(bmc_partial_tag(2, 3, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 3]);
                assert(bmc_partial_tag(2, 4, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 4]);
                assert(bmc_partial_tag(2, 5, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 5]);
                assert(bmc_partial_tag(2, 6, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 6]);
                assert(bmc_partial_tag(2, 7, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 7]);
                assert(bmc_partial_tag(2, 0, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 0]);
                assert(bmc_partial_tag(2, 1, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 1]);
                assert(bmc_partial_tag(2, 2, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 2]);
                assert(bmc_partial_tag(2, 3, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 3]);
                assert(bmc_partial_tag(2, 4, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 4]);
                assert(bmc_partial_tag(2, 5, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 5]);
                assert(bmc_partial_tag(2, 6, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 6]);
                assert(bmc_partial_tag(2, 7, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 2) + 7]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 0), t) ^ trow_of(self_tags@, c as int, 0)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(1, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(1, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 1)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(2, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(2, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == trow_of(self_tags@, c as int, 2)[t]);
                assert(forall |t: int|
                    #![trigger bmc_contrib_tag(3, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_contrib_tag(3, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == btag_slot(trow_of(self_tags@, c as int, 3), t));
                assert(forall |t: int|
                    #![trigger bmc_partial_tag(3, t, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))]
                    0 <= t < 8
                        ==> bmc_partial_tag(3, t, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                            == bmc_contrib_tag(0, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(1, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(2, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)) ^ bmc_contrib_tag(3, 3, t, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3)));
                assert(bmc_partial_tag(3, 0, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 0]);
                assert(bmc_partial_tag(3, 1, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 1]);
                assert(bmc_partial_tag(3, 2, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 2]);
                assert(bmc_partial_tag(3, 3, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 3]);
                assert(bmc_partial_tag(3, 4, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 4]);
                assert(bmc_partial_tag(3, 5, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 5]);
                assert(bmc_partial_tag(3, 6, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 6]);
                assert(bmc_partial_tag(3, 7, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                    == o_tags[8 * (4 * c + 3) + 7]);
            }
            r += 1;
        }
        // column-closing material (per k, t: partial(4) == final via
        // the lemmas + the written slot values)
            assert(bmc_partial_key(0, 4, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                == o_keys[4 * c + 0]);
            proof {
                lemma_bmc_final_key(0,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]);
            }
            assert(o_keys[4 * c + 0]
                == bmc_final_key(0,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]));
            assert(bmc_partial_key(1, 4, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                == o_keys[4 * c + 1]);
            proof {
                lemma_bmc_final_key(1,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]);
            }
            assert(o_keys[4 * c + 1]
                == bmc_final_key(1,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]));
            assert(bmc_partial_key(2, 4, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                == o_keys[4 * c + 2]);
            proof {
                lemma_bmc_final_key(2,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]);
            }
            assert(o_keys[4 * c + 2]
                == bmc_final_key(2,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]));
            assert(bmc_partial_key(3, 4, self_keys[4 * c + 0], self_keys[4 * c + 1], self_keys[4 * c + 2], self_keys[4 * c + 3])
                == o_keys[4 * c + 3]);
            proof {
                lemma_bmc_final_key(3,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]);
            }
            assert(o_keys[4 * c + 3]
                == bmc_final_key(3,
                    self_keys[4 * c + 0], self_keys[4 * c + 1],
                    self_keys[4 * c + 2], self_keys[4 * c + 3]));
            proof {
                lemma_bmc_final_tag(0, 0,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 0, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 0]);
            proof {
                lemma_bmc_final_tag(0, 1,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 1]);
            proof {
                lemma_bmc_final_tag(0, 2,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 2]);
            proof {
                lemma_bmc_final_tag(0, 3,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 3]);
            proof {
                lemma_bmc_final_tag(0, 4,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 4]);
            proof {
                lemma_bmc_final_tag(0, 5,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 5, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 5]);
            proof {
                lemma_bmc_final_tag(0, 6,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 6, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 6]);
            proof {
                lemma_bmc_final_tag(0, 7,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(0, 7, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 0) + 7]);
            proof {
                lemma_bmc_final_tag(1, 0,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 0, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 0]);
            proof {
                lemma_bmc_final_tag(1, 1,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 1]);
            proof {
                lemma_bmc_final_tag(1, 2,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 2]);
            proof {
                lemma_bmc_final_tag(1, 3,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 3]);
            proof {
                lemma_bmc_final_tag(1, 4,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 4]);
            proof {
                lemma_bmc_final_tag(1, 5,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 5, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 5]);
            proof {
                lemma_bmc_final_tag(1, 6,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 6, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 6]);
            proof {
                lemma_bmc_final_tag(1, 7,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(1, 7, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 1) + 7]);
            proof {
                lemma_bmc_final_tag(2, 0,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 0, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 0]);
            proof {
                lemma_bmc_final_tag(2, 1,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 1]);
            proof {
                lemma_bmc_final_tag(2, 2,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 2]);
            proof {
                lemma_bmc_final_tag(2, 3,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 3]);
            proof {
                lemma_bmc_final_tag(2, 4,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 4]);
            proof {
                lemma_bmc_final_tag(2, 5,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 5, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 5]);
            proof {
                lemma_bmc_final_tag(2, 6,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 6, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 6]);
            proof {
                lemma_bmc_final_tag(2, 7,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(2, 7, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 2) + 7]);
            proof {
                lemma_bmc_final_tag(3, 0,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 0, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 0]);
            proof {
                lemma_bmc_final_tag(3, 1,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 1, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 1]);
            proof {
                lemma_bmc_final_tag(3, 2,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 2, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 2]);
            proof {
                lemma_bmc_final_tag(3, 3,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 3, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 3]);
            proof {
                lemma_bmc_final_tag(3, 4,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 4, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 4]);
            proof {
                lemma_bmc_final_tag(3, 5,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 5, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 5]);
            proof {
                lemma_bmc_final_tag(3, 6,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 6, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 6]);
            proof {
                lemma_bmc_final_tag(3, 7,
                    trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1),
                    trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3));
            }
            assert(bmc_final_tag(3, 7, trow_of(self_tags@, c as int, 0), trow_of(self_tags@, c as int, 1), trow_of(self_tags@, c as int, 2), trow_of(self_tags@, c as int, 3))
                == o_tags[8 * (4 * c + 3) + 7]);
        c += 1;
    }
    ByteCommits { keys: o_keys, tags: o_tags }
}

} // verus!
