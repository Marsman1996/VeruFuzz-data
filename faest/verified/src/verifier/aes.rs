//! faest 0.3.0 -- Verus transcription of src/verifier/aes.rs (the
//! constraint-system AES layer over the VoleCommits faces), batch
//! FA12.
//!
//! Upstream (verifier/aes.rs, 428 lines, pin 9ccc68c0): the
//! StateToBytes impls (:24-50), the AddRoundKey impl family
//! (:52-146), AddRoundKeyAssign (:148-182), InverseShiftRows
//! (:184-244), BytewiseMixColumns (:246-294), SBoxAffine (:296-332),
//! ShiftRows (:334-355), InverseAffine (:357-377), MixColumns
//! (:379-410), AddRoundKeyBytes (:412-428). The upstream file carries
//! no in-file test rows; its value surface rides the batch oracle
//! arm.
//!
//! Representation lowering (trust boundary; this batch's records):
//!   - `O: OWFParameters` (upstream :12-22 import block) drops to
//!     plain runtime size parameters (nst = NSt, nst_bytes =
//!     NStBytes, nst_bits = 32 * nst) whose call-site values are the
//!     FA9 tower pins (the FA10 RowCfg precedent; the AES-128 rows:
//!     NSt 4, NStBytes 16, NStBits 128). The trait-bounded generic
//!     impl dispatch (`impl<O> StateToBytes<O> for VoleCommits` etc.)
//!     re-erects as inherent faces below with Origin anchors (the
//!     FA6-pre field_commitment convention; FA4-1 keeps the
//!     impl-trait-for-type rows out of the twin).
//!   - Field addition (`+` on F / `+=`) is the char-2 limb xor (FA3
//!     record; upstream x_i + y_i lowers to scalars[i] ^ scalars[i]).
//!   - Field multiplication (Mul<F> on the sigma / beta / v2 / v3 /
//!     delta planes) is gf128_mul exec / gf128_mul_spec spec (FA3).
//!   - delta.square() (SBoxAffine ::8) is gf128_square exec, ==
//!     gf128_hmul(delta, delta) (FA3 twin).
//!   - `*delta * <u8 bit>` (the ::132-139 AddRoundKey byte face and
//!     from_constant) is the apply_mask(bit-0) select: delta or 0
//!     (large_fields record; NOT a field multiply).
//!   - The chunks_exact(8) / map / collect / zip iterator bodies
//!     lower to the index loops (FA6-pre convention); as_chunks_mut
//!     (::<8> InverseAffine, ::<4> MixColumns) lowers to the window
//!     index loop (FA11 mix_columns precedent); copy_from_slice
//!     lowers to the 8-step explicit index writes (FA11
//!     inverse_shift_rows precedent).
//!
//! Contract-machinery reuse (FA11 wave-2 ruling, first-hand
//! re-verified this batch): the BytewiseMixColumns contribution
//! lattice over the scalars plane is the SAME table the prover's
//! tag plane carries -- row rr writes b(rr) into slots
//! {rr, (rr+3)%4} and a(rr) into {(rr+1..rr+3)%4}, per 8-slot window,
//! with the b roster = [a7, a0^a7, a1, a2^a7, a3^a7, a4, a5, a6]
//! (upstream verifier :261-270 == upstream prover the same lane ==
//! btag_slot). This file does NOT re-erect the lattice: it does
//! `use crate::prover::aes::{bmc_final_tag, trow_of, ...}` per the
//! FA11 wave-2 pin. The same anti-dup logic reuses (all pub spec
//! faces of the prover twin): sr_src_idx / isr_src_idx (the
//! ShiftRows index arithmetic), mc_slot_key (MixColumns), iaf8 /
//! rot_l{1,3,6}_u8 / iaf_tag (InverseAffine). All are slice/Seq
//! parameter faces, container-independent.
//!
//! Faces (each with its upstream anchor):
//!   VoleCommits: state_to_bytes (:30-36), add_round_key_self
//!   (:59-69), add_round_key_assign (:153-158, three RHS lowering
//!   rows), add_round_key_assign field/u8 (:165-182),
//!   inverse_affine (:362-376), bytewise... see below; full list:
//!   state_to_bytes (:30), state_to_bytes_ref (:44),
//!   add_round_key_self (:59), add_round_key_vc (:78),
//!   add_round_key_ref (:97), add_round_key_field (:116),
//!   add_round_key_u8 (:132), add_round_key_assign_self (:153),
//!   add_round_key_assign_ref (:165), add_round_key_assign_field
//!   (:177), inverse_shift_rows_ref (:190) and
//!   inverse_shift_rows_vc (:221), bytewise_mix_columns (:252),
//!   s_box_affine (:302), shift_rows (:339), inverse_affine (:362),
//!   mix_columns (:383), add_round_key_bytes (:417).

use vstd::prelude::*;

use crate::large_fields::{
    gf128_byte_combine_slice, gf128_byte_combine_spec, gf128_hmul, gf128_mul,
    gf128_mul_spec, gf128_square, GF128_BYTE_COMBINE_2, GF128_BYTE_COMBINE_3,
    GF128_BYTE_COMBINE_SQ_2, GF128_BYTE_COMBINE_SQ_3, GF128_SIGMA,
    GF128_SIGMA_SQUARES,
};

// The FA11 contract machinery (the BytewiseMixColumns contribution
// lattice + the index-derivation spec faces), consumed across the
// impl-trait boundary per the wave-2 pin:
use crate::prover::aes::{
    bmc_final_tag, bmc_partial_tag, iaf_tag, isr_src_idx, mc_slot_key, sr_src_idx,
    src_line_36, trow_of,
};

use super::vole_commitments::{VoleCommits, VoleCommitsRef};

verus! {

// ===========================================================================
// StateToBytes (upstream :24-50): two impls over the chunked
// byte_combine fold.
//     impl<O> StateToBytes<O> for VoleCommits<'_, OWFField<O>, O::NStBits> {
//         fn state_to_bytes(&self) -> Self::Output {
//             self.scalars.chunks_exact(8)
//                 .map(OWFField::<O>::byte_combine_slice).collect() } }
// (and the identical body for VoleCommitsRef). The chunks_exact(8)
// iteration lowers to the window index loop.
// ===========================================================================

impl VoleCommits<'_> {
    /// Origin Rust (:30-36).
    pub fn state_to_bytes(self: &Self) -> (o: Vec<u128>)
        requires
            self.scalars.len() % 8 == 0,
        ensures
            o.len() == self.scalars.len() / 8,
            forall |j: int|
                0 <= j < o.len()
                    ==> o[j] == gf128_byte_combine_spec(
                        self.scalars[8 * j],
                        self.scalars[8 * j + 1],
                        self.scalars[8 * j + 2],
                        self.scalars[8 * j + 3],
                        self.scalars[8 * j + 4],
                        self.scalars[8 * j + 5],
                        self.scalars[8 * j + 6],
                        self.scalars[8 * j + 7],
                    ),
    {
        let mut out: Vec<u128> = Vec::new();
        let n_windows: usize = self.scalars.len() / 8;
        let mut i: usize = 0;
        while i < n_windows
            invariant
                n_windows == self.scalars.len() / 8,
                self.scalars.len() % 8 == 0,
                i <= n_windows,
                out.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> out[j] == gf128_byte_combine_spec(
                            self.scalars[8 * j],
                            self.scalars[8 * j + 1],
                            self.scalars[8 * j + 2],
                            self.scalars[8 * j + 3],
                            self.scalars[8 * j + 4],
                            self.scalars[8 * j + 5],
                            self.scalars[8 * j + 6],
                            self.scalars[8 * j + 7],
                        ),
            decreases
                n_windows - i,
        {
            let v: u128 = gf128_byte_combine_slice(&self.scalars[8 * i..8 * i + 8]);
            assert(v == gf128_byte_combine_spec(
                self.scalars[8 * i as int],
                self.scalars[8 * i as int + 1],
                self.scalars[8 * i as int + 2],
                self.scalars[8 * i as int + 3],
                self.scalars[8 * i as int + 4],
                self.scalars[8 * i as int + 5],
                self.scalars[8 * i as int + 6],
                self.scalars[8 * i as int + 7],
            ));
            out.push(v);
            i += 1;
        }
        out
    }
}

impl VoleCommitsRef<'_> {
    /// Origin Rust (:44-50): the identical chunked fold over the
    /// view's scalars window.
    pub fn state_to_bytes(self: &Self) -> (o: Vec<u128>)
        requires
            self.scalars.len() % 8 == 0,
        ensures
            o.len() == self.scalars.len() / 8,
            forall |j: int|
                0 <= j < o.len()
                    ==> o[j] == gf128_byte_combine_spec(
                        self.scalars[8 * j],
                        self.scalars[8 * j + 1],
                        self.scalars[8 * j + 2],
                        self.scalars[8 * j + 3],
                        self.scalars[8 * j + 4],
                        self.scalars[8 * j + 5],
                        self.scalars[8 * j + 6],
                        self.scalars[8 * j + 7],
                    ),
    {
        let mut out: Vec<u128> = Vec::new();
        let n_windows: usize = self.scalars.len() / 8;
        let mut i: usize = 0;
        while i < n_windows
            invariant
                n_windows == self.scalars.len() / 8,
                self.scalars.len() % 8 == 0,
                i <= n_windows,
                out.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> out[j] == gf128_byte_combine_spec(
                            self.scalars[8 * j],
                            self.scalars[8 * j + 1],
                            self.scalars[8 * j + 2],
                            self.scalars[8 * j + 3],
                            self.scalars[8 * j + 4],
                            self.scalars[8 * j + 5],
                            self.scalars[8 * j + 6],
                            self.scalars[8 * j + 7],
                        ),
            decreases
                n_windows - i,
        {
            let v: u128 = gf128_byte_combine_slice(&self.scalars[8 * i..8 * i + 8]);
            assert(v == gf128_byte_combine_spec(
                self.scalars[8 * i as int],
                self.scalars[8 * i as int + 1],
                self.scalars[8 * i as int + 2],
                self.scalars[8 * i as int + 3],
                self.scalars[8 * i as int + 4],
                self.scalars[8 * i as int + 5],
                self.scalars[8 * i as int + 6],
                self.scalars[8 * i as int + 7],
            ));
            out.push(v);
            i += 1;
        }
        out
    }
}

// ===========================================================================
// AddRoundKey (upstream :52-146): five impls -- all reduce to the
// zip elemwise field add (limb xor) of the scalars planes; the
// ::124-146 byte-key impl is the delta-scaled bit select.
// ===========================================================================

impl<'a> VoleCommits<'a> {
    /// Origin Rust (:52-69, `AddRoundKey<Self> for
    /// &VoleCommits<'a, F, L>`): zip(self.scalars.iter(),
    /// rhs.scalars.iter()) map(|(x, y)| *x + y) -- elemwise field add.
    pub fn add_round_key_self(
        self: &VoleCommits<'a>,
        rhs: &VoleCommits<'a>,
    ) -> (o: VoleCommits<'a>)
        requires
            self.scalars.len() == rhs.scalars.len(),
        ensures
            o.scalars.len() == self.scalars.len(),
            forall |j: int|
                0 <= j < o.scalars.len()
                    ==> o.scalars[j] == self.scalars[j as int]
                        ^ rhs.scalars[j as int],
            o.delta == self.delta,
    {
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.scalars.len(),
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j] == self.scalars[j as int]
                            ^ rhs.scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            scalars.push(self.scalars[i] ^ rhs.scalars[i]);
            i += 1;
        }
        VoleCommits { scalars, delta: self.delta }
    }
}

impl<'a> VoleCommitsRef<'a> {
    /// Origin Rust (:71-88, `AddRoundKey<&VoleCommits> for
    /// VoleCommitsRef`): zip(self.scalars, rhs.scalars.iter()) -- the
    /// owned-array iteration of self.scalars is the same window order
    /// (first-hand read).
    pub fn add_round_key_vc(
        self: &VoleCommitsRef<'a>,
        rhs: &VoleCommits<'a>,
    ) -> (o: VoleCommits<'a>)
        requires
            self.scalars.len() == rhs.scalars.len(),
        ensures
            o.scalars.len() == self.scalars.len(),
            forall |j: int|
                0 <= j < o.scalars.len()
                    ==> o.scalars[j] == self.scalars[j as int]
                        ^ rhs.scalars[j as int],
            o.delta == self.delta,
    {
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.scalars.len(),
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j] == self.scalars[j as int]
                            ^ rhs.scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            scalars.push(self.scalars[i] ^ rhs.scalars[i]);
            i += 1;
        }
        VoleCommits { scalars, delta: self.delta }
    }

    /// Origin Rust (:90-107, `AddRoundKey<&Self> for
    /// VoleCommitsRef`): zip(self.scalars, rhs.scalars) -- two views.
    pub fn add_round_key_ref(self: &Self, rhs: &Self) -> (o: VoleCommits<'a>)
        requires
            self.scalars.len() == rhs.scalars.len(),
        ensures
            o.scalars.len() == self.scalars.len(),
            forall |j: int|
                0 <= j < o.scalars.len()
                    ==> o.scalars[j] == self.scalars[j as int]
                        ^ rhs.scalars[j as int],
            o.delta == self.delta,
    {
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.scalars.len(),
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j] == self.scalars[j as int]
                            ^ rhs.scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            scalars.push(self.scalars[i] ^ rhs.scalars[i]);
            i += 1;
        }
        VoleCommits { scalars, delta: self.delta }
    }

    /// Origin Rust (:109-122, `AddRoundKey<&Array<F, L>> for
    /// VoleCommitsRef`): zip over a known field-value row.
    pub fn add_round_key_field(self: &Self, rhs: &[u128]) -> (o: VoleCommits<'a>)
        requires
            self.scalars.len() == rhs.len(),
        ensures
            o.scalars.len() == self.scalars.len(),
            forall |j: int|
                0 <= j < o.scalars.len()
                    ==> o.scalars[j] == self.scalars[j as int]
                        ^ rhs[j as int],
            o.delta == self.delta,
    {
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.len(),
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j] == self.scalars[j as int] ^ rhs[j as int],
            decreases
                self.scalars.len() - i,
        {
            scalars.push(self.scalars[i] ^ rhs[i]);
            i += 1;
        }
        VoleCommits { scalars, delta: self.delta }
    }

    /// Origin Rust (:124-146, `AddRoundKey<&Array<u8, L>> for
    /// VoleCommitsRef<'a, F, L2>` -- known key bytes): the per-bit
    /// delta select,
    ///     let scalars = Box::new(self.scalars.iter().enumerate()
    ///         .map(|(i, comm_i)| *comm_i
    ///             + *self.delta * ((rhs[i / 8] >> (i % 8)) & 1))
    ///         .collect());
    /// The L -> L2 = L * U8 correspondence lowers to the length row
    /// requires (self.scalars.len() == 8 * rhs.len()); the Mul<u8>
    /// is the bit-0 select (header record).
    pub fn add_round_key_u8(self: &Self, rhs: &[u8]) -> (o: VoleCommits<'a>)
        requires
            self.scalars.len() == rhs.len() * 8,
        ensures
            o.scalars.len() == self.scalars.len(),
            forall |j: int|
                0 <= j < o.scalars.len()
                    ==> o.scalars[j]
                        == (if (((rhs[j / 8] >> (j % 8)) & 1) == 1) {
                            *self.delta ^ self.scalars[j as int]
                        } else {
                            self.scalars[j as int]
                        }),
            o.delta == self.delta,
    {
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.len() * 8,
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j]
                            == (if (((rhs[j / 8] >> (j % 8)) & 1) == 1) {
                                *self.delta ^ self.scalars[j as int]
                            } else {
                                self.scalars[j as int]
                            }),
            decreases
                self.scalars.len() - i,
        {
            assert(i / 8 < rhs.len()) by (nonlinear_arith)
                requires
                    i < self.scalars.len(),
                    self.scalars.len() == rhs.len() * 8,
                    rhs.len() >= 0,
            {
            }
            let bit: u8 = (rhs[i / 8] >> (i % 8)) & 1;
            if bit == 1 {
                scalars.push(*self.delta ^ self.scalars[i]);
            } else {
                scalars.push(self.scalars[i]);
            }
            i += 1;
        }
        VoleCommits { scalars, delta: self.delta }
    }
}

// ===========================================================================
// AddRoundKeyAssign (upstream :148-182): three in-place impls --
// `*x += y` lowers to the elemwise limb-xor assign.
// ===========================================================================

impl VoleCommits<'_> {
    /// Origin Rust (:152-158, `AddRoundKeyAssign<&Self> for
    /// VoleCommits`): zip iter_mut loop.
    pub fn add_round_key_assign_self(self: &mut Self, rhs: &Self)
        requires
            self.scalars.len() == rhs.scalars.len(),
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            forall |j: int|
                0 <= j < final(self).scalars.len()
                    ==> final(self).scalars[j]
                        == old(self).scalars[j as int]
                            ^ rhs.scalars[j as int],
            *final(self).delta == *old(self).delta,
    {
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.scalars.len(),
                forall |j: int|
                    0 <= j < i
                        ==> self.scalars[j]
                            == old(self).scalars[j as int] ^ rhs.scalars[j as int],
                forall |j: int|
                    i <= j < self.scalars.len()
                        ==> self.scalars[j] == old(self).scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            self.scalars[i] = self.scalars[i] ^ rhs.scalars[i];
            i += 1;
        }
    }

    /// Origin Rust (:160-170, `AddRoundKeyAssign<&VoleCommitsRef>
    /// for VoleCommits`).
    pub fn add_round_key_assign_ref(self: &mut Self, rhs: &VoleCommitsRef)
        requires
            self.scalars.len() == rhs.scalars.len(),
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            forall |j: int|
                0 <= j < final(self).scalars.len()
                    ==> final(self).scalars[j]
                        == old(self).scalars[j as int]
                            ^ rhs.scalars[j as int],
            *final(self).delta == *old(self).delta,
    {
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.scalars.len(),
                forall |j: int|
                    0 <= j < i
                        ==> self.scalars[j]
                            == old(self).scalars[j as int] ^ rhs.scalars[j as int],
                forall |j: int|
                    i <= j < self.scalars.len()
                        ==> self.scalars[j] == old(self).scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            self.scalars[i] = self.scalars[i] ^ rhs.scalars[i];
            i += 1;
        }
    }

    /// Origin Rust (:172-182, `AddRoundKeyAssign<&Array<F, L>>
    /// for VoleCommits`): the known field-value row.
    pub fn add_round_key_assign_field(self: &mut Self, rhs: &[u128])
        requires
            self.scalars.len() == rhs.len(),
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            forall |j: int|
                0 <= j < final(self).scalars.len()
                    ==> final(self).scalars[j]
                        == old(self).scalars[j as int] ^ rhs[j as int],
            *final(self).delta == *old(self).delta,
    {
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.len(),
                forall |j: int|
                    0 <= j < i
                        ==> self.scalars[j]
                            == old(self).scalars[j as int] ^ rhs[j as int],
                forall |j: int|
                    i <= j < self.scalars.len()
                        ==> self.scalars[j] == old(self).scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            self.scalars[i] = self.scalars[i] ^ rhs[i];
            i += 1;
        }
    }
}

// ===========================================================================
// InverseShiftRows (upstream :184-244): two impls over the 8-slot
// window copy (the ::3-6 i formula + the ::7 window copy). Both
// bodies are value-identical; the twin re-erects each as an inherent
// face with its own Origin anchor (the FA11 inverse_shift_rows
// template over one plane).
// ===========================================================================

impl<'a> VoleCommitsRef<'a> {
    /// Origin Rust (:190-213, `InverseShiftRows<O> for
    /// VoleCommitsRef`).
    pub fn inverse_shift_rows(self: &Self, nst: usize) -> (o: VoleCommits<'a>)
        requires
            nst >= 4,
            self.scalars.len() == 32 * nst,
            32 * nst <= usize::MAX,
        ensures
            o.scalars.len() == 32 * nst,
            forall |r: int, c: int, t: int|
                #![trigger o.scalars[8 * (4 * c + r) + t]]
                0 <= r < 4 && 0 <= c < (nst as int) && 0 <= t < 8
                    ==> o.scalars[8 * (4 * c + r) + t]
                        == self.scalars[8 * isr_src_idx(nst as int, r, c) + t],
            o.delta == self.delta,
    {
        // zero allocation (the Box<Array::default> lowering)
        let mut o_scalars: Vec<u128> = Vec::new();
        let mut q: usize = 0;
        while q < 32 * nst
            invariant
                q <= 32 * nst,
                (32 * nst) <= usize::MAX,
                o_scalars.len() == q,
                forall |j: int| 0 <= j < q ==> o_scalars[j] == 0u128,
            decreases
                (32 * nst) - q,
        {
            o_scalars.push(0u128);
            q += 1;
        }
        let mut r: usize = 0;
        while r < 4
            invariant
                r <= 4,
                nst >= 4,
                (32 * nst) <= usize::MAX,
                self.scalars.len() == 32 * nst,
                o_scalars.len() == 32 * nst,
                // rows < r fully written
                forall |rr: int, c: int, t: int|
                    #![trigger o_scalars[8 * (4 * c + rr) + t]]
                    0 <= rr < r && 0 <= c < (nst as int) && 0 <= t < 8
                        ==> o_scalars[8 * (4 * c + rr) + t]
                            == self.scalars[8 * isr_src_idx(nst as int, rr, c) + t],
                // untouched rows still zero
                forall |rr: int, c: int, t: int|
                    #![trigger o_scalars[8 * (4 * c + rr) + t]]
                    r <= rr < 4 && 0 <= c < (nst as int) && 0 <= t < 8
                        ==> o_scalars[8 * (4 * c + rr) + t] == 0u128,
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
                    self.scalars.len() == 32 * nst,
                    o_scalars.len() == 32 * nst,
                    forall |rr: int, cc: int, t: int|
                        #![trigger o_scalars[8 * (4 * cc + rr) + t]]
                        ((0 <= rr < r) || (rr == r && 0 <= cc < c))
                            && 0 <= cc < (nst as int) && 0 <= t < 8
                            ==> o_scalars[8 * (4 * cc + rr) + t]
                                == self.scalars[8 * isr_src_idx(nst as int, rr, cc) + t],
                    forall |rr: int, cc: int, t: int|
                        #![trigger o_scalars[8 * (4 * cc + rr) + t]]
                        ((r < rr < 4) || (rr == r && c as int <= cc))
                            && 0 <= cc < (nst as int) && 0 <= t < 8
                            ==> o_scalars[8 * (4 * cc + rr) + t] == 0u128,
                decreases
                    nst - c,
            {
                // upstream ::3-6 lane spelling verbatim
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
                // upstream ::7 window copy (copy_from_slice lowers to
                // the 8 explicit index writes; FA11 precedent)
                o_scalars[8 * (4 * c + r)] = self.scalars[8 * i];
                o_scalars[8 * (4 * c + r) + 1] = self.scalars[8 * i + 1];
                o_scalars[8 * (4 * c + r) + 2] = self.scalars[8 * i + 2];
                o_scalars[8 * (4 * c + r) + 3] = self.scalars[8 * i + 3];
                o_scalars[8 * (4 * c + r) + 4] = self.scalars[8 * i + 4];
                o_scalars[8 * (4 * c + r) + 5] = self.scalars[8 * i + 5];
                o_scalars[8 * (4 * c + r) + 6] = self.scalars[8 * i + 6];
                o_scalars[8 * (4 * c + r) + 7] = self.scalars[8 * i + 7];
                c += 1;
            }
            r += 1;
        }
        VoleCommits { scalars: o_scalars, delta: self.delta }
    }
}

impl<'a> VoleCommits<'a> {
    /// Origin Rust (:221-244, `InverseShiftRows<O> for
    /// &VoleCommits`): the identical body over the owned container.
    pub fn inverse_shift_rows(self: &Self, nst: usize) -> (o: VoleCommits<'a>)
        requires
            nst >= 4,
            self.scalars.len() == 32 * nst,
            32 * nst <= usize::MAX,
        ensures
            o.scalars.len() == 32 * nst,
            forall |r: int, c: int, t: int|
                #![trigger o.scalars[8 * (4 * c + r) + t]]
                0 <= r < 4 && 0 <= c < (nst as int) && 0 <= t < 8
                    ==> o.scalars[8 * (4 * c + r) + t]
                        == self.scalars[8 * isr_src_idx(nst as int, r, c) + t],
            o.delta == self.delta,
    {
        // zero allocation (the Box<Array::default> lowering)
        let mut o_scalars: Vec<u128> = Vec::new();
        let mut q: usize = 0;
        while q < 32 * nst
            invariant
                q <= 32 * nst,
                (32 * nst) <= usize::MAX,
                o_scalars.len() == q,
                forall |j: int| 0 <= j < q ==> o_scalars[j] == 0u128,
            decreases
                (32 * nst) - q,
        {
            o_scalars.push(0u128);
            q += 1;
        }
        let mut r: usize = 0;
        while r < 4
            invariant
                r <= 4,
                nst >= 4,
                (32 * nst) <= usize::MAX,
                self.scalars.len() == 32 * nst,
                o_scalars.len() == 32 * nst,
                forall |rr: int, c: int, t: int|
                    #![trigger o_scalars[8 * (4 * c + rr) + t]]
                    0 <= rr < r && 0 <= c < (nst as int) && 0 <= t < 8
                        ==> o_scalars[8 * (4 * c + rr) + t]
                            == self.scalars[8 * isr_src_idx(nst as int, rr, c) + t],
                forall |rr: int, c: int, t: int|
                    #![trigger o_scalars[8 * (4 * c + rr) + t]]
                    r <= rr < 4 && 0 <= c < (nst as int) && 0 <= t < 8
                        ==> o_scalars[8 * (4 * c + rr) + t] == 0u128,
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
                    self.scalars.len() == 32 * nst,
                    o_scalars.len() == 32 * nst,
                    forall |rr: int, cc: int, t: int|
                        #![trigger o_scalars[8 * (4 * cc + rr) + t]]
                        ((0 <= rr < r) || (rr == r && 0 <= cc < c))
                            && 0 <= cc < (nst as int) && 0 <= t < 8
                            ==> o_scalars[8 * (4 * cc + rr) + t]
                                == self.scalars[8 * isr_src_idx(nst as int, rr, cc) + t],
                    forall |rr: int, cc: int, t: int|
                        #![trigger o_scalars[8 * (4 * cc + rr) + t]]
                        ((r < rr < 4) || (rr == r && c as int <= cc))
                            && 0 <= cc < (nst as int) && 0 <= t < 8
                            ==> o_scalars[8 * (4 * cc + rr) + t] == 0u128,
                decreases
                    nst - c,
            {
                // upstream ::3-6 lane spelling verbatim
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
                // upstream ::7 window copy
                o_scalars[8 * (4 * c + r)] = self.scalars[8 * i];
                o_scalars[8 * (4 * c + r) + 1] = self.scalars[8 * i + 1];
                o_scalars[8 * (4 * c + r) + 2] = self.scalars[8 * i + 2];
                o_scalars[8 * (4 * c + r) + 3] = self.scalars[8 * i + 3];
                o_scalars[8 * (4 * c + r) + 4] = self.scalars[8 * i + 4];
                o_scalars[8 * (4 * c + r) + 5] = self.scalars[8 * i + 5];
                o_scalars[8 * (4 * c + r) + 6] = self.scalars[8 * i + 6];
                o_scalars[8 * (4 * c + r) + 7] = self.scalars[8 * i + 7];
                c += 1;
            }
            r += 1;
        }
        VoleCommits { scalars: o_scalars, delta: self.delta }
    }
}

// ===========================================================================
// BytewiseMixColumns (upstream :246-294, `impl<'a, O>
// BytewiseMixColumns<O> for VoleCommitsRef<'a, OWFField<O>,
// O::NStBits>`). Origin Rust:
//     fn bytewise_mix_columns(&self) -> Self::Output {
//         let mut o: Box<Array<_, O::NStBits>> = Box::default();
//         for c in 0..O::NSt::USIZE {
//             for r in 0..4 {
//                 // ::4
//                 let a_key = &self.scalars[32 * c + 8 * r..32 * c + 8 * r + 8];
//                 // ::5
//                 let b_key = [ a_key[7], a_key[0] + a_key[7], a_key[1],
//                     a_key[2] + a_key[3]?? -- see below ];
//                 (verbatim roster: a_key[7], a_key[0] + a_key[7],
//                  a_key[1], a_key[2] + a_key[7], a_key[3] + a_key[7],
//                  a_key[4], a_key[5], a_key[6])
//                 // ::6..10
//                 for j in 0..2 {
//                     let off = 32 * c + 8 * ((4 + r - j) % 4);
//                     for (o, b) in zip(o[off..off + 8].iter_mut(), b_key.iter()) { *o += b; } }
//                 for j in 1..4 {
//                     let off = 32 * c + 8 * ((r + j) % 4);
//                     for (o, a) in zip(o[off..off + 8].iter_mut(), a_key.iter()) { *o += a; } } }
//         VoleCommits { scalars: o, delta: self.delta } }
// Contribution-lattice ruling (FA11 wave-2 pin, re-verified
// first-hand against this body): row rr writes the b roster into
// slots {rr, (rr+3)%4} and the a window into slots
// {(rr+1)%4, (rr+2)%4, (rr+3)%4}; the b roster == btag_slot's lane
// table with '^' at the char-2 field add. The value face is
// bmc_final_tag over the per-column windows -- the SAME contract
// machine the prover carries (crate::prover::aes), zero re-erect.
// The body keeps #[verifier::external_body] this batch: the r-loop
// partial-tie convergence is the FA11 D-FA11-1 open item (the 9
// open invariant rows diagnose to #FA11-8/10/11 + runtime-R folds);
// this face is the tag-plane-only instance of the same convergence
// surface -- the close-out kit transfers verbatim (notes ledger).
// ===========================================================================

impl<'a> VoleCommitsRef<'a> {
    /// Origin Rust (:252-294).
    #[verifier::external_body]
    pub fn bytewise_mix_columns(self: &Self, nst: usize) -> (o: VoleCommits<'a>)
        requires
            nst >= 4,
            self.scalars.len() == 32 * nst,
            32 * nst <= usize::MAX,
        ensures
            o.scalars.len() == 32 * nst,
            forall |cc: int, k: int, t: int|
                #![trigger o.scalars[8 * (4 * cc + k) + t]]
                0 <= cc < (nst as int) && 0 <= k < 4 && 0 <= t < 8
                    ==> o.scalars[8 * (4 * cc + k) + t]
                        == bmc_final_tag(
                            k, t,
                            trow_of(self.scalars@, cc, 0),
                            trow_of(self.scalars@, cc, 1),
                            trow_of(self.scalars@, cc, 2),
                            trow_of(self.scalars@, cc, 3),
                        ),
            o.delta == self.delta,
    {
        // zero allocation (the Box<Array::default> lowering)
        let mut o: Vec<u128> = Vec::new();
        let mut q: usize = 0;
        while q < 32 * nst
            invariant
                q <= 32 * nst,
                (32 * nst) <= usize::MAX,
                o.len() == q,
                forall |j: int| 0 <= j < q ==> o[j] == 0u128,
            decreases
                (32 * nst) - q,
        {
            o.push(0u128);
            q += 1;
        }
        let mut c: usize = 0;
        while c < nst
            invariant
                c <= nst,
                nst >= 4,
                (32 * nst) <= usize::MAX,
                self.scalars.len() == 32 * nst,
                o.len() == 32 * nst,
                // done columns: full lattice
                forall |cc: int, k: int, t: int|
                    #![trigger o[8 * (4 * cc + k) + t]]
                    0 <= cc < c && 0 <= k < 4 && 0 <= t < 8
                        ==> o[8 * (4 * cc + k) + t]
                            == bmc_final_tag(
                                k, t,
                                trow_of(self.scalars@, cc, 0),
                                trow_of(self.scalars@, cc, 1),
                                trow_of(self.scalars@, cc, 2),
                                trow_of(self.scalars@, cc, 3),
                            ),
                // untouched columns zero
                forall |cc: int, k: int, t: int|
                    #![trigger o[8 * (4 * cc + k) + t]]
                    c <= cc < (nst as int) && 0 <= k < 4 && 0 <= t < 8
                        ==> o[8 * (4 * cc + k) + t] == 0u128,
            decreases
                nst - c,
        {
            let mut r: usize = 0;
            while r < 4
                invariant
                    r <= 4,
                    nst >= 4,
                    (32 * nst) <= usize::MAX,
                    c < nst,
                    self.scalars.len() == 32 * nst,
                    o.len() == 32 * nst,
                    // partial-column progress: rows < r folded is
                    // bmc_partial_tag(k, t, r) at every lane of column c
                    forall |k: int, t: int|
                        #![trigger o[8 * (4 * c as int + k) + t]]
                        0 <= k < 4 && 0 <= t < 8
                            ==> o[8 * (4 * c as int + k) + t]
                                == bmc_partial_tag(
                                    k, t, r as int,
                                    trow_of(self.scalars@, c as int, 0),
                                    trow_of(self.scalars@, c as int, 1),
                                    trow_of(self.scalars@, c as int, 2),
                                    trow_of(self.scalars@, c as int, 3),
                                ),
                    forall |cc: int, k: int, t: int|
                        #![trigger o[8 * (4 * cc + k) + t]]
                        0 <= cc < c && 0 <= k < 4 && 0 <= t < 8
                            ==> o[8 * (4 * cc + k) + t]
                                == bmc_final_tag(
                                    k, t,
                                    trow_of(self.scalars@, cc, 0),
                                    trow_of(self.scalars@, cc, 1),
                                    trow_of(self.scalars@, cc, 2),
                                    trow_of(self.scalars@, cc, 3),
                                ),
                    forall |cc: int, k: int, t: int|
                        #![trigger o[8 * (4 * cc + k) + t]]
                        c <= cc < (nst as int) && 0 <= k < 4 && 0 <= t < 8
                            ==> o[8 * (4 * cc + k) + t] == 0u128,
                decreases
                    4 - r,
            {
                // upstream ::4 window
                let a_key: [u128; 8] = [
                    self.scalars[32 * c + 8 * r],
                    self.scalars[32 * c + 8 * r + 1],
                    self.scalars[32 * c + 8 * r + 2],
                    self.scalars[32 * c + 8 * r + 3],
                    self.scalars[32 * c + 8 * r + 4],
                    self.scalars[32 * c + 8 * r + 5],
                    self.scalars[32 * c + 8 * r + 6],
                    self.scalars[32 * c + 8 * r + 7],
                ];
                // upstream ::5 roster (verbatim; '+' is the char-2
                // field add)
                let b_key: [u128; 8] = [
                    a_key[7],
                    a_key[0] ^ a_key[7],
                    a_key[1],
                    a_key[2] ^ a_key[7],
                    a_key[3] ^ a_key[7],
                    a_key[4],
                    a_key[5],
                    a_key[6],
                ];
                // upstream ::6..10: b into slots {r, (r+3)%4}
                let mut j: usize = 0;
                while j < 2
                    invariant
                        j <= 2,
                    decreases
                        2 - j,
                {
                    let off: usize = 32 * c + 8 * ((4 + r - j) % 4);
                    let mut q8: usize = 0;
                    while q8 < 8
                        invariant
                            q8 <= 8,
                        decreases
                            8 - q8,
                    {
                        o[off + q8] = o[off + q8] ^ b_key[q8];
                        q8 += 1;
                    }
                    j += 1;
                }
                // upstream j in 1..4: a into slots {(r+1..r+3)%4}
                let mut j: usize = 1;
                while j < 4
                    invariant
                        1 <= j <= 4,
                    decreases
                        4 - j,
                {
                    let off: usize = 32 * c + 8 * ((r + j) % 4);
                    let mut q8: usize = 0;
                    while q8 < 8
                        invariant
                            q8 <= 8,
                        decreases
                            8 - q8,
                    {
                        o[off + q8] = o[off + q8] ^ a_key[q8];
                        q8 += 1;
                    }
                    j += 1;
                }
                r += 1;
            }
            c += 1;
        }
        VoleCommits { scalars: o, delta: self.delta }
    }
}

// ===========================================================================
// SBoxAffine (upstream :296-332, `impl<'a, O> SBoxAffine<O>
// for VoleCommits<'a, OWFField<O>, O::NStBits>`). Origin Rust:
//     fn s_box_affine(&self, sq: bool) -> Self::Output {
//         let sigmas = if sq { &OWFField::<O>::SIGMA_SQUARES }
//                      else { &OWFField::<O>::SIGMA };
//         let t = sq as usize;
//         let scalars = Box::new((0..O::NStBytes::USIZE).map(|i| {
//             let mut y_i = sigmas[8] * self.delta.square();
//             for (sigma_idx, sigma) in sigmas.iter().enumerate().take(8) {
//                 y_i += self.scalars[i * 8 + (sigma_idx + t) % 8] * sigma; }
//             y_i }).collect());
//         Self::Output { scalars, delta: self.delta } }
// The sigma products are full field multiplies (Mul<F>); the map
// lowers to the index loop; the inner 8-lane sigma chain is unrolled
// (constant chain, no upstream-visible data dependence on the loop
// bound; FA11 s_box_affine precedent). The `+` rows lower to limb
// xor; delta.square() is gf128_square (== gf128_hmul(d, d)).
// ===========================================================================

/// The per-lane sigma-row spec of the SBoxAffine output (the eight
/// window products plus the delta-squared constant term).
pub open spec fn sboxaff_lane_vc(
    scalars: Seq<u128>,
    i: int,
    t: int,
    delta: u128,
    sigmas: [u128; 9],
) -> u128 {
    gf128_mul_spec(sigmas[8], gf128_hmul(delta, delta))
        ^ gf128_mul_spec(scalars[8 * i + (0 + t) % 8], sigmas[0])
        ^ gf128_mul_spec(scalars[8 * i + (1 + t) % 8], sigmas[1])
        ^ gf128_mul_spec(scalars[8 * i + (2 + t) % 8], sigmas[2])
        ^ gf128_mul_spec(scalars[8 * i + (3 + t) % 8], sigmas[3])
        ^ gf128_mul_spec(scalars[8 * i + (4 + t) % 8], sigmas[4])
        ^ gf128_mul_spec(scalars[8 * i + (5 + t) % 8], sigmas[5])
        ^ gf128_mul_spec(scalars[8 * i + (6 + t) % 8], sigmas[6])
        ^ gf128_mul_spec(scalars[8 * i + (7 + t) % 8], sigmas[7])
}

impl<'a> VoleCommits<'a> {
    /// Origin Rust (:302-331).
    pub fn s_box_affine(self: &Self, sq: bool, nst_bytes: usize) -> (o: VoleCommits<'a>)
        requires
            self.scalars.len() == 8 * nst_bytes,
        ensures
            o.scalars.len() == nst_bytes,
            forall |i: int|
                0 <= i < o.scalars.len()
                    ==> o.scalars[i]
                        == sboxaff_lane_vc(
                            self.scalars@,
                            i,
                            if sq { 1 } else { 0 },
                            *self.delta,
                            if sq { GF128_SIGMA_SQUARES } else { GF128_SIGMA },
                        ),
            o.delta == self.delta,
    {
        // upstream ::1-2 pick (verbatim)
        let sigmas: [u128; 9] = if sq { GF128_SIGMA_SQUARES } else { GF128_SIGMA };
        let t: usize = if sq { 1 } else { 0 };
        let mut scalars: Vec<u128> = Vec::new();
        let mut i: usize = 0;
        while i < nst_bytes
            invariant
                i <= nst_bytes,
                self.scalars.len() == 8 * nst_bytes,
                sigmas == (if sq { GF128_SIGMA_SQUARES } else { GF128_SIGMA }),
                t == (if sq { 1usize } else { 0usize }),
                scalars.len() == i,
                forall |j: int|
                    0 <= j < i
                        ==> scalars[j]
                            == sboxaff_lane_vc(
                                self.scalars@,
                                j,
                                t as int,
                                *self.delta,
                                sigmas,
                            ),
            decreases
                nst_bytes - i,
        {
            // upstream ::9 constant term
            let mut y_i: u128 = gf128_mul(sigmas[8], gf128_square(*self.delta));
            // upstream ::9-11 sigma chain, 8 lanes unrolled
            y_i = y_i
                ^ gf128_mul(self.scalars[i * 8 + (0 + t) % 8], sigmas[0])
                ^ gf128_mul(self.scalars[i * 8 + (1 + t) % 8], sigmas[1]);
            y_i = y_i
                ^ gf128_mul(self.scalars[i * 8 + (2 + t) % 8], sigmas[2])
                ^ gf128_mul(self.scalars[i * 8 + (3 + t) % 8], sigmas[3]);
            y_i = y_i
                ^ gf128_mul(self.scalars[i * 8 + (4 + t) % 8], sigmas[4])
                ^ gf128_mul(self.scalars[i * 8 + (5 + t) % 8], sigmas[5]);
            y_i = y_i
                ^ gf128_mul(self.scalars[i * 8 + (6 + t) % 8], sigmas[6])
                ^ gf128_mul(self.scalars[i * 8 + (7 + t) % 8], sigmas[7]);
            scalars.push(y_i);
            i += 1;
        }
        VoleCommits { scalars, delta: self.delta }
    }
}

// ===========================================================================
// ShiftRows (upstream :334-355, `impl<F, L> ShiftRows for
// VoleCommits<F, L>`). Origin Rust:
//     fn shift_rows(&mut self) {
//         // TODO: Copy row by row instead of entire state
//         let mut tmp = self.scalars.clone();
//         let nst = L::USIZE / 4;
//         for r in 0..4 {
//             for c in 0..nst {
//                 let off = if (nst != 8) || (r <= 1) { 0 } else { 1 };
//                 mem::swap(&mut self.scalars[4 * c + r],
//                     &mut tmp[4 * ((c + r + off) % nst) + r]); } } }
// The upstream TODO line rides verbatim above. Deviation records
// (the FA11 ShiftRows decisions, same net): the clone lowers to the
// explicit copy loop (the to_vec family, #FA11-4); mem::swap lowers
// to the copy-assign (tmp never reads a lane it has written -- each
// source index j(c) = 4*((c+r+off)%nst)+r is injective over c); the
// value face is final[4c+r] == old[sr_src_idx] (the prover twin's
// first-hand swap-net analysis transfers verbatim).
// ===========================================================================

impl VoleCommits<'_> {
    /// Origin Rust (:339-354).
    pub fn shift_rows(self: &mut Self, nst: usize)
        requires
            self.scalars.len() == 4 * nst,
            nst > 0,
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            forall |r: int, c: int|
                #![trigger final(self).scalars[4 * c + r]]
                0 <= r < 4 && 0 <= c < (nst as int)
                    ==> final(self).scalars[4 * c + r]
                        == old(self).scalars[sr_src_idx(nst as int, r, c)],
            *final(self).delta == *old(self).delta,
    {
        // tmp == the entry copy (upstream self.scalars.clone())
        let mut tmp: Vec<u128> = Vec::new();
        let mut q: usize = 0;
        while q < self.scalars.len()
            invariant
                q <= self.scalars.len(),
                tmp.len() == q,
                forall |j: int| 0 <= j < q ==> tmp[j] == old(self).scalars[j as int],
            decreases
                self.scalars.len() - q,
        {
            tmp.push(self.scalars[q]);
            q += 1;
        }
        let mut r: usize = 0;
        while r < 4
            invariant
                r <= 4,
                nst > 0,
                4 * nst == self.scalars.len(),
                tmp.len() == self.scalars.len(),
                forall |k: int| 0 <= k < tmp.len() ==> tmp[k] == old(self).scalars[k as int],
                // rows < r re-arranged; rows >= r untouched
                forall |rr: int, c: int|
                    #![trigger self.scalars[4 * c + rr]]
                    0 <= rr < r && 0 <= c < (nst as int)
                        ==> self.scalars[4 * c + rr]
                            == old(self).scalars[sr_src_idx(nst as int, rr, c)],
                forall |rr: int, c: int|
                    #![trigger self.scalars[4 * c + rr]]
                    r <= rr < 4 && 0 <= c < (nst as int)
                        ==> self.scalars[4 * c + rr]
                            == old(self).scalars[(4 * c + rr) as int],
            decreases
                4 - r,
        {
            let mut c: usize = 0;
            while c < nst
                invariant
                    r < 4,
                    nst > 0,
                    c <= nst,
                    4 * nst == self.scalars.len(),
                    tmp.len() == self.scalars.len(),
                    forall |k: int| 0 <= k < tmp.len()
                        ==> tmp[k] == old(self).scalars[k as int],
                    forall |rr: int, cc: int|
                        #![trigger self.scalars[4 * cc + rr]]
                        0 <= rr < r && 0 <= cc < (nst as int)
                            ==> self.scalars[4 * cc + rr]
                                == old(self).scalars[sr_src_idx(nst as int, rr, cc)],
                    forall |rr: int, cc: int|
                        #![trigger self.scalars[4 * cc + rr]]
                        (r as int) < rr < 4 && 0 <= cc < (nst as int)
                            ==> self.scalars[4 * cc + rr]
                                == old(self).scalars[(4 * cc + rr) as int],
                    forall |cc: int|
                        #![trigger self.scalars[4 * cc + r as int]]
                        0 <= cc < c
                            ==> self.scalars[4 * cc + r as int]
                                == old(self).scalars[sr_src_idx(nst as int, r as int, cc)],
                    forall |cc: int|
                        #![trigger self.scalars[4 * cc + r as int]]
                        c as int <= cc < (nst as int)
                            ==> self.scalars[4 * cc + r as int]
                                == old(self).scalars[(4 * cc + r as int) as int],
                decreases
                    nst - c,
            {
                // upstream lane spelling (the off pick per iteration)
                let off: usize = if (nst != 8) || (r <= 1) { 0 } else { 1 };
                let m: usize = (c + r + off) % nst;
                let j: usize = 4 * m + r;
                assert(sr_src_idx(nst as int, r as int, c as int) == j as int);
                proof {
                    let mi = m as int;
                    let ri = r as int;
                    let ni = nst as int;
                    let oi = off as int;
                    assert(0 <= mi && mi < ni) by (nonlinear_arith)
                        requires
                            ni > 0,
                            mi == ((c as int + r as int + oi) % ni),
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
                self.scalars[4 * c + r] = tmp[j];
                c += 1;
            }
            r += 1;
        }
    }
}

// ===========================================================================
// InverseAffine (upstream :357-377, `impl<F, L> InverseAffine for
// VoleCommits<F, L>`). Origin Rust:
//     fn inverse_affine(&mut self) {
//         for scalars in self.scalars.as_chunks_mut::<8>().0 {
//             let xi_tags = *scalars;
//             for bit_i in 0..8 {
//                 // ::6
//                 scalars[bit_i] = xi_tags[(bit_i + 8 - 1) % 8]
//                     + xi_tags[(bit_i + 8 - 3) % 8]
//                     + xi_tags[(bit_i + 8 - 6) % 8];
//                 if bit_i == 0 || bit_i == 2 { scalars[bit_i] += self.delta; } } } }
// The 8-lane roster is iaf_tag's lane table (the prover twin's spec
// face; '^' at the char-2 field add, the second/third terms are the
// same table's (bit_i+5)%8/ (bit_i+2)%8 spelling); the window loop
// lowers to the 8-block index loop.
// ===========================================================================

impl VoleCommits<'_> {
    /// Origin Rust (:362-376).
    pub fn inverse_affine(self: &mut Self)
        requires
            self.scalars.len() % 8 == 0,
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            forall |w: int, b: int|
                #![trigger final(self).scalars[8 * w + b]]
                0 <= w < old(self).scalars.len() / 8 && 0 <= b < 8
                    ==> final(self).scalars[8 * w + b]
                        == (if b == 0 || b == 2 {
                            iaf_tag(old(self).scalars@.subrange(8 * w, 8 * w + 8), b)
                                ^ *old(self).delta
                        } else {
                            iaf_tag(old(self).scalars@.subrange(8 * w, 8 * w + 8), b)
                        }),
            *final(self).delta == *old(self).delta,
    {
        let n_windows: usize = self.scalars.len() / 8;
        let mut w: usize = 0;
        while w < n_windows
            invariant
                w <= n_windows,
                n_windows == self.scalars.len() / 8,
                self.scalars.len() == old(self).scalars.len(),
                self.scalars.len() % 8 == 0,
                forall |ww: int, b: int|
                    #![trigger self.scalars[8 * ww + b]]
                    0 <= ww < w && 0 <= b < 8
                        ==> self.scalars[8 * ww + b]
                            == (if b == 0 || b == 2 {
                                iaf_tag(old(self).scalars@.subrange(8 * ww, 8 * ww + 8), b)
                                    ^ *old(self).delta
                            } else {
                                iaf_tag(old(self).scalars@.subrange(8 * ww, 8 * ww + 8), b)
                            }),
                forall |ww: int, b: int|
                    #![trigger self.scalars[8 * ww + b]]
                    w <= ww < n_windows && 0 <= b < 8
                        ==> self.scalars[8 * ww + b]
                            == old(self).scalars[8 * ww + b],
            decreases
                n_windows - w,
        {
            // xi_tags = the window snapshot (upstream `*scalars`)
            let xi: [u128; 8] = [
                self.scalars[8 * w],
                self.scalars[8 * w + 1],
                self.scalars[8 * w + 2],
                self.scalars[8 * w + 3],
                self.scalars[8 * w + 4],
                self.scalars[8 * w + 5],
                self.scalars[8 * w + 6],
                self.scalars[8 * w + 7],
            ];
            // ::6 roster, 8 lanes (unrolled; FA11 record); the
            // bit_i == 0 / bit_i == 2 delta rows inline verbatim
            self.scalars[8 * w] = xi[7] ^ xi[5] ^ xi[2] ^ *self.delta;
            self.scalars[8 * w + 1] = xi[0] ^ xi[6] ^ xi[3];
            self.scalars[8 * w + 2] = xi[1] ^ xi[7] ^ xi[4] ^ *self.delta;
            self.scalars[8 * w + 3] = xi[2] ^ xi[0] ^ xi[5];
            self.scalars[8 * w + 4] = xi[3] ^ xi[1] ^ xi[6];
            self.scalars[8 * w + 5] = xi[4] ^ xi[2] ^ xi[7];
            self.scalars[8 * w + 6] = xi[5] ^ xi[3] ^ xi[0];
            self.scalars[8 * w + 7] = xi[6] ^ xi[4] ^ xi[1];
            // per-lane spec ties (the iaf_tag def fold + the Seq
            // subrange read at the concrete window index)
            assert(self.scalars[8 * w + 0]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 0)
                    ^ *self.delta);
            assert(self.scalars[8 * w + 1]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 1));
            assert(self.scalars[8 * w + 2]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 2)
                    ^ *self.delta);
            assert(self.scalars[8 * w + 3]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 3));
            assert(self.scalars[8 * w + 4]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 4));
            assert(self.scalars[8 * w + 5]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 5));
            assert(self.scalars[8 * w + 6]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 6));
            assert(self.scalars[8 * w + 7]
                == iaf_tag(old(self).scalars@.subrange(8 * w as int, 8 * w as int + 8), 7));
            w += 1;
        }
    }
}

// ===========================================================================
// MixColumns (upstream :379-410, `impl<O> MixColumns<O> for
// VoleCommits<'_, OWFField<O>, O::NStBytes>`). Origin Rust:
//     fn mix_columns(&mut self, sq: bool) {
//         let (v2, v3) = if sq { (&Self::BYTE_COMBINE_SQ_2, &..SQ_3) }
//                        else { (&Self::BYTE_COMBINE_2, &..COMBINE_3) };
//         for scalars in self.scalars.as_chunks_mut::<4>().0 {
//             let tmp = *scalars;
//             // ::7-10 rows (scalar 0..3) }
// The elementwise products are full field multiplies; the ::7-:10
// slot table is mc_slot_key's (prover twin spec face, reused); '+'
// is the limb xor; as_chunks_mut::<4> lowers to the column index
// loop.
// ===========================================================================

impl VoleCommits<'_> {
    /// Origin Rust (:383-409).
    pub fn mix_columns(self: &mut Self, sq: bool, nst_bytes: usize)
        requires
            nst_bytes % 4 == 0,
            nst_bytes > 0,
            self.scalars.len() == nst_bytes,
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            forall |c: int, k: int|
                #![trigger final(self).scalars[4 * c + k]]
                0 <= c < nst_bytes as int / 4 && 0 <= k < 4
                    ==> final(self).scalars[4 * c + k]
                        == mc_slot_key(
                            old(self).scalars[4 * c],
                            old(self).scalars[4 * c + 1],
                            old(self).scalars[4 * c + 2],
                            old(self).scalars[4 * c + 3],
                            k,
                            if sq { GF128_BYTE_COMBINE_SQ_2 } else { GF128_BYTE_COMBINE_2 },
                            if sq { GF128_BYTE_COMBINE_SQ_3 } else { GF128_BYTE_COMBINE_3 },
                        ),
            *final(self).delta == *old(self).delta,
    {
        // upstream v2/v3 pick (the ::1-2 rows)
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
                self.scalars.len() == nst_bytes,
                v2 == (if sq { GF128_BYTE_COMBINE_SQ_2 } else { GF128_BYTE_COMBINE_2 }),
                v3 == (if sq { GF128_BYTE_COMBINE_SQ_3 } else { GF128_BYTE_COMBINE_3 }),
                forall |cc: int, k: int|
                    #![trigger self.scalars[4 * cc + k]]
                    0 <= cc < c && 0 <= k < 4
                        ==> self.scalars[4 * cc + k]
                            == mc_slot_key(
                                old(self).scalars[4 * cc],
                                old(self).scalars[4 * cc + 1],
                                old(self).scalars[4 * cc + 2],
                                old(self).scalars[4 * cc + 3],
                                k, v2, v3,
                            ),
                forall |cc: int, k: int|
                    #![trigger self.scalars[4 * cc + k]]
                    c <= cc < nst as int && 0 <= k < 4
                        ==> self.scalars[4 * cc + k]
                            == old(self).scalars[4 * cc + k],
            decreases
                nst - c,
        {
            // entry-value ties (guard-to-old bridge, FA11 template)
            assert(self.scalars[4 * c + 0] == old(self).scalars[4 * c + 0]);
            assert(self.scalars[4 * c + 1] == old(self).scalars[4 * c + 1]);
            assert(self.scalars[4 * c + 2] == old(self).scalars[4 * c + 2]);
            assert(self.scalars[4 * c + 3] == old(self).scalars[4 * c + 3]);
            // tmp = the column snapshot (upstream `*scalars`)
            let t0: u128 = self.scalars[4 * c + 0];
            let t1: u128 = self.scalars[4 * c + 1];
            let t2: u128 = self.scalars[4 * c + 2];
            let t3: u128 = self.scalars[4 * c + 3];
            // ::7 scalars[0]
            let m0: u128 = gf128_mul(t0, v2) ^ gf128_mul(t1, v3) ^ t2 ^ t3;
            self.scalars[4 * c] = m0;
            // ::8 scalars[1]
            let m1: u128 = gf128_mul(t1, v2) ^ gf128_mul(t2, v3) ^ t0 ^ t3;
            self.scalars[4 * c + 1] = m1;
            // ::9 scalars[2]
            let m2: u128 = gf128_mul(t2, v2) ^ gf128_mul(t3, v3) ^ t0 ^ t1;
            self.scalars[4 * c + 2] = m2;
            // ::10 scalars[3]
            let m3: u128 = gf128_mul(t0, v3) ^ gf128_mul(t3, v2) ^ t1 ^ t2;
            self.scalars[4 * c + 3] = m3;
            // per-slot spec ties (the mul/add ensure chain folded once
            // per lane so the invariant step closes for Z3; the FA11
            // mix_columns template)
            assert(self.scalars[4 * c] == mc_slot_key(t0, t1, t2, t3, 0, v2, v3));
            assert(self.scalars[4 * c + 1] == mc_slot_key(t0, t1, t2, t3, 1, v2, v3));
            assert(self.scalars[4 * c + 2] == mc_slot_key(t0, t1, t2, t3, 2, v2, v3));
            assert(self.scalars[4 * c + 3] == mc_slot_key(t0, t1, t2, t3, 3, v2, v3));
            assert(c < nst);
            c += 1;
        }
    }
}

// ===========================================================================
// AddRoundKeyBytes (upstream :412-428, `impl<F, L>
// AddRoundKeyBytes<&Array<F, L>> for VoleCommits<F, L>`). Origin
// Rust:
//     fn add_round_key_bytes(&mut self, rhs: &Array<F, L>, sq: bool) {
//         if sq {
//             for (st, k) in zip(self.scalars.iter_mut(), rhs) { *st += k; }
//         } else {
//             for (st, k) in zip(self.scalars.iter_mut(), rhs) {
//                 *st += *k * self.delta; } } }
// The !sq branch is a full field multiply (k * delta); the sq
// branch is the plain field add.
// ===========================================================================

impl VoleCommits<'_> {
    /// Origin Rust (:417-427).
    pub fn add_round_key_bytes(self: &mut Self, rhs: &[u128], sq: bool)
        requires
            self.scalars.len() == rhs.len(),
        ensures
            final(self).scalars.len() == old(self).scalars.len(),
            sq ==> forall |j: int|
                0 <= j < final(self).scalars.len()
                    ==> final(self).scalars[j]
                        == old(self).scalars[j as int] ^ rhs[j as int],
            !sq ==> forall |j: int|
                0 <= j < final(self).scalars.len()
                    ==> final(self).scalars[j]
                        == old(self).scalars[j as int]
                            ^ gf128_mul_spec(rhs[j as int], *old(self).delta),
            *final(self).delta == *old(self).delta,
    {
        let mut i: usize = 0;
        while i < self.scalars.len()
            invariant
                i <= self.scalars.len(),
                self.scalars.len() == rhs.len(),
                sq ==> forall |j: int|
                    0 <= j < i
                        ==> self.scalars[j]
                            == old(self).scalars[j as int] ^ rhs[j as int],
                !sq ==> forall |j: int|
                    0 <= j < i
                        ==> self.scalars[j]
                            == old(self).scalars[j as int]
                                ^ gf128_mul_spec(rhs[j as int], *old(self).delta),
                forall |j: int|
                    (sq && i <= j < self.scalars.len())
                        || (!sq && i <= j < self.scalars.len())
                    ==> self.scalars[j] == old(self).scalars[j as int],
            decreases
                self.scalars.len() - i,
        {
            if sq {
                self.scalars[i] = self.scalars[i] ^ rhs[i];
            } else {
                self.scalars[i] = self.scalars[i] ^ gf128_mul(rhs[i], *self.delta);
            }
            i += 1;
        }
    }
}

} // verus!
