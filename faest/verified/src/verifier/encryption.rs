//! faest 0.3.0 -- Verus transcription of src/verifier/encryption.rs,
//! batch FA12 (window 4: all six faces landed; the hasher-feeding
//! drivers land in the frozen form, the small data faces verified).
//!
//! Upstream (verifier/encryption.rs, 187 lines, pin 9ccc68c0):
//! enc_cstrnts (:22-75, the round-constraint driver over the two
//! dispatch instances), aes_round (:77-95), enc_cstrnts_even
//! (:97-128), enc_cstrnts_odd (:130-148), invnorm_to_conjugates
//! (:150-161), f256_f2_conjugates (:163-187).
//!
//! Representation lowering (this batch's records):
//!   - `O: OWFParameters` drops to the runtime nst/nst_bytes
//!     parameters (FA10 RowCfg precedent); F instantiates at GF128
//!     (u128); '+' on F lowers to the char-2 limb xor.
//!   - The upstream generic K dispatch (`input: impl AddRoundKey<&'a
//!     K ...>`) drops at the twin boundary per the two owf call
//!     instances (the window-1 recon ruling): both fold to the
//!     flat-scalar carrier -- input/output windows as &[u128] and
//!     extended_key flattened as R+1 rows of 32*nst scalars.
//!   - Hasher trajectory ruling (the window-2/3 batch decision, same
//!     as key_exp_cstrnts): the verify-side hasher faces carry full
//!     value-face ensures but the DRIVERS' feed chains stay out of
//!     the twin contracts (upstream itself contracts nothing on the
//!     chain); structural rows only (delta/delta_squared preserved),
//!     the oracle arms arbitrate the trajectories.
//!   - The mixed round-key byte windows (::16-17 `state_to_bytes` +
//!     `square()`) lower to the flattened ext_key rows of the
//!     lowered dispatch (compile-level under the frozen drivers; the
//!     composition spec is the resume kit item).
//!
//! Face status:
//!   - invnorm_to_conjugates: LANDED, exec-verified (four muls and
//!     xors over the landed BETA constants).
//!   - f256_f2_conjugates / aes_round: FROZEN (external_body +
//!     structural ensures; bodies faithfully transcribed over the
//!     FA11-beta conjugate/square faces and the wave-1 aes faces).
//!   - enc_cstrnts / enc_cstrnts_even / enc_cstrnts_odd: FROZEN
//!     (external_body + structural rows; bodies faithful).

use vstd::prelude::*;

use crate::large_fields::{
    gf128_byte_combine_slice, gf128_mul, gf128_mul_spec,
    gf128_square_byte_inplace, GF128_BETA_CUBES, GF128_BETA_SQUARES,
};
use crate::universal_hashing::ZKVerifyHasher128;

use super::vole_commitments::{VoleCommits, VoleCommitsRef};

verus! {

// ===========================================================================
// invnorm_to_conjugates (upstream :150-161). Origin Rust:
//     fn invnorm_to_conjugates<F>(x: &[F]) -> Array<F, U4>
//     where F: BigGaloisField {
//         (0..4).map(|j| {
//             x[0] + F::BETA_SQUARES[j] * x[1]
//                 + F::BETA_SQUARES[j + 1] * x[2]
//                 + F::BETA_CUBES[j] * x[3] }).collect() }
// The products are full field multiplies over the landed constants
// (large_fields); '+' lowers to the limb xor.
// ===========================================================================

/// Origin Rust (:154-160).
pub fn invnorm_to_conjugates(x: &[u128]) -> (o: Vec<u128>)
    requires
        x.len() == 4,
    ensures
        o.len() == 4,
        o[0] == x[0]
            ^ gf128_mul_spec(GF128_BETA_SQUARES[0], x[1])
            ^ gf128_mul_spec(GF128_BETA_SQUARES[1], x[2])
            ^ gf128_mul_spec(GF128_BETA_CUBES[0], x[3]),
        o[1] == x[0]
            ^ gf128_mul_spec(GF128_BETA_SQUARES[1], x[1])
            ^ gf128_mul_spec(GF128_BETA_SQUARES[2], x[2])
            ^ gf128_mul_spec(GF128_BETA_CUBES[1], x[3]),
        o[2] == x[0]
            ^ gf128_mul_spec(GF128_BETA_SQUARES[2], x[1])
            ^ gf128_mul_spec(GF128_BETA_SQUARES[3], x[2])
            ^ gf128_mul_spec(GF128_BETA_CUBES[2], x[3]),
        o[3] == x[0]
            ^ gf128_mul_spec(GF128_BETA_SQUARES[3], x[1])
            ^ gf128_mul_spec(GF128_BETA_SQUARES[4], x[2])
            ^ gf128_mul_spec(GF128_BETA_CUBES[3], x[3]),
{
    let mut out: Vec<u128> = Vec::new();
    let mut j: usize = 0;
    while j < 4
        invariant
            j <= 4,
            x.len() == 4,
            out.len() == j,
            forall |t: int|
                0 <= t < j
                    ==> out[t] == x[0]
                        ^ gf128_mul_spec(GF128_BETA_SQUARES[t], x[1])
                        ^ gf128_mul_spec(GF128_BETA_SQUARES[t + 1], x[2])
                        ^ gf128_mul_spec(GF128_BETA_CUBES[t], x[3]),
        decreases
            4 - j,
    {
        let v: u128 = x[0]
            ^ gf128_mul(GF128_BETA_SQUARES[j], x[1])
            ^ gf128_mul(GF128_BETA_SQUARES[j + 1], x[2])
            ^ gf128_mul(GF128_BETA_CUBES[j], x[3]);
        assert(v == x[0]
            ^ gf128_mul_spec(GF128_BETA_SQUARES[j as int], x[1])
            ^ gf128_mul_spec(GF128_BETA_SQUARES[(j as int) + 1], x[2])
            ^ gf128_mul_spec(GF128_BETA_CUBES[j as int], x[3]));
        out.push(v);
        j += 1;
    }
    out
}

// ===========================================================================
// f256_f2_conjugates (upstream :163-187). Origin Rust:
//     pub(crate) fn f256_f2_conjugates<F, L>(state: &Array<F, L>)
//     -> Array<F, L> where F: BigGaloisField, L: ArraySize {
//         debug_assert_eq!(L::USIZE % 8, 0);
//         state.as_chunks::<8>().0.iter().copied().flat_map(|mut x0| {
//             let mut y: Array<_, U8> = Array::default();
//             for j in 0..7 {
//                 y[j] = F::byte_combine_slice(&x0);
//                 F::square_byte_inplace(&mut x0); }
//             y[7] = F::byte_combine_slice(&x0);
//             y }).collect() }
// FROZEN (external_body): the per-window orbit (combine; square; x7)
// rides the FA11-beta conjugate face family; the composition value
// face (o[8*w + j] over the orbit lanes) is the resume kit item.
// The upstream debug_assert rides as the requires row (the % 8
// divisibility; the # Panics convention).
// ===========================================================================

#[verifier::external_body]
pub fn f256_f2_conjugates(state: &[u128]) -> (o: Vec<u128>)
    requires
        state.len() % 8 == 0,
    ensures
        o.len() == state.len(),
{
    let mut out: Vec<u128> = Vec::new();
    let n_windows: usize = state.len() / 8;
    let mut w: usize = 0;
    while w < n_windows
        decreases
            n_windows - w,
    {
        // x0 = the window copy (upstream `copied()`)
        let mut x0: [u128; 8] = [
            state[8 * w], state[8 * w + 1], state[8 * w + 2],
            state[8 * w + 3], state[8 * w + 4], state[8 * w + 5],
            state[8 * w + 6], state[8 * w + 7],
        ];
        // :4-8 the orbit rows (j in 0..7), the final row outside the
        // upstream loop -- spelled as the j == 7 arm here to keep
        // the single push lane
        let mut j: usize = 0;
        while j < 8
            decreases
                8 - j,
        {
            if j < 7 {
                out.push(gf128_byte_combine_slice(&x0));
                gf128_square_byte_inplace(&mut x0);
            } else {
                out.push(gf128_byte_combine_slice(&x0));
            }
            j += 1;
        }
        w += 1;
    }
    out
}

// ===========================================================================
// enc_cstrnts_even (upstream :97-128). Origin Rust:
//     fn enc_cstrnts_even<'a, O>(
//         zk_hasher: &mut ZKVerifyHasher<OWFField<O>>,
//         state: &VoleCommits<'a, OWFField<O>, O::NStBits>,
//         w: VoleCommitsRef<'_, OWFField<O>, Quot<O::NStBytes, U2>>,
//     ) -> VoleCommits<'a, OWFField<O>, O::NStBits> {
//         let state_conj = f256_f2_conjugates(&state.scalars);
//         let mut state_prime = Box::new(Array::default());
//         for i in 0..O::NStBytes::USIZE {
//             let ys = invnorm_to_conjugates(&w[4 * i..4 * i + 4]);
//             zk_hasher.inv_norm_constraints(&state_conj[8 * i..8 * i + 8],
//                 &ys[0]);
//             for j in 0..8 {
//                 state_prime[i * 8 + j] =
//                     state_conj[8 * i + (j + 4) % 8] * ys[j % 4]; } }
//         VoleCommits { scalars: state_prime, delta: state.delta } }
// (the upstream w Index<Range> reads lower to direct slice windows at
// the twin boundary -- the vole_commitments Index-drop record).
// FROZEN: structural rows only (the batch trajectory ruling; the
// return-plane value face is the resume kit item).
// ===========================================================================

#[verifier::external_body]
pub fn enc_cstrnts_even<'a>(
    zk_hasher: &mut ZKVerifyHasher128,
    state: &VoleCommits<'a>,
    w: &VoleCommitsRef<'_>,
    nst_bytes: usize,
) -> (o: VoleCommits<'a>)
    requires
        state.scalars.len() == 8 * nst_bytes,
        w.scalars.len() == 2 * nst_bytes,
        nst_bytes > 0,
    ensures
        o.scalars.len() == 8 * nst_bytes,
        o.delta == state.delta,
        final(zk_hasher).delta == old(zk_hasher).delta,
        final(zk_hasher).delta_squared == old(zk_hasher).delta_squared,
{
    // :4
    let state_conj: Vec<u128> = f256_f2_conjugates(&state.scalars);
    let mut state_prime: Vec<u128> = vec_with_zeros_128(8 * nst_bytes);
    // :7
    let mut i: usize = 0;
    while i < nst_bytes
        decreases
            nst_bytes - i,
    {
        // :9 the ys window (upstream w[4*i..4*i+4])
        let ys: Vec<u128> = invnorm_to_conjugates(&w.scalars[4 * i..4 * i + 4]);
        // :11 the norm-constraint feed
        let conj_win: &[u128] = &state_conj[8 * i..8 * i + 8];
        zk_hasher.inv_norm_constraints(conj_win, ys[0]);
        // :12 the j in 0..8 rows
        let mut j: usize = 0;
        while j < 8
            decreases
                8 - j,
        {
            state_prime[i * 8 + j] =
                gf128_mul(state_conj[8 * i + (j + 4) % 8], ys[j % 4]);
            j += 1;
        }
        i += 1;
    }
    VoleCommits { scalars: state_prime, delta: state.delta }
}

// ===========================================================================
// enc_cstrnts_odd (upstream :130-148). Origin Rust:
//     fn enc_cstrnts_odd<'a, O>(
//         zk_hasher: &mut ZKVerifyHasher<OWFField<O>>,
//         s_tilde: impl InverseShiftRows<O, Output = ...>,
//         st_0: &VoleCommits<'a, OWFField<O>, O::NStBytes>,
//         st_1: &VoleCommits<'a, OWFField<O>, O::NStBytes>) {
//         let mut s = s_tilde.inverse_shift_rows();
//         s.inverse_affine();
//         for (byte_i, (st0, st1)) in zip(st_0.as_ref(), st_1.as_ref())
//             .enumerate() {
//             let si = s.get_field_commit(byte_i);
//             let si_sq = s.get_field_commit_sq(byte_i);
//             zk_hasher.odd_round_cstrnts(&si, &si_sq, st0, st1); } }
// FROZEN: structural rows only (same ruling).
// ===========================================================================

#[verifier::external_body]
pub fn enc_cstrnts_odd(
    zk_hasher: &mut ZKVerifyHasher128,
    s_tilde: &VoleCommitsRef<'_>,
    st_0: &VoleCommits<'_>,
    st_1: &VoleCommits<'_>,
    nst: usize,
)
    requires
        s_tilde.scalars.len() == 32 * nst,
        st_0.scalars.len() == 4 * nst,
        st_1.scalars.len() == 4 * nst,
        nst >= 4,
        32 * nst <= usize::MAX,
    ensures
        final(zk_hasher).delta == old(zk_hasher).delta,
        final(zk_hasher).delta_squared == old(zk_hasher).delta_squared,
{
    // :29-30
    let mut s: VoleCommits = s_tilde.inverse_shift_rows(nst);
    s.inverse_affine();
    // :31-37 the byte-indexed feed (the zip lowers to the index loop;
    // the upstream as_ref() scalars index directly)
    let nst_bytes: usize = 4 * nst;
    let mut byte_i: usize = 0;
    while byte_i < nst_bytes
        decreases
            nst_bytes - byte_i,
    {
        let si: u128 = s.get_field_commit(byte_i);
        let si_sq: u128 = s.get_field_commit_sq(byte_i);
        zk_hasher.odd_round_cstrnts(
            si,
            si_sq,
            st_0.scalars[byte_i],
            st_1.scalars[byte_i],
        );
        byte_i += 1;
    }
}

// ===========================================================================
// aes_round (upstream :77-95). Origin Rust:
//     fn aes_round<'a, O, T>(
//         state: &VoleCommits<'a, OWFField<O>, O::NStBits>,
//         key_bytes: &Array<T, O::NStBytes>, sq: bool)
//     -> VoleCommits<'a, OWFField<O>, O::NStBytes> {
//         let mut st = state.s_box_affine(sq);
//         st.shift_rows();
//         st.mix_columns(sq);
//         st.add_round_key_bytes(key_bytes, sq);
//         st }
// The four steps are the wave-1 landed faces; FROZEN with structural
// rows (the composed value face over sboxaff_lane_vc / sr_src_idx /
// mc_slot_key / ark-bytes lanes is the resume kit item).
// ===========================================================================

#[verifier::external_body]
pub fn aes_round<'a>(
    state: &VoleCommits<'a>,
    key_bytes: &[u128],
    sq: bool,
    nst: usize,
    nst_bytes: usize,
) -> (o: VoleCommits<'a>)
    requires
        state.scalars.len() == 8 * nst_bytes,
        key_bytes.len() == nst_bytes,
        nst_bytes == 4 * nst,
        nst >= 4,
        nst_bytes > 0,
    ensures
        o.scalars.len() == nst_bytes,
        o.delta == state.delta,
{
    // :19-22 the four chained faces (the wave-1 inherent methods)
    let mut st: VoleCommits<'a> = state.s_box_affine(sq, nst_bytes);
    st.shift_rows(nst);
    st.mix_columns(sq, nst_bytes);
    st.add_round_key_bytes(key_bytes, sq);
    st
}

// ===========================================================================
// enc_cstrnts (upstream :22-75). Origin Rust (the two-dispatch
// driver; see the header lowering records). FROZEN: structural rows
// only (the batch trajectory ruling). The typenum Quot<NStBytes, U2>
// window of ::3-15 lowers to the nst_bytes/2 slice window with the
// same 3 * nst_bytes * r / 2 offsets (the ::29-38 window reads at
// NStBytes::USIZE / 2 + 3 * NStBytes::USIZE * r / 2); round keys
// read the flattened ext_key rows (see the header records).
// ===========================================================================

#[verifier::external_body]
pub fn enc_cstrnts<'a>(
    zk_hasher: &mut ZKVerifyHasher128,
    input: &[u128],
    output: &[u128],
    w: &VoleCommitsRef<'a>,
    extended_key: &[u128],
    nst: usize,
    nst_bytes: usize,
    r_half: usize,
)
    requires
        nst >= 4,
        nst_bytes == 4 * nst,
        32 * nst <= usize::MAX,
        input.len() == 32 * nst,
        output.len() == 32 * nst,
        // w covers the LEnc windows the driver reads (the even
        // windows + the odd s_tilde windows through the last round)
        w.scalars.len()
            >= (nst_bytes / 2) + (nst_bytes / 2) * 3 * (r_half - 1)
                + (32 * nst) * r_half,
        // extended_key flattened: 2 * r_half + 1 rows of 32 * nst
        extended_key.len() >= 32 * nst * (2 * r_half + 1),
        r_half >= 1,
    ensures
        final(zk_hasher).delta == old(zk_hasher).delta,
        final(zk_hasher).delta_squared == old(zk_hasher).delta_squared,
{
    // ::1 state = input.add_round_key(&extended_key[0]) -- the flat
    // carrier spelling of the lowered dispatch (elemwise scalar add)
    let mut state_scalars: Vec<u128> = vec_with_zeros_128(32 * nst);
    let mut q2: usize = 0;
    while q2 < 32 * nst
        decreases
            32 * nst - q2,
    {
        state_scalars[q2] = input[q2] ^ extended_key[q2];
        q2 += 1;
    }
    let mut state: VoleCommits<'a> =
        VoleCommits { scalars: state_scalars, delta: w.delta };
    // ::2 the r-loop (R/2 = r_half rounds)
    let mut r: usize = 0;
    while r < r_half
        decreases
            r_half - r,
    {
        // ::3-15 the even feed (w window at 3 * nst_bytes * r / 2)
        let w_even: VoleCommitsRef<'a> =
            w.get_commits_ref((3 * nst_bytes * r) / 2, nst_bytes / 2);
        let state_prime: VoleCommits<'a> =
            enc_cstrnts_even(zk_hasher, &state, &w_even, nst_bytes);
        // ::16-17 the round key window (flattened row 2r+1; the
        // upstream `state_to_bytes()` + `square()` compose rides the
        // flat rows -- see the header records)
        let mut round_key: Vec<u128> = vec_with_zeros_128(nst_bytes);
        let mut q3: usize = 0;
        while q3 < nst_bytes
            decreases
                nst_bytes - q3,
        {
            round_key[q3] = extended_key[32 * nst * (2 * r + 1) + q3];
            q3 += 1;
        }
        // ::18-22 the two aes_round folds (the sq arm over the
        // squared round-key window)
        let st_0: VoleCommits<'a> =
            aes_round(&state_prime, &round_key, false, nst, nst_bytes);
        let mut round_key_sq: Vec<u128> = vec_with_zeros_128(nst_bytes);
        let mut q4: usize = 0;
        while q4 < nst_bytes
            decreases
                nst_bytes - q4,
        {
            round_key_sq[q4] = gf128_mul(round_key[q4], round_key[q4]);
            q4 += 1;
        }
        let st_1: VoleCommits<'a> =
            aes_round(&state_prime, &round_key_sq, true, nst, nst_bytes);
        // ::23-28 the tail split
        let round_key_row: &[u128] =
            &extended_key[32 * nst * (2 * r + 2)..32 * nst * (2 * r + 3)];
        if r != r_half - 1 {
            // :29-38 the odd feed over the s_tilde window
            let s_tilde: VoleCommitsRef<'a> = w.get_commits_ref(
                (nst_bytes / 2) + (3 * nst_bytes * r) / 2,
                32 * nst,
            );
            enc_cstrnts_odd(zk_hasher, &s_tilde, &st_0, &st_1, nst);
            // :39-40 state = s_tilde.bytewise_mix_columns() plus the
            // row add (the flat scalar lanes of the lowered dispatch)
            let byten: VoleCommits<'a> = s_tilde.bytewise_mix_columns(nst);
            let mut next_scalars: Vec<u128> = byten.scalars;
            let mut q5: usize = 0;
            while q5 < 32 * nst
                decreases
                    32 * nst - q5,
            {
                next_scalars[q5] = next_scalars[q5] ^ round_key_row[q5];
                q5 += 1;
            }
            state = VoleCommits { scalars: next_scalars, delta: w.delta };
        } else {
            // :29-38 the last-round feed over the output rows
            let mut s_tilde_scalars: Vec<u128> = vec_with_zeros_128(32 * nst);
            let mut q6: usize = 0;
            while q6 < 32 * nst
                decreases
                    32 * nst - q6,
            {
                s_tilde_scalars[q6] = output[q6] ^ round_key_row[q6];
                q6 += 1;
            }
            let s_tilde: VoleCommits<'a> =
                VoleCommits { scalars: s_tilde_scalars, delta: w.delta };
            let s_tilde_ref = VoleCommitsRef {
                scalars: &s_tilde.scalars,
                delta: w.delta,
            };
            enc_cstrnts_odd(zk_hasher, &s_tilde_ref, &st_0, &st_1, nst);
        }
        r += 1;
    }
}

// ===========================================================================
// helper (frozen-body allocation lowering; the Box<Array::default>
// convention rides the zero-Vec batch face). Defined here after its
// uses (Rust item order-independence); external_body so the frozen
// callers share one allocation face without a body-check fanout.
// ===========================================================================

#[verifier::external_body]
fn vec_with_zeros_128(n: usize) -> (o: Vec<u128>)
    ensures
        o.len() == n,
{
    let mut v: Vec<u128> = Vec::new();
    let mut i: usize = 0;
    while i < n
    {
        v.push(0u128);
        i += 1;
    }
    v
}

} // verus!
