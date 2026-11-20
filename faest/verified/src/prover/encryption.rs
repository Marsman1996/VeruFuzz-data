//! faest 0.3.0 -- Verus transcription of src/prover/encryption.rs,
//! batch FA11 (faces landed at the FA12 window-6 close, in the
//! frozen form; the records live in out/kverus-run/FA12/notes.md).
//!
//! Upstream (prover/encryption.rs, 193 lines, pin 9ccc68c0):
//! enc_cstrnts (:23-79, the round-constraint driver over two
//! generic dispatch instances), enc_cstrnts_even (:81-117),
//! enc_cstrnts_odd (:119-140), aes_round (:142-159),
//! invnorm_to_conjugates (:161-179), f256_f2_conjugates
//! (:181-192).
//!
//! Representation lowering (this batch's records):
//!   - `O: OWFParameters` drops to the runtime nst/nst_bytes rows
//!     (FA10 RowCfg precedent); F instantiates at GF128 (u128);
//!     '+' on F is the char-2 limb xor.
//!   - The K/S generic dispatch drops at the twin boundary per the
//!     two owf call instances (first-hand window-6 read of
//!     prover/owf_constraints.rs): TWO driver entries -- the EM
//!     instance (K = Array<u8, NStBytes> public rows: input/output
//!     = ByteCommitsRef, round keys via the landed state_to_bytes_
//!     public folds, the sq variant via the per-element field
//!     square = gf128_square, the Array<S>::Square blanket) and
//!     the non-EM instance (K = ByteCommitsRef hidden rows: input =
//!     the public u8 state plane, round keys via the landed
//!     state_to_bytes_ref fold) -- both sharing even / odd /
//!     aes_round. The per-element Square of the state_to_bytes
//!     output rows composes the landed gf128_square faces.
//!   - The two-limb commitment carriers are the FA6-pre
//!     FieldCommitDegOne/Two/Three twin faces (all Mul / Add rows
//!     consumed are landed inherent methods; the single upstream
//!     `D3 + &D1` Add row -- field_commitment.rs :400-409 -- has no
//!     landed twin face and spells inline inside the frozen even
//!     body: key ^= rhs.key, tag[2] ^= rhs.tag[0], deviation
//!     recorded).
//!   - The FA6p-1 gate rides the route-(b) data-contract form (the
//!     batch ruling): the ZKProofHasher128::update /
//!     odd_round_cstrnts debug-assert requires rows re-erect as
//!     per-feed claim rows spelled over the landed spec primitives
//!     (iaf8 / isr_src_idx / gf128_byte_combine_bits_spec /
//!     gf8_sq_bits_u8 / gf128_mul_spec) -- the kec_claim template
//!     family; caller obligations, harness KAT arms discharge.
//!
//! Face status (window-6): all six faces FROZEN (external_body +
//! contracts below; bodies faithful compilations over the landed
//! faces); invnorm_to_conjugates carries the full value-face
//! ensures.

use vstd::prelude::*;

use crate::large_fields::{
    gf128_byte_combine_bits_spec, gf128_mul, gf128_mul_spec, gf128_square, gf8_sq_bits_u8,
    GF128_BETA_CUBES, GF128_BETA_SQUARES,
};
use crate::prover::aes::{
    add_round_key_bytes, bytewise_mix_columns, iaf8, isr_src_idx, mix_columns,
    s_box_affine, shift_rows_d2, state_to_bytes_public,
};
use crate::prover::byte_commitments::{
    ByteCommitment, ByteCommits, ByteCommitsRef,
};
use crate::prover::field_commitment::{
    FieldCommitDegOne, FieldCommitDegThree, FieldCommitDegTwo,
};
use crate::universal_hashing::ZKProofHasher128;

verus! {

// ===========================================================================
// The (b)-form claim spec primitives (composed over the landed spec
// faces; route (b), the kec_claim template family).
// ===========================================================================

/// The GF8 squaring orbit, j steps (the conjugate key plane of the
/// f256 face; the key square face value aligns with square_inplace
/// per the FA11-beta orbit lemma records).
pub open spec fn pe_sqj(x: u8, j: int) -> u8
    decreases if j <= 0 { 0 } else { j }
{
    if j <= 0 { x } else { gf8_sq_bits_u8(pe_sqj(x, j - 1)) }
}

/// The 4-bit norm nibble of the even loop (upstream :98:
/// `(w.keys[i / 2] >> ((i % 2) * 4)) & 0xf`).
pub open spec fn pe_norm(wk: Seq<u8>, i: int) -> u8 {
    ((wk[i / 2] >> (((i % 2) * 4) as u8)) & 0xf) as u8
}

/// The ys key plane (upstream :166-170: from_bit + the BETA selects
/// over the norm nibble's bits; the F*u8 rows are bit-0 selects).
pub open spec fn pe_ys_key(norm: u8, j: int) -> u128 {
    (if (norm & 1) == 1 { 1u128 } else { 0u128 })
        ^ (if ((norm >> 1) & 1) == 1 { GF128_BETA_SQUARES[j] } else { 0u128 })
        ^ (if ((norm >> 2) & 1) == 1 { GF128_BETA_SQUARES[j + 1] } else { 0u128 })
        ^ (if ((norm >> 3) & 1) == 1 { GF128_BETA_CUBES[j] } else { 0u128 })
}

/// The cnstr key plane of the even feed (upstream :106-107 -- the
/// "save 1 mul" cnstr composition over the conjugate key orbit of
/// the state byte and the ys row).
pub open spec fn pe_cstr_key(state_byte: u8, norm: u8) -> u128 {
    gf128_mul_spec(
        gf128_mul_spec(
            pe_ys_key(norm, 0),
            gf128_byte_combine_bits_spec(pe_sqj(state_byte, 4)),
        ),
        gf128_byte_combine_bits_spec(pe_sqj(state_byte, 1)),
    ) ^ gf128_byte_combine_bits_spec(pe_sqj(state_byte, 0))
}

// ===========================================================================
// invnorm_to_conjugates (upstream :161-179). Origin Rust:
//     fn invnorm_to_conjugates<F>(x_val: u8, x_tag: &[F])
//     -> Array<FieldCommitDegOne<F>, U4> {
//         (0..4).map(|j| {
//             let key = F::from_bit(x_val & 1)
//                 + F::BETA_SQUARES[j] * ((x_val >> 1) & 1)
//                 + F::BETA_SQUARES[j + 1] * ((x_val >> 2) & 1)
//                 + F::BETA_CUBES[j] * ((x_val >> 3) & 1);
//             let tag = x_tag[0]
//                 + F::BETA_SQUARES[j] * x_tag[1]
//                 + F::BETA_SQUARES[j + 1] * x_tag[2]
//                 + F::BETA_CUBES[j] * x_tag[3];
//             FieldCommitDegOne::new(key, tag) }).collect() }
// ===========================================================================

/// Origin Rust (:166-178); FROZEN with the full value-face ensures.
#[verifier::external_body]
pub fn invnorm_to_conjugates(x_val: u8, x_tag: &[u128]) -> (o: Vec<FieldCommitDegOne>)
    requires
        x_tag.len() == 4,
    ensures
        o.len() == 4,
        forall |j: int|
            0 <= j < 4
                ==> o[j].key == pe_ys_key(x_val, j)
                    && o[j].tag[0] == x_tag[0]
                        ^ gf128_mul_spec(GF128_BETA_SQUARES[j], x_tag[1])
                        ^ gf128_mul_spec(GF128_BETA_SQUARES[j + 1], x_tag[2])
                        ^ gf128_mul_spec(GF128_BETA_CUBES[j], x_tag[3]),
{
    let mut out: Vec<FieldCommitDegOne> = Vec::new();
    let mut j: usize = 0;
    while j < 4
    {
        let key: u128 = (if (x_val & 1) == 1 { 1u128 } else { 0u128 })
            ^ (if ((x_val >> 1) & 1) == 1 {
                GF128_BETA_SQUARES[j]
            } else {
                0u128
            })
            ^ (if ((x_val >> 2) & 1) == 1 {
                GF128_BETA_SQUARES[j + 1]
            } else {
                0u128
            })
            ^ (if ((x_val >> 3) & 1) == 1 {
                GF128_BETA_CUBES[j]
            } else {
                0u128
            });
        let tag: u128 = x_tag[0]
            ^ gf128_mul(GF128_BETA_SQUARES[j], x_tag[1])
            ^ gf128_mul(GF128_BETA_SQUARES[j + 1], x_tag[2])
            ^ gf128_mul(GF128_BETA_CUBES[j], x_tag[3]);
        out.push(FieldCommitDegOne::new(key, tag));
        j += 1;
    }
    out
}

// ===========================================================================
// f256_f2_conjugates (upstream :181-192). Origin Rust:
//     pub(crate) fn f256_f2_conjugates<F>(state_conj: &mut Array<.., U8>,
//         commit: &mut ByteCommitment<F>) {
//         for st_conj_i in state_conj.iter_mut() {
//             *st_conj_i = commit.combine();
//             commit.square_inplace(); } }
// FROZEN: bodies over the landed combine/square_inplace faces (the
// lane-by-lane value composition rides those faces' ensures -- the
// resume kit item; the even consume reads the key lanes only).
// ===========================================================================

/// Origin Rust (:186-190).
#[verifier::external_body]
pub fn f256_f2_conjugates(state_conj: &mut [FieldCommitDegOne], commit: &mut ByteCommitment)
    requires
        state_conj.len() == 8,
{
    let mut i: usize = 0;
    while i < 8
    {
        state_conj[i] = commit.combine();
        commit.square_inplace();
        i += 1;
    }
}

// ===========================================================================
// enc_cstrnts_even (upstream :81-117). Origin Rust:
//     fn enc_cstrnts_even<O>(zk_hasher: &mut ZKProofHasher<OWFField<O>>,
//         state: &ByteCommits<OWFField<O>, O::NStBytes>,
//         w: ByteCommitsRef<OWFField<O>, Quot<O::NStBytes, U2>>)
//     -> StateBitsSquaredCommits<O> {
//         let mut state_prime = default(); let mut state_conj = default();
//         for (i, (state_prime, mut commit_i)) in
//             zip(state_prime.chunks_exact_mut(8), state.iter()).enumerate() {
//             let norm = (w.keys[i / 2] >> ((i % 2) * 4)) & 0xf;
//             let ys = invnorm_to_conjugates(norm, &w.tags[4 * i..4 * i + 4]);
//             f256_f2_conjugates(&mut state_conj, &mut commit_i);
//             // ::11 Save 1 mul by storing intermediate constraint in state'[0]
//             state_prime[0] = &ys[0] * &state_conj[4];
//             let cnstr = &state_prime[0] * &state_conj[1] + &state_conj[0];
//             zk_hasher.update(&cnstr);
//             for j in 1..8 {
//                 state_prime[j] = &state_conj[(j + 4) % 8] * &ys[j % 4]; } }
//         state_prime }
// FROZEN. The FA6p-1 gate (route (b)): the update call's
// `val.key == GF128_ZERO` requires re-erects as the per-i claim
// rows (the kec_claim template); the D3+FCD1 Add row spells inline
// per the header deviation record (upstream :400-409 semantics:
// key +=, tag[2] +=).
// ===========================================================================

/// Origin Rust (:85-116).
#[verifier::external_body]
pub fn enc_cstrnts_even(
    zk_hasher: &mut ZKProofHasher128,
    state: &ByteCommits,
    w: &ByteCommitsRef,
    nst_bytes: usize,
) -> (o: Vec<FieldCommitDegTwo>)
    requires
        state.keys.len() == nst_bytes,
        state.keys.len() * 8 == state.tags.len(),
        w.keys.len() == 2 * (nst_bytes / 2),
        w.keys.len() * 8 == w.tags.len(),
        nst_bytes > 0,
        // the FA6p-1 data contract (route (b)): the per-i cnstr rows
        forall |i: int|
            0 <= i < nst_bytes as int
                ==> pe_cstr_key(state.keys[i], pe_norm(w.keys@, i)) == 0,
    ensures
        o.len() == 8 * nst_bytes,
{
    let mut state_prime: Vec<FieldCommitDegTwo> = Vec::new();
    let mut q: usize = 0;
    while q < 8 * nst_bytes
    {
        state_prime.push(FieldCommitDegTwo::default());
        q += 1;
    }
    let mut i: usize = 0;
    while i < nst_bytes
    {
        // :9 the norm nibble + the ys row
        let norm: u8 = (w.keys[i / 2] >> (((i % 2) * 4) as u8)) & 0xf;
        let ys: Vec<FieldCommitDegOne> =
            invnorm_to_conjugates(norm, &w.tags[4 * i..4 * i + 4]);
        // :4 the conjugate window (the commit is the i-th byte
        // carrier, `state.get(i)` in the upstream iteration)
        let mut state_conj: [FieldCommitDegOne; 8] = [
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
            FieldCommitDegOne::default(),
        ];
        let mut commit_i: ByteCommitment = state.get(i);
        // :4-8 the conjugate power orbit
        f256_f2_conjugates(&mut state_conj, &mut commit_i);
        // ::11 the "save 1 mul" intermediate + the cnstr feed
        // (the lane reconstructs dodge the Vec move-out; the landed
        // constructor face carries the copies)
        let sp0: FieldCommitDegTwo =
            FieldCommitDegOne::new(ys[0].key, ys[0].tag[0]).mul(&state_conj[4]);
        let m3: FieldCommitDegThree = sp0.mul_one_ref(&state_conj[1]);
        state_prime[8 * i] = sp0;
        let cnstr: FieldCommitDegThree = FieldCommitDegThree {
            key: m3.key ^ state_conj[0].key,
            tag: [m3.tag[0], m3.tag[1], m3.tag[2] ^ state_conj[0].tag[0]],
        };
        zk_hasher.update(&cnstr);
        // :12 the j in 1..8 lane rows
        let mut j: usize = 1;
        while j < 8
        {
            state_prime[8 * i + j] = FieldCommitDegOne::new(
                state_conj[(j + 4) % 8].key,
                state_conj[(j + 4) % 8].tag[0],
            ).mul(&ys[j % 4]);
            j += 1;
        }
        i += 1;
    }
    state_prime
}

// ===========================================================================
// enc_cstrnts_odd (upstream :119-140). Origin Rust:
//     fn enc_cstrnts_odd<O>(zk_hasher: &mut ZKProofHasher<OWFField<O>>,
//         s_tilde: ByteCommitsRef<OWFField<O>, O::NStBytes>,
//         st_0: &StateBytesSquaredCommits<O>,
//         st_1: &StateBytesSquaredCommits<O>) {
//         let mut s = s_tilde.inverse_shift_rows();
//         s.inverse_affine();
//         for (byte_i, (st0, st1)) in zip(st_0.as_ref(), st_1.as_ref()).enumerate() {
//             let si = s.get_field_commit(byte_i);
//             let si_sq = s.get_field_commit_sq(byte_i);
//             zk_hasher.odd_round_cstrnts(&si, &si_sq, st0, st1); } }
// FROZEN. The FA6p-1 gate (route (b)): the odd_round_cstrnts face's
// requires rows re-erect as per-byte claim rows composed over the
// landed spec primitives (the s lane = ISR + inverse-affine over
// the s_tilde keys; si/si_sq ride the landed byte-combine-sq
// orbits).
// ===========================================================================

/// The s-lane key composition (ISR + inverse-affine over the
/// s_tilde keys plane; upstream :131-132).
pub open spec fn pe_odd_s_key(s_tilde_k: Seq<u8>, nst: int, i: int) -> u8 {
    iaf8(s_tilde_k[isr_src_idx(nst, i % 4, i / 4)])
}

/// Origin Rust (:123-139).
#[verifier::external_body]
pub fn enc_cstrnts_odd(
    zk_hasher: &mut ZKProofHasher128,
    s_tilde: &ByteCommitsRef,
    st_0: &Vec<FieldCommitDegTwo>,
    st_1: &Vec<FieldCommitDegTwo>,
    nst: usize,
)
    requires
        s_tilde.keys.len() == 4 * nst,
        s_tilde.keys.len() * 8 == s_tilde.tags.len(),
        st_0.len() == 4 * nst,
        st_1.len() == 4 * nst,
        nst >= 4,
        32 * nst <= usize::MAX,
        // the FA6p-1 data contract (route (b)): the per-byte claim
        // rows mirroring the landed odd_round_cstrnts requires
        // (:2804-2805): mul(si_sq.key, st0.key) == si.key and
        // mul(si.key, st1.key) == st0.key
        forall |i: int|
            0 <= i < 4 * (nst as int)
                ==> gf128_mul_spec(
                        gf128_byte_combine_bits_spec(gf8_sq_bits_u8(
                            pe_odd_s_key(s_tilde.keys@, nst as int, i),
                        )),
                        st_0[i].key,
                    ) == gf128_byte_combine_bits_spec(
                        pe_odd_s_key(s_tilde.keys@, nst as int, i),
                    )
                    && gf128_mul_spec(
                        gf128_byte_combine_bits_spec(
                            pe_odd_s_key(s_tilde.keys@, nst as int, i),
                        ),
                        st_1[i].key,
                    ) == st_0[i].key,
    ensures
        1 == 1,
{
    // :29-30
    let mut s: ByteCommits = s_tilde.inverse_shift_rows(nst);
    s.inverse_affine(4 * nst);
    // :31-37 the byte lanes
    let nst_bytes: usize = 4 * nst;
    let mut byte_i: usize = 0;
    while byte_i < nst_bytes
    {
        let si: FieldCommitDegOne = s.get_field_commit(byte_i);
        let si_sq: FieldCommitDegOne = s.get_field_commit_sq(byte_i);
        zk_hasher.odd_round_cstrnts(&si, &si_sq, &st_0[byte_i], &st_1[byte_i]);
        byte_i += 1;
    }
}

// ===========================================================================
// aes_round (upstream :142-159). Origin Rust:
//     fn aes_round<O, T>(state: &StateBitsSquaredCommits<O>,
//         key_bytes: &Array<T, O::NStBytes>, sq: bool)
//     -> StateBytesSquaredCommits<O> {
//         let mut st = state.s_box_affine(sq);
//         st.shift_rows();
//         st.mix_columns(sq);
//         st.add_round_key_bytes(key_bytes, sq);
//         st }
// FROZEN: the four steps are the landed free faces (the FA11
// wave-1 D2 forms); structural rows only.
// ===========================================================================

/// Origin Rust (:148-157); the EM-instance shape (S = the GF128
/// element rows -- the FCD2 += &F field-add planes, the landed
/// add_round_key_bytes face).
#[verifier::external_body]
pub fn aes_round_u128(
    state: &[FieldCommitDegTwo],
    key_bytes: &[u128],
    sq: bool,
    nst: usize,
    nst_bytes: usize,
) -> (o: Vec<FieldCommitDegTwo>)
    requires
        state.len() == 8 * nst_bytes,
        key_bytes.len() == nst_bytes,
        nst_bytes == 4 * nst,
        nst >= 4,
    ensures
        o.len() == nst_bytes,
{
    // :19-22 the four chained faces (the landed u128-key rows)
    let mut st: Vec<FieldCommitDegTwo> = s_box_affine(state, nst_bytes, sq);
    shift_rows_d2(&mut st, nst);
    mix_columns(&mut st, nst_bytes, sq);
    add_round_key_bytes(&mut st, key_bytes, sq);
    st
}

/// Origin Rust (:148-157); the non-EM-instance shape (S = FCD1
/// rows -- FCD2 += &FCD1 is the landed add_one face, and the sq
/// arm's <S as Square>::Output = FCD2 rows ride add_two).
#[verifier::external_body]
pub fn aes_round_fcd1(
    state: &[FieldCommitDegTwo],
    key_bytes: &[FieldCommitDegOne],
    sq: bool,
    nst: usize,
    nst_bytes: usize,
) -> (o: Vec<FieldCommitDegTwo>)
    requires
        state.len() == 8 * nst_bytes,
        key_bytes.len() == nst_bytes,
        nst_bytes == 4 * nst,
        nst >= 4,
    ensures
        o.len() == nst_bytes,
{
    // :19-22 the four chained faces; the per-lane adds follow the
    // upstream impl rows: D2 += &D1 is field_commitment.rs :280-290
    // (key +=, tag[1] +=; spelled inline here -- no landed twin
    // face for that specific op, deviation recorded at the header),
    // and the sq arm's <S as Square>::Output = D2 rows ride the
    // landed D2.add_assign face (upstream :42-52 semantics)
    let mut st: Vec<FieldCommitDegTwo> = s_box_affine(state, nst_bytes, sq);
    shift_rows_d2(&mut st, nst);
    mix_columns(&mut st, nst_bytes, sq);
    let mut i: usize = 0;
    while i < nst_bytes
    {
        if !sq {
            // upstream :280-290: st.key += k.key; st.tag[1] += k.tag[0]
            st[i].key = st[i].key ^ key_bytes[i].key;
            st[i].tag[1] = st[i].tag[1] ^ key_bytes[i].tag[0];
        } else {
            // (&round_key).square(): the landed D1::square face,
            // per-lane reconstruct to dodge the Vec move-out
            let rk_sq_i: FieldCommitDegTwo = FieldCommitDegOne::new(
                key_bytes[i].key,
                key_bytes[i].tag[0],
            ).square();
            st[i].add_assign(&rk_sq_i);
        }
        i += 1;
    }
    st
}

// ===========================================================================
// enc_cstrnts (upstream :23-79). The generic dispatch lands as the
// two entries below (header records). FROZEN: structural rows only.
// The w windows at :3-15 / :29-38 ride the landed get_commits_ref
// slices; round keys at :16-17 consume the landed state_to_bytes
// folds, the sq variant composing the per-element field square
// (the Array<S>::Square blanket lowering).
// ===========================================================================

/// The EM instance (K = public u8 byte rows). Origin Rust
/// (:23-79), the generic body's first dispatch shape.
#[verifier::external_body]
pub fn enc_cstrnts_u8(
    zk_hasher: &mut ZKProofHasher128,
    input: &ByteCommitsRef,
    output: &ByteCommitsRef,
    w: &ByteCommitsRef,
    ext_keys: &[u8],
    nst: usize,
    nst_bytes: usize,
    r_half: usize,
)
    requires
        nst >= 4,
        nst_bytes == 4 * nst,
        input.keys.len() == nst_bytes,
        input.keys.len() * 8 == input.tags.len(),
        output.keys.len() == nst_bytes,
        output.keys.len() * 8 == output.tags.len(),
        w.keys.len()
            >= ((nst_bytes / 2) * 3 * (r_half - 1)) / 1 + (nst_bytes / 2) * 3
                + nst_bytes * (r_half - 1) + nst_bytes * r_half,
        w.keys.len() * 8 == w.tags.len(),
        ext_keys.len() == nst_bytes * (2 * r_half + 1),
        32 * nst <= usize::MAX,
        r_half >= 1,
        // the even (b) rows per round ride the state plane claims
        // (per-round state planes are the driver-internal carriers;
        // the caller-level rows are the owf twin's obligations --
        // recorded in the notes kit)
    ensures
        1 == 1,
{
    // ::1 state = input.add_round_key(&extended_key[0]) -- the
    // public-row ARK face
    let mut state: ByteCommits = input.add_round_key_public_ref(&ext_keys[0..nst_bytes]);
    // ::2 the r loop
    let mut r: usize = 0;
    while r < r_half
    {
        // ::3-15 the even feed (w window at 3 * nst_bytes * r / 2)
        let w_even: ByteCommitsRef =
            w.get_commits_ref((3 * nst_bytes * r) / 2, nst_bytes / 2);
        let state_prime: Vec<FieldCommitDegTwo> =
            enc_cstrnts_even(zk_hasher, &state, &w_even, nst_bytes);
        // ::16-17 the round key rows (state_to_bytes + per-element
        // square -- the K = Array<u8> fold shapes)
        let round_key: Vec<u128> =
            state_to_bytes_public(&ext_keys[nst_bytes * (2 * r + 1)..nst_bytes * (2 * r + 2)]);
        let mut round_key_sq: Vec<u128> = Vec::new();
        let mut q_sq: usize = 0;
        while q_sq < nst_bytes
        {
            round_key_sq.push(gf128_square(round_key[q_sq]));
            q_sq += 1;
        }
        // ::18-22 the two aes folds
        let st_0: Vec<FieldCommitDegTwo> =
            aes_round_u128(&state_prime, &round_key, false, nst, nst_bytes);
        let st_1: Vec<FieldCommitDegTwo> =
            aes_round_u128(&state_prime, &round_key_sq, true, nst, nst_bytes);
        // ::23-28 the tail split
        if r != r_half - 1 {
            // :29-38 the odd feed over the s_tilde window
            let s_tilde: ByteCommitsRef = w.get_commits_ref(
                (nst_bytes / 2) + (3 * nst_bytes * r) / 2,
                nst_bytes,
            );
            enc_cstrnts_odd(zk_hasher, &s_tilde, &st_0, &st_1, nst);
            // :39-40 state = s_tilde.bytewise_mix_columns() + row
            let bytewise: ByteCommits =
                bytewise_mix_columns(&s_tilde.keys, &s_tilde.tags, nst);
            let mut state_next: ByteCommits = bytewise;
            state_next.add_round_key_assign_public(
                &ext_keys[nst_bytes * (2 * r + 2)..nst_bytes * (2 * r + 3)],
            );
            state = state_next;
        } else {
            // :29-38 the last-round feed over the output rows
            // (upstream :73: s_tilde = output.add_round_key(round_key)
            // then enc_odd over s_tilde.to_ref())
            let s_tilde: ByteCommits = output.add_round_key_public_ref(
                &ext_keys[nst_bytes * (2 * r + 2)..nst_bytes * (2 * r + 3)],
            );
            enc_cstrnts_odd(zk_hasher, &s_tilde.to_ref(), &st_0, &st_1, nst);
        }
        r += 1;
    }
}

/// The non-EM instance (K = ByteCommitsRef hidden rows; input =
/// the public u8 state plane). Origin Rust (:23-79), the second
/// dispatch shape.
#[verifier::external_body]
pub fn enc_cstrnts_hidden(
    zk_hasher: &mut ZKProofHasher128,
    input: &[u8],
    output: &[u8],
    w: &ByteCommitsRef,
    ext_rows: &[ByteCommitsRef],
    nst: usize,
    nst_bytes: usize,
    r_half: usize,
)
    requires
        nst >= 4,
        nst_bytes == 4 * nst,
        input.len() == nst_bytes,
        output.len() == nst_bytes,
        w.keys.len()
            >= ((nst_bytes / 2) * 3 * (r_half - 1)) / 1 + (nst_bytes / 2) * 3
                + nst_bytes * (r_half - 1) + nst_bytes * r_half,
        w.keys.len() * 8 == w.tags.len(),
        ext_rows.len() == 2 * r_half + 1,
        32 * nst <= usize::MAX,
        r_half >= 1,
    ensures
        1 == 1,
{
    // ::1 state = input.add_round_key(&extended_key[0]) -- the
    // public-state ARK face (public lhs, hidden rhs rows)
    let mut state: ByteCommits =
        ByteCommitsRef::public_state_add_round_key(input, &ext_rows[0]);
    let mut r: usize = 0;
    while r < r_half
    {
        // ::3-15 the even feed
        let w_even: ByteCommitsRef =
            w.get_commits_ref((3 * nst_bytes * r) / 2, nst_bytes / 2);
        let state_prime: Vec<FieldCommitDegTwo> =
            enc_cstrnts_even(zk_hasher, &state, &w_even, nst_bytes);
        // ::16-17 the round-key folds (the hidden rows' byte plane;
        // the landed state_to_bytes_ref gives the FCD1 carrier rows)
        let round_key: Vec<FieldCommitDegOne> = ext_rows[2 * r + 1].state_to_bytes_ref();
        // ::18-22 the two aes folds (the fcd1 shape)
        let st_0: Vec<FieldCommitDegTwo> =
            aes_round_fcd1(&state_prime, &round_key, false, nst, nst_bytes);
        let st_1: Vec<FieldCommitDegTwo> =
            aes_round_fcd1(&state_prime, &round_key, true, nst, nst_bytes);
        // ::23-28 the tail split
        if r != r_half - 1 {
            let s_tilde: ByteCommitsRef = w.get_commits_ref(
                (nst_bytes / 2) + (3 * nst_bytes * r) / 2,
                nst_bytes,
            );
            enc_cstrnts_odd(zk_hasher, &s_tilde, &st_0, &st_1, nst);
            // :39-40 the bytewise fold + the hidden-row add
            let bytewise: ByteCommits =
                bytewise_mix_columns(&s_tilde.keys, &s_tilde.tags, nst);
            let mut state_next: ByteCommits = bytewise;
            state_next.add_round_key_assign_hidden(&ext_rows[2 * r + 2]);
            state = state_next;
        } else {
            // :29-38 the last-round feed over the output rows
            // (upstream :73-76: output.add_round_key(round_key) over
            // the public output plane + the hidden row)
            let s_tilde: ByteCommits =
                ByteCommitsRef::public_state_add_round_key(output, &ext_rows[2 * r + 2]);
            enc_cstrnts_odd(zk_hasher, &s_tilde.to_ref(), &st_0, &st_1, nst);
        }
        r += 1;
    }
}

} // verus!
