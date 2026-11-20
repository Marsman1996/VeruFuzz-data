//! faest 0.3.0 -- Verus transcription of src/zk_constraints.rs,
//! batch FA13 (the sign/verify chain layer between the outer
//! faest.rs faces and the landed prover/verifier owf_constraint
//! twins).
//!
//! Upstream (zk_constraints.rs, 124 lines, pin 9ccc68c0; code/
//! read-only): the CstrntsVal carrier type (:16-17), reshape_and_
//! to_field (:19-35), aes_prove (:37-72), aes_verify (:74-124).
//!
//! Ownership ruling (first-hand ledger sweep, recorded in
//! out/kverus-run/FA13/notes.md): no prior batch claimed this file
//! (FA6-pre and FA11-beta point at it as "the sign/verify API
//! layer" only); FA13 takes it as its own consumed-chain twin since
//! the faest.rs sign/verify bodies thread straight through it
//! (upstream parameter.rs :23 imports these two faces and :333/:346
//! dispatch to them from P::OWF::prove / P::OWF::verify).
//!
//! Representation lowerings (this batch's records):
//!   - `CstrntsVal<'a, O> = &'a Array<Array<u8, O::LHatBytes>,
//!     O::Lambda>` lowers to a flattened byte slice of Lambda rows,
//!     each LHatBytes long (the flag carrier of the landed twin
//!     faces; the twin's flat index = row * lhat_bytes + col).
//!   - `OWFField<O>` at the FAEST-128 axes lowers to u128 (the GF128
//!     landing axis of the whole universal_hashing / prover / verifier
//!     twin tree). The ZKProofHasher128 / ZKVerifyHasher128 landing
//!     faces pin Chall = 8 + 3 * LambdaBytes bytes (the FA9 tower
//!     rows); the lambda-192/256 constraint drivers are not landed
//!     (SF192/256 ZK hasher rows exist in universal_hashing.rs but
//!     no ZKProofHasher192/256 driver does), so the exec-active axis
//!     of these faces is lambda == 128 -- the requires rows keep the
//!     FA9-row domain shape, the record is here.
//!   - `OWFField::from(bytes)` is the GF128 little-endian lane
//!     fold (le16 convention of the FA3 twin arithmetic; the
//!     reshaper below assembles each element bit-row directly, which
//!     is the same u128).
//!   - SumPoly::sum_poly / sum_poly_bits (large_fields.rs :224-246):
//!     arbitrary-length consumers here re-erect as the two local
//!     exec faces below (verifier chains themselves; upstream
//!     iterator fold preserved inside), seeded at the LAST element /
//!     bit (the upstream rev().skip(1) shape).
//!   - Field `+`/`-` is the char-2 limb xor; `*` is gf128_mul;
//!     `.square()` is gf128_square (the landed exec faces).
//!
//! Trust / contract split (the FA12 window-6 FA13 kit rows):
//!   - aes_prove carries the (b)-form claim uplift: the kec_claim1 /
//!     kec_claim2 rows (the prover key_exp_cstrnts data contract,
//!     per the FA12 window-3 route-(b) ruling) re-erect in THIS
//!     face's requires over the witness byte window (the LKeBytes
//!     window over the flattened witness slice) -- the harness KAT
//!     arms discharge them with oracle data (the single-AES-128
//!     manual splice sample archived in the FA13 notes/oracle kit).
//!     The pe_cstr_key / pe_odd_* even/odd rows stay inside the
//!     frozen enc drivers (their per-round state planes are
//!     driver-internal carriers per the FA12 window-6 records); the
//!     machine-oracle batch owns their discharge (recorded, not
//!     re-erected here).
//!   - aes_verify carries NO claim rows (the verifier side has no
//!     (b) family -- the FA12 window-4 ruling, re-checked first-hand
//!     against the landed verifier owf twin).
//!   - Both faces stay FROZEN bodies (external_body + structural
//!     ensures; the FA12 driver trajectory ruling) with the two
//!     sum_poly helper leaves exec-verified inside this file.

use vstd::prelude::*;

use crate::large_fields::{gf128_double, gf128_mul, gf128_square, gf128_xtime, GF128_ONE};
use crate::prover::byte_commitments::ByteCommitsRef;
use crate::prover::key_expansion::{kec_claim1, kec_claim2};
use crate::prover::owf_constraints::owf_constraints as prover_owf_constraints;
use crate::universal_hashing::{ZKProofHasher128, ZKVerifyHasher128};
use crate::utils::get_bit;
use crate::verifier::owf_constraints::owf_constraints as verifier_owf_constraints;
use crate::verifier::vole_commitments::VoleCommitsRef;

verus! {

// ===========================================================================
// SumPoly arbitrary-length exec leaves (upstream large_fields.rs
// :224-246, the blanket SumPoly faces consumed by zk_constraints
// :46-49 and :108-112; the [:8] fixed faces landed in large_fields,
// the chain-length instances re-erect here).
//
// Origin Rust (trait body):
//     fn sum_poly(v: &[Self]) -> Self {
//         v.iter().rev().skip(1)
//             .fold(v[v.len() - 1], |sum, val| sum.double() + val) }
// ===========================================================================

/// The spec recursion of sum_poly: acc(v, j) is the fold value after
/// consuming v[len-1] ..= v[len-1-j] (j consumed terms past the
/// seed). gf128_xtime is the field double (fields record).
pub open spec fn gf128_sum_poly_slice_spec(sv: Seq<u128>, j: int) -> u128
    decreases j
{
    if j <= 0 {
        sv[sv.len() - 1]
    } else {
        gf128_xtime(gf128_sum_poly_slice_spec(sv, j - 1)) ^ sv[sv.len() - 1 - j]
    }
}

/// Origin Rust (upstream :333-338 blanket; the chain-length instance
/// this file consumes). exec + spec both: verified leaf.
pub fn gf128_sum_poly_slice(v: &[u128]) -> (res: u128)
    requires
        v.len() >= 1,
    ensures
        res == gf128_sum_poly_slice_spec(v@, (v@.len() as int) - 1),
{
    let lam: usize = v.len();
    let mut acc: u128 = v[lam - 1];
    let mut j: usize = 1;
    while j < lam
        invariant
            1 <= j <= lam,
            lam == v.len(),
            acc == gf128_sum_poly_slice_spec(v@, (j as int) - 1),
        decreases lam - j,
    {
        proof {
            assert((j as int) - 1 < (lam as int) - 1);
            assert(lam - 1 - j < lam);
            assert(v@[(v@.len() as int) - 1 - (j as int)] == v[lam - 1 - j]);
            assert(gf128_sum_poly_slice_spec(v@, j as int)
                == gf128_xtime(gf128_sum_poly_slice_spec(v@, (j as int) - 1))
                    ^ v@[(v@.len() as int) - 1 - (j as int)]);
        }
        acc = gf128_double(acc) ^ v[lam - 1 - j];
        j += 1;
    }
    proof {
        assert((lam as int) - 1 == (v@.len() as int) - 1);
        assert(j == lam);
    }
    acc
}

/// The spec recursion of sum_poly_bits: seed = from_bit of the most
/// significant bit (bit 8*len - 1), then bits 8*len - 2 ..= 0 fold
/// double-then-add-from_bit, MSB-first.
pub open spec fn gf128_sum_poly_bits_slice_spec(sv: Seq<u8>, i: int) -> u128
    decreases (sv.len() as int) * 8 - i
{
    if i >= (sv.len() as int) * 8 - 1 {
        if (sv[i / 8] >> 7) & 1 == 1 { GF128_ONE } else { 0u128 }
    } else {
        gf128_xtime(gf128_sum_poly_bits_slice_spec(sv, i + 1))
            ^ (if (sv[i / 8] >> (i % 8)) & 1 == 1 { GF128_ONE } else { 0u128 })
    }
}

/// Origin Rust (upstream :340-345 blanket; the 16-byte instance this
/// file consumes). exec + spec both: verified leaf.
pub fn gf128_sum_poly_bits_slice(v: &[u8]) -> (res: u128)
    requires
        v.len() >= 1,
        8 * v.len() <= usize::MAX,
    ensures
        res == gf128_sum_poly_bits_slice_spec(v@, 0),
{
    let lam: usize = v.len();
    let top: usize = 8 * lam - 1;
    let mut acc: u128 = if (v[lam - 1] >> 7) & 1 == 1 { GF128_ONE } else { 0u128 };
    let mut i: usize = top;
    while i > 0
        invariant
            0 <= i <= top,
            top == 8 * lam - 1,
            lam == v.len(),
            acc == gf128_sum_poly_bits_slice_spec(v@, i as int),
        decreases i,
    {
        proof {
            // the def-unfold at (i-1): the guard picks the else arm
            assert((i as int) - 1 < (v@.len() as int) * 8 - 1);
            // the exec bit vs the spec bit (Seq <-> slice read bridge)
            assert(v@[((i as int) - 1) / 8] == v[(i - 1) / 8]);
            assert(gf128_sum_poly_bits_slice_spec(v@, (i as int) - 1)
                == gf128_xtime(gf128_sum_poly_bits_slice_spec(v@, i as int))
                    ^ (if (v@[((i as int) - 1) / 8]
                        >> (((i as int) - 1) % 8)) & 1 == 1 {
                        GF128_ONE
                    } else {
                        0u128
                    }));
        }
        let bi: usize = i - 1;
        let term: u128 = if (v[bi / 8] >> (bi % 8)) & 1 == 1 {
            GF128_ONE
        } else {
            0u128
        };
        acc = gf128_double(acc) ^ term;
        i -= 1;
    }
    proof {
        assert(0 == (lam as int) * 8 - 8 * lam);
        assert(gf128_sum_poly_bits_slice_spec(v@, 0) == acc);
    }
    acc
}

// ===========================================================================
// reshape_and_to_field (upstream :19-35).
// Origin Rust:
//     fn reshape_and_to_field<O: OWFParameters>(m: CstrntsVal<O>)
//     -> Vec<OWFField<O>> {
//         (0..O::LBytes::USIZE + O::LambdaBytesTimes2::USIZE)
//             .flat_map(|col| {
//                 let mut ret = vec![Array::<u8, O::LambdaBytes>::default(); 8];
//                 for row in 0..O::Lambda::USIZE {
//                     for (i, ret_i) in ret.iter_mut().enumerate() {
//                         ret_i[row / 8] |= get_bit(&[m[row][col]], i) << (row % 8);
//                     }
//                 }
//                 ret.into_iter().map(|r_i| OWFField::<O>::from(r_i.as_slice()))
//             })
//             .collect() }
// FROZEN (the FA12 driver trajectory ruling): the bit-gather below is
// the faithful flat lowering (rows = the Lambda vole-matrix rows,
// col = the witness-byte column); the byte assembly folds straight
// into the u128 lane (the le16 GF128 record at this header).
// ===========================================================================

/// Origin Rust (:19-35); the flat carrier: m holds Lambda rows, each
/// lhat_bytes long (CstrntsVal lowered).
#[verifier::external_body]
pub fn reshape_and_to_field(
    m: &[u8],
    lhat_bytes: usize,
    lambda: usize,
    l_bytes: usize,
    lambda_bytes: usize,
) -> (o: Vec<u128>)
    requires
        lambda == 8 * lambda_bytes,
        l_bytes >= 1,
        m.len() == lambda * lhat_bytes,
        lambda as int * lhat_bytes as int <= usize::MAX as int,
        lambda >= 1,
    ensures
        o.len() == (l_bytes + 2 * lambda_bytes) * 8,
{
    let mut o: Vec<u128> = Vec::new();
    let mut col: usize = 0;
    while col < l_bytes + 2 * lambda_bytes
    {
        let mut q: usize = 0;
        while q < 8
        {
            // the per-lane element (the upstream ret_i carrier as the
            // le16 u128 lane: assembling ret_i[row / 8] |= bit <<
            // (row % 8) over the byte plane is BIT row of the le16
            // lane -- the same u128 bit index; the assembly below
            // writes each row's bit at its lane position directly)
            let mut lane_elem: u128 = 0;
            let mut row: usize = 0;
            while row < lambda
            {
                let byte: u8 = m[row * lhat_bytes + col];
                let bit: u8 = (byte >> q) & 1;
                lane_elem = lane_elem | ((bit as u128) << row);
                row += 1;
            }
            o.push(lane_elem);
            q += 1;
        }
        col += 1;
    }
    o
}

// ===========================================================================
// aes_prove (upstream :37-72).
// Origin Rust:
//     pub(crate) fn aes_prove<O>(w: &Array<u8, O::LBytes>,
//         u: &Array<u8, O::LambdaBytesTimes2>,
//         v: CstrntsVal<O>, pk: &PublicKey<O>,
//         chall_2: &Array<u8, BaseParams::Chall>) -> QSProof<O> {
//         let mut zk_hasher = ...::new_zk_proof_hasher(chall_2);
//         let v = reshape_and_to_field::<O>(v);
//         let u0_star = OWFField::<O>::sum_poly_bits(&u[..O::LambdaBytes::USIZE]);
//         let u1_star = OWFField::<O>::sum_poly_bits(&u[O::LambdaBytes::USIZE..]);
//         let v0_star = OWFField::<O>::sum_poly(&v[O::L::USIZE..O::L::USIZE + O::Lambda::USIZE]);
//         let v1_star = OWFField::<O>::sum_poly(&v[O::L::USIZE + O::Lambda::USIZE..]);
//         prover::owf_constraints::<O>(&mut zk_hasher,
//             ByteCommitsRef::from_slices(w, &v[..O::L::USIZE]), pk);
//         zk_hasher.finalize(&v0_star, &(u0_star + v1_star), &u1_star) }
// FROZEN (external_body + the structural returns; the window-5
// requires table below mirrors the landed prover owf twin row for
// row, adapted to this face's explicit row parameters).
// The (b)-form claim uplift: the kec_claim1/kec_claim2 forall rows
// (route (b), the FA12 window-3 ruling; the prover owf_constraints
// chain consumes key_exp_cstrnts whose own requires carries them)
// re-erect here over the LKeBytes witness window -- the caller
// (sign / harness KAT) discharges them with oracle data.
// ===========================================================================

/// Origin Rust (:37-72); the (a1_tilde, a2_tilde, a0_tilde) are the
/// three u128 lanes making the QSProof triple at the GF128 axis
/// (upstream returns QSProof<O> = (OWFField, OWFField, OWFField);
/// note the upstream faest.rs consumes them as (a0, a1, a2)).
#[verifier::external_body]
pub fn aes_prove(
    w_bytes: &[u8],
    u_bytes: &[u8],
    v_flat: &[u8],
    owf_input: &[u8],
    owf_output: &[u8],
    schedule_bytes: &[u8],
    chall2: &[u8],
    nst: usize,
    nst_bytes: usize,
    nk: usize,
    lambda: usize,
    r: usize,
    ske: usize,
    n_words: usize,
    l_bytes: usize,
    lhat_bytes: usize,
    lke_bytes: usize,
    lenc_bytes: usize,
    beta: usize,
    is_em: bool,
) -> (o: (u128, u128, u128))
    requires
        // the FA9-row domain (the owf twins' shared table)
        nst >= 4,
        nst_bytes == 4 * nst,
        nk >= 1,
        nk <= 8,
        lambda == 128 || lambda == 192 || lambda == 256,
        lambda == 32 * nk,
        r >= 2,
        r % 2 == 0,
        r <= 14,
        n_words == 4 * (r + 1),
        n_words > nk,
        ske >= 4,
        ske <= 64,
        ske % 4 == 0,
        n_words <= 64,
        4 * n_words <= usize::MAX,
        32 * n_words <= usize::MAX,
        // the byte-slice carrier rows of THIS face
        w_bytes.len() == l_bytes,
        u_bytes.len() == 2 * (lambda / 8),
        v_flat.len() == lambda * lhat_bytes,
        chall2.len() == 8 + 3 * (lambda / 8),
        // the prover owf twin's window-5 requires rows (adapted:
        // the w carrier here IS the full LBytes window)
        l_bytes * 8 == w_bytes.len() * 8,
        lke_bytes + (lenc_bytes * (if is_em { 1 } else { beta }))
            <= w_bytes.len(),
        owf_input.len() == nst_bytes,
        if is_em {
            owf_output.len() == nst_bytes
        } else {
            owf_output.len() == beta * nst_bytes
        },
        beta >= 1,
        if is_em {
            schedule_bytes.len() >= 32 * (r + 1)
        } else {
            schedule_bytes.len() == 0
        },
        // the FA6p-1 data-contract rows (route (b), the key_exp
        // chain claims over the LKeBytes witness window; the
        // harness KAT arms discharge them with oracle data)
        if !is_em {
            forall |q: int, r_c: int|
                0 <= q < (ske as int / 4) && 0 <= r_c < 4
                    ==> kec_claim1(
                            w_bytes@.subrange(0, lke_bytes as int),
                            nk as int,
                            lambda as int,
                            n_words as int,
                            lke_bytes as int,
                            q,
                            r_c,
                        )
                        && kec_claim2(
                            w_bytes@.subrange(0, lke_bytes as int),
                            nk as int,
                            lambda as int,
                            n_words as int,
                            lke_bytes as int,
                            q,
                            r_c,
                        )
        } else {
            true
        },
    ensures
        1 == 1,
{
    // ::1 the zk hasher seed (the chall2 slab = the Chall row)
    let mut zk_hasher: ZKProofHasher128 = ZKProofHasher128::new_zk_proof_hasher(chall2);
    // ::1-4 the reshape (the CstrntsVal bit-gather)
    let v: Vec<u128> = reshape_and_to_field(
        v_flat,
        lhat_bytes,
        lambda,
        l_bytes,
        lambda / 8,
    );
    // ::7 the u stars (sum_poly_bits; plus/+= is the char-2 xor)
    let u0_star: u128 = gf128_sum_poly_bits_slice(&u_bytes[0..lambda / 8]);
    let u1_star: u128 = gf128_sum_poly_bits_slice(&u_bytes[lambda / 8..2 * (lambda / 8)]);
    // ::8 the v stars (sum_poly)
    let l_bits: usize = l_bytes * 8;
    let v0_star: u128 = gf128_sum_poly_slice(&v[l_bits..l_bits + lambda]);
    let v1_star: u128 = gf128_sum_poly_slice(&v[l_bits + lambda..l_bits + 2 * lambda]);
    // ::12 the constraints segment (the landed prover owf twin; the
    // witness tags plane = the first L lanes of the reshape)
    let w_ref: ByteCommitsRef = ByteCommitsRef::from_slices(w_bytes, &v[0..l_bits]);
    prover_owf_constraints(
        &mut zk_hasher,
        &w_ref,
        owf_input,
        owf_output,
        schedule_bytes,
        nst,
        nst_bytes,
        nk,
        lambda,
        r,
        ske,
        n_words,
        lke_bytes,
        lenc_bytes,
        beta,
        is_em,
    );
    // ::13-18 the finalization triple (upstream returns QSProof;
    // faest.rs destructure order (a0_tilde, a1_tilde, a2_tilde))
    let (f0, f1, f2): (u128, u128, u128) = zk_hasher.finalize(
        v0_star,
        u0_star ^ v1_star,
        u1_star,
    );
    (f1, f2, f0)
}

// ===========================================================================
// aes_verify (upstream :74-124).
// Origin Rust:
//     pub(crate) fn aes_verify<O>(q: CstrntsVal<O>,
//         d: &Array<u8, O::LBytes>, pk: &PublicKey<O>,
//         chall_2: &Array<u8, BaseParams::Chall>,
//         chall_3: &Array<u8, O::LambdaBytes>,
//         a1_tilde: &Array<u8, O::LambdaBytes>,
//         a2_tilde: &Array<u8, O::LambdaBytes>) -> OWFField<O> {
//         let delta = OWFField::<O>::from(chall_3.as_slice());
//         let mut q = reshape_and_to_field::<O>(q);
//         for (i, q_i) in q.iter_mut().take(O::L::USIZE).enumerate() {
//             if get_bit(d, i) != 0 { *q_i += delta; } }
//         let w = VoleCommitsRef { scalars: array_ref(&q[..O::L::USIZE]),
//             delta: &delta };
//         let q0_star = sum_poly(&q[L..L+Lambda]); let q1_star = sum_poly(...);
//         let q_star = delta * q1_star + q0_star;
//         let mut zk_hasher = ...::new_zk_verify_hasher(chall_2, delta);
//         verifier::owf_constraints::<O>(&mut zk_hasher, w, &delta, pk);
//         let q_tilde = zk_hasher.finalize(&q_star);
//         q_tilde - delta * OWFField::<O>::from(a1_tilde)
//                  - delta.square() * OWFField::<O>::from(a2_tilde) }
// FROZEN (same ruling); the window-5 requires table (the VERIFIER
// owf twin's own block, row for row, re-anchored first-hand) is the
// caller obligation table of the verify chain.
// ===========================================================================

/// Origin Rust (:74-124); returns the a0_tilde lane recomputed at
/// the verify side (upstream returns OWFField<O> = u128 here).
#[verifier::external_body]
pub fn aes_verify(
    q_flat: &[u8],
    d_bytes: &[u8],
    owf_input: &[u8],
    owf_output: &[u8],
    schedule_bytes: &[u8],
    chall2: &[u8],
    chall3: &[u8],
    a1_tilde: &[u8],
    a2_tilde: &[u8],
    nst: usize,
    nst_bytes: usize,
    nk: usize,
    lambda: usize,
    r: usize,
    ske: usize,
    n_words: usize,
    l_bytes: usize,
    lhat_bytes: usize,
    lke: usize,
    lenc: usize,
    beta: usize,
    is_em: bool,
) -> (o: u128)
    requires
        // the window-5 requires table (the landed verifier owf twin,
        // re-anchored row for row; the VoleCommitsRef carrier rows
        // are spelled at the end)
        nst >= 4,
        nst_bytes == 4 * nst,
        nk >= 1,
        nk <= 8,
        lambda == 128 || lambda == 192 || lambda == 256,
        lambda == 32 * nk,
        r >= 2,
        r % 2 == 0,
        r <= 14,
        n_words == 4 * (r + 1),
        n_words > nk,
        ske >= 4,
        ske <= 64,
        ske % 4 == 0,
        n_words <= 64,
        32 * n_words <= usize::MAX,
        // this face's carrier rows (the w scalars plane length =
        // the l_bytes witness bits; the verifier twin indexes use
        // bit-granular window rows, mirrored here with L* = bits)
        l_bytes >= 1,
        lke >= lambda,
        lke + (lenc * (if is_em { 1 } else { beta })) <= l_bytes * 8,
        owf_input.len() == nst_bytes,
        if is_em {
            owf_output.len() == nst_bytes
        } else {
            owf_output.len() == beta * nst_bytes
        },
        beta >= 1,
        8 * beta <= usize::MAX,
        if is_em {
            schedule_bytes.len() >= 32 * (r + 1)
        } else {
            schedule_bytes.len() == 0
        },
        // the key_exp_cstrnts chain rows (the verifier twin's own
        // non-EM block, row for row)
        if !is_em {
            8 * ske <= (l_bytes * 8 - lambda)
                && (lambda as int)
                    + 32 * (crate::prover::key_expansion::kef_cw(
                        nk as int, nk as int, n_words as int) + 1)
                    <= (l_bytes * 8) as int
                && crate::prover::key_expansion::keb_iwd(
                    lambda as int, ske as int - 1) + 8 * 3 + 8
                    <= 32 * n_words
                && ((ske as int - 1)
                    / (4 * (lambda as int / 128))) < 30
                && (32 * (nk as int - 1)
                    + (if lambda == 192 { 192int } else { 128int })
                        * ((ske as int / 4) - 1) + 40)
                    <= 32 * n_words as int
        } else {
            true
        },
        // the byte-slice carrier rows
        d_bytes.len() == l_bytes,
        q_flat.len() == lambda * lhat_bytes,
        chall2.len() == 8 + 3 * (lambda / 8),
        chall3.len() == lambda / 8,
        a1_tilde.len() == lambda / 8,
        a2_tilde.len() == lambda / 8,
    ensures
        1 == 1,
{
    // ::1 the challenge delta (the chall3 lane as the GF128
    // element; the le16 fold rows the landed le16_u128 spec face)
    let mut delta: u128 = 0;
    {
        let mut bi: usize = 0;
        while bi < chall3.len()
        {
            let b: u8 = chall3[bi];
            delta = delta ^ ((b as u128) << (8 * bi));
            bi += 1;
        }
    }
    // ::2-5 the reshape
    let mut q: Vec<u128> = reshape_and_to_field(
        q_flat,
        lhat_bytes,
        lambda,
        l_bytes,
        lambda / 8,
    );
    // the first L rows take the masked-witness increments
    let l_bits: usize = l_bytes * 8;
    {
        let mut i: usize = 0;
        while i < l_bits
        {
            if get_bit(d_bytes, i) != 0 {
                q[i] = q[i] ^ delta;
            }
            i += 1;
        }
    }
    // the w carrier (the witness-plane window)
    let w: VoleCommitsRef = VoleCommitsRef {
        scalars: &q[0..l_bits],
        delta: &delta,
    };
    // ::7 the q stars
    let q0_star: u128 = gf128_sum_poly_slice(&q[l_bits..l_bits + lambda]);
    let q1_star: u128 = gf128_sum_poly_slice(
        &q[l_bits + lambda..l_bits + 2 * lambda],
    );
    // ::10
    let q_star: u128 = gf128_mul(delta, q1_star) ^ q0_star;
    // the verify hasher seed
    let mut zk_hasher: ZKVerifyHasher128 =
        crate::universal_hashing::new_zk_verify_hasher_128(chall2, delta);
    // ::12 the constraints segment (the landed verifier owf twin)
    verifier_owf_constraints(
        &mut zk_hasher,
        &w,
        &delta,
        owf_input,
        owf_output,
        schedule_bytes,
        nst,
        nst_bytes,
        8 * nst_bytes,
        nk,
        lambda,
        r,
        ske,
        n_words,
        lke,
        lenc,
        beta,
        is_em,
    );
    // ::14 the finalization
    let q_tilde: u128 = zk_hasher.finalize(q_star);
    // the a1/a2 folds and the closing field ops (upstream `+`/`-`
    // are the char-2 limb xor)
    let mut a1_f: u128 = 0;
    let mut a2_f: u128 = 0;
    {
        let mut bi: usize = 0;
        while bi < a1_tilde.len()
        {
            a1_f = a1_f ^ ((a1_tilde[bi] as u128) << (8 * bi));
            a2_f = a2_f ^ ((a2_tilde[bi] as u128) << (8 * bi));
            bi += 1;
        }
    }
    q_tilde
        ^ gf128_mul(delta, a1_f)
        ^ gf128_mul(gf128_square(delta), a2_f)
}

} // verus!
