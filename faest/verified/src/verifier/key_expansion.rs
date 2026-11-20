//! faest 0.3.0 -- Verus transcription of src/verifier/key_
//! expansion.rs, batch FA12.
//!
//! Upstream (verifier/key_expansion.rs, 172 lines, pin 9ccc68c0):
//! key_exp_fwd (:19-52), key_exp_bkwd (:54-99),
//! inverse_affine_byte (:101-114), key_exp_cstrnts (:116-172).
//! RCON_TABLE is FA10-pre landed (verified/src/rijndael_32.rs).
//!
//! Wave status (out/kverus-run/FA12/notes.md):
//! - inverse_affine_byte: LANDED and verified (wave-2a).
//! - key_exp_fwd / key_exp_bkwd: LANDED in the frozen form
//!   (window 3): #[verifier::external_body] + the FULL value-face
//!   ensures over the shared kef_lane spec (bits plane == this
//!   tree's scalars plane; the prover-seat contract core -- the two
//!   trees' fwd/bkwd are the SAME convergence surface, the prover
//!   twin carries the row-kit in its file; see the notes kit).
//! - key_exp_cstrnts: LANDED, exec-verified (the verify-side
//!   ZKVerifyHasher128.lift_and_process carries no requires, so the
//!   FA6p-1 square-duality gate does NOT apply here); the hasher
//!   trajectory rows stay un-recorded at the twin boundary (upstream
//!   itself carries no contract on the feed chain; the oracle arms
//!   arbitrate -- the batch's structural ruling).
//!
//! Representation lowering (trust boundary, this batch's records):
//!   - `O: OWFParameters` drops to runtime size parameters (the
//!     FA10 RowCfg precedent); F instantiates at GF128 (u128); '+'
//!   on F is the char-2 limb xor; delta is &'a u128 (the
//!     vole_commitments convention).

use vstd::prelude::*;

use crate::large_fields::{gf128_byte_combine_slice, gf128_byte_combine_sq_slice};
use crate::prover::aes::iaf_tag;

use super::vole_commitments::{VoleCommits, VoleCommitsRef};
use crate::prover::key_expansion::{keb_iwd, keb_stride, kef_cw, kef_lane};
use crate::rijndael_32::RCON_TABLE;
use crate::universal_hashing::ZKVerifyHasher128;

verus! {

// ===========================================================================
// inverse_affine_byte (upstream :101-114). Origin Rust:
//     pub fn inverse_affine_byte<O>(
//         y_tag: &mut [OWFField<O>],
//         x_tag: &Array<OWFField<O>, U8>,
//         delta: &OWFField<O>,
//     ) where O: OWFParameters {
//         for i in 0..8 {
//             y_tag[i] = x_tag[(i + 8 - 1) % 8]
//                 + x_tag[(i + 8 - 3) % 8] + x_tag[(i + 8 - 6) % 8]; }
//         y_tag[0] += delta;
//         y_tag[2] += delta; }
// The 8-lane roster is iaf_tag's lane table (the FA11 prover twin's
// spec face, reused here per the same anti-dup logic the wave-1
// verifier/aes.rs faces use); the y_tag[0]/y_tag[2] delta rows ride
// verbatim (two-step `+=` per upstream, lowered to the ^ lane with
// the identical operand order at each step -- #FA12-2).
// ===========================================================================

/// Origin Rust (:108-113).
pub fn inverse_affine_byte(
    y_tag: &mut [u128],
    x_tag: &[u128],
    delta: &u128,
)
    requires
        y_tag.len() >= 8,
        x_tag.len() == 8,
    ensures
        forall |b: int|
            0 <= b < 8
                ==> final(y_tag)[b]
                    == (if b == 0 || b == 2 {
                        iaf_tag(x_tag@, b) ^ *delta
                    } else {
                        iaf_tag(x_tag@, b)
                    }),
        forall |b: int|
            8 <= b < final(y_tag).len()
                ==> final(y_tag)[b] == old(y_tag)[b],
{
    // ::7 the eight roster writes then ::12-13 the two delta adds;
    // unrolled (constant 8-lane chain, the FA11 record) with the
    // two-step `+=` spelling preserved at slots 0 and 2
    y_tag[0] = x_tag[7] ^ x_tag[5] ^ x_tag[2];
    y_tag[1] = x_tag[0] ^ x_tag[6] ^ x_tag[3];
    y_tag[2] = x_tag[1] ^ x_tag[7] ^ x_tag[4];
    y_tag[3] = x_tag[2] ^ x_tag[0] ^ x_tag[5];
    y_tag[4] = x_tag[3] ^ x_tag[1] ^ x_tag[6];
    y_tag[5] = x_tag[4] ^ x_tag[2] ^ x_tag[7];
    y_tag[6] = x_tag[5] ^ x_tag[3] ^ x_tag[0];
    y_tag[7] = x_tag[6] ^ x_tag[4] ^ x_tag[1];
    y_tag[0] = y_tag[0] ^ *delta;
    y_tag[2] = y_tag[2] ^ *delta;
    // per-lane spec ties (the iaf_tag def folds; #FA12-4 recipe)
    assert(final(y_tag)[0] == iaf_tag(x_tag@, 0) ^ *delta);
    assert(final(y_tag)[1] == iaf_tag(x_tag@, 1));
    assert(final(y_tag)[2] == iaf_tag(x_tag@, 2) ^ *delta);
    assert(final(y_tag)[3] == iaf_tag(x_tag@, 3));
    assert(final(y_tag)[4] == iaf_tag(x_tag@, 4));
    assert(final(y_tag)[5] == iaf_tag(x_tag@, 5));
    assert(final(y_tag)[6] == iaf_tag(x_tag@, 6));
    assert(final(y_tag)[7] == iaf_tag(x_tag@, 7));
}

// Records (this file's remaining upstream faces, deferred to
// D-FA12-3 with the kit in the batch notes):
//   - key_exp_fwd (:19-52): the j-loop over
//     [NK, 4*(R+1)) with the consumed-word windows (32-wide) --
//     the consumed-before-j counter needed on the spec side.
//   - key_exp_bkwd (:54-99): the iwd stride ladder (j%4==3 steps,
//     Lambda==192 branches) + the RCON_TABLE bit tap over
//     ske_noreq-shaped rows (FA10-pre pins) + inverse_affine_byte.
//   - key_exp_cstrnts (:116-172): key_exp_fwd + key_exp_bkwd then
//     the iproduct!(0..SKe/4, 0..4) loop (lowered to the literal
//     nesting, same iteration order) feeding lift_and_process.

// ===========================================================================
// key_exp_fwd (upstream :19-52). Origin Rust:
//     pub(crate) fn key_exp_fwd<O>(w: VoleCommitsRef<OWFField<O>, O::LKe>)
//     -> VoleCommits<OWFField<O>, O::R1Times128> {
//         let mut y_tags = Box::new(Array::default());
//         y_tags[..O::Lambda::USIZE].copy_from_slice(&w.scalars[..O::Lambda::USIZE]);
//         let mut i_wd = O::Lambda::USIZE;
//         for j in O::NK::USIZE..(4 * (O::R::USIZE + 1)) {
//             if (j % O::NK::USIZE == 0) || ((O::NK::USIZE > 6)
//                 && (j % O::NK::USIZE == 4)) {
//                 y_tags[32 * j..32 * j + 32]
//                     .copy_from_slice(&w.scalars[i_wd..i_wd + 32]);
//                 i_wd += 32;
//             } else {
//                 for i in 0..32 {
//                     y_tags[32 * j + i] = y_tags[32 * (j - O::NK::USIZE) + i]
//                         + y_tags[32 * (j - 1) + i]; } } }
//         VoleCommits { scalars: y_tags, delta: w.delta } }
// FROZEN FORM (window 3, the #FA12 bytewise/FA11-D-FA11-1 precedent;
// the same rows the prover twin's fwd carries are the convergence
// kit): #[verifier::external_body] + the FULL value-face ensures
// over the shared kef_lane spec (this tree's scalars plane), body
// faithfully transcribed below.
// ===========================================================================

#[verifier::external_body]
pub fn key_exp_fwd<'a>(
    w: &VoleCommitsRef<'a>,
    nk: usize,
    lambda: usize,
    n_words: usize,
) -> (o: VoleCommits<'a>)
    requires
        nk >= 1,
        nk <= 8,
        lambda == 32 * nk,
        n_words > nk,
        n_words <= 64,
        32 * n_words <= usize::MAX,
        (lambda as int) + 32 * (kef_cw(nk as int, nk as int, n_words as int) + 1)
            <= w.scalars.len() as int,
    ensures
        o.scalars.len() == 32 * n_words,
        forall |j: int, i: int|
            0 <= j < n_words as int && 0 <= i < 32
                ==> o.scalars[32 * j + i]
                    == kef_lane(w.scalars@, nk as int, lambda as int, j, i),
        o.delta == w.delta,
{
    // y_tags = Box<Array::default()> lowering: zero allocation
    let mut y: Vec<u128> = Vec::new();
    let mut q: usize = 0;
    while q < 32 * n_words
        invariant
            y.len() == q,
        decreases
            32 * n_words - q,
    {
        y.push(0u128);
        q += 1;
    }
    // ::1 the init copy (Lambda bits)
    let mut q4: usize = 0;
    while q4 < lambda
        invariant
            q4 <= lambda,
        decreases
            lambda - q4,
    {
        y[q4] = w.scalars[q4];
        q4 += 1;
    }
    // ::2 the j-loop
    let mut i_wd: usize = lambda;
    let mut j: usize = nk;
    while j < n_words
        decreases
            n_words - j,
    {
        if (j % nk == 0) || (nk > 6 && j % nk == 4) {
            // :6 the consume window
            let mut i: usize = 0;
            while i < 32
                decreases
                    32 - i,
            {
                y[32 * j + i] = w.scalars[i_wd + i];
                i += 1;
            }
            i_wd += 32;
        } else {
            // :9-10 the diff recurrence
            let mut i: usize = 0;
            while i < 32
                decreases
                    32 - i,
            {
                y[32 * j + i] = y[32 * (j - nk) + i] ^ y[32 * (j - 1) + i];
                i += 1;
            }
        }
        j += 1;
    }
    VoleCommits { scalars: y, delta: w.delta }
}

// ===========================================================================
// key_exp_bkwd (upstream :54-99). Origin Rust:
//     pub(crate) fn key_exp_bkwd<O>(
//         x: VoleCommitsRef<OWFField<O>, O::LKeMinusLambda>,
//         xk: VoleCommitsRef<OWFField<O>, O::R1Times128>,
//     ) -> VoleCommits<OWFField<O>, Prod<O::SKe, U8>> {
//         let mut y_tag = Box::new(Array::default());
//         let mut iwd = 0;
//         let rcon_evry = 4 * (O::Lambda::USIZE / 128);
//         for j in 0..O::SKe::USIZE {
//             let xt_tag: Array<_, U8> = (0..8).map(|i| {
//                 let mut x_tilde_i = x.scalars[8 * j + i]
//                     + xk.scalars[iwd + 8 * (j % 4) + i];
//                 if j % rcon_evry == 0
//                     && get_bit(&[RCON_TABLE[j / rcon_evry]], i) != 0 {
//                     x_tilde_i += x.delta; }
//                 x_tilde_i }).collect();
//             inverse_affine_byte::<O>(&mut y_tag[8 * j..8 * j + 8],
//                 &xt_tag, x.delta);
//             if j % 4 == 3 {
//                 if O::Lambda::USIZE != 256 { iwd += O::Lambda::USIZE; }
//                 else { iwd += 128; } } }
//         VoleCommits { scalars: y_tag, delta: x.delta } }
// The RCON tap hits the SCALAR lane per bit (get_bit rows) -- the
// verifier-specific value face below; the iwd ladder shares keb_
// stride / keb_iwd with the prover seat (same arithmetic).
// ===========================================================================

/// The per-(j, lane i) pre-affine scalar value (upstream :70-81).
pub open spec fn keb_xt_vc(
    x_s: Seq<u128>,
    xk_s: Seq<u128>,
    lambda: int,
    j: int,
    i: int,
    delta: u128,
) -> u128 {
    let base = x_s[8 * j + i] ^ xk_s[keb_iwd(lambda, j) + 8 * (j % 4) + i];
    if j % (4 * (lambda / 128)) == 0
        && ((RCON_TABLE[(j / (4 * (lambda / 128))) as int] >> (i % 8)) & 1) == 1 {
        base ^ delta
    } else {
        base
    }
}

/// The per-(j, slot b) output scalar (the inverse_affine_byte roster
/// over the xt window + the delta rows at 0/2 -- the landed twin's
/// ensures shape).
pub open spec fn keb_y_vc(
    x_s: Seq<u128>,
    xk_s: Seq<u128>,
    lambda: int,
    j: int,
    b: int,
    delta: u128,
) -> u128 {
    let w: Seq<u128> = Seq::new(8nat, |t: int|
        keb_xt_vc(x_s, xk_s, lambda, j, t, delta));
    if b == 0 || b == 2 {
        iaf_tag(w, b) ^ delta
    } else {
        iaf_tag(w, b)
    }
}

#[verifier::external_body]
pub fn key_exp_bkwd<'a>(
    x: &VoleCommitsRef<'a>,
    xk: &VoleCommitsRef<'a>,
    ske: usize,
    lambda: usize,
) -> (o: VoleCommits<'a>)
    requires
        lambda == 128 || lambda == 192 || lambda == 256,
        ske >= 1,
        ske <= 64,
        8 * ske <= usize::MAX,
        8 * ske <= x.scalars.len(),
        keb_iwd(lambda as int, ske as int - 1) + 8 * 3 + 8
            <= xk.scalars.len() as int,
        (ske as int - 1) / (4 * (lambda as int / 128)) < 30,
        x.delta == xk.delta,
    ensures
        o.scalars.len() == 8 * ske,
        forall |jj: int, b: int|
            #![trigger o.scalars[8 * jj + b]]
            0 <= jj < ske as int && 0 <= b < 8
                ==> o.scalars[8 * jj + b]
                    == keb_y_vc(
                        x.scalars@,
                        xk.scalars@,
                        lambda as int,
                        jj,
                        b,
                        *x.delta,
                    ),
        o.delta == x.delta,
{
    // y_tag = Box<Array::default()> lowering: zero allocation
    let mut y: Vec<u128> = Vec::new();
    let mut q: usize = 0;
    while q < 8 * ske
        invariant
            y.len() == q,
        decreases
            8 * ske - q,
    {
        y.push(0u128);
        q += 1;
    }
    // ::3-:5 the j-loop
    let rcon_evry: usize = 4 * (lambda / 128);
    let mut iwd: usize = 0;
    let mut j: usize = 0;
    while j < ske
        decreases
            ske - j,
    {
        // :7-:10 the xt window (per-lane delta tap)
        let mut xt: [u128; 8] = [0u128; 8];
        let mut i: usize = 0;
        while i < 8
            decreases
                8 - i,
        {
            let mut x_tilde_i: u128 = x.scalars[8 * j + i]
                ^ xk.scalars[iwd + 8 * (j % 4) + i];
            if j % rcon_evry == 0
                && ((RCON_TABLE[j / rcon_evry] >> i) & 1) != 0 {
                x_tilde_i = x_tilde_i ^ *x.delta;
            }
            xt[i] = x_tilde_i;
            i += 1;
        }
        // :10 the affine fold into this window
        inverse_affine_byte(&mut y[8 * j..8 * j + 8], &xt, x.delta);
        // :12 the ladder increment
        if j % 4 == 3 {
            if lambda != 256 {
                iwd += lambda;
            } else {
                iwd += 128;
            }
        }
        j += 1;
    }
    VoleCommits { scalars: y, delta: x.delta }
}

// ===========================================================================
// key_exp_cstrnts (upstream :116-172). Origin Rust:
//     pub(crate) fn key_exp_cstrnts<O>(
//         zk_hasher: &mut ZKVerifyHasher<OWFField<O>>,
//         w: VoleCommitsRef<'a, OWFField<O>, O::LKe>,
//     ) -> VoleCommits<'a, OWFField<O>, O::R1Times128> {
//         let k = key_exp_fwd::<O>(w);
//         let w_flat = key_exp_bkwd::<O>(
//             w.get_commits_ref::<O::LKeMinusLambda>(O::Lambda::USIZE),
//             k.to_ref());
//         let mut iwd = 32 * (O::NK::USIZE - 1);
//         let mut do_rot_word = true;
//         for (j, r) in iproduct!(0..O::SKe::USIZE / 4, 0..4) {
//             let r_prime_inv = if do_rot_word { (4 + r - 3) % 4 } else { r };
//             let k_hat = OWFField::<O>::byte_combine_slice(
//                 &k[iwd + 8 * r_prime_inv..iwd + 8 * r_prime_inv + 8]);
//             let k_hat_sq = OWFField::<O>::byte_combine_sq_slice(
//                 &k[iwd + 8 * r_prime_inv..iwd + 8 * r_prime_inv + 8]);
//             let w_hat = OWFField::<O>::byte_combine_slice(
//                 &w_flat[32 * j + 8 * r..32 * j + 8 * r + 8]);
//             let w_hat_sq = OWFField::<O>::byte_combine_sq_slice(
//                 &w_flat[32 * j + 8 * r..32 * j + 8 * r + 8]);
//             zk_hasher.lift_and_process(&k_hat, &k_hat_sq, &w_hat, &w_hat_sq);
//             if r == 3 {
//                 if O::Lambda::USIZE == 256 { do_rot_word = !do_rot_word; }
//                 if O::Lambda::USIZE == 192 { iwd += 192; } else { iwd += 128; }
//             } }
//         k }
// Structurally verified (the verify-side lift_and_process carries no
// requires, so no FA6p-1 gate): the hasher trajectory rows stay
// out of the twin contract (upstream itself contracts nothing on
// the feed chain); the return value rows delegate to the fwd face.
// The k/w_hat windows read through this file's landed
// gf128_byte_combine_slice / _sq_slice folds, whose spec faces are
// the FA11-beta lane tables.
// ===========================================================================

/// Origin Rust (:116-172).
pub fn key_exp_cstrnts<'a>(
    zk_hasher: &mut ZKVerifyHasher128,
    w: &VoleCommitsRef<'a>,
    nk: usize,
    lambda: usize,
    ske: usize,
    n_words: usize,
) -> (k: VoleCommits<'a>)
    requires
        nk >= 1,
        nk <= 8,
        lambda == 128 || lambda == 192 || lambda == 256,
        lambda == 32 * nk,
        n_words > nk,
        n_words <= 64,
        ske >= 4,
        ske <= 64,
        ske % 4 == 0,
        32 * n_words <= usize::MAX,
        8 * ske <= usize::MAX,
        // the fwd consume bound
        (lambda as int) + 32 * (kef_cw(nk as int, nk as int, n_words as int) + 1)
            <= w.scalars.len() as int,
        // the bkwd x-window rows
        8 * ske <= (w.scalars.len() - lambda),
        keb_iwd(lambda as int, ske as int - 1) + 8 * 3 + 8
            <= 32 * n_words,
        (ske as int - 1) / (4 * (lambda as int / 128)) < 30,
        // the last-group read slack (FA9 row-derived; holds on all
        // three AES rows: 1296 <= 1408 / 1544 <= 1664 / 1800 <= 1920)
        32 * (nk as int - 1)
            + (if lambda == 192 { 192int } else { 128int })
                * ((ske as int / 4) - 1) + 40
            <= 32 * n_words as int,
    ensures
        k.scalars.len() == 32 * n_words,
        forall |j: int, i: int|
            0 <= j < n_words as int && 0 <= i < 32
                ==> k.scalars[32 * j + i]
                    == kef_lane(w.scalars@, nk as int, lambda as int, j, i),
        k.delta == w.delta,
        final(zk_hasher).delta == old(zk_hasher).delta,
        final(zk_hasher).delta_squared == old(zk_hasher).delta_squared,
{
    // ::1
    let k = key_exp_fwd(w, nk, lambda, n_words);
    // ::2
    let x_ref: VoleCommitsRef<'a> = VoleCommitsRef {
        scalars: &w.scalars[lambda..],
        delta: w.delta,
    };
    let w_flat = key_exp_bkwd(&x_ref, &k.to_ref(), ske, lambda);
    // ::3-:4 the iproduct loop (nested, same iteration order)
    let mut iwd: usize = 32 * (nk - 1);
    let mut do_rot_word: bool = true;
    let n_groups: usize = ske / 4;
    let mut j: usize = 0;
    while j < n_groups
        invariant
            nk >= 1,
            nk <= 8,
            lambda == 128 || lambda == 192 || lambda == 256,
            lambda == 32 * nk,
            n_words > nk,
            n_words <= 64,
            ske >= 4,
            ske <= 64,
            ske % 4 == 0,
            32 * n_words <= usize::MAX,
            8 <= 32 * n_words,
            8 * ske <= usize::MAX,
            n_groups == ske / 4,
            j <= n_groups,
            k.scalars.len() == 32 * n_words,
            w_flat.scalars.len() == 8 * ske,
            do_rot_word == (lambda != 256 || j % 2 == 0),
            iwd as int == 32 * (nk as int - 1)
                + (if lambda == 192 { 192int } else { 128int }) * (j as int),
            32 * n_groups <= 8 * ske,
            j == n_groups || (iwd as int + 40 <= 32 * n_words as int),
            zk_hasher.delta == old(zk_hasher).delta,
            zk_hasher.delta_squared == old(zk_hasher).delta_squared,
            32 * (nk as int - 1)
                + (if lambda == 192 { 192int } else { 128int }) * ((ske as int / 4) - 1) + 40
                <= 32 * n_words as int,
        decreases
            n_groups - j,
    {
        let mut r: usize = 0;
        while r < 4
            invariant
                nk >= 1,
                nk <= 8,
                lambda == 128 || lambda == 192 || lambda == 256,
                lambda == 32 * nk,
                n_words > nk,
                n_words <= 64,
                ske >= 4,
                ske <= 64,
                ske % 4 == 0,
                32 * n_words <= usize::MAX,
                8 * ske <= usize::MAX,
                n_groups == ske / 4,
                j < n_groups,
                r <= 4,
                j <= n_groups,
                k.scalars.len() == 32 * n_words,
                w_flat.scalars.len() == 8 * ske,
                32 * n_groups <= 8 * ske,
                (r as int == 4) || (iwd as int + 40 <= 32 * n_words as int),
                32 * (nk as int - 1)
                    + (if lambda == 192 { 192int } else { 128int }) * ((ske as int / 4) - 1) + 40
                    <= 32 * n_words as int,
                do_rot_word == (if lambda != 256 {
                    true
                } else {
                    ((j as int) + (if r == 4 { 1int } else { 0int })) % 2 == 0
                }),
                iwd as int == 32 * (nk as int - 1)
                    + (if lambda == 192 { 192int } else { 128int })
                        * ((j as int) + (if r == 4 { 1int } else { 0int })),
                zk_hasher.delta == old(zk_hasher).delta,
                zk_hasher.delta_squared == old(zk_hasher).delta_squared,
            decreases
                4 - r,
        {
            // ::11 the rot-word discriminator
            let r_prime_inv: usize = if do_rot_word {
                (4 + r - 3) % 4
            } else {
                r
            };
            // bounds rows for the four window reads
            assert(iwd + 8 * r_prime_inv + 8 <= k.scalars.len());
            assert(32 * j + 8 * r + 8 <= w_flat.scalars.len());
            assert(iwd + 8 * r_prime_inv + 8 <= usize::MAX);
            assert(32 * j + 8 * r + 8 <= usize::MAX);
            // ::12-13 the k windows
            let k_hat: u128 =
                gf128_byte_combine_slice(&k.scalars[iwd + 8 * r_prime_inv..iwd + 8 * r_prime_inv + 8]);
            let k_hat_sq: u128 =
                gf128_byte_combine_sq_slice(&k.scalars[iwd + 8 * r_prime_inv..iwd + 8 * r_prime_inv + 8]);
            // ::14-15 the w_flat windows
            let w_hat: u128 =
                gf128_byte_combine_slice(&w_flat.scalars[32 * j + 8 * r..32 * j + 8 * r + 8]);
            let w_hat_sq: u128 =
                gf128_byte_combine_sq_slice(&w_flat.scalars[32 * j + 8 * r..32 * j + 8 * r + 8]);
            // ::19-20 the feed (FA6 verify-side face: no requires)
            zk_hasher.lift_and_process(k_hat, k_hat_sq, w_hat, w_hat_sq);
            // ::16 / :21 the group tail
            if r == 3 {
                if lambda == 256 {
                    do_rot_word = !do_rot_word;
                }
                if lambda == 192 {
                    iwd += 192;
                } else {
                    iwd += 128;
                }
            }
            r += 1;
        }
        j += 1;
    }
    k
}

} // verus!
