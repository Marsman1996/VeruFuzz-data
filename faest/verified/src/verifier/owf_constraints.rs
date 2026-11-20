//! faest 0.3.0 -- Verus transcription of src/verifier/owf_
//! constraints.rs, batch FA12 (window 5: the two-branch dispatch
//! face lands in the frozen form -- the same trajectory ruling as
//! the key_exp_cstrnts / enc_cstrnts drivers of windows 3-4).
//!
//! Upstream (verifier/owf_constraints.rs, 121 lines, pin 9ccc68c0):
//! owf_constraints (:24-90, the two-branch OWF dispatch),
//! byte_to_field (:92-98), key_schedule_bytes (:100-121).
//!
//! Consumption-surface rulings (batch records, first-hand):
//!   - The key_schedule production line stays the FA10 oracle
//!     contract (D-FA10-1): the EM branch's ext_key rows ride as a
//!     DATA parameter (the schedule bytes, oracle-arbitrated; 32
//!     bytes per round row, the first nst_bytes of each row used --
//!     upstream :108-121 verbatim lowering below), NOT a re-erected
//!     schedule.
//!   - The upstream `pk: &PublicKey<O>` parameter lowers to the
//!     (owf_input, owf_output) byte-slice pair (FA10 delivered the
//!     layout faces, not the type).
//!   - `O: OWFParameters` drops to runtime rows (ns/nk/r/ske/lambda/
//!     lke/lenc/beta and the is_em discriminator); the Index<..> /
//!     as_slice() carriers lower per the vole_commitments records.
//!   - The two consumers (key_exp_cstrnts, enc_cstrnts) are the
//!     landed twin faces; under this driver's external_body the
//!     bodies ride their signatures (requires rows of the chain
//!     re-erect as the caller obligations listed in the batch
//!     notes' FA13 ledger).

use vstd::prelude::*;

use crate::universal_hashing::ZKVerifyHasher128;

use super::key_expansion::key_exp_cstrnts;
use super::vole_commitments::{VoleCommits, VoleCommitsRef};

verus! {

// ===========================================================================
// byte_to_field (upstream :92-98). Origin Rust:
//     #[inline]
//     fn byte_to_field<F>(byte: u8, delta: F) -> [F; 8]
//     where F: BigGaloisField {
//         array::from_fn(|i| delta * ((byte >> i) & 1)) }
// The Mul<u8> is the bit-0 select (the apply_mask record); rides
// inside the frozen driver body (helper below).
// ===========================================================================

/// Origin Rust (:24-90); the two-branch dispatch face, FROZEN
/// (external_body + structural rows; the batch trajectory ruling:
/// upstream itself contracts nothing on the feed chain).
#[verifier::external_body]
pub fn owf_constraints(
    zk_hasher: &mut ZKVerifyHasher128,
    w: &VoleCommitsRef,
    delta: &u128,
    owf_input: &[u8],
    owf_output: &[u8],
    schedule_bytes: &[u8],
    nst: usize,
    nst_bytes: usize,
    nst_bits: usize,
    nk: usize,
    lambda: usize,
    r: usize,
    ske: usize,
    n_words: usize,
    lke: usize,
    lenc: usize,
    beta: usize,
    is_em: bool,
)
    requires
        nst >= 4,
        nst_bytes == 4 * nst,
        nst_bits == 8 * nst_bytes,
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
        lke >= lambda,
        lke + (lenc * (if is_em { 1 } else { beta })) <= w.scalars.len(),
        w.delta == delta,
        // the x/y plane rows (the three non-EM rows have
        // InputSize == NStBytes; the EM rows likewise)
        owf_input.len() == nst_bytes,
        if is_em {
            owf_output.len() == nst_bytes
        } else {
            owf_output.len() == beta * nst_bytes
        },
        beta >= 1,
        8 * beta <= usize::MAX,
        // the EM data-contract rows (D-FA10-1: the schedule bytes,
        // 32 per round row, R+1 rows)
        if is_em {
            schedule_bytes.len() >= 32 * (r + 1)
        } else {
            schedule_bytes.len() == 0
        },
        // the key_exp_cstrnts chain rows (non-EM; mirrored from the
        // landed twin face so future callers see the exact form)
        if !is_em {
            8 * ske <= (w.scalars.len() - lambda)
                && (lambda as int)
                    + 32 * (crate::prover::key_expansion::kef_cw(
                        nk as int, nk as int, n_words as int) + 1)
                        <= w.scalars.len() as int
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
    ensures
        final(zk_hasher).delta == old(zk_hasher).delta,
        final(zk_hasher).delta_squared == old(zk_hasher).delta_squared,
{
    // ::5 the linear-constraint seed feed
    zk_hasher.mul_and_update(w.scalars[0], w.scalars[1]);
    if is_em {
        // ::8-9 key_schedule_bytes (the D-FA10-1 data contract):
        // take the first NStBytes of each 32-byte schedule row and
        // expand every byte into its eight bit-select scalars
        let n_rows: usize = r + 1;
        let mut ext_flat: Vec<u128> = Vec::new();
        let mut row: usize = 0;
        while row < n_rows
        {
            let mut byte_i: usize = 0;
            while byte_i < nst_bytes
            {
                let byte: u8 = schedule_bytes[32 * row + byte_i];
                let mut i: usize = 0;
                while i < 8
                {
                    if ((byte >> i) & 1) == 1 {
                        ext_flat.push(*delta);
                    } else {
                        ext_flat.push(0u128);
                    }
                    i += 1;
                }
                byte_i += 1;
            }
            row += 1;
        }
        // :10-11 the owf_input window + the output rows
        let owf_input_c: VoleCommitsRef = w.get_commits_ref(0, nst_bits);
        let mut out_scalars: Vec<u128> = Vec::new();
        let mut q: usize = 0;
        while q < nst_bits
        {
            out_scalars.push(0u128);
            q += 1;
        }
        let out_row: &[u128] = &ext_flat[0..0];
        let _ = out_row;
        // :11 owf_output = owf_input.add_round_key(y) -- the u8-key
        // select face of the landed aes twin (elemwise delta taps)
        let mut q_y: usize = 0;
        while q_y < nst_bits
        {
            let bit: u8 = (owf_output[q_y / 8] >> (q_y % 8)) & 1;
            if bit == 1 {
                out_scalars[q_y] = owf_input_c.scalars[q_y] ^ *delta;
            } else {
                out_scalars[q_y] = owf_input_c.scalars[q_y];
            }
            q_y += 1;
        }
        let owf_output_c: VoleCommits = VoleCommits {
            scalars: out_scalars,
            delta,
        };
        // :19 / :21 the enc driver over the window rows
        let w_tilde: VoleCommitsRef = w.get_commits_ref(lke, lenc);
        super::encryption::enc_cstrnts(
            zk_hasher,
            &owf_input_c.scalars,
            &owf_output_c.scalars,
            &w_tilde,
            &ext_flat,
            nst,
            nst_bytes,
            r / 2,
        );
    } else {
        // :13 the owf_input commitment rows (from_constant over the
        // x plane; the Mul<u8> bit-select is the roster below)
        let mut in_scalars: Vec<u128> = Vec::new();
        let mut q_in: usize = 0;
        while q_in < nst_bits
        {
            let bit: u8 = (owf_input[q_in / 8] >> (q_in % 8)) & 1;
            if bit == 1 {
                in_scalars.push(*delta);
            } else {
                in_scalars.push(0u128);
            }
            q_in += 1;
        }
        let mut owf_input_c: VoleCommits = VoleCommits {
            scalars: in_scalars,
            delta,
        };
        // :16 the key-expansion constraint chain (landed twin)
        let k: VoleCommits = key_exp_cstrnts(
            zk_hasher,
            &w.get_commits_ref(0, lke),
            nk,
            lambda,
            ske,
            n_words,
        );
        // :17-18 the extended-key rows (R+1 windows of NStBits at
        // the i * NStBits::USIZE offsets -- flattened carrier)
        // (k.scalars is exactly the flattened row set)
        let ext_flat: &[u128] = &k.scalars;
        // :18-22 the beta loop
        let n_rows: usize = r + 1;
        let _ = n_rows;
        let mut b: usize = 0;
        while b < beta
        {
            // :19 the w_tilde window
            let w_tilde: VoleCommitsRef =
                w.get_commits_ref(lke + b * lenc, lenc);
            // :19-20 the owf_output rows over the y slice window
            let y_win: &[u8] =
                &owf_output[nst_bytes * b..nst_bytes * (b + 1)];
            let mut out_scalars: Vec<u128> = Vec::new();
            let mut q_out: usize = 0;
            while q_out < nst_bits
            {
                let bit: u8 = (y_win[q_out / 8] >> (q_out % 8)) & 1;
                if bit == 1 {
                    out_scalars.push(*delta);
                } else {
                    out_scalars.push(0u128);
                }
                q_out += 1;
            }
            let owf_output_c: VoleCommits = VoleCommits {
                scalars: out_scalars,
                delta,
            };
            // :21 the enc driver
            super::encryption::enc_cstrnts(
                zk_hasher,
                &owf_input_c.scalars,
                &owf_output_c.scalars,
                &w_tilde,
                ext_flat,
                nst,
                nst_bytes,
                r / 2,
            );
            // :20 owf_input.scalars[0] += delta
            owf_input_c.scalars[0] = owf_input_c.scalars[0] ^ *delta;
            b += 1;
        }
    }
}

// Records (this file's remaining upstream surface, both riding the
// frozen driver body per the header rulings):
//   - byte_to_field (:92-98): the per-bit delta selects inline above
//     (the array::from_fn lowers to the 8-lane push rosters; the
//     FA6-pre from_constant face is the same arithmetic -- recorded,
//     not re-erected inside the frozen body).
//   - key_schedule_bytes (:100-121): the D-FA10-1 data contract --
//     the EM branch consumes the schedule-bytes parameter directly
//     (the chunk/take/map lowering spelled above); no schedule
//     production is re-erected here.

} // verus!
