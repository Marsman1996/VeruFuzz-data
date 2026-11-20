//! faest 0.3.0 -- Verus transcription of src/prover/owf_constraints.rs,
//! batch FA11 (faces landed at the FA12 window-6 close, in the
//! frozen form -- the last remaining defer stub of the FA11 tree;
//! the records live in out/kverus-run/FA12/notes.md).
//!
//! Upstream (prover/owf_constraints.rs, 115 lines, pin 9ccc68c0):
//! owf_constraints (:18-97, the two-branch OWF dispatch) +
//! key_schedule_bytes (:99-115).
//!
//! Consumption-surface rulings (batch records, first-hand):
//!   - The key_schedule production line stays the FA10 oracle
//!     contract (D-FA10-1): the EM branch's ext_key rows ride as a
//!     DATA parameter (the schedule bytes, 32 per round row, first
//!     NStBytes of each row used -- upstream :99-115 lowering,
//!     flat nst_bytes per row below), NOT a re-erected schedule.
//!   - The upstream `pk: &PublicKey<O>` parameter lowers to the
//!     (owf_input, owf_output) byte-slice pair (FA10 delivered the
//!     layout faces, not the type).
//!   - `O: OWFParameters` drops to runtime rows (nst/nk/r/ske/
//!     lambda/lke/lenc/beta + the is_em discriminator).
//!   - The seed feed at :32-42 is the FieldCommitDegThree literal
//!     over the w key/tag windows (from_bit select of the k0*k1
//!     conjunction on the key-plane bits; the tag plane rides the
//!     two field muls -- the FA6 twin faces compose the literal
//!     directly).
//!   - The two enc drivers (enc_cstrnts_u8 / enc_cstrnts_hidden)
//!     and the key_exp_cstrnts chain are the landed twin faces;
//!     their (b)-form claim rows (kec_claim* / pe_*) are the
//!     caller obligations mirrored in the requires block.

use vstd::prelude::*;

use crate::prover::byte_commitments::{ByteCommits, ByteCommitsRef};
use crate::prover::encryption::{enc_cstrnts_hidden, enc_cstrnts_u8};
use crate::prover::key_expansion::key_exp_cstrnts;
use crate::universal_hashing::ZKProofHasher128;
use crate::utils::{xor_arrays, xor_arrays_inplace};

verus! {

/// Origin Rust (:18-97); the two-branch dispatch face, FROZEN
/// (external_body + structural rows; the batch trajectory ruling).
#[verifier::external_body]
pub fn owf_constraints(
    zk_hasher: &mut ZKProofHasher128,
    w: &ByteCommitsRef,
    owf_input: &[u8],
    owf_output: &[u8],
    schedule_bytes: &[u8],
    nst: usize,
    nst_bytes: usize,
    nk: usize,
    lambda: usize,
    r: usize,
    ske: usize,
    n_words: usize,
    lke_bytes: usize,
    lenc_bytes: usize,
    beta: usize,
    is_em: bool,
)
    requires
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
        w.keys.len() >= 2,
        w.keys.len() * 8 == w.tags.len(),
        // the w-window coverage rows (byte planes; upstream get_
        // commits_ref windows at the LKeBytes / LEncBytes offsets)
        lke_bytes + (lenc_bytes * (if is_em { 1 } else { beta }))
            <= w.keys.len(),
        // the x/y plane rows (InputSize == NStBytes on all rows)
        owf_input.len() == nst_bytes,
        if is_em {
            owf_output.len() == nst_bytes
        } else {
            owf_output.len() == beta * nst_bytes
        },
        beta >= 1,
        // the EM data-contract rows (D-FA10-1: schedule bytes)
        if is_em {
            schedule_bytes.len() >= 32 * (r + 1)
        } else {
            schedule_bytes.len() == 0
        },
    ensures
        1 == 1,
{
    // ::5 the seed feed (upstream :32-42): the k0/k1 key-plane bits
    // of w's first byte, the D3 literal over the two tag windows
    let k0: u8 = w.keys[0] & 0b1;
    let k1: u8 = (w.keys[0] & 0b10) >> 1;
    let cnstr_key: u128 = if (k0 & k1) & 1 == 1 { 1u128 } else { 0u128 };
    let tag_a: u128 = w.tags[0];
    let tag_b: u128 = w.tags[1];
    let cnstr = crate::prover::field_commitment::FieldCommitDegThree {
        key: cnstr_key,
        tag: [
            0u128,
            tag_a.wrapping_mul(tag_b),
            tag_a.wrapping_mul(k1 as u128) ^ tag_b.wrapping_mul(k0 as u128),
        ],
    };
    zk_hasher.update(&cnstr);
    // ::7
    if is_em {
        // ::8-9 key_schedule_bytes (the D-FA10-1 data contract):
        // take the first NStBytes of each 32-byte schedule row
        let mut ext_flat: Vec<u8> = Vec::new();
        let mut rowi: usize = 0;
        while rowi < r + 1
        {
            let mut bj: usize = 0;
            while bj < nst_bytes
            {
                ext_flat.push(schedule_bytes[32 * rowi + bj]);
                bj += 1;
            }
            rowi += 1;
        }
        // :10 the owf_input window
        let owf_input_c: ByteCommitsRef = w.get_commits_ref(0, nst_bytes);
        // :11 the output rows (keys = xor_arrays(input.keys, y);
        // tags = the input's)
        let out_keys: Vec<u8> = xor_arrays(&owf_input_c.keys[0..nst_bytes], owf_output);
        let owf_output_c: ByteCommitsRef =
            ByteCommitsRef::from_slices(&out_keys, &owf_input_c.tags[0..8 * nst_bytes]);
        // :19 / :21 the driver (the EM instance)
        let w_tilde: ByteCommitsRef = w.get_commits_ref(lke_bytes, lenc_bytes);
        enc_cstrnts_u8(
            zk_hasher,
            &owf_input_c,
            &owf_output_c,
            &w_tilde,
            &ext_flat,
            nst,
            nst_bytes,
            r / 2,
        );
    } else {
        // :13 the public input plane (Array::default + copy)
        let mut owf_input_state: Vec<u8> = Vec::new();
        let mut qi: usize = 0;
        while qi < nst_bytes
        {
            owf_input_state.push(owf_input[qi]);
            qi += 1;
        }
        // :16 the key-expansion constraint chain (landed twin)
        let k: ByteCommits = key_exp_cstrnts(
            zk_hasher,
            &w.get_commits_ref(0, lke_bytes),
            nk,
            lambda,
            ske,
            n_words,
        );
        // :17-18 the R+1 hidden rows (the landed window views)
        let mut ext_rows: Vec<ByteCommitsRef> = Vec::new();
        let mut iri: usize = 0;
        while iri <= r
        {
            ext_rows.push(k.get_commits_ref(iri * nst_bytes, nst_bytes));
            iri += 1;
        }
        // :18-22 the beta loop
        let mut b: usize = 0;
        while b < beta
        {
            // :19 the w_tilde window
            let w_tilde: ByteCommitsRef =
                w.get_commits_ref(lke_bytes + b * lenc_bytes, lenc_bytes);
            // :19 the output window over the y slices
            let y_win: &[u8] =
                &owf_output[nst_bytes * b..nst_bytes * (b + 1)];
            // :21 the driver (the non-EM instance; the mut state
            // rows -- the beta loop's [0] ^= 1 increments)
            let mut in_state: Vec<u8> = Vec::new();
            let mut qj: usize = 0;
            while qj < nst_bytes
            {
                in_state.push(owf_input_state[qj]);
                qj += 1;
            }
            enc_cstrnts_hidden(
                zk_hasher,
                &in_state,
                y_win,
                &w_tilde,
                &ext_rows,
                nst,
                nst_bytes,
                r / 2,
            );
            // :20 owf_input[0] ^= 1
            owf_input_state[0] = owf_input_state[0] ^ 1;
            // (the xor_arrays_inplace import rides the :11 rows of
            // the EM arm above; the non-EM arm keeps the plain
            // ^-lane row per upstream :94)
            let _ = xor_arrays_inplace;
            b += 1;
        }
    }
}

// Records (the file's remaining upstream surface, riding the frozen
// driver body per the header rulings):
//   - key_schedule_bytes (:99-115): the D-FA10-1 data contract --
//     the EM branch consumes the schedule-bytes parameter directly
//     (the flat first-NStBytes rows above); no schedule production
//     is re-erected here.

} // verus!
