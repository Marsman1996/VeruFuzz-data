//! faest FA12 batch driver -- verifier/{vole_commitments,aes,
//! key_expansion,encryption,owf_constraints}.rs + verifier/mod.rs
//! (the verifier constraint tree), mounted standalone (the
//! fa6p/fa10w/fa11 driver shape; src/lib.rs NOT mounted and NOT
//! modified -- the mount is by direct #[path], single source of
//! verified facts).
//!
//! Mounts (read-only, in-flight/closed panels):
//! - `src/fields/large_fields.rs` (FA3 + FA11-beta; direct #[path]).
//! - `src/fields/small_fields.rs` (FA2; direct #[path]).
//! - `src/universal_hashing.rs` (FA6; the ZKVerifyHasher128 consume
//!   face of enc_cstrnts / key_exp_cstrnts / owf_constraints).
//! - `src/utils.rs` (FA1).
//! - `src/internal_keys.rs` (FA10; record-only for the PK layout),
//!   `src/rijndael_32.rs` (FA10-pre; RCON_TABLE + the D-FA10-1
//!   key-schedule oracle contract pins),
//!   `src/parameter_tower.rs` (FA9; the row pins),
//!   `src/witness.rs` (FA10) -- mounted for the consumers below.
//! - `src/prover/mod.rs` (FA11): the BytewiseMixColumns contract
//!   machinery (col4/trow4/bmc_* + xt_lane, the double lemma) and
//!   the index-derivation spec faces (sr_src_idx / isr_src_idx /
//!   mc_slot_key / iaf_tag) are CONSUMED across the tree boundary
//!   here (the FA11 wave-2 pin, zero re-erect on the FA12 side).
//! Mounts (this batch, via src/verifier/mod.rs):
//! - `src/verifier/vole_commitments.rs` -- the VoleCommits /
//!   VoleCommitsRef carriers (the Delta storage face);
//! - `src/verifier/aes.rs` -- the constraint-system AES verification
//!   layer over those carriers (StateToBytes / AddRoundKey fam /
//!   ShiftRows / InverseShiftRows / BytewiseMixColumns / SBoxAffine
//!   / InverseAffine / MixColumns / AddRoundKeyBytes);
//! - `src/verifier/{encryption,key_expansion,owf_constraints}.rs` --
//!   later-wave workspaces (defer headers this window; see
//!   out/kverus-run/FA12/notes.md).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/fields/large_fields.rs"]
mod large_fields;

#[path = "src/fields/small_fields.rs"]
mod small_fields;

#[path = "src/universal_hashing.rs"]
mod universal_hashing;

#[path = "src/utils.rs"]
mod utils;

#[path = "src/internal_keys.rs"]
mod internal_keys;

#[path = "src/rijndael_32.rs"]
mod rijndael_32;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

#[path = "src/witness.rs"]
mod witness;

#[path = "src/aes.rs"]
mod aes;

#[path = "src/prover/mod.rs"]
mod prover;

#[path = "src/verifier/mod.rs"]
mod verifier;

fn main() {}
