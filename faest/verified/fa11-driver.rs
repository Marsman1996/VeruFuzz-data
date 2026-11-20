//! faest FA11 batch driver -- prover/aes.rs + prover/encryption.rs +
//! prover/key_expansion.rs + prover/owf_constraints.rs (the prover
//! constraint tree), mounted standalone (the fa6p/fa10w driver shape;
//! src/lib.rs NOT mounted and NOT modified -- the mount is by direct
//! #[path], single source of verified facts).
//!
//! Mounts (read-only, in-flight/closed panels):
//! - `src/fields/large_fields.rs` (FA3 + FA11-beta; direct #[path]).
//! - `src/fields/small_fields.rs` (FA2; direct #[path]).
//! - `src/universal_hashing.rs` (FA6; the ZKProofHasher128 consume
//!   face of encryption key_expansion owf_constraints).
//! - `src/utils.rs` (FA1; xor_arrays family).
//! - `src/internal_keys.rs` (FA10; record-only for the PK layout),
//!   `src/rijndael_32.rs` (FA10-pre; RCON_TABLE),
//!   `src/parameter_tower.rs` (FA9; the row pins),
//!   `src/witness.rs` (FA10) -- mounted for the consumers below.
//! Mounts (this batch, via src/prover/mod.rs):
//! - `src/prover/aes.rs` -- the FA11 wave-1 twin (all sixteen faces
//!   of the constraint-AES layer: StateToBytes / AddRoundKey fam /
//!   ShiftRows / InverseShiftRows / MixColumns / SBoxAffine /
//!   InverseAffine / BytewiseMixColumns) over the FA6-pre
//!   byte_commitments / field_commitment seat;
//! - `src/prover/encryption.rs`, `src/prover/key_expansion.rs`,
//!   `src/prover/owf_constraints.rs` -- FA11 wave-2 workspaces (stub
//!   headers only this window; see out/kverus-run/FA11/notes.md, the
//!   defer ledger for the recon kit of each).

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

fn main() {}
