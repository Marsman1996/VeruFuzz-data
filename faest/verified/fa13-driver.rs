//! faest FA13 batch driver -- src/faest.rs (the sign/verify/keygen
//! outer chain) + src/zk_constraints.rs (the aes_prove / aes_verify
//! pair layer), mounted standalone over the fa12-driver full set
//! (the fa6p/fa10w/fa11/fa12 driver shape; src/lib.rs NOT mounted
//! and NOT modified -- the mount is by direct #[path], single
//! source of verified facts).
//!
//! Mounts (read-only, closed/in-flight panels):
//! - `src/fields/large_fields.rs` (FA3 + FA11-beta; direct #[path]).
//! - `src/fields/small_fields.rs` (FA2; direct #[path]).
//! - `src/universal_hashing.rs` (FA6; the ZKProofHasher128 /
//!   ZKVerifyHasher128 / VoleHasher128 consume faces of the
//!   constraints segment and the u/v/q matrix hashing).
//! - `src/utils.rs` (FA1; xor_arrays_into / decode rows / get_bit /
//!   array_ref).
//! - `src/internal_keys.rs` (FA10; the SK/PK layout rows,
//!   record-only), `src/rijndael_32.rs` (FA10-pre; RCON_TABLE +
//!   the D-FA10-1 key-schedule oracle pins), `src/parameter.rs`
//!   (FA1; tau constants), `src/parameter_tower.rs` (FA9; the row
//!   pins), `src/witness.rs` (FA10; the extended-witness contract
//!   records), `src/aes.rs` (FA10-pre trait slice).
//! - `src/random_oracles.rs` (FA5): the H0..H4 ordered-init rows +
//!   the trusted-stream reader contract faces -- the faest.rs
//!   FaestHash bodies consume these direct (out/kverus-run/FA13/
//!   notes.md records the deviation from the FA12 window-4 mount
//!   list: this twin cannot compile the FaestHash faces without
//!   the closed FA5 panel).
//! - `src/prover/mod.rs` (FA11 + FA12): the prover constraint
//!   tree, whose owf_constraints twin is the sign chain's
//!   constraints segment.
//! - `src/verifier/mod.rs` (FA12): the verifier constraint tree,
//!   whose owf_constraints twin is the verify chain's constraints
//!   segment.
//! Mounts (this batch):
//! - `src/zk_constraints.rs` -- the aes_prove / aes_verify pair
//!   layer (reshape + the hasher finalization; the (b)-row
//!   requires uplift lives here);
//! - `src/faest.rs` -- the full outer chain twin (SignatureRefMut /
//!   SignatureRef carve faces, FaestHash, check_challenge_3,
//!   keygen, sign, verify and wrappers; the vole/bavc trust
//!   boundary shims; the iv_pre doc-context note).

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

#[path = "src/random_oracles.rs"]
mod random_oracles;

#[path = "src/prover/mod.rs"]
mod prover;

#[path = "src/verifier/mod.rs"]
mod verifier;

#[path = "src/zk_constraints.rs"]
mod zk_constraints;

#[path = "src/faest.rs"]
mod faest;

fn main() {}
