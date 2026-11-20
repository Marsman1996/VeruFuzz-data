//! faest FA10 batch driver -- witness.rs + internal_keys.rs, mounted
//! standalone (the fa10-driver shape). src/lib.rs is NOT mounted and
//! NOT modified: the FA3 large_fields window owns it this cycle; the
//! fields small-domain file is mounted directly by path (it has zero
//! crate-internal dependencies -- recon confirmed: the only import of
//! verified/src/fields/small_fields.rs is the vstd prelude), which
//! bypasses both lib.rs and the fields/mod.rs tree (whose mod lines
//! would chain-mount the in-flight large_fields.rs).
//!
//! Mounts (read-only closed panels):
//! - `src/parameter.rs` (FA1): the tau-offset face family (the
//!   constants this batch does not itself consume ride the tower's
//!   imports; mounted to keep the fa10-driver shape for the panel
//!   start).
//! - `src/parameter_tower.rs` (FA9): the constant tower with the
//!   six OWFParameters row sets the witness twin dispatches over.
//! - `src/rijndael_32.rs` (FA10-pre): the bitslice/permutation layer
//!   and the word accessor consumed at every witness step.
//! - `src/fields/small_fields.rs` (FA2, direct #[path]): the GF8
//!   faces behind gf8_exp_238/invnorm.
//! Mounts (this batch):
//! - `src/witness.rs` (FA10): the gf8_exp_238/invnorm/
//!   store_invnorm_state value twins, the save_key_bits /
//!   save_non_lin_bits / round_with_save byte-accounting twins with
//!   the RowCfg dispatch over the six rows, the kb pins + window
//!   identities (built HERE -- the FA10-pre notes listed them but
//!   they never landed), and aes_extendedwitness_from_kb (kb as the
//!   D-FA10-1 data contract; the production line rides the oracle).
//! - `src/internal_keys.rs` (FA10): the SK/PK serialization contract
//!   faces, the parse verdict twin with the format-domain gate, and
//!   the classify/declassify cfg-face records.
//! - `src/witness_loops.rs` (FA10 wave2): the three deep-loop exec
//!   twins (save_non_lin_bits / round_with_save /
//!   aes_extendedwitness_from_kb) with their converged loop
//!   contracts -- the wave-1 D-FA10w-1 carry-over closed.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

#[path = "src/rijndael_32.rs"]
mod rijndael_32;

#[path = "src/fields/small_fields.rs"]
mod small_fields;

#[path = "src/witness.rs"]
mod witness;

#[path = "src/internal_keys.rs"]
mod internal_keys;

#[path = "src/witness_loops.rs"]
mod witness_loops;

fn main() {}
