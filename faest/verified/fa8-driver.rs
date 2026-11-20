//! faest FA8 batch driver -- src/vole.rs (the VOLE commitment /
//! reconstruct layer over bavc: convert_to_vole, volecommit,
//! volereconstruct, the two VoleCommitmentCRef index faces,
//! TWEAK_OFFSET, vole_array_length), mounted standalone over the
//! FULL fa12/fa13 closed set (the fa13-driver shape; src/lib.rs NOT
//! mounted and NOT modified -- the mount is by direct #[path],
//! single source of verified facts).
//!
//! Mounts (read-only, closed/in-flight panels):
//! - the full fa13-driver closed set: `src/fields/{large,
//!   small}_fields.rs`, `src/universal_hashing.rs`, `src/utils.rs`,
//!   `src/internal_keys.rs`, `src/rijndael_32.rs`,
//!   `src/parameter.rs`, `src/parameter_tower.rs`,
//!   `src/witness.rs`, `src/aes.rs`, `src/random_oracles.rs`,
//!   `src/prover/mod.rs`, `src/verifier/mod.rs`,
//!   `src/zk_constraints.rs`, `src/faest.rs`, PLUS `src/prg.rs`
//!   (FA4 -- the fa13driver itself does not mount it, faest.rs's only
//!   prg consumption is the IV row type; the bavc/vole twins consume
//!   the PRG carrier + prg_byte + add_tweak_spec and require the
//!   module).
//! Mounts (this batch):
//! - `src/bavc.rs` (FA7 -- the first driver to mount it next to the
//!   faest twin: the FA13 shims made zero-intersection with the FA7
//!   in-flight tree; that tree closed this window's predecessor, so
//!   FA8 mounts both.  The consumed green machinery: the tau
//!   helpers + spec faces, prg_prefix, key_row, bpow/mpow and their
//!   lemmas -- the FA7 notes' consumable list).
//! - `src/vole.rs` (FA8, the twin of this batch).

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

#[path = "src/prg.rs"]
mod prg;

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

#[path = "src/bavc.rs"]
mod bavc;

#[path = "src/vole.rs"]
mod vole;

fn main() {}
