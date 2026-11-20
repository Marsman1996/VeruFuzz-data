//! faest FA6 batch driver -- universal_hashing.rs (the leaf hash /
//! VOLE hash / ZK hash / constraint-side proof hasher family),
//! mounted standalone (the fa6p-driver shape). src/lib.rs is NOT
//! touched: the prover twin tree keeps its driver-mount import
//! spellings (crate::large_fields) and mounts by #[path] here.
//!
//! Mounts (read-only, closed panels):
//! - `src/fields/large_fields.rs` + `src/fields/small_fields.rs`
//!   (FA3, closed tree at the 2026-11-14 10:28 snapshot; taken at
//!   the current-facts rule).
//! - `src/prover/mod.rs` -> field_commitment.rs + byte_commitments.rs
//!   (FA6-pre, closed: fa6p-driver re-mount against the FA3-closed
//!   tree is 706 verified / 0 errors @300 -- the two in-flight
//!   remnant rows cleared with the FA3 close).
//! Mounts (this batch):
//! - `src/universal_hashing.rs`: the universal_hashing twin at the
//!   GF128/GF192/GF256 axes.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/fields/large_fields.rs"]
mod large_fields;

#[path = "src/fields/small_fields.rs"]
mod small_fields;

#[path = "src/prover/mod.rs"]
mod prover;

#[path = "src/universal_hashing.rs"]
mod universal_hashing;

fn main() {}
