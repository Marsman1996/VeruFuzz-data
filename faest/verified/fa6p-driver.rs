//! faest FA6-pre batch driver -- prover/field_commitment.rs +
//! prover/byte_commitments.rs (the FA6/FA11 material batch),
//! mounted standalone (the fa10w-driver shape). src/lib.rs is NOT
//! mounted and NOT modified: the FA3 large_fields window owns the
//! fields tree this cycle; field files mount directly by path
//! (recon: verified/src/fields/large_fields.rs and
//! verified/src/fields/small_fields.rs each import only the vstd
//! prelude -- zero crate-internal dependencies, same first-hand
//! confirmation as the fa10w small_fields mount), which bypasses
//! lib.rs and fields/mod.rs (whose mod lines chain the module tree).
//!
//! Mounts (read-only in-flight/closed panels):
//! - `src/fields/large_fields.rs` (FA3, direct #[path]): the GF128
//!   axis faces -- gf128_mul/gf128_mul_spec, gf128_square/gf128_hmul,
//!   gf128_byte_combine(_bits)(_slice) + spec faces, GF128_ALPHA /
//!   GF128_ZERO / GF128_MODULUS consts. Mounted at the 2026-11-14
//!  08:0x mtime snapshot (the FA3 wave window); take the current
//!   facts rule applies.
//! - `src/fields/small_fields.rs` (FA2, direct #[path]): the GF8
//!   orbit faces -- gf8_ref_square_spread (the GF8::square_bits spec
//!   model), gf8_square_bits, gf8_mul_spec / lemma bank.
//! Mounts (this batch):
//! - `src/prover/mod.rs`: the module-tree re-export mirror.
//! - `src/prover/field_commitment.rs`: the FieldCommitment carrier +
//!   the degree faces (this batch's twin).
//! - `src/prover/byte_commitments.rs`: the byte-plane commitment
//!   twin + the derived SquareBytes/ByteCombineSquared faces + the
//!   bit-plane orbit obligations (this batch's twin).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/fields/large_fields.rs"]
mod large_fields;

#[path = "src/fields/small_fields.rs"]
mod small_fields;

#[path = "src/prover/mod.rs"]
mod prover;

fn main() {}
