//! `engine/mod.rs` mirror -- machine-level translation of the Engine trait domain (the config types)
//!
//! Relaxation: the `Engine` trait + its default methods are not transcribed (see the lib.rs
//! ledger); the decode/encode default-method semantics are carried by the machine-level
//! functions under general_purpose and by their harness contract lemmas; this file
//! carries the `DecodePaddingMode` / estimate-related contract constants.

use vstd::prelude::*;

/* Module order matters for the per-panel verification cost: naive is declared
   first so its obligations are checked before the general_purpose scan-algebra
   items join the shared SMT context (the reverse order flips naive_internal_decode
   far over the default budget; see the execution ledger). */
pub mod naive;
pub mod general_purpose;

verus! {

/// Origin: engine/mod.rs:490 `DecodePaddingMode`
/// doc:
/// - Indifferent: "Canonical padding is allowed, but any fewer padding bytes
///   than that is also allowed."
/// - RequireCanonical: "Padding must be canonical (0, 1, or 2 `=` as needed
///   to produce a 4 byte suffix)."
/// - RequireNone: "Padding must be absent -- for when you want predictable
///   padding, without any wasted bytes."
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DecodePaddingMode {
    Indifferent,
    RequireCanonical,
    RequireNone,
}

} // verus!
