//! faest 0.3.0 -- Verus transcription of src/aes.rs (the state-op
//! trait surface of the OWF constraint layers), batch FA10-pre.
//!
//! Origin Rust: upstream src/aes.rs declares eight pub(crate) traits
//! that the prover/verifier constraint modules (prover/aes.rs,
//! verifier/aes.rs, prover/encryption.rs, verifier/encryption.rs;
//! later batches) implement over the constraint state types. Every
//! upstream doc line is transcribed verbatim below at its trait.
//!
//! Transcription decisions:
//!  1. The `O: OWFParameters` generic bound lowers to the local
//!     marker trait OWFParametersFace: the FA9 tower pinned the
//!     upstream OWFParameters row values as flat constants
//!     (verified/src/parameter_tower.rs), and the FA4-1 hazard class
//!     bans trait-declaration-side trait bounds carrying assоciated
//!     WF axioms into shared units; a bare marker keeps the trait
//!     shape bit-identical (generic parameter, S-FA10-x in the
//!     notes).
//!  2. No impls live in this file upstream (and none here); the
//!     traits compile as declarations only.

use vstd::prelude::*;

verus! {

/// Marker for the upstream `parameter::OWFParameters` bound
/// (parameter.rs:236-303): the numeric face is FA9's flat constant
/// tower; this marker carries no members and no WF axioms.
pub trait OWFParametersFace {
}

/// Upstream aes.rs:3-8 (doc verbatim):
///   "Trait for adding a round key to the state, generating a new state"
pub(crate) trait AddRoundKey<Rhs = Self> {
    type Output;

    fn add_round_key(&self, rhs: Rhs) -> Self::Output;
}

/// Upstream aes.rs:10-13 (doc verbatim):
///   "Trait for adding a round key to the state in-place"
pub(crate) trait AddRoundKeyAssign<Rhs = Self> {
    fn add_round_key_assign(&mut self, rhs: Rhs);
}

/// Upstream aes.rs:15-20 (doc verbatim):
///   "Trait for combining commitments to the state bits into commitments to the state bytes"
pub(crate) trait StateToBytes<O: OWFParametersFace> {
    type Output;

    fn state_to_bytes(&self) -> Self::Output;
}

/// Upstream aes.rs:22-26 (doc verbatim):
///   "Trait for applying the AES inverse shift rows transformation to the state, generating a new state"
pub(crate) trait InverseShiftRows<O: OWFParametersFace> {
    type Output;
    fn inverse_shift_rows(&self) -> Self::Output;
}

/// Upstream aes.rs:28-32 (doc verbatim):
///   "Trait for applying the AES mix columns transformation to the state bytes, generating a new state"
pub(crate) trait BytewiseMixColumns<O: OWFParametersFace> {
    type Output;
    fn bytewise_mix_columns(&self) -> Self::Output;
}

/// Upstream aes.rs:34-38 (doc verbatim):
///   "Trait for applying the AES S-box affine transformation to the state, generating a new state"
pub(crate) trait SBoxAffine<O: OWFParametersFace> {
    type Output;
    fn s_box_affine(&self, sq: bool) -> Self::Output;
}

/// Upstream aes.rs:40-43 (doc verbatim):
///   "Trait for applying the AES shift rows transformation to the state in-place"
pub(crate) trait ShiftRows {
    fn shift_rows(&mut self);
}

/// Upstream aes.rs:45-48 (doc verbatim):
///   "Trait for applying the AES S-box affine inverse transformation to the state in-place"
pub(crate) trait InverseAffine {
    fn inverse_affine(&mut self);
}

/// Upstream aes.rs:50-53 (doc verbatim):
///   "Trait for applying the AES mix columns transformation to the state in-place"
pub(crate) trait MixColumns<O> {
    fn mix_columns(&mut self, sq: bool);
}

/// Upstream aes.rs:55-58 (doc verbatim):
///   "Trait for adding a round key to the state bytes in-place"
pub(crate) trait AddRoundKeyBytes<Rhs = Self> {
    fn add_round_key_bytes(&mut self, rhs: Rhs, sq: bool);
}

} // verus!
