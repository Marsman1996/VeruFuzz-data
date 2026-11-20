//! faest 0.3.0 -- Verus transcription of src/prover/mod.rs, batch
//! FA6-pre.
//!
//! Upstream (prover/mod.rs, 10 lines, pin 9ccc68c0):
//!     mod aes;
//!     pub(crate) mod byte_commitments;
//!     mod encryption;
//!     pub(crate) mod field_commitment;
//!     mod key_expansion;
//!     pub(crate) mod owf_constraints;
//!
//!     pub(crate) use byte_commitments::{ByteCommits, ByteCommitsRef};
//!     use field_commitment::{FieldCommitDegOne, FieldCommitDegThree,
//!         FieldCommitDegTwo};
//!     pub(crate) use owf_constraints::owf_constraints;
//!
//! This batch transcribes the middle two module bodies
//! (field_commitment, byte_commitments -- the FA6/FA11 material
//! batch); the remaining four (aes, encryption, key_expansion,
//! owf_constraints) are FA11 scope and mount with their own batch
//! (records below). The re-export lines ride as twin module exports
//! (Verus module visibility is pub here per the lib.rs harness-mount
//! convention: single source of verified facts).

pub mod aes;
pub mod byte_commitments;
pub mod encryption;
pub mod field_commitment;
pub mod key_expansion;
pub mod owf_constraints;

pub use byte_commitments::{ByteCommitment, ByteCommits, ByteCommitsRef};
pub use field_commitment::{FieldCommitDegOne, FieldCommitDegThree, FieldCommitDegTwo};

// Records (upstream module lines whose bodies are not transcribed
// here, with the consumer-batch pointers):
//   - `mod aes` (383 lines): the ByteCommits/AddRoundKey concrete
//     impl layer over the crate::aes traits -- FA11.
//   - `mod encryption` (192 lines): enc_cstrnts / f256_f2_conjugates
//     over ByteCommitsRef + FieldCommitDegOne/Two + ZKProofHasher --
//     FA11; consumes this batch's square_inplace/combine faces
//     directly (f256_f2_conjugates, encryption.rs:181-192).
//   - `mod key_expansion` (165 lines): FA11.
//   - `mod owf_constraints` (115 lines): the owf_constraints driver
//     over ByteCommitsRef -- FA11 (needs zk_constraints.rs /
//     universal_hashing.rs from FA6 first).
