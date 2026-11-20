//! faest 0.3.0 -- Verus transcription of src/verifier/mod.rs, batch
//! FA12.
//!
//! Upstream (verifier/mod.rs, 8 lines, pin 9ccc68c0):
//!     mod aes;
//!     mod encryption;
//!     mod key_expansion;
//!     pub(crate) mod owf_constraints;
//!     pub(crate) mod vole_commitments;
//!
//!     pub(crate) use owf_constraints::owf_constraints;
//!     pub(crate) use vole_commitments::{VoleCommits, VoleCommitsRef};
//!
//! The upstream `pub(crate)` visibility rows lower to `pub` here per
//! the lib.rs harness-mount convention (single source of verified
//! facts). Both re-export rows ride as twin module exports below
//! (the FA12 window-5 close restored the owf_constraints row with
//! that module's landed face).
//!
//! The three consumer files beyond vole_commitments / aes carry the
//! standard FA11-style defer headers until their batch wave lands
//! (recon kits in out/kverus-run/FA12/notes.md):
//!   - `mod encryption` (187 lines): enc_cstrnts / enc_cstrnts_even /
//!     enc_cstrnts_odd / aes_round / invnorm_to_conjugates /
//!     f256_f2_conjugates.
//!   - `mod key_expansion` (172 lines): key_exp_cstrnts /
//!     key_exp_fwd / key_exp_bkwd / inverse_affine_byte.
//!   - `mod owf_constraints` (121 lines): owf_constraints (the
//!     two-branch OWF dispatch) + byte_to_field / key_schedule_bytes.

pub mod aes;
pub mod encryption;
pub mod key_expansion;
pub mod owf_constraints;
pub mod vole_commitments;

pub use owf_constraints::owf_constraints;
pub use vole_commitments::{VoleCommits, VoleCommitsRef};
