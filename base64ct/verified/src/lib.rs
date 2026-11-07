//! base64ct library-body mirror (crate root)
//!
//! Upstream: https://github.com/RustCrypto/formats (SUBDIR=base64ct)
//!   pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614 (see code/base64ct/src/lib.rs;
//!   the code/ tree is unmodified)
//!
//! Consumption: this file has no fn main; the harness files drive it per the
//! KVerus convention (`#[path = "../src/lib.rs"] mod base64ct_v;`); files under
//! harness/ reference the work of this module tree; copying its spec is forbidden.
//!
//! Transcription ledger (KVerus relax conventions; see out/bug-finder-summary.md):
//! - Upstream crate attributes/doc (`no_std`, feature gates, docsrs cfg, etc.) and re-export
//!   declarations are builder-domain, outside the verification surface; the eight alphabet
//!   types are monomorphized into per-alphabet exec fns (modules alphabet/*); the trait
//!   correspondence is written in the alphabet.rs header notes.

pub mod alphabet;
pub mod encoding;
pub mod errors;

/// Minimum supported line width.
/// Origin: code/base64ct/src/lib.rs:108 `const MIN_LINE_WIDTH: usize = 4`
pub const MIN_LINE_WIDTH: usize = 4;
