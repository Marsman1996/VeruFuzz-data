// Verified transcription of idna 1.1.0 src/lib.rs: the Errors face.
//
// Upstream pin: 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (servo/rust-url,
// SUBDIR=idna, file src/lib.rs, 198 lines).
// Basis: database/idna/code/idna/src/lib.rs; the pub-use re-exports of the
// module faces live in the sibling verified files (uts46.rs, deprecated.rs,
// punycode.rs), so this core holds the crate-level Errors type only.
// This is a standalone file (like the sibling faces): no external crate
// deps, ending with fn main() {}.
//
// Scope:
// * the `pub struct Errors {}` error-sentinel type (lib.rs:67-68) and its
//   Default core (`#[derive(Default)]`, lib.rs:66);
// * the `impl From<Errors> for Result<(), Errors>` channel (lib.rs:70-74)
//   as the core fn errors_to_result (external trait impls are not
//   verifiable faces; the From semantics is exactly this core).
//
// Locked ledger of the blocked surface (one line each with reason):
// * domain_to_ascii_cow / domain_to_ascii_from_cow / domain_to_ascii /
//   domain_to_ascii_strict / domain_to_unicode and the rest of the lib entry
//   surface (lib.rs:83-198): drive the blocked Uts46::to_ascii/to_unicode
//   pipeline (see the uts46 face ledger); batch C material.
// * `impl std::error::Error for Errors` / `impl core::error::Error` /
//   `impl core::fmt::Display` (Display = the derived Debug of the empty
//   struct, lib.rs:60-64 and 76-79): trait impls on external types; the
//   displayed text of the unit-like struct ("Errors") is attribute-level.
// * the module wiring layer (mod/pub use of punycode/uts46/deprecated and
//   the crate doc, lib.rs:1-59): module structure, not verification surface.
//
// Upstream doc (lib.rs:66):
// "Type indicating that there were errors during UTS #46 processing."

use vstd::prelude::*;

verus! {

/* ============================================================
 * Errors (lib.rs:66-79)
 * ============================================================ */

/// Origin: lib.rs:66-68 `pub struct Errors {}` with `#[derive(Default)]`
/// and `#[non_exhaustive]`: the empty error sentinel (the error channel
/// carries no payload; the process APIs signal rejects by mere presence).
/// Upstream doc (lib.rs:66):
///   Type indicating that there were errors during UTS #46 processing.
pub struct Errors {}

impl Errors {
    /// Origin: lib.rs:66 `#[derive(Default)]` as a core fn (external trait
    /// impls are not verifiable faces; semantics identical).
    pub fn default_() -> (r: Errors)
    {
        Errors {}
    }
}

/// Origin: lib.rs:70-74 `impl From<Errors> for Result<(), Errors>`, the
/// error-channel conversion as a core fn (the From semantics is exactly
/// this core: every Errors value converts to the Err arm).
/// Origin Rust: impl From<Errors> for Result<(), Errors> {
///     fn from(e: Errors) -> Self { Err(e) } }
pub fn errors_to_result(e: Errors) -> (r: Result<(), Errors>)
    ensures
        r.is_err(),
        r matches Err(e2) ==> e2 == e,
{
    Result::Err(e)
}

} // verus!

fn main() {}
